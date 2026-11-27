// Independent full-space replay for the square-summand calculation at level 79072.
// See docs/replays/square-2471-eclib.md for dependencies, inputs and invocation.
#include <fflas-ffpack/fflas-ffpack.h>
#include <givaro/modular-balanced.h>
#include <eclib/homspace.h>
#include <NTL/mat_lzz_p.h>

#include <fstream>
#include <sstream>
#include <stdexcept>

namespace {
constexpr int level = 79072, prime = 31;
using Field = Givaro::ModularBalanced<float>;
using Rows = std::vector<std::vector<int>>;
using Matrix = NTL::mat_zz_p;

int residue(long value) { return (value % prime + prime) % prime; }

struct Filter {
    int ell;
    std::vector<int> values;
};

std::vector<Filter> read_filters(const char* path) {
    std::ifstream input(path);
    std::vector<Filter> filters;
    std::string line;
    while (std::getline(input, line)) {
        std::istringstream row(line);
        Filter filter;
        if (!(row >> filter.ell)) continue;
        int a;
        while (row >> a) filter.values.push_back(a);
        filters.push_back(filter);
    }
    if (filters.empty() || filters.front().ell != 3 ||
        filters.front().values != std::vector<int>{0, 4, 27})
        throw std::runtime_error("expected the R1 filter at 3");
    return filters;
}

// Rows represent functionals by their values on eclib's primal Manin basis.
// Column i of the primal operator is row i in the equations for a functional.
Rows first_space(const homspace& symbols, const Filter& filter) {
    const int n = symbols.h1dim();
    const Field field(prime);
    Rows basis;
    for (const int a : filter.values) {
        std::vector<float> equations(static_cast<size_t>(n)*n, field.zero);
        for (int i = 0; i < n; ++i) {
            float* row = equations.data() + static_cast<size_t>(i)*n;
            for (auto [j,b] : symbols.s_heckeop_col(filter.ell, i+1))
                field.init(row[j-1], b);
            field.init(row[i], static_cast<long>(row[i])-a);
        }
        float* nullspace = nullptr;
        size_t stride = 0, dimension = 0;
        FFPACK::NullSpaceBasis(field, FFLAS::FflasRight, n, n,
            equations.data(), n, nullspace, stride, dimension);
        for (size_t k = 0; k < dimension; ++k) {
            auto& v = basis.emplace_back(n);
            for (int i = 0; i < n; ++i)
                v[i] = residue(static_cast<long>(nullspace[i*stride+k]));
        }
        FFLAS::fflas_delete(nullspace);
        std::cout << "T3 eigenvalue " << a << " dimension " << dimension << std::endl;
    }
    return basis;
}

std::vector<int> normalize(Rows& rows) {
    std::vector<int> pivots;
    const int m = rows.size(), n = rows.at(0).size();
    for (int j = 0; j < n && static_cast<int>(pivots.size()) < m; ++j) {
        const int r = pivots.size();
        int i = r;
        while (i < m && !rows[i][j]) ++i;
        if (i == m) continue;
        std::swap(rows[i], rows[r]);
        const int inverse = NTL::InvMod(rows[r][j], prime);
        for (int k = j; k < n; ++k) rows[r][k] = rows[r][k]*inverse % prime;
        for (i = 0; i < m; ++i) {
            if (i == r || !rows[i][j]) continue;
            const int factor = prime - rows[i][j];
            for (int k = j; k < n; ++k)
                rows[i][k] = (rows[i][k]+factor*rows[r][k]) % prime;
        }
        pivots.push_back(j);
    }
    if (static_cast<int>(pivots.size()) != m) throw std::runtime_error("dependent basis");
    return pivots;
}

// Every intermediate space is a common Hecke kernel and hence stable.
// Its pivot evaluations determine each image uniquely.
Matrix restrict_hecke(const homspace& symbols, const Rows& basis,
                      const std::vector<int>& pivots, int ell) {
    const int m = basis.size();
    Matrix result;
    result.SetDims(m, m);
    for (int j = 0; j < m; ++j) {
        auto column = symbols.s_heckeop_col(ell, pivots[j]+1);
        for (int i = 0; i < m; ++i) {
            long total = 0;
            for (auto [k,b] : column) total += basis[i][k-1]*(b % prime);
            result[i][j] = total;
        }
    }
    return result;
}

void filter_space(Rows& basis, std::vector<int>& pivots,
                  const Matrix& op, const std::vector<int>& values) {
    const int m = basis.size();
    Matrix product = NTL::ident_mat_zz_p(m), kernel;
    for (int a : values) {
        Matrix factor = op;
        for (int i = 0; i < m; ++i) factor[i][i] -= a;
        product = product * factor;
    }
    NTL::kernel(kernel, product); // left kernel in the row-vector convention
    if (kernel.NumRows() == m) return;
    if (!kernel.NumRows()) throw std::runtime_error("empty space before CM control");
    Rows next(kernel.NumRows(), std::vector<int>(basis[0].size()));
    for (long i = 0; i < kernel.NumRows(); ++i) {
        for (int j = 0; j < m; ++j) {
            const int c = NTL::rep(kernel[i][j]);
            if (c) for (size_t k = 0; k < basis[j].size(); ++k)
                next[i][k] += c*basis[j][k];
        }
        for (int& value : next[i]) value %= prime;
    }
    basis = std::move(next);
    pivots = normalize(basis);
}

const std::vector<int> dump_primes{3,5,11,13,17,19,61,683,1117,1303,1489,1861,2357,2543};

std::vector<Matrix> replay(int sign, const std::vector<Filter>& filters) {
    homspace symbols(level, sign, 0, 0);
    // eclib returns denominator-scaled columns. The run uses integral bases.
    if (symbols.h1denom() != 1) throw std::runtime_error("nonintegral Manin basis");
    std::cout << "sign " << sign << " ambient " << symbols.h1dim() << std::endl;
    Rows basis = first_space(symbols, filters.front());
    auto pivots = normalize(basis);
    std::cout << "after 3 dimension " << basis.size() << std::endl;
    for (size_t i = 1; i < filters.size(); ++i) {
        const auto& f = filters[i];
        filter_space(basis, pivots, restrict_hecke(symbols, basis, pivots, f.ell), f.values);
        std::cout << "after " << f.ell << " dimension " << basis.size() << std::endl;
    }
    std::vector<Matrix> blocks;
    for (int ell : dump_primes) {
        blocks.push_back(restrict_hecke(symbols, basis, pivots, ell));
        std::cout << "computed T_" << ell << std::endl;
    }
    return blocks;
}
} // namespace

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: check_square_2471_eclib FILTERS OUTPUT_PREFIX\n";
        return 1;
    }
    NTL::zz_p::init(prime);
    const auto filters = read_filters(argv[1]);
    const auto plus = replay(1, filters);
    const auto minus = replay(-1, filters);
    for (size_t k = 0; k < dump_primes.size(); ++k) {
        const int p = plus[k].NumRows(), n = p + minus[k].NumRows();
        std::ofstream out(std::string(argv[2]) + "_" + std::to_string(dump_primes[k]) + ".txt");
        out.exceptions(std::ios::badbit | std::ios::failbit);
        out << n << '\n';
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                long value = 0;
                if (i < p && j < p) value = NTL::rep(plus[k][i][j]);
                if (i >= p && j >= p) value = NTL::rep(minus[k][i-p][j-p]);
                out << value << (j+1 == n ? '\n' : ' ');
            }
        }
    }
}
