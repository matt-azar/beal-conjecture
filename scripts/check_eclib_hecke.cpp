// Build against eclib 20250122, FFLAS-FFPACK 2.5 and Givaro 4.2.
// g++ -O3 -std=c++17 check_eclib_hecke.cpp -o check_eclib_hecke -lec -lntl -lgivaro -lgmpxx -lgmp -lopenblas
#include <fflas-ffpack/fflas-ffpack.h>
#include <givaro/modular-balanced.h>
#include <eclib/homspace.h>

#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <vector>

using Field = Givaro::ModularBalanced<float>;

struct Equation {
    int level, modulus, dimension;
    int first_prime, first_value, second_prime, second_value;
    int expected_nullity = 0;
};

void check(const Equation& eq) {
    homspace symbols(eq.level, 1, 0, 0); // plus relative homology
    const int n = symbols.h1dim();
    if (symbols.h1denom() != 1 || n != eq.dimension)
        throw std::runtime_error("unexpected modular-symbol denominator or dimension");

    const Field field(eq.modulus);
    const int extra = std::min(160, n);
    std::vector<float> entries(static_cast<size_t>(n + extra) * n, field.zero);
    auto write_rows = [&](int prime, int value, int count, int offset) {
        for (int i = 0; i < count; ++i) {
            // A primal Hecke column is a row of its dual operator.
            auto coefficients = symbols.s_heckeop_col(prime, i + 1);
            auto* row = entries.data() + static_cast<size_t>(offset + i) * n;
            for (const auto& [j, coefficient] : coefficients)
                field.init(row[j - 1], coefficient);
            field.init(row[i], static_cast<long>(row[i]) - value);
        }
    };
    write_rows(eq.first_prime, eq.first_value, n, 0);
    write_rows(eq.second_prime, eq.second_value, extra, n);
    const auto rank = FFPACK::Rank(field, n + extra, n, entries.data(), n);
    std::cout << "level=" << eq.level << " modulus=" << eq.modulus
              << " T_" << eq.first_prime << "=" << eq.first_value
              << " T_" << eq.second_prime << "=" << eq.second_value
              << " stacked_rank=" << rank << "/" << n << std::endl;
    if (n - static_cast<int>(rank) != eq.expected_nullity)
        throw std::runtime_error("unexpected stacked rank");
}

int main() {
    // The level-11 cusp form has a_3 = -1 and a_5 = 1.
    check({11, 31, 2, 3, -1, 5, 1, 1});
    check({5344, 11, 676, 3, -4, 89, -3});
    check({5344, 11, 676, 3, 0, 89, -3});
    check({79072, 31, 11336, 5, -2, 683, -2});
    check({79072, 31, 11336, 5, 2, 683, -2});
}
