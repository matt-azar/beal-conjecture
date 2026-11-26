// Replay the finite checks for the two curves in docs/local-points.md.
// Bounds below are fixed: all modular products fit in a signed 64-bit integer.
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Integer = std::int64_t;
constexpr Integer d = 2471;
constexpr Integer p = 31;
constexpr Integer bound = 2731 * 2731;

Integer mod_power(Integer base, Integer exponent, Integer modulus)
{
    Integer result = 1;
    while (exponent > 0)
    {
        if (exponent % 2 == 1)
            result = result * base % modulus;
        base = base * base % modulus;
        exponent /= 2;
    }
    return result;
}

// Tonelli–Shanks for a nonzero square n at an odd prime q.
Integer square_root(Integer n, Integer q)
{
    Integer s = 0, odd_part = q - 1;
    while (odd_part % 2 == 0)
    {
        ++s;
        odd_part /= 2;
    }
    if (s == 1)
        return mod_power(n, (q + 1) / 4, q);
    Integer nonsquare = 2;
    while (mod_power(nonsquare, (q - 1) / 2, q) == 1)
        ++nonsquare;
    Integer c = mod_power(nonsquare, odd_part, q);
    Integer root = mod_power(n, (odd_part + 1) / 2, q);
    Integer t = mod_power(n, odd_part, q);
    while (t != 1)
    {
        Integer i = 0, v = t;
        while (v != 1)
        {
            v = v * v % q;
            ++i;
        }
        Integer f = mod_power(c, Integer(1) << (s - i - 1), q);
        root = root * f % q;
        c = f * f % q;
        t = t * c % q;
        s = i;
    }
    return root;
}

// x + y*s, with s^2 = -2471, in the inert residue field.
struct Element
{
    Integer x, y;
};

Element multiply(Element a, Element b, Integer q)
{
    Integer real = (a.x * b.x % q + q - d * (a.y * b.y % q) % q) % q;
    return {real, (a.x * b.y + a.y * b.x) % q};
}

Element field_power(Element a, Integer exponent, Integer q)
{
    Element result{1, 0};
    while (exponent > 0)
    {
        if (exponent % 2 == 1)
            result = multiply(result, a, q);
        a = multiply(a, a, q);
        exponent /= 2;
    }
    return result;
}

std::pair<Integer, Integer> eta_coefficients(Integer m)
{
    Integer half = (m + 1) / 2;
    return {90621 * half % m, 391 * half % m};
}

std::pair<Integer, Integer> eta_values(Integer m, Integer root, Integer k)
{
    auto [real, imag] = eta_coefficients(m);
    Integer offset = imag * root % m;
    return {mod_power((real + offset) % m, k, m),
            mod_power((real + m - offset) % m, k, m)};
}

bool split_unit_witness(Integer q, Integer root, Integer a, Integer k)
{
    auto [plus, minus] = eta_values(q, root, k);
    Integer shift = a * root % q;
    for (Integer b = 0; b <= (q - 1) / 2; ++b)
    {
        Integer square = b * b % q;
        Integer left = plus * ((square + shift) % q) % q;
        Integer right = minus * ((square + q - shift) % q) % q;
        if (mod_power(left, (q - 1) / p, q) == 1 &&
            mod_power(right, (q - 1) / p, q) == 1)
            return true;
    }
    return false;
}

bool inert_unit_witness(Integer q, Integer a, Integer k)
{
    auto [real, imag] = eta_coefficients(q);
    Element factor = field_power({real, imag}, k, q);
    for (Integer b = 0; b <= (q - 1) / 2; ++b)
    {
        Element value = multiply(factor, {b * b % q, a}, q);
        Element character = field_power(value, (q * q - 1) / p, q);
        if (character.x == 1 && character.y == 0)
            return true;
    }
    return false;
}

void check_683(Integer x, Integer k, Integer expected)
{
    constexpr Integer q = 683, root = 332;
    if ((root * root + d) % q != 0)
        throw std::runtime_error("Invalid root at 683");
    auto [plus, minus] = eta_values(q, root, k);
    Integer shift = mod_power(d, (x - 1) / 2, q) * root % q;
    std::vector<Integer> surviving;
    for (Integer b = 0; b < q; ++b)
    {
        Integer left = plus * ((b * b + shift) % q) % q;
        Integer right = minus * ((b * b + q - shift) % q) % q;
        if ((left == 0 || mod_power(left, (q - 1) / p, q) == 1) &&
            (right == 0 || mod_power(right, (q - 1) / p, q) == 1))
        {
            if ((left == 0) == (right == 0))
                throw std::runtime_error("Expected exactly one zero component");
            surviving.push_back(b);
        }
    }
    if (surviving != std::vector<Integer>{expected, q - expected})
        throw std::runtime_error("Unexpected residue of b at 683");
    std::cout << "q=683, x=" << x << ", b = +/-" << expected << '\n';
}

void check_31(Integer x, Integer k, Integer b, Integer y1, Integer y2)
{
    constexpr Integer m = 961, root = 90;
    if ((root * root + d) % m != 0)
        throw std::runtime_error("Invalid root modulo 961");
    Integer shift = mod_power(d, (x - 1) / 2, m) * root % m;
    auto [plus, minus] = eta_values(m, root, k);
    if (y1 % p == 0 || y2 % p == 0 ||
        mod_power(y1, p, m) != plus * ((b * b + shift) % m) % m ||
        mod_power(y2, p, m) != minus * ((b * b + m - shift) % m) % m)
        throw std::runtime_error("Invalid unit witness at 31");
}

int main()
{
    check_31(5, 23, 425, 10, 27);
    check_31(67, 8, 461, 25, 13);
    check_683(5, 23, 26);
    check_683(67, 8, 298);

    std::vector<bool> prime(bound, true);
    for (Integer q = 2; q * q < bound; ++q)
        if (prime[q])
            for (Integer j = q * q; j < bound; j += q)
                prime[j] = false;
    Integer good = 0, split = 0, inert = 0;
    for (Integer q = 3; q < bound; q += 2)
    {
        if (!prime[q] || q == 7 || q == 353 || q == p)
            continue;
        ++good;
        if (q % p != 1 && q % p != p - 1)
            continue;
        Integer n = q - d % q;
        bool splits = mod_power(n, (q - 1) / 2, q) == 1;
        if (splits && q % p != 1)
            continue;
        Integer root = splits ? square_root(n, q) : 0;
        if (splits && root * root % q != n)
            throw std::runtime_error("Invalid split root");
        if (splits)
            ++split;
        else
            ++inert;
        if (q == 683)
            continue; // check_683 handles the necessary nonunit residues.
        for (auto [x, k] : {std::pair{5, 23}, std::pair{67, 8}})
        {
            Integer a = mod_power(d, (x - 1) / 2, q);
            bool found = splits ? split_unit_witness(q, root, a, k)
                                : inert_unit_witness(q, a, k);
            if (!found)
            {
                std::cerr << "No unit witness at q=" << q << ", x=" << x << '\n';
                return 1;
            }
        }
    }
    if (good != 505656 || split != 8420 || inert != 16819)
        throw std::runtime_error("Unexpected good-prime coverage");
    std::cout << good << " good primes below " << bound << "; "
              << split << " split and " << inert << " inert cases requiring tests.\n";
}
