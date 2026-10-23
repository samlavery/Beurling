# Finite computations on ℕ (Section 5 of the paper)

`finite_checks.py` reproduces every finite computation on the integers that Section 5 (the noise section) quotes. It uses
ball arithmetic from python-flint 0.9.0 (Arb) and exact rationals. Run it from any directory, with a Python that has
python-flint installed, with

    python3 -I -B finite_checks.py

It prints one line per fact and the runtime (about 3 s). Each line gives the value (an Arb ball, or an exact rational),
where it is attained, the bound the paper uses, and the result of the comparison with that bound:

| line | quantity | paper |
|---|---|---|
| 1 | Lemma CM (i): max of (ψ(x) − ψ(x/2))/x over 1 ≤ x < 1500, and the analytic bound for x ≥ 1500 | 0.6803 at x = 5 (§5.2) |
| 2 | Lemma CM (ii): range of S(x) − log x on 1 ≤ x ≤ 10⁷, S(x) = Σ_{p^k ≤ x} log p/p^k | [−0.753, 0] (§5.2) |
| 3a | Lemma V, small heights: max of Σ_{Y<n≤2Y} 1/n over 72 ≤ Y < 10⁴, and log 2 + 10⁻⁴ for Y ≥ 10⁴ | 0.69659 and 0.6933 (§5.2) |
| 3b | Lemma V, small heights: max of the same sum over 1 ≤ Y < 72, in exact rationals | 5/6 ≤ 0.8334 (§5.2) |
| 4 | F_{1/2}: max of y^{−1/2} Σ_{n≤y} μ²(n) n^{−1/2} over 1 ≤ y ≤ 10⁶ | 1.32964 at y = 7 (§5.8) |
| 5 | threshold-mass lemma: max over primes p < 400 of Π_{q<p}(1 − 1/q)^{−1} − 1.8 log p, exact products | ≤ 0.25 (§5.7) |
| 6 | Lemma CM (iii): Σ_p log p/(p(p − 1)), partial sum to 10⁷ plus an explicit tail bound | 0.75537 (§5.2) |

Each supremum over a real variable is reduced to finitely many points by the step structure described in the comment
above the corresponding check. Line 3b and the products of line 5 are exact rationals; every other quantity is an Arb
ball, and each comparison with the bound used in the paper is decided on the ball.

Expected output:

    1  CM(i), N, 1<=x<1500: max (psi(x)-psi(x/2))/x = [0.68023948 +/- 3.67e-9] at x = 5 (paper: 0.6803 <= 0.71): True; x>=1500: 0.71x - (x log2 + 3log x + 3) = [0.339568 +/- 1.21e-9] at x=1500, derivative >= [0.01485 +/- 2.82e-6] for x>=1500: True
    2  CM(ii), N, 1<=x<=1e7: S(x)-log x in [[-0.75203870 +/- 1.62e-9], 0]; inf approached as x -> 3-, sup at x = 1 (paper: [-0.753, 0]): True; 665134 prime powers
    3a Lemma V, N, 72<=Y<1e4: max sum_{Y<n<=2Y} 1/n = [0.69658357 +/- 3.91e-9] for Y in [72.5, 73.0) (paper: 0.69659 <= C0 = 0.70): True; Y>=1e4: log2 + 1e-4 = [0.69324718 +/- 5.61e-10] (paper: 0.6933): True
    3b Lemma V, N, 1<=Y<72: max sum_{Y<n<=2Y} 1/n = 5/6 for Y in [1.5, 2.0), exact (paper: 0.8334): True
    4  F_{1/2}, N, 1<=y<=1e6: max y^{-1/2} sum_{n<=y} mu^2(n) n^{-1/2} = [1.3296349 +/- 4.90e-8] at y = 7 (paper: 1.32964 <= 1.33): True
    5  Lemma threshold-mass, primes p<400: max prod_{q<p}(1-1/q)^{-1} - 1.8 log p = [0.24736173 +/- 1.71e-9] at p = 7 (paper: <= 0.25): True
    6  CM(iii), rational primes: sum log p/(p(p-1)) <= [0.75536651 +/- 8.30e-10] + [1.71e-6 +/- 1.81e-9] = [0.75536822 +/- 2.64e-9] (paper: 0.75537): True
    runtime 2.9 s

The value on the runtime line varies.
