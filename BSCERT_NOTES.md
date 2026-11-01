# The Beurling–Saias certificates (Appendix B.1) in Lean

This note explains how the uploaded certificate scripts correspond to the Lean files in
`RequestProject/BSCert/`.

| Script | What it certifies | Lean theorem |
| --- | --- | --- |
| `cert_run_arb_patched.py` / `cert_run_arb.py` + `bs_cert_arb.py` + `ivarb.py` | region Z2: for `3·10⁹ ≤ ℓ ≤ 10¹⁸` and `2 ≤ u ≤ Ū(ℓ)`, `r(u-1) > γ₁`, `r(u-1) > γ_max` and `S(ℓ,u) > 0` | `BSCert.Z2.z2_certificate` (`Z2Cert.lean`) |
| `aux_cert_arb.py`, check (1) | `c₀(u)/(K'u²)` bracket `> log(1+u)` on `[27, 4·10⁵]` | `BSCert.cA_certificate` (`AuxCert.lean`) |
| `aux_cert_arb.py`, check (2) | left side of (28) of Lemma 5.3 (no `X(u)`), `L_z = max(100,u)`, positive on `[1, 10⁶]` | `BSCert.lemV_certificate` |
| `aux_cert_arb.py`, check (3) | left side of (28) at `L_z = 100` with `X(u)` and `2K_M r(u)(e^{0.141}-1)`, positive on `[1, 2]` | `BSCert.lemVExt_certificate` |

The binary64 scripts `bs_cert.py`, `cert_run.py` and `aux_cert.py` check the same inequalities,
so the theorems above cover them too.

## Statements

The real-valued quantities follow the paper (Step 7(iii) of the proof of Theorem 5.6, and
Lemma 5.3) and use the same names as `S_cell`:
* `Z2Defs.lean`: `u0`, `Ubar`, `betaI`, `betaII`, `alpha`, `gamma1`, `gammaMax`, `qq`,
  `eta`, `Mm1`, `E1`, `E2`, `E3`, `aV`, `ET`, `T` and `S`.
* `AuxDefs.lean`: `cAMargin`, `lemVLHS`, `lemVExtLHS`.

Dickman's function is not in Mathlib. Every theorem therefore takes an arbitrary function `r`
and the hypothesis `DickmanRatioFacts r` (`Dickman.lean`). This hypothesis collects exactly
the facts the scripts use:
* (R2): `r` is non-decreasing on `[1, ∞)`;
* the exact formula `r(x) = 1/(x(1 - log x))` on `[1, 2]`;
* (R3): `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})` for `v ≥ 3`;
* (R4): `r(x) ≤ log((x+1)/δ)/(1-δ)` for `x ≥ 2` and `0 < δ < 1`.

No axioms are added. Besides the standard axioms, the theorems depend only on
`Lean.ofReduceBool` and `Lean.trustCompiler`, which come from `native_decide`.

## How the computation is verified

* `Interval.lean`, `Transc.lean`: interval arithmetic with rational endpoints and outward
  rounding.
  - `exp` uses a Taylor polynomial with Mathlib's remainder bound `Real.exp_bound`, then
    repeated squaring.
  - `log` and `sqrt` start from floating-point guesses and then check them exactly: for `log`
    through the certified `exp`, for `sqrt` by squaring. The floats only suggest candidate
    values; no bound depends on them.
* `Expr.lean`: a small expression language with `let`. The theorem `Ex.ieval_sound` proves
  that interval evaluation encloses the real value.
* `Dickman.lean`: the table of lower bounds `r_low`, built from (R3) starting at `r(2)`, and
  the upper bound `r_up` from (R4). `rEnc_sound` proves that these enclose `r(u)` on every
  cell.
* `Cover.lean`: coverage of an interval by checked cells, with optional bisection
  (`cover_sound`).
* `Z2Ex.lean`: `z2Ex_eval` proves that the expression evaluated on each cell is exactly the
  real-valued claim.
* `Z2Cells.lean`: the cell layout of `cert_run_arb.py`.
  - Bands in `ℓ` have ratio 1.05.
  - `u`-cells cover `[2, max(40, u₀/2)]`.
  - `v`-cells, in the variable `v = u - ℓ^{1/4}`, cover the rest up to `Ū(ℓ)`.
  - The seams between the two kinds of cells, and the top edge, are bounded over each whole
    band with interval arithmetic.
* `Z2Chunks/C00.lean` … `C31.lean`: the 403 bands, split into 32 pieces. Each piece is checked
  by `native_decide`. Every cell passes on its first evaluation, with no bisection.
  `Z2Cert.lean` glues the 32 pieces together.

## Differences from the scripts

None of these changes what is certified:
* The real-valued `S` uses the true values `r(u)` and `r(u-1)` throughout. In a few places the
  script uses only a one-sided bound for them; that is simply a weaker form of the same
  enclosure.
* In `E_T`, the first branch writes `(U₃₀ - u)₊`, as the script does. On that branch it equals
  `U₃₀ - u`.
* In check (2), `E*` is written with the true `r(u-1)` (`max(1/2, 1 - 1/r(u-1))` for `u ≥ 2`)
  instead of `r_low(u-1)`. This is the quantity the proof of Lemma 5.3 uses. The script's
  version with `r_low` implies it, because the left side increases with `r(u-1)`.
* Lean's cells use its own rational grid of the same shape, not the script's floating-point
  endpoints.

## What is not formalized

* The reduction `S ≤ Σ` (the analytic part of Theorem 5.6).
* The analytic ranges beyond the certified intervals.
* The Dickman facts themselves; these are hypotheses.

# The capacity-theorem scripts (Appendix B.5, `capl-cert`) in Lean

Appendix B.5 of the paper says that `rankin_R.py` is a step of the proof, of Lemma 6.22(c),(e).
The other scripts in that directory are floating-point cross-checks of the analytic proof of
Theorem 6.23. They are not interval-certified, and the proof does not depend on them.

## `rankin_R.py` (proof step; fully formalized)

| Check | Lean theorem |
| --- | --- |
| (1) `R(0.69) ≤ 0.77` | `BSCert.Rankin.R_069_le` (`RankinCert.lean`) |
| (1) `R(0.75) ≤ 0.63` | `BSCert.Rankin.R_075_le` |
| (2) `Ei(11) - e¹¹/11 - e¹¹/121 ≤ 134` | `BSCert.EiFn.Ei_11_le` (`EiCert.lean`) |
| (2) `2.75/x + 134x²e^{-x} < 1`, proved for every `x ≥ 11` | `BSCert.EiFn.f_lt_one` |
| consequence: `Ei(x) ≤ (eˣ/x)(1 + 2/x)` for `x ≥ 11` | `BSCert.EiFn.Ei_le_of_ge_11` |
| (3) `(3/2)^{3/4} ≤ 1.3555` | `BSCert.EiFn.three_halves_rpow_le` |
| (3) `Ei(log 2 / 4) ≥ -1` | `BSCert.EiFn.Ei_log2_div4_ge` |

Definitions:
* `R(σ) = ∑_p (-log(1 - p^{-σ}) - p^{-σ})` is a `tsum` over `Nat.Primes` (`Rankin.lean`).
  `summable_rTerm` proves that the series converges for `σ > 1/2`, so the bound is not about a
  junk value.
* `Ein(x) = ∫₀ˣ (eʷ - 1)/w dw` is the paper's definition. `Ei(x) = γ + log x + Ein(x)` is the
  classical identity for `x > 0`; `γ` is Mathlib's `Real.eulerMascheroniConstant` (`Ei.lean`).
  Lean also proves `Ei'(x) = eˣ/x` for `x > 0`.

How the bounds are proved:
* `R(σ)`: every prime `p ≤ 10⁵` is handled by exact rational arithmetic.
  - `p^{-a/b} ≤ x` is certified by `x^b p^a ≥ 1`.
  - `-log(1-x) - x` is bounded by a Taylor polynomial with Mathlib's remainder bound.
  - The primes `p > 10⁵` use the proved bound `(1/2 + δ/(1-δ)) p^{-2σ}` and a telescoping sum
    over the odd integers.
  - The script instead sums to `10⁷` and bounds the tail over all integers. Lean's totals are
    about `0.766` and `0.622`.
* `Ein`: Taylor polynomials of `exp` give an enclosure, integrated exactly. `γ` is bounded
  below by Mathlib's `H₁₀₂₃ - log 1024 < γ` and above by `γ < 2/3`.

## The cross-check scripts: the claims they test, proved for all parameters

`Capl.lean` defines `A(Λ,s)`, `G(Λ,s)`, `Λ_s`, `γ*(s)` and `γ(s)` exactly as in Theorem 6.23.

| Script | What it tests numerically | Lean theorem (all real parameters in range) |
| --- | --- | --- |
| `analytic_capl.py`, `caplw_check_independent.py`, `raise_max.py` | `s_H = 5.9745…`, the root of `γ*(s_H) = 1/3 - 10⁻⁵` | `BSCert.Capl.sH_spec`: the root in `[0,10]` exists, is unique, and lies in `(5.9745, 5.9746)` (`CaplSH.lean`) |
| `analytic_capl.py` (sample `s`), `caplw_check_independent.py` Step 1 | `G(Λ,s)` decreases in `Λ` | `BSCert.Capl.G_antitone`: for `Λ₁ ≥ 10⁸`, `-log Λ₁ ≤ s ≤ 60`, `Λ₁ ≤ Λ₂` (`CaplChecks.lean`) |
| `caplw_check_independent.py` Step 2 | high-degree-row criterion `(1+j)·gain ≥ L + 10ℓ + 10` | `BSCert.Capl.step2`: for `Λ ≥ 10⁸`, `-log Λ ≤ s ≤ s_H + 1` (`CaplStep2.lean`) |
| `caplw_check_independent.py` Dickman rows | `(1+j)·g/L ≥ 1.001` | `BSCert.Capl.step3`: for `Λ ≥ 10⁸`, `s > s_H + 1`, `ℓ ≤ 0.3Λ` (`CaplStep3.lean`) |
| `caplw_check_independent.py` Step 5 | `eˢ log(Λeˢ/(8·3.01γ)) ≥ 107.6γ²` | `BSCert.Capl.step5`: for `Λ ≥ 10⁸`, `s ≥ 5.9745`, `0 < γ ≤ 7.5` |
| `raise_max.py` | `max(0, 2 log M̄₁ - 8ℓ²)/L ≤ 10⁻⁶` | `BSCert.Capl.raise_le_at_sH`: for every `Λ ≥ 10⁸` and `s ≥ -log Λ` (`CaplRaise.lean`) |

Here `s_H` is the true root from `sH_spec`, not the floating-point value. The scripts sample
finite grids or random points; these theorems cover the whole ranges (for `raise_max.py` the
script samples `Λ ∈ [10⁸, 10³⁰]`, `s ≤ 30`, and the theorem covers all `Λ ≥ 10⁸`, `s ≥ -log Λ`).
The proofs follow the paper's analytic arguments. The only computer checks are a few
rational inequalities and interval evaluations, which `native_decide` checks.

Not formalized:
* the "precise-model" grid checks in `capl_model.py`, used by `analytic_capl.py` (its third part)
  and `cert_capl.py`. These evaluate finer criteria: a degree cap `D*` found by bisection,
  `j_of`, and condition (81) with the exact absorption threshold. They do so at discrete points
  or cells in floating point. The paper calls `cert_capl.py` superseded, and says the proof
  uses only the analytic bounds above.
* `needs.py`: a diagnostic that prints values and checks nothing.
* the combinatorial and probabilistic parts of Theorem 6.23 itself (the reduction to these
  inequalities).

# The Section 5 and Appendix A certificates (Appendix B.2, B.3, B.6, B.7) in Lean

No axioms are added. Besides the standard axioms, the theorems that use computation depend only
on `Lean.ofReduceBool` and `Lean.trustCompiler`, which come from `native_decide`; the
linear-algebra theorems use no computation at all.

## `finite_checks.py` (Appendix B.2, a step of the proof)

All files are in `RequestProject/BSCert/Finite/`. Every statement is about the real quantity of
the paper, over the whole real range the script reduces to finitely many points.

| Line | What the paper uses | Lean theorem |
| --- | --- | --- |
| 1 | `ψ(x) - ψ(x/2) ≤ 0.6803 x` for `1 ≤ x < 1500` | `BSCert.FiniteN.psi_sub_psi_half_le_small` (`CMCert.lean`) |
| 1 | `x log 2 + 3 log x + 3 < 0.71 x` for every `x ≥ 1500` (the script checks `x = 1500` and the derivative) | `BSCert.FiniteN.cm1_tail` (`CM.lean`) |
| 2 | `-0.753 ≤ S(x) - log x ≤ 0` for `1 ≤ x ≤ 10⁷`, `S(x) = ∑_{p^k ≤ x} log p / p^k` | `BSCert.FiniteN.mertensS_sub_log_mem` (`CMCert.lean`) |
| 3a | `∑_{Y<n≤2Y} 1/n ≤ 0.69659` for `72 ≤ Y < 10⁴` | `BSCert.FiniteN.harmWin_le_mid` (`SmallCert.lean`) |
| 3a | `∑_{Y<n≤2Y} 1/n ≤ log 2 + 10⁻⁴ ≤ 0.6933` for every `Y ≥ 10⁴` (the script only evaluates `log 2 + 10⁻⁴`) | `BSCert.FiniteN.harmWin_le_large'` |
| 3b | `∑_{Y<n≤2Y} 1/n ≤ 5/6` for `1 ≤ Y < 72`, attained at `Y = 3/2` | `BSCert.FiniteN.harmWin_le_five_sixths`, `harmWin_three_halves` |
| 4 | `y^{-1/2} ∑_{n≤y} μ²(n) n^{-1/2} ≤ 1.32964` for `1 ≤ y ≤ 10⁶` | `BSCert.FiniteN.F12_le` |
| 5 | `∏_{q<p} (1-1/q)⁻¹ - 1.8 log p ≤ 0.25` for every prime `p < 400` | `BSCert.FiniteN.threshold_mass_small` |
| 6 | `∑_p log p / (p(p-1)) ≤ 0.75537` (the series converges) | `BSCert.FiniteN.sum_log_div_prime_le` (`CMCert.lean`) |

Consequence (`ChebN.lean`): Lemma 5.1(i) for `ℕ` in full, `ψ(x) - ψ(x/2) ≤ 0.71x` for all
`x ≥ 1` (`psi_sub_psi_half_le`) and `ψ(x) ≤ 1.42x` for all `x ≥ 0`
(`psi_le_one_point_four_two`). For the analytic range the paper cites Stirling,
`ψ(x) - ψ(x/2) ≤ x log 2 + 3 log x + 3`; Lean proves the stronger
`ψ(x) - ψ(x/2) ≤ x log 2 + log x` with the classical Chebyshev argument
(`log m! = ∑_{d≤m} Λ(d)⌊m/d⌋` and `C(2k+1, k) ≤ 4^k`).

Definitions: `ψ` is Mathlib's `Chebyshev.psi`; `mertensS x = ∑_{n ≤ x} Λ(n)/n` (this equals the
paper's sum over prime powers); `harmWin Y` is the sum over `{n ∈ ℕ : Y < n ≤ 2Y}`;
`F12 y = (√y)⁻¹ ∑_{n ≤ y} μ(n)²/√n`.

How the computation is verified:
* `LogTab.lean`: fixed-point integers `a / 2^50`. A table of certified enclosures of
  `log(i/4096)` for `4096 ≤ i ≤ 8192` is built from `logLoPt`/`logHiPt` of `Transc.lean`;
  `logLoN`, `logHiN` enclose `log n` by splitting off a power of 2 (`logLoN_spec`,
  `logHiN_spec`). `ppBase` computes `Λ` exactly (`vonMangoldt_eq_ppBase`).
* `Loop.lean`: a running-sum loop with checked lower and upper fixed-point bounds
  (`sumLoop_spec`). Lines 2, 4 and 6 run it over every integer up to `10⁷`, `10⁶` and `10⁷`.
* Line 1 sums the upper bounds of `Λ` over `(N/2, N]` for each `N < 1500`. Line 3a uses an
  exact integer recurrence for the window sums of `⌈2^50/n⌉`; line 3b uses exact rationals.
  Line 4 bounds `1/√n` by the least integer `u` with `u² n ≥ 4^50`. Line 5 uses exact rational
  products.
* Line 6: the primes `p ≤ 10⁷` are summed with fixed-point upper bounds, and the tail is bounded
  by the telescoping majorant `log n/(n(n-1)) ≤ F(n-1) - F(n)`, `F(n) = (log n + 2)/n`, over all
  integers `n > 10⁷`; the total is `≤ 0.7553683`.

## `x0band_exact.py` (Appendix B.3, a step of the proof)

`X0Band.lean`, `X0BandCert.lean`. `Bx n` is `B(n)` of Proposition 5.31(i), defined exactly
(a rational number), with `Hord` (ordered factorisations) and `X` as in the paper.

| Claim | Lean theorem |
| --- | --- |
| `B(n) ≤ 5/12` for `2 ≤ n ≤ 10⁶`, strictly unless `n = 6` | `BSCert.X0Band.Bx_le_five_twelfths` |
| `B(6) = 5/12` | `BSCert.X0Band.Bx_six` |
| the analytic tail `(1/2 + 1.64√n)/n + (1/4)·7.4915·2^{0.2}n^{-0.2} ≤ 0.1375` for every `n ≥ 10⁶` (the script prints its value at `n = 10⁶`) | `BSCert.X0Band.x0_tail_bound` |

The check is exact: `20000 n (μ²(n) + ∑_d (2μ²(d) + λX(d)/(2d)))` is an integer, so `B(n) ≤ 5/12`
is decided by integer arithmetic, with no rounding and no `1 + 10⁻⁹` inflation (`Bx_eq`).
`fdivs` computes divisors from the factorisation (`fdivs_eq`), and `H_ord`, `X` are tabulated
(`hArr_spec`, `xArr_spec`). The constant `7.4915` comes from Appendix B.4 and is certified by
`BSCert.Consts.ordA_x1_le` (see below).

`x0band.py` is, by the paper, an earlier floating-point exploration that is not part of the
certificate; it checks nothing and is not formalized.

## `sc_check.py`, `sc_greedy.py`, `sc_check_independent.py` (Appendix B.6, Lemma A.8)

The paper proves Lemma A.8 in Appendix A; the scripts test it on random integer matrices. Lean
proves the lemma itself, for every matrix over any field (`StageRows.lean`):

| Claim | Lean theorem |
| --- | --- |
| Lemma A.8 (1)–(3), for a rank-full `E`, any cover `C`, any row order with the rows of `C` first, and the lexicographically first bases `R≤t` | `BSCert.StageRows.lemmaA8` |
| the explicit construction of `sc_greedy.py` is this one (`rkCFirst` is the order "rows of `C` first") | `rkCFirst_injective`, `rkCFirst_first` |
| greedy pivots: `IsPivot` (not in the span of the later columns) is the paper's rule (not in the span of the later pivots) | `BSCert.StageRows.isPivot_iff_greedy` |
| Remark A.9 / the `advfail` count of `sc_check_independent.py`: with the rows of `C` last, (3) can fail (explicit `2 × 3` example) | `BSCert.StageRows.order_matters` (`StageRowsOrder.lean`) |

Statement details: columns are indexed latest first (column `0` is the latest decided); runs
are the maximal sets of consecutive pivots (`RunStart`), and `stageOf j` is the number of runs
starting at or before `j`, so `P≤t ∪ F≤t = {j : stageOf j ≤ t}` (`upTo`). `R≤t` is
`rowsUpTo E rk t`. "Invertible" is stated as the existence of a two-sided inverse of
`E_{R≤t,P≤t}` (its rows and columns are indexed by the different sets `R≤t` and `P≤t`).
Conclusion (3) is stated for non-zero columns, i.e. columns that are primes occurring in `B'`
(the scripts remove zero columns). Lean's proof of (3) differs slightly from the paper's: a row
`y ∈ C` outside `R≤t` is a combination of rows of `R≤t` listed before it, and these are all in
`C`.

## `svl_stress.py` (Appendix B.7, structural facts of Theorem A.10)

`SVLFacts.lean`, for every matrix with natural-number entries, with `C` = all rows and the
natural row order (which is how the script builds the stage rows):

| Check | Lean theorem |
| --- | --- |
| C1: the stage rows exist, are nested, and `R≤t` has as many rows as `P≤t` has columns | `lemmaA8` (1), (2) |
| C2: every pivot column of `P≤t` has mass `≥ 1` on `R≤t` | `BSCert.StageRows.svl_C2` |
| C3: every non-zero late free column of `F≤t` is non-zero on `R≤t` | `BSCert.StageRows.svl_C3` |
| C4/C5: a column of `P≤t ∪ F≤t` equals `E_{·,P≤t} E_{R≤t,P≤t}⁻¹ e_{f,R≤t}` on every row | `BSCert.StageRows.svl_C4_C5` (general form: `col_determined`) |
| C6: `det E_{R≤t,P≤t}` is a non-zero integer | `BSCert.StageRows.svl_C6` |

As in the script, the identity of Theorem A.10 itself is not formalized.

# The numerical constants (Appendix B.4: `consts.py`, `phi_bounds.py`) in Lean

All files are in `RequestProject/BSCert/Consts/`. No axioms are added. Besides the standard
axioms, the theorems that use computation depend only on `Lean.ofReduceBool` and
`Lean.trustCompiler`, which come from `native_decide`.

## Definitions

* `ζ` is Mathlib's `riemannZeta`. For real `s > 1`, `zetaR s = ∑_{n ≥ 1} n^{-s}` and
  `zetaDR s = ∑_{n ≥ 1} log n · n^{-s}`, with `riemannZeta s = zetaR s`
  (`riemannZeta_eq_zetaR`) and `deriv riemannZeta s = -zetaDR s` (`deriv_riemannZeta_eq`)
  (`ZetaSeries.lean`).
* `ordA s = 1/(2 - ζ(s)) - 1` (the script's `A(s)`) and `ordA1 s = -ζ'(s)/(2 - ζ(s))²`
  (`ZetaCert.lean`). `OrdFact.lean` proves that these are the paper's sums over ordered
  factorisations (`H_ord` is `BSCert.X0Band.Hord`, as in `x0band_exact.py`):
  - `hasSum_Hord`: `∑_{m ≥ 1} H_ord(m) m^{-s} = 1/(2 - ζ(s))` for real `s > 1` with `ζ(s) < 2`;
  - `ordA_eq_tsum`: `ordA s = ∑_{m ≥ 2} H_ord(m) m^{-s}`;
  - `tsum_Hord_log`: `∑_{m ≥ 1} H_ord(m) m^{-s} log m = ordA1 s` when `1 < s₁ < s` and `ζ(s₁) < 2`.
* `I1`, `I2`, `I3`, `c3` (`MarginCert.lean`), with `U = Uf v = 1 + 2 log v`; `Ein` is the
  paper's `∫₀ˣ (eʷ - 1)/w dw` (`Ei.lean`); `γ` is Mathlib's `Real.eulerMascheroniConstant`.
* `phiCut` is the cutoff `ϕ` of (1), defined from `ψ` as in the paper; it equals Mathlib's
  `Real.smoothTransition` (`phiCut_eq`), which gives smoothness (`PhiDefs.lean`).

## `consts.py`

| Line | Claim | Lean theorem |
| --- | --- | --- |
| k1 | `ζ(1.7286) > 2 > ζ(1.7287)` | `BSCert.Consts.zeta_bracket` |
| k1 | `ζ(ρ) = 2` has exactly one root `ρ₀ > 1`, and `ρ₀ ∈ (1.7286, 1.7287)` | `rho0_spec`, `rho0_mem` |
| k2 | `A₀(0.03) = A(1.97) ≤ 2.07` | `ordA_197_le`; as the `H_ord` series: `Hord_sum_197_le` |
| k3 | `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.42` | `ordA1_197_le`; as the `H_ord log` series: `Hord_log_sum_197_le` |
| k4 | `ζ(1.8) + 10⁻³⁰ ≤ 1.883` | `zeta_18_le` |
| k5 | `1/(2 - 1.883) ≤ 8.6`, i.e. `∑ H_ord(m) m^{-1.8} ≤ 8.6` for `N = ℕ` | `k5`, `Hord_sum_18_le` |
| x1 | `A(1.8 - 3·10⁻⁶) ≤ 7.4915` | `ordA_x1_le`; series form `Hord_sum_x1_le` |
| x2 | `(1/4) · 7.4915 · 2^{0.2} ≤ 2.152` | `x2` (`XBandConsts.lean`) |
| x3 | `2^{ω(n)} ≤ (4/√6)√n` for every `n ≥ 1`, and `4/√6 ≤ 1.64` | `x3` |
| x4 | `(1/2 + 1.64√n)/n + 2.152 n^{-0.2} ≤ 0.14` for every `n ≥ 10⁶` | `x4`; with x2: `x0_tail_le` |
| x5 | `A(1.77) ≤ 13.1` (and `ζ(1.77) < 2`) | `ordA_177_le`; series form `Hord_sum_177_le` |
| x6 | `ζ(1.97) - 1 ≤ 0.674` | `zeta_197_sub_one_le` |
| x7 | `-ζ'(1.97) ≤ 1.0001` | `zetaD_197_le`, `neg_deriv_riemannZeta_197_le` |
| m1 | `3.6838 < Ein(2) < 3.69` | `Ein_two_bounds` (`MarginCert.lean`) |
| m2 | `I₁ = 16 log 2 + 3.825 ≤ 14.92` | `I1_eq`, `I1_le` |
| m3 | `I₂ ≤ 214.8`, and the integrand is integrable on `(4, ∞)` | `I2_le` |
| m4 | `I₃ ≤ 6.7`, and the integrand is integrable on `(4, ∞)` | `I3_le` |
| m5 | `(2.02/log 2)(I₁ + I₂ + I₃) ≤ 690` | `margin_total_le` |
| m6 | `690/Λ ≤ 7·10⁻⁶` for every `Λ ≥ 10⁸` | `m6` |

## `phi_bounds.py` and the analytic bound of (2)

| Claim | Lean theorem |
| --- | --- |
| `|ϕ''(t)| ≤ 10` for every real `t` | `BSCert.Consts.phiCut_deriv2_le` (`PhiCert.lean`) |
| `0 ≤ ϕ'(t) ≤ 2` for every real `t` (the analytic proof of (2); the script only cross-checks it to 2.001) | `phiCut_deriv_mem` |
| equality `ϕ'(1/2) = 2` | `phiCut_deriv_half` |

## How the computation is verified

* `ζ(s)`, `-ζ'(s)` (`ZetaItv.lean`): the first 3000 terms are enclosed with the certified
  `exp`/`log` of `Transc.lean` (`n^{-s} = exp(-s log n)`); the tails are bounded by integrals,
  `F(N+1) ≤ ∑_{n>N} f(n) ≤ F(N)` for a decreasing `f` with `F' = -f` (mean value theorem;
  `tail_le`, `le_tail`), with `F(x) = x^{1-s}/(s-1)` and
  `F(x) = x^{1-s}(log x/(s-1) + 1/(s-1)²)`. The script uses Arb's `ζ` instead.
* `I₂`, `I₃` (`IntCells.lean`): integer cells `[p, q]`, `q = p + max(1, ⌊p/8⌋)`, from `4` to beyond
  `10¹³`, and a tail. On each cell the integrand is bounded by `P(U)/v²` with `P` a polynomial
  of degree `≤ 4`, integrated exactly with `d/dv[-S_m(U)/v] = U^m/v²`,
  `S_m(U) = ∑_j 2^j m!/(m-j)! U^{m-j}` (for `m = 4` this is the script's
  `y⁴ + 8y³ + 48y² + 192y + 384`). For `I₂` the bound is the tangent line
  `log U ≤ log c + U/c - 1`; for `I₃` it is `1/U ≤ 3/c - 3U/c² + U²/c³` for `U ≥ c` (that is,
  `(U - c)³ ≥ 0`). `γ ≤ H_{10⁴} - log 10⁴` (Mathlib's `eulerMascheroniSeq'`) and
  `Ein(2)` from its Taylor polynomial. The script uses Arb's certified integration and the
  closed form `I₃ = c₃ (e^{1/2}/2) E₁(log 4 + 1/2)` instead.
* `ϕ''` (`PhiDefs.lean`, `PhiCert.lean`): the formulas `ϕ' = e^g q/(1+e^g)²`,
  `ϕ'' = e^g/(1+e^g)² (q' + q²(e^g-1)/(e^g+1))` on `(0,1)` are proved by differentiation. On
  `[0.02, 0.98]`, cells of width `10⁻³` (with bisection) are checked from monotone enclosures of
  `g`, `q`, `q'` and `e^g`. On `(0, 0.02]`, `|ϕ''| ≤ e^{-|g|}(q² + |q'|) ≤ 8e²x⁴e^{-x}` with
  `x = 1/t ≥ 50`, bounded with `eˣ ≥ x⁸/8!`; `[0.98, 1)` follows from `ϕ''(1-t) = -ϕ''(t)`.
  Outside `(0, 1)` `ϕ` is constant, and the points `0`, `1` follow by continuity of `ϕ'`, `ϕ''`.

## Not formalized

* The "precise-model" cross-checks (`capl_model.py`, the third part of `analytic_capl.py`,
  `cert_capl.py`) and `needs.py`, as before: the paper says they are floating-point
  cross-checks that the proof does not use (`cert_capl.py` is superseded and `needs.py` checks
  nothing). Their analytic counterparts are formalized (see the Appendix B.5 section).

# Using the certificates in the main proof

The certified constants are now used to remove hypotheses from the analytic part of the
development in `RequestProject/Beurling/`. No axioms are added. Besides the standard axioms, the
results depend only on `Lean.ofReduceBool` and `Lean.trustCompiler`, which come from
`native_decide` inside the certificates.

| Paper step | Certificates used | Lean theorem |
| --- | --- | --- |
| Theorem 6.23(c) for the jitter width `H = max(H_std, M̄₁²)`: `M̄₁² ≤ H`, `H_std ≤ H`, `log H - 8ℓ² ≤ 10⁻⁶ L` for all `x ≥ X₀`, `log X₀ ≥ 10⁸` | `raise_max.py` (`raise_le`), `s_H` (`sH_spec`) | `CaplLink.capH_conditions` (`PartICapl.lean`) |
| Theorem 2.1 / Corollary 2.2 from the refined hypothesis in which these three conditions are no longer assumed | as above | `corollary_2_2_of_capl`, `theorem21_of_capl` |
| Lemma 6.22(c), first part: the Euler-product estimate `log ∏_{p<X₀}(1-p^{-σ})^{-1} ≤ 1.42 log Λ + 1.42u + 5.5` | `R(0.69) ≤ 0.77`, `ψ(x) ≤ 1.42x`, `Ei(x) ≤ (eˣ/x)(1+2/x)` for `x ≥ 11` | `SmoothTails.euler_estimate` (`SmoothTailsCert.lean`) |
| Lemma 6.22(c), first part: `Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)` with no Euler-product hypothesis (for `X₀ ≥ 3`, `u ≥ max(10⁴, log Λ)`, `σ ≥ 0.69`) | as above | `SmoothTails.smooth_tail_rankin_cert` |
| Lemma 5.1(iii) for the rational primes, `1 ≤ x ≤ 10⁷`: `-1.50837 ≤ ∑_{p≤x} log p/p - log x ≤ 0` | `finite_checks.py` lines 2 and 6 | `Lemma51Nat.lemma_5_1_iii_nat` (`Lemma51Nat.lean`) |
| Lemma 5.1(iv) for the rational primes, `2 ≤ y ≤ x ≤ 10⁷`: `|∑_{y<p≤x} 1/p - log(log x/log y)| ≤ 1.50837/log y` | as above | `Lemma51Nat.lemma_5_1_iv_nat` |

Notes:
* `PartICapl.lean`: the capacity parameter is `s = log log x - 2 log Λ` with `Λ = log X₀`, so that
  `ℓ = 2 log Λ + s = log log x` and `L = e^ℓ = log x`. The range `s ≥ -log Λ` of `raise_max.py` is
  exactly `x ≥ X₀`. `M̄₁` is taken at the true break point `s_H` (the root from `sH_spec`). Only
  the queue bound `B ≤ 34 M̄₁ L²` (75) and the lag decomposition remain as hypotheses on `H`.
* `SmoothTailsCert.lean`: the paper uses the Rosser–Schoenfeld bound, which is not available
  here. With the certified `ψ(x) ≤ 1.42x` instead, the intermediate estimate has the constants
  `1.42 log Λ + 1.42u + 5.5` in place of `log Λ + 1.3u + 2`, but the final bound
  `Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)` is the paper's. The sum over primes is handled by partial
  summation against `θ(x) ≤ ψ(x) ≤ 1.42x`, compared with `F(t) = log log t + Ein(η log t)`, whose
  derivative is `t^{-σ}/log t`. The condition `σ ≥ 0.69` is the range of `R(0.69) ≤ 0.77`.
* `Lemma51Nat.lean`: the prime-power part `∑_{n≤x, n not prime} Λ(n)/n` is bounded by
  `∑_{p≤x} log p/(p(p-1)) ≤ 0.75537` (`nonprime_vonMangoldt_le`, `primePowerConst_le`). The range
  `x ≤ 10⁷` is the range of the certificate; the paper's analytic argument for larger `x` is not
  formalized.

# Dickman's function, Lemma 5.1 for ℕ in full, and Chebyshev's bound for Lemma 6.22(c)

No axioms are added. The Dickman files use no computation at all; the other results depend,
besides the standard axioms, only on `Lean.ofReduceBool` and `Lean.trustCompiler` (from
`native_decide` inside the `finite_checks.py` certificates they reuse).

## Dickman's function (Section 5.2, "Facts on Dickman's function")

`RequestProject/BSCert/DickmanFn.lean` constructs `ρ` (`Dickman.rho`), interval by interval, as
the continuous solution of `ρ(u) = 1` for `u ≤ 1` and `ρ(u) = 1 - ∫_1^u ρ(t-1)/t dt` for `u ≥ 1`.
`RequestProject/BSCert/DickmanRatio.lean` studies `r(v) = ρ(v-1)/(v ρ(v))` (`Dickman.ratio`).

| Paper fact | Lean theorem |
| --- | --- |
| `u ρ'(u) = -ρ(u-1)` for `u > 1` | `Dickman.hasDerivAt_rho` (integral form `Dickman.rho_eq`) |
| (R1) `v ρ(v) = ∫_{v-1}^v ρ` for `v ≥ 1` | `Dickman.mul_rho_eq_integral` |
| (R1) `∫_a^∞ ρ(w-1) dw/w = ρ(a)` for `a ≥ 1` | `Dickman.tendsto_integral_shift_div` |
| (R1) `∫_{u-1}^u ρ(w-1)(u-w) dw/w = ρ(u-1) - u ρ(u)` for `u ≥ 2` | `Dickman.integral_shift_mul_div` |
| `ρ > 0`, `ρ` non-increasing | `Dickman.rho_pos`, `Dickman.rho_antitone` |
| `r = 1/(v(1 - log v))` on `[1, 2]` | `Dickman.ratio_one_two` |
| (R2) `r` is increasing on `[1, ∞)` (strictly) | `Dickman.ratio_strictMonoOn` |
| (R3) `ρ(w)/ρ(u) ≤ e^{-r(u)(w-u)}` for `1 ≤ u ≤ w` | `Dickman.rho_le_exp` |
| (R3) `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})` for `v ≥ 2` | `Dickman.ratio_recursion` |
| (R4) `r(x) ≤ log((x+1)/δ)/(1-δ)` for `x ≥ 1`, `0 < δ < 1` | `Dickman.ratio_upper` |

The proof of (R2) is the paper's: with `I(v) = v ρ(v)/ρ(v-1) = 1/r(v)` one has
`I'(v) ρ(v-1) = ∫_{v-1}^v ρ(t)(r(v-1) - r(t)) dt` for `v > 2`, which is negative while `r` is
strictly increasing on `[v-1, v]`; a "first failure" argument with the supremum of the good
range then propagates strict monotonicity from `[1, 2]` to `[1, ∞)`.

Consequence (`RequestProject/BSCert/DickmanCert.lean`): `BSCert.dickmanRatioFacts :
DickmanRatioFacts Dickman.ratio`, so the hypothesis of the Appendix B.1 certificates is
discharged. `BSCert.z2_certificate_dickman`, `cA_certificate_dickman`,
`lemV_certificate_dickman` and `lemVExt_certificate_dickman` are the certificates for the true
Dickman ratio, with no hypothesis.

## Lemma 5.1(ii)–(iv) for the rational primes, for every `x`

`RequestProject/Beurling/Lemma51NatFull.lean`. The paper uses Rosser–Schoenfeld for
`10⁷ < x < X₀⁻`; Lean uses instead the identity (25) with `E₁ = 0`
(`N S(N) - ψ(N) ≤ log N! ≤ N S(N)`), Stirling's bounds from Mathlib's `Stirling.stirlingSeq`, and
`ψ(x) ≤ 1.42x`; for `x ≤ 10⁷` the certificate of `finite_checks.py` is used.

| Claim | Lean theorem |
| --- | --- |
| (ii) `-1.01 ≤ S(x) - log x ≤ 0.43` for all `x ≥ 1` | `Lemma51Nat.lemma_5_1_ii_nat` |
| (iii) `-1.77 ≤ ∑_{p ≤ x} log p/p - log x ≤ 0.43` for all `x ≥ 1` | `Lemma51Nat.lemma_5_1_iii_nat_all` |
| (iv) `|∑_{y<p≤x} 1/p - log(log x/log y)| ≤ 2.20/log y` for all `2 ≤ y ≤ x` | `Lemma51Nat.lemma_5_1_iv_nat_all` |

## Lemma 6.22(c), second part, without the Rosser–Schoenfeld hypothesis

`RequestProject/Beurling/ChebyshevUpper.lean`. Chebyshev's weights `1, -1/2, -1/3, -1/5, 1/30`
give `ψ(x) - ψ(x/6) ≤ 0.926x + 4 log x + 43` (`ChebyshevUpper.psi_sub_psi_sixth_le`) and
`ψ(x) ≤ 1.1112x + (log x + 1)(4 log x + 43)` (`ChebyshevUpper.psi_le`). From this,
`π(X) ≤ 1.26 X/log X` for `log X ≥ 10⁸` (`ChebyshevUpper.primesBelow_card_le`), which is the
paper's range. `SmoothTails.smooth_tail_count_large` is Lemma 6.22(c), second part, for
`log X₀ ≥ 10⁸` with no hypothesis on `π(X₀)`.

# Lemma 5.1 for a general Beurling system, the queue bound (75), Freedman's inequality, Lemma 6.1, and the counting inputs of Theorem 4.10

No axioms are added. Freedman's inequality and Lemma 6.1 depend only on the standard axioms. The
other results also depend on `Lean.ofReduceBool` and `Lean.trustCompiler`, which come from the
`native_decide` certificates they reuse.

## Lemma 5.1 for the constructed system (Section 5.2)

Lemma 5.1 is now proved for **any** Beurling system `P` that satisfies (HBS) on `[1, z]`, not
only for ℕ. This covers the constructed system, since the paper applies Lemma 5.1 to it through
(HBS).

The hypothesis is `BeurlingSystem.HBS P X₀⁻ z η₁ η₂ ε₁`
(`RequestProject/Beurling/GenLemma51.lean`). It requires:

* `X₀⁻ ≥ 10⁷` and `0 ≤ η₁, η₂ ≤ 10⁻³`;
* `N_P(v) = ⌊v⌋` for `1 ≤ v < X₀⁻`;
* `|N_P(v) - ⌊v⌋| ≤ ε₁(v) v` and `ε₁(v) log v ≤ η₂` on `[X₀⁻, z]`;
* the dyadic sums of `ε₁` are at most `η₁`.

| Claim | Lean |
| --- | --- |
| Chebyshev identity `∑_{n ≤ x} log n = ∑_{p^k ≤ x} log p · N(x/p^k)` | `BeurlingSystem.chebyshev_identity` (`GenChebyshev.lean`) |
| If `N = ⌊·⌋` on a down-closed set, the generalised primes there are the rational primes | `BeurlingSystem.p_eq_nth_prime` (`GenIdentify.lean`) |
| Lemma 5.1(i)–(iv) under (HBS), for `1 ≤ x ≤ z` | `BeurlingSystem.lemma_5_1` (`GenLemma51Final.lean`) |

The supporting files are `GenNatPart.lean` (the part below `X₀⁻`, identified with ℕ),
`GenPartial.lean` (partial summation) and `GenDyadic.lean` (dyadic blocks).

## The queue bound (75) (Theorem 6.6(ii))

`RequestProject/Beurling/QueueBound75.lean`:

* `QueueBound.queueBound75` is the explicit
  `B = 4M₁L²/c' + 16M₁L/3 + 4√(M₁L(K_d+4)) + 8M₁L(L/Λ+1) + K_d + 9`.
* `queueBound75_le`: `B ≤ 34 M₁ L²` for `c' = 0.15`, `K_d = 3`, `M₁ ≥ 1` and `L, Λ ≥ 10⁸`.
* `queueBound75_cap_le`: `B(x) ≤ 34 M̄₁(x) (log x)²` with the paper's `M̄₁`.
* `Theorem21InputsQueue75` fixes the queue bound to this explicit `B(x)`, so its size is no longer
  assumed. `theorem21_of_queue75` and `corollary_2_2_of_queue75` follow.

## Freedman's inequality (73) (Section 6)

`RequestProject/Beurling/Freedman.lean`. Here `S_n = ∑_{k<n} ξ_k`, where:

* `ξ_k` is `ℱ_{k+1}`-measurable, `E[ξ_k | ℱ_k] = 0`, `ξ_k ≤ b`, and `|ξ_k| ≤ C` (for
  integrability);
* `V_n = ∑_{k<n} E[ξ_k² | ℱ_k]`.

| Claim | Lean |
| --- | --- |
| `e^{λx} ≤ 1 + λx + λ²x²/(2(1-λb/3))` for `x ≤ b`, `0 ≤ λ`, `λb < 3` | `Freedman.exp_le_quad` |
| `exp(λS_n - ψV_n)` is a supermartingale | `Freedman.supermartingale_expMart` |
| maximal inequality `c·P(∃ n ≤ N, M_n ≥ c) ≤ E[M_0]` | `Freedman.max_ineq` |
| (73) `P(∃ n ≤ N, S_n ≥ a, V_n ≤ v) ≤ exp(-a²/(2v + 2ab/3))` | `Freedman.freedman` |
| (73) for all `n` | `Freedman.freedman_iUnion` |

## Lemma 6.1 (landing count)

`RequestProject/Beurling/Landing.lean`. Setting: indicators `X_k` (`ℱ_{k+1}`-measurable) whose
conditional means `p_k = E[X_k | ℱ_k]` sum to at most `μ̄` (almost surely, at every time), and
`λ > 0`.

| Claim | Lean |
| --- | --- |
| `P(∃ n, \|∑_{k<n}(X_k - p_k)\| ≥ √(2μ̄λ) + 2λ/3) ≤ 2e^{-λ}` | `Freedman.landing_count` |
| `P(∃ n, ∑_{k<n} X_k > 2μ̄ + 7λ/6) ≤ 2e^{-λ}` | `Freedman.landing_count_upper` |

## The counting inputs of Lemma 4.8(ii) / Theorem 4.10

`RequestProject/Beurling/Theorem410Count.lean`. Previously two counting hypotheses on the residual
elements were assumed:

* windows of length 2 hold at most `2(n+2)^η + 5` elements;
* blocks `(N, 2N]` hold at most `1.02N` elements.

They now follow from one short-interval count, which mirrors the paper's
`D(v) - D(u-) + ∫ T'_cont` with `T'_cont ≤ 1.01` and `|D| ≤ x^η`:

  `#{i : u ≤ n_i ≤ v} ≤ v^η + u^η + 1.01(v-u) + 1`   for `X ≤ u ≤ v`,

with `X ≥ 10⁴` and `0 ≤ η ≤ 1/8`. The derivation is `Lemma48PiecesCount.toPieces`.

`Theorem21InputsCount` combines this with the explicit queue bound (75).
`theorem21_of_count` and `corollary_2_2_of_count` follow.

## Still assumed

* The random construction itself (Section 3). Its probability space and the event `G` with
  `P(G) ≥ 1 - 1.5/log X₀` are hypotheses, as in all the `Theorem21Inputs*` statements.
  Freedman's inequality and Lemma 6.1 are now proved as general martingale statements. However,
  their instantiation with the construction's filtration, and the union bound over all events,
  are not formalized.
* The lag bound `|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` (Theorem 6.6 with Corollary 3.8).
* The remaining analytic inputs of Theorem 4.10:
  * the decomposition (14) and the pieces of Lemma 4.8(ii) other than the counts;
  * the choice rule for `γ_k`;
  * the design parameters and the absorbed-set growth.

# Design parameters, choice rule for `γ_k`, absorbed-set growth, the lag bound split, and the good-event union bound

No axioms are added. The new results in `Theorem410Design.lean` and `GoodEvent.lean` depend only on
the standard axioms; the refined Theorem 2.1 / Corollary 2.2 statements also inherit
`Lean.ofReduceBool` / `Lean.trustCompiler` from the existing `native_decide` certificates.

The PDF did not arrive with this request, so this step was done from the existing Lean files and
these notes. Every formula below either was already in the project or was derived from it.

## Design parameters and the choice rule for `γ_k` (`Theorem410Design.lean`)

The heights and amplitudes are now **defined** instead of being free sequences that satisfy
hypotheses:

* `Γ_k = heightScale θ κ₀ x⁺_k = κ₀ (x⁺_k)^{1-θ} / (2 (log x⁺_k)³)`;
* `γ_k = chooseHeight X₀ κ D̂_{<a_k} Γ_k`: a good height in `[Γ_k, 2Γ_k]` if one exists, and `Γ_k`
  otherwise;
* `α_k = amplitudeOf θ κ₀ γ_k x⁺_k = κ₀ (x⁺_k)^{1-θ} / ((log x⁺_k)³ γ_k)`.

| Claim | Lean |
| --- | --- |
| The chosen height obeys the choice rule of Lemma 4.8 | `DesignedZero.chooseHeight_rule` |
| `γ_k ∈ [Γ_k, 2Γ_k]` | `DesignedZero.chooseHeight_mem` |
| `1 ≤ α_k ≤ 2` and `α_k γ_k = κ₀ x^{1-θ}/(log x)³` | `DesignedZero.amplitudeOf_mem` |
| `DesignParams`, `1 ≤ α ≤ 2` and `γ ≤ x`, assuming `θ ∈ [1/4,1/2]`, `Λ ≥ 10`, `e^{-Λ} ≤ κ₀ ≤ 1/4`, `x > 1`, `log log x ≥ 2Λ`, `Γ ≥ 2` | `DesignedZero.designParams_of_mem` |

## Absorbed-set growth

`DesignedZero.growth_of_uniform`: the single uniform condition `42 log(2+ℓ) + 5 ≤ ς(ℓ)` for all
`ℓ ≥ 0` implies, for every `k`, the per-height condition
`δ_k ℓ + 2 log(2+ℓ) + 5 ≤ ς(ℓ)` on `0 ≤ ℓ ≤ log(γ_k+1)/(1-θ/2)`. Here `δ_k = 9 log log x⁺_k / log x⁺_k`,
and the lemma assumes `γ_k ≤ x⁺_k`, `x⁺_k > 1`, `θ ≤ 1/2` and `log log x⁺_k ≥ 1`. The proof splits
at `ℓ = √(log x)`.

`Theorem410InputsDesign` is `Theorem410InputsCount` with these definitions plugged in. In it, the
`DesignParams`, `1 ≤ α_k ≤ 2`, `T + 1/2 ≤ γ_k`, `γ_k ≤ x⁺_k`, `ChoiceRule` and per-`k` growth
hypotheses are replaced by conditions on `κ₀` and `x⁺_k` only, plus the uniform growth condition.
`Theorem410InputsDesign.toCount` derives the old form. `theorem21_of_design` and
`corollary_2_2_of_design` follow.

## The lag bound split (`LagTwoSided.lean`)

`PartIInputsLag` replaces the hypothesis `|N_P(x) - T(x)| ≤ B(x) + 3H(x) + 3` with two separate
hypotheses:

* the two-sided lag (12) (Corollary 3.8):
  `-(H/2)(1 + κ₊/log x) - 4 ≤ N_P - T ≤ max Q + (H/2)(1 + κ₊/log x) + 3`, with `0 ≤ κ₊ ≤ log x`;
* the queue bound of Theorem 6.6(ii): `0 ≤ max Q ≤ B(x)`.

`PartIInputsLag.toQueue75` derives the lag bound from these two hypotheses. `Theorem21InputsLag` is
the new top-level refined hypothesis, and `theorem21_of_lag` and `corollary_2_2_of_lag` follow.

## Good event by a union bound (`GoodEvent.lean`)

`GoodEvent.measure_iInter_ge` (finite) and `GoodEvent.measure_iInter_ge_countable` (countable):
suppose each event `E_i` is measurable and fails with probability at most `ε_i ≥ 0`, and
`∑ ε_i ≤ c`. Then `ofReal(1 - c) ≤ μ(⋂ E_i)`. This is the form of `P(G) ≥ 1 - 1.5/log X₀` used in
Theorem 2.1.

## Still assumed

* The random construction itself (Section 3): its probability space, the filtration, the
  individual failure events and their probabilities. The union bound and the martingale tools are
  proved, but they are not yet instantiated with the construction.
* The two-sided lag (12) and the queue bound of Theorem 6.6(ii) (now separate hypotheses).
* The decomposition (14), and the pieces of Lemma 4.8(ii) other than the counts (`Lemma48PiecesCount`).
* The size conditions on `κ₀` and `x⁺_k` (`log log x⁺_k ≥ 2 log X₀`, `Γ_k ≥ T + 1/2`,
  `κ Γ_k ≥ e^{X₀²/3}`), and the uniform growth `42 log(2+ℓ) + 5 ≤ ς(ℓ)` of the Rankin exponent of
  the absorbed set (Lemma 6.26).

# The Rankin minorant `ς_*` (Lemma 4.4 / Lemma 6.26) and Corollary 3.8 from the slot structure

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added. The new
results depend only on the standard axioms; the refined Theorem 2.1 / Corollary 2.2 statements also
inherit `Lean.ofReduceBool` / `Lean.trustCompiler` from the existing `native_decide` certificates.

## The absorbed-set exponent is now the paper's `ς_*` (`RankinMinorant.lean`, `Theorem410Rankin.lean`)

The proof of Lemma 4.4 uses `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` with

  `ς_*(v) = 0.9 ũ(v) log ũ(v)`, `ũ(v) = v/λ(v)`, `λ(v) = max(22.6Λ, 12(log v)² + 9 log v + 8)`,

where `Λ = log X₀`. Before this step, `ς` was a free function, and three facts about it were
assumed: it is monotone, the counting bound holds, and `42 log(2+ℓ) + 5 ≤ ς(ℓ)` for all `ℓ ≥ 0`.

| Claim | Lean |
| --- | --- |
| `ũ` is non-decreasing on `[Λ², ∞)` (the paper's `vλ'(v) ≤ 24 log v + 9 < λ(v)`; here `v/g(v)` has derivative numerator `12L² - 15L - 1 ≥ 0` for `L ≥ 2`) | `RankinMinorant.rankinU_monotoneOn` |
| `ς_*` is non-decreasing on `[Λ², ∞)`, for `Λ ≥ 10⁸` | `RankinMinorant.sigmaStar_monotoneOn` |
| `ũ(v) ≥ 4·10⁶` and `v ≤ 511 ũ(v)²` for `v ≥ Λ²` | `RankinMinorant.rankinU_lower` |
| `sigmaExt Λ ℓ := ς_*(max(ℓ, Λ²))` is monotone on `ℝ` | `RankinMinorant.sigmaExt_monotone` |
| `42 log(2+ℓ) + 5 ≤ sigmaExt Λ ℓ` for all `ℓ ≥ 0` | `RankinMinorant.sigmaExt_growth` |
| `A` empty below `log x = Λ²` and the `ς_*` bound above give the bound with `sigmaExt` for all `x ≥ 1` | `RankinMinorant.le_sigmaExt` |

`Theorem410InputsRankin` is `Theorem410InputsDesign` without the free `ς`. In its place it has
`log X₀ ≥ 10⁸` and two hypotheses stated by the paper:
* `#(A ∩ [1, x]) = 0` for `log x ≤ (log X₀)²`. The paper has `A = ∅` for
  `log log x ≤ 2 log Λ + s_H`, which is stronger.
* `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` above that height.

`Theorem410InputsRankin.toDesign` derives the old form. `theorem21_of_rankin` and
`corollary_2_2_of_rankin` follow.

## Corollary 3.8 from the slot structure (`SlotCount.lean`)

* `SlotCount.card_le_of_unit_gaps`: suppose `F` is monotone, `S ⊆ [a, b]` is finite, and any two
  points `s < t` of `S` satisfy `F t - F s ≥ 1`. Then `#S ≤ F b - F a + 1`. This is §3.4's "an
  interval `I` contains at most `∫_I T'_cont + 1` continuous-slot starts".
* `SlotCount.card_le_of_slope`: with the slope bound `F b - F a ≤ c(b - a)`, the count is at most
  `c(b - a) + 1`.
* `SlotCount.two_sided_lag_of_slots`: Corollary 3.8. The inputs are:
  * the decomposition `N(x) = (j + 1 + Q_j) - C + E₊ - E₋` (Lemma 3.6);
  * `x ∈ J_j`;
  * `0 ≤ C ≤ A_j` and `Q_j - A_j ≥ -1`;
  * `E±` bounded by the number of continuous-slot starts in `[x, x + ℓ₊]` and `[x - ℓ₋, x]`;
  * the slope bound `c` on those windows, with `c ℓ± ≤ (H/2)(1 + κ₊/log x) + ε` and `ε ≤ 1/2`.

  From these, the theorem gives (12).
* `SlotData` collects these data at one height. `PartIInputsSlots` is `PartIInputsLag` with (12)
  replaced by `SlotData` at every `x ≥ X₀`, and `PartIInputsSlots.toLag` derives (12).
  `Theorem21InputsSlots` combines it with `Theorem410InputsRankin`. `theorem21_of_slots` and
  `corollary_2_2_of_slots` follow.

## Still assumed

* The random construction itself (Section 3): its probability space, the slot structure and the
  data in `SlotData`, the filtration, the failure events and their probabilities.
* The queue bound of Theorem 6.6(ii).
* The Rankin bound `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` itself (Lemma 6.26, steps (i), (v)), and
  the emptiness of `A` at low heights.
* The decomposition (14), and the pieces of Lemma 4.8(ii) other than the counts.
* The size conditions on `κ₀` and `x⁺_k`.
* As in the previous form, (12) is used at every `x ≥ X₀`. The paper states it for
  `x ≥ X₀ + 2H(x)` and treats `[X₀, X₀ + 2H]` separately in Proposition 4.1, with the constant
  `+5` in place of `+3`.

# Proposition 4.1 with the paper's split, and the deterministic part of Theorem 6.6(ii)

No axioms are added. The new results in `QueueDeterministic.lean` and `LagSplit.initial_lag_of_slots`
depend only on the standard axioms. The refined Theorem 2.1 / Corollary 2.2 statements also inherit
`Lean.ofReduceBool` / `Lean.trustCompiler` from the existing `native_decide` certificates.

## Proposition 4.1 with the split at `x = X₀ + 2H(x)` (`LagSplit.lean`)

Earlier forms assumed (12) for every `x ≥ X₀`. The paper (Corollary 3.8) states (12) only for
`x ≥ X₀ + 2H(x)`. On `[X₀, X₀ + 2H]` the proof of Proposition 4.1 has the weaker bound
`|D| ≤ B(X₀) + (H(X₀)/2)(1 + κ₊/log X₀) + 5`.

| Claim | Lean |
| --- | --- |
| `|D| ≤ B(x) + 3H(x) + 3` gives `|D| ≤ x^η` for `x ≥ X₀`, with the explicit `B = queueB` and `H = capH` | `LagSplit.lag_rpow_of_queue` |
| The initial-range bound gives `|D(x)| ≤ x^η` for `x ≥ X₀` | `LagSplit.lag_rpow_initial` |
| The accounting of Corollary 3.8 with landing slack `ε ≤ 5/2` gives `-W - 5 ≤ D ≤ Q_max + W + 5` (the constant `5` of the initial range) | `LagSplit.initial_lag_of_slots` |
| Proposition 4.1: `|D(x)| ≤ x^η` for all `x ≥ X₀` | `PartIInputsSlotsSplit.toTarget` |
| Theorem 2.1 / Corollary 2.2 from the refined hypothesis | `theorem21_of_split`, `corollary_2_2_of_split` |

`PartIInputsSlotsSplit` is `PartIInputsSlots` with the slot data assumed only for
`x ≥ X₀ + 2H(x)`. On `X₀ ≤ x < X₀ + 2H(x)` it assumes only the bound from the proof of
Proposition 4.1. `Theorem21InputsSplit` combines it with `Theorem410InputsRankin`. It is a weaker
hypothesis than `Theorem21InputsSlots` on the initial range, and it is now the paper's.

## Theorem 6.6(ii), deterministic part (`QueueDeterministic.lean`)

| Step of the proof | Lean |
| --- | --- |
| AM–GM `√(by) ≤ ay + b/(4a)` | `QueueDet.sqrt_mul_le_affine` |
| Maximising over `ℓ`: `-c'ℓ/L + √(16M₁L(ℓ+K)) ≤ 4M₁L²/c' + c'K/L` | `QueueDet.neg_lin_add_sqrt_le` |
| Short windows: `exc(W) ≤ B(x)` from the excess identity, `Fr(I)`(a),(b) and `R1'` | `QueueDet.short_window_le_queueBound75`, `QueueDet.short_window_excess_le` |
| Inequality (76) for full blocks (`L₀ = 48M₁L³/c'²`, `L₀ - 1 ≤ K₀ ≤ L₀`, `M₁ ≥ L²`) | `QueueDet.full_block_ineq`, `QueueDet.FullBlockData.exc_nonpos` |
| Lindley step `Q_j ≤ max(Q_k + exc((k,j]), max_{i≥k} exc((i,j]))` | `QueueDet.greedyQueue_le_split` |
| Induction over slots with `B` non-decreasing | `QueueDet.greedyQueue_le_of_blocks`, `..._real` |
| Combined: `Q_j ≤ B j` from the per-window inputs | `QueueDet.queue_bound_deterministic` |

This result stands on its own. It is not yet connected to the top-level hypothesis
`0 ≤ Q_max(x) ≤ B(x)`, for two reasons. The slot model of Section 3 (slots `s_j` and the queue
`Q_j` of the construction) is not formalized; `SlotData` treats the queue abstractly. Also, the
paper's `B(s_j)` is frozen per dyadic scale, while `queueB X₀ x` is evaluated at `x`. Connecting
them requires `M̄₁` to be monotone in `x`, which is not proved here.

## Still assumed

* The random construction itself (Section 3): its probability space, the slot structure, the data
  in `SlotData`, the filtration, the failure events and their probabilities.
* The queue bound `0 ≤ Q_max ≤ B(x)` as a top-level input. Its deterministic part is now proved
  as a separate result (above). Its probabilistic part (Theorem 6.6(i)) and the per-window inputs
  are not formalized.
* The initial-range bound of Proposition 4.1 (now its own hypothesis, stated as in the paper).
* The Rankin bound for `A` (Lemma 6.26), the emptiness of `A` at low heights, the decomposition
  (14), the parts of Lemma 4.8(ii) other than the counts, and the size conditions on `κ₀` and
  `x⁺_k`.

# The slot model of Section 3.4, and monotonicity of `M̄₁` and `B`

No axioms are added. The new results use the standard axioms only; results that involve the break
point `s_H` (`capM1_mono`, `queueB_mono`, the slot-model statements and Corollary 2.2) also inherit
`Lean.ofReduceBool` / `Lean.trustCompiler` from the existing `native_decide` certificate for `s_H`.

## `M̄₁` and `B` are non-decreasing (`BSCert/CaplMono.lean`, `Beurling/QueueMono.lean`)

This is Theorem 6.23(c), proved as in Steps 1 and 6 of the paper's proof.

| Claim | Lean |
| --- | --- |
| `G(Λ, s)` is non-decreasing in `s` at fixed `Λ` (`-log Λ ≤ s ≤ t ≤ 6`, `Λ ≥ 10⁸`) | `BSCert.Capl.G_mono_s` |
| `G(Λ, s)` is non-increasing in `Λ` at fixed `s` (Step 1; uses `A ≥ 6` and `Λ'/Λ ≥ 1 + u + u²/2`) | `BSCert.Capl.G_anti_lam` |
| `γ*` is non-decreasing on `(-∞, 6]` | `BSCert.Capl.gstar_mono` |
| `γ` is non-decreasing (for `s_H ≤ 6`, `γ*(s_H) ≤ 7.5`) | `BSCert.Capl.gam_monotone` |
| `log c`, `r̄₀`, `M̄₁` are non-decreasing in `s` (`ℓ ≥ 1`) | `logc_mono`, `rbar0_mono`, `Mbar1_mono` |
| `M̄₁(x)` is non-decreasing on `[X₀, ∞)` (`log X₀ ≥ 10⁸`) | `QueueMono.capM1_mono` |
| `B(x)` of (75) (`queueB`) is non-decreasing on `[X₀, ∞)` | `QueueMono.queueB_mono` |
| The dyadic scale `u = X₀ 2^⌊log₂(s/X₀)⌋ ∈ (s/2, s]` | `QueueMono.dyadicScale`, `dyadicScale_le`, `lt_two_mul_dyadicScale`, `le_dyadicScale` |
| `B(s) := B(u)` for `s ∈ [u, 2u)` (Definition 6.8) is non-decreasing across scales | `QueueMono.queueBScale`, `queueBScale_monotone` |
| `B(s) ≤ B(x)` for `s ≤ x`, `x ≥ X₀` | `QueueMono.queueBScale_le` |

## The slot model (`Beurling/SlotModel.lean`)

`SlotModel X₀` records the data of Section 3.4: the target `T`, which is non-decreasing,
right-continuous and unbounded, with `T(X₀) ≥ X₀`; the slot offset `ϑ ∈ (0, 1/2]`; the composite
arrivals `A_j ≥ 0`; and the count `V_j` of Lemma 3.6, which starts at `V_{j₀-1} = X₀` and increases
by `A_j + P_j` at each slot. Slots are indexed from the first slot: relative slot `k` is the
paper's slot `j = X₀ - 1 + k`.

| Claim | Lean |
| --- | --- |
| Slot starts `s_j = min{x ≥ 1 : T(x) ≥ j + ϑ}`; the minimum is attained by right-continuity | `SlotModel.slot`, `slot_mem` |
| Slot starts are non-decreasing | `SlotModel.slot_mono` |
| For `x ≥ X₀`, the slot `k = slotIdx x` has `s_k ≤ x < s_{k+1}` and `T(x) ∈ [j + ϑ, j + 1 + ϑ)` | `SlotModel.mem_slot` |
| The queue is **defined** as the greedy queue of the arrivals | `SlotModel.queue` |
| Lemma 3.6: `V_j = j + 1 + Q_j` | `SlotModel.count_identity` |
| `Q_j - A_j ≥ -1` | `SlotModel.queue_sub_slotArr` |
| Theorem 6.6(ii), deterministic part, for the model's queue: `Q_j ≤ B(s_j)` with `B` frozen per scale | `SlotModel.queue_le_frozen` |
| Remark 6.9(ii): `Q_j ≤ B(x)` for every slot with `s_j ≤ x` | `SlotModel.queue_le_queueB` |
| The landing data of Corollary 3.8 give `SlotData` with `Q_max = B(x)` | `SlotModel.Landing.toSlotData` |
| Proposition 4.1 inputs from the slot model | `PartIInputsSlotModel.toSplit` |
| Theorem 2.1 / Corollary 2.2 | `theorem21_of_slotModel`, `corollary_2_2_of_slotModel` |

The new hypothesis `PartIInputsSlotModel` differs from `PartIInputsSlotsSplit` in three ways:
- the queue in the slot data is the model's queue, not an abstract number;
- the top-level queue bound `0 ≤ Q_max(x) ≤ B(x)` is **no longer assumed** and is derived from the
  per-window inputs of Theorem 6.6(ii) (`SlotModel.QueueWindowData`, with the bound `B(s_j)`
  frozen per dyadic scale);
- the position of `T(x)` in its slot, the count identity and `Q_j - A_j ≥ -1` are proved from the
  model and no longer assumed.

## Still assumed

- The random construction (Section 3): the probability space, the elements of the semigroup, the
  filtration and the failure events. The facts about `T` used by the slot model (monotone,
  right-continuous, unbounded, `T(X₀) ≥ X₀`) are fields of `SlotModel`.
- The per-window inputs of Theorem 6.6(ii) (`ShortWindowData` / `FullBlockData`: the excess
  identity, the event `Fr(I)` and the drift bound `R1'`), which come from Theorem 6.6(i) and
  Section 5.
- The landing data of Corollary 3.8 (`SlotModel.Landing`): the decomposition
  `N = V_j - C + E₊ - E₋` and the placement of the landing primes at continuous-slot starts.
- The initial-range bound of Proposition 4.1, the Rankin bound for `A` (Lemma 6.26), the
  emptiness of `A` at low heights, the decomposition (14), the remaining parts of Lemma 4.8(ii),
  and the size conditions on `κ₀` and `x⁺_k`.

# Initial range of Proposition 4.1, emptiness of `A` at low heights, and the size conditions on `κ₀` and `x⁺_k`

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added. The new
results use the standard axioms; the statements that involve `s_H`, `H` or `B` (and the refined
Corollary 2.2) also inherit `Lean.ofReduceBool` / `Lean.trustCompiler` from the existing
`native_decide` certificates.

## The size conditions on `κ₀` and `x⁺_k` (`Beurling/DesignSize.lean`)

Section 2.2 fixes `κ₀ ∈ [X₀⁻¹, 1/4]` and the switch-on rule `x₁ ≥ exp(X₀²)`, `x_{k+1} ≥ exp(x_k)`.
`Theorem410InputsRankin` instead assumed an auxiliary height `T` together with
`e^{X₀²/3} ≤ κT`, and for every `k`: `x⁺_k > 1`, `log log x⁺_k ≥ 2 log X₀`, `Γ_k ≥ T + 1/2` and
`κΓ_k ≥ e^{X₀²/3}`.

| Claim | Lean |
| --- | --- |
| At one switch-on point with `log x ≥ X₀²` (and `κ, κ₀ ≥ X₀⁻¹`, `θ ≤ 1/2`): `x > 1`, `log log x ≥ 2 log X₀` and `e^{X₀²/3}/κ + 1/2 ≤ Γ(x)` (the computation behind (20)) | `DesignSize.size_of_log_ge` |
| The switch-on points increase, `x⁺_0 ≤ x⁺_k` | `DesignSize.xp_ge_zero` |
| `Theorem410InputsSize` (only `log x⁺_0 ≥ X₀²`, `κ ≥ X₀⁻¹` and `κ₀ ∈ [X₀⁻¹, 1/4]`) gives `Theorem410InputsRankin`, with `T := e^{X₀²/3}/κ` | `Theorem410InputsSize.toRankin` |

The paper's `κ = X₀^{-5/12+2ε_κ}` satisfies `κ ≥ X₀⁻¹`. What remains on these parameters are their
choices in Section 2.2: `κ₀ ∈ [X₀⁻¹, 1/4]`, `log x⁺_0 ≥ X₀²` and the spacing `x⁺_{k+1} ≥ exp(x⁺_k)`.

## Proposition 4.1 on the initial range (`Beurling/InitialRange.lean`)

The paper: on `[X₀, X₀ + 2H]` "the accounting in the proof of Corollary 3.8 applies verbatim (with
`j := j₀ - 1` if `x < s_{j₀}`)". In the slot model, relative slot `0` is the paper's `j₀ - 1`
(`V = X₀`, no arrivals, `Q = 0`), so that case is covered automatically.

| Claim | Lean |
| --- | --- |
| `H(x) ≤ x^{1/8}` for `x ≥ X₀` | `InitialRange.capH_le_rpow` |
| `X₀ ≤ x < X₀ + 2H(x)` implies `x < 2X₀` | `InitialRange.lt_two_mul_of_initial` |
| On `[1, 2X₀)` the frozen bound `B(s)` is `B(X₀)` | `InitialRange.queueBScale_eq_init` |
| Landing data with slack `5/2` give `|N - T| ≤ B(X₀) + W + 5`, using `Q_j ≤ B(X₀)` from the deterministic part of Theorem 6.6(ii) | `SlotModel.LandingInit.abs_le` |
| `PartIInputsSlotModelInit` (landing data on the initial range instead of the bound) gives `PartIInputsSlotModel` | `PartIInputsSlotModelInit.toSlotModel` |

## `A` is empty at low heights (`Beurling/AbsorbEmpty.lean`)

§6.8: "Every jittered prime is at least `X₀⁻ = X₀ - H(X₀)/2`, so `A` has no element at heights
where `y < X₀⁻`." Here `y(x) = H(x) L₀(x) (log x)⁶` with `L₀ = max(L⁵, 48 M̄₁ L³/c'²)` (`absorbYAt`;
`M̄₁ ≥ M₁` is used, so this `y` majorizes the paper's), frozen at the dyadic scale (`absorbY`).

| Claim | Lean |
| --- | --- |
| `γ(s) ≤ γ*(s_H) = 1/3 - 10⁻⁵` for `s ≤ 0` | `AbsorbEmpty.gstar_le_target` |
| `y(x) < X₀ - H(X₀)/2` for `X₀ ≤ x`, `log x ≤ (log X₀)²` | `AbsorbEmpty.absorbYAt_lt` |
| If each `a ∈ A` has a prime `r` with `X₀⁻ ≤ r < y(a)` (definition (5) with centred placement), then `#(A ∩ [1, x]) = 0` for `log x ≤ (log X₀)²` | `AbsorbEmpty.countA_eq_zero_of_low` |
| `Theorem410InputsAbs` gives `Theorem410InputsSize` | `Theorem410InputsAbs.toSize` |
| Theorem 2.1 / Corollary 2.2 from `Theorem21InputsAbs` (= `PartIInputsSlotModelInit` and `Theorem410InputsAbs`) | `theorem21_of_abs`, `corollary_2_2_of_abs` |

The margin is the `3·10⁻⁵ Λ` gap between `3γ*(s_H) = 1 - 3·10⁻⁵` and `1`. It covers the polynomial
factors `Λ^{30}` (`log` of these is at most `2.5·10⁻⁵ Λ` for `Λ ≥ 10⁸`).

## Still assumed

- The random construction (Section 3): the probability space, the semigroup elements, the
  filtration, the failure events and their probabilities. The facts about `T` used by the slot
  model, and the placement facts (each element of `A` has a jittered latest prime `≥ X₀⁻` below
  `y`), are hypotheses about it.
- The queue bound apart from its deterministic part: the per-window inputs of Theorem 6.6(ii)
  (`QueueWindowData`) and the landing data of Corollary 3.8 (`Landing`, `LandingInit`).
- The Rankin bound for `A` (Lemma 6.26) above `log x = (log X₀)²`. It uses the cluster event at
  lower heights and Rankin's bound for the realised system.
- The decomposition (14) and the remaining parts of Lemma 4.8(ii) (`Lemma48PiecesCount`: the
  decomposition of `D̂_{<a_k}`, the bounds of the pieces and the final numerical inequality).
- The parameter choices of Section 2.2: `κ₀ ∈ [X₀⁻¹, 1/4]`, `κ ≥ X₀⁻¹`, `log x⁺_0 ≥ X₀²`, the spacing.

# The decomposition (14), the construction of Section 3, and Rankin's bound for Beurling systems

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added; anything
not proved is a hypothesis of a named `Prop`. The new results use the standard axioms; the
top-level corollaries also inherit `Lean.ofReduceBool` / `Lean.trustCompiler` from the existing
`native_decide` certificates.

## The decomposition (14) (`Beurling/Decomp/`)

`ζ_P` is the continuation `zetaCont P 1 = s/(s-1) + s ∫_1^∞ (N_P(x) - x) x^{-s-1} dx`; `D = N_P - T`
is the lag for the target (6) (`lagOf`); `D̂_{<a} = s ∫_{(1,a]} D x^{-s-1} + D(a) a^{-s}`
(`earlyNoise`), `D̂_{≥a} = s ∫_a^∞ D x^{-s-1}` (`lateNoise`).

| Claim | Lean |
| --- | --- |
| `s ∫_c^∞ (∫_c^x g) x^{-s-1} dx = ∫_c^∞ g(u) u^{-s} du` | `Decomp.mellin_primitive` |
| `s ∫_1^∞ D x^{-s-1} = D̂_{<a}(s) + D̂_{≥a}(s)` | `Decomp.mellin_split` |
| `D̂_{<a}` is entire when `D` is integrable and bounded on `(1, a]` | `Decomp.differentiable_earlyNoise_of_integrableOn` |
| Transform of the base part: `s ∫ (T_base - x) x^{-s-1} = Z_B(s) - s/(s-1)` | `Decomp.mellin_baseErr` |
| Transform of the oscillation: `s ∫ R x^{-s-1} = ∑_k R̂_k(s)` (`σ > θ`) | `Decomp.mellin_osc` |
| Transform of the absorbed part: `s ∫ E_A x^{-s-1} = Ê_A(s)` (cap inactive) | `Decomp.mellin_absE` |
| **(14)**: `ζ_P = Z_B + ∑_k R̂_k + (D̂_{<a} + D̂_{≥a}) + Ê_A` on `σ > max(θ, η)`, `s ≠ 1` | `Decomp.decomposition_14` |
| `Theorem410InputsDec θ P` (no decomposition hypothesis; `D̂_{<a_k}` is the early transform of the lag) gives `Theorem410InputsAbs θ ζ_P` | `Decomp.Theorem410InputsDec.toAbs` |
| Corollary 2.2 from `Theorem21InputsDec` | `Decomp.corollary_2_2_of_dec` |

The heights and amplitudes enter `Theorem410InputsDec` as a fixed-point condition
(`γ_k = designGamma … (D̂_{<a_·}) …`, `α_k = amplitudeOf …`): in the paper `γ_k` reads only the system
on `[1, a_k)`, so the choice is recursive.

## The construction of Section 3 (`Beurling/Construction/`)

| Claim | Lean |
| --- | --- |
| The jitter space: `Ω = ℕ → ℝ` with the product of uniform laws on `[0,1]`, a probability measure | `Construction.jitterMeasure` |
| The jitters `U_j` are independent and uniform; a.s. all in `[0, 1]` | `jitter_iIndepFun`, `jitter_map`, `ae_jitter_mem` |
| The filtration `F_t` of the jitters at slots `≤ t`; `U_t` is `F_t`-measurable; `U_{t+1}` is independent of `F_t` | `jitterFiltration`, `jitterFiltration_eq`, `jitter_measurable_filtration`, `jitter_indep_past` |
| Box-centred landing: `s + H(U - 1/2) ∈ [s - H/2, s + H/2]`, and its law is uniform on the box | `landing_mem_box`, `landing_law` |
| A run of the greedy rule (slot model, width `H`, jitters `U`, `T = ⌊x⌋` below `X₀`); the placed primes | `GreedyRun`, `placedAt`, `primeValueOf`, `jitteredPrimesOf` |
| Every slot start is `≥ X₀` | `GreedyRun.slot_ge` |
| Every jittered prime is `≥ X₀ - H(X₀)/2` (if `U_j ∈ [0,1]` and `v - H(v)/2` is non-decreasing) | `GreedyRun.jittered_ge` |
| The absorbed set (5) and the placement fact for its elements | `absorbedRule`, `absorbedRule_placement` |
| Failure events with times, adapted; `Good(< t) = {τ ≥ t}`, `G = {τ = ∞}`; `Good(< t) ∈ F_t`; `P(G) ≥ 1 - ∑ P(E_iᶜ)` | `FailureAdapted`, `goodBefore`, `failTime`, `goodBefore_eq`, `goodAll_eq`, `goodBefore_measurable`, `goodAll_prob_ge` |
| The Part I inputs for fixed data give the lag bound (13) for that data | `PartIWith`, `PartIWith.lag` |
| Even `X₀ ≥ 4` is `X₀`-smooth; `(log v)^{-4} ≤ 0.1/log v` (cap inactive) | `even_mem_smoothNumbers`, `zpow_neg_four_le` |
| Coupled Theorem 4.10 inputs give `Theorem410InputsDec` (lag bound, cap, smoothness, `u_a ≥ X₀`, placement derived) | `Theorem410InputsCoupled`, `Theorem410InputsCoupled.toDec` |
| Theorem 2.1 / Corollary 2.2 from the hypothesis on the concrete construction | `Theorem21InputsCon`, `theorem21_of_con`, `corollary_2_2_of_con` |

In `Theorem21InputsCon` the probability space is the jitter space, the good event is the
intersection of a countable family of adapted failure events (intersected with the full-measure
event that all jitters lie in `[0, 1]`), and Part I and Theorem 4.10 use the same data
`κ, A, u, α, γ, x⁺` and the same slot model. The jittered primes are those placed by the greedy
rule from that slot model with `H = capH X₀` and the jitters `ω`.

## Rankin's bound for a Beurling system (`Beurling/Construction/RankinBeurling.lean`)

| Claim | Lean |
| --- | --- |
| `Ψ_N(Y, z) ≤ Y^σ ∏_{p_j < z} (1 - p_j^{-σ})^{-1}` (Lemma 6.26, step (v), first bullet) | `BeurlingSystem.smoothCountN_le_rankin` |
| If every `n ∈ A` is the value of a `z`-smooth element, then `#(A ∩ [1, x]) ≤ x^σ ∏_{p_j<z} (1 - p_j^{-σ})^{-1}` (steps (iii), (v)) | `BeurlingSystem.countA_le_rankin` |

## Still assumed

- The per-window inputs of Theorem 6.6(ii) (`QueueWindowData`) and the landing data of
  Corollary 3.8 (`Landing`, `LandingInit`).
- `ρ_A ≤ (log v)^{-4}` (Lemma 6.27(a)) and the Rankin bound for `A` above `log x = (log X₀)²`
  (Lemma 6.26). Rankin's inequality for the realised system is proved; the smoothness of the
  elements of `A` (step (i)), which uses the cluster event, and the numerical estimate of the
  Rankin product for the realised primes are not.
- The pieces of `D̂_{<a_k}` in Lemma 4.8(ii) (`Lemma48PiecesCount`): the split of `D̂_{<a_k}` into
  a Dirichlet polynomial over `B = N \ (D ∪ A)`, a bounded part and an integral, the bounds on the
  pieces, and the final numerical inequality. This needs the elements of the system below `a_k`
  identified with the integers, the rigid set and `A`, which is not formalized.
- The consistency (fixed-point) condition on `γ_k, α_k`, the failure-probability budget
  `∑ P(E_iᶜ) ≤ 1.5/log X₀` (Lemma 6.10), the monotonicity of `v - H(v)/2`, and the parameter
  choices of Section 2.2.
- The construction's coupling between the system `P(ω)` and the greedy run beyond the jittered
  primes: the elements of `P(ω)`, the latest-prime map and the composite arrivals are data, not
  built from the jitters.

# The heights, the parameters, the jitter floor, Lemma 6.27(a) and the divisor trick of Lemma 6.26

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added; anything
not proved is a hypothesis of a named `Prop`. The new results use the standard axioms; the
statements that involve `H` (and the refined Corollary 2.2) also inherit `Lean.ofReduceBool` /
`Lean.trustCompiler` from the existing `native_decide` certificates.

## The heights `γ_k`, `α_k` (`Beurling/Construction/Design.lean`)

The fixed-point condition is now a theorem. On `(0, x⁺_k]` only the terms `R_j`, `j < k`, of the
oscillation are switched on, so `D̂_{<a_k}` (for `a_k ≤ x⁺_k`) reads only `γ_j, α_j` with `j < k`,
and the rule of Lemma 4.8 defines the heights by recursion.

| Claim | Lean |
| --- | --- |
| `R`, `D = N - T` and `D̂_{<a_k}` on `(0, x⁺_k]` only read `γ_j, α_j`, `j < k` | `osc_congr_lt`, `lagOf_congr_lt`, `earlyOf_congr` |
| The designed heights (recursion) and amplitudes | `designedGamma`, `designedAlpha` |
| **Fixed point**: `γ_k = designGamma … (D̂_{<a_·} of the lag built with all designed γ, α) … k` | `designedGamma_fixed` |
| `γ_k ∈ [Γ_k, 2Γ_k]`; `1 ≤ α_k ≤ 2` when `Γ_k > 0` | `designedGamma_mem`, `designedAlpha_mem` |

The rule picks *a* good height in `[Γ_k, 2Γ_k]` when one exists (the paper takes the least one);
everything downstream only uses that the chosen height is good when a good height exists.

## The parameters of Section 2.2 (`Beurling/Construction/Design.lean`)

`κ = X₀^{-5/12 + 2ε_κ}` with `ε_κ = 0.01` (`kappaParam`), `κ₀ = 1/4` (`kappa0Param`), and the
switch-on points `x⁺_0 = exp(X₀²)`, `x⁺_{k+1} = exp(x⁺_k)` (`switchOn`, the least admissible
choice). Proved: `0 < κ ≤ 1`, `κ ≥ X₀⁻¹`, `X₀⁻¹ ≤ κ₀ ≤ 1/4` (`X₀ ≥ 4`), the spacing,
`x⁺_0 ≥ X₀`, `log x⁺_0 = X₀²`, `x⁺_k > 1` (`kappaParam_*`, `kappa0Param_ge`, `switchOn_*`).

## The jitter floor (`Beurling/Construction/JitterFloor.lean`)

The monotonicity of `v - H(v)/2` was only used to place the jittered primes above
`X₀⁻ = X₀ - H(X₀)/2`. That consequence is now proved for the paper's `H = max(H_std, M̄₁²)`:

| Claim | Lean |
| --- | --- |
| `γ*(s) Λ ≤ 7.5 (log Λ + 1)` for `-log Λ ≤ s ≤ 1 - log Λ`, `Λ ≥ 10⁸` | `JitterFloor.gstar_mul_le` |
| On `[X₀, 2X₀]`: `log c = 4ℓ² - log 4`, `M̄₁² ≤ H_std`, so `H = H_std = e^{8(log log x)²}` | `JitterFloor.capH_eq_std` |
| `H(x) - H(X₀) ≤ 2(x - X₀)` on `[X₀, 2X₀]` (mean value theorem) | `JitterFloor.capH_sub_le` |
| **Floor**: `X₀ - H(X₀)/2 ≤ s - H(s)/2` for every `s ≥ X₀` | `JitterFloor.capH_floor` |
| Every jittered prime is `≥ X₀ - H(X₀)/2` (from the floor) | `GreedyRun.jittered_ge_of_floor` |

The full monotonicity of `v - H(v)/2` on `[X₀, ∞)` (which needs the derivative bound of
Theorem 6.23(c) on the raised range) is not proved; it is no longer a hypothesis.

## Lemma 6.27(a) from Lemma 6.26 (`Beurling/Construction/LocalCount.lean`)

| Claim | Lean |
| --- | --- |
| `#(A ∩ [v, w])` | `Absorbed.localCountA` |
| `#(A ∩ [v, v + v^b]) ≤ v^b ε` implies `ρ_A(v) ≤ ε` | `Absorbed.absorbedDensity_le_of_localCount` |
| **Lemma 6.27(a)**: Lemma 6.26 (`#(A ∩ [v, v + v^b]) ≤ v^b (log v)^{-4}`) gives `ρ_A ≤ (log v)^{-4}` | `Absorbed.rhoA_le_of_lemma626` |

## Lemma 6.26: the divisor trick (`Beurling/Construction/DivisorTrick.lean`)

| Claim | Lean |
| --- | --- |
| (ii) a `z`-smooth element of value `> h ≥ 1` has a divisor `d` with `h < d ≤ z h` | `BeurlingSystem.exists_split` |
| (ii)–(iii) with (i) and the window bound (iv): `#(A ∩ [u, u + h]) ≤ C Ψ_N(z h, z)` | `BeurlingSystem.localCount_le_divisor` |
| with Rankin's bound: `#(A ∩ [u, u + h]) ≤ C (z h)^σ ∏_{p_j<z} (1 - p_j^{-σ})^{-1}` | `BeurlingSystem.localCount_le_rankin` |
| **Lemma 6.26 from steps (i), (iv), (v) and (81)**: `#(A ∩ [u, u + h]) ≤ h L^{-4}` | `BeurlingSystem.lemma626_of_steps` |

## The refined top-level hypothesis (`Beurling/Construction/Fix.lean`)

`Theorem21InputsFix` is `Theorem21InputsCon` with the parameters fixed, the heights designed, no
monotonicity of `v - H(v)/2`, no fixed-point condition, and Lemma 6.26 in place of
`ρ_A ≤ (log v)^{-4}`. The weight hypotheses on `A` and `|α_k| ≤ 2` are derived.

| Claim | Lean |
| --- | --- |
| The remaining inputs | `PartIRest`, `Theorem410Rest`, `Theorem21InputsFix` |
| `Theorem21InputsFix` gives `Theorem21InputsDec` | `theorem21InputsDec_of_fix` |
| Theorem 2.1 / **Corollary 2.2** from `Theorem21InputsFix` | `theorem21_of_fix`, `corollary_2_2_of_fix` |

## Still assumed

- The per-window inputs of Theorem 6.6(ii) (`QueueWindowData`) and the landing data of
  Corollary 3.8 (`Landing`, `LandingInit`).
- Lemma 6.26 itself (the pointwise sparsity of `A`). Its steps (ii), (iii), the first bullet of
  (v) and (vi) are proved (`lemma626_of_steps`); step (i) (smoothness of the elements of `A`, from
  the decision order), the window count of step (iv) (from the cluster event), the numerical
  estimate of the Rankin product for the realised primes (step (v)) and condition (81)
  (Theorem 6.23(b)) are not.
- The Rankin bound for `A` above `log x = (log X₀)²`: the same step (i) and numerical estimate.
- The pieces of `D̂_{<a_k}` in Lemma 4.8(ii) (`Lemma48PiecesCount`).
- The failure-probability budget `∑ P(E_iᶜ) ≤ 1.5/log X₀` (Lemma 6.10) and the adaptedness of the
  failure events.
- The construction's coupling: the system `P(ω)`, the latest-prime map, the slot model with its
  composite arrivals, `A` and `u_a`, and the construction scales `a_k` are data, not built from the
  jitters.

# Lemma 6.26, step (v): Rankin's bound for the realised system, and its inputs from (HBS)

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added. The new
results use the standard axioms plus `Lean.ofReduceBool` / `Lean.trustCompiler` (from
`native_decide` certificates: the existing `R(0.69) ≤ 0.77`, `Ei` and `ψ ≤ 1.42x` certificates,
and a new check of `π(N) ≤ 2N/log N` for `8 ≤ N ≤ 1000`).

## Step (v) (`Beurling/Construction/RankinRealised.lean`)

Let `z = 2y ≥ 8`, `Y > 0`, `u_* = log Y/log z`, `η = log u_*/log z`, `σ = 1 - η`.

| Claim | Lean |
| --- | --- |
| `log ∏_{p_j<z} (1 - p_j^{-σ})^{-1} = ∑ (p_j^{-σ} + R-term)`, R-term non-increasing in `σ` | `log_rankinProd_eq`, `rTermR_anti` |
| `p^{-σ} = 1/p + g(p)`, `g(t) = (t^η - 1)/t`; `g` non-increasing on `[8, ∞)` for `η ≤ 0.31` | `rpow_neg_one_sub_eq`, `gEta_anti` |
| `d/dt Ein(η log t) = g(t)/log t` | `hasDerivAt_EinLog` |
| Partial summation against `π_P(s) ≤ 2s/log s`: `∑_{p_j<z} g(p_j) ≤ 26 + 2 Ein(η log z)` | `sum_gEta_le` |
| **Step (v)**: with `π_P(s) ≤ 2s/log s` (`8 ≤ s ≤ z`), `∑_{p_j<z} 1/p_j ≤ log log z + 4.1`, `R_N(0.69) ≤ 0.78` and `(∗)` (`u_* ≥ 2·10⁸`, `log log z ≤ 1.79u_*`, `η ≤ 0.31`): `Ψ_N(Y, z) ≤ Y exp(-0.9 u_* log u_*)` | `BeurlingSystem.smoothCountN_le_realised` |
| Lemma 6.26 from steps (i), (iv), (81) and the hypotheses of step (v) at `Y = 2yh` (`1 ≤ u₀ ≤ u_*`) | `BeurlingSystem.lemma626_of_steps_v` |

The partial summation is done on the integer parts of the realised primes (discrete Abel
summation), so the additive constant is `26` instead of the paper's `1`; it is absorbed since
`u_* ≥ 2·10⁸`. The coefficient `2(1 + 2/log u_*)` of `u_*/log u_*` is the paper's. Only the second
bound of step (v), `exp(-0.9 u_* log u_*)`, is stated (it is the one used in step (vi) and in
Lemma 4.4).

## `π(N) ≤ 2N/log N` for ℕ (`Beurling/Construction/NatPrimeCount.lean`)

The paper cites Rosser–Schoenfeld (`π(s) ≤ 1.26 s/log s`) for the rational primes. Step (v) only
needs `2s/log s`, which is proved here (`NatPrimeCount.primeCount_le`, every `N ≥ 8`): Abel
summation against `θ(N) ≤ 1.42N` gives `π(N) ≤ 2.84/log 2 + 1.42 ∑_{n=3}^N 1/log n`; this is
`≤ 2N/log N` at `N = 1000` (certified fixed-point logarithms) and for all larger `N` by induction;
`8 ≤ N ≤ 1000` is a direct certified check.

## The inputs of step (v) from (HBS) (`Beurling/Construction/RealisedPrimes.lean`)

Under `BeurlingSystem.HBS X₀⁻ z' η₁ η₂ ε₁` (on `[1, z']`) with `log X₀⁻ ≥ 100` (the paper has
`log X₀ ≥ 10⁸`), for `z ≤ z'`:

| Claim | Lean |
| --- | --- |
| `∑_{p_j<z} 1/p_j ≤ log log z + 4.1` (Lemma 5.1(iv) at `y = 2`, plus `p_0 = 2`) | `HBS.sum_inv_primesLt_le` |
| `π_P(s) ≤ 2s/log s` for `8 ≤ s ≤ z'` (rational below `X₀⁻`; above, `ψ_P(s^{0.9})/log 2 + ψ_P(s)/(0.9 log s)`) | `HBS.primesLe_card_le` |
| `R_N(0.69) ≤ 0.77 + 2·0.004 ≤ 0.78` (`R(0.69)` certificate for the rational primes; dyadic blocks with `ψ_P ≤ 1.42t` above `X₀⁻`) | `HBS.sum_rTermR_le` |
| **Step (v)** with only `(∗)` as hypothesis | `HBS.smoothCountN_le` |
| **Lemma 6.26** from steps (i), (iv) and (81) (`2y ≤ z'`, `1 ≤ u₀ ≤ u_*`, `(∗)` at `Y = 2yh`) | `HBS.lemma626` |
| `#(A ∩ [1, x]) ≤ Ψ_N(x, z)` when the elements of `A` up to `x` are values of `z`-smooth elements | `countA_le_smoothCountN` |
| **Rankin bound for `A`** (proof of Lemma 4.4): with step (i) up to `x`, `(∗)` at `Y = x` and `log 2y ≤ λ(log x)`, `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` | `HBS.countA_le_sigmaStar` |

## Still assumed

- Step (i) of Lemma 6.26 (smoothness of the elements of `A`, from the decision order of the
  construction), the window count of step (iv) (cluster event), condition (81) and the bounds on
  `y` behind `(∗)` and `log 2y ≤ λ(log x)` (Theorem 6.23(b)). The top-level hypothesis
  `Theorem21InputsFix` still takes Lemma 6.26 and the Rankin bound for `A` as inputs, since `y(v)`,
  `C_d` and the construction's latest-prime map are not formalized.
- Everything listed as still assumed in the previous section, other than the numerical estimate
  of the Rankin product for the realised primes, which is now proved.

# Lemma 6.26 and the Rankin bound for `A` derived; Lemma 6.10 summation

This step was done with the paper (`beurling-paper.pdf`) at hand. No axioms are added. The new
results use the standard axioms, plus `Lean.ofReduceBool` / `Lean.trustCompiler` where they
depend on the existing certified computations.

## Step (i): the decision order (`Beurling/Construction/StepOne.lean`)

| Claim | Lean |
| --- | --- |
| The origin of each realised prime: rational `< X₀`, or decided at relative slot `k + 1` with value `primeValueOf M H U k` | `PrimeOrigin` |
| The decision order (rational first, then slot order) and the latest-prime map of an element | `PrimeOrigin.decisionKey`, `latestIdx`, `latestPrime` |
| **Step (i)**: jitters in `[0,1]`, `H ≥ 0` non-decreasing on `[X₀,∞)`, `4H(v) ≤ v`, `X₀ - H(X₀)/2 ≤ r < y` for the latest prime `r` of `e` ⟹ `e` is `2y`-smooth | `PrimeOrigin.smooth_of_latest` |
| For `H = max(H_std, M̄₁²)`: `H` non-decreasing on `[X₀,∞)` and `4H(v) ≤ v` | `capH_monotoneOn`, `four_capH_le` (`YBounds.lean`) |

The paper has `p ≤ (1 + e^{-10⁶}) r`; `4H(v) ≤ v` gives `p ≤ 9r/7`, which is all `p < 2y` needs.

## Step (iv): the window count from the cluster event (`Beurling/Construction/Window.lean`)

| Claim | Lean |
| --- | --- |
| Grid windows `[kδ₁, (k+2)δ₁)`, `δ₁ = 2(log z)^{-6}`, left end in `[z, 2z)`, dyadic heights `z = (X₀/2)2^m`; the cluster event up to `Z` | `gridDelta`, `IsDyadicHeight`, `winCount`, `ClusterUpTo` |
| One dyadic block: `[a,b] ∩ [w,2w)` is covered by `(b-a)/(2δ₁(w)) + 3` windows (at `w`, and the last window at `w/2`) | `block_count_le` |
| Below `X₀⁻`, an interval of length `< 1` holds at most one element (from `N(v) = ⌊v⌋`) | `low_count_le_one` |
| **Step (iv)**: `[a,b]`, `b < a + 1`, `b ≤ Z` holds at most `1 + ((log b)^6/4 + 6)M` elements | `interval_count_le` |
| The windows `I_d = [u/d, (u+h)/d]`, `d > h`; `1 + ((log(u+h))^6/4 + 6)M ≤ C_d = M L^6/2` | `window_count_divisor`, `window_const_le` |

The paper has `L^6/4 + 5` windows; the extra window comes from cruder bookkeeping at the dyadic
boundary.

## The threshold `y` and Theorem 6.23(b) (`YBounds.lean`, `Cond81.lean`)

| Claim | Lean |
| --- | --- |
| `log 2y ≤ max(8ℓ², 2K + 1.39) + K + 9ℓ + 9.07`, `K = log c`; so `log 2y ≤ 3K + 9ℓ + 11.85`, and `≤ 12ℓ² + 9ℓ + 7.69` in the standard regime | `log_two_absorbYAt_le`, `log_two_absorbYAt_le_three`, `log_two_absorbYAt_le_std` |
| `log y ≥ 8ℓ²`; `y` non-decreasing on `[X₀,∞)` | `log_absorbYAt_ge`, `absorbYAt_mono` |
| **Theorem 6.23(b), first case**: `s ≤ s_H` ⟹ `2y < X₀` | `two_absorbYAt_lt_of_le_sH` |
| Above `s_H`: the raised regime (`log 2y ≤ 3.01γΛ`, `K + 10ℓ ≤ 1.01γΛ`, `log x ≥ 393Λ²`) or the standard regime (`log 2y ≤ 12.1ℓ²`, `K + 10ℓ ≤ 4.1ℓ²`, `ℓ ≥ 2886`) | `regimes_of_gt_sH` |
| The numerical core of Step 5: `u₀ ≥ 2·10⁸` and `log 2y + D ≤ 0.9u₀ log u₀` | `cond81_core` |
| **Condition (81) and `(∗)` at a window** (`2y(x) > X₀`, `u ≤ x ≤ 2u`, `C_d = M̄₁(u)(log u)^6/2`) | `cond81_window` |
| **`(∗)` and `log 2y ≤ λ(log x)` for the Rankin bound** (`Y = x`) | `rankin_conditions`, `log_two_absorbYAt_le_lambda` |

The paper's constant `11.14` in `log y ≤ 3 log c + 9ℓ + 11.14` becomes `11.85` here (cruder bound
on `L₀`); Step 5 has room for this.

## Lemma 6.26 and the Rankin bound for the construction (`Sparsity.lean`)

`AbsorbedCoupling`: the prime origins, `A ⊆` the absorbed set (5) for the latest-prime map, and
every `n ∈ A` the value of an element whose latest prime is `latest n`.

| Claim | Lean |
| --- | --- |
| **Lemma 6.26**: under the coupling, `H = max(H_std, M̄₁²)`, jitters in `[0,1]`, (HBS) at every height (`log X₀⁻ ≥ 100`, `X₀⁻ ≥ X₀/2 + 1`) and the cluster event at every `v ≥ X₀` (heights `≤ 4v/(log v)^{11}`, bound `M̄₁(v)`): `#(A ∩ [v, v + v^{θ/2}]) ≤ v^{θ/2}(log v)^{-4}` | `lemma626_construction` |
| **Rankin bound for `A`**: `#(A ∩ [1,x]) ≤ x e^{-ς_*(log x)}` for `log x > (log X₀)²` | `rankinA_construction` |

The threshold of Lemma 6.26 at `u` is `y(2u)`, which bounds `y(n)` for all `n ≤ 2u`.

## Lemma 6.10 (`Budget.lean`)

| Claim | Lean |
| --- | --- |
| First failure: `Gᶜ ⊆ ⋃_E (Eᶜ ∩ Good(< t(E)))` | `compl_goodAll_subset_firstFailure` |
| `P(G) ≥ 1 - ∑_E P(Eᶜ ∩ Good(< t(E)))` | `goodAll_prob_ge_firstFailure` |
| Summation: `∑_m (1.0001(Λ + m log 2)^{-2} + 3.2(2^m X₀)^{-2}) ≤ 1.5/Λ` | `budget_sum_le` |
| **Lemma 6.10** from the per-scale bounds of Table 1 (`TableBudget`) | `goodAll_prob_ge_table` |

## The refined top-level hypothesis (`Top.lean`, and `Fix.lean`)

`Theorem21InputsSp` is `Theorem21InputsFix` without Lemma 6.26 and the Rankin bound for `A`
(replaced by `AbsorbedCoupling`, (HBS) and the cluster event, `SparsityInputs`) and with the union
bound `∑ P(Eᶜ) ≤ 1.5/log X₀` replaced by `TableBudget`. `Fix.lean` now factors through
`Theorem21InputsFixP` (the budget stated as `P(G) ≥ 1 - 1.5/log X₀`).

| Claim | Lean |
| --- | --- |
| `Theorem21InputsSp` ⟹ `Theorem21InputsFixP` ⟹ `Theorem21InputsDec` | `theorem21InputsFixP_of_sp`, `theorem21InputsDec_of_fixP` |
| Theorem 2.1 / **Corollary 2.2** from `Theorem21InputsSp` | `theorem21_of_sp`, `corollary_2_2_of_sp` |

## Still assumed

- The per-window queue data (`QueueWindowData`), the landing data of Corollary 3.8 (`Landing`,
  `LandingInit`) and `Lemma48PiecesCount`.
- The per-event probability bounds of Table 1 (`TableBudget`) and the adaptedness of the events.
- (HBS) for the realised system and the cluster event (Proposition 6.11) on the good event.
- The coupling: the system `P(ω)`, the origin of its primes, `A`, `u_a`, the latest-prime map and
  the slot model are data related by `AbsorbedCoupling` and the hypotheses above, not built from
  the jitters.

# The realised system, `A`, `u_a` and the latest-prime map built from the jitters

The PDF was not available in this step. The work below follows the existing formalization and
the earlier notes. No axioms are added. The new results use the standard axioms, plus
`Lean.ofReduceBool` / `Lean.trustCompiler` through the existing certified computations.

## Construction (`Beurling/Construction/Realised.lean`)

| Object | Lean |
| --- | --- |
| Any countably infinite family of reals with finitely many members below each bound can be listed by `ℕ` in non-decreasing order | `exists_mono_equiv_nat` |
| Index set of the realised primes: the rational primes `p < X₀` and the relative slots where the greedy rule places a prime | `RealisedIdx`, `realisedVal` |
| **The realised system `P(ω)`**: those primes in non-decreasing order (a fixed default system if the conditions below fail) | `realisedSystem` |
| **The origin of its primes** (rational, or the slot of decision) | `realisedSrc`, `realisedOrigin` |
| Latest prime in the decision order, from the origin data | `keyOf`, `latestIdxOf`, `PrimeOrigin.latestPrime_eq` |
| **The absorbed set (5)**: `n` with `log n ≥ 10⁷` that are the value of an element whose latest prime is jittered and `< y(n)` | `absorbedSetOf`, `realisedA` |
| **The latest-prime map** of `A` | `latestOf`, `realisedLatest` |
| **`u_a`**: the solution `u ≥ 0` of `u + u^{θ/2} = a` | `solveU` |

## Results

| Claim | Lean |
| --- | --- |
| For `H = max(H_std, M̄₁²)`, jitters in `[0,1]`, target `⌊x⌋` below `X₀` and infinitely many placed primes, the realised primes form a Beurling system (values `> 1`, finitely many below each bound) | `realisedOK_of` |
| The placed prime of slot `k + 1` is `≥ 7/8` of the slot start, which is `≥ X₀`; finitely many slot starts lie below each bound | `primeValueOf_ge`, `finite_slot_le` |
| **`AbsorbedCoupling` for the constructed data** | `absorbedCouplingOf`, `realisedCoupling` |
| Elements of `A` satisfy `log n > (log X₀)²` and `n > 2X₀` | `realisedA_large` |
| **`X₀ ≤ u_a` and `u_a + u_a^{θ/2} = a` for `a ∈ A`** | `realisedU_spec` |
| `Theorem21InputsJ ⟹ Theorem21InputsSp`; Theorem 2.1 and **Corollary 2.2** from `Theorem21InputsJ` | `theorem21InputsSp_of_J`, `theorem21_of_J`, `corollary_2_2_of_J` |

`Theorem21InputsJ` is `Theorem21InputsSp` with these changes. `P(ω)`, `A`, `u_a`, the
latest-prime map and the coupling are no longer inputs: they are the constructed objects. The
condition `X₀ ≤ u_a`, `u_a + u_a^{θ/2} = a` is proved, not assumed. One new condition is added:
the greedy rule places infinitely many primes. Without it the realised primes would not tend to
infinity.

## Still assumed

- The slot model `M(ω)`, i.e. the target `T`, the composite arrivals and the counts `V`. The
  target is pinned by the formula `T = target(…)`, but it is still data. The arrivals are not tied
  to the composites of `P(ω)`. Building the slot model from the jitters needs a recursion over
  slots: arrivals depend on earlier primes, and the target depends on `A` and the designed heights.
  That recursion also needs analytic bounds on the slot gaps, which are not formalized.
- The construction scales `a_k`.
- `QueueWindowData`, the landing data (`Landing`, `LandingInit`) and `Lemma48PiecesCount`.
- The per-event probability bounds of Table 1 (`TableBudget`) and the adaptedness of the events.
- (HBS) and the cluster event on the good event (`SparsityInputs`).
- That the greedy rule places infinitely many primes.

# Removing adaptedness and (HBS) from the hypothesis (`Theorem21InputsK`, `Theorem21InputsL`)

New files in `RequestProject/Beurling/Construction/`: `Unadapted.lean`, `HBSLag.lean`,
`RigidFine.lean`, `HBSPieces.lean`, `HBSLocal.lean`, `RealisedLow.lean`, `HBSEps.lean`,
`HBSDerive.lean`, `NoHBS.lean`. All build with no `sorry`. The main results use only the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) plus `Lean.ofReduceBool` and
`Lean.trustCompiler`.

## Adaptedness of the failure events is no longer assumed

The first-failure argument behind Lemma 6.10 does not need the events to be adapted. Write
`Gᶜ` as the disjoint union of the sets "event `i` is the first one to fail". The bound
`P(G) ≥ 1 - ∑ P(Eᵢᶜ ∩ {no earlier failure})` then holds for any countable family
(`goodAll_prob_ge_firstFailure'`, `goodAll_prob_ge_table'`).
`Theorem21InputsK` is `Theorem21InputsJ` without `FailureAdapted`, with
`theorem21InputsK_of_J`, `theorem21_of_K` and `corollary_2_2_of_K`.

## (HBS) for the realised system is derived (`sparsityInputs_of_cluster`)

The parameters are `X₀⁻ = X₀ - H(X₀)/2` and `η₁ = η₂ = 10⁻³`. The error profile is
`ε₁(v) = 10 v^{-2/5} + min(κ + (κX₀+1)/v, Ψ(2v, X₀)/v)` (`hbsEps`).

| Step | Lean |
| --- | --- |
| `|N(x) - T(x)| ≤ x^η` from `QueueWindowData`, `Landing` and `LandingInit` alone | `lag_of_slotData` |
| Fine rigid error `|E_rig(x)| ≤ κx + κX₀ + 1` | `abs_rigidErr_le_fine` |
| Absorbed error, needing the density bound only on `[X₀, x]` | `absorbed_target_error_cap_loc` |
| Lemma 6.26 at one height `v`, needing (HBS) only up to `2y(2v)`; and `2y(2v) < X₀` or `2y(2v) ≤ v/2` | `lemma626_local`, `two_absorbYAt_two_le` |
| `N(v) = ⌊v⌋` below `X₀⁻` for the realised system | `realised_floor_eq` |
| `Ψ(Y, X₀) ≤ Y^{0.85}` when `log Y ≥ 20 X₀^{0.3}` (Rankin's bound with the Euler-product estimate) | `smoothCount_le_rpow_large` |
| Geometric bound for sums of `w_k^{-a}` over dyadic points | `dyadic_rpow_sum_le` |
| `ε₁(v) log v ≤ 10⁻³` and `∑_k ε₁(w_k) ≤ 10⁻³` | `hbsEps_mul_log_le`, `hbsEps_dyadic_sum_le` |
| `|N(v) - ⌊v⌋| ≤ ε₁(v) v` on `[X₀⁻, X₀)` and on `[X₀, ∞)` | `hbs_err_low`, `hbs_err_high` |
| **(HBS) from the slot data and the cluster event**, by strong induction on `⌊v⌋` | `sparsityInputs_of_cluster` |

`Theorem21InputsL` is `Theorem21InputsK` with `SparsityInputs` replaced by the cluster event alone.
The two hypotheses are equivalent (`theorem21InputsK_of_L`, `theorem21InputsL_of_K`).
Theorem 2.1 and **Corollary 2.2** follow from it (`theorem21_of_L`, `corollary_2_2_of_L`).

## Still assumed (in `Theorem21InputsL`)

- The slot model `M(ω)` and the construction scales `a_k`. This needs the slot-by-slot recursion
  that links the arrivals to the composites of `P(ω)`, together with bounds on the slot gaps.
- `QueueWindowData`, `Landing`/`LandingInit` and `Lemma48PiecesCount`. All of them depend on that
  link between the model and `P(ω)`.
- The per-event probability bounds of Table 1 (`TableBudget`).
- The cluster event on the good event.
- That the greedy rule places infinitely many primes.

## Construction scales, the arrival link and the landing data (this update; uses `beurling-paper.pdf`)

| Step | Lean | File |
| --- | --- | --- |
| The scales `a_k := sup{a ≥ X₀ : a + 2H(a) ≤ x_k}`, with `X₀ ≤ a_k`, `0 < a_k ≤ x_k ≤ 1.001 a_k` | `constructionScale`, `constructionScale_spec` | `Construction/Scales.lean` |
| `Theorem21InputsM`: `Theorem21InputsL` with the scales fixed to `a_k` | `theorem21InputsL_of_M`, `corollary_2_2_of_M` | `Construction/Scales.lean` |
| The arrivals are the composites of `P(ω)` slot by slot | `ArrivalsLinked` | `Construction/Link.lean` |
| Infinitely many primes are placed (derived from the link and the target formula) | `placed_infinite_of_linked` | `Construction/Link.lean` |
| `Theorem21InputsN`: the infinitude condition replaced by `ArrivalsLinked` | `theorem21InputsM_of_N`, `corollary_2_2_of_N` | `Construction/Link.lean` |
| `N(x) = 1 + #(primes ≤ x) + #(composites ≤ x)` | `realised_N_eq` | `Construction/ElemCount.lean` |
| Primes `≤ x` = rational primes + placed at slots `< k` − `E₋` + `E₊` | `realised_primes_eq` | `Construction/SlotCounts.lean` |
| Lemma 3.6 (count identity) from its base case | `V_eq_count` | `Construction/SlotCounts.lean` |
| `C ≤ A_k` | `compIoo_le_slotArr` | `Construction/SlotCounts.lean` |
| `E± ≤ H(x) + 3/2` from the window count of placed slot starts and the slow variation of `H` | `Em_le`, `Ep_le` | `Construction/SlotCounts.lean` |
| `H(x) ≤ H(X₀) + 2` on the initial range `x < X₀ + 2H(x)` (proved) | `capH_initial_le` | `Construction/SlotCounts.lean` |
| `Landing` and `LandingInit` for the construction | `landing_of_linked`, `landingInit_of_linked` | `Construction/LandingDerive.lean` |
| `Theorem21InputsO`: the landing data replaced by `SlotFacts` and `JitterWidthRegular` | `theorem21InputsN_of_O`, `corollary_2_2_of_O` | `Construction/LandingDerive.lean` |

## Still assumed (in `Theorem21InputsO`)

- The slot model `M(ω)` as data. Its target is the paper's target `(6)`, and its arrivals are tied
  to the composites of `P(ω)` by `ArrivalsLinked`. The slot-by-slot construction itself, which
  needs causality (Lemma 3.5) and slot-gap bounds, is not built.
- `SlotFacts`, which holds pathwise in the paper:
  - the base case of Lemma 3.6: the elements below `s_{j₀}` number `X₀`, and no composite lies in
    `(X₀, s_{j₀})`;
  - the window count: a window `(a, b]` contains at most `1.01 (b − a) + 1` starts of slots that
    receive a prime (§3.4 and Corollary 3.8, with `T'_cont ≤ 1.01`).

  The paper proves these off the null event `N=`. Here they are required on the good event.
- `JitterWidthRegular`: if `x ≤ y` and `y − H(y)/2 ≤ x`, then `H(y) ≤ H(x) + 1/4`. This is a
  deterministic property of `H` (Theorem 6.23(c)); its `M̄₁²` part is not proved.
- `QueueWindowData` and `Lemma48PiecesCount`.
- The per-event probability bounds of Table 1 (`TableBudget`).
- The cluster event on the good event.
