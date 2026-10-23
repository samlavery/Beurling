# R8: Independent reproduction of the Appendix B certificates

The checker was cert-repro, a fresh AI agent. It was not allowed to write files, so the lead saved its messages here. Its
scripts were in `/tmp/rhscratch/cert-repro/`, which is temporary.

**Inputs.**
- Snapshot `874bf72`, extracted to `/tmp/rhscratch/cert-repro/src`.
- `rankin_R.py`, together with the working-tree `B-certificates.tex` and `05-queue.tex`, copied to
  `/tmp/rhscratch/cert-repro/new/`. The `rankin_R.py` and App B copies are byte-identical to commit `4b24c72`, which landed
  after the snapshot.

**Environment.** Python 3.15.0, python-flint 0.9.0 (`/tmp/rhscratch/flintenv/bin/python`), macOS, 12 cores. All runs used
`-I -B`. Nothing under `~/work` was modified.

## Verdict

- **Re-runs.** All 18 App B commands, and the 2 double-precision twins, run cleanly, and every quoted output reproduces
  exactly. The only differences are fields that App B itself marks as omitted or varying, and one whitespace artifact at a
  line-wrap point.
- **Independent re-implementations.** These were written from the paper text before the scripts were read. They confirm every
  proof-step claim, in rigorous ball arithmetic or with exact integers or rationals:
  - bs-cert: region Z2 and the three one-variable checks;
  - finite-n: all six lines;
  - x0-band: B(n) ≤ 5/12 for 2 ≤ n ≤ 10⁶, with equality only at n = 6;
  - `rankin_R`: all six constants. R(σ) is computed by a different method, the prime zeta function via Möbius inversion.
- **Script review.** Each proof-step script computes what the paper claims, rounds in the safe direction (up to the
  ≤ 10⁻¹⁵ float constants of C5), and covers the whole claimed range.
- **Defects.** None BLOCKING. Three FIXABLE and eleven COSMETIC (C1–C11):
  - F1: the rigour of `finite_checks.py`;
  - F2: ball-arithmetic constants in the text that are not certified;
  - F3: the bound S of bs-cert is specified only in the code.
- **Audit item.** "Proof-critical numerical certificates: full independent reproduction outstanding" can be closed, subject
  to the limitations in §8.

## 1. Inventory

| # | Certificate | Run command (repo root) | Role in App B | Paper result that depends on it | Output quoted in App B |
|---|---|---|---|---|---|
| 1 | bs-cert, main region | `cert_run_arb_patched.py 1.05 10` (needs flint); `cert_run_arb.py 1.05 10` "gives the same result" | **proof step** | Thm bs, Step 7(iii), region Z2 (30τ ≤ ℓ < 10¹⁸, u ≥ 2), feeding Thm bs, Lemma bs-profile, Cor saias, Lemma si and others | `[patched seams] q=1.05 bands=403 cells=302013 failed=0 min certified l*S=2.491e+06 at (82792994654.45967, …, 200.127…, 210.133…, False)`, run time omitted |
| 2 | bs-cert, one-variable checks | `aux_cert_arb.py` | **proof step** | (i) c₀ ≥ K′u²log(1+u) on [27, 4·10⁵] (Thm bs, Step 7(ii)); (ii) the one-step inequality of Lemma smooth-v on [1, 10⁶]; (iii) the same on [1, 2], with X(u) and the allowance | `cells=9609 … margin=0.189`; `cells=13823 … 1.724`; `cells=1387 … 0.829` |
| 3 | bs-cert twins `bs_cert.py`, `cert_run.py`, `aux_cert.py` | no command given | cross-check | none | "minimum 2.598·10⁶" |
| 4 | finite-n | `finite_checks.py` | **proof step** | Lemma cm (i), (ii), (iii); Lemma smooth-v at small heights (C₀ = 0.70, excess 0.1334); F₁/₂ ≤ 1.33 (squarefree average, 04f); Lemma threshold-mass (p < 400) | 7 lines, plus a runtime line marked as varying |
| 5 | x0-band, small range | `cd certificates/x0-band && python3 -I -B x0band_exact.py 1000000` | **proof step** | Prop xb-ranges(i) (Lemma xb): j_{X0} ≤ 0.4209, feeding Prop 3.18(b) and the g1 margin | 8 lines (abridged). `x0band.py` is an earlier exploration, not part of the certificate. |
| 6 | `rankin_R.py` (working tree, 4b24c72) | `capl-cert/rankin_R.py` (needs flint) | **proof step** (working-tree preamble, correction 49) | Lemma rowweights (c), (e), feeding Thm caplw, Steps 3–4 (T2) | 7 lines, ending `ALL OK` |
| 7 | capl-cert: `analytic_capl`, `caplw_check_independent`, `cert_capl`, `needs`, `raise_max` (`capl_model` is a library) | `python3 -I -B certificates/capl-cert/<name>.py`, ×5 | cross-check | Thm caplw (Steps 1–5). `raise_max` gives the value 1.3·10⁻⁸ in Remark caplw-numerics, against the analytic bound 10⁻⁶ that the proof uses | `analytic_capl`: prose (s_H = 5.9745; "decreasing"; 4842/5072/5302/5763/6684/7605 points, 0 failures). `caplw_check_independent`: 2 lines. `cert_capl`: first 2 lines. `needs`: none. `raise_max`: 2 lines |
| 8 | lemma-sc | `sc_check.py 1`; `sc_check.py 7 20000 7`; `sc_check.py 11 60000 5`; `sc_greedy.py 5 30000 8`; `sc_check_independent.py` | cross-check | Lemma SC, which is proved in App A (A-rankfull l.522 quotes 13,433) | 5 dictionaries |
| 9 | svl-stress | `svl_stress.py` | cross-check | Thm svl | 4 lines |
| 10 | depcheck | `depcheck.py` | cross-check | the bookkeeping of §logic (01-setup l.112 quotes 79 nodes, 193 edges, 27 strictly earlier) | 1 line |

**The preamble against the text.**
- The snapshot's B-certificates.tex:8–11 lists three proof steps: bs, finite-n and the x0-band small range. The working tree
  (= 4b24c72) adds `rankin_R.py`.
- Every "computer-assisted", "direct computation" or "see App cert" citation in 04a, 04c, 04e, 04f and 04x matches this list.
- The one exception is 01-setup.tex:72, which calls "Theorem caplw and eq:mu1sum" computer-assisted. See F2.

## 2. Re-runs (byte comparison)

**Method.** App B wraps long lines, with continuations indented by 4 spaces. The checker unwrapped them and compared byte for
byte with the outputs.

| Run | Wall time | Result against App B |
|---|---|---|
| `cert_run_arb_patched.py 1.05 10` | 6.4 s (54 s CPU) | IDENTICAL after removing ` time=6s` (App B omits the run time) |
| `cert_run_arb.py 1.05 10` | 6.2 s | the same numbers, without the `[patched seams]` prefix, as expected |
| `aux_cert_arb.py` | 0.8 s | IDENTICAL (3 lines) |
| twins `cert_run.py 1.05 10` / `aux_cert.py` | 6.9 s / 0.5 s | min 2.598e+06, as App B says; aux margins 0.1895 and 1.724 |
| `finite_checks.py` | 1.1 s | IDENTICAL, except `runtime 1.0 s` against `2.0 s` (App B says the runtime varies) |
| `x0band_exact.py 1000000` | 5.0 s | IDENTICAL. App B abridges the `top:` line; its 6 entries are the first 6 of the 10 printed |
| `analytic_capl.py` | 1.9 s | matches the prose: s_H = 5.9745; "decreasing" on all 5 lines; 4842/5072/5302/5763/6684/7605 points, 0 failures; 35,268 in total |
| `caplw_check_independent.py` | 0.6 s | IDENTICAL. The only diff is a double space at the wrap point, collapsed by the unwrap; an artifact, not a real difference |
| `cert_capl.py` | 1.9 s | first two lines IDENTICAL |
| `needs.py` | 0.1 s | diagnostic; App B quotes no output |
| `raise_max.py` | 5.3 s | IDENTICAL |
| `sc_check.py 1` / `7 20000 7` / `11 60000 5` | 6.1 / 8.2 / 9.3 s | IDENTICAL |
| `sc_greedy.py 5 30000 8` / `sc_check_independent.py` | 22.7 / 2.8 s | IDENTICAL |
| `svl_stress.py` | 2.1 s | IDENTICAL |
| `depcheck.py` | 0.02 s | IDENTICAL |
| `rankin_R.py` (working tree, identical to 4b24c72) | 1.9 s | IDENTICAL to the working-tree App B block |

Nothing was slow, so no background or reduced runs were needed.

## 3. Proof-step certificates

For each certificate, the checker read the lemma first, wrote its own implementation, compared the results, and only then
read the script.

### 3.1 bs-cert (Thm bs, Step 7(ii)/(iii); the one-step inequality of Lemma smooth-v)

**Independent implementation.** The checker derived its own lower bound S ≤ Σ from Steps 2–6 and (R1)–(R4).
- **Part I** (w ∈ [u−1, u]): chord and mean-value bounds. h′ is increasing on [1, ∞), checked by hand: both terms of h′
  increase.
- **Part II** (w ∈ [u, Ū]): a piecewise-linear majorant of D, with about 20 geometric pieces and a finite upper end Ū, so no
  condition r₀ > γ is needed.
- **E₁, E₂, E₃** are bounded with the same majorants. ℓη_f gets an explicit five-term bound, evaluated at the worst endpoint of
  each piece.
- **T** comes from Step 6, maximised over y.
- **Enclosures of r:**
  - r_low comes from the recursion r(v) ≥ g(r(v−1)), seeded on a 1/256 grid with the exact r on (1, 2], combined with the
    integer-grid chain;
  - r_up uses the sharper form of (R4), log((x+1−δ)/δ)/(1−δ), with δ optimised.

**Results.**
- **Z2.**
  - q = 1.05: 403 bands, 544,829 cells, 0 failures, no bisection needed. The minimum certified ℓS is 3.25·10⁶, at
    ℓ ≈ 1.2·10¹⁰, u ∈ [157, 165]; 39 s on 10 workers.
  - q = 1.03: 1,172,150 cells, 0 failures, minimum 3.55·10⁶; 84 s.
  - The script gives 2.491·10⁶. They agree.
- **c₀ on [27, 4·10⁵]:** 9,609 cells, 0 failures, minimum 0.213 on [27, 27.027]. The script gives 0.189 on the same cell; the
  difference comes from the sharper r_up.
- **The one-step inequality of Lemma V on [1, 10⁶]:** 13,823 cells, 0 failures, minimum 2.08. The script gives 1.724.
- **Lemma V on [1, 2]**, with X(u), 22e^{−0.4L} and the allowance: 0 failures, minimum 0.8296. The script gives 0.829.

**A numerical sanity check (not rigorous).** The checker evaluated Σ(ℓ, u; τ) directly from its definition, using Dickman's ρ
from a stable discretisation of uρ(u) = ∫_{u−1}^{u} ρ. At 21 points (ℓ, u, τ), covering u-cells, v-cells, points near u = 2,
near u₀ and near the top edge, the numerical ℓΣ was always ≥ the checker's bound ≥ the script's bound. At τ = 10⁸ the
checker's bound is 85–95% of ℓΣ.

**Script review** (bs_cert_arb.py, ivarb.py, cert_run_arb(_patched).py, aux_cert_arb.py). The script computes what Step 7(iii)
says.
- **Part I.** β_I, β_II, α and β_a are as in the paper, and α_A = (B/ℓ)u³(3u−4)log(1+u)/(u−1)² ≤ (B/ℓ)h′(u−1).
- **Part II.** γ₁ and γ_max use h′ ≤ 8(1+w)²log(2+w), which holds with room (5.21 is enough). tailII (l.62) is
  ∫e^{−r₀s}(e^{γ(s)s} − 1).
- **Masses.**
  - Mm1 (l.63) uses the exact mass π(w ≥ u) = 1/(u r(u)), from (R1).
  - E₂, Part I (l.66), uses ∫_{u−1}^{u} ρ(w−1) = (u−1)ρ(u−1), also from (R1).
- **eta()** (l.68). Term by term it dominates:
  - κ/m²;
  - |∂_m A|;
  - |∂_m a|, via m ≥ ℓ/2 and ((1+w)/w)^{3/2} ≤ 2k_u;
  - (1+w)²/ℓ·|∂_w Q|.

  It is increasing in w, so evaluating it at u, u+60 and Ū covers each piece.
- **Tail and convergence.** E_T follows Step 6. The script returns −inf, so the cell fails, unless r₀ > γ₁ and r₀ > γ_max.
- **Rounding direction.** Ball arithmetic throughout. Float conversions go through nextafter in the safe direction, and r_up
  has a (1+2⁻⁵⁰) margin. The exception is C5.
- **Cover.**
  - The ℓ-bands chain exactly from 3·10⁹ to 10¹⁸.
  - The u-cells cover [2, split].
  - The v-cells start at va = fdn(split − fup(ℓ_b^{1/4})) and end at vtop = fup(Ū(ℓ_b) − fdn(ℓ_a^{1/4})), so both seams are
    closed for every ℓ in the band.
  - Bisection midpoints are shared, and each cell is a box evaluated in balls. There are no gaps.
- **The inputs match 04a/04c.** B = 11, K′ = 2.2, κ_min = 4e8, κ_max = 4ℓ/30 + 1500, Ū at τ = 1e8, S₁ = 60, K = 3.2,
  K_M = 1.01, C₀ = 0.70, 0.7627 and log 72/100, e^{0.141}, and the ranges [27, 4e5], [1, 1e6], [1, 2] and [3e9, 1e18].
- **The analytic tails check out.** r_low(4e5) = 15.57 ≥ 15.3, and 12.79·log(u+1) for u > 1e6.
- **Defects:** F3, C4, C5, C6 and C9.

### 3.2 finite-n

**Independent implementation.** arb at 96 bits plus exact Fractions, with the checker's own sieve and its own step-structure
reductions.

| Line | Independent (rigorous) | Script | Bound used | Agrees |
|---|---|---|---|---|
| 1 | 0.68023948 at x = 5; at x = 1500, 0.71x − (x log 2 + 3 log x + 3) = 0.3396, increasing | 0.680239 | 0.71 | ✓ |
| 2 | S − log x ∈ [−0.75203870 (x → 3⁻), 0 (x = 1)]; 665,134 prime powers | same | [−0.753, 0] | ✓ |
| 3a | max = Σ_{n=73}^{145} 1/n = 0.6965835661 on [72.5, 73); log 2 + 1e-4 = 0.69324718 | 0.696584 | 0.70 | ✓ (see C1) |
| 3b | 5/6 exactly, on [1.5, 2) | 5/6 | 0.8334 | ✓ |
| 4 | 1.329634949 at y = 7 | 1.329635 | 1.33 | ✓ (see C2) |
| 5 | 0.24736173 at p = 7 | 0.247362 | 0.25 | ✓ |
| 6 | 0.7553665108 + tail ≤ 1.712e-6, giving 0.7553682226 | 0.7553682 | 0.75537 | ✓ (margin 1.8e-6) |

**Script review.**
- The step-structure reductions are correct: line 1 uses ψ(x/2) = ψ(⌊⌊x⌋/2⌋), and the (k+2)//2 indexing of line 3a is right.
- The inputs (1500, 1e7, 72, 1e4, 1e6, 400) match 04a, 04e and 04f.
- **Defects.** Rigour: F1. Others: C1, C2 and C3.

### 3.3 x0-band (Prop xb-ranges(i))

**Independent implementation.** Exact integers only.
- X(d)/d is replaced by ⌈2⁴⁰X(d)/d⌉/2⁴⁰, and λ = 10001/10⁴ is exact.
- The check 12W(n) ≤ 5·4·10⁴·2⁴⁰·n is exact.

**Results.**
- **No violation of B(n) ≤ 5/12 for 2 ≤ n ≤ 1e6, and equality holds only at n = 6.**
- The suprema over n ≥ 10^a are 0.277781, 0.088059, 0.022826, 0.007607 and 0.002121, identical to the script, as are H_max and
  X_max.
- Analytic ingredients, in arb:
  - A(1.8 − 3e-6) = 7.4914232 ≤ 7.4915, and ¼·7.4915·2^{0.2} = 2.15137 ≤ 2.152;
  - the tail bound at n = 1e6 is 0.13742 ≤ 0.14, and it decreases in n;
  - 4/√6 = 1.63299 ≤ 1.64;
  - 1.010102·5/12 = 0.420876 ≤ 0.42088.

**Script review.**
- The B(n) formula matches 04x:234–235 exactly.
- Python's array('q') raises on overflow anyway.
- The floats use only +, × and ÷, which IEEE rounds correctly. There are at most 240 terms, and the (1+1e-9) inflation covers
  both the rounding and the fact that λ = 1.0001 is stored slightly low.
- Every n from 2 to 1e6 is covered.
- **Defect:** C7.

### 3.4 rankin_R.py (Lemma rowweights (c), (e); working tree)

**Independent implementation, by a different method.** R(σ) = Σ_{k≥2} P(kσ)/k, with the prime zeta function computed by
Möbius inversion, P(s) = Σ μ(n)/n·log ζ(ns), with rigorous tails (n ≤ 120, k ≤ 250, 300 bits).

**Results.**
- R(0.69) = 0.759059831497 ≤ 0.7618 ≤ 0.77.
- R(0.75) = 0.620874531338 ≤ 0.6212 ≤ 0.63.
- A direct prime sum to 1e6, with the checker's own tail bound, gives intervals that contain both values.
- Ei(11) − e¹¹/11 − e¹¹/121 = 133.474964 ≤ 134.
- f(11) = 0.5208 < 1, and f′ < 0 for x > 2.
- (3/2)^{3/4} = 1.3554030 ≤ 1.3555.
- Ei(¼ log 2) = −0.9944990 ≥ −1.

**The surrounding text of (c) and (e), checked by hand.** All of these are correct:
- the two integrations by parts behind the constant 2.75;
- Ein ≤ Ei for x ≥ 11;
- t₀ ∈ [e, e^{1.45}];
- 1.26η/(1−η) ≤ 0.566;
- ηΛ ≥ 11.43;
- the Ei substitution in (e);
- 5.04 → 5.05;
- 1.3555·4/0.99 = 5.477 ≤ 5.5.

**Script review.** The sum over p ≤ 1e7 is done in arb with string constants, and the tail bound is valid. **Defect:** C8.

## 4. Cross-checks

All the quoted outputs reproduce (§2). Independent spot checks:
- **depcheck.** The checker re-parsed the dep() calls and ran Kahn's algorithm.
  - 79 nodes, 193 distinct edges (no duplicates) and 27 strictly earlier; the same-time subgraph is acyclic.
  - Adding eq:sF3p+eq:sF4 → thm:caplw(a) produces exactly the cycle App B describes.
  - Every node label exists as a \label in the source, and every cite key is in refs.bib.
- **s_H**, by arb bisection: s_H = 5.97453803169 ± 4e-12. This matches both "5.9745…" and the script's 5.974538031693934. The
  ramp claim of Step 2 also holds: d log γ*/ds ≤ 0.5306 ≤ 0.532 on [s_H, s_H+1].

## 5. Hygiene

- **Scripts the paper names:** all exist. edge_toy_c47.py is mentioned only in a LaTeX comment (06-base-range.tex:103). It
  exists in review/recheck/, not in certificates/.
- **Scripts in certificates/ that the paper does not name:** only bs_cert_arb.py (C9). In the working tree, rankin_R.py is
  named.
- **Numerical claims with no certificate script:** see F2. All of them verify.
## 6. Defects

Nothing is BLOCKING. "wt" below means the working tree (= 4b24c72).

### F1 (FIXABLE): the rigour of finite-n rests on libm and hard-coded error strings

**Where.**
- certificates/finite-n/finite_checks.py, header lines 5–8. Lines 1, 2, 3a, 4 and 6 are computed in floating point, with
  math.log and n**-0.5.
- The "err < …" bounds are literal strings, at l.51, 79, 96, 121 and 139.
- The comparison in line 5 is a float (l.128).
- App B (B-certificates.tex:89–91) says that "each such line prints a bound on its rounding error". In fact it prints
  constants, not computed bounds, and IEEE does not guarantee correct rounding for log or pow.

**Status.** Every line holds rigorously. The checker's arb/Fraction re-implementation (3 s) gives margins ≥ 1.8e-6 against
ball radii ≤ 4e-11.

**Exact fix.**
1. Replace finite_checks.py with an arb version. The checker's finite_indep.py is a ready candidate: it prints the same
   quantities as balls, together with True/False comparisons against the paper's bounds.
2. Replace B-certificates.tex:89–91 ("Lines 3b and 5 use exact rational arithmetic. The other lines are floating-point sums …
   rounding error, which is far below the margin to the bound used in the paper. The script uses only the Python standard
   library.") with: "The products in lines 3b and 5 are exact rationals; every other quantity is computed in ball arithmetic
   (\texttt{python-flint} 0.9.0), and each comparison with the bound used in the paper is decided on the ball."
3. Change the run line (l.93) to "(about 3 seconds, with \texttt{python-flint})", and regenerate the expected-output block from
   the new script.

### F2 (FIXABLE): constants computed in ball arithmetic with no certificate, and an inconsistent "computer-assisted" list

**Where.** These constants are used in proofs, some of them explicitly "in ball arithmetic", but no script in certificates/
computes them and App B does not list them:
- 04x-x0band.tex:254–255: A(1.8−3·10⁻⁶) ≤ 7.4915. x0band_exact.py:40 hard-codes A(1.8) = 7.49109924 instead.
- 04x-x0band.tex:279–281: A(1.77) = 13.08 (≤ 13.1 used); the abscissa 1.7286; Σ_{w≥2} w^{ε−2} ≤ ζ(1.97) − 1 = 0.674.
- 04x-x0band.tex:328: A(1.77).
- 04x-x0band.tex:338–340: Σ_{w≥2} w^{−1.97} = 0.674 and −ζ′(1.97) ≤ 1.0001 "(ball arithmetic)".
- 04k-kernels.tex:139–141: ρ₀ = 1.7286…, A₀(0.03) = 2.0673 (≤ 2.07 used), A₁(0.03) = 9.409 (≤ 9.42 used).
- 04k-kernels.tex:144–145: ζ(1.8) + X₀^{−0.7} ≤ 1.883, giving Σ H(m)m^{−1.8} ≤ 8.6.
- 06-base-range.tex:169: Ein(2) < 3.69.
- 06-base-range.tex:173 and 264–267: I₁ = 14.92, I₂ = 214.8, I₃ = 6.7; total ≤ 690/Λ (eq:mu1sum).

Separately, 01-setup.tex:71–72 says "in particular the computer-assisted Theorem~\ref{thm:bs}, Theorem~\ref{thm:caplw} and
\eqref{eq:mu1sum}". That contradicts B-certificates.tex:8–11, which lists bs, finite-n and x0-band as the proof steps (plus
rankin_R in wt), and l.163 ("Theorem caplw is proved analytically").

**Status.** All values verify:

| Constant | Computed | Bound used |
|---|---|---|
| ζ(1.97) − 1 | 0.673984 | 0.674 |
| −ζ′(1.97) | 1.00004 | 1.0001 (margin 6e-5) |
| A(1.77) | 13.0822 | 13.1 |
| A(1.8−3e-6) | 7.4914232 | 7.4915 |
| ζ(1.8) | 1.88223 | 1.883 |
| ρ₀ | 1.7286472 | 1.7286… |
| A₀(0.03) | 2.06733 | 2.07 |
| A₁(0.03) | 9.40888 | 9.42 |
| Ein(2), with the paper's (e^w−1)/w convention | 3.6838715 | 3.69 |
| I₁ / I₂ / I₃ | 14.9154 / 214.771 / 6.696 | 14.92 / 214.8 / 6.7 |
| (2.02/log 2)(I₁+I₂+I₃) | 688.9 | 690 |

The checks of I₂ and I₃ used float quadrature, not ball arithmetic.

**Exact fix.**
1. Add certificates/constants/consts.py, based on the checker's consts_indep.py. Replace its float quadrature for I₂ and I₃ by
   rigorous bounds: I₁ has a closed form; for I₂ and I₃, substitute v = e^t and use monotone Riemann sums in arb, or flint's
   acb.integral.
2. Add an App B subsection, "Numerical constants (\texttt{constants})", listing the values above, with the command
   `python3 -I -B certificates/constants/consts.py`.
3. Add it to the preamble at B-certificates.tex:8–11 ("Five of them are steps of the proof: …").
4. In 01-setup.tex:72, replace "in particular the computer-assisted Theorem~\ref{thm:bs}, Theorem~\ref{thm:caplw} and
   \eqref{eq:mu1sum}." with "in particular Theorem~\ref{thm:bs}, Theorem~\ref{thm:caplw} and \eqref{eq:mu1sum}, which use
   computer-assisted steps (Appendix~\ref{app:cert})."
5. Optionally, change x0band_exact.py:40 to use 7.4915 without λ, so that its printed tail is the paper's expression,
   0.137423.

### F3 (FIXABLE, documentation): the bound S of bs-cert is specified only in the code

**Where.**
- 04c-saias.tex:533–569 (Step 7(iii)) gives S only in outline: the Part I/II majorants, β_I, α, β_a, a two-slope γ, and "the
  same majorants (with a two-piece bound for η_f) bound E₁, E₂ and E₃".
- The actual formulas exist only in certificates/bs-cert/bs_cert_arb.py: tailII l.62, Mm1 l.63–64, E₁ l.65, E₂ l.66,
  eta l.68–73, E₃ l.74, T l.76–90.
- App B:70–73 names the variables but not the file (C9).

**Status.** The checker verified every term (§3.1), and a bound rebuilt independently from the outline passes with
0 failures. But a human referee cannot check the script's S from the paper alone.

**Exact fix.** Insert in 04c after l.553 (the Part II item), or as a paragraph in App B §bs-cert:

```
With $r:=r(u)$, $r_0:=r(u-1)$, $S_1:=60$, $q:=e^{-(r_0-\gamma_{\max})S_1}/(r_0-\gamma_{\max})$ and $d_+:=(d+c_u)_+$,
\begin{align*}
M-1&\le(e^{\beta_I}-1)\big(1-\tfrac1{ur}\big)+\tfrac{e^{\beta_{II}}-1}{ur}-e^{\beta_I}(1-e^{-\alpha})\big(1-\tfrac1r\big)
   +\tfrac{e^{\beta_{II}}}u\Big(\tfrac{\gamma_1}{r_0(r_0-\gamma_1)}+q\Big),\\
\ell E_1&\le2K'u^2r_0e^{\beta_I-\alpha},\qquad
\ell E_2\le K'\tfrac u{u-1}\Big((u-1)e^{\beta_I}+e^{\beta_{II}}\big(\tfrac1{r_0-\gamma_1}+q\big)\Big),\\
E_3&\le2K'\Big(\bar\eta(u,v)e^{\beta_I}+\tfrac{e^{\beta_{II}}}u\Big(\tfrac{\bar\eta(u+S_1,v+S_1)}{r_0-\gamma_1}
   +\bar\eta(\bar U,\bar U-u_0)\,q\Big)\Big),\\
\bar\eta(w,d)&:=\tfrac{4\kappa_{\max}}{\ell^2}+\tfrac{4B(1+w)^3\log(2+w)}{\ell^2}+\tfrac{d_+}{4(\ell/2)^{5/4}}
   +\tfrac{k_ud_+^2}{2\ell^{3/2}}+\tfrac{(1+w)^2}\ell\Big(\tfrac{2B(1+w)^2(3\log(2+w)+1)}\ell+\tfrac{\sqrt2\,d_+}{\sqrt\ell}\Big),
\end{align*}
$T\le\exp(\kappa_{\max}/\ell+a_V(\bar U+\tfrac12)+E_T)$, and $S:=-\big[(M-1)+E_1+E_2+E_3+T\big]$.
```

Follow it with one sentence of justification:
- the masses π(w ≥ u) = 1/(u r(u)) and ∫_{u−1}^{u} ρ(w−1)dw = (u−1)ρ(u−1) come from (R1);
- η̄ ≥ η_f, because (1+w)/w ≤ 2, m ≥ ℓ/2 and ((1+w)/w)^{3/2} ≤ 2k_u;
- η̄ is increasing in w, so its values at u, u+S₁ and Ū bound it on the three pieces.

### C1–C11 (COSMETIC)

- **C1.** 04a-setup.tex:270 says "gives at most $0.69658$". The true maximum is Σ_{n=73}^{145} 1/n = 0.6965836 > 0.69658, so
  the stated figure is not an upper bound. The bound used, C₀ = 0.70, holds.
  **Fix:** write $0.69659$ there, at finite_checks.py:96 ("paper: 0.69659 <= C0 = 0.70") and at B-certificates.tex:107.
- **C2.** 04f-bridge.tex:117 says "gives the maximum $1.3296$". The true value is 1.3296349, so 1.3296 is not an upper bound.
  The bound used, 1.33, holds.
  **Fix:** write $1.32964$ there, at finite_checks.py:121 and at B-certificates.tex:112.
- **C3.** B-certificates.tex:89 says "Lines 3b and 5 use exact rational arithmetic", but the final comparison in line 5 is a
  float (finite_checks.py:128).
  **Fix:** "Line 3b, and the products of line 5, are exact rationals". F1 supersedes this.
- **C4.** aux_cert_arb.py:27 uses `15 * iexp(-0.4 * L)`, while eq:lemV-onestep (04a:344) has 22e^{−0.4L}. 04a:351–353
  acknowledges this; the difference is 7e^{−40}.
  **Fix:** change 15 to 22 at l.27. At 04a:351–353, delete "(and with $15e^{-0.4L_z}$)" and "(the difference
  $7e^{-0.4L_z}\le10^{-16}$ … is immaterial)". Rerun; the printed margin should stay 1.724.
- **C5.** Decimal constants enter as Python floats.
  - Non-conservative by about 2e-16 relative: aux_cert_arb.py:20 K = 3.2 (α slightly too large); l.27 and l.56 `-0.4 * L`;
    l.59 `I(0.141)`.
  - Conservative: bs_cert_arb.py:5 KP = 2.20; aux_cert_arb.py:20 KM = 1.01, l.50 C0 = 0.70, l.58 0.7627; and arb(12.8) in
    the T of bs_cert_arb.py.
  - So B-certificates.tex:31–34 ("Floating-point numbers enter only as exactly representable cell endpoints and as
    outward-rounded … images") is not literally true. The effect is ≤ 1e-14, against margins ≥ 0.189.
  - **Fix:** use arb strings (K = arb("3.2"), KM = arb("1.01"), C0 = arb("0.70"), KP = arb("2.2"), `L * arb("-0.4")`,
    `I(arb("0.141"))`, `I(arb("0.7627"))`), check that the I wrapper accepts them, and rerun.
- **C6.** B-certificates.tex:30–31 says r_up is "optimised over $\delta$". bs_cert_arb.py:19 takes the minimum over
  δ ∈ {0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5}.
  **Fix:** replace "optimised over $\delta$" with "minimised over $\delta\in\{0.05,0.1,0.15,0.2,0.3,0.4,0.5\}$".
- **C7.** x0band_exact.py never tests B(n) ≤ 5/12 itself. Its values are inflated by 1+1e-9, so B(6) prints as
  0.41667 > 5/12, and "attained only at n = 6, B(6) = 5/12 exactly" (App B:130) has to be read off by hand. The checker's
  exact integer check confirms it: equality holds at n = 6 only.
  **Fix:** after l.37, add an exact pass, for example `assert all(b < 5/12 for b, n in best if n != 6)` on the inflated
  values, plus a Fraction recomputation of B(6) == Fraction(5, 12), and print "B(n) <= 5/12 for 2<=n<=N, equality only at
  n=6: True". See also F2.5 about l.40.
- **C8.** wt rankin_R.py:31 checks 2.75/x + 134x²e^{−x} < 1 on a 0.1-grid of [11, 411]. A grid proves nothing between its
  points, and App B relies on monotonicity anyway: f′(x) = −2.75/x² + 134x(2−x)e^{−x} < 0 for x > 2, so f(11) < 1 suffices.
  **Fix:** replace l.31 with `good = (arb("2.75")/11 + 134*arb(11)**2*arb(-11).exp()) < 1`, with that comment. In wt
  B-certificates.tex:221–222, replace "the script evaluates it on a grid of step $0.1$" with "so it suffices that it is $<1$
  at $x=11$". Change the output label to "2.75/x + 134 x^2 e^-x < 1 at x = 11 (decreasing for x > 2): OK".
- **C9.** App B does not name bs_cert_arb.py, the module that implements S.
  **Fix:** at B-certificates.tex:28, replace "module \texttt{ivarb.py}" with "the bound $S$ is in \texttt{bs\_cert\_arb.py},
  the interval layer in \texttt{ivarb.py}". At l.71, change "In the code" to "In \texttt{bs\_cert\_arb.py}".
- **C10.** depcheck.py has no edges to RosserSchoenfeld1962, which lem:cm (04a:197), lem:threshold-mass (04e:27) and
  lem:rowweights use (depcheck.py:36, 49, 77), and no edges to the certificates. So "one edge per input"
  (B-certificates.tex:276) is not literally true. This is harmless, because external leaves cannot close cycles.
  **Fix**, either:
  - (a) reword l.276 to "one edge per internal input (external results enter only as leaves, and only some are listed)"; or
  - (b) add `cite:RosserSchoenfeld1962` to those three dep() calls. That gives 80 nodes and 196 edges, and App B:282 and
    01-setup.tex:112 must then be updated.
- **C11.** B-certificates.tex:44 says "(\texttt{pip install python-flint==0.9.0})", but the commands use `python3 -I`, which
  ignores the user site, so a `--user` install is invisible. The bs-cert commands (l.47, 49) and wt l.246 say python3 but need
  flint.
  **Fix:** replace l.44's parenthesis with "(with \texttt{python-flint} 0.9.0 installed for the interpreter used, e.g.\ in a
  virtual environment; \texttt{-I} ignores the user site directory)".

## 7. Run times (wall clock)

Every run of an original certificate is within the time App B states; the individual times are in §2.

The independent re-implementations took:

| Script | Wall time |
|---|---|
| finite_indep | 3.0 s |
| x0band_indep | 19.2 s |
| rankin_indep | 0.5 s |
| aux_indep | 1.6 s |
| z2_indep, q = 1.05, 10 workers | 39 s |
| z2_indep, q = 1.03, 10 workers | 84 s |
| true_sigma / true_sigma2 | 2.3 s / 1.8 s |
| consts_indep, depcheck_indep, sH_indep | under 1 s each |

## 8. Remaining limitations

1. **bs-cert is independent at the level of the bound, not of the reduction.** The independent S was derived from the paper's
   outline, but it rests on the same analytic reduction:
   - the definitions of Σ, E₁–E₃ and T in Steps 2–6;
   - (R1)–(R4) and the T formula of Step 6;
   - a(m,w) ≤ k_uφ(w);
   - the argument for uniformity in τ (κ_min, κ_max, Ū).

   The pieces S relies on were checked: h′ increasing, h′ ≤ 8Λ, the bound on a(m,w), and the maximisation of E_T. Steps 1–6
   of Thm bs, Lemma bs-remainder, region Z1 and the region ℓ ≥ 10¹⁸ were **not** re-verified.
2. **Shared software.** Arb (python-flint 0.9.0) is trusted by both the scripts and the re-implementations, so it is a
   common-mode risk. The x0-band check (exact Python integers) and parts of finite-n (Fractions) avoid it.
3. **No human review.** The re-implementations were written by an AI agent and have not been reviewed by a human.
4. **Cross-checks only partly re-derived.** The capl-cert, lemma-sc and svl-stress outputs were reproduced, but only depcheck
   and s_H were re-derived independently. The precise capl model, lemma-sc and svl-stress were not re-implemented.
5. **rankin_R covers only the constants.** The rest of Lemma rowweights (c),(e), the Rosser–Schoenfeld inputs and the partial
   summation, was checked by hand, not mechanically.
6. **The F2 constants are verified but have no certificate.** The repository has no script for them. The eq:mu1sum
   integrals I₂ and I₃ were checked with float quadrature only.
7. **The numerical Σ is a sanity check, not a proof.** The comparison in true_sigma*.py uses a float discretisation of ρ;
   ρ(3) and ρ(10) agree with tables to about 10⁻⁵ relative.

**Line references.** In F3, E₁ is bs_cert_arb.py l.65, and T is l.76–89 (with tot at l.90). The checker's working files were
in /tmp/rhscratch/cert-repro/, which is temporary.
Copies of the checker's independent scripts are kept in `review/recheck/cert-repro/`.

## 9. Re-check of #54, the fixes of the R8 findings

**Verdict: VERIFIED.**
- All 14 items are resolved: F1, F2 (with F2.5), F3, and C1–C11. Nothing BLOCKING or FIXABLE remains; there is one cosmetic
  residual, R1.
- 21 of 21 commands were run. All 16 verbatim blocks in App B reproduce byte for byte, apart from the exceptions App B
  itself declares (bs-cert omits the run time, the finite-n runtime line varies, and the x0-band `top:` line is abridged).
- The 7 changed certificates were checked for rigour, and no regression was found.

**Set-up.** The checker worked read-only on the live working tree, compared it with `02bbd5c`, and ran everything from a
frozen copy. At the end, all 12 checked files were still byte-identical to the live tree.

### 9.1 Re-runs

- **Results unchanged.**
  - bs-cert: 302,013 cells, 0 failures, minimum ℓS = 2.491e6, from both drivers.
  - The aux margins are 0.189, 1.724 and 0.829, unchanged by C4 (15 → 22) and C5.
  - The cross-checks are byte-identical to their R8 runs.
- **finite-n now needs python-flint.** App B, the finite-n README and the top-level README all say so.
- **The paper copy** compiles with no undefined references, and every new `\ref` resolves.
- **Times (s):** bs patched 6.5, bs arb 6.6, aux 0.9, finite 3.0, x0band 4.8, consts 0.06, rankin 1.9.

### 9.2 Item by item

- **F1.** `finite_checks.py` now uses arb (prec 96) and Fractions, and no float enters any computed quantity.
  - Every comparison is decided on the ball.
  - The line-6 tail is correct: f(t) = log t/(t−1)² decreases for t ≥ 2, so
    Σ_{n>N} ≤ (log N + 1)/(N−1) + 1/(N−1)².
  - The values agree with the checker's own finite_indep.py to every printed digit. The margins are ≥ 1.78e-6, against ball
    radii ≤ 4.9e-8.
- **F2.** Every value printed by `consts.py` agrees with the checker's consts_indep.py to every printed digit.
  - **I₂.** acb.integral is called with the analytic flag forwarded to log, and Re(1+2t) > 3 on the path, so the result is a
    rigorous enclosure.
    - The tail derivation is correct: (log y + c)/y is decreasing, and ∫_T^∞ p e^{−t} = e^{−T}(p + p′ + … + p⁗)(T).
    - An independent closed form via incomplete gamma functions gives 214.771420263705 ± 1.3e-13, which lies in
      main + [0, tail].
  - **I₃.** The closed form (e^{1/2}/2)E₁(log 4 + ½) is correct, and matches an independent acb.integral to 12 digits.
  - **Text.** The App B subsection, the preamble's "Five …" and the 01-setup rewording are correct.
- **F2.5 and C7.**
  - **0.137383.** This is the middle expression of the proof at n = 10⁶, before rounding to 2.152. The value 0.137423 uses
    2.152, and the constants certificate certifies that form. The two are consistent.
  - **The exact pass is sound.** B(6) = 5/12 is recomputed in Fractions, and every other inflated value is < 5/12.
- **F3.** The bound S written out in 04c Step 7(iii) matches `bs_cert_arb.py` term by term: Mm1/tailII, E₁, E₂, E₃, η̄, T
  and tot. Both added facts hold:
  - π(dw) ≤ e^{−r₀(w−u)}dw/u on w ≥ u, by (R3);
  - κ_Φ ≤ κ_max, and (w − m^{1/4})₊ ≤ (w − u₀ + c_u)₊.
- **C1, C2.** 0.69659 and 1.32964 are upper bounds of the true maxima, 0.6965836 and 1.3296349.
- **C4.** 22 is now used, and the margins are identical.
- **C5.** The remaining floats are covered.
  - δ is an exact binary value.
  - fl(1−δ) has relative error ≤ 2⁻⁵³, and the factor 1 + 2⁻⁵⁰ covers it.
  - `_fdn` and `_fup` are safe.
- **C6, C8, C9, C10(a), C11.** Resolved.

### 9.3 Residual

**R1 (COSMETIC).** The places in the paper that use the certified constants did not cite the new certificate. The lead fixed
this by adding references to Appendix~\ref{app:cert-consts} at 04x (A(1.8−3·10⁻⁶) and the ball-arithmetic ζ values), at 04k
(A₀ and A₁) and at 06 (eq:mu1sum).
