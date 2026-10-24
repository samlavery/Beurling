# R30: independent audit of the bs-cert code (Theorem bs, Step 7(iii), region Z2)

**What was audited.** A fresh agent audited the certificate's code itself; the earlier check R8 only re-ran it. It worked on
a copy of the certificate at 1457ebb, using python-flint 0.9.0 with arb at precision 53. Its scripts are in
`review/recheck/r30/`. The two large intermediate files are not included; `build_big.py` and `dump_run.py` regenerate them.

**Verdict: bs-cert is SOUND WITH FIXES.** The certificate proves what Theorem bs needs on Z2, namely Σ(ℓ, u) ≥ 0. There
were no BLOCKING findings, one FIXABLE finding in the paper text (F1), and seven COSMETIC findings. All have been applied,
and the certificates were re-run after the code changes with unchanged results.

## Findings
- **F1 (FIXABLE, text).** The printed β_a (04c) had no condition on its shift term c_u(2v₊ + c_u)/(2√ℓ). The code,
  correctly, sets that term to 0 when v + c_u ≤ 0, because there k_uφ(u) − a(ℓ, u) = 0. The printed version is valid but
  too weak:
  - on every u-cell v + c_u ≤ 0, and the extra term there is 1/(18u²);
  - at ℓ = 10¹², u = 2, the printed formula gives ℓS = −1.4·10¹⁰, against +1.4·10⁸ from the code;
  - coded literally, it fails 44,861 of the 59,997 u-cells (388 of 403 bands, from ℓ ≈ 6.2·10⁹ on), and bisection cannot
    rescue them.

  This is now correction #101.
- **F2.** The text said "including adaptive bisections", but no cell was bisected: every one of the 302,013 cells passed
  at its first evaluation.
- **F3.** `cert_run_arb_patched.py` is not an independent driver: it imports `cert_run_arb`'s cell code and copies its
  band layout.
- **F4.** `r_up` applied `_fup` to the midpoint of a ball rather than to its upper end. The 1 + 2⁻⁵⁰ factor covered this,
  but Appendix B credited that factor to something else. `r_up` now takes the upper end of the ball, and the factor is
  dropped.
- **F5.** `aux_cert_arb.py` formed one product in floating point (effect about 10⁻¹⁵ against a margin of 0.189). It now
  squares in arb.
- **F6.** The float twin `aux_cert.py` still used the superseded constant 15 instead of 22.
- **F7.** γ₁ and γ_max are now displayed.
- **F8.** The run time is about 10 s, not about 20 s.

## Correspondence (Q1)
Every summand and constant in `bs_cert_arb.py` matches 04c, except β_a (F1). Each majorant was re-derived from the Step 5
and Step 6 definitions. The following analytic facts were checked in ball arithmetic:
- h″ > 0;
- h′ ≤ 8Λ (in fact ≤ 4.56Λ);
- the bound on h′(u−1);
- (u/(u−1))^{3/2} ≤ 2k_u.

Two elementary inequalities were proved by hand.

## Coverage (Q2)
Checked from a dump of every leaf cell:
- 403 bands, from exactly 3·10⁹ to 10¹⁸, with matching seams.
- In every band the u-cells cover [2, split] with no gaps, and the u/v seam and the top edge were checked rigorously at
  200 bits.
- 200,000 random points: 0 uncovered.
- The region ℓ ≥ 10¹⁸ is covered analytically by Step 7(ii).
- Extra cross-check: [10¹⁸, 10²⁴] gives 313,965 cells and 0 failures.

## Enclosures (Q3)
- Every quantity is evaluated as a ball over the whole cell.
- Every endpoint shortcut is justified by a monotonicity: r increases (R2), Ū increases, a_V decreases.
- The float operations are all exact or outward-rounded.
- No comparison is made on a midpoint.
- ρ is never evaluated directly. It enters only through the enclosures r_low and r_up, which were validated against an
  independent Dickman table at every integer from 2 to 269,998 and at 200,000 random reals: 0 violations.
- Γ and Ein do not occur in this certificate.
- `exp` is evaluated rigorously, with a guard.

## Constants (Q4)
Each constant is the proven one and is used in the safe direction:
- K′ = 2.20;
- B = 11;
- κ_min = 4·10⁸ and κ_max;
- Ū;
- 12.8 = 4·3.2;
- C₀ = 0.70.

## aux_cert_arb.py (Q5)
All three checks are sound:
- c₀ ≥ K′u² log(1+u) on [27, 4·10⁵];
- Lemma V one-step on [1, 10⁶];
- the same on [1, 2] with both extra terms.

## Runs (Q6)
- `cert_run_arb_patched.py` and `cert_run_arb.py`: 302,013 cells, 0 failed, minimum ℓS = 2.491·10⁶, about 6–11 s.
- `aux_cert_arb.py`: 9,609, 13,823 and 1,387 cells, 0 failed, margins 0.189, 1.724 and 0.829.
- The lead re-ran all three after the F4 and F5 code changes and got the same results.

## Independent high-precision check
The checker computed its own S from the LaTeX in 200-bit arb, using the true r(u), and compared it with Σ_true from exact
ρ by quadrature, at τ ∈ {10⁸, random, ℓ/30}.
- About 925 cells, 3,700 points and 9,608 evaluations: 0 violations. S_point ≥ s_cell, S_point ≤ Σ_true, and Σ_true > 0
  (minimum ℓS_point = 3.9·10⁶).
- 1,723 targeted points at the seams, edges and extremes: 0 violations.
- Caveat: Σ_true uses binary64 quadrature and a validated, but non-rigorous, table of ρ. It is a strong numerical check,
  not a second proof.
