# R25: independent check of correction #91 (ramp truncation at X₀)

The checker was a fresh agent that had not written the repair. It worked on a snapshot of the working tree with the #91
repair applied (base a4441b2). Its scripts are in `review/recheck/r25/` and use arb at 200 bits.

**Verdict: #91 CONFIRMED.** There are no BLOCKING or FIXABLE findings. There are three COSMETIC findings, all now applied.

## 1. Sign and form of the correction
- **Direct integration.** The full ramp transforms to W(s)n^{−s}, and the part kept above X₀ transforms to
  (X₀^{−s} − n^{−s})/(sκ). Z_B − eq. (14) is the full ramp minus the kept part,
  ((n/(1+κ))^{−s} − X₀^{−s})/(sκ). That is the repair's expression, with the repair's sign. The v3 expression is the
  transform of the kept part, which is the correct quantity in Lemma goodheights.
- **Per-n check in arb.** κ = 1/10, X₀ = 100, n ∈ {100, 105}, 9 values of s. All four identities hold to ≤ 1.6·10⁻⁵⁸.
  At n = X₀ the v3 expression is 0, but the true change is not (0.0940 at s = ½+10i).
- **Whole-set check in arb.** The 49 integers in [100, 160] whose prime factors are all < 100, X₀ itself included:

  | boundary terms used | residual of Z_B − ((14) + boundary terms) |
  |---|---|
  | corrected | ≤ 3·10⁻⁵⁷ |
  | v3 | 1.3·10⁻⁴ to 0.19 |
  | corrected, sign flipped | 7·10⁻⁴ to 0.65 |

- **The factor 2.** It covers both terms of the correction, and it is needed: the supremum ratio is 1.909 at κ = 0.1 and
  tends to 2 as κ → 0.

## 2. Bounds
- **ZB chain.** It needs 2(1+κ)² ≤ 2.01, X₀ + 1/κ ≤ 1.0001X₀ (1/(κX₀) = X₀^{−0.6033}), and |s| ≥ |t|. All hold.
- **ZBlow chain.** All steps hold: log(1+κ) ≤ κ, (1+κ)^{1−a/Λ} ≤ 1.01, X₀^{a/Λ} = e^a, and
  1.01(κX₀+1)/X₀ ≤ 3κ.
- **The old ZBlow bound fails.** At n = X₀, σ = 10/κ, the ratio is 1378 at κ = 0.1, 2191.6 at κ = 10⁻³, and 2202.54 at
  κ = 10⁻⁶; the limit is (e¹⁰−1)/10 = 2202.55. The new bound holds at σ = 100.

## 3. Downstream
These are unchanged: the "≤ 4X₀^{1/2}/|t|" step in ZB, the "+3κe^a" term in ZBlow, and Step 6 of Thm lp
(3κe⁸ is absorbed there).

## 4. Sweep (no error of the same kind found)
- **Lemma goodheights (ii).** It bounds the part kept above X₀, so the v3 form is right there. The edge terms are
  ≤ 3X₀^{1/4}/|t| and ≤ 3a_k^{1/4}/|t|.
- **The absorbed part.** The closed form of w_a checks. 𝒜 is empty near X₀, so no absorbed window is cut off.
- **Other sites.** Lemma ZA has no truncation. \hat T₀ goes through ZBlow. E_rig, blin(4) and Step 3 of Thm lp are mass
  statements, not transforms. §6, 04f, 04g and 04x use ρ_det only as a density.

## Findings (applied)
- **F1.** Interval endpoint made consistent: [n/(1+κ), X₀).
- **F2.** "changes the transform by" → "adds … to Z_B compared with eq:ZBformula".
- **F3 (from v3).** |Z_B| ≤ 2 log X₀ is now stated for σ ≤ 2, the range the proof covers. Every use is at σ ≤ 1.01.

## Build
142 pages, 15 overfull boxes (none in 03-zeros), 0 undefined references. Both passages were checked as rendered PNGs.
