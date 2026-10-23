# R12: check of correction #68, the explicit replacements for ≪, o(1) and O(·) in §5

The checker was cond-check, a fresh AI agent. It worked read-only on the live tree, diffed against c067708. It was not allowed
to write files, so the lead saved its message here. A private build gave latexmk exit 0, no warnings and 17 overfull boxes;
depcheck gave 78/196/28, matching App B.

## Verdict on #68: CORRECT WITH FIXES

0 BLOCKING, 1 FIXABLE, 3 COSMETIC. Every load-bearing replacement holds.

The comment scan also found two swallowed-text defects in #69 hunks (§7). They belong to #69, not to #68.

## 1. s₂ for Freedman (05-queue:381–391): correct

- **The window.** |I| ≤ 12L(L₀+1) + 2 ≤ 13L·L₀, since L·L₀ ≥ 12L + 2.
- **log L₀.** log(48/0.15²) = 7.665, so log L₀ = max(5ℓ, log M₁ + 3ℓ + 7.67).
- **M₁.** log M₁ ≤ log c + log 2.
- **log c ≤ 0.38√L.**
  - The standard term, at the smallest L = Λ = 10⁸: 4ℓ² = 1357 ≤ 0.14√L = 1400. This is the tightest step.
  - For s ≥ s_H: γ ≤ 7.5 ≤ 0.38·e^{s_H/2} = 7.536.
  - For s ≤ s_H: numerically, max γ_*/e^{s/2} = 0.0168 over s ∈ [−69, s_H], so γ_* ≤ 0.03e^{s/2}. The intermediate bound
    2.6(A+1)/√Λ_s is at least the exact value 2.6√(A(A+1))/√(Λ_s−A−1) (0.01694 against 0.01681), so the chain is valid.
- **Independent parameter script.** 0.38√L + 0.7 − log M₁ ≥ 2445 for ℓ ∈ [log Λ, 60] at Λ = 10⁸, and more at larger Λ.
- **The exponent.**
  - ½√(L log L) = (√ℓ/2)·√L, with √ℓ/2 = 2.146 ≥ 2.14 at ℓ = 18.42. This step is also tight.
  - log(117L²L₀) ≤ 7ℓ + 13.2 + 0.38√L, where 117 = 9·13 and log 117 = 4.76.
  - Subtracting 2.14√L leaves 7ℓ + 13.2 − 1.76√L ≤ −√L, since 0.76√L = 7600 ≫ 142.
- **The smallest L.** Freedman runs at scales x ≥ X₀, so L ≥ Λ ≥ 10⁸. All three tight steps hold there.

## 2. Line 411: correct

13/(HL⁵) ≤ 2L⁻⁶ holds if and only if H ≥ 6.5L, and H ≥ e^{8ℓ²}. Also δ₁(x/q) = 2L_{x/q}⁻⁶ ≥ 2L⁻⁶.

## 3. The summation (l.524–530): correct

- **The E1 part.** Σ(Λ + m log 2)⁻² ≤ Λ⁻² + 1/(Λ log 2). Since 1.0001/log 2 = 1.44284, adding about 10⁻⁸ still gives ≤ 1.443.
- **The rest, per scale.**
  - E2 ≤ u⁻².
  - E3 + E3′ ≤ 1.2u⁻².
  - E4: 146H(u)u⁻³ ≤ u⁻², since 146H(u) ≤ u.

  That is 3.2u⁻² per scale, and 3.2/(1 − ¼) = 4.267 ≤ 4.3.
- **The total** is ≤ 1.5/Λ.
- **The budget row in 01-setup** is consistent with this.

## 4. Prop ecl (l.559–563): correct

- The new heights lie in (2u/L_{u/2}¹¹, 4u/L_u¹¹]. The endpoint ratio is 2(L_{u/2}/L_u)¹¹ < 2, so the interval holds at most one
  dyadic z.
- log z ≥ L_u − 11 log L_u + log 2.
- For tiny x, (1 − x)⁻² ≤ 1 + 2.0001x, which gives the factor 23. At L = 10⁸, 23 log L/L = 4.2·10⁻⁶.
- The table entry for E1, 1.0001·L_u⁻², matches.

## 5. The other explicit forms: correct, apart from F1 and C1

- **l.50.** r̄₀ ≤ L ≤ e^{−600}·c^{1/2}, since 2ℓ² = 677 ≥ ℓ + 600.7 at ℓ = 18.4.
- **l.216.** 1/κ = X₀^{0.3967}, and H(P)/P ≤ H(X₀)/X₀ ≤ e^{−0.98Λ} for dyadic P ≥ X₀, so 7e^{−0.58Λ} ≤ e^{−0.5Λ}.
- **l.365.** Off the raised range, M₁ ≤ 2c = ½H_std^{1/2}, so B ≤ 34M₁L² ≤ 17L²H_std^{1/2}.
- **l.426.** ¼e^{4ℓ²} ≥ L².
- **l.436.** 0.99L⁵ ≥ 12L + 2.
- **l.514.** H ≥ e^{8ℓ²}.
- **l.1103 (caplw Step 2).** m ≤ L²/(ℓΛ) ≤ Λ³e^{2s} ≤ Λ³e^{14} and D ≤ 2Λe^{6.97}, so e(π+k)/(kX₀⁻) ≤ 1/3.
- **l.1244, and 01-setup (N5).** y(n) ≤ n^{0.01} wherever 𝒜 ≠ ∅.
- **The non-dyadic sentence, "at most 1 + 10⁻⁵".**
  - H across [u, 2u] changes by at most 2^{4·10⁻⁶} = 1 + 2.8·10⁻⁶, by caplw(c).
  - On the ramp, y changes by at most 2^{10⁻⁵}(1 + 2c^{−1/2}) = 1 + 6.9·10⁻⁶. Directly, Δlog c ≈ 10⁻¹⁰ there.
  - M₁: r₀ jumps by at most 1, which changes M₁ by a relative c^{−1/2}. L⁶ changes by a relative 4·10⁻⁸, and C_d likewise.
  - This is consistent with the checker's two-scale computation (ratio 3.60, against Step 5's 3.56).

## 6. The items left descriptive: all five agreed

- **l.7** (B quasi-polylogarithmic, ≤ H^{O(1)}): descriptive. It could also say B ≤ H(x) (C3).
- **l.245** (rem:oldlanding, λ ≲ |J|): an unused form.
- **l.316** (rem:localcount-uses, δx ≫ H): descriptive, but it should be aligned with 01-setup (N4) (C2).
- **l.712** (TCL, O(r) supports): the proof gives ≤ 3r.
- **A-rankfull:470** (rem:widened): an optional route, not used.

## Defects in #68

- **F1 (FIXABLE, minor). Remark caplw-sizes, 05-queue:1225.**
  - "Elsewhere y = H_std·L₀·L⁶ ≤ e^{12.1ℓ²}" is false at low heights off the raised range. There log y = 12ℓ² + 9ℓ + 7, which
    exceeds 12.1ℓ² by up to 170: for ℓ ∈ [18.42, 25.4] at Λ = 10⁸, and for ℓ ∈ [27.6, 31.9] at Λ = 10¹².
  - The bound holds only for ℓ ≥ 91, which covers the standard regime ℓ ≥ ℓ_std. The remark's conclusion is unaffected,
    because it uses the bound only where 𝒜 can be nonempty.
  - **Fix:** replace "elsewhere" with "in the standard regime ℓ ≥ ℓ_std".
- **C1. Lemma raisedy, l.1418.**
  - The text says "B ≤ x^{10⁻⁵} … at these heights, since log x ≥ 393Λ²". On the part of the raised range below s_H, which starts
    at s ≈ −11.4 for Λ = 10⁸, log x is much smaller than 393Λ².
  - The conclusion still holds on the whole raised range: the smallest value of 10⁻⁵·log x − log B is 1.07·10⁶ at Λ = 10⁸,
    using γ_* ≤ 0.03e^{s/2}.
  - **Fix:** restrict the stated reason to s > s_H, or cite γ_*.
- **C2. l.316.** Align "δx ≫ H" with 01-setup's "δx ≥ x^{0.98} > H(x)".
- **C3. l.7.** Optionally, H^{O(1)} could become B ≤ H(x).

## 7. Paperwork

- **Row 68** matches the hunks.
- **The #68 comments.** All five (05-queue:381, 524, 563, 1228, 1414) are whole-line, and the text before and after each is
  intact.
- **Swallowed text in #69 hunks (FIXABLE, belongs to #69).** The checker scanned every logged comment numbered 6x or 7x, and
  every comment line containing $…$. Two #69 comments swallow live text, and the PDF confirms both:
  - **04a-setup.tex:152.** The comment ends "… made explicit. in the rigid part the term $(\kappa X_0+1)/u$ contributes", so the
    PDF reads "Indeed, ≤ 4.01κ to η₁ …".
  - **04e-lp.tex:209.** The comment ends "… (was "<< kappa"). The same computation against $u^{-\sigma}\log u$ (decreasing for
    $u\ge e$), whose main", so the PDF reads "(κ = X₀^{−0.3967}). term is ∫_y^∞ u^{−σ} log u du = … gives".
  - **Fix:** end each comment at its own text, and put the swallowed clause back on a line of its own.

## Confidence

High. Every constant was recomputed, and the tight steps were checked at the smallest admissible L. The checker's independent
parameter script backs the claims about γ, M₁, y and B.

## Addendum: confirmation of the R12 fixes

**Verdict: all CONFIRMED.** 0 BLOCKING, 0 FIXABLE, 0 COSMETIC.

- **F1, Remark caplw-sizes.** The bound is now claimed only for the standard regime, where log y ≤ 12ℓ² + 9ℓ + 7 ≤ 12.1ℓ²
  once ℓ ≥ 91, and that regime starts at ℓ_std ≥ 1.37·10⁴. The 01-setup line "y ≤ X₀^{22.6}L⁹ for ℓ ≤ ℓ_std" is also true there.
- **C1, Lemma raisedy.** log B ≤ log c + 2ℓ + 4.21 ≤ log c + 2ℓ + 4.3.
  - For s > s_H, 7.5Λ + 2ℓ + 4.3 ≤ 10⁻⁵·393Λ².
  - For s ≤ s_H, γ_*Λ ≤ 0.03√L (the actual maximum ratio is 0.0168), and 10⁻⁵L ≥ 0.1√L because L ≥ 10⁸.
  - This agrees with the earlier independent margin of at least 1.07·10⁶.
- **C2.** "δx ≥ x^{0.98} > H(x)" now matches 01-setup (N4) and Prop g1.
- **C3.** Theorem queue does prove B ≤ H at every scale, the raised range included. The chain is
  B ≤ 34M₁L² ≤ M₁·H_std^{1/2} ≤ H, using M₁² ≤ M̄₁² ≤ H and H_std ≤ H.
- **The comments** are all whole-line, and no comment line in paper/sections now contains $…$.
- **The two passages lost behind #69 comments** are restored, and render in full in the PDF.
- **Row 68** is consistent with the text. A private build exits 0 with no warnings.
