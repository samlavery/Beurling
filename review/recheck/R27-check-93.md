# R27: independent check of correction #93 (Prop g1(B), Step 3 at displacement 2δ)

**Who checked, and on what.** A fresh agent that had not written the repair. It worked on a snapshot of the working tree
after the #93 repair. Its scripts are in `review/recheck/r27/`; the toy test is `toy_rhodet.py`.

**Verdict.** #93 is CONFIRMED WITH FIXES. Nothing is BLOCKING. There is one FIXABLE item, which changes wording only, and
there are three COSMETIC items. All four are applied.

## Verified
1. **The ρ_det bound at displacement 2δ.**
   - The two windows overlap, because 2δ ≤ 2X₀^{−1/2} < κ.
   - They differ by two pieces, each of length ≤ 2δ(1+κ)v. The pieces enter with opposite signs, so the counts differ by
     at most 2δ(1+κ)v + 1.
   - The normalisation term is ≤ 2.01δ(1 + 1/(κv)), which the factor 2 absorbs.
   - The second form holds with the factor 2.0001 ≤ 3.
   - Toy test (X₀ = 100, κ = 0.15, 100-smooth integers up to 2·10⁶, δ from 10⁻⁴ to 0.2): the largest ratio to the bound
     was 0.49.
2. **The weighted sum.**
   - Σ log(2v) = 0.7213Λ⁴. The first part is ≤ 7Λ⁴X₀^{−1/12}.
   - ζ_{X₀}(1 − 1/(2Λ)) ≈ 3.1Λ. The Rankin tail is 86.56Λ^{4.65}e^{−Λ/12} ≤ 90Λ^{4.7}e^{−Λ/12}.
   - At Λ = 10⁸ with C_S = 77, the logarithm of the bound is −8,333,237.9. The bound is ≤ X₀^{−0.08} for every Λ ≥ 10⁸.
3. **R′_j.** |ΔR′_j| ≤ 1.01δγ_jκ_j(v/x_j)^{θ−1} per level; numerically the ratio is 0.999. Summed, the bound is
   ≤ 1.35δγ_jκ_j, which is below the stated bound by about a factor of 2. In Step 5 it contributes
   ≤ 4Σκ_j log⁻³x ≪ log⁻²x.
4. **Step 5.**
   - Every item except σ_𝒜 is ≤ 200e^{−0.015Λ}.
   - The σ_𝒜 item is 1.453·10⁻³Λ⁻⁴.
   - So o(1) ≤ 1.6·10⁻³Λ⁻⁴, and the 0.97 margin holds.
5. **Sweep.** Each width is applied where it is stated:
   - the jump bullet (width 2δN_*);
   - threshold-mass at 2δ;
   - Step 4 (R(2δ), |J| = δx);
   - the π₀ variation (≤ 2.0001δ/log x, in the favourable direction);
   - Prop br, Lemma predictable, Thm g2, Prop pointwise.
6. **Build.** 142 pages, 15 overfull boxes (none in the edited lines), 0 undefined references. The new multline renders on
   two lines.

## Findings (applied)
- **F1 (FIXABLE).** The definition v′ := y/n left the levels with y/n < X₀ ≤ x/n unassigned. Now v′ := max(y/n, X₀), and in
  that case T′(x/n) − T′(y/n) = j_{X₀} + ρ_det(X₀) − ρ_det(x/n).
- **C1.** The window comparison now says the windows "overlap (as 2δ < κ)" and that the pieces "enter with opposite signs".
- **C2.** The R″_j derivation is written out (F_θ ≤ 1.33), replacing "the bound is linear in the displacement".
- **C3.**
  - The ρ_det bullet now says "log x times this part", where it said "weighted sum".
  - Step 1's (1 + O(δ)) is replaced by (1 + ε_J) with 0 ≤ ε_J ≤ 2.01δ/log x, matching Step 5's 3δ/log x.
