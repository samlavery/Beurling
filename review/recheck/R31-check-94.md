# R31: independent check of correction #94 (the cutoff φ)

A fresh agent did this check; it did not write the repair. It worked on a snapshot of the working tree after the #94
repair; the snapshot's paper/ and certificates/ are byte-identical to the live tree. Its scripts are in `review/recheck/r31/`.

**Verdict: #94 CONFIRMED WITH FIXES.** Nothing was BLOCKING. There were 2 FIXABLE items (wording and bookkeeping) and 4
COSMETIC items. All are applied.

## Verified
1. **φ.** It is C^∞, and φ(1−t) = 1 − φ(t). The formula for φ′ is correct. Each step of the proof that φ′ ≤ 2 holds:
   - r = g/2;
   - φ(1−φ) = 1/(4cosh²r);
   - q = (1−2s)/s²;
   - cosh²r ≥ 1 + r² = (1−2s)²/(4s²).

   Equality is reached at t = ½. All four identities were also checked in arb.
2. **phi_bounds.py is rigorous.**
   - Each cell's ball contains the whole cell, bisection keeps the endpoints inside, and the fail-safe guard cannot produce
     a false pass.
   - The bounds on (0, 0.02] are right. φ″ = φ(1−φ)((1−2φ)q² + q′) was re-derived.
   - The symmetry step is right.
   - The output matches Appendix B.

   The checker also located the maximum independently. With closed-form φ‴ and bisection at 200 bits,
   sup|φ″| = 9.84104230183 at t = 0.21826 and 0.78174. A separate rigorous cover (midpoint value plus half-width times
   |φ‴|) gives sup ≤ 9.841055.
3. **G1.** Γ_k ≥ X₀⁻¹x_k^{1/2}/(2log³x_k), which is far above θ + 2, whether Γ_k is computed from x_k or from x_k⁺.
4. **Prop g1(B) Step 3.** R″ was derived by hand, and it matches an arb series to 10⁻³⁵. The coefficient bound is right:
   1 + 6/γ needs γ ≥ 12.25. Also w ≥ (1−2δ)v, and 2α_jγ_jx_j^{θ−1} = κ_j·f with f ∈ [1, 1+ε_j].
5. **Step 4.** |R_k(v)| ≤ α_kv^θ ≤ 3α_kv^θ/(1−θ) ≤ the right side. The v3 bound was weaker than this trivial one.
6. **Sweep.**
   - The Φ(w) bounds (|Φ| ≤ 1, |Φ′| ≤ 1, Re Φ ≥ e⁻¹cos 1, and |Φ| ≥ e⁻¹ on the designed-zero disc) use only φ′ ≥ 0,
     ∫φ′ = 1 and supp φ′ ⊂ [0, 1].
   - eq:Rhat uses only φ(0) = 0 and φ = 1 on [1, ∞). eq:Rhatbound uses only |Φ| ≤ 1.
   - Every consumer of κ₊ depends on ‖φ′‖ only through G1.
   - Nothing else uses ‖φ′‖ or ‖φ″‖.
7. **Rendering.**
   - 145 pages, 14 overfull boxes (the same list as HEAD), 0 undefined references, no stray `%`.
   - Equation numbers shift by one after eq:phibounds = (2). No text hard-codes an equation number.

## Findings (applied)
- **F1 (FIXABLE).** In Step 3, the factor 1.01 was justified only by δ ≤ X₀^{−1/2}, while the only stated bound
  γ_j ≥ 13 allows 1 + 6/γ_j = 1.46. The text now states Γ₁ ≥ e^{X₀²/3}, ε_j ≤ 2x_j^{−0.99} and 6/γ_j ≤ 6e^{−X₀²/3}, so
  the factors multiply to at most 1 + 10⁻⁶.
- **F2 (FIXABLE).** The AI statement and the README still called #94 unused. The counts are now 101 corrections, with
  fifty of #31–#101 reported by the reader.
- **C1.** "As φ = 0 on (−∞, 0], R_k ≡ 0 on …".
- **C2.** Appendix B's list of sections for the constants certificate now includes §construction.
- **C3.** Appendix B now states the small-t step of phi_bounds explicitly.
- **C4.** Section numbers in log rows #77, #94 and #96 are fixed: 02-construction renders as §3, and the zeros section as §4.
