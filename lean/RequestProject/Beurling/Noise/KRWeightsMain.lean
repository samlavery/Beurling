module

public import RequestProject.Beurling.Noise.KRWeights
public import RequestProject.Beurling.Noise.Lemma53Main

/-!
# Corollary 5.17(b) with Corollary 5.9 discharged

`cor_5_17_b_hbs` : for a Beurling system satisfying (HBS) on `[1, Z]`, with Theorem 5.6 on
`[1, Z]` (`P.Thm56 Z`, proved in `BSAssembly.lean` from (HBS) and the Lemma 5.7 residual), the
paper's hypotheses on `H`, and the ordered-factorisation sums `HordSums P ε A₀ A₁`: for every
start `y ∈ [X₀⁻, x]` (correction #90) and `X₀⁻/2 ≤ u ≤ y` with `2y/X₀⁻ ≤ Z`,

  `W^nom_y(u) ≤ C_S [(1 + ½λ₀A₀) log(2u) + ½λ₀A₁]/log y`,  `C_S = max(2.01 C_BS, 1.4)`,

and `≤ C_N log(2u)/log y`, `C_N = C_S(2.04 + 4.71/log X₀)`, under the numerical conditions of
`cor_5_17_b_CN`.
-/

@[expose] public section

open BeurlingSystem

namespace KR

variable (P : BeurlingSystem)

/-- Corollary 5.9 gives `SaiasAt` at every start `y ≥ X₀⁻`. -/
theorem saiasAt_of_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (h56 : P.Thm56 Z) {tw : ℕ → ℝ}
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y : ℝ} (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    SaiasAt P tw X0m y (max (2.01 * BSaias.PhiInf 100000000) 1.4) :=
  fun _ hv1 hv2 => P.cor_5_9 h hXm h56 h.smallHeights ht htv hy hv1 hv2 hZ

/-- **Corollary 5.17(b)** under (HBS) and Theorem 5.6. -/
theorem cor_5_17_b_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (h56 : P.Thm56 Z) {H : ℝ → ℝ} {ε θ lam0 A0 A1 : ℝ}
    {tw : ℕ → ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hA : HordSums P ε A0 A1) {y u : ℝ} (hy : X0m ≤ y)
    (hu : X0m / 2 ≤ u) (huy : u ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    Wnom P H tw X0m y u ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 *
      ((1 + 1 / 2 * lam0 * A0) * Real.log (2 * u) + 1 / 2 * lam0 * A1) / Real.log y := by
  have hX := h.X0m_ge
  have hy1 : 1 < y := by norm_num at hX; linarith
  exact cor_5_17_b (P := P) hP hp2 ht hlam hy hy1 hu huy
    (le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1.4))
    (saiasAt_of_hbs P h hXm h56 ht htv hy hZ) hA (by norm_num at hX; linarith)

end KR

end
