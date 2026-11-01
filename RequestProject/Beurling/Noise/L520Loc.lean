module

public import RequestProject.Beurling.Noise.MarginChainLoc
public import RequestProject.Beurling.Noise.TauNearLocNum

/-!
# Lemma 5.20 at a start `y` at the cofactor horizon

`l520At_of_loc` : the conclusions `L520At` of Lemma 5.20 at a start `y`, from the localized
proof `TauNearLoc*`: (HBS) is read only up to `3√(2v)` for the scales `v ≤ y`, i.e. under
`2500 ≤ Z` and `18 y ≤ Z²` (in place of `18 y ≤ Z` of `l520At_of_18`).
-/

@[expose] public section

open Real

namespace KR.Chain

open KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **Lemma 5.20 at a start `y`**, under `2500 ≤ Z`, `18 y ≤ Z²` and the width bound
`H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}`. -/
theorem l520At_of_loc (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 y lam0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hZ0 : 2500 ≤ Z) (h18 : 18 * y ≤ Z ^ 2)
    {N K : ℕ} (hK : √(2 * y) ≤ Pk X0m K) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
    L520At P H tw X0m X0 lam0 y N K := by
  obtain ⟨-, -, -, h4, hX0⟩ := sizes h hX0e hX0m
  have h1 : Sep (dyScales X0 y N) := dyScales_sep hX0
  have h2 : ∀ v ∈ dyScales X0 y N, 1 ≤ v := fun v hv => dyScales_ge h4 hv
  have h3 : ∀ v ∈ dyScales X0 y N, 18 * v ≤ Z ^ 2 := fun v hv => by
    have := dyScales_le hv; linarith
  have h5 : ∀ v ∈ dyScales X0 y N, √(2 * v) ≤ Pk X0m K := fun v hv =>
    sqrt_le_Pk hK (dyScales_le hv)
  refine ⟨fun u hu => by linarith [h2 u hu], (etaBound_energy_loc h h1 h2 hZ0 h3 h5).1, ?_,
    (thetaBlk_sum_loc h h1 h2 hZ0 h3 h5).1⟩
  exact KR.WidthReal.energy_small_loc h hH h1 h2 hZ0 h3 h5 hlam0 hlam
    (CNt_bounds (sizes h hX0e hX0m).2.1).1 (CNt_bounds (sizes h hX0e hX0m).2.1).2

end KR.Chain

end
