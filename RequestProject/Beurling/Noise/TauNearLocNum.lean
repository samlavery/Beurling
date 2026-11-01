module

public import RequestProject.Beurling.Noise.TauNearLocMain
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# Lemma 5.20 at the cofactor horizon: the numerical consequences

`energy_small_loc`, `etaBlk_small_loc`, `thetaE_small_loc` : the smallness facts of
`KRWidthReal.lean` (`energy_small_r`, …) from the cofactor-horizon theorems of
`TauNearLocMain.lean`, i.e. with `18 v ≤ Z²` and `2500 ≤ Z` in place of `18 v ≤ Z`, and the width
input `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}` (`KR.WidthReal.Hc_Xm_half_le` for the realised width). The
bound `2.04 λ₀ θ_* ≤ 0.02` needs no horizon (`KR.WidthReal.thetaStar_small_r`); `θ(y) ≤ θ_*` at
the horizon `9y ≤ Z²` is `KR.TNP.thetaStar_on_loc`.
-/

@[expose] public section

open BeurlingSystem Finset

namespace KR.WidthReal

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `λ₀ C_N E_η ≤ ½` at the cofactor horizon, under
`H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`. -/
theorem energy_small_loc (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ0 : 2500 ≤ Z)
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) {lam0 CN : ℝ} (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hCN0 : 0 ≤ CN) (hCN : CN ≤ 158) :
    lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) *
        TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v ≤ 1 / 2 := by
  have h1 := (TNP.etaBound_energy_loc h hS hSc hZ0 hZ hK).2.1
  have h2 := Phi_small_r h hH (a := 1) (by norm_num)
  have hlc : lam0 * CN ≤ 316 := by nlinarith
  have hE : ∑ v ∈ Sc, Real.log (2 * v) *
      TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v ≤ 1 / 1000000 := by
    linarith
  rcases le_or_gt 0 (∑ v ∈ Sc, Real.log (2 * v) *
      TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v) with h0 | h0
  · nlinarith [mul_nonneg hlam0 hCN0]
  · nlinarith [mul_nonneg hlam0 hCN0]

/-- `2.04 ∑_v s_v ≤ 0.02` at the cofactor horizon, under
`H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`. -/
theorem etaBlk_small_loc (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 0 < v) (hZ0 : 2500 ≤ Z)
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) :
    2.04 * ∑ v ∈ Sc, TNP.blk P H X0m K (fun _ => 1) v ≤ 0.02 := by
  have h1 := (TNP.etaBlk_sum_loc h hS hSc hZ0 hZ hK).2
  have h2 := Phi_small_r h hH (a := 1) (by norm_num)
  nlinarith

/-- `E_θ ≤ 10⁻⁷` at the cofactor horizon, under
`H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`. -/
theorem thetaE_small_loc (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ0 : 2500 ≤ Z)
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) :
    ∑ v ∈ Sc, Real.log (2 * v) * TNP.blk P H X0m K (fun k => Real.log (TNP.Pk X0m k) + 2) v ≤
      1 / 10000000 := by
  have h1 := (TNP.thetaBlk_sum_loc h hS hSc hZ0 hZ hK).2
  have h2 := Phi_small_r h hH (a := 3) (by norm_num)
  nlinarith

/-- The cofactor horizon for a scale family below `x`: `18 x ≤ Z²` gives `18 v ≤ Z²` on `Sc`. -/
lemma horizon_loc_of_le {Sc : Finset ℝ} {x : ℝ} (hv : ∀ v ∈ Sc, v ≤ x) (hx : 18 * x ≤ Z ^ 2) :
    ∀ v ∈ Sc, 18 * v ≤ Z ^ 2 := fun v h => by linarith [hv v h]

end KR.WidthReal

end
