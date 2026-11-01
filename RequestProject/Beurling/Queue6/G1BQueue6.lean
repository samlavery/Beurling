module

public import RequestProject.Beurling.Queue6.HCount
public import RequestProject.Beurling.Model.G1BWire

/-!
# The Queue6 part of `KR.RML6.G1BRest`: Step 1's count at `δ = deltaB` (Proposition 5.35(B))

* `g1B_hcount_R` : the fields `Eloc`, `hE0`, `hE`, `hcount` of `G1BRest` for `P(ω)`,
  `δ = deltaB θ X₀ ω y`, `ρ̃ = rhoT`, at every range-(B) start `y` (`log y > X₀^{1/100}`), on
  `NiceEv` (`hcount_field`, with `E_loc = Eloc X₀ (y(1-δ))`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1600000 in
/-- **Step 1, first bullet, at `δ = deltaB`** (the Queue6 fields `Eloc`, `hE0`, `hE`, `hcount` of
`KR.RML6.G1BRest`). -/
theorem g1B_hcount_R {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    0 ≤ Eloc X₀ (y * (1 - deltaB θ X₀ ω y)) ∧
      Eloc X₀ (y * (1 - deltaB θ X₀ ω y)) ≤ 40 * √y ∧
      LocalPNT.piCount (PR θ X₀ ω) (y * (1 - deltaB θ X₀ ω y)) -
          LocalPNT.piCount (PR θ X₀ ω) (y * (1 - 2 * deltaB θ X₀ ω y)) -
          Eloc X₀ (y * (1 - deltaB θ X₀ ω y)) ≤
        ∫ z in (y * (1 - 2 * deltaB θ X₀ ω y))..(y * (1 - deltaB θ X₀ ω y)), rhoT θ X₀ ω z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set Λ := Real.log X₀ with hΛe
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  set δ := deltaB θ X₀ ω y
  have hδ0 : 0 < δ := deltaB_pos hc ω hy
  -- `δ ≤ X₀^{-1/2} ≤ 1/4`
  have hδ : δ ≤ 1 / 4 := by
    refine (deltaB_le (θ := θ) ω y).trans ?_
    rw [Real.rpow_neg hX0, ← one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (4 : ℝ) ^ 2 ≤ X₀ := by linarith [X₀_ge_two_pow hc.hX]
    calc (4 : ℝ) = ((4 : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) this (by norm_num)
  -- `log y > X₀^{1/100} ≥ 4Λ + 10`, so `y ≥ e^{10} X₀⁴`
  have hpow : 4 * Λ + 10 ≤ (X₀ : ℝ) ^ (1 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos hX0p]
    have h1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ Λ * (1 / 100) by positivity)
    nlinarith
  have hly : 4 * Λ + 10 < Real.log y := lt_of_le_of_lt hpow hyB
  have hy0 : 0 < y := by linarith
  have hy4 : 16 * (X₀ : ℝ) ^ 4 ≤ y := by
    have e : Real.log (16 * (X₀ : ℝ) ^ 4) = Real.log 16 + 4 * Λ := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h16 : Real.log 16 ≤ 10 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (10 : ℝ)
      nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 10 by norm_num)]
    have : Real.log (16 * (X₀ : ℝ) ^ 4) ≤ Real.log y := by rw [e]; linarith
    exact (Real.log_le_log_iff (by positivity) hy0).mp this
  have hX4 : (X₀ : ℝ) ^ 3 ≤ (X₀ : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hX3 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have ha : (X₀ : ℝ) ≤ y * (1 - 2 * δ) := by nlinarith
  have hb3 : (X₀ : ℝ) ^ 3 ≤ y * (1 - δ) := by nlinarith
  have hlb : 10 ^ 4 ≤ Real.log (y * (1 - δ)) := by
    rw [Real.log_mul hy0.ne' (by linarith)]
    have : Real.log (3 / 4) ≤ Real.log (1 - δ) := Real.log_le_log (by norm_num) (by linarith)
    have h34 : -1 ≤ Real.log (3 / 4) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_gt_d9
      have h := Real.exp_neg_one_lt_d9
      linarith
    linarith
  exact hcount_field hc hev hN hδ0 hδ ha hb3 hlb

end Queue6

end
