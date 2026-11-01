module

public import RequestProject.Beurling.Queue6.ThreshFields

/-!
# The field `localCount` of `ThreshHyp` with `K_loc = 0`

`localCount_R0` : for `x ≥ 16`, `X₀ ≤ a_*` and `6H(x)x^{-1/3} ≤ δ ≤ 1/4`, on `NiceEv`,
`#{p_j ≤ x : a_* ≤ p_j < b_*} ≤ 13.5 (b_* - a_*) + 0 + 2`: the `p`-interval has length
`ℓ ≥ δ√x/2 ≥ 3 H(x)`, so the slot count `1.0001 (ℓ + H(2b_*) + 1) + 1` (`localCount_R`) is
`≤ 13.5 ℓ + 2`. Hence `K_loc = 0` and the fields `hK0`, `hK` (`K_loc ≤ H_y`) of `G1BRest` hold.
-/

@[expose] public section

open Set Real Construction CaplLink QueueMono

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

open Classical in
set_option maxHeartbeats 1600000 in
/-- **`localCount` with `K_loc = 0`**. -/
theorem localCount_R0 {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {x δ : ℝ} (hx : 16 ≤ x)
    (hδge : 6 * Hc X₀ x / x ^ (1 / 3 : ℝ) ≤ δ) (hδ : δ ≤ 1 / 4)
    (ha : (X₀ : ℝ) ≤ BeurlingSystem.aStar x δ) :
    ((((PR θ X₀ ω).primesLe x).filter (fun j => BeurlingSystem.aStar x δ ≤ (PR θ X₀ ω).p j ∧
        (PR θ X₀ ω).p j < BeurlingSystem.bStar x δ)).card : ℝ) ≤
      13.5 * (BeurlingSystem.bStar x δ - BeurlingSystem.aStar x δ) + 0 + 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hx0 : 0 < x := by linarith
  set a := BeurlingSystem.aStar x δ with hae
  set b := BeurlingSystem.bStar x δ with hbe
  have hH1 : 1 ≤ Hc X₀ x := Hx_ge_R hc x
  have hc3 : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hδ0 : 0 < δ := lt_of_lt_of_le (div_pos (by linarith) hc3) hδge
  set r := √x with hre
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx0
  have hrr : r * r = x := Real.mul_self_sqrt hx0.le
  -- `b ≥ √x`, `a ≤ √x (1 - δ/2)`
  have hb1 : r ≤ b := by
    rw [hbe]; unfold BeurlingSystem.bStar
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have ha1 : a ≤ r * (1 - δ / 2) := by
    rw [hae]; unfold BeurlingSystem.aStar
    rw [Real.sqrt_le_left (by nlinarith)]
    rw [div_le_iff₀ (by linarith)]
    have : x * (1 - δ) ≤ (r * (1 - δ / 2)) ^ 2 := by
      have e : (r * (1 - δ / 2)) ^ 2 = x * (1 - δ / 2) ^ 2 := by rw [mul_pow, sq r, hrr]
      rw [e]; nlinarith [mul_nonneg hx0.le (sq_nonneg δ)]
    nlinarith
  have hℓ : δ * r / 2 ≤ b - a := by nlinarith
  -- `δ r ≥ 6 H(x)`: `r ≥ x^{1/3}`
  have hr3 : x ^ (1 / 3 : ℝ) ≤ r := by
    rw [hre, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδr : 6 * Hc X₀ x ≤ δ * r := by
    have := (div_le_iff₀ hc3).mp hδge
    nlinarith
  -- `H(2b) ≤ H(x)`
  have hb2 : 2 * b ≤ x := by
    rw [hbe]; unfold BeurlingSystem.bStar
    have h1 : √(x / (1 - δ / 20)) ≤ 1.01 * r := by
      rw [Real.sqrt_le_left (by nlinarith), div_le_iff₀ (by linarith)]
      nlinarith
    have : 4 ≤ r := by
      rw [hre, show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq]
        <;> norm_num]
      exact Real.sqrt_le_sqrt hx
    nlinarith
  have hbX : (X₀ : ℝ) ≤ b := ha.trans (by nlinarith)
  have hHb : capH X₀ (2 * b) ≤ Hc X₀ x := by
    rw [Hc_eq (by linarith : (X₀ : ℝ) ≤ x)]
    exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) hb2
  have hcnt := primeCount_le hc hev hN (S := Ico a b) ha (by linarith) Ico_subset_Icc_self
  have hsub : ((((PR θ X₀ ω).primesLe x).filter (fun j => a ≤ (PR θ X₀ ω).p j ∧
      (PR θ X₀ ω).p j < b)) : Set ℕ) ⊆ {j | (PR θ X₀ ω).p j ∈ Ico a b} := by
    intro j hj
    simp only [Finset.coe_filter, mem_setOf_eq] at hj
    exact hj.2
  have hfin : {j | (PR θ X₀ ω).p j ∈ Ico a b}.Finite :=
    ((PR θ X₀ ω).finite_p_le b).subset fun j hj => hj.2.le
  have h2 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at h2
  have h3 : ((((PR θ X₀ ω).primesLe x).filter (fun j => a ≤ (PR θ X₀ ω).p j ∧
      (PR θ X₀ ω).p j < b)).card : ℝ) ≤ ({j | (PR θ X₀ ω).p j ∈ Ico a b}.ncard : ℝ) := by
    exact_mod_cast h2
  have hHb0 := capH_nonneg (X₀ : ℝ) (2 * b)
  linarith

end Queue6

end
