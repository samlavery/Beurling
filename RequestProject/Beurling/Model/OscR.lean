module

public import RequestProject.Beurling.Model.OscD2
public import RequestProject.Beurling.Queue6.TNPHyp

/-!
# The `R`-part of the oscillation `o_u` for every `θ > 0` (04f, the `o_R` bullet)

For small `θ` the modulus of `R'` has no θ-free power decay. As in the paper, `o_R = 0` below the
switch-on and `o_R ≤ H(u) u^{-θ}` beyond it, and the switch-on condition makes the dyadic sums tiny:

* `oscModU θ X₀ u`: the modulus of `R'` on windows inside `[u/2, 4u]`: `0` if `4u ≤ x⁺_0`, else
  `(u/2)^{-θ}/10¹³` (`oscMod_le_U`);
* `oscModU_term_le`: `(log 4u)² · 2.04 H(2u) · (u/2)^{-θ}/10¹³ ≤ e^{-θ log(u/2)/2}` for
  `4u > x⁺_0` (from `H = H_std = e^{8ℓ²}` and `θ log y ≥ 16ℓ² + 4ℓ + 2Λ + 10`, `switchOn_cond'`);
* `sum_oscModU_le`: `∑_k (log 4u_k)² · 2.04 H(2u_k) · oscModU(u_k) ≤ 10⁻⁸⁰` for `u_k = c 2^k`,
  `c ≥ 2` (the geometric sum with ratio `2^{-θ/4}`, `1/θ ≤ S/1000`).
-/

@[expose] public section

open Set Real Construction CaplLink

namespace BModel

/-- The modulus of `R'` on windows inside `[u/2, 4u]`: `0` if `4u ≤ x⁺_0`, else
`(u/2)^{-θ}/10¹³`. -/
noncomputable def oscModU (θ : ℝ) (X₀ : ℕ) (u : ℝ) : ℝ :=
  if 4 * u ≤ switchOn (swS θ X₀) 0 then 0 else mS θ (u / 2) / 10 ^ 13

lemma oscModU_nonneg (θ : ℝ) (X₀ : ℕ) {u : ℝ} (hu : 0 < u) : 0 ≤ oscModU θ X₀ u := by
  unfold oscModU
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mS_nonneg θ (by linarith)) (by norm_num)

/-- The window modulus is at most the scale modulus. -/
lemma oscMod_le_U {θ : ℝ} (hθ : 0 ≤ θ) {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {u s t : ℝ}
    (hu : 0 < u) (hs : u / 2 ≤ s) (ht : t ≤ 4 * u) : oscMod θ X₀ s t ≤ oscModU θ X₀ u := by
  have hU0 := oscModU_nonneg θ X₀ hu
  unfold oscMod
  by_cases h1 : t ≤ switchOn (swS θ X₀) 0
  · rw [if_pos h1]; exact hU0
  · rw [if_neg h1]
    unfold oscModU
    rw [if_neg (fun h2 => h1 (ht.trans h2))]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    push_neg at h1
    -- `u/2` is far beyond `X₀`: `log(u/2) ≥ S² - 3`
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := QueueMono.one_lt_of_logX hX0 hX
    set S := swS θ (X₀ : ℝ) with hS
    have hSX : (X₀ : ℝ) ≤ S := le_swS θ _
    have hx0 : Real.log (switchOn S 0) = S ^ 2 := log_switchOn_zero S
    have hx0p : 0 < switchOn S 0 := switchOn_pos S 0
    have h4u : switchOn S 0 < 4 * u := lt_of_lt_of_le h1 ht
    have hl8 : Real.log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    have hLS : S ^ 2 - 3 ≤ Real.log (u / 2) := by
      have h := Real.log_lt_log hx0p h4u
      have e : Real.log (4 * u) = Real.log (u / 2) + Real.log 8 := by
        rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
      rw [hx0, e] at h; linarith
    have hS8 : (10 : ℝ) ^ 8 ≤ S := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < X₀); linarith
    have hu2 : 1 < u / 2 := by
      have : (0 : ℝ) < Real.log (u / 2) := by nlinarith
      exact (Real.log_pos_iff (by positivity)).mp this
    have hll : 1.1 ≤ Real.log (Real.log (u / 2)) := by
      rw [Real.le_log_iff_exp_le (by nlinarith)]
      have := Real.exp_one_lt_d9
      have e : Real.exp 1.1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have e3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr
      nlinarith
    calc mS θ (max s (switchOn (swS θ X₀) 0)) ≤ mS θ (u / 2) :=
          mS_anti hθ hu2 hll (hs.trans (le_max_left _ _))
      _ ≤ mS θ (u / 2) := le_rfl

set_option maxHeartbeats 1000000 in
/-- **The weight of one scale beyond the switch-on**, for every design: for `4u > x⁺_0`,
`log(u/2) ≥ S² - 3` and `(log 4u)² · 2.04 H(2u) ≤ 9 e^{2ℓ + 8ℓ² + 1}`, `ℓ = log log(u/2)`
(`H = H_std = e^{8ℓ₂²}` at `2u`). -/
theorem logsq_H_le {θ : ℝ} {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ}
    (h4 : switchOn (swS θ X₀) 0 < 4 * u) :
    swS θ (X₀ : ℝ) ^ 2 - 3 ≤ Real.log (u / 2) ∧
    Real.log (4 * u) ^ 2 * (2.04 * Queue6.Hc X₀ (2 * u)) ≤
      9 * Real.exp (2 * Real.log (Real.log (u / 2)) + 8 * Real.log (Real.log (u / 2)) ^ 2 + 1) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  set S := swS θ (X₀ : ℝ) with hS
  have hSX : (X₀ : ℝ) ≤ S := le_swS θ _
  have hx0 : Real.log (switchOn S 0) = S ^ 2 := log_switchOn_zero S
  have hx0p : 0 < switchOn S 0 := switchOn_pos S 0
  have hu0 : 0 < u := by linarith
  -- `L = log(u/2) ≥ S² - 3`
  set L := Real.log (u / 2) with hL
  have hl8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hl80 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h4u : Real.log (4 * u) = L + Real.log 8 := by
    rw [hL, ← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have hLS : S ^ 2 - 3 ≤ L := by
    have := Real.log_lt_log hx0p h4
    rw [hx0, h4u] at this; linarith
  have hS8 : (10 : ℝ) ^ 8 ≤ S := by linarith
  have hL1 : (10 : ℝ) ^ 15 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  -- `H(2u) = e^{8ℓ₂²}`, `ℓ₂ = log log 2u ≤ ℓ + 2/L`
  have h2u : Real.log (2 * u) = L + Real.log 4 := by
    rw [hL, ← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have hl4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hl40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hS2 : S ≤ S ^ 2 - 3 := by nlinarith
  have hXu : (X₀ : ℝ) ≤ 2 * u := by
    have : Real.log X₀ ≤ Real.log (2 * u) := by rw [h2u]; linarith
    exact (Real.log_le_log_iff (by linarith) (by positivity)).mp this
  set ℓ₂ := Real.log (Real.log (2 * u)) with hℓ₂
  have hℓ₂le : ℓ₂ ≤ ℓ + 2 / L := by
    rw [hℓ₂, h2u, hℓ]
    have e : L + Real.log 4 = L * (1 + Real.log 4 / L) := by field_simp
    rw [e, Real.log_mul hL0.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log 4 / L by positivity)
    have : Real.log 4 / L ≤ 2 / L := div_le_div_of_nonneg_right hl4.le hL0.le
    linarith
  have hℓ₂ge : 2 * Real.log X₀ - 1 ≤ ℓ₂ := by
    have hX2 : (X₀ : ℝ) ^ 2 * Real.exp (-1) ≤ Real.log (2 * u) := by
      have h1 : Real.exp (-1) ≤ 1 / 2 := by
        have := Real.exp_one_gt_d9
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
      have h5 : (X₀ : ℝ) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hX0 hSX 2
      have h6 : (2 : ℝ) ≤ (X₀ : ℝ) ^ 2 / 2 := by nlinarith
      rw [h2u]
      nlinarith [Real.exp_pos (-1)]
    have hpos : 0 < (X₀ : ℝ) ^ 2 * Real.exp (-1) := by positivity
    have := Real.log_le_log hpos hX2
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at this
    push_cast at this; rw [← hℓ₂] at this; linarith
  have hs : sHroot < capS X₀ (2 * u) := by
    unfold capS; rw [← hℓ₂]
    have := sHroot_mem.2
    have h3 : Real.log (Real.log X₀) ≤ Real.log X₀ / 100 := by
      have := LagSplit.eight_log_sq_le hX
      have h0 : 0 ≤ Real.log (Real.log X₀) := Real.log_nonneg (by linarith)
      nlinarith
    linarith
  have hstd : 7.5 * Real.log X₀ + Real.log 4 ≤ 4 * ℓ₂ ^ 2 := by
    have h1 : Real.log X₀ ≤ ℓ₂ := by linarith
    have h2 : Real.log X₀ ^ 2 ≤ ℓ₂ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  obtain ⟨-, hH⟩ := capH_eq_std hX0 hX hXu hs hstd
  have hHc : Queue6.Hc X₀ (2 * u) = Real.exp (8 * ℓ₂ ^ 2) := by
    unfold Queue6.Hc; rw [max_eq_left hXu]; exact hH
  -- `8ℓ₂² ≤ 8ℓ² + 1`
  have hℓL : ℓ ≤ L / 10 ^ 6 := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have hsq : L ^ (1 / 2 : ℝ) ≤ L / 10 ^ 7 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have h8 : 8 * ℓ₂ ^ 2 ≤ 8 * ℓ ^ 2 + 1 := by
    have hℓ₂0 : 0 ≤ ℓ₂ := by linarith
    have : ℓ₂ ^ 2 ≤ (ℓ + 2 / L) ^ 2 := pow_le_pow_left₀ hℓ₂0 hℓ₂le 2
    have h2L : 2 / L ≤ 1 / 10 ^ 14 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    have h2L0 : 0 ≤ 2 / L := by positivity
    have e : (ℓ + 2 / L) ^ 2 = ℓ ^ 2 + 2 * ℓ * (2 / L) + (2 / L) ^ 2 := by ring
    have h3 : 2 * ℓ * (2 / L) ≤ 4 / 10 ^ 6 := by
      rw [show 2 * ℓ * (2 / L) = 4 * (ℓ / L) by field_simp; ring]
      have : ℓ / L ≤ 1 / 10 ^ 6 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
      linarith
    have h4 : (2 / L) ^ 2 ≤ (1 / 10 ^ 14) ^ 2 := pow_le_pow_left₀ h2L0 h2L 2
    have h5 : ((1 : ℝ) / 10 ^ 14) ^ 2 ≤ 1 / 100 := by norm_num
    linarith
  -- `(log 4u)² ≤ 4L² = 4 e^{2ℓ}`
  have hL2 : Real.log (4 * u) ^ 2 ≤ 4 * Real.exp (2 * ℓ) := by
    have e : Real.exp (2 * ℓ) = L ^ 2 := by
      rw [show 2 * ℓ = ((2 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓ, Real.exp_log hL0]
    rw [e, h4u]
    have : L + Real.log 8 ≤ 2 * L := by linarith
    have h0 : 0 ≤ L + Real.log 8 := by linarith
    nlinarith [pow_le_pow_left₀ h0 this 2]
  refine ⟨hLS, ?_⟩
  rw [hHc]
  have hmono : Real.exp (8 * ℓ₂ ^ 2) ≤ Real.exp (8 * ℓ ^ 2 + 1) := Real.exp_le_exp.mpr h8
  have e : Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1) = Real.exp (2 * ℓ) * Real.exp (8 * ℓ ^ 2 + 1) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have h0 : 0 ≤ Real.log (4 * u) ^ 2 := sq_nonneg _
  have hp1 := Real.exp_pos (2 * ℓ)
  have hp2 := Real.exp_pos (8 * ℓ ^ 2 + 1)
  calc Real.log (4 * u) ^ 2 * (2.04 * Real.exp (8 * ℓ₂ ^ 2))
      ≤ (4 * Real.exp (2 * ℓ)) * (2.04 * Real.exp (8 * ℓ ^ 2 + 1)) := by
        apply mul_le_mul hL2 _ (by positivity) (by positivity)
        linarith
    _ ≤ 9 * (Real.exp (2 * ℓ) * Real.exp (8 * ℓ ^ 2 + 1)) := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **One scale beyond the switch-on**: for `4u > x⁺_0`,
`(log 4u)² · 2.04 H(2u) · (u/2)^{-θ}/10¹³ ≤ e^{-θ log(u/2)/2}`. -/
theorem oscModU_term_le {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (h4 : switchOn (swS θ X₀) 0 < 4 * u) :
    Real.log (4 * u) ^ 2 * (2.04 * Queue6.Hc X₀ (2 * u) * ((u / 2) ^ (-θ) / 10 ^ 13)) ≤
      Real.exp (-(θ * Real.log (u / 2)) / 2) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  set S := swS θ (X₀ : ℝ) with hS
  have hSX : (X₀ : ℝ) ≤ S := le_swS θ _
  have hx0 : Real.log (switchOn S 0) = S ^ 2 := log_switchOn_zero S
  have hx0p : 0 < switchOn S 0 := switchOn_pos S 0
  have hu0 : 0 < u := by linarith
  -- `L = log(u/2) ≥ S² - 3`
  set L := Real.log (u / 2) with hL
  have hl8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hl80 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h4u : Real.log (4 * u) = L + Real.log 8 := by
    rw [hL, ← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have hLS : S ^ 2 - 3 ≤ L := by
    have := Real.log_lt_log hx0p h4
    rw [hx0, h4u] at this; linarith
  have hS8 : (10 : ℝ) ^ 8 ≤ S := by linarith
  have hL1 : (10 : ℝ) ^ 15 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  -- the switch-on condition at `u/2`
  have hsw := switchOn_cond' hθ.1 hX0 hX (u / 2) (by rw [← hS, hx0]; linarith)
  rw [← hL] at hsw
  set ℓ := Real.log L with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  -- `H(2u) = e^{8ℓ₂²}`, `ℓ₂ = log log 2u ≤ ℓ + 2/L`
  have h2u : Real.log (2 * u) = L + Real.log 4 := by
    rw [hL, ← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have hl4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hl40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hS2 : S ≤ S ^ 2 - 3 := by nlinarith
  have hXu : (X₀ : ℝ) ≤ 2 * u := by
    have : Real.log X₀ ≤ Real.log (2 * u) := by rw [h2u]; linarith
    exact (Real.log_le_log_iff (by linarith) (by positivity)).mp this
  set ℓ₂ := Real.log (Real.log (2 * u)) with hℓ₂
  have hℓ₂le : ℓ₂ ≤ ℓ + 2 / L := by
    rw [hℓ₂, h2u, hℓ]
    have e : L + Real.log 4 = L * (1 + Real.log 4 / L) := by field_simp
    rw [e, Real.log_mul hL0.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log 4 / L by positivity)
    have : Real.log 4 / L ≤ 2 / L := div_le_div_of_nonneg_right hl4.le hL0.le
    linarith
  have hℓ₂ge : 2 * Real.log X₀ - 1 ≤ ℓ₂ := by
    have hX2 : (X₀ : ℝ) ^ 2 * Real.exp (-1) ≤ Real.log (2 * u) := by
      have h1 : Real.exp (-1) ≤ 1 / 2 := by
        have := Real.exp_one_gt_d9
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
      have h5 : (X₀ : ℝ) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hX0 hSX 2
      have h6 : (2 : ℝ) ≤ (X₀ : ℝ) ^ 2 / 2 := by nlinarith
      rw [h2u]
      nlinarith [Real.exp_pos (-1)]
    have hpos : 0 < (X₀ : ℝ) ^ 2 * Real.exp (-1) := by positivity
    have := Real.log_le_log hpos hX2
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at this
    push_cast at this; rw [← hℓ₂] at this; linarith
  have hs : sHroot < capS X₀ (2 * u) := by
    unfold capS; rw [← hℓ₂]
    have := sHroot_mem.2
    have h3 : Real.log (Real.log X₀) ≤ Real.log X₀ / 100 := by
      have := LagSplit.eight_log_sq_le hX
      have h0 : 0 ≤ Real.log (Real.log X₀) := Real.log_nonneg (by linarith)
      nlinarith
    linarith
  have hstd : 7.5 * Real.log X₀ + Real.log 4 ≤ 4 * ℓ₂ ^ 2 := by
    have h1 : Real.log X₀ ≤ ℓ₂ := by linarith
    have h2 : Real.log X₀ ^ 2 ≤ ℓ₂ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  obtain ⟨-, hH⟩ := capH_eq_std hX0 hX hXu hs hstd
  have hHc : Queue6.Hc X₀ (2 * u) = Real.exp (8 * ℓ₂ ^ 2) := by
    unfold Queue6.Hc; rw [max_eq_left hXu]; exact hH
  -- `8ℓ₂² ≤ 8ℓ² + 1`
  have hℓL : ℓ ≤ L / 10 ^ 6 := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have hsq : L ^ (1 / 2 : ℝ) ≤ L / 10 ^ 7 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have h8 : 8 * ℓ₂ ^ 2 ≤ 8 * ℓ ^ 2 + 1 := by
    have hℓ₂0 : 0 ≤ ℓ₂ := by linarith
    have : ℓ₂ ^ 2 ≤ (ℓ + 2 / L) ^ 2 := pow_le_pow_left₀ hℓ₂0 hℓ₂le 2
    have h2L : 2 / L ≤ 1 / 10 ^ 14 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    have h2L0 : 0 ≤ 2 / L := by positivity
    have e : (ℓ + 2 / L) ^ 2 = ℓ ^ 2 + 2 * ℓ * (2 / L) + (2 / L) ^ 2 := by ring
    have h3 : 2 * ℓ * (2 / L) ≤ 4 / 10 ^ 6 := by
      rw [show 2 * ℓ * (2 / L) = 4 * (ℓ / L) by field_simp; ring]
      have : ℓ / L ≤ 1 / 10 ^ 6 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
      linarith
    have h4 : (2 / L) ^ 2 ≤ (1 / 10 ^ 14) ^ 2 := pow_le_pow_left₀ h2L0 h2L 2
    have h5 : ((1 : ℝ) / 10 ^ 14) ^ 2 ≤ 1 / 100 := by norm_num
    linarith
  -- `(log 4u)² ≤ 4L² = 4 e^{2ℓ}`
  have hL2 : Real.log (4 * u) ^ 2 ≤ 4 * Real.exp (2 * ℓ) := by
    have e : Real.exp (2 * ℓ) = L ^ 2 := by
      rw [show 2 * ℓ = ((2 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓ, Real.exp_log hL0]
    rw [e, h4u]
    have : L + Real.log 8 ≤ 2 * L := by linarith
    have h0 : 0 ≤ L + Real.log 8 := by linarith
    nlinarith [pow_le_pow_left₀ h0 this 2]
  -- assemble
  have hθp := hθ.1
  have hpow : (u / 2) ^ (-θ) = Real.exp (-(θ * L)) := by
    rw [Real.rpow_def_of_pos (by positivity), ← hL]; ring_nf
  rw [hHc, hpow]
  have hE : 4 * Real.exp (2 * ℓ) * (2.04 * Real.exp (8 * ℓ ^ 2 + 1) *
      (Real.exp (-(θ * L)) / 10 ^ 13)) ≤ Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1 - θ * L) := by
    have e : Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1 - θ * L) =
        Real.exp (2 * ℓ) * Real.exp (8 * ℓ ^ 2 + 1) * Real.exp (-(θ * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [e]
    have hp := mul_pos (mul_pos (Real.exp_pos (2 * ℓ)) (Real.exp_pos (8 * ℓ ^ 2 + 1)))
      (Real.exp_pos (-(θ * L)))
    nlinarith
  have hmono : Real.exp (8 * ℓ₂ ^ 2) ≤ Real.exp (8 * ℓ ^ 2 + 1) := Real.exp_le_exp.mpr h8
  have hfin : Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1 - θ * L) ≤ Real.exp (-(θ * L) / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hq0 : 0 ≤ Real.exp (-(θ * L)) / 10 ^ 13 := by positivity
  calc Real.log (4 * u) ^ 2 * (2.04 * Real.exp (8 * ℓ₂ ^ 2) * (Real.exp (-(θ * L)) / 10 ^ 13))
      ≤ 4 * Real.exp (2 * ℓ) * (2.04 * Real.exp (8 * ℓ ^ 2 + 1) *
          (Real.exp (-(θ * L)) / 10 ^ 13)) := by
        apply mul_le_mul hL2 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) hq0
    _ ≤ _ := hE.trans hfin

/-- `10⁸⁰ ≤ e^{200}`. -/
lemma ten80_le_exp200 : (10 : ℝ) ^ 80 ≤ Real.exp 200 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (10 : ℝ) ^ 80 ≤ 2.7182818283 ^ 200 := by norm_num
    _ ≤ Real.exp 1 ^ 200 := pow_le_pow_left₀ (by norm_num) h.le 200

set_option maxHeartbeats 1000000 in
/-- **The `R`-part of the dyadic sums** (the paper's `∑_{u ≥ x₁/4} log²(3u) H(u) u^{-θ} ≤ e^{-Λ²}`,
04f, small `θ`): for `u_k = c 2^k`, `c ≥ 2`,
`∑_{k<N} (log 4u_k)² · 2.04 H(2u_k) · oscModU(u_k) ≤ 10⁻⁸⁰`. -/
theorem sum_oscModU_le_pos {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {c : ℝ} (hc : 2 ≤ c) (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.log (4 * (c * 2 ^ k)) ^ 2 *
      (2.04 * Queue6.Hc X₀ (2 * (c * 2 ^ k)) * oscModU θ X₀ (c * 2 ^ k)) ≤ 1 / 10 ^ 80 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hθp := hθ.1
  set S := swS θ (X₀ : ℝ) with hS
  have hSX : (X₀ : ℝ) ≤ S := le_swS θ _
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hS8 : (10 : ℝ) ^ 8 ≤ S := by linarith
  have hθS : 1000 ≤ θ * S := by
    have : 1000 / θ ≤ S := le_max_right _ _
    rw [div_le_iff₀ hθp] at this; linarith
  have hx0 : Real.log (switchOn S 0) = S ^ 2 := log_switchOn_zero S
  have hx0p : 0 < switchOn S 0 := switchOn_pos S 0
  set δ := Real.log 2 with hδ
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ1 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  set E := Real.exp (-(θ * (S ^ 2 - 3)) / 4) with hE
  set r := Real.exp (-(θ * δ) / 4) with hr
  have hr0 : 0 < r := Real.exp_pos _
  -- the terms
  have hterm : ∀ k : ℕ, Real.log (4 * (c * 2 ^ k)) ^ 2 *
      (2.04 * Queue6.Hc X₀ (2 * (c * 2 ^ k)) * oscModU θ X₀ (c * 2 ^ k)) ≤ E * r ^ k := by
    intro k
    set u := c * 2 ^ k with hu
    have hu0 : 0 < u := by positivity
    have hER : 0 ≤ E * r ^ k := by positivity
    unfold oscModU
    split_ifs with h4
    · simp only [mul_zero]; exact hER
    · push_neg at h4
      rw [show mS θ (u / 2) = (u / 2) ^ (-θ) from if_neg hθp.ne']
      refine (oscModU_term_le hθ hX h4).trans ?_
      -- `log(u/2) ≥ S² - 3` and `log(u/2) ≥ kδ`
      have hLu : Real.log (u / 2) = Real.log (c / 2) + k * δ := by
        rw [hu, show c * 2 ^ k / 2 = c / 2 * 2 ^ k by ring,
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hc2 : 0 ≤ Real.log (c / 2) := Real.log_nonneg (by linarith)
      have hl8 : Real.log 8 < 3 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; linarith [Real.log_two_lt_d9]
      have hLS : S ^ 2 - 3 ≤ Real.log (u / 2) := by
        have h1 := Real.log_lt_log hx0p h4
        have e : Real.log (4 * u) = Real.log (u / 2) + Real.log 8 := by
          rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
        rw [hx0, e] at h1; linarith
      have hrk : r ^ k = Real.exp (-(θ * (k * δ)) / 4) := by
        rw [hr, ← Real.exp_nat_mul]; ring_nf
      rw [hrk, hE, ← Real.exp_add, Real.exp_le_exp]
      have : 0 ≤ θ * Real.log (c / 2) := mul_nonneg hθp.le hc2
      nlinarith
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.mul_sum]
  -- `∑ r^k ≤ 1/(1 - r) ≤ 12/θ ≤ S`
  have hθ2 : θ ≤ 1 / 2 := by linarith [hθ.2]
  have hθδ0 : 0 < θ * δ := by positivity
  have hc1 : θ * δ / 4 ≤ 1 := by nlinarith
  have hr1 : r ≤ 1 / (1 + θ * δ / 4) := by
    have e : -(θ * δ) / 4 = -(θ * δ / 4) := by ring
    rw [hr, e, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [Real.add_one_le_exp (θ * δ / 4)]
  have hrlt : r < 1 := by
    refine lt_of_le_of_lt hr1 ?_
    rw [div_lt_one (by positivity)]; linarith
  have hgeom : ∑ k ∈ Finset.range N, r ^ k ≤ S := by
    rw [geom_sum_eq hrlt.ne N, div_le_iff_of_neg (by linarith)]
    have h1 : θ * δ / 8 ≤ 1 - r := by
      have : 1 / (1 + θ * δ / 4) ≤ 1 - θ * δ / 8 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hrN : 0 ≤ r ^ N := pow_nonneg hr0.le N
    have h2 : 1 ≤ S * (θ * δ / 8) := by nlinarith
    nlinarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc E * ∑ k ∈ Finset.range N, r ^ k ≤ E * S := mul_le_mul_of_nonneg_left hgeom hE0
    _ ≤ Real.exp (-200) := by
        have hSe : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
        have : E * S ≤ E * Real.exp S := mul_le_mul_of_nonneg_left hSe hE0
        refine this.trans ?_
        rw [hE, ← Real.exp_add, Real.exp_le_exp]
        nlinarith
    _ ≤ 1 / 10 ^ 80 := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by positivity) ten80_le_exp200

set_option maxHeartbeats 2000000 in
/-- **The `R`-part of the dyadic sums for the design `θ = 0`** (§8, the per-zero `o_R`
argument, here with the modulus density `g`): for `u_k = c 2^k`, `c ≥ 2`,
`∑_{k<N} (log 4u_k)² · 2.04 H(2u_k) · oscModU(u_k) ≤ 10⁻⁸⁰`. Each nonzero term is at most
`e^{-ℓ² + 21.8ℓ} ≤ L^{-2} e^{-1000}` (`L = log(u_k/2) ≥ 0.345 (k + 1)`, `ℓ = log L ≥ 2Λ - 1`), and
`∑ (k+1)^{-2} ≤ 2`. -/
theorem sum_oscModU_le_zero {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {c : ℝ} (hc : 2 ≤ c)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.log (4 * (c * 2 ^ k)) ^ 2 *
      (2.04 * Queue6.Hc X₀ (2 * (c * 2 ^ k)) * oscModU 0 X₀ (c * 2 ^ k)) ≤ 1 / 10 ^ 80 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  set S := swS 0 (X₀ : ℝ) with hS
  have hSX : (X₀ : ℝ) ≤ S := le_swS 0 _
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hS8 : (10 : ℝ) ^ 8 ≤ S := by linarith
  set δ := Real.log 2 with hδ
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hE : Real.exp (-1000) ≤ 1 / 10 ^ 300 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by positivity)
    have h := Real.exp_one_gt_d9
    have e : Real.exp 1000 = Real.exp 1 ^ 1000 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 300 = ((10 : ℝ) ^ 3) ^ 100 := by rw [← pow_mul]
      _ ≤ ((2 : ℝ) ^ 10) ^ 100 := pow_le_pow_left₀ (by norm_num) (by norm_num) 100
      _ = 2 ^ 1000 := by rw [← pow_mul]
      _ ≤ Real.exp 1 ^ 1000 := pow_le_pow_left₀ (by norm_num) (by linarith) 1000
  -- the terms
  have hterm : ∀ k : ℕ, Real.log (4 * (c * 2 ^ k)) ^ 2 *
      (2.04 * Queue6.Hc X₀ (2 * (c * 2 ^ k)) * oscModU 0 X₀ (c * 2 ^ k)) ≤
      Real.exp (-1000) * (9 * (1 / ((k : ℝ) + 1) ^ 2)) := by
    intro k
    set u := c * 2 ^ k with hu
    have hu0 : 0 < u := by positivity
    have hR0 : 0 ≤ Real.exp (-1000) * (9 * (1 / ((k : ℝ) + 1) ^ 2)) := by positivity
    unfold oscModU
    split_ifs with h4
    · simp only [mul_zero]; exact hR0
    · push_neg at h4
      obtain ⟨hLS, hW⟩ := logsq_H_le (θ := 0) hX h4
      rw [← hS] at hLS
      set L := Real.log (u / 2) with hL
      set ℓ := Real.log L with hℓ
      have hS0 : 0 < S := by linarith
      have hlS : 10 ^ 8 ≤ Real.log S := hX.trans (Real.log_le_log (by linarith) hSX)
      have hSL : S ≤ L := by nlinarith
      have hL0 : 0 < L := by linarith
      have hL1 : (10 : ℝ) ^ 8 ≤ L := by linarith
      have hℓ0 : 10 ^ 8 ≤ ℓ := hlS.trans (Real.log_le_log hS0 hSL)
      have hLe : Real.exp ℓ = L := Real.exp_log hL0
      -- `L ≥ 0.69 k`
      have hLk : 0.69 * (k : ℝ) ≤ L := by
        have e : L = Real.log (c / 2) + k * δ := by
          rw [hL, hu, show c * 2 ^ k / 2 = c / 2 * 2 ^ k by ring,
            Real.log_mul (by positivity) (by positivity), Real.log_pow]
        have : 0 ≤ Real.log (c / 2) := Real.log_nonneg (by linarith)
        have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      -- `(k+1)² ≤ L³`
      have hk3 : ((k : ℝ) + 1) ^ 2 ≤ L ^ 3 := by
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        rcases le_or_gt (k : ℝ) (10 ^ 7) with hk | hk
        · have h1 : ((k : ℝ) + 1) ^ 2 ≤ (10 ^ 7 + 1) ^ 2 := by gcongr
          have h2 : (10 : ℝ) ^ 24 ≤ L ^ 3 := by
            have := pow_le_pow_left₀ (by norm_num) hL1 3; norm_num at this ⊢; linarith
          nlinarith
        · have h1 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
          have h2 : (0.69 * (k : ℝ)) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by positivity) hLk 3
          nlinarith
      -- the exponent
      have hgS : mS 0 (u / 2) = Real.exp (-(9 * (ℓ - 1.1) ^ 2)) := by
        rw [show mS 0 (u / 2) = gS (u / 2) from if_pos rfl]; rfl
      rw [hgS]
      have hexp : Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1) * Real.exp (-(9 * (ℓ - 1.1) ^ 2)) ≤
          Real.exp (-1000) * Real.exp (-(3 * ℓ)) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]; nlinarith
      have hL3 : Real.exp (-(3 * ℓ)) = 1 / L ^ 3 := by
        rw [Real.exp_neg, show 3 * ℓ = ((3 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hLe,
          one_div]
      have hfrac : 1 / L ^ 3 ≤ 1 / ((k : ℝ) + 1) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hk3
      have hW0 : 0 ≤ Real.log (4 * u) ^ 2 * (2.04 * Queue6.Hc X₀ (2 * u)) := by
        have : 0 ≤ Queue6.Hc X₀ (2 * u) := Construction.capH_nonneg' _ _
        positivity
      have hg0 : 0 ≤ Real.exp (-(9 * (ℓ - 1.1) ^ 2)) := (Real.exp_pos _).le
      calc Real.log (4 * u) ^ 2 * (2.04 * Queue6.Hc X₀ (2 * u) *
            (Real.exp (-(9 * (ℓ - 1.1) ^ 2)) / 10 ^ 13))
          = (Real.log (4 * u) ^ 2 * (2.04 * Queue6.Hc X₀ (2 * u))) *
              Real.exp (-(9 * (ℓ - 1.1) ^ 2)) / 10 ^ 13 := by ring
        _ ≤ (9 * Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1)) * Real.exp (-(9 * (ℓ - 1.1) ^ 2)) / 10 ^ 13 := by
            gcongr
        _ ≤ 9 * (Real.exp (-1000) * Real.exp (-(3 * ℓ))) := by
            have := hexp
            have h0 : 0 ≤ Real.exp (2 * ℓ + 8 * ℓ ^ 2 + 1) * Real.exp (-(9 * (ℓ - 1.1) ^ 2)) :=
              by positivity
            nlinarith
        _ ≤ Real.exp (-1000) * (9 * (1 / ((k : ℝ) + 1) ^ 2)) := by
            rw [hL3]; have := Real.exp_pos (-1000); nlinarith
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- `∑_{k<N} (k+1)^{-2} ≤ 2`
  have hsq : ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
    have e : ∑ i ∈ Finset.Ioo 0 (N + 1), ((i : ℝ) ^ 2)⁻¹ =
        ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) ^ 2) := by
      have hI : Finset.Ioo 0 (N + 1) = Finset.Ico 1 (N + 1) := by
        ext i; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
      rw [hI, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) fun k _ => ?_
      push_cast; rw [one_div]; ring_nf
    rw [← e]
    exact h.trans (by norm_num)
  have h18 : Real.exp (-1000) * (9 * ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) ^ 2)) ≤
      Real.exp (-1000) * (9 * 2) := by
    gcongr
  refine h18.trans ?_
  have h220 : (18 : ℝ) ≤ 10 ^ 220 :=
    le_trans (by norm_num : (18 : ℝ) ≤ 10 ^ 2) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h300 : (10 : ℝ) ^ 300 = 10 ^ 80 * 10 ^ 220 := by rw [← pow_add]
  calc Real.exp (-1000) * (9 * 2) ≤ 1 / 10 ^ 300 * 18 := by nlinarith
    _ ≤ 1 / 10 ^ 80 := by
        rw [h300, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [show (0 : ℝ) < 10 ^ 80 by positivity]

/-- **The `R`-part of the dyadic sums**, for every design `θ ∈ [0, 1/2 - 10⁻⁴]`. -/
theorem sum_oscModU_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {c : ℝ} (hc : 2 ≤ c) (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.log (4 * (c * 2 ^ k)) ^ 2 *
      (2.04 * Queue6.Hc X₀ (2 * (c * 2 ^ k)) * oscModU θ X₀ (c * 2 ^ k)) ≤ 1 / 10 ^ 80 := by
  by_cases h0 : θ = 0
  · subst h0; exact sum_oscModU_le_zero hX hc N
  · exact sum_oscModU_le_pos ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), hθ.2⟩ hX hc N

end BModel

end
