module

public import RequestProject.Beurling.Noise.Lemma53Dickman

/-!
# Lemma 5.3: the one-step inequality (28) for every `L_z ≥ 100`

`lemV_onestep`: for `L ≥ 100` and `1 ≤ u ≤ L`,

  `L (1 - e^{-α}) E_* - 2 K_M r(u) - 22 e^{-0.4L} - X_L(u) > 0`,

with `X_L(u) = 0.7627/(C₀ (1 - log u) u)` for `u < 1 + log 72/L` and `0` otherwise. The paper's
reduction to the certified cases: the left side increases in `L` (`mul_one_sub_exp_mono`) and the
range of `X` shrinks, so `L = max(100, u)` is the worst case. For `u ≤ 10⁶` this is
`BSCert.lemV_certificate_dickman` (without `X`) and `BSCert.lemVExt_certificate_dickman` (on
`[1, 2]`, at `L = 100`, with `X`); for `u > 10⁶` it is the analytic bound of the paper
(`E_* = 1/2`, `r(u) ≤ log(2(u+1))/(1/2)` by (R4)).
-/

@[expose] public section

open Real Set Dickman

namespace BSaias

/-- `X_L(u)`. -/
noncomputable def XL (L u : ℝ) : ℝ :=
  if u < 1 + Real.log 72 / L then 0.7627 / (0.70 * (1 - Real.log u) * u) else 0

/-- The left side of (28) at `L`. -/
noncomputable def lhs28 (L u : ℝ) : ℝ :=
  L * (1 - Real.exp (-BSCert.lemVAlpha u L)) * Estar u - 2 * 1.01 * ratio u
    - 22 * Real.exp (-0.4 * L) - XL L u

/-- `L ↦ L(1 - e^{-c/L})` is non-decreasing on `(0, ∞)` for `c ≥ 0`. -/
lemma mul_one_sub_exp_mono {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    a * (1 - Real.exp (-(c / a))) ≤ b * (1 - Real.exp (-(c / b))) := by
  set f : ℝ → ℝ := fun L => L * (1 - Real.exp (-(c / L)))
  have hd : ∀ L, 0 < L → HasDerivAt f
      (1 * (1 - Real.exp (-(c / L))) + L * (-(Real.exp (-(c / L)) * (-(-(c / L ^ 2)))))) L := by
    intro L hL
    have h1 : HasDerivAt (fun L : ℝ => c / L) (-(c / L ^ 2)) L := by
      have := (hasDerivAt_inv hL.ne').const_mul c
      convert! this using 1
      ring
    have h2 := ((h1.neg).exp)
    exact (hasDerivAt_id L).mul ((hasDerivAt_const L 1).sub h2) |>.congr_deriv (by simp)
  have hmono : MonotoneOn f (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a)
    · intro L hL; exact (hd L (lt_of_lt_of_le ha hL)).continuousAt.continuousWithinAt
    · intro L hL
      rw [interior_Ici] at hL
      exact (hd L (lt_trans ha hL)).differentiableAt.differentiableWithinAt
    · intro L hL
      rw [interior_Ici] at hL
      have hL0 : 0 < L := lt_trans ha hL
      rw [(hd L hL0).deriv]
      set y := c / L
      have hy : y * L = c := by simp only [y]; field_simp
      have he := Real.add_one_le_exp y
      have hpos := Real.exp_pos (-y)
      have : (1 + y) * Real.exp (-y) ≤ 1 := by
        calc (1 + y) * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
              mul_le_mul_of_nonneg_right (by linarith) hpos.le
          _ = 1 := by rw [← Real.exp_add]; simp
      have e : L * (-(Real.exp (-y) * -(-(c / L ^ 2)))) = -(y * Real.exp (-y)) := by
        simp only [y]; field_simp
      rw [e]; nlinarith
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hab) hab

lemma lemVAlpha_eq (u L : ℝ) :
    BSCert.lemVAlpha u L = (4 * 3.2 * (Real.log (u + 1) + (u - 1) / (u + 1))) / L := rfl

lemma lemVAlpha_num_nonneg {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ 4 * 3.2 * (Real.log (u + 1) + (u - 1) / (u + 1)) := by
  have : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
  have : 0 ≤ (u - 1) / (u + 1) := div_nonneg (by linarith) (by linarith)
  positivity

/-- `L(1 - e^{-α(u, L)})` is non-decreasing in `L`. -/
lemma lemV_main_mono {u a b : ℝ} (hu : 1 ≤ u) (ha : 0 < a) (hab : a ≤ b) :
    a * (1 - Real.exp (-BSCert.lemVAlpha u a)) ≤ b * (1 - Real.exp (-BSCert.lemVAlpha u b)) := by
  rw [lemVAlpha_eq, lemVAlpha_eq]
  exact mul_one_sub_exp_mono (lemVAlpha_num_nonneg hu) ha hab

lemma one_sub_exp_neg_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) := by
  have := Real.exp_le_one_iff.mpr (show -x ≤ 0 by linarith); linarith

lemma log72_lt : Real.log 72 < 100 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.add_one_le_exp (100 : ℝ); linarith

/-- **The one-step inequality (28)** for every `L ≥ 100`, `1 ≤ u ≤ L`. -/
theorem lemV_onestep {L u : ℝ} (hL : 100 ≤ L) (hu1 : 1 ≤ u) (huL : u ≤ L) : 0 < lhs28 L u := by
  have hL0 : 0 < L := by linarith
  have hr0 : 0 ≤ ratio u := (ratio_pos (by linarith)).le
  have hEs := Estar_nonneg u
  have hα : 0 ≤ BSCert.lemVAlpha u L := by
    rw [lemVAlpha_eq]; exact div_nonneg (lemVAlpha_num_nonneg hu1) hL0.le
  have h72 := log72_lt
  by_cases hX : u < 1 + Real.log 72 / L
  · -- the case with `X(u)`: `lemVExt` at `L = 100`
    have hu2 : u < 2 := by
      have : Real.log 72 / L < 1 := by rw [div_lt_one hL0]; linarith
      linarith
    have hX100 : u < 1 + Real.log 72 / 100 := by
      have : Real.log 72 / L ≤ Real.log 72 / 100 :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by norm_num) hL
      linarith
    have hc := BSCert.lemVExt_certificate_dickman u hu1 hu2.le
    unfold BSCert.lemVExtLHS at hc
    have hE : Estar u = 1 / 2 := by unfold Estar; rw [if_neg (by linarith)]
    have hXe : XL L u = BSCert.lemVX u := by
      unfold XL BSCert.lemVX; rw [if_pos hX, if_pos hX100]
    have hmono := lemV_main_mono hu1 (by norm_num : (0 : ℝ) < 100) hL
    have he : Real.exp (-0.4 * L) ≤ Real.exp (-0.4 * 100) := Real.exp_le_exp.mpr (by linarith)
    have hall : 0 ≤ 2 * 1.01 * ratio u * (Real.exp 0.141 - 1) := by
      have := Real.one_le_exp (show (0:ℝ) ≤ 0.141 by norm_num)
      exact mul_nonneg (by positivity) (by linarith)
    unfold lhs28
    rw [hE, hXe]
    nlinarith
  · have hXe : XL L u = 0 := by unfold XL; rw [if_neg hX]
    rcases le_or_gt u 1000000 with hu6 | hu6
    · -- `lemV` at `max(100, u)`
      have hc := BSCert.lemV_certificate_dickman u hu1 hu6
      unfold BSCert.lemVLHS at hc
      have hM : max 100 u ≤ L := max_le hL huL
      have hmono := lemV_main_mono hu1 (lt_of_lt_of_le (by norm_num) (le_max_left 100 u)) hM
      have he : Real.exp (-0.4 * L) ≤ Real.exp (-0.4 * max 100 u) :=
        Real.exp_le_exp.mpr (by linarith)
      have hEe : (if 2 ≤ u then max (1 / 2) (1 - 1 / ratio (u - 1)) else 1 / 2) = Estar u := rfl
      rw [hEe] at hc
      unfold lhs28
      rw [hXe]
      nlinarith
    · -- the analytic range `u > 10⁶`
      have hL6 : 1000000 < L := lt_of_lt_of_le hu6 huL
      set α := BSCert.lemVAlpha u L
      have hEs2 : 1 / 2 ≤ Estar u := by
        unfold Estar; split_ifs
        · exact le_max_left _ _
        · exact le_rfl
      -- `Lα ≥ 12.8 log(u+1)`
      have hlu : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
      have hLα : 12.8 * Real.log (u + 1) ≤ L * α := by
        simp only [α, lemVAlpha_eq]
        rw [mul_div_cancel₀ _ hL0.ne']
        have : 0 ≤ (u - 1) / (u + 1) := div_nonneg (by linarith) (by linarith)
        nlinarith
      -- `α ≤ 0.01`
      have hlogL : Real.log (L + 1) ≤ 7 + (L + 1) / 2900 := by
        have h8 : (2900 : ℝ) ≤ Real.exp 8 := by
          have := Real.exp_one_gt_d9
          have h : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h]
          calc (2900 : ℝ) ≤ 2.7182818283 ^ 8 := by norm_num
            _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) this.le 8
        have := Real.log_le_sub_one_of_pos (show 0 < (L + 1) / Real.exp 8 by positivity)
        rw [Real.log_div (by linarith) (Real.exp_pos 8).ne', Real.log_exp] at this
        have : (L + 1) / Real.exp 8 ≤ (L + 1) / 2900 :=
          div_le_div_of_nonneg_left (by linarith) (by norm_num) h8
        linarith
      have hα1 : α ≤ 0.01 := by
        simp only [α, lemVAlpha_eq]
        rw [div_le_iff₀ hL0]
        have h1 : Real.log (u + 1) ≤ Real.log (L + 1) := Real.log_le_log (by linarith) (by linarith)
        have h2 : (u - 1) / (u + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        nlinarith
      have hα0 : 0 ≤ α := hα
      -- `1 - e^{-α} ≥ α/(1+α)`
      have hk : α / (1 + α) ≤ 1 - Real.exp (-α) := by
        have h := Real.add_one_le_exp α
        have hpos := Real.exp_pos α
        have : Real.exp (-α) = 1 / Real.exp α := by rw [Real.exp_neg]; ring
        rw [this, div_le_iff₀ (by linarith)]
        rw [show (1 - 1 / Real.exp α) * (1 + α) = (1 + α) - (1 + α) / Real.exp α by ring]
        have : (1 + α) / Real.exp α ≤ 1 := by rw [div_le_one hpos]; linarith
        linarith
      -- `r(u) ≤ 2 log(2(u+1))`
      have hr : ratio u ≤ Real.log ((u + 1) / (1 / 2)) / (1 - 1 / 2) :=
        ratio_upper (by linarith) (by norm_num) (by norm_num)
      have hr' : ratio u ≤ 2 * Real.log (u + 1) + 2 * Real.log 2 := by
        rw [show (u + 1) / (1 / 2) = 2 * (u + 1) by ring, Real.log_mul (by norm_num) (by linarith)]
          at hr
        have e : (Real.log 2 + Real.log (u + 1)) / (1 - 1 / 2) =
            2 * Real.log (u + 1) + 2 * Real.log 2 := by ring
        linarith
      have hlog6 : 13 ≤ Real.log (u + 1) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have : Real.exp 13 ≤ 1000000 := by
          have := Real.exp_one_lt_d9
          have h : Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h]
          calc Real.exp 1 ^ 13 ≤ 2.7182818286 ^ 13 := pow_le_pow_left₀ (by positivity) this.le 13
            _ ≤ 1000000 := by norm_num
        linarith
      have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have he : Real.exp (-0.4 * L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hmain : 6.3 * Real.log (u + 1) ≤ L * (1 - Real.exp (-α)) * Estar u := by
        have h1 : L * (α / (1 + α)) ≥ 12.8 * Real.log (u + 1) / 1.01 := by
          rw [mul_div_assoc', ge_iff_le, div_le_div_iff₀ (by norm_num) (by linarith)]
          nlinarith
        have h2 : L * (1 - Real.exp (-α)) ≥ 12.8 * Real.log (u + 1) / 1.01 :=
          le_trans h1 (mul_le_mul_of_nonneg_left hk hL0.le)
        have h3 : 0 ≤ L * (1 - Real.exp (-α)) := le_trans (by positivity) h2
        calc 6.3 * Real.log (u + 1) ≤ (12.8 * Real.log (u + 1) / 1.01) * (1 / 2) := by
              rw [show (12.8 * Real.log (u + 1) / 1.01) * (1 / 2) =
                (640 / 101) * Real.log (u + 1) by norm_num; ring]
              nlinarith
          _ ≤ L * (1 - Real.exp (-α)) * Estar u := mul_le_mul h2 hEs2 (by norm_num) h3
      unfold lhs28
      rw [hXe]
      nlinarith

end BSaias

end
