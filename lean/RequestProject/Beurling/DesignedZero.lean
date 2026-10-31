module

public import RequestProject.Beurling.DesignedZeroAux

/-!
# Lemma 4.6 (A designed zero)
-/

@[expose] public section

open Complex Metric Set SmoothStep

namespace DesignedZero

/-- The designed term `M_k(s) = (α s/2) (x⁺)^{-w} Φ(w)/w`, `w = s - θ - iγ`: the first term
of (17). -/
noncomputable def Mk (θ α γ x : ℝ) (s : ℂ) : ℂ :=
  α * s / 2 * ((x : ℂ) ^ (-(s - θ - γ * I)) * phiTransform (s - θ - γ * I) / (s - θ - γ * I))

/-- The radius `δ_k = 9 log log x_k / log x_k` of Lemma 4.6. -/
noncomputable def designRadius (x : ℝ) : ℝ := 9 * Real.log (Real.log x) / Real.log x

/-- The hypotheses of Lemma 4.6, in the parameter range of the paper: `θ ∈ [1/20, 1/2]`,
`Λ = log X₀ ≥ 10`, `κ₀ ∈ [X₀⁻¹, 1/4]`, `log log x_k ≥ 2Λ`, `α_k γ_k = κ₀ x_k^{1-θ}/log³ x_k`,
and on the disc `|s - (1 + iγ_k)| ≤ δ_k`: `Z_B` is holomorphic, `1/2 ≤ |Z_B| ≤ Z_max = 2Λ` (the
hypothesis of the lemma) and `|Z_B'| ≤ 4.01 Λ²` (from Lemma 4.2, step 3 of the proof). -/
structure Lemma46Hyp (θ Λ κ₀ α γ x : ℝ) (ZB : ℂ → ℂ) : Prop where
  θ_ge : 1 / 20 ≤ θ
  θ_le : θ ≤ 1 / 2
  Λ_ge : 10 ≤ Λ
  κ_ge : Real.exp (-Λ) ≤ κ₀
  κ_le : κ₀ ≤ 1 / 4
  one_lt_x : 1 < x
  loglog_ge : 2 * Λ ≤ Real.log (Real.log x)
  α_pos : 0 < α
  γ_ge : 2 ≤ γ
  αγ_eq : α * γ = κ₀ * x ^ (1 - θ) / Real.log x ^ 3
  diff : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), DifferentiableAt ℂ ZB s
  deriv_le : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), ‖deriv ZB s‖ ≤ 4.01 * Λ ^ 2
  norm_ge : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), 1 / 2 ≤ ‖ZB s‖
  norm_le : ∀ s ∈ closedBall (1 + γ * I) (designRadius x), ‖ZB s‖ ≤ 2 * Λ

namespace Lemma46Hyp

variable {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}

section numerics

variable (h : Lemma46Hyp θ Λ κ₀ α γ x ZB)
include h

lemma L_pos : 0 < Real.log x := Real.log_pos h.one_lt_x

lemma logL_ge : 20 ≤ Real.log (Real.log x) := by linarith [h.loglog_ge, h.Λ_ge]

lemma big : 10 ^ 4 * Λ ^ 3 * Real.log (Real.log x) ≤ Real.log x :=
  large_L h.Λ_ge h.L_pos h.loglog_ge

lemma L_ge : 100 * Λ ^ 2 ≤ Real.log x := by
  have h1 := h.big; have h2 := h.logL_ge; have h3 := h.Λ_ge
  have h4 : 100 * Λ ^ 2 ≤ 10 ^ 4 * Λ ^ 3 * 20 := by nlinarith [sq_nonneg Λ]
  have h5 : 10 ^ 4 * Λ ^ 3 * 20 ≤ 10 ^ 4 * Λ ^ 3 * Real.log (Real.log x) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

lemma L_ge' : 10 ^ 4 ≤ Real.log x := by
  have := h.L_ge; have := h.Λ_ge; nlinarith

lemma δ_pos : 0 < designRadius x := by
  unfold designRadius; have := h.logL_ge; have := h.L_pos; positivity

lemma δΛ3 : designRadius x * Λ ^ 3 ≤ 9 / 10 ^ 4 := by
  unfold designRadius
  have := h.big; have := h.L_pos; have := h.logL_ge
  rw [div_mul_eq_mul_div, div_le_div_iff₀ h.L_pos (by norm_num)]
  nlinarith

lemma δΛ2 : designRadius x * Λ ^ 2 ≤ 1 / 10 ^ 4 := by
  have h1 := h.δΛ3; have h2 := h.Λ_ge; have h3 := h.δ_pos
  have : designRadius x * Λ ^ 2 * 10 ≤ designRadius x * Λ ^ 3 := by
    rw [show designRadius x * Λ ^ 3 = designRadius x * Λ ^ 2 * Λ by ring]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

lemma δ_le : designRadius x ≤ 1 / 10 ^ 6 := by
  have h1 := h.δΛ2; have h2 := h.Λ_ge; have h3 := h.δ_pos
  have : designRadius x * 100 ≤ designRadius x * Λ ^ 2 := by gcongr; nlinarith
  nlinarith

lemma log_αγ : Real.log (α * γ) =
    Real.log κ₀ + (1 - θ) * Real.log x - 3 * Real.log (Real.log x) := by
  have hκ : 0 < κ₀ := lt_of_lt_of_le (Real.exp_pos _) h.κ_ge
  have hx : 0 < x := by linarith [h.one_lt_x]
  rw [h.αγ_eq, Real.log_div (by positivity) (by have := h.L_pos; positivity),
    Real.log_mul hκ.ne' (by positivity), Real.log_rpow hx, Real.log_pow]
  push_cast; ring

end numerics

/-- `s(w) = w + θ + iγ`, inverse to `w = s - θ - iγ`. -/
noncomputable def sOf (θ γ : ℝ) (w : ℂ) : ℂ := w + θ + γ * I

/-- The centre `1 - θ` of the disc in the variable `w`. -/
noncomputable def cen (θ : ℝ) : ℂ := ((1 - θ : ℝ) : ℂ)

lemma sOf_sub (θ γ : ℝ) (w : ℂ) : sOf θ γ w - (1 + γ * I) = w - cen θ := by
  simp only [sOf, cen]; push_cast; ring

lemma sOf_sub_sOf (θ γ : ℝ) (w₁ w₂ : ℂ) : sOf θ γ w₁ - sOf θ γ w₂ = w₁ - w₂ := by
  simp only [sOf]; ring

lemma sOf_sub_theta (θ γ : ℝ) (w : ℂ) : sOf θ γ w - θ - γ * I = w := by
  simp only [sOf]; ring

lemma sOf_mem {θ γ : ℝ} {w : ℂ} {r : ℝ} (hw : w ∈ closedBall (cen θ) r) :
    sOf θ γ w ∈ closedBall (1 + γ * I) r := by
  rw [mem_closedBall, dist_eq_norm, sOf_sub]; rwa [mem_closedBall, dist_eq_norm] at hw

section disc

variable (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w : ℂ} (hw : w ∈ closedBall (cen θ) (designRadius x))
include h hw

lemma re_im_bounds : |w.re - (1 - θ)| ≤ 1 / 10 ^ 6 ∧ |w.im| ≤ 1 / 10 ^ 6 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - cen θ)
  have h2 := Complex.abs_im_le_norm (w - cen θ)
  simp only [cen, Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at h1 h2 hw
  have := h.δ_le
  exact ⟨by linarith, by linarith⟩

lemma re_nonneg : 0 ≤ w.re := by
  have := (abs_le.mp (h.re_im_bounds hw).1).1; have := h.θ_le; linarith

lemma re_le_one : w.re ≤ 1 := by
  have := (abs_le.mp (h.re_im_bounds hw).1).2; have := h.θ_ge; linarith

lemma abs_im_le_one : |w.im| ≤ 1 := by
  have := (h.re_im_bounds hw).2; linarith

lemma norm_w_ge : 1 / 4 ≤ ‖w‖ := by
  have := (abs_le.mp (h.re_im_bounds hw).1).1; have := h.θ_le
  have := Complex.re_le_norm w; linarith

lemma norm_w_le : ‖w‖ ≤ 1 := by
  have := (abs_le.mp (h.re_im_bounds hw).1).2; have := h.θ_ge
  have h2 := (h.re_im_bounds hw).2
  have := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonneg (h.re_nonneg hw)] at this; linarith

lemma w_ne_zero : w ≠ 0 := by
  intro h0; have := h.norm_w_ge hw; rw [h0, norm_zero] at this; linarith

lemma norm_phi_ge : 1 / 6 ≤ ‖phiTransform w‖ :=
  one_sixth_le_norm_phiTransform (h.re_nonneg hw) (h.re_le_one hw) (h.abs_im_le_one hw)

lemma norm_phi_le : ‖phiTransform w‖ ≤ 1 := norm_phiTransform_le (h.re_nonneg hw)

lemma phi_ne_zero : phiTransform w ≠ 0 := by
  intro h0; have := h.norm_phi_ge hw; rw [h0, norm_zero] at this; linarith

lemma norm_s_ge : γ / 2 ≤ ‖sOf θ γ w‖ := by
  have h2 := (h.re_im_bounds hw).2; have := h.γ_ge
  have h3 := Complex.abs_im_le_norm (sOf θ γ w)
  have : (sOf θ γ w).im = w.im + γ := by simp [sOf]
  rw [this] at h3
  have := (abs_le.mp h2).1
  rw [abs_of_nonneg (by linarith)] at h3; linarith

lemma norm_s_le : ‖sOf θ γ w‖ ≤ 2 * γ := by
  have h1 := (abs_le.mp (h.re_im_bounds hw).1).2
  have h2 := (abs_le.mp (h.re_im_bounds hw).2).2
  have := h.γ_ge; have := h.θ_ge; have := h.θ_le
  have h3 := Complex.norm_le_abs_re_add_abs_im (sOf θ γ w)
  have hre : (sOf θ γ w).re = w.re + θ := by simp [sOf]
  have him : (sOf θ γ w).im = w.im + γ := by simp [sOf]
  rw [hre, him] at h3
  have := (abs_le.mp (h.re_im_bounds hw).2).1
  rw [abs_of_nonneg (by linarith [h.re_nonneg hw]), abs_of_nonneg (by linarith)] at h3
  linarith

lemma s_ne_zero : sOf θ γ w ≠ 0 := by
  intro h0; have := h.norm_s_ge hw; rw [h0, norm_zero] at this; linarith [h.γ_ge]

lemma ZB_ne_zero : ZB (sOf θ γ w) ≠ 0 := by
  intro h0; have := h.norm_ge _ (sOf_mem hw); rw [h0, norm_zero] at this; linarith

end disc

lemma cen_mem (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : cen θ ∈ closedBall (cen θ) (designRadius x) :=
  mem_closedBall_self h.δ_pos.le

lemma ZB_lipschitz (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {s₁ s₂ : ℂ}
    (h₁ : s₁ ∈ closedBall (1 + γ * I) (designRadius x))
    (h₂ : s₂ ∈ closedBall (1 + γ * I) (designRadius x)) :
    ‖ZB s₁ - ZB s₂‖ ≤ 4.01 * Λ ^ 2 * ‖s₁ - s₂‖ :=
  (convex_closedBall _ _).norm_image_sub_le_of_norm_deriv_le h.diff h.deriv_le h₂ h₁

lemma sOf_cen (θ γ : ℝ) : sOf θ γ (cen θ) = 1 + γ * I := by
  simp only [sOf, cen]; push_cast; ring

lemma norm_div_sub_one {a b : ℂ} (hb : b ≠ 0) : ‖a / b - 1‖ = ‖a - b‖ / ‖b‖ := by
  rw [div_sub_one hb, norm_div]

lemma norm_div_sub_div {a₁ a₂ b : ℂ} : ‖a₁ / b - a₂ / b‖ = ‖a₁ - a₂‖ / ‖b‖ := by
  rw [← sub_div, norm_div]

/-- `G(w) = -(α s/2) Φ(w)/(w Z_B(s))`, `s = w + θ + iγ` (step 1 of the proof). -/
noncomputable def Gfun (θ α γ : ℝ) (ZB : ℂ → ℂ) (w : ℂ) : ℂ :=
  -(α * sOf θ γ w / 2) * phiTransform w / (w * ZB (sOf θ γ w))

/-- The branch of `log G` on the disc: `log G(c)` plus principal logarithms of the ratios of the
factors of `G` to their values at the centre `c = 1 - θ`. -/
noncomputable def ellFun (θ α γ : ℝ) (ZB : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.log (Gfun θ α γ ZB (cen θ)) + Complex.log (sOf θ γ w / sOf θ γ (cen θ)) +
    Complex.log (phiTransform w / phiTransform (cen θ)) - Complex.log (w / cen θ) -
    Complex.log (ZB (sOf θ γ w) / ZB (sOf θ γ (cen θ)))

section ratios

variable (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w₁ w₂ : ℂ}
  (hw₁ : w₁ ∈ closedBall (cen θ) (designRadius x)) (hw₂ : w₂ ∈ closedBall (cen θ) (designRadius x))
include h hw₁ hw₂

omit hw₁ hw₂ in
lemma us_lip : ‖sOf θ γ w₁ / sOf θ γ (cen θ) - sOf θ γ w₂ / sOf θ γ (cen θ)‖ ≤ ‖w₁ - w₂‖ := by
  rw [norm_div_sub_div, sOf_sub_sOf]
  have := h.norm_s_ge h.cen_mem; have := h.γ_ge
  exact div_le_self (norm_nonneg _) (by linarith)

lemma uphi_lip : ‖phiTransform w₁ / phiTransform (cen θ) - phiTransform w₂ / phiTransform (cen θ)‖
    ≤ 6 * ‖w₁ - w₂‖ := by
  rw [norm_div_sub_div]
  have h1 := h.norm_phi_ge h.cen_mem
  have h2 := norm_phiTransform_sub_le (h.re_nonneg hw₁) (h.re_nonneg hw₂)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (w₁ - w₂)]

omit hw₁ hw₂ in
lemma uw_lip : ‖w₁ / cen θ - w₂ / cen θ‖ ≤ 4 * ‖w₁ - w₂‖ := by
  rw [norm_div_sub_div]
  have h1 := h.norm_w_ge h.cen_mem
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (w₁ - w₂)]

lemma uZ_lip : ‖ZB (sOf θ γ w₁) / ZB (sOf θ γ (cen θ)) - ZB (sOf θ γ w₂) / ZB (sOf θ γ (cen θ))‖
    ≤ 8.02 * Λ ^ 2 * ‖w₁ - w₂‖ := by
  rw [norm_div_sub_div]
  have h1 := h.norm_ge _ (sOf_mem h.cen_mem)
  have h2 := h.ZB_lipschitz (sOf_mem hw₁) (sOf_mem hw₂)
  rw [sOf_sub_sOf] at h2
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (w₁ - w₂), sq_nonneg Λ, mul_nonneg (sq_nonneg Λ) (norm_nonneg (w₁ - w₂))]

end ratios

section ell

variable (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w : ℂ}
  (hw : w ∈ closedBall (cen θ) (designRadius x))
include h hw

omit h in
lemma dist_cen_le : ‖w - cen θ‖ ≤ designRadius x := by
  rwa [mem_closedBall, dist_eq_norm] at hw

lemma us_close : ‖sOf θ γ w / sOf θ γ (cen θ) - 1‖ ≤ designRadius x := by
  have := h.us_lip (w₁ := w) (w₂ := cen θ)
  rw [div_self (h.s_ne_zero h.cen_mem)] at this
  exact this.trans (dist_cen_le hw)

lemma uphi_close : ‖phiTransform w / phiTransform (cen θ) - 1‖ ≤ 6 * designRadius x := by
  have := h.uphi_lip hw h.cen_mem
  rw [div_self (h.phi_ne_zero h.cen_mem)] at this
  exact this.trans (by linarith [dist_cen_le hw])

lemma uw_close : ‖w / cen θ - 1‖ ≤ 4 * designRadius x := by
  have := h.uw_lip (w₁ := w) (w₂ := cen θ)
  rw [div_self (h.w_ne_zero h.cen_mem)] at this
  exact this.trans (by linarith [dist_cen_le hw])

lemma uZ_close : ‖ZB (sOf θ γ w) / ZB (sOf θ γ (cen θ)) - 1‖ ≤ 8.02 * Λ ^ 2 * designRadius x := by
  have := h.uZ_lip hw h.cen_mem
  rw [div_self (h.ZB_ne_zero h.cen_mem)] at this
  exact this.trans (mul_le_mul_of_nonneg_left (dist_cen_le hw) (by positivity))

lemma G_ne_zero : Gfun θ α γ ZB w ≠ 0 := by
  unfold Gfun
  have := h.α_pos
  have := h.s_ne_zero hw; have := h.phi_ne_zero hw; have := h.w_ne_zero hw
  have := h.ZB_ne_zero hw
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast h.α_pos.ne'
  field_simp
  simp_all

lemma exp_ell : Complex.exp (ellFun θ α γ ZB w) = Gfun θ α γ ZB w := by
  have hc := h.cen_mem
  have hn : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / 10 → z ≠ 0 := fun z hz h0 => by
    rw [h0, zero_sub, norm_neg, norm_one] at hz; linarith
  have hδ := h.δ_le; have hδ2 := h.δΛ2
  have e1 := hn _ ((h.us_close hw).trans (by linarith))
  have e2 := hn _ ((h.uphi_close hw).trans (by linarith))
  have e3 := hn _ ((h.uw_close hw).trans (by linarith))
  have e4 := hn _ ((h.uZ_close hw).trans (by nlinarith))
  unfold ellFun
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_log e1,
    Complex.exp_log e2, Complex.exp_log e3, Complex.exp_log e4,
    Complex.exp_log (h.G_ne_zero hc)]
  have := h.s_ne_zero hw; have := h.phi_ne_zero hw; have := h.w_ne_zero hw
  have := h.ZB_ne_zero hw
  have := h.s_ne_zero hc; have := h.phi_ne_zero hc; have := h.w_ne_zero hc
  have := h.ZB_ne_zero hc
  unfold Gfun
  field_simp

lemma ell_re : (ellFun θ α γ ZB w).re = Real.log ‖Gfun θ α γ ZB w‖ := by
  rw [← h.exp_ell hw, Complex.norm_exp, Real.log_exp]

lemma ell_im : |(ellFun θ α γ ZB w).im| ≤ 4 := by
  have hδ := h.δ_le; have hδ2 := h.δΛ2
  have hl : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / 100 → |(Complex.log z).im| ≤ 3 / 200 := fun z hz => by
    have h1 := Complex.norm_log_one_add_half_le_self (z := z - 1) (by linarith)
    rw [add_sub_cancel] at h1
    exact (Complex.abs_im_le_norm _).trans (by linarith)
  have e1 := hl _ ((h.us_close hw).trans (by linarith))
  have e2 := hl _ ((h.uphi_close hw).trans (by linarith))
  have e3 := hl _ ((h.uw_close hw).trans (by linarith))
  have e4 := hl _ ((h.uZ_close hw).trans (by nlinarith))
  have e0 : |(Complex.log (Gfun θ α γ ZB (cen θ))).im| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
  unfold ellFun
  simp only [Complex.sub_im, Complex.add_im]
  have := Real.pi_lt_d2
  rw [abs_le] at e0 e1 e2 e3 e4 ⊢
  constructor <;> linarith

omit hw in
lemma norm_G : ‖Gfun θ α γ ZB w‖ =
    α * ‖sOf θ γ w‖ * ‖phiTransform w‖ / (2 * ‖w‖ * ‖ZB (sOf θ γ w)‖) := by
  unfold Gfun
  rw [norm_div, norm_mul, norm_neg, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos h.α_pos]
  simp only [Complex.norm_ofNat]
  ring

lemma logG_ge : Real.log κ₀ + (1 - θ) * Real.log x - 3 * Real.log (Real.log x) -
    Real.log (48 * Λ) ≤ Real.log ‖Gfun θ α γ ZB w‖ := by
  have hαγ : 0 < α * γ := mul_pos h.α_pos (by linarith [h.γ_ge])
  have hΛ := h.Λ_ge
  have hs := h.norm_s_ge hw; have hp := h.norm_phi_ge hw; have hw1 := h.norm_w_le hw
  have hw0 := h.norm_w_ge hw
  have hZ := h.norm_le _ (sOf_mem hw); have hZ0 := h.norm_ge _ (sOf_mem hw)
  have hlow : α * γ / (48 * Λ) ≤ ‖Gfun θ α γ ZB w‖ := by
    rw [h.norm_G (w := w), div_le_div_iff₀ (by positivity) (by positivity)]
    have hα := h.α_pos
    have e1 : α * γ ≤ 2 * (α * ‖sOf θ γ w‖) := by nlinarith
    have e2 : 2 * ‖w‖ * ‖ZB (sOf θ γ w)‖ ≤ 4 * Λ := by nlinarith
    have e3 : 0 ≤ α * ‖sOf θ γ w‖ := by positivity
    have e4 : α * ‖sOf θ γ w‖ * (8 * Λ) ≤ α * ‖sOf θ γ w‖ * ‖phiTransform w‖ * (48 * Λ) := by
      nlinarith [mul_nonneg (mul_nonneg e3 (show (0:ℝ) ≤ Λ by linarith))
        (show (0:ℝ) ≤ 48 * ‖phiTransform w‖ - 8 by linarith)]
    nlinarith [mul_le_mul e1 e2 (by positivity) (by positivity)]
  rw [← h.log_αγ, ← Real.log_div hαγ.ne' (by positivity)]
  exact Real.log_le_log (by positivity) hlow

lemma logG_le : Real.log ‖Gfun θ α γ ZB w‖ ≤ Real.log κ₀ + (1 - θ) * Real.log x -
    3 * Real.log (Real.log x) + Real.log 8 := by
  have hαγ : 0 < α * γ := mul_pos h.α_pos (by linarith [h.γ_ge])
  have hs := h.norm_s_le hw; have hp := h.norm_phi_le hw
  have hw0 := h.norm_w_ge hw
  have hZ0 := h.norm_ge _ (sOf_mem hw)
  have hup : ‖Gfun θ α γ ZB w‖ ≤ α * γ * 8 := by
    rw [h.norm_G (w := w), div_le_iff₀ (by positivity)]
    have hα := h.α_pos
    have := h.γ_ge
    have e1 : α * ‖sOf θ γ w‖ * ‖phiTransform w‖ ≤ α * (2 * γ) * 1 := by
      gcongr
    have e2 : (1 / 4 : ℝ) ≤ 2 * ‖w‖ * ‖ZB (sOf θ γ w)‖ := by nlinarith
    nlinarith
  rw [← h.log_αγ, ← Real.log_mul hαγ.ne' (by norm_num)]
  exact Real.log_le_log (G_ne_zero h hw |> norm_pos_iff.mpr) hup

end ell

lemma ell_lip (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ closedBall (cen θ) (designRadius x))
    (hw₂ : w₂ ∈ closedBall (cen θ) (designRadius x)) :
    ‖ellFun θ α γ ZB w₁ - ellFun θ α γ ZB w₂‖ ≤ 17 * Λ ^ 2 * ‖w₁ - w₂‖ := by
  have hδ := h.δ_le; have hδ2 := h.δΛ2
  have hl : ∀ z₁ z₂ : ℂ, ‖z₁ - 1‖ ≤ 1 / 100 → ‖z₂ - 1‖ ≤ 1 / 100 →
      ‖Complex.log z₁ - Complex.log z₂‖ ≤ 2 * ‖z₁ - z₂‖ := fun z₁ z₂ h₁ h₂ =>
    norm_log_sub_log_le (by linarith) (by linarith)
  have e1 := hl _ _ ((h.us_close hw₁).trans (by linarith)) ((h.us_close hw₂).trans (by linarith))
  have e2 := hl _ _ ((h.uphi_close hw₁).trans (by linarith))
    ((h.uphi_close hw₂).trans (by linarith))
  have e3 := hl _ _ ((h.uw_close hw₁).trans (by linarith)) ((h.uw_close hw₂).trans (by linarith))
  have e4 := hl _ _ ((h.uZ_close hw₁).trans (by nlinarith)) ((h.uZ_close hw₂).trans (by nlinarith))
  have l1 := h.us_lip (w₁ := w₁) (w₂ := w₂)
  have l2 := h.uphi_lip hw₁ hw₂
  have l3 := h.uw_lip (w₁ := w₁) (w₂ := w₂)
  have l4 := h.uZ_lip hw₁ hw₂
  have hsplit : ellFun θ α γ ZB w₁ - ellFun θ α γ ZB w₂ =
      (Complex.log (sOf θ γ w₁ / sOf θ γ (cen θ)) - Complex.log (sOf θ γ w₂ / sOf θ γ (cen θ))) +
      (Complex.log (phiTransform w₁ / phiTransform (cen θ)) -
        Complex.log (phiTransform w₂ / phiTransform (cen θ))) -
      (Complex.log (w₁ / cen θ) - Complex.log (w₂ / cen θ)) -
      (Complex.log (ZB (sOf θ γ w₁) / ZB (sOf θ γ (cen θ))) -
        Complex.log (ZB (sOf θ γ w₂) / ZB (sOf θ γ (cen θ)))) := by
    unfold ellFun; ring
  rw [hsplit]
  have hΛ := h.Λ_ge
  have hn := norm_nonneg (w₁ - w₂)
  calc _ ≤ ‖Complex.log (sOf θ γ w₁ / sOf θ γ (cen θ)) -
          Complex.log (sOf θ γ w₂ / sOf θ γ (cen θ))‖ +
        ‖Complex.log (phiTransform w₁ / phiTransform (cen θ)) -
          Complex.log (phiTransform w₂ / phiTransform (cen θ))‖ +
        ‖Complex.log (w₁ / cen θ) - Complex.log (w₂ / cen θ)‖ +
        ‖Complex.log (ZB (sOf θ γ w₁) / ZB (sOf θ γ (cen θ))) -
          Complex.log (ZB (sOf θ γ w₂) / ZB (sOf θ γ (cen θ)))‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ 2 * ‖w₁ - w₂‖ + 2 * (6 * ‖w₁ - w₂‖) + 2 * (4 * ‖w₁ - w₂‖) +
        2 * (8.02 * Λ ^ 2 * ‖w₁ - w₂‖) := by
        gcongr
        · exact e1.trans (by linarith)
        · exact e2.trans (by linarith)
        · exact e3.trans (by linarith)
        · exact e4.trans (by linarith)
    _ ≤ 17 * Λ ^ 2 * ‖w₁ - w₂‖ := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ 0.96 * Λ ^ 2 - 22 by nlinarith) hn]

lemma log_κ_ge (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : -Λ ≤ Real.log κ₀ := by
  have := Real.log_le_log (Real.exp_pos _) h.κ_ge
  rwa [Real.log_exp] at this

lemma log_κ_le (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : Real.log κ₀ ≤ 0 :=
  Real.log_nonpos (lt_of_lt_of_le (Real.exp_pos _) h.κ_ge).le (by linarith [h.κ_le])

lemma log_48Λ_le (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : Real.log (48 * Λ) ≤ Λ + 3 := by
  have hΛ := h.Λ_ge
  rw [Real.log_mul (by norm_num) (by linarith)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Λ by linarith)
  have h2 : Real.log 48 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
    rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
  linarith

lemma log_8_le : Real.log 8 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
  rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith

/-- The fixed-point map `F(w) = log G(w) / log x_k` of step 3. -/
noncomputable def Ffun (θ α γ x : ℝ) (ZB : ℂ → ℂ) (w : ℂ) : ℂ :=
  ellFun θ α γ ZB w / (Real.log x : ℂ)

lemma Ffun_re (θ α γ x : ℝ) (ZB : ℂ → ℂ) (w : ℂ) :
    (Ffun θ α γ x ZB w).re = (ellFun θ α γ ZB w).re / Real.log x := by
  simp [Ffun, Complex.div_ofReal_re]

lemma Ffun_im (θ α γ x : ℝ) (ZB : ℂ → ℂ) (w : ℂ) :
    (Ffun θ α γ x ZB w).im = (ellFun θ α γ ZB w).im / Real.log x := by
  simp [Ffun, Complex.div_ofReal_im]

/-- Steps 2 and 6: `F` maps the disc into the smaller disc of radius `δ_k - 1/log x_k`. -/
lemma Ffun_sub_cen (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w : ℂ}
    (hw : w ∈ closedBall (cen θ) (designRadius x)) :
    ‖Ffun θ α γ x ZB w - cen θ‖ ≤ designRadius x - 1 / Real.log x := by
  have hL := h.L_pos
  have hre : (Ffun θ α γ x ZB w - cen θ).re =
      (Real.log ‖Gfun θ α γ ZB w‖ - (1 - θ) * Real.log x) / Real.log x := by
    rw [Complex.sub_re, Ffun_re, h.ell_re hw]
    simp only [cen, Complex.ofReal_re]
    field_simp
  have him : (Ffun θ α γ x ZB w - cen θ).im = (ellFun θ α γ ZB w).im / Real.log x := by
    rw [Complex.sub_im, Ffun_im]; simp [cen]
  have h1 := h.logG_ge hw; have h2 := h.logG_le hw
  have h3 := h.log_κ_ge; have h4 := h.log_κ_le; have h5 := h.log_48Λ_le; have h6 := log_8_le
  have h7 := h.ell_im hw
  have hLL := h.loglog_ge; have hΛ := h.Λ_ge
  have hRe : |Real.log ‖Gfun θ α γ ZB w‖ - (1 - θ) * Real.log x| ≤
      3 * Real.log (Real.log x) + 2 * Λ + 3 := by
    rw [abs_le]; constructor <;> linarith
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him, abs_div, abs_div, abs_of_pos hL, ← add_div]
  unfold designRadius
  rw [div_sub_div_same, div_le_div_iff_of_pos_right hL]
  linarith

lemma Ffun_lip (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ closedBall (cen θ) (designRadius x))
    (hw₂ : w₂ ∈ closedBall (cen θ) (designRadius x)) :
    ‖Ffun θ α γ x ZB w₁ - Ffun θ α γ x ZB w₂‖ ≤ 17 * Λ ^ 2 / Real.log x * ‖w₁ - w₂‖ := by
  have hL := h.L_pos
  unfold Ffun
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hL]
  exact h.ell_lip hw₁ hw₂

/-- Step 1: at a fixed point `w₀ = F(w₀)`, `s₀ = w₀ + θ + iγ` is a zero of `Z_B + M_k`. -/
lemma Mk_at_fixedPoint (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w₀ : ℂ}
    (hw₀ : w₀ ∈ closedBall (cen θ) (designRadius x)) (hfix : Ffun θ α γ x ZB w₀ = w₀) :
    ZB (sOf θ γ w₀) + Mk θ α γ x (sOf θ γ w₀) = 0 := by
  have hL := h.L_pos
  have hx : 0 < x := by linarith [h.one_lt_x]
  have hℓ : ellFun θ α γ ZB w₀ = Real.log x * w₀ := by
    unfold Ffun at hfix
    have hL' : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp at hfix; rw [← hfix]
  have hpow : (x : ℂ) ^ (-w₀) = (Gfun θ α γ ZB w₀)⁻¹ := by
    rw [Oscillation.ofReal_cpow_eq_exp hx, mul_neg, ← hℓ, Complex.exp_neg, h.exp_ell hw₀]
  unfold Mk
  rw [sOf_sub_theta, hpow]
  have := h.s_ne_zero hw₀; have := h.phi_ne_zero hw₀; have := h.w_ne_zero hw₀
  have := h.ZB_ne_zero hw₀
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast h.α_pos.ne'
  unfold Gfun
  field_simp
  ring

/-- Steps 4–5: if `s₀ = s(w₀)` is a zero of `Z_B + M_k` and the circle `|s - s₀| = 1/log x_k`
lies in the disc, then `|Z_B + M_k| ≥ 1/4` on that circle. -/
lemma circle_bound (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {w₀ : ℂ}
    (hw₀ : ‖w₀ - cen θ‖ + 1 / Real.log x ≤ designRadius x)
    (hz : ZB (sOf θ γ w₀) + Mk θ α γ x (sOf θ γ w₀) = 0) :
    ∀ s ∈ sphere (sOf θ γ w₀) (1 / Real.log x), 1 / 4 ≤ ‖ZB s + Mk θ α γ x s‖ := by
  intro s hs
  have hL := h.L_pos
  have hL4 := h.L_ge'
  have hLΛ := h.L_ge
  have hx : 0 < x := by linarith [h.one_lt_x]
  set w := s - θ - γ * I with hwdef
  have hsw : s = sOf θ γ w := by simp only [hwdef, sOf]; ring
  rw [hsw] at hs ⊢
  have hww : ‖w - w₀‖ = 1 / Real.log x := by
    rw [mem_sphere, dist_eq_norm, sOf_sub_sOf] at hs; exact hs
  have hw0m : w₀ ∈ closedBall (cen θ) (designRadius x) := by
    rw [mem_closedBall, dist_eq_norm]; have : 0 < 1 / Real.log x := by positivity
    linarith
  have hwm : w ∈ closedBall (cen θ) (designRadius x) := by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖w - cen θ‖ = ‖(w - w₀) + (w₀ - cen θ)‖ := by ring_nf
      _ ≤ ‖w - w₀‖ + ‖w₀ - cen θ‖ := norm_add_le _ _
      _ ≤ designRadius x := by linarith
  set ξ : ℂ := (Real.log x : ℂ) * (w - w₀) with hξ
  have hξn : ‖ξ‖ = 1 := by
    rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, hww]; field_simp
  set u : ℂ → ℂ := fun v => sOf θ γ v * phiTransform v / v with hu
  have hMk : ∀ v, Mk θ α γ x (sOf θ γ v) = α / 2 * (x : ℂ) ^ (-v) * u v := by
    intro v; simp only [Mk, sOf_sub_theta, hu]; ring
  have hpow : (x : ℂ) ^ (-w) = (x : ℂ) ^ (-w₀) * Complex.exp (-ξ) := by
    rw [Oscillation.ofReal_cpow_eq_exp hx, Oscillation.ofReal_cpow_eq_exp hx, ← Complex.exp_add]
    congr 1; rw [hξ]; ring
  have hu0 : u w₀ ≠ 0 := by
    simp only [hu]
    exact div_ne_zero (mul_ne_zero (h.s_ne_zero hw0m) (h.phi_ne_zero hw0m)) (h.w_ne_zero hw0m)
  have hA : α / 2 * (x : ℂ) ^ (-w₀) * u w₀ = -ZB (sOf θ γ w₀) := by
    rw [← hMk]; linear_combination hz
  have hkey : ZB (sOf θ γ w) + Mk θ α γ x (sOf θ γ w) =
      ZB (sOf θ γ w₀) * (1 - Complex.exp (-ξ)) + (ZB (sOf θ γ w) - ZB (sOf θ γ w₀)) -
        ZB (sOf θ γ w₀) * Complex.exp (-ξ) * (u w / u w₀ - 1) := by
    rw [hMk, hpow]
    have : α / 2 * ((x : ℂ) ^ (-w₀) * Complex.exp (-ξ)) * u w =
        (α / 2 * (x : ℂ) ^ (-w₀) * u w₀) * Complex.exp (-ξ) * (u w / u w₀) := by
      field_simp
    rw [this, hA]; ring
  -- the three estimates
  have hZ0 := h.norm_ge _ (sOf_mem hw0m)
  have hexp : ‖1 - Complex.exp (-ξ)‖ ≥ 3 / 5 := norm_one_sub_exp_neg_ge hξn
  have hdZ : ‖ZB (sOf θ γ w) - ZB (sOf θ γ w₀)‖ ≤ 4.01 * Λ ^ 2 / Real.log x := by
    have := h.ZB_lipschitz (sOf_mem hwm) (sOf_mem hw0m)
    rw [sOf_sub_sOf, hww] at this; rw [mul_one_div] at this; exact this
  have hexpn : ‖Complex.exp (-ξ)‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have : -1 ≤ (-ξ).re := by
      have := Complex.abs_re_le_norm ξ; rw [hξn] at this
      simp; linarith [(abs_le.mp this).2]
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc Real.exp (-ξ).re ≤ Real.exp 1 := by
          rw [Real.exp_le_exp]; have := Complex.abs_re_le_norm ξ; rw [hξn] at this
          simp; linarith [(abs_le.mp this).1]
      _ ≤ 3 := h3
  have hratio : ‖u w / u w₀ - 1‖ ≤ 42 / Real.log x := by
    have e : u w / u w₀ = (sOf θ γ w / sOf θ γ w₀) * (phiTransform w / phiTransform w₀) *
        (w₀ / w) := by
      simp only [hu]
      have := h.s_ne_zero hw0m; have := h.phi_ne_zero hw0m; have := h.w_ne_zero hw0m
      have := h.w_ne_zero hwm
      field_simp
    rw [e]
    have hε : 6 / Real.log x ≤ 1 := by rw [div_le_one hL]; linarith
    have h1 : ‖sOf θ γ w / sOf θ γ w₀ - 1‖ ≤ 6 / Real.log x := by
      rw [norm_div_sub_one (h.s_ne_zero hw0m), sOf_sub_sOf, hww]
      have := h.norm_s_ge hw0m; have := h.γ_ge
      rw [div_le_iff₀ (by linarith)]
      have : 1 / Real.log x ≤ 6 / Real.log x * 1 := by
        rw [mul_one]; exact div_le_div_of_nonneg_right (by norm_num) hL.le
      calc 1 / Real.log x ≤ 6 / Real.log x * 1 := this
        _ ≤ 6 / Real.log x * ‖sOf θ γ w₀‖ := by gcongr; linarith
    have h2 : ‖phiTransform w / phiTransform w₀ - 1‖ ≤ 6 / Real.log x := by
      rw [norm_div_sub_one (h.phi_ne_zero hw0m)]
      have := norm_phiTransform_sub_le (h.re_nonneg hwm) (h.re_nonneg hw0m)
      rw [hww] at this
      have := h.norm_phi_ge hw0m
      rw [div_le_iff₀ (by linarith)]
      calc _ ≤ 1 / Real.log x := by assumption
        _ = 6 / Real.log x * (1 / 6) := by ring
        _ ≤ 6 / Real.log x * ‖phiTransform w₀‖ := by gcongr
    have h3 : ‖w₀ / w - 1‖ ≤ 6 / Real.log x := by
      rw [norm_div_sub_one (h.w_ne_zero hwm), norm_sub_rev, hww]
      have := h.norm_w_ge hwm
      rw [div_le_iff₀ (by linarith)]
      calc 1 / Real.log x = 6 / Real.log x * (1 / 6) := by ring
        _ ≤ 6 / Real.log x * ‖w‖ := by gcongr; linarith
    exact (norm_mul3_sub_one_le hε h1 h2 h3).trans (le_of_eq (by ring))
  rw [hkey]
  set Z0 := ZB (sOf θ γ w₀)
  have hfinal : ‖Z0 * (1 - Complex.exp (-ξ))‖ - ‖ZB (sOf θ γ w) - Z0‖ -
      ‖Z0 * Complex.exp (-ξ) * (u w / u w₀ - 1)‖ ≤
      ‖Z0 * (1 - Complex.exp (-ξ)) + (ZB (sOf θ γ w) - Z0) -
        Z0 * Complex.exp (-ξ) * (u w / u w₀ - 1)‖ := by
    have a1 := norm_sub_norm_le (Z0 * (1 - Complex.exp (-ξ)) + (ZB (sOf θ γ w) - Z0))
      (Z0 * Complex.exp (-ξ) * (u w / u w₀ - 1))
    have a2 := norm_add_le (Z0 * (1 - Complex.exp (-ξ)) + (ZB (sOf θ γ w) - Z0))
      (-(ZB (sOf θ γ w) - Z0))
    simp only [add_neg_cancel_right, norm_neg] at a2
    linarith
  rw [norm_mul, norm_mul, norm_mul] at hfinal
  have hr0 : 0 ≤ ‖u w / u w₀ - 1‖ := norm_nonneg _
  have hq : ‖Complex.exp (-ξ)‖ * ‖u w / u w₀ - 1‖ ≤ 3 * (42 / Real.log x) :=
    mul_le_mul hexpn hratio hr0 (by norm_num)
  have h126 : 3 * (42 / Real.log x) ≤ 126 / 10 ^ 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hL (by norm_num)]; linarith
  have hΛL : 4.01 * Λ ^ 2 / Real.log x ≤ 4.01 / 100 := by
    rw [div_le_div_iff₀ hL (by norm_num)]; linarith
  have hZ0n : 0 ≤ ‖Z0‖ := norm_nonneg _
  have : ‖Z0‖ * ‖Complex.exp (-ξ)‖ * ‖u w / u w₀ - 1‖ ≤ ‖Z0‖ * (126 / 10 ^ 4) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hq.trans h126) hZ0n
  have : ‖Z0‖ * (3 / 5) ≤ ‖Z0‖ * ‖1 - Complex.exp (-ξ)‖ := mul_le_mul_of_nonneg_left hexp hZ0n
  nlinarith

end Lemma46Hyp

open Lemma46Hyp in
/-- **Lemma 4.6 (A designed zero).** Under the hypotheses `Lemma46Hyp` (in particular
`1/2 ≤ |Z_B| ≤ Z_max = 2Λ` on the disc `|s - (1 + iγ_k)| ≤ δ_k = 9 log log x_k / log x_k`),
`Z_B + M_k` has a zero `s*` with
`Re s* = 1 - (3 log log x_k + O_{X₀}(1)) / log x_k` (explicitly `|O_{X₀}(1)| ≤ 2Λ + 4`),
the circle `|s - s*| = 1/log x_k` lies in the disc, and `|Z_B + M_k| ≥ 1/4` on it. -/
theorem lemma_4_6 {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ} (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) :
    ∃ s₀ : ℂ, ZB s₀ + Mk θ α γ x s₀ = 0 ∧
      ‖s₀ - (1 + γ * I)‖ + 1 / Real.log x ≤ designRadius x ∧
      |(1 - s₀.re) * Real.log x - 3 * Real.log (Real.log x)| ≤ 2 * Λ + 4 ∧
      ∀ s ∈ sphere s₀ (1 / Real.log x), 1 / 4 ≤ ‖ZB s + Mk θ α γ x s‖ := by
  have hL := h.L_pos
  have hq : 17 * Λ ^ 2 / Real.log x < 1 := by
    rw [div_lt_one hL]; have := h.L_ge; have := h.Λ_ge; nlinarith
  obtain ⟨w₀, hw₀, hfix⟩ := exists_fixedPoint_closedBall (F := Ffun θ α γ x ZB)
    h.δ_pos.le (by positivity) hq
    (fun w hw => by
      rw [mem_closedBall, dist_eq_norm]
      have : 0 < 1 / Real.log x := by positivity
      linarith [h.Ffun_sub_cen hw])
    (fun w₁ hw₁ w₂ hw₂ => h.Ffun_lip hw₁ hw₂)
  have hz := h.Mk_at_fixedPoint hw₀ hfix
  have hD : ‖w₀ - cen θ‖ + 1 / Real.log x ≤ designRadius x := by
    have := h.Ffun_sub_cen hw₀; rw [hfix] at this; linarith
  refine ⟨sOf θ γ w₀, hz, by rw [sOf_sub]; exact hD, ?_, h.circle_bound hD hz⟩
  -- the real part
  have hre : (sOf θ γ w₀).re = θ + Real.log ‖Gfun θ α γ ZB w₀‖ / Real.log x := by
    have e1 : (sOf θ γ w₀).re = w₀.re + θ := by simp [sOf]
    have e2 : w₀.re = Real.log ‖Gfun θ α γ ZB w₀‖ / Real.log x := by
      conv_lhs => rw [← hfix]
      rw [Ffun_re, h.ell_re hw₀]
    rw [e1, e2]; ring
  have e : (1 - (sOf θ γ w₀).re) * Real.log x - 3 * Real.log (Real.log x) =
      (1 - θ) * Real.log x - Real.log ‖Gfun θ α γ ZB w₀‖ - 3 * Real.log (Real.log x) := by
    rw [hre]; field_simp; ring
  rw [e]
  have h1 := h.logG_ge hw₀; have h2 := h.logG_le hw₀
  have h3 := h.log_κ_ge; have h4 := h.log_κ_le; have h5 := h.log_48Λ_le; have h6 := log_8_le
  have h7 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have := h.Λ_ge
  rw [abs_le]; constructor <;> linarith

end DesignedZero

end
