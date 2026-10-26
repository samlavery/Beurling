module

public import RequestProject.Beurling.DesignedZero

/-!
# Lemma 4.7 (Late noise)

The transform `D̂_{≥a}(s) = ∫_{(a,∞)} x^{-s} dD` of the noise beyond `a`, written by partial
summation as `s ∫_a^∞ D(x) x^{-s-1} dx - D(a) a^{-s}`, is small on the Rouché circle of
Lemma 4.6, given the lag bound `|D(x)| ≤ x^η` (13) beyond `a`.
-/

@[expose] public section

open Complex Metric Set Filter MeasureTheory SmoothStep

namespace DesignedZero

/-- `D̂_{≥a}(s) = ∫_{(a,∞)} x^{-s} dD = s ∫_a^∞ D(x) x^{-s-1} dx - D(a) a^{-s}` (partial
summation, for `D(x) x^{-s} → 0`). -/
noncomputable def lateNoise (D : ℝ → ℝ) (a : ℝ) (s : ℂ) : ℂ :=
  s * (∫ x in Ioi a, (D x : ℂ) * (x : ℂ) ^ (-s - 1)) - (D a : ℂ) * (a : ℂ) ^ (-s)

/-- The by-parts estimate `|D̂_{≥a}(s)| ≤ a^{η-σ} (1 + |s|/(σ - η))`. -/
lemma norm_lateNoise_le {D : ℝ → ℝ} {η a : ℝ} (ha : 0 < a) (hD : ∀ y ≥ a, |D y| ≤ y ^ η)
    {s : ℂ} (hs : η < s.re) :
    ‖lateNoise D a s‖ ≤ a ^ (η - s.re) * (1 + ‖s‖ / (s.re - η)) := by
  unfold lateNoise
  have h1 := Oscillation.norm_tail_mellin_le ha (fun y hy => hD y hy.le) hs
  have h2 : ‖(D a : ℂ) * (a : ℂ) ^ (-s)‖ ≤ a ^ (η - s.re) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ha,
      Complex.neg_re, sub_eq_add_neg, Real.rpow_add ha]
    exact mul_le_mul_of_nonneg_right (hD a le_rfl) (Real.rpow_nonneg ha.le _)
  calc _ ≤ ‖s * ∫ x in Ioi a, (D x : ℂ) * (x : ℂ) ^ (-s - 1)‖ +
        ‖(D a : ℂ) * (a : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ ‖s‖ * a ^ (η - s.re) / (s.re - η) + a ^ (η - s.re) := add_le_add h1 h2
    _ = a ^ (η - s.re) * (1 + ‖s‖ / (s.re - η)) := by ring

/-- `e^{-1} cos 1 ≥ e^{-1}/2`, so `|Φ(w)| ≥ e^{-1}/2` on the box `0 ≤ Re w ≤ 1`, `|Im w| ≤ 1`. -/
lemma half_exp_neg_one_le_norm_phiTransform {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1)
    (him : |w.im| ≤ 1) : Real.exp (-1) / 2 ≤ ‖phiTransform w‖ := by
  have h := re_phiTransform_ge h0 h1 him
  have hc : (1/2 : ℝ) ≤ Real.cos 1 := by
    have := Real.one_sub_sq_div_two_le_cos (x := 1); norm_num at this; linarith
  have := Complex.re_le_norm (phiTransform w)
  have := Real.exp_pos (-1)
  nlinarith

lemma alg_aux (c e Λ X α S T : ℝ) (hα : α ≠ 0) (hS : S ≠ 0) :
    c * (e * (X * (8 * e * Λ / (α * S)))) * T = c * 8 * (e * e) * Λ * X / α * (T / S) := by
  field_simp

lemma exp_one_mul_exp_one_le : Real.exp 1 * Real.exp 1 ≤ 7.39 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  nlinarith

namespace Lemma46Hyp

variable {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.7 (Late noise).** On the Rouché circle `|s - s*| = 1/log x_k` of Lemma 4.6, if
`α_k ≥ 1`, `η ≤ θ/2`, `a_k ≤ x_k ≤ (1 + 10⁻³) a_k`, and `|D(y)| ≤ y^η` for `y ≥ a_k` (the lag
bound (13)), then `|D̂_{≥a_k}(s)| ≤ 150 Λ x_k^{η-θ}/α_k ≤ 165 Λ x_k^{-1/8}`. -/
theorem lemma_4_7 (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) (hα : 1 ≤ α) {D : ℝ → ℝ} {η a : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ θ / 2) (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ (1 + 1 / 1000) * a)
    (hD : ∀ y ≥ a, |D y| ≤ y ^ η) {s₀ : ℂ} (hz : ZB s₀ + Mk θ α γ x s₀ = 0)
    (hs₀ : ‖s₀ - (1 + γ * I)‖ + 1 / Real.log x ≤ designRadius x) :
    ∀ s ∈ sphere s₀ (1 / Real.log x),
      ‖lateNoise D a s‖ ≤ 150 * Λ * x ^ (η - θ) / α ∧
      ‖lateNoise D a s‖ ≤ 165 * Λ * x ^ (-(1 / 8 : ℝ)) := by
  intro s hs
  have hL := h.L_pos
  have hL4 := h.L_ge'
  have hx0 : 0 < x := by linarith [h.one_lt_x]
  have hΛ := h.Λ_ge
  have hθ1 := h.θ_ge; have hθ2 := h.θ_le
  have hδ := h.δ_le
  set w₀ := s₀ - θ - γ * I with hw₀def
  have hs₀w : s₀ = sOf θ γ w₀ := by simp only [hw₀def, sOf]; ring
  have hw₀ : w₀ ∈ closedBall (cen θ) (designRadius x) := by
    rw [mem_closedBall, dist_eq_norm, ← sOf_sub θ γ, ← hs₀w]
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have hss : ‖s - s₀‖ = 1 / Real.log x := by rwa [mem_sphere, dist_eq_norm] at hs
  have hinvL : 1 / Real.log x ≤ 1 / 10 ^ 4 := by
    rw [div_le_div_iff₀ hL (by norm_num)]; linarith
  -- real parts
  have hre0 : |s₀.re - 1| ≤ 1 / 10 ^ 6 := by
    have := Complex.abs_re_le_norm (s₀ - (1 + γ * I)); simp at this
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have hreS : |s.re - s₀.re| ≤ 1 / Real.log x := by
    have := Complex.abs_re_le_norm (s - s₀); rw [Complex.sub_re] at this; linarith
  have hσ1 : 99 / 100 ≤ s.re := by
    have := (abs_le.mp hre0).1; have := (abs_le.mp hreS).1; linarith
  have hσ2 : s.re ≤ 101 / 100 := by
    have := (abs_le.mp hre0).2; have := (abs_le.mp hreS).2; linarith
  have hηs : η < s.re := by linarith
  -- norms of s, s₀
  have hs0n : 1 ≤ ‖s₀‖ := by
    have := h.norm_s_ge hw₀; rw [← hs₀w] at this; have := h.γ_ge; linarith
  have hsn : ‖s‖ ≤ ‖s₀‖ + 1 / Real.log x := by
    have := norm_le_norm_add_norm_sub' s s₀; rw [hss] at this; linarith
  -- step A–B
  have hA := norm_lateNoise_le ha hD hηs
  have hB : 1 + ‖s‖ / (s.re - η) ≤ 1 + 1.36 * ‖s‖ := by
    have : ‖s‖ / (s.re - η) ≤ 1.36 * ‖s‖ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg s]
    linarith
  -- step C: a^{η-σ} ≤ 1.0021 x^{η-σ}
  have hC : a ^ (η - s.re) ≤ 1.0021 * x ^ (η - s.re) := by
    have hxa1 : 1 ≤ x / a := by rw [le_div_iff₀ ha]; linarith
    have e : a ^ (η - s.re) = x ^ (η - s.re) * (x / a) ^ (s.re - η) := by
      rw [Real.div_rpow hx0.le ha.le, mul_div_assoc', ← Real.rpow_add hx0,
        show η - s.re + (s.re - η) = 0 by ring, Real.rpow_zero, one_div, ← Real.rpow_neg ha.le,
        neg_sub]
    rw [e, mul_comm (1.0021 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx0.le _)
    calc (x / a) ^ (s.re - η) ≤ (x / a) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hxa1 (by linarith)
      _ ≤ (1 + 1 / 1000) ^ (2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          rw [div_le_iff₀ ha]; linarith
      _ ≤ 1.0021 := by norm_num
  -- step D: x^{-σ} ≤ e x^{-Re s₀}
  have hD' : x ^ (η - s.re) ≤ Real.exp 1 * (x ^ η * x ^ (-s₀.re)) := by
    have e : x ^ (η - s.re) = x ^ η * x ^ (-s₀.re) * x ^ (s₀.re - s.re) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    rw [e, mul_comm (Real.exp 1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp]
    have := (abs_le.mp hreS).1
    have : Real.log x * (s₀.re - s.re) ≤ Real.log x * (1 / Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith) hL.le
    rw [mul_one_div_cancel hL.ne'] at this; exact this
  -- step E–F: x^{-Re s₀} ≤ x^{-θ} · 8eΛ/(α |s₀|)
  have hF : x ^ (-s₀.re) ≤ x ^ (-θ) * (8 * Real.exp 1 * Λ / (α * ‖s₀‖)) := by
    have hpow : ‖(x : ℂ) ^ (-w₀)‖ = x ^ (θ - s₀.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; congr 1; simp [hw₀def]
    have e : x ^ (-s₀.re) = x ^ (-θ) * ‖(x : ℂ) ^ (-w₀)‖ := by
      rw [hpow, ← Real.rpow_add hx0]; ring_nf
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx0.le _)
    have hMk : Mk θ α γ x s₀ = -ZB s₀ := by linear_combination hz
    have hnorm : ‖Mk θ α γ x s₀‖ =
        α * ‖s₀‖ / 2 * (‖(x : ℂ) ^ (-w₀)‖ * ‖phiTransform w₀‖ / ‖w₀‖) := by
      unfold Mk
      rw [← hw₀def, norm_mul, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      simp
    rw [hMk, norm_neg, hs₀w] at hnorm
    have hZ := h.norm_le _ (sOf_mem hw₀)
    rw [← hs₀w] at hnorm hZ
    have hphi := half_exp_neg_one_le_norm_phiTransform (h.re_nonneg hw₀) (h.re_le_one hw₀)
      (h.abs_im_le_one hw₀)
    have hw1 := h.norm_w_le hw₀
    have hw0 := h.norm_w_ge hw₀
    have he := Real.exp_pos (-1)
    have hee : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    set P := ‖(x : ℂ) ^ (-w₀)‖
    have hP : 0 ≤ P := norm_nonneg _
    rw [le_div_iff₀ (by positivity)]
    have key : α * ‖s₀‖ * P * ‖phiTransform w₀‖ ≤ 4 * Λ * ‖w₀‖ := by
      have : α * ‖s₀‖ / 2 * (P * ‖phiTransform w₀‖ / ‖w₀‖) ≤ 2 * Λ := hnorm ▸ hZ
      rw [div_mul_div_comm, div_le_iff₀ (by positivity)] at this; linarith
    have k2 : α * ‖s₀‖ * P * (Real.exp (-1) / 2) ≤ α * ‖s₀‖ * P * ‖phiTransform w₀‖ :=
      mul_le_mul_of_nonneg_left hphi (by positivity)
    have hee' : Real.exp (-1) * Real.exp 1 = 1 := by rw [mul_comm]; exact hee
    have k3 : P * (α * ‖s₀‖) = (α * ‖s₀‖ * P * (Real.exp (-1) / 2)) * (2 * Real.exp 1) := by
      linear_combination (-(α * ‖s₀‖ * P)) * hee'
    have k4 : α * ‖s₀‖ * P * (Real.exp (-1) / 2) ≤ 4 * Λ := by
      have : 4 * Λ * ‖w₀‖ ≤ 4 * Λ := by nlinarith
      linarith
    rw [k3]
    have := mul_le_mul_of_nonneg_right k4 (show 0 ≤ 2 * Real.exp 1 by positivity)
    linarith
  -- combine
  have hE2 : Real.exp 1 * Real.exp 1 ≤ 7.39 := exp_one_mul_exp_one_le
  have hratio : (1 + 1.36 * ‖s‖) / ‖s₀‖ ≤ 2.3602 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hxη : 0 ≤ x ^ η := Real.rpow_nonneg hx0.le _
  have hxθ : 0 ≤ x ^ (-θ) := Real.rpow_nonneg hx0.le _
  have hαs : 0 < α * ‖s₀‖ := by positivity
  have hmain : ‖lateNoise D a s‖ ≤ 150 * Λ * x ^ (η - θ) / α := by
    have hxηθ : x ^ (η - θ) = x ^ η * x ^ (-θ) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc ‖lateNoise D a s‖ ≤ a ^ (η - s.re) * (1 + 1.36 * ‖s‖) :=
          hA.trans (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg ha.le _))
      _ ≤ 1.0021 * (Real.exp 1 * ((x ^ η * x ^ (-θ)) * (8 * Real.exp 1 * Λ / (α * ‖s₀‖)))) *
          (1 + 1.36 * ‖s‖) := by
          gcongr
          calc a ^ (η - s.re) ≤ 1.0021 * x ^ (η - s.re) := hC
            _ ≤ 1.0021 * (Real.exp 1 * (x ^ η * x ^ (-s₀.re))) := by gcongr
            _ ≤ 1.0021 * (Real.exp 1 * (x ^ η * (x ^ (-θ) *
                (8 * Real.exp 1 * Λ / (α * ‖s₀‖))))) := by gcongr
            _ = _ := by ring
      _ = 1.0021 * 8 * (Real.exp 1 * Real.exp 1) * Λ * (x ^ η * x ^ (-θ)) / α *
          ((1 + 1.36 * ‖s‖) / ‖s₀‖) :=
          alg_aux _ _ _ _ _ _ _ (by positivity) (by positivity)
      _ ≤ 1.0021 * 8 * 7.39 * Λ * (x ^ η * x ^ (-θ)) / α * 2.3602 := by
          gcongr
      _ ≤ 150 * Λ * x ^ (η - θ) / α := by
          rw [hxηθ]
          have : 0 ≤ Λ * (x ^ η * x ^ (-θ)) / α := by positivity
          have e1 : 1.0021 * 8 * 7.39 * Λ * (x ^ η * x ^ (-θ)) / α * 2.3602 =
              (1.0021 * 8 * 7.39 * 2.3602) * (Λ * (x ^ η * x ^ (-θ)) / α) := by ring
          have e2 : 150 * Λ * (x ^ η * x ^ (-θ)) / α = 150 * (Λ * (x ^ η * x ^ (-θ)) / α) := by
            ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right (by norm_num) this
  refine ⟨hmain, hmain.trans ?_⟩
  have h1 : x ^ (η - θ) ≤ x ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h.one_lt_x.le (by linarith)
  have h2 : 150 * Λ * x ^ (η - θ) / α ≤ 150 * Λ * x ^ (η - θ) := by
    apply div_le_self (by positivity) hα
  have h4 : 150 * Λ * x ^ (η - θ) ≤ 165 * Λ * x ^ (-(1 / 8 : ℝ)) := by
    have hp : 0 ≤ x ^ (η - θ) := Real.rpow_nonneg hx0.le _
    have : 150 * Λ ≤ 165 * Λ := by linarith
    exact mul_le_mul this h1 hp (by linarith)
  exact h2.trans h4

end Lemma46Hyp

end DesignedZero

end
