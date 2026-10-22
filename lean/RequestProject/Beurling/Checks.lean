module

public import Mathlib

/-!
# Machine checks of self-contained steps of the paper

* `re_Phi_ge` — Section 4.2, second bullet: `Re Φ(w) ≥ e⁻¹ cos 1` for `0 ≤ Re w ≤ 1`,
  `|Im w| ≤ 1`, where `Φ(w) = ∫₀¹ e^{-wv} ϕ'(v) dv`, `ϕ' ≥ 0`, `∫₀¹ ϕ' = 1`.
* `zeta2_pow4_div_zeta4_le` — Lemma 4.8(i): `ζ(2)⁴/ζ(4) ≤ 6.8`, and the Paley–Zygmund
  density `(1/4)/6.8 > 0.036`.
* `prop41_numeric`, `eta_ge` — Proposition 4.1: `8 (log L)² + 10⁻⁶ L + 2 ≤ 2.82·10⁻⁵ L` for
  all `L ≥ 10⁸ - 1`, and `η = min(θ, 1/2 - θ)/2 ≥ 5·10⁻⁵ > 2.82·10⁻⁵` for
  `θ ∈ [1/4, 1/2 - 10⁻⁴]`.
-/

@[expose] public section

open MeasureTheory Set

namespace BeurlingPaper

lemma re_cexp_lower {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) (him : |w.im| ≤ 1)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp (-1) * Real.cos 1 ≤ (Complex.exp (-(w * v))).re := by
  rw [Complex.exp_re]
  have hre : (-(w * (v:ℂ))).re = -(w.re * v) := by simp
  have him' : (-(w * (v:ℂ))).im = -(w.im * v) := by simp
  rw [hre, him', Real.cos_neg]
  have hc1 : 0 < Real.cos 1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have he : Real.exp (-1) ≤ Real.exp (-(w.re * v)) := Real.exp_le_exp.mpr (by nlinarith)
  have hc : Real.cos 1 ≤ Real.cos (w.im * v) := by
    rw [← Real.cos_abs (w.im * v)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
    rw [abs_mul, abs_of_nonneg hv0]; nlinarith [abs_nonneg w.im]
  exact mul_le_mul he hc hc1.le (Real.exp_pos _).le

/-- Section 4.2: `Re Φ(w) ≥ e⁻¹ cos 1` for `0 ≤ Re w ≤ 1`, `|Im w| ≤ 1`, where
`Φ(w) = ∫₀¹ e^{-wv} g(v) dv` with `g ≥ 0` on `[0,1]` and `∫₀¹ g = 1` (in the paper `g = ϕ'`). -/
theorem re_Phi_ge (g : ℝ → ℝ) (hg0 : ∀ v ∈ Icc (0:ℝ) 1, 0 ≤ g v)
    (hgi : IntervalIntegrable g volume 0 1) (hg1 : ∫ v in (0:ℝ)..1, g v = 1)
    {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) (him : |w.im| ≤ 1) :
    Real.exp (-1) * Real.cos 1 ≤ (∫ v in (0:ℝ)..1, Complex.exp (-(w * v)) * g v).re := by
  have hcont : Continuous (fun v : ℝ => Complex.exp (-(w * v))) := by fun_prop
  have hint : IntervalIntegrable (fun v : ℝ => Complex.exp (-(w * v)) * g v) volume 0 1 := by
    have : IntervalIntegrable (fun v : ℝ => ((g v : ℝ) : ℂ)) volume 0 1 :=
      ⟨hgi.1.ofReal, hgi.2.ofReal⟩
    exact this.continuousOn_mul hcont.continuousOn
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at hcomm
  rw [← hcomm]
  have hre : ∀ v : ℝ,
      (Complex.exp (-(w * v)) * g v).re = (Complex.exp (-(w * v))).re * g v := by
    intro v; simp
  simp_rw [hre]
  calc Real.exp (-1) * Real.cos 1 = ∫ v in (0:ℝ)..1, Real.exp (-1) * Real.cos 1 * g v := by
        rw [intervalIntegral.integral_const_mul, hg1, mul_one]
    _ ≤ ∫ v in (0:ℝ)..1, (Complex.exp (-(w * v))).re * g v := by
        apply intervalIntegral.integral_mono_on zero_le_one (hgi.const_mul _)
        · exact (hgi.continuousOn_mul (Complex.continuous_re.comp hcont).continuousOn)
        · intro v hv
          exact mul_le_mul_of_nonneg_right (re_cexp_lower h0 h1 him hv.1 hv.2) (hg0 v hv)

/-- Lemma 4.8(i): the fourth-moment constant `ζ(2)⁴/ζ(4) = 5π⁴/72 ≤ 6.8`, and the resulting
Paley–Zygmund density `(1/4)/6.8` exceeds `0.036`. -/
theorem zeta2_pow4_div_zeta4_le :
    ‖riemannZeta 2 ^ 4 / riemannZeta 4‖ ≤ 6.8 ∧ (0.036:ℝ) < 1 / (4 * 6.8) := by
  refine ⟨?_, by norm_num⟩
  rw [riemannZeta_two, riemannZeta_four]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have : ((Real.pi:ℂ) ^ 2 / 6) ^ 4 / ((Real.pi:ℂ) ^ 4 / 90) =
      ((5 * Real.pi ^ 4 / 72 : ℝ) : ℂ) := by
    push_cast
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    field_simp; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h := Real.pi_lt_d4
  have h4 : Real.pi ^ 4 < 3.1416 ^ 4 := pow_lt_pow_left₀ h hpi.le (by norm_num)
  nlinarith

lemma log_1e8_le : Real.log (10 ^ 8) ≤ 18.43 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 18.43 = Real.exp 1 ^ 18 * Real.exp 0.215 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.215 by norm_num)
  rw [h1]
  have a : (2.7182818283:ℝ) ^ 18 ≤ Real.exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) he.le 18
  have b : ((1:ℝ) + 0.215 + 0.215 ^ 2 / 2) ^ 2 ≤ Real.exp 0.215 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hq 2
  calc (10:ℝ) ^ 8 ≤ (2.7182818283:ℝ) ^ 18 * ((1:ℝ) + 0.215 + 0.215 ^ 2 / 2) ^ 2 := by norm_num
    _ ≤ _ := mul_le_mul a b (by positivity) (by positivity)

/-- Proposition 4.1: with `ℓ = log L`, `8ℓ² + 10⁻⁶ L + 2 ≤ 2.82·10⁻⁵ L` for all `L ≥ 10⁸ - 1`. -/
theorem prop41_numeric {L : ℝ} (hL : 10 ^ 8 - 1 ≤ L) :
    8 * Real.log L ^ 2 + 1e-6 * L + 2 ≤ 2.82e-5 * L := by
  set L0 : ℝ := 10 ^ 8 - 1
  have hL0 : 0 < L0 := by norm_num [L0]
  set a := Real.log L0
  have ha : a ≤ 18.43 := le_trans (Real.log_le_log hL0 (by norm_num [L0])) log_1e8_le
  have ha0 : 0 ≤ a := Real.log_nonneg (by norm_num [L0])
  set t := L / L0
  have ht : 1 ≤ t := by rw [le_div_iff₀ hL0]; linarith
  have hLt : L = L0 * t := by simp only [t]; field_simp
  set r := Real.sqrt t
  have hr : 1 ≤ r := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht
  have hrt : r ^ 2 = t := Real.sq_sqrt (by linarith)
  have hlogt : Real.log t ≤ 2 * (r - 1) := by
    have : Real.log t = 2 * Real.log r := by
      rw [← hrt, Real.log_pow]; push_cast; ring
    rw [this]; linarith [Real.log_le_sub_one_of_pos (show 0 < r by linarith)]
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog : Real.log L = a + Real.log t := by
    rw [hLt, Real.log_mul hL0.ne' (by linarith)]
  rw [hlog, hLt]
  have hs : 0 ≤ a + Real.log t := by linarith
  have h1 : (a + Real.log t) ^ 2 ≤ (18.43 + 2 * (r - 1)) ^ 2 := by
    apply pow_le_pow_left₀ hs; linarith
  have h2 : 8 * (18.43 + 2 * (r - 1)) ^ 2 + 2 ≤ (2.82e-5 - 1e-6) * L0 * r ^ 2 := by
    norm_num [L0]; nlinarith
  rw [hrt] at h2
  nlinarith

/-- Proposition 4.1: for `θ ∈ [1/4, 1/2 - 10⁻⁴]`, `η = min(θ, 1/2 - θ)/2 ≥ 5·10⁻⁵`, which
exceeds the exponent `2.82·10⁻⁵` of `prop41_numeric`. -/
theorem eta_ge {θ : ℝ} (h1 : 1/4 ≤ θ) (h2 : θ ≤ 1/2 - 1e-4) :
    (2.82e-5 : ℝ) < 5e-5 ∧ 5e-5 ≤ min θ (1/2 - θ) / 2 := by
  refine ⟨by norm_num, ?_⟩
  rcases le_total θ (1/2 - θ) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end BeurlingPaper

end
