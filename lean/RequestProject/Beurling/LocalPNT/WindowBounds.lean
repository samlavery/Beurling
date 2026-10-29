module

public import RequestProject.Beurling.LocalPNT.Kernel

/-!
# Step 10 of the proof of Theorem 5.24: bounds for the transform of the window

`Φ(s) = ∫ ψ(x) e^{sx} dx = Î(s) κ̂(s)` with `Î(s) = ∫_{a-ω}^{b+ω} e^{sx} dx` and
`κ̂(s) = (sinh(sω/k)/(sω/k))^k`. For `σ = Re s ≥ 0`:
`|Φ(s)| ≤ e^{σ(b+2ω)} (b - a + 2ω)`, `|Φ(s)| ≤ e^{σ(b+2ω)} 2/|t|` and
`|Φ(s)| ≤ e^{σ(b+2ω)} (2/|t|) (k/(|t|ω))^k`; `Φ` is holomorphic on `σ > 0`.
-/

@[expose] public section

open Set Real Complex MeasureTheory intervalIntegral

namespace LocalPNT

/-- The transform `Φ(s) = ∫ ψ(x) e^{sx} dx` of the window `ψ = windowLog a b ω k`. -/
noncomputable def PhiW (a b ω : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x, (windowLog a b ω k x : ℂ) * cexp (s * x)

variable {a b ω : ℝ} {k : ℕ}

lemma norm_kappaHat_le (hω : 0 < ω) (hk : 1 ≤ k) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Complex.sinh (s * (ω / k)) / (s * (ω / k))) ^ k‖ ≤ Real.exp (s.re * ω) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [norm_pow]
  have h1 := norm_sinh_div_le (s * (ω / k))
  have hre : (s * (ω / k : ℝ)).re = s.re * (ω / k) := by simp
  have e : (s * ((ω : ℂ) / (k : ℂ))) = s * (((ω / k : ℝ)) : ℂ) := by push_cast; ring
  rw [e, hre, abs_of_nonneg (by positivity)] at h1
  calc ‖Complex.sinh (s * (ω / k)) / (s * (ω / k))‖ ^ k ≤ (Real.exp (s.re * (ω / k))) ^ k := by
        rw [e]; exact pow_le_pow_left₀ (norm_nonneg _) h1 k
    _ = Real.exp (s.re * ω) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma norm_kappaHat_le' (hω : 0 < ω) (hk : 1 ≤ k) {s : ℂ} (hs : 0 ≤ s.re) (ht : s.im ≠ 0) :
    ‖(Complex.sinh (s * (ω / k)) / (s * (ω / k))) ^ k‖ ≤
      Real.exp (s.re * ω) * (k / (|s.im| * ω)) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [norm_pow]
  have e : (s * ((ω : ℂ) / (k : ℂ))) = s * (((ω / k : ℝ)) : ℂ) := by push_cast; ring
  have h1 := norm_sinh_div_le' (s * (((ω / k : ℝ)) : ℂ))
  have hre : (s * (ω / k : ℝ)).re = s.re * (ω / k) := by simp
  rw [hre, abs_of_nonneg (by positivity)] at h1
  have him : |s.im| * (ω / k) ≤ ‖s * (((ω / k : ℝ)) : ℂ)‖ := by
    have := Complex.abs_im_le_norm (s * (((ω / k : ℝ)) : ℂ))
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      add_zero] at this
    rw [abs_mul, abs_of_pos (by positivity : 0 < ω / k)] at this
    exact this
  have hpos : 0 < |s.im| * (ω / k) := by positivity
  have h2 : ‖Complex.sinh (s * (((ω / k : ℝ)) : ℂ)) / (s * (((ω / k : ℝ)) : ℂ))‖ ≤
      Real.exp (s.re * (ω / k)) * (k / (|s.im| * ω)) := by
    refine h1.trans ?_
    rw [div_le_iff₀ (lt_of_lt_of_le hpos him)]
    calc Real.exp (s.re * (ω / k)) = Real.exp (s.re * (ω / k)) * (k / (|s.im| * ω)) *
          (|s.im| * (ω / k)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left him (by positivity)
  rw [e]
  calc ‖Complex.sinh (s * (((ω / k : ℝ)) : ℂ)) / (s * (((ω / k : ℝ)) : ℂ))‖ ^ k ≤
        (Real.exp (s.re * (ω / k)) * (k / (|s.im| * ω))) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) h2 k
    _ = Real.exp (s.re * ω) * (k / (|s.im| * ω)) ^ k := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; field_simp

/-- `|Φ(s)| ≤ e^{σ(b+2ω)} (b - a + 2ω)` and, for `t ≠ 0`, `≤ e^{σ(b+2ω)} (2/|t|)` and
`≤ e^{σ(b+2ω)} (2/|t|) (k/(|t|ω))^k`. -/
theorem norm_PhiW_le (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    ‖PhiW a b ω k s‖ ≤ Real.exp (s.re * (b + 2 * ω)) * (b - a + 2 * ω) ∧
    (s.im ≠ 0 → ‖PhiW a b ω k s‖ ≤ Real.exp (s.re * (b + 2 * ω)) * (2 / |s.im|)) ∧
    (s.im ≠ 0 → ‖PhiW a b ω k s‖ ≤
      Real.exp (s.re * (b + 2 * ω)) * (2 / |s.im|) * (k / (|s.im| * ω)) ^ k) := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at hs; simp at hs
  have hab' : a - ω ≤ b + ω := by linarith
  unfold PhiW
  rw [windowLog_laplace hab hω hk hs0, norm_mul]
  have hI1 := norm_integral_cexp_le hab' hs.le
  have hK1 := norm_kappaHat_le hω hk hs.le
  have he : Real.exp (s.re * (b + ω)) * Real.exp (s.re * ω) = Real.exp (s.re * (b + 2 * ω)) := by
    rw [← Real.exp_add]; ring_nf
  refine ⟨?_, fun ht => ?_, fun ht => ?_⟩
  · calc _ ≤ ((b + ω) - (a - ω)) * Real.exp (s.re * (b + ω)) * Real.exp (s.re * ω) :=
          mul_le_mul hI1 hK1 (norm_nonneg _)
            (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = _ := by rw [← he]; ring
  · have hI2 := norm_integral_cexp_le_im hab' hs.le ht
    calc _ ≤ 2 * Real.exp (s.re * (b + ω)) / |s.im| * Real.exp (s.re * ω) :=
          mul_le_mul hI2 hK1 (norm_nonneg _) (by positivity)
      _ = _ := by rw [← he]; ring
  · have hI2 := norm_integral_cexp_le_im hab' hs.le ht
    have hK2 := norm_kappaHat_le' hω hk hs.le ht
    calc _ ≤ 2 * Real.exp (s.re * (b + ω)) / |s.im| *
          (Real.exp (s.re * ω) * (k / (|s.im| * ω)) ^ k) :=
          mul_le_mul hI2 hK2 (norm_nonneg _) (by positivity)
      _ = _ := by rw [← he]; ring

/-- `|Φ(σ + it)| ≤ (2D + 4k/ω) e^{σ(b+2ω)}/(1 + t²)`, `D = b - a + 2ω`. -/
theorem norm_PhiW_le_sq (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖PhiW a b ω k (σ + t * I)‖ ≤
      (2 * (b - a + 2 * ω) + 4 * k / ω) * Real.exp (σ * (b + 2 * ω)) / (1 + t ^ 2) := by
  have hs : 0 < ((σ : ℂ) + t * I).re := by simpa using hσ
  obtain ⟨h1, h2, h3⟩ := norm_PhiW_le hab hω hk hs
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at h1 h2 h3
  have hD : 0 ≤ b - a + 2 * ω := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hE := Real.exp_pos (σ * (b + 2 * ω))
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rw [le_div_iff₀ h1t]
  by_cases ht : |t| ≤ 1
  · have : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
    have h4 : 0 ≤ 4 * (k : ℝ) / ω := by positivity
    have := mul_le_mul h1 (show 1 + t ^ 2 ≤ 2 by linarith) h1t.le (by positivity)
    nlinarith
  · push_neg at ht
    have ht0 : t ≠ 0 := by intro e; rw [e] at ht; simp at ht; linarith
    have hta : 0 < |t| := by linarith
    have hkey : ‖PhiW a b ω k (σ + t * I)‖ ≤
        Real.exp (σ * (b + 2 * ω)) * (2 * k / (t ^ 2 * ω)) := by
      have ht2 : t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
      by_cases hq : (k : ℝ) / (|t| * ω) ≤ 1
      · have hpow : ((k : ℝ) / (|t| * ω)) ^ k ≤ (k : ℝ) / (|t| * ω) :=
          pow_le_of_le_one (by positivity) hq (by omega)
        calc _ ≤ Real.exp (σ * (b + 2 * ω)) * (2 / |t|) * (k / (|t| * ω)) ^ k := h3 ht0
          _ ≤ Real.exp (σ * (b + 2 * ω)) * (2 / |t|) * (k / (|t| * ω)) := by gcongr
          _ = _ := by rw [ht2]; field_simp
      · push_neg at hq
        calc _ ≤ Real.exp (σ * (b + 2 * ω)) * (2 / |t|) := h2 ht0
          _ ≤ Real.exp (σ * (b + 2 * ω)) * (2 / |t| * (k / (|t| * ω))) := by
              apply mul_le_mul_of_nonneg_left _ hE.le
              have : 0 < 2 / |t| := by positivity
              nlinarith
          _ = _ := by rw [ht2]; field_simp
    have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
    calc ‖PhiW a b ω k (σ + t * I)‖ * (1 + t ^ 2) ≤
          Real.exp (σ * (b + 2 * ω)) * (2 * k / (t ^ 2 * ω)) * (1 + t ^ 2) :=
          mul_le_mul_of_nonneg_right hkey h1t.le
      _ ≤ Real.exp (σ * (b + 2 * ω)) * (2 * k / (t ^ 2 * ω)) * (2 * t ^ 2) := by
          gcongr; linarith
      _ = Real.exp (σ * (b + 2 * ω)) * (4 * k / ω) := by field_simp; ring
      _ ≤ _ := by nlinarith

/-- `Φ` is holomorphic on `σ > 0`. -/
theorem differentiableOn_PhiW (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) :
    DifferentiableOn ℂ (PhiW a b ω k) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by intro e; rw [e] at hs; simp at hs
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  set F : ℂ → ℂ := fun s => ((cexp (s * (b + ω)) - cexp (s * (a - ω))) / s) *
    (Complex.sinh (s * (ω / k)) / (s * (ω / k))) ^ k
  have hO : IsOpen {s : ℂ | s ≠ 0} := isOpen_compl_singleton
  have heq : PhiW a b ω k =ᶠ[nhds s] F := by
    filter_upwards [hO.mem_nhds hs0] with z hz
    unfold PhiW
    rw [windowLog_laplace hab hω hk hz, integral_exp_mul_complex hz]
    push_cast; ring
  have hF : DifferentiableAt ℂ F s := by
    have hsk : s * ((ω : ℂ) / k) ≠ 0 := mul_ne_zero hs0 (div_ne_zero hω0 hk0)
    refine (((((differentiableAt_id.mul_const _).cexp).sub
      ((differentiableAt_id.mul_const _).cexp)).div differentiableAt_id hs0)).mul ?_
    exact ((((differentiableAt_id.mul_const _).csinh).div
      (differentiableAt_id.mul_const _) hsk)).pow k
  exact (heq.differentiableAt_iff.mpr hF).differentiableWithinAt

end LocalPNT

end
