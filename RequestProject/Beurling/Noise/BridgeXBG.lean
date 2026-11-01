module

public import RequestProject.Beurling.Noise.BridgeXBKR
public import RequestProject.Beurling.Noise.KRTrueStep

/-!
# The window function `G` of the proof of Lemma 5.27

For a centre `c`, `G(c) = P(c + U_c ≥ X₀)` with `U_c` uniform on `[-H(c)/2, H(c)/2)`, i.e. the
mass of the window `bx_{H(c)}(· - c)` on `[X₀, ∞)` (`Gs`). Then:

* `Gs_eq_ramp` : `G(c) = clamp(½ + (c - X₀)/H(c), 0, 1)` (Step 2 of the proof);
* `setIntegral_Qd` : `∫_{[X₀,∞)} Q_w f = ∫ f(v) G(v/w) dv` (Fubini);
* `abs_Gs_sub_ind_le` : `|G(c) - 1[c ≥ X₀]| ≤ ½`, and it vanishes unless `|c - X₀| ≤ H(c)/2`;
* `Gs_eq_zero_of`, `Gs_eq_one_of` : `G` is constant off `[X₀ - H(c)/2, X₀ + H(c)/2]`;
* `Gs_lip` : the Lipschitz bound `|G(c₁) - G(c₂)| ≤ ((1 + θM/h)/h)|c₁ - c₂|` on a set where
  `H ≥ h`, `H` is `θ`-Lipschitz and `|c - X₀| ≤ M`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace KR

variable {H : ℝ → ℝ}

/-- `G(c)`: the mass of the window `bx_{H(c)}(· - c)` on `[X₀, ∞)`. -/
noncomputable def Gs (H : ℝ → ℝ) (X0 c : ℝ) : ℝ := ∫ t in Ici X0, kd H c t

lemma integral_kd (hH : WidthReg H) (c : ℝ) : ∫ t, kd H c t = 1 := by
  have h := integral_norm_eq_lintegral_enorm (integrable_kd hH c).1
  rw [lintegral_kd hH c, ENNReal.toReal_one] at h
  rw [← h]
  congr 1; funext t; rw [Real.norm_eq_abs, abs_of_nonneg (kd_nonneg hH c t)]

lemma Gs_eq_ramp (hH : WidthReg H) (X0 c : ℝ) :
    Gs H X0 c = ramp ((c - X0) / H c + 1 / 2) := by
  have hp := hH.pos c
  have hi := integrable_kd hH c
  have h1 : Gs H X0 c = 1 - cdf (kd H c) X0 := by
    unfold Gs cdf
    rw [← integral_kd hH c, ← integral_add_compl (s := Iic X0) measurableSet_Iic hi, compl_Iic,
      integral_Ici_eq_integral_Ioi]
    ring
  rw [h1, cdf_kd hH, boxAvg_stepF hp]
  set h := H c
  have hh : h⁻¹ * h = 1 := inv_mul_cancel₀ hp.ne'
  rcases le_or_gt (h / 2) (c - X0) with hA | hA
  · rw [max_eq_left (by linarith), max_eq_left (by linarith),
      ramp_of_one_le (by
        have : 1 / 2 ≤ (c - X0) / h := by rw [le_div_iff₀ hp]; linarith
        linarith)]
    ring
  rcases le_or_gt (c - X0) (-(h / 2)) with hB | hB
  · rw [max_eq_right (by linarith), max_eq_right (by linarith),
      ramp_of_nonpos (by rw [div_add' _ _ _ hp.ne', div_nonpos_iff]; right; constructor <;>
        linarith)]
    field_simp; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), sub_zero]
    rw [ramp_of_mem]
    · field_simp; ring
    · rw [div_add' _ _ _ hp.ne']; apply div_pos _ hp; linarith
    · rw [div_add' _ _ _ hp.ne', div_lt_one hp]; linarith

lemma ramp_mem (s : ℝ) : 0 ≤ ramp s ∧ ramp s ≤ 1 := by
  unfold ramp; constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

lemma Gs_mem (hH : WidthReg H) (X0 c : ℝ) : 0 ≤ Gs H X0 c ∧ Gs H X0 c ≤ 1 := by
  rw [Gs_eq_ramp hH]; exact ramp_mem _

lemma Gs_eq_zero_of (hH : WidthReg H) {X0 c : ℝ} (h : c + H c / 2 ≤ X0) : Gs H X0 c = 0 := by
  have hp := hH.pos c
  rw [Gs_eq_ramp hH, ramp_of_nonpos]
  rw [div_add' _ _ _ hp.ne', div_nonpos_iff]; right; constructor <;> linarith

lemma Gs_eq_one_of (hH : WidthReg H) {X0 c : ℝ} (h : X0 ≤ c - H c / 2) : Gs H X0 c = 1 := by
  have hp := hH.pos c
  rw [Gs_eq_ramp hH, ramp_of_one_le]
  rw [div_add' _ _ _ hp.ne', le_div_iff₀ hp]; linarith

lemma abs_ramp_sub_le (a b : ℝ) : |ramp a - ramp b| ≤ |a - b| := by
  unfold ramp
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 a) 0 (min 1 b)
  have h2 := abs_min_sub_min_le_max (1 : ℝ) a 1 b
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min 1 a - min 1 b))] at h1
  rw [max_eq_right (abs_nonneg (a - b))] at h2
  exact h1.trans h2

/-- **`|G(c) - 1[c ≥ X₀]| ≤ ½`**, and it vanishes unless `|c - X₀| ≤ H(c)/2`. -/
lemma abs_Gs_sub_ind_le (hH : WidthReg H) (X0 c : ℝ) :
    |Gs H X0 c - (if X0 ≤ c then 1 else 0)| ≤
      if |c - X0| ≤ H c / 2 then 1 / 2 else 0 := by
  have hp := hH.pos c
  split_ifs with h1 h2 h2
  · -- `c ≥ X₀`, inside
    rw [Gs_eq_ramp hH]
    have hr := ramp_mem ((c - X0) / H c + 1 / 2)
    have hge : 1 / 2 ≤ ramp ((c - X0) / H c + 1 / 2) := by
      unfold ramp
      refine le_max_of_le_right (le_min (by norm_num) ?_)
      have : 0 ≤ (c - X0) / H c := div_nonneg (by linarith) hp.le
      linarith
    rw [abs_le]; constructor <;> linarith [hr.2]
  · push_neg at h2
    rw [abs_of_nonneg (by linarith)] at h2
    rw [Gs_eq_one_of hH (by linarith)]; simp
  · rw [Gs_eq_ramp hH]
    have hr := ramp_mem ((c - X0) / H c + 1 / 2)
    have hle : ramp ((c - X0) / H c + 1 / 2) ≤ 1 / 2 := by
      unfold ramp
      refine max_le (by norm_num) (min_le_of_right_le ?_)
      have : (c - X0) / H c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
      linarith
    rw [sub_zero, abs_le]; constructor <;> linarith [hr.1]
  · push_neg at h2
    rw [abs_of_neg (by linarith)] at h2
    rw [Gs_eq_zero_of hH (by linarith)]; simp

/-- **The Lipschitz bound of `G`** on a set where `H ≥ h > 0`, `H` is `θ`-Lipschitz and
`|c - X₀| ≤ M`. -/
lemma Gs_lip (hH : WidthReg H) {X0 h θ M : ℝ} {S : Set ℝ} (hh : 0 < h) (hθ : 0 ≤ θ)
    (hHS : ∀ c ∈ S, h ≤ H c) (hlip : ∀ c₁ ∈ S, ∀ c₂ ∈ S, |H c₁ - H c₂| ≤ θ * |c₁ - c₂|)
    (hM : ∀ c ∈ S, |c - X0| ≤ M) {c₁ c₂ : ℝ} (h1 : c₁ ∈ S) (h2 : c₂ ∈ S) :
    |Gs H X0 c₁ - Gs H X0 c₂| ≤ (1 + θ * M / h) / h * |c₁ - c₂| := by
  rw [Gs_eq_ramp hH, Gs_eq_ramp hH]
  refine (abs_ramp_sub_le _ _).trans ?_
  have hH1 := hHS c₁ h1
  have hH2 := hHS c₂ h2
  have hp1 : 0 < H c₁ := lt_of_lt_of_le hh hH1
  have hp2 : 0 < H c₂ := lt_of_lt_of_le hh hH2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c₂ h2)
  have e : (c₁ - X0) / H c₁ + 1 / 2 - ((c₂ - X0) / H c₂ + 1 / 2) =
      (c₁ - c₂) / H c₁ + (c₂ - X0) * (H c₂ - H c₁) / (H c₁ * H c₂) := by
    field_simp; ring
  rw [e]
  have t1 : |(c₁ - c₂) / H c₁| ≤ |c₁ - c₂| / h := by
    rw [abs_div, abs_of_pos hp1]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hh hH1
  have t2 : |(c₂ - X0) * (H c₂ - H c₁) / (H c₁ * H c₂)| ≤ M * (θ * |c₁ - c₂|) / (h * h) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hp1 hp2)]
    have hl := hlip c₂ h2 c₁ h1
    rw [abs_sub_comm c₂ c₁] at hl
    apply div_le_div₀ (by positivity) (mul_le_mul (hM c₂ h2) hl (abs_nonneg _) hM0)
      (by positivity) (mul_le_mul hH1 hH2 hh.le hp1.le)
  calc _ ≤ |(c₁ - c₂) / H c₁| + |(c₂ - X0) * (H c₂ - H c₁) / (H c₁ * H c₂)| := abs_add_le _ _
    _ ≤ |c₁ - c₂| / h + M * (θ * |c₁ - c₂|) / (h * h) := add_le_add t1 t2
    _ = (1 + θ * M / h) / h * |c₁ - c₂| := by field_simp

/-- **Fubini for the step**: `∫_{[X₀,∞)} Q_w f = ∫ f(v) G(v/w) dv`. -/
lemma setIntegral_Qd (hH : WidthReg H) (w X0 : ℝ) {f : ℝ → ℝ} (hf : Integrable f)
    (hfm : Measurable f) :
    ∫ t in Ici X0, Qd H w f t = ∫ v, f v * Gs H X0 (v / w) := by
  unfold Qd Gs
  rw [integral_integral_swap (integrable_prod_Qd hH w hf hfm _)]
  congr 1; funext v
  rw [integral_const_mul]

end KR

end
