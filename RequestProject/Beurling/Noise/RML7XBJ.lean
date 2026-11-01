module

public import RequestProject.Beurling.Noise.RML7XB

/-!
# The field `hjb` (Proposition 5.31(i) / 5.33): `j_{X₀}(t) ≤ 0.4209` in the small range

`hjb_of` : for `jb := jXdef … j₀ NK` (eq. (jX0)), from `xbB_le_five_twelfths`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.XB7

open KR.Chain KR.TNP BModel

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- **The field `hjb` of `BModel.RealMarginLoc`** (Proposition 5.31(i) / 5.33) for
`jb := jXdef P H tw X0m X0 θ lam0 j0 NK` (eq. (jX0)): `j_{X₀}(t) ≤ 0.4209` for
`2X₀ ≤ t ≤ X₀^{1.01}`.

Inputs: `TNP.Hyp` (with `(HBS)` and `PaperWidth`), `H(X₀) ≤ X₀^{1/8}`, the width bound
`H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`, `λ₀ ≤ 1.00003`, the jump `0 ≤ j₀ ≤ 1.0001/log X₀` (eq. (huxley),
`BaseRange.jz_le`), and at the starts of the windows the scale horizon `18y ≤ Z²` and
`√(2y) ≤ P_K` for the chosen indices `NK y`. -/
theorem hjb_of {Z η1 η2 ε θ X0 lam0 j0 b : ℝ} {ε1 : ℝ → ℝ}
    (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (hXZ : X0m ≤ Z) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hlamS : lam0 ≤ 1.00003) (hΛ : 100000000 ≤ Real.log X0) (hHX : H X0 ≤ X0 ^ (1 / 8 : ℝ))
    (hHm : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hj0Λ : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z) {NK : ℝ → ℕ × ℕ}
    (hwin : ∀ t y, 2 * X0 ≤ t → t ≤ X0 ^ (1.01 : ℝ) → t ≤ b → InW (H t) t y →
      18 * y ≤ Z ^ 2 ∧ √(2 * y) ≤ Pk X0m (NK y).2) :
    ∀ t, 2 * X0 ≤ t → t ≤ X0 ^ (1.01 : ℝ) → t ≤ b →
      jXdef P H tw X0m X0 θ lam0 j0 NK t ≤ 0.4209 := by
  intro t ht2 ht1 htb
  have hP := h.width
  have hX := hP.X0m_pos
  have hHX0 := hP.reg.pos X0
  have hΛ0 : 0 < Real.log X0 := by linarith
  have hX0pos : 0 < X0 := by linarith
  have hX0m : X0m ≤ X0 := by linarith
  have hX0big : (100 : ℝ) ≤ X0 := by
    have := h.hbs.X0m_ge; norm_num at this; linarith
  have hsmallt := hP.small t (by linarith)
  have hHt := hP.reg.pos t
  have hnon : Nonempty {y : ℝ // InW (H t) t y} :=
    ⟨⟨t, by unfold InW; constructor <;> linarith⟩⟩
  refine ciSup_le fun ⟨y, hyW⟩ => ?_
  obtain ⟨hyl, hyu⟩ := hyW
  have hy0 : 0 < y := by linarith
  -- sizes of the start `y`
  have hrp1 : X0 ^ (1.01 : ℝ) * X0 ^ (1 / 8 : ℝ) * X0 ^ (0.865 : ℝ) = X0 ^ (2 : ℝ) := by
    rw [← Real.rpow_add hX0pos, ← Real.rpow_add hX0pos]; norm_num
  have hrp2 : (10 : ℝ) ≤ X0 ^ (0.865 : ℝ) := by
    have h1 : X0 ^ (1 / 2 : ℝ) ≤ X0 ^ (0.865 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : (10 : ℝ) ≤ X0 ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, show (10 : ℝ) = √100 by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX0big
    linarith
  have hX2 : X0 ^ (2 : ℝ) = X0 ^ 2 := by norm_num
  have hrp3 : 0 < X0 ^ (1.01 : ℝ) := Real.rpow_pos_of_pos hX0pos _
  have hrp4 : 0 < X0 ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hX0pos _
  have hyle : y ≤ 1.05 * X0 ^ (1.01 : ℝ) := by linarith
  have hδ : 8 * y * H X0 ≤ X0 ^ 2 := by
    rw [← hX2, ← hrp1]
    have h1 : 8 * y * H X0 ≤ 8 * (1.05 * X0 ^ (1.01 : ℝ)) * X0 ^ (1 / 8 : ℝ) := by
      have := mul_le_mul hyle hHX hHX0.le (by positivity)
      have e : 8 * (1.05 * X0 ^ (1.01 : ℝ)) * X0 ^ (1 / 8 : ℝ) =
          8 * (1.05 * X0 ^ (1.01 : ℝ) * X0 ^ (1 / 8 : ℝ)) := by ring
      rw [e, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    have h2 : 8 * (1.05 * X0 ^ (1.01 : ℝ)) * X0 ^ (1 / 8 : ℝ) ≤
        X0 ^ (1.01 : ℝ) * X0 ^ (1 / 8 : ℝ) * X0 ^ (0.865 : ℝ) := by
      have hp := mul_pos hrp3 hrp4
      have := mul_le_mul_of_nonneg_left hrp2 hp.le
      linarith
    linarith
  have hyN : 2 * y ≤ X0m * X0 := by
    have hX0m95 : 0.95 * X0 ≤ X0m := by
      have := hP.small X0 (by linarith); linarith
    have h1 : X0 ^ (1.01 : ℝ) * X0 ^ (0.99 : ℝ) = X0 ^ 2 := by
      rw [← Real.rpow_add hX0pos]; norm_num
    have h2 : (10 : ℝ) ≤ X0 ^ (0.99 : ℝ) := by
      have h3 : X0 ^ (1 / 2 : ℝ) ≤ X0 ^ (0.99 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h4 : (10 : ℝ) ≤ X0 ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, show (10 : ℝ) = √100 by
          rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hX0big
      linarith
    have h5 : 2 * y ≤ 2.1 * X0 ^ (1.01 : ℝ) := by linarith
    have k1 := mul_le_mul_of_nonneg_left h2 hrp3.le
    rw [h1] at k1
    have k2 := mul_le_mul_of_nonneg_right hX0m95 hX0pos.le
    have k3 : X0 ^ 2 = X0 * X0 := sq X0
    linarith
  have hyX : X0m ≤ y := by linarith
  -- `𝔅(y) ≤ 5/12`
  obtain ⟨hB0, hB⟩ := xbB_le_five_twelfths h hXZ hX0e hp2 ht hlam hlamS hyX hδ hyN
  -- `log y · j₀ ≤ 1.010102`
  have hly0 : 0 < Real.log y := Real.log_pos (by linarith)
  have hly : Real.log y ≤ 1.01 * Real.log X0 + 0.05 := by
    have h1 : Real.log y ≤ Real.log (1.05 * X0 ^ (1.01 : ℝ)) := Real.log_le_log hy0 hyle
    rw [Real.log_mul (by norm_num) hrp3.ne', Real.log_rpow hX0pos] at h1
    have h2 : Real.log 1.05 ≤ 0.05 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.05 by norm_num); linarith
    linarith
  have hlj : Real.log y * j0 ≤ 1.010102 := by
    have h1 : Real.log y * j0 ≤ (1.01 * Real.log X0 + 0.05) * (1.0001 / Real.log X0) :=
      mul_le_mul hly hj0Λ hj0 (by positivity)
    have h2 : (1.01 * Real.log X0 + 0.05) * (1.0001 / Real.log X0) =
        1.010101 + 0.050005 / Real.log X0 := by field_simp; ring
    have h3 : 0.050005 / Real.log X0 ≤ 0.050005 / 100000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
    have h4 : (0.050005 : ℝ) / 100000000 ≤ 1 / 10 ^ 6 := by norm_num
    linarith
  -- the `τ`-term
  obtain ⟨h18, hK⟩ := hwin t y ht2 ht1 htb ⟨hyl, hyu⟩
  have hsz := sizeE_le h hHm (X0 := X0) (y := y) hΛ hX0e hX0m hZ0 h18 (N := (NK y).1) hK
    (o := fun _ => 0) (by simp; positivity)
  simp only [mul_zero, Finset.sum_const_zero, zero_add] at hsz
  have hCN := CNc_bounds hΛ
  set Sθ := ∑ v ∈ dyScales X0 y (NK y).1, Real.log (2 * v) * sTheta P H X0m (NK y).2 v
  have hτ : j0 * (4.3 * CNc X0 * Sθ) ≤ 1 / 10 ^ 6 := by
    have hτ1 : 4.3 * CNc X0 * Sθ ≤ 1 := by
      have he := Real.exp_le_one_iff.mpr (by norm_num : (-76 : ℝ) ≤ 0)
      have hs : 8.4 * CNc X0 * Sθ ≤ 1 := hsz.trans he
      have e1 : 4.3 * CNc X0 * Sθ = 4.3 * (CNc X0 * Sθ) := by ring
      have e2 : 8.4 * CNc X0 * Sθ = 8.4 * (CNc X0 * Sθ) := by ring
      rw [e2] at hs
      rw [e1]
      rcases le_or_gt 0 (CNc X0 * Sθ) with h0 | h0
      · linarith only [hs, h0]
      · linarith only [h0]
    have hj1 : j0 ≤ 1 / 10 ^ 7 := by
      have : 1.0001 / Real.log X0 ≤ 1.0001 / 100000000 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
      have h' : (1.0001 : ℝ) / 100000000 ≤ 1 / 10 ^ 7 := by norm_num
      linarith only [this, h', hj0Λ]
    rcases le_or_gt 0 (4.3 * CNc X0 * Sθ) with h0 | h0
    · have := mul_le_mul hj1 hτ1 h0 (by norm_num)
      linarith only [this]
    · have : j0 * (4.3 * CNc X0 * Sθ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hj0 h0.le
      linarith only [this]
  -- assemble
  show jXat P H tw X0m X0 θ lam0 j0 (NK y).1 (NK y).2 y ≤ 0.4209
  unfold jXat
  have e : j0 * (xbB P H tw X0m y X0 θ lam0 + 4.3 * CNc X0 * Sθ / Real.log y) * Real.log y =
      Real.log y * j0 * (xbB P H tw X0m y X0 θ lam0 + (4.3 * CNc X0 * Sθ) / Real.log y) := by
    ring
  rw [e]
  exact Margin.RML6.jX0_small hly0 hB0 hB hlj hτ

end KR.XB7

end
