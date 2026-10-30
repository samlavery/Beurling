module

public import RequestProject.BSCert.Ei
public import RequestProject.BSCert.FX.LogQ

/-!
# `rankin_R.py`, parts (2) and (3)

* (2) `Ei(11) - e¹¹/11 - e¹¹/121 ≤ 134`, and `2.75/x + 134 x² e^{-x} < 1` for `x ≥ 11`;
  together they give `Ei(x) ≤ (eˣ/x)(1 + 2/x)` for `x ≥ 11` (proof of Lemma 6.22(c)).
* (3) `(3/2)^{3/4} ≤ 1.3555` and `Ei(log 2 / 4) ≥ -1` (proof of Lemma 6.22(e)).
-/

@[expose] public section

namespace BSCert.EiFn

open Real Finset

/-! ## Exact rational versions of the polynomial bounds -/

/-- Rational version of `EinLo`. -/
def EinLoQ (K : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ range K, x ^ (k + 1) / (((k + 1 : ℕ) : ℚ) * ((k + 1).factorial : ℚ))

/-- Rational version of `EinHi`. -/
def EinHiQ (K : ℕ) (x : ℚ) : ℚ :=
  EinLoQ K x + 2 * x ^ (K + 1) / (((K + 1 : ℕ) : ℚ) * ((K + 1).factorial : ℚ))

/-- Partial sum of the exponential series (a lower bound for `exp x` when `x ≥ 0`). -/
def expLoQ (n : ℕ) (x : ℚ) : ℚ := ∑ i ∈ range n, x ^ i / (i.factorial : ℚ)

lemma EinLoQ_cast (K : ℕ) (x : ℚ) : ((EinLoQ K x : ℚ) : ℝ) = EinLo K (x : ℝ) := by
  unfold EinLoQ EinLo; push_cast; rfl

lemma EinHiQ_cast (K : ℕ) (x : ℚ) : ((EinHiQ K x : ℚ) : ℝ) = EinHi K (x : ℝ) := by
  unfold EinHiQ EinHi; push_cast; rw [EinLoQ_cast]

lemma expLoQ_le {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : ((expLoQ n x : ℚ) : ℝ) ≤ Real.exp x := by
  unfold expLoQ; push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) n

/-! ## Part (2) -/

lemma Ei11_check :
    (2 / 3 : ℚ) + FX.logHiQF 11 + EinHiQ 40 11 - expLoQ 60 11 * (1 / 11 + 1 / 121) ≤ 134 := by
  decide +kernel

/-- **`rankin_R.py`, check (2a).** `Ei(11) - e¹¹/11 - e¹¹/121 ≤ 134`. -/
theorem Ei_11_le : Ei 11 - Real.exp 11 / 11 - Real.exp 11 / 121 ≤ 134 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog : Real.log 11 ≤ ((FX.logHiQF 11 : ℚ) : ℝ) := by
    have := FX.le_logHiQF (a := 11) (by norm_num); exact_mod_cast this
  have hEin : Ein 11 ≤ ((EinHiQ 40 11 : ℚ) : ℝ) := by
    rw [EinHiQ_cast]; push_cast
    exact Ein_le_EinHi (by norm_num) (by norm_num)
  have hexp : ((expLoQ 60 11 : ℚ) : ℝ) ≤ Real.exp 11 := by
    have := expLoQ_le (x := 11) (by norm_num) 60; exact_mod_cast this
  have hc := (Rat.cast_le (K := ℝ)).mpr Ei11_check
  push_cast at hc
  unfold Ei
  generalize ((FX.logHiQF 11 : ℚ) : ℝ) = a at *
  generalize ((EinHiQ 40 11 : ℚ) : ℝ) = b at *
  generalize ((expLoQ 60 11 : ℚ) : ℝ) = c at *
  linarith

lemma exp11_ge : (59000 : ℝ) ≤ Real.exp 11 := by
  have h := expLoQ_le (x := 11) (by norm_num) 30
  push_cast at h
  have hc : (59000 : ℚ) ≤ expLoQ 30 11 := by decide +kernel
  have hc' : (59000 : ℝ) ≤ ((expLoQ 30 11 : ℚ) : ℝ) := by exact_mod_cast hc
  linarith

/-- **`rankin_R.py`, check (2b)**, for every `x ≥ 11` (the script checks `x = 11` and uses the
monotonicity of the left side). -/
theorem f_lt_one {x : ℝ} (hx : 11 ≤ x) :
    2.75 / x + 134 * x ^ 2 * Real.exp (-x) < 1 := by
  set t := x - 11 with ht
  have ht0 : 0 ≤ t := by linarith
  have hxt : x = 11 + t := by linarith
  have hE := exp11_ge
  have hP : 1 + t + t ^ 2 / 2 + t ^ 3 / 6 ≤ Real.exp t := by
    have := Real.sum_le_exp_of_nonneg ht0 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hexp : Real.exp x = Real.exp 11 * Real.exp t := by rw [hxt, Real.exp_add]
  have hx0 : 0 < x := by linarith
  have hEx : 0 < Real.exp x := Real.exp_pos x
  have key : 134 * x ^ 3 < (x - 2.75) * Real.exp x := by
    have h1 : 59000 * (1 + t + t ^ 2 / 2 + t ^ 3 / 6) ≤ Real.exp x := by
      rw [hexp]
      have : 0 ≤ 1 + t + t ^ 2 / 2 + t ^ 3 / 6 := by positivity
      calc 59000 * (1 + t + t ^ 2 / 2 + t ^ 3 / 6) ≤ Real.exp 11 * Real.exp t := by
            apply mul_le_mul hE hP this (Real.exp_pos 11).le
        _ = Real.exp 11 * Real.exp t := rfl
    have h2 : 134 * x ^ 3 < (x - 2.75) * (59000 * (1 + t + t ^ 2 / 2 + t ^ 3 / 6)) := by
      rw [hxt]
      nlinarith [sq_nonneg t, mul_nonneg ht0 (sq_nonneg t), pow_nonneg ht0 4, pow_nonneg ht0 3]
    have h3 : 0 ≤ x - 2.75 := by linarith
    nlinarith
  rw [Real.exp_neg]
  have h1 : 134 * x ^ 2 * (Real.exp x)⁻¹ = 134 * x ^ 3 / (x * Real.exp x) := by
    field_simp
  have h2 : 2.75 / x = 2.75 * Real.exp x / (x * Real.exp x) := by
    field_simp
  rw [h1, h2, ← add_div, div_lt_one (by positivity)]
  nlinarith

/-- The consequence drawn in the proof of Lemma 6.22(c): `Ei(x) ≤ (eˣ/x)(1 + 2/x)` for
`x ≥ 11`. -/
theorem Ei_le_of_ge_11 {x : ℝ} (hx : 11 ≤ x) :
    Ei x ≤ Real.exp x / x * (1 + 2 / x) := by
  set G : ℝ → ℝ := fun y => Real.exp y / y + 2 * Real.exp y / y ^ 2 - Ei y with hG
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt G (Real.exp y * (y - 4) / y ^ 3) y := by
    intro y hy
    have h1 := (Real.hasDerivAt_exp y).div (hasDerivAt_id' y) hy.ne'
    have h2 := ((Real.hasDerivAt_exp y).const_mul 2).div (hasDerivAt_pow 2 y)
      (pow_ne_zero 2 hy.ne')
    have h3 := hasDerivAt_Ei hy
    convert (h1.add h2).sub h3 using 1
    field_simp
    ring
  have hmono : MonotoneOn G (Set.Ici 11) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => Real.exp y * (y - 4) / y ^ 3)
      (convex_Ici 11)
    · intro y hy
      exact (hderiv y (by simp at hy; linarith)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hderiv y (by simp at hy; linarith)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      simp at hy
      have : 0 < y := by linarith
      have : 0 ≤ y - 4 := by linarith
      positivity
  have hG11 : 0 ≤ G 11 := by
    have h := Ei_11_le
    have hE := exp11_ge
    simp only [hG]
    nlinarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [hG] at this hG11
  have hx0 : 0 < x := by linarith
  have e : Real.exp x / x * (1 + 2 / x) = Real.exp x / x + 2 * Real.exp x / x ^ 2 := by
    field_simp
  rw [e]
  linarith

/-! ## Part (3) -/

/-- **`rankin_R.py`, check (3a).** `(3/2)^{3/4} ≤ 1.3555`. -/
theorem three_halves_rpow_le : (3 / 2 : ℝ) ^ (3 / 4 : ℝ) ≤ 1.3555 := by
  have h0 : 0 ≤ (3 / 2 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma EiLog2_check :
    -1 ≤ (harmonic 1023 : ℚ) - 10 * (6931471808 / 10 ^ 10) + FX.logLoQF (6931471803 / 10 ^ 10)
      - 2 * (6931471808 / 10 ^ 10) + EinLoQ 30 (6931471803 / (4 * 10 ^ 10)) := by
  decide +kernel

/-- **`rankin_R.py`, check (3b).** `Ei(log 2 / 4) ≥ -1`. -/
theorem Ei_log2_div4_ge : -1 ≤ Ei (Real.log 2 / 4) := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  -- Euler's constant
  have hγ : (harmonic 1023 : ℝ) - 10 * (6931471808 / 10 ^ 10) < Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1023
    unfold Real.eulerMascheroniSeq at h
    have e : Real.log ((1023 : ℕ) + 1) = 10 * Real.log 2 := by
      rw [show ((1023 : ℕ) : ℝ) + 1 = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
    rw [e] at h
    have : 10 * Real.log 2 < 10 * (6931471808 / 10 ^ 10) := by norm_num at hl2 ⊢; linarith
    linarith
  -- `log (log 2 / 4)`
  have hlog : ((FX.logLoQF (6931471803 / 10 ^ 10) : ℚ) : ℝ) - 2 * (6931471808 / 10 ^ 10)
      ≤ Real.log (Real.log 2 / 4) := by
    rw [Real.log_div hl0.ne' (by norm_num)]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hA := FX.logLoQF_le (a := 6931471803 / 10 ^ 10) (by norm_num)
    have hB : Real.log (((6931471803 / 10 ^ 10 : ℚ)) : ℝ) ≤ Real.log (Real.log 2) := by
      apply Real.log_le_log (by norm_num)
      push_cast; norm_num at hl1 ⊢; linarith
    rw [h4]
    norm_num at hl2 ⊢
    linarith
  -- `Ein (log 2 / 4)`
  have hEin : ((EinLoQ 30 (6931471803 / (4 * 10 ^ 10)) : ℚ) : ℝ) ≤ Ein (Real.log 2 / 4) := by
    rw [EinLoQ_cast]
    refine le_trans (EinLo_mono (by norm_num) ?_ 30) (EinLo_le_Ein (by positivity) 30)
    push_cast; norm_num at hl1 ⊢; linarith
  have hc := (Rat.cast_le (K := ℝ)).mpr EiLog2_check
  push_cast at hc
  unfold Ei
  generalize ((FX.logLoQF (6931471803 / 10 ^ 10) : ℚ) : ℝ) = a at *
  generalize ((EinLoQ 30 (6931471803 / (4 * 10 ^ 10)) : ℚ) : ℝ) = b at *
  linarith

end BSCert.EiFn
