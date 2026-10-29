module

public import RequestProject.Beurling.Noise.BSL57PPt
public import RequestProject.Beurling.Noise.BSL57PMom

/-!
# Lemma 5.7, remainder (a) (04c-saias.tex, lines 436-439): `remA : RemA`

`ρ₁ = E_π[(1 - e^{-κ_Φ/(wℓ)}) |D'|] ≤ y₁ E_π|D'|` with `y₁ = 1 - e^{-κ_Φ/((u-1)ℓ)}`; by (P1),
(P2) and the moments, `E_π|D'| ≤ (11Λ/ℓ)(4 + 393.5/u) + a'(1.2502 + 1.2502/u) +
(0.0314 + 2.2816/u)/√ℓ`; and `y₁ ≤ 3.673 Φ_ben` (`≤ 1.079 Φ_ben` for `u ≥ 27`), from
`Φ_ben ≥ (1 - e^{-κ_Φ/(uℓ)})(1 - 1/(ur(u)))` and concavity. The constants obtained,
`8119λ + 6.89α'` and `221λ + 1.40α'`, are below the paper's `13540λ + 7.6α'`, `540λ + 7.6α'`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- Concavity: `t (1 - e^{-z}) ≤ 1 - e^{-tz}` for `0 ≤ t ≤ 1`. -/
lemma one_sub_exp_concave {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - Real.exp (-z)) ≤ 1 - Real.exp (-(t * z)) := by
  have h := convexOn_exp.2 (Set.mem_univ (-z)) (Set.mem_univ 0) ht0 (by linarith : 0 ≤ 1 - t)
    (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have e : t * -z = -(t * z) := by ring
  rw [e] at h
  linarith

/-- `y₁ ≤ (u/(u-1)) (1 - 1/(u r(u)))⁻¹ Φ_ben`. -/
lemma LargeRange.y1_le (hR : LargeRange τ ℓ u) :
    (u - 1) / u * (1 - 1 / (u * Dickman.ratio u)) *
        (1 - Real.exp (-(kappa τ / ((u - 1) * ℓ)))) ≤ PhiBen τ ℓ u := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hPB := PhiBen_ge (τ := τ) (ℓ := ℓ) hu hκ hℓ0
  have ht0 : 0 ≤ (u - 1) / u := div_nonneg (by linarith) (by linarith)
  have ht1 : (u - 1) / u ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hc := one_sub_exp_concave (z := kappa τ / ((u - 1) * ℓ)) ht0 ht1
  have hu1 : u - 1 ≠ 0 := by linarith
  have e : (u - 1) / u * (kappa τ / ((u - 1) * ℓ)) = kappa τ / (u * ℓ) := by
    field_simp
  rw [e] at hc
  have hr := ratio_ge_one (v := u) (by linarith)
  have hm : 0 ≤ 1 - 1 / (u * Dickman.ratio u) := by
    rw [sub_nonneg, div_le_one (by nlinarith)]; nlinarith
  calc (u - 1) / u * (1 - 1 / (u * Dickman.ratio u)) *
        (1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))))
      = (1 - 1 / (u * Dickman.ratio u)) *
          ((u - 1) / u * (1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))))) := by ring
    _ ≤ (1 - 1 / (u * Dickman.ratio u)) * (1 - Real.exp (-(kappa τ / (u * ℓ)))) :=
        mul_le_mul_of_nonneg_left hc hm
    _ ≤ PhiBen τ ℓ u := by linarith

lemma LargeRange.y1_le_gen (hR : LargeRange τ ℓ u) :
    1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))) ≤ 3.673 * PhiBen τ ℓ u := by
  have hu := hR.2.2.2.1
  have h := hR.y1_le
  have hur := hR.ur_ge
  have hy0 : 0 ≤ 1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))) := by
    have : 0 ≤ kappa τ / ((u - 1) * ℓ) := by
      unfold kappa; have := hR.τ_pos; have := hR.ℓ_pos
      exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith [Real.exp_le_one_iff.mpr (by linarith : -(kappa τ / ((u - 1) * ℓ)) ≤ 0)]
  have h1 : 0.5 ≤ (u - 1) / u := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : 0.5446 ≤ 1 - 1 / (u * Dickman.ratio u) := by
    have : 1 / (u * Dickman.ratio u) ≤ 1 / 2.196 := one_div_le_one_div_of_le (by norm_num) hur
    norm_num at this ⊢; linarith
  have h3 : 0.2723 ≤ (u - 1) / u * (1 - 1 / (u * Dickman.ratio u)) := by nlinarith
  have := mul_le_mul_of_nonneg_right h3 hy0
  linarith

lemma LargeRange.y1_le_27 (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) :
    1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))) ≤ 1.079 * PhiBen τ ℓ u := by
  have h := hR.y1_le
  have hy0 : 0 ≤ 1 - Real.exp (-(kappa τ / ((u - 1) * ℓ))) := by
    have : 0 ≤ kappa τ / ((u - 1) * ℓ) := by
      unfold kappa; have := hR.τ_pos; have := hR.ℓ_pos
      exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith [Real.exp_le_one_iff.mpr (by linarith : -(kappa τ / ((u - 1) * ℓ)) ≤ 0)]
  have hr := ratio_ge_one (v := u) (by linarith)
  have h1 : 26 / 27 ≤ (u - 1) / u := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : 26 / 27 ≤ 1 - 1 / (u * Dickman.ratio u) := by
    have : 1 / (u * Dickman.ratio u) ≤ 1 / 27 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  have h3 : 0.9272 ≤ (u - 1) / u * (1 - 1 / (u * Dickman.ratio u)) := by nlinarith
  have := mul_le_mul_of_nonneg_right h3 hy0
  linarith

/-- `|D'| ≤ 4L + 1.2502a' + 0.0314/√ℓ` on the head, `L = 11Λ(u)/ℓ`. -/
lemma LargeRange.absDp_head (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    |Dp ℓ u w| ≤ 4 * (11 * Lam u / ℓ) + 1.2502 * aprime ℓ u + 0.0314 / √ℓ := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have h1 := hA_head_upper hu hw1 hwu
  have h2 := hA_head_lower hu hw1 hwu
  have h15 : (1 + u) / u ≤ 1.5 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : |hA u w| ≤ 4 * Lam u := by
    rw [abs_le]; constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_right h15 hΛ0]
  obtain ⟨hD, -⟩ := hR.Da_head hw1 hwu
  rw [Dp_eq_Da hℓ0 (by linarith)]
  have h4 : |11 / ℓ * hA u w| ≤ 4 * (11 * Lam u / ℓ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 11 / ℓ)]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
    have e : 11 / ℓ * (4 * Lam u) = 4 * (11 * Lam u / ℓ) := by ring
    linarith
  linarith [abs_add_le (11 / ℓ * hA u w) (Da ℓ u w)]

/-- `0 ≤ D' ≤ L((1+u)/u + 8s(1+s)³) + a'(s + 0.2502) + (s² + 0.2502 s + 0.0314)/√ℓ`
beyond `u`. -/
lemma LargeRange.Dp_tail (hR : LargeRange τ ℓ u) {w : ℝ} (huw : u ≤ w) :
    0 ≤ Dp ℓ u w ∧ Dp ℓ u w ≤ 11 * Lam u / ℓ * ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3)
      + aprime ℓ u * ((w - u) + 0.2502) + ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  obtain ⟨h1, h2⟩ := hA_tail hu huw
  obtain ⟨h3, h4⟩ := hR.Da_tail huw
  rw [Dp_eq_Da hℓ0 (by linarith)]
  have h5 : 11 / ℓ * hA u w ≤ 11 * Lam u / ℓ *
      ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3) := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 11 / ℓ)
    have e : 11 / ℓ * (Lam u * ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3)) =
        11 * Lam u / ℓ * ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3) := by ring
    linarith
  have h6 : 0 ≤ 11 / ℓ * hA u w := mul_nonneg (by positivity) h1
  constructor <;> linarith

/-- The tail coefficients of `y₁ |D'|`. -/
noncomputable def cA (y L h a q : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then y * (L * h + 0.2502 * a + 0.0314 * q) else
  if k = 1 then y * (8 * L + a + 0.2502 * q) else
  if k = 2 then y * (24 * L + q) else
  if k = 3 then y * (24 * L) else
  if k = 4 then y * (8 * L) else 0

lemma cA_nonneg {y L h a q : ℝ} (hy : 0 ≤ y) (hL : 0 ≤ L) (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (k : ℕ) : 0 ≤ cA y L h a q k := by
  unfold cA; split_ifs <;> positivity

lemma cA_poly (y L h a q t : ℝ) :
    ∑ k ∈ Finset.range 5, cA y L h a q k * t ^ k =
      y * (L * (h + 8 * t * (1 + t) ^ 3) + a * (t + 0.2502) + (t ^ 2 + 0.2502 * t + 0.0314) * q)
      := by
  simp [Finset.sum_range_succ, cA]; ring

lemma cA_mom (y L h a q : ℝ) :
    ∑ k ∈ Finset.range 5, cA y L h a q k * ((k.factorial : ℝ) / 1 ^ (k + 1)) =
      y * (L * (h + 392) + 1.2502 * a + 2.2816 * q) := by
  simp [Finset.sum_range_succ, cA, Nat.factorial]; ring

/-- `ρ₁ ≤ y₁ E` with `E = 4L + 1.2502a' + 0.0314/√ℓ + (L((1+u)/u + 392) + 1.2502a' +
2.2816/√ℓ)/u`. -/
lemma LargeRange.rho1_le (hR : LargeRange τ ℓ u) :
    rho1 τ ℓ u ≤ (1 - Real.exp (-(kappa τ / ((u - 1) * ℓ)))) *
      (4 * (11 * Lam u / ℓ) + 1.2502 * aprime ℓ u + 0.0314 * (1 / √ℓ) +
        (11 * Lam u / ℓ * ((1 + u) / u + 392) + 1.2502 * aprime ℓ u + 2.2816 * (1 / √ℓ)) / u)
      := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have hρ := Dickman.rho_pos (u - 1)
  set y := 1 - Real.exp (-(kappa τ / ((u - 1) * ℓ)))
  have hy0 : 0 ≤ y := by
    have : 0 ≤ kappa τ / ((u - 1) * ℓ) := div_nonneg hκ (mul_nonneg (by linarith) hℓ0.le)
    simp only [y]; linarith [Real.exp_le_one_iff.mpr (by linarith :
      -(kappa τ / ((u - 1) * ℓ)) ≤ 0)]
  -- the weight `1 - e^{-κ/(wℓ)} ∈ [0, y]` for `w > u - 1`
  have hwt : ∀ w, u - 1 < w → 0 ≤ 1 - Real.exp (-(kappa τ / (w * ℓ))) ∧
      1 - Real.exp (-(kappa τ / (w * ℓ))) ≤ y := by
    intro w hw
    have hw0 : 0 < w := by linarith
    constructor
    · have : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (by positivity)
      linarith [Real.exp_le_one_iff.mpr (by linarith : -(kappa τ / (w * ℓ)) ≤ 0)]
    · have : kappa τ / (w * ℓ) ≤ kappa τ / ((u - 1) * ℓ) :=
        div_le_div_of_nonneg_left hκ (mul_pos (by linarith) hℓ0)
          (mul_le_mul_of_nonneg_right hw.le hℓ0.le)
      simp only [y]; linarith [Real.exp_le_exp.mpr (by linarith :
        -(kappa τ / ((u - 1) * ℓ)) ≤ -(kappa τ / (w * ℓ)))]
  set L := 11 * Lam u / ℓ
  have hL : 0 ≤ L := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hh : 0 ≤ (1 + u) / u := by positivity
  have ha := hR.ap_nonneg
  have hq : 0 ≤ 1 / √ℓ := by have := hR.sqrt_pos; positivity
  have hm := master (u := u) (γ := 0) (A := y * (4 * L + 1.2502 * aprime ℓ u + 0.0314 * (1 / √ℓ)))
    hu (by linarith [hR.r0_ge_one]) (by have := hR.ap_nonneg; positivity) 5
    (cA y L ((1 + u) / u) (aprime ℓ u) (1 / √ℓ)) (cA_nonneg hy0 hL hh ha hq) (S := Ioi (u - 1))
    subset_rfl measurableSet_Ioi (f := fun w => (1 - Real.exp (-(kappa τ / (w * ℓ)))) *
      |Dp ℓ u w|) (int_R hR.2.2.1 hu hκ)
    (fun w hw => mul_nonneg (hwt w hw).1 (abs_nonneg _))
    (by
      intro w hw hwu
      have h1 := hR.absDp_head (w := w) (le_of_lt hw) hwu
      have e : 0.0314 * (1 / √ℓ) = 0.0314 / √ℓ := by ring
      rw [e]
      exact mul_le_mul (hwt w hw).2 h1 (abs_nonneg _) hy0)
    (by
      intro w hw huw
      obtain ⟨h0, h1⟩ := hR.Dp_tail huw.le
      beta_reduce
      rw [cA_poly, zero_mul, Real.exp_zero, mul_one, abs_of_nonneg h0]
      have e : ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ =
          ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) * (1 / √ℓ) := by ring
      rw [e] at h1
      exact mul_le_mul (hwt w hw).2 h1 h0 hy0)
  have hr1 := hR.r0_ge_one
  have hsum := momSum_le (r := Dickman.ratio (u - 1) - 0) (rmin := 1) one_pos (by linarith) 5
    (cA y L ((1 + u) / u) (aprime ℓ u) (1 / √ℓ)) (cA_nonneg hy0 hL hh ha hq)
  rw [cA_mom] at hsum
  unfold rho1 Epi
  rw [div_le_iff₀ hρ]
  have hu0 : 0 < u := by linarith
  have h2 : (∑ k ∈ Finset.range 5, cA y L ((1 + u) / u) (aprime ℓ u) (1 / √ℓ) k *
      ((k.factorial : ℝ) / (Dickman.ratio (u - 1) - 0) ^ (k + 1))) / u ≤
      y * (L * ((1 + u) / u + 392) + 1.2502 * aprime ℓ u + 2.2816 * (1 / √ℓ)) / u :=
    div_le_div_of_nonneg_right hsum hu0.le
  calc _ ≤ _ := hm
    _ ≤ Dickman.rho (u - 1) * (y * (4 * L + 1.2502 * aprime ℓ u + 0.0314 * (1 / √ℓ)) +
        y * (L * ((1 + u) / u + 392) + 1.2502 * aprime ℓ u + 2.2816 * (1 / √ℓ)) / u) := by
      gcongr
    _ = _ := by ring

/-- **Remainder (a)** (lines 436-439). -/
theorem remA : RemA := by
  intro τ ℓ u hR
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith [hR.τ_pos]
  have h := hR.rho1_le
  set y := 1 - Real.exp (-(kappa τ / ((u - 1) * ℓ)))
  have hy0 : 0 ≤ y := by
    have : 0 ≤ kappa τ / ((u - 1) * ℓ) := div_nonneg hκ (mul_nonneg (by linarith) hℓ0.le)
    simp only [y]; linarith [Real.exp_le_one_iff.mpr (by linarith :
      -(kappa τ / ((u - 1) * ℓ)) ≤ 0)]
  have hPB := PhiBen_nonneg (τ := τ) (ℓ := ℓ) hu hκ hℓ0
  have hΛ := hR.Lam_le
  have hL : 11 * Lam u / ℓ ≤ 11.011 * lamL τ ℓ := by
    rw [div_le_iff₀ hℓ0]; nlinarith
  have hL0 : 0 ≤ 11 * Lam u / ℓ := by have := Lam_nonneg (x := u) (by linarith); positivity
  have hap := hR.ap_le
  have ha0 := hR.ap_nonneg
  have hinv := hR.inv_sqrt_le
  have hq0 : 0 ≤ 1 / √ℓ := by have := hR.sqrt_pos; positivity
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hu0 : 0 < u := by linarith
  set L := 11 * Lam u / ℓ
  set a := aprime ℓ u
  set q := 1 / √ℓ
  set E := 4 * L + 1.2502 * a + 0.0314 * q + (L * ((1 + u) / u + 392) + 1.2502 * a +
    2.2816 * q) / u
  have hE0 : 0 ≤ E := by positivity
  -- `ℓ ρ₁ ≤ c (ℓΦ) E`
  have key : ∀ c : ℝ, y ≤ c * PhiBen τ ℓ u → ℓ * rho1 τ ℓ u ≤ c * E * (ℓ * PhiBen τ ℓ u) := by
    intro c hc
    have := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hc hE0)) hℓ0.le
    linarith
  constructor
  · refine (key 3.673 hR.y1_le_gen).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h15 : (1 + u) / u ≤ 1.5 := by rw [div_le_iff₀ hu0]; linarith
    have hE : E ≤ 200.75 * L + 1.8753 * a + 1.1722 * q := by
      have h1 : (L * ((1 + u) / u + 392) + 1.2502 * a + 2.2816 * q) / u ≤
          (L * 393.5 + 1.2502 * a + 2.2816 * q) / 2 := by
        rw [div_le_div_iff₀ hu0 (by norm_num)]
        have : L * ((1 + u) / u + 392) ≤ L * 393.5 := mul_le_mul_of_nonneg_left (by linarith) hL0
        nlinarith
      simp only [E]; linarith
    have hq : q ≤ alphaL τ ℓ / 63244 := hinv
    nlinarith
  · intro h27
    refine (key 1.079 (hR.y1_le_27 h27)).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h28 : (1 + u) / u ≤ 28 / 27 := by rw [div_le_iff₀ hu0]; linarith
    have hE : E ≤ 18.56 * L + 1.297 * a + 0.116 * q := by
      have h1 : (L * ((1 + u) / u + 392) + 1.2502 * a + 2.2816 * q) / u ≤
          (L * (28 / 27 + 392) + 1.2502 * a + 2.2816 * q) / 27 := by
        rw [div_le_div_iff₀ hu0 (by norm_num)]
        have : L * ((1 + u) / u + 392) ≤ L * (28 / 27 + 392) :=
          mul_le_mul_of_nonneg_left (by linarith) hL0
        nlinarith
      simp only [E]; linarith
    have hq : q ≤ alphaL τ ℓ / 63244 := hinv
    nlinarith

end BSaias.Large

end
