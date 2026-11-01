module

public import RequestProject.Beurling.LocalPNT.Extension

/-!
# Step 3 of the proof of Theorem 5.24: `∑_{n ≤ y} n^{-σ}` from (HBS)

From (HBS) on `[1, y]` (first branch of the error profile, `ε₁(v) ≤ 10 v^{-2/5} + κ + (κX₀+1)/v`)
and Abel summation, for `1 < σ ≤ 2`,

  `∑_{n ∈ 𝒩, n ≤ y} n^{-σ} ≤ (1 + 2κ)/(σ - 1) + 70`.

The paper has `1/η + 2.01`; any bound `(1 + o(1))/η + O(1)` serves (Step 3 and Step 7 use it
only through `|ζ^♯(1+η+it)| ≥ 0.98 η`).
-/

@[expose] public section

open Set Real MeasureTheory Construction

namespace LocalPNT

lemma alg_main (σ κ Y : ℝ) (h : σ - 1 ≠ 0) :
    σ * ((1 + κ) * ((1 - Y) / (σ - 1))) + (1 + κ) * Y =
      (1 + κ) * (1 + 1 / (σ - 1)) - (1 + κ) * Y * (1 / (σ - 1)) := by
  field_simp; ring

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- Real Abel summation over the elements `≤ y`. -/
lemma abel_elems_real {σ : ℝ} (hσ : 0 < σ) :
    σ * (∫ x in Ioc 1 y, P.N x * x ^ (-σ - 1)) + P.N y * y ^ (-σ) =
      ∑ e ∈ P.elems y, P.val e ^ (-σ) := by
  have hs : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hab := abel_elems P (y := y) hs
  have e1 : ∀ x ∈ Ioc (1 : ℝ) y, ((P.N x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((P.N x * x ^ (-σ - 1) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    push_cast
    rw [Complex.ofReal_cpow hx0]; push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc e1, integral_complex_ofReal] at hab
  have e2 : ((P.N y : ℝ) : ℂ) * (y : ℂ) ^ (-(σ : ℂ)) = ((P.N y * y ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hy0.le]; push_cast; ring_nf
  have e3 : ∀ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-(σ : ℂ)) = ((P.val e ^ (-σ) : ℝ) : ℂ) := by
    intro e _
    rw [Complex.ofReal_cpow (P.val_pos e).le]; push_cast; ring_nf
  rw [e2, Finset.sum_congr rfl e3] at hab
  exact_mod_cast hab

/-- `N(x) ≤ (1 + κ) x + 1_{x ≥ X₀⁻} (10 x^{0.6} + κX₀ + 1)` on `[1, y]`. -/
lemma N_le_majorant {x : ℝ} (hx1 : 1 ≤ x) (hxy : x ≤ y) :
    P.N x ≤ (1 + kap X₀) * x + (Ici Xm).indicator
      (fun x => 10 * x ^ (0.6 : ℝ) + kap X₀ * X₀ + 1) x := by
  have hκ := kappa_pos_aux h.logX
  have hx0 : 0 < x := by linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  rcases lt_or_ge x Xm with hlo | hhi
  · rw [h.N_low hlo, Set.indicator_of_notMem (by simpa using hlo)]; nlinarith
  · rw [Set.indicator_of_mem (by simpa using hhi)]
    have he := (abs_le.mp (h.hbs_err hhi hxy)).2
    rw [hbsEps_mul_self hx0] at he
    have hm := min_le_left (kappaParam (X₀ : ℝ) * x + kappaParam X₀ * X₀ + 1)
      (Rankin.smoothCount X₀ (2 * x) : ℝ)
    simp only [kap] at *
    linarith

set_option maxHeartbeats 1600000 in
/-- **`∑_{n ≤ y} n^{-σ} ≤ (1 + 2κ)/(σ - 1) + 70`** for `1 < σ ≤ 2`. -/
theorem sum_elems_rpow_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    ∑ e ∈ P.elems y, P.val e ^ (-σ) ≤ (1 + 2 * kap X₀) / (σ - 1) + 70 := by
  set κ := kap X₀
  have hκ : 0 < κ := kappa_pos_aux h.logX
  have hκ1 : κ ≤ 1 / 100 := (kappa_le_aux h.logX).trans (by
    rw [div_le_div_iff₀ (by nlinarith [h.logX]) (by norm_num)]; nlinarith [h.logX])
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  have hXm := h.Xm_pos
  have hX0 := h.X0_pos
  set F : ℝ → ℝ := fun x => (Ici Xm).indicator (fun x => 10 * x ^ (0.6 : ℝ) + κ * X₀ + 1) x
  -- integrability
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hiA : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi Xm) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hXm
  have hiB : IntegrableOn (fun x : ℝ => x ^ (0.6 - σ - 1)) (Ioi Xm) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hXm
  have hiC : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi Xm) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hXm
  have hrw : ∀ x ∈ Ioi (0 : ℝ), x * x ^ (-σ - 1) = x ^ (-σ) := by
    intro x hx; rw [Real.rpow_sub_one (ne_of_gt hx)]; field_simp [ne_of_gt hx.out]
  have hrw2 : ∀ x ∈ Ioi (0 : ℝ), x ^ (0.6 : ℝ) * x ^ (-σ - 1) = x ^ (0.6 - σ - 1) := by
    intro x hx; rw [← Real.rpow_add hx]; ring_nf
  -- the integral against the majorant
  set G : ℝ → ℝ := fun x => (1 + κ) * x ^ (-σ) + (Ici Xm).indicator
    (fun x => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) x
  have hiGi : IntegrableOn ((Ici Xm).indicator
      (fun x : ℝ => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1))) (Ioi 1) := by
    refine ((integrable_indicator_iff measurableSet_Ici).mpr ?_).integrableOn
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((hiB.const_mul 10).add (hiC.const_mul _))
  have hiG : IntegrableOn G (Ioi 1) := (hi1.const_mul _).add hiGi
  have hNm : Measurable P.N := (BeurlingSystem.N_mono P).measurable
  have hiN : IntegrableOn (fun x => P.N x * x ^ (-σ - 1)) (Ioc 1 y) := by
    refine Integrable.mono' (hiG.mono_set Ioc_subset_Ioi_self)
      ((hNm.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (BeurlingSystem.N_nonneg P x),
      abs_of_nonneg hp]
    have hb := h.N_le_majorant hx.1.le hx.2
    simp only [G]
    by_cases hm : x ∈ Ici Xm
    · rw [Set.indicator_of_mem hm] at hb ⊢
      rw [← hrw x hx0, ← hrw2 x hx0]; nlinarith
    · rw [Set.indicator_of_notMem hm] at hb ⊢
      rw [← hrw x hx0]; nlinarith
  have hGnn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ G x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.out]
    simp only [G]
    have : 0 ≤ (Ici Xm).indicator
        (fun x : ℝ => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) x := by
      apply Set.indicator_nonneg; intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hXm hz
      positivity
    positivity
  have hle1 : ∫ x in Ioc 1 y, P.N x * x ^ (-σ - 1) ≤ ∫ x in Ioc 1 y, G x := by
    refine setIntegral_mono_on hiN (hiG.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc ?_
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have hb := h.N_le_majorant hx.1.le hx.2
    simp only [G]
    by_cases hm : x ∈ Ici Xm
    · rw [Set.indicator_of_mem hm] at hb ⊢
      rw [← hrw x hx0, ← hrw2 x hx0]; nlinarith
    · rw [Set.indicator_of_notMem hm] at hb ⊢
      rw [← hrw x hx0]; nlinarith
  -- the integral of `G` over `(1, y]`: main part exactly, the rest over `(X₀⁻, ∞)`
  have hmain : ∫ x in Ioc 1 y, x ^ (-σ) = (1 - y ^ (1 - σ)) / (σ - 1) := by
    rw [← intervalIntegral.integral_of_le hy1, integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hy1]; intro h0; linarith [h0.1]⟩)]
    rw [Real.one_rpow, show -σ + 1 = 1 - σ by ring, show (1 : ℝ) - σ = -(σ - 1) by ring]
    rw [div_neg, ← neg_div, neg_sub]
  have hrest : ∫ x in Ioc 1 y, (Ici Xm).indicator
      (fun x : ℝ => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) x ≤
      10 * (Xm ^ (0.6 - σ) / (σ - 0.6)) + (κ * X₀ + 1) * (Xm ^ (-σ) / σ) := by
    calc _ ≤ ∫ x in Ioi 1, (Ici Xm).indicator
          (fun x : ℝ => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) x := by
          refine setIntegral_mono_set hiGi ?_ (Ioc_subset_Ioi_self).eventuallySubset
          refine (ae_restrict_mem measurableSet_Ioi).mono fun x _ => ?_
          apply Set.indicator_nonneg; intro z hz
          have hz0 : 0 < z := lt_of_lt_of_le hXm hz
          positivity
      _ = ∫ x in Ioi Xm, (10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) := by
          rw [setIntegral_indicator measurableSet_Ici]
          have : Ioi (1 : ℝ) ∩ Ici Xm = Ici Xm := by
            ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
            exact ⟨fun h => h.2, fun hx => ⟨by linarith [h.Xm_ge_e7], hx⟩⟩
          rw [this, integral_Ici_eq_integral_Ioi]
      _ = _ := by
          rw [integral_add (hiB.const_mul _) (hiC.const_mul _), integral_const_mul,
            integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hXm,
            integral_Ioi_rpow_of_lt (by linarith) hXm]
          rw [show 0.6 - σ - 1 + 1 = 0.6 - σ by ring, show -σ - 1 + 1 = -σ by ring]
          rw [show (0.6 : ℝ) - σ = -(σ - 0.6) by ring, div_neg, neg_div, neg_neg, div_neg,
            neg_div, neg_neg]
  have hIG : ∫ x in Ioc 1 y, G x = (1 + κ) * ((1 - y ^ (1 - σ)) / (σ - 1)) +
      ∫ x in Ioc 1 y, (Ici Xm).indicator
        (fun x : ℝ => 10 * x ^ (0.6 - σ - 1) + (κ * X₀ + 1) * x ^ (-σ - 1)) x := by
    simp only [G]
    rw [integral_add ((hi1.mono_set Ioc_subset_Ioi_self).const_mul _)
      (hiGi.mono_set Ioc_subset_Ioi_self), integral_const_mul, hmain]
  -- small quantities
  have hXmσ : Xm ^ (0.6 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [h.Xm_ge_e7]) (by linarith)
  have hXm2 : Xm ^ (-σ) ≤ Xm ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
    (by linarith [h.Xm_ge_e7]) (by linarith)
  have hXm1 : (κ * X₀ + 1) * Xm ^ (-1 : ℝ) ≤ 2 * κ + 1 := by
    rw [Real.rpow_neg_one]
    rw [mul_inv_le_iff₀ hXm]
    have := h.Xm_ge
    nlinarith [h.Xm_ge_e7]
  -- the boundary term
  have hNy := h.N_le_majorant hy1 le_rfl
  have hyσ : y * y ^ (-σ) = y ^ (1 - σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hy0, Real.rpow_one]
  have hy06 : y ^ (0.6 : ℝ) * y ^ (-σ) ≤ 1 := by
    rw [← Real.rpow_add hy0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hyX : (κ * X₀ + 1) * y ^ (-σ) ≤ 2 * κ + 1 := by
    have : y ^ (-σ) ≤ Xm ^ (-1 : ℝ) := (Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      linarith : -σ ≤ -1)).trans (Real.rpow_le_rpow_of_nonpos hXm (h.Xm_le.trans h.y_ge)
        (by norm_num))
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ κ * X₀ + 1)]
  have hBy : P.N y * y ^ (-σ) ≤ (1 + κ) * y ^ (1 - σ) + 10 + (2 * κ + 1) := by
    have hp : 0 ≤ y ^ (-σ) := Real.rpow_nonneg hy0.le _
    have hF : (Ici Xm).indicator (fun x => 10 * x ^ (0.6 : ℝ) + kap X₀ * X₀ + 1) y * y ^ (-σ)
        ≤ 10 + (2 * κ + 1) := by
      rw [Set.indicator_of_mem (by simpa using h.Xm_le.trans h.y_ge)]
      nlinarith
    calc P.N y * y ^ (-σ) ≤ ((1 + κ) * y + (Ici Xm).indicator
          (fun x => 10 * x ^ (0.6 : ℝ) + kap X₀ * X₀ + 1) y) * y ^ (-σ) :=
          mul_le_mul_of_nonneg_right hNy hp
      _ = (1 + κ) * (y * y ^ (-σ)) + (Ici Xm).indicator
          (fun x => 10 * x ^ (0.6 : ℝ) + kap X₀ * X₀ + 1) y * y ^ (-σ) := by ring
      _ ≤ _ := by rw [hyσ]; linarith
  rw [← h.abel_elems_real hσ0]
  have hσ06 : 0 < σ - 0.6 := by linarith
  have hyp : 0 ≤ y ^ (1 - σ) := Real.rpow_nonneg hy0.le _
  have hfrac : σ * (Xm ^ (0.6 - σ) / (σ - 0.6)) ≤ 5 := by
    rw [mul_div_assoc', div_le_iff₀ hσ06]; nlinarith [Real.rpow_nonneg hXm.le (0.6 - σ)]
  have hfrac2 : σ * ((κ * X₀ + 1) * (Xm ^ (-σ) / σ)) ≤ 2 * κ + 1 := by
    rw [show σ * ((κ * X₀ + 1) * (Xm ^ (-σ) / σ)) = (κ * X₀ + 1) * Xm ^ (-σ) by
      rw [mul_left_comm]; congr 1; field_simp]
    have := mul_le_mul_of_nonneg_left hXm2 (by positivity : (0 : ℝ) ≤ κ * X₀ + 1)
    linarith
  have hmainσ : σ * ((1 + κ) * ((1 - y ^ (1 - σ)) / (σ - 1))) + (1 + κ) * y ^ (1 - σ) ≤
      (1 + κ) * (1 + 1 / (σ - 1)) := by
    have hσ1' : 0 < σ - 1 := by linarith
    rw [alg_main σ κ _ hσ1'.ne']
    have : 0 ≤ (1 + κ) * y ^ (1 - σ) * (1 / (σ - 1)) := by positivity
    linarith
  have hI : ∫ x in Ioc 1 y, P.N x * x ^ (-σ - 1) ≤ (1 + κ) * ((1 - y ^ (1 - σ)) / (σ - 1)) +
      (10 * (Xm ^ (0.6 - σ) / (σ - 0.6)) + (κ * X₀ + 1) * (Xm ^ (-σ) / σ)) := by
    exact (hle1.trans hIG.le).trans (add_le_add le_rfl hrest)
  have hσ1' : 0 < σ - 1 := sub_pos.mpr hσ1
  have hfin : (1 + κ) * (1 / (σ - 1)) ≤ (1 + 2 * κ) / (σ - 1) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hσ1'.le
  clear hle1 hIG hrest hiN hiG hiGi hmain hNy
  clear_value G F
  generalize ∫ x in Ioc 1 y, P.N x * x ^ (-σ - 1) = I at hI ⊢
  generalize P.N y * y ^ (-σ) = Bd at hBy ⊢
  generalize Xm ^ (0.6 - σ) / (σ - 0.6) = A1 at hI hfrac ⊢
  generalize Xm ^ (-σ) / σ = A2 at hI hfrac2 ⊢
  generalize y ^ (1 - σ) = Y at hI hBy hmainσ hyp ⊢
  have h1 : σ * I ≤ σ * ((1 + κ) * ((1 - Y) / (σ - 1))) + 10 * (σ * A1) +
      σ * ((κ * X₀ + 1) * A2) := by
    have := mul_le_mul_of_nonneg_left hI hσ0.le; linarith
  linarith

end LPHyp

end LocalPNT

end
