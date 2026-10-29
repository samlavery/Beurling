module

public import RequestProject.Beurling.LocalPNT.Kernel
public import RequestProject.Beurling.LocalPNT.Inversion

/-!
# Step 10 of the proof of Theorem 5.24: the main term

`∫ φ dΠ₀ ≥ ∫_v^{v(1+η)} (1 - 1/u)/log u du ≥ η v/(1.0001 Λ_p)` for `Λ_p = log v ≥ 10⁵`,
`0 < η ≤ 1/2` (`pi0Int_lpWindow_ge`), and the integrability of `φ π₀` on `(1, ∞)`.
-/

@[expose] public section

open Set Real MeasureTheory

namespace LocalPNT

theorem pi0Int_lpWindow_ge {v η : ℝ} (hv1 : 1 < v) (hv : 10 ^ 5 ≤ Real.log v) (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) :
    IntegrableOn (fun u => lpWindow v η u * pi0Dens u) (Ioi 1) ∧
    η * v / (1.0001 * Real.log v) ≤ pi0Int (lpWindow v η) := by
  have hv0 : 0 < v := by linarith
  have hlv : 1 ≤ Real.log v := by linarith
  have hw := lpW_pos hlv hη
  have hwη := lpW_le hlv hη
  set w := lpW v η
  have hw1 : w ≤ 1 / 10 ^ 8 := by
    simp only [w, lpW]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (10 ^ 5 : ℝ) ^ 2 ≤ Real.log v ^ 2 := pow_le_pow_left₀ (by norm_num) hv 2
    nlinarith
  have hvbig : 10 ^ 4 ≤ v := by
    have := Real.add_one_le_exp (Real.log v); rw [Real.exp_log hv0] at this; linarith
  set A := v * (1 - w)
  set B := v * (1 + η + w)
  have hA1 : 1 < A := by simp only [A]; nlinarith
  have hAB : A ≤ B := by simp only [A, B]; nlinarith
  have hsupp : ∀ u, lpWindow v η u ≠ 0 → u ∈ Icc A B := fun u hu =>
    lpWindow_support hv1 hlv hη hη2 hu
  have hcont : ContinuousOn (fun u => lpWindow v η u * pi0Dens u) (Icc A B) := by
    refine ((continuousOn_lpWindow hv1 hlv hη hη2).mono fun u hu => ?_).mul
      (continuousOn_pi0Dens.mono fun u hu => ?_)
    · exact lt_trans (by linarith) (lt_of_lt_of_le hA1 hu.1)
    · exact lt_of_lt_of_le hA1 hu.1
  have hintAB : IntegrableOn (fun u => lpWindow v η u * pi0Dens u) (Icc A B) :=
    hcont.integrableOn_Icc
  have hint : IntegrableOn (fun u => lpWindow v η u * pi0Dens u) (Ioi 1) := by
    refine hintAB.of_forall_diff_eq_zero measurableSet_Ioi fun u hu => ?_
    by_contra hc
    have h1 : lpWindow v η u ≠ 0 := by intro e; apply hc; rw [e, zero_mul]
    exact hu.2 (hsupp u h1)
  refine ⟨hint, ?_⟩
  -- the lower bound on `[v, v(1+η)]`
  have hsub : Icc v (v * (1 + η)) ⊆ Ioi 1 := fun u hu => lt_of_lt_of_le hv1 hu.1
  have hnn : ∀ u ∈ Ioi (1 : ℝ), 0 ≤ lpWindow v η u * pi0Dens u := fun u hu =>
    mul_nonneg (lpWindow_bounds hv1 hlv hη hη2 u).1 (pi0Dens_nonneg hu)
  have h1 : ∫ u in Icc v (v * (1 + η)), lpWindow v η u * pi0Dens u ≤ pi0Int (lpWindow v η) :=
    setIntegral_mono_set hint ((ae_restrict_mem measurableSet_Ioi).mono hnn)
      (hsub.eventuallyLE)
  set c0 := (1 - 1 / v) / Real.log (v * (1 + η))
  have hlog : Real.log (v * (1 + η)) ≤ Real.log v + 1 := by
    rw [Real.log_mul hv0.ne' (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + η by linarith); linarith
  have hlog0 : 0 < Real.log (v * (1 + η)) := Real.log_pos (by nlinarith)
  have h2 : ∀ u ∈ Icc v (v * (1 + η)), c0 ≤ lpWindow v η u * pi0Dens u := by
    intro u hu
    rw [lpWindow_eq_one hv1 hlv hη hη2 hu, one_mul]
    have hu1 : 1 < u := lt_of_lt_of_le hv1 hu.1
    unfold pi0Dens
    have hlu : Real.log u ≤ Real.log (v * (1 + η)) := Real.log_le_log (by linarith) hu.2
    have hlu0 : 0 < Real.log u := Real.log_pos hu1
    have hnum : 1 - 1 / v ≤ 1 - 1 / u := by
      have : 1 / u ≤ 1 / v := one_div_le_one_div_of_le hv0 hu.1
      linarith
    have hnum0 : 0 ≤ 1 - 1 / v := by
      have : 1 / v ≤ 1 := by rw [div_le_one hv0]; linarith
      linarith
    simp only [c0]
    calc (1 - 1 / v) / Real.log (v * (1 + η)) ≤ (1 - 1 / v) / Real.log u :=
          div_le_div_of_nonneg_left hnum0 hlu0 hlu
      _ ≤ (1 - 1 / u) / Real.log u := div_le_div_of_nonneg_right hnum hlu0.le
  have h3 : ∫ u in Icc v (v * (1 + η)), c0 ≤
      ∫ u in Icc v (v * (1 + η)), lpWindow v η u * pi0Dens u :=
    setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hsub) measurableSet_Icc h2
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by nlinarith), smul_eq_mul] at h3
  have hfin : η * v / (1.0001 * Real.log v) ≤ (v * (1 + η) - v) * c0 := by
    simp only [c0]
    have e : (v * (1 + η) - v) = η * v := by ring
    rw [e, mul_div_assoc', div_le_div_iff₀ (by positivity) hlog0]
    have hvL : Real.log v + 1 ≤ v := by
      have := Real.add_one_le_exp (Real.log v); rwa [Real.exp_log hv0] at this
    have hv1' : 1 / v ≤ 1 / (Real.log v + 1) := one_div_le_one_div_of_le (by linarith) hvL
    have hηv : 0 < η * v := by positivity
    have hL0 : 0 < Real.log v + 1 := by linarith
    have hk : (1 - 1 / (Real.log v + 1)) * (1.0001 * Real.log v) ≥ Real.log v + 1 := by
      rw [one_sub_div hL0.ne', add_sub_cancel_right, div_mul_eq_mul_div, ge_iff_le,
        le_div_iff₀ hL0]
      nlinarith
    have : (1 - 1 / v) * (1.0001 * Real.log v) ≥ Real.log v + 1 := by nlinarith
    nlinarith
  linarith

end LocalPNT

end
