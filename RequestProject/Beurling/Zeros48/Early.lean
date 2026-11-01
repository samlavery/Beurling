module

public import RequestProject.Beurling.Construction.JitterRegular

/-!
# `D̂_{<a}` of step functions and of primitives (proof of Lemma 4.8(ii))

`D̂_{<a}(s) = s ∫_{(1,a]} D x^{-s-1} dx + D(a) a^{-s}` (`earlyNoise`) is `∫_{(1,a]} x^{-s} dD`.
Here:

* `earlyNoise_step`: for the unit step at `t ∈ [1, a]` it is `t^{-s}` (and `0` for `t > a`);
* `earlyNoise_sum_sub`: it is linear;
* `earlyNoise_primitive`: for `C = ∫_c^x g` on `[c, a]` (and `C = 0` on `(1, c)`) it is
  `∫_c^a g(u) u^{-s} du` (`Re s > 0`);
* `integral_cpow_eq_exp`: `∫_c^a g(u) u^{-z} du = ∫_{log c}^{log a} g(e^t) e^{(1-z)t} dt`.
-/

@[expose] public section

open Set Finset MeasureTheory Complex Decomp

namespace Zeros48


lemma continuousOn_cpow_Icc {c a : ℝ} (hc : 0 < c) (r : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) (Icc c a) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hc hx.1
  exact (Complex.continuousAt_ofReal_cpow_const x r (Or.inr hx0.ne')).continuousWithinAt

lemma integrableOn_cpow_Ioc {c a : ℝ} (hc : 0 < c) (r : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ r) (Ioc c a) :=
  ((continuousOn_cpow_Icc hc r).integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- **`D̂_{<a}` of a unit step** at `t ≥ 1`. -/
lemma earlyNoise_step {t a : ℝ} (ht : 1 ≤ t) (s : ℂ) :
    IntegrableOn (fun x : ℝ => (((if t ≤ x then 1 else 0 : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioc 1 a) ∧
    earlyNoise (fun x => if t ≤ x then 1 else 0) a s = if t ≤ a then (t : ℂ) ^ (-s) else 0 := by
  have e : (fun x : ℝ => (((if t ≤ x then 1 else 0 : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Set.Ici t).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) := by
    funext x; by_cases hx : t ≤ x <;> simp [hx, Set.indicator]
  have hint : IntegrableOn (fun x : ℝ => (((if t ≤ x then 1 else 0 : ℝ)) : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Set.Ioc 1 a) := by
    rw [e]; exact (integrableOn_cpow_Ioc one_pos _).indicator measurableSet_Ici
  refine ⟨hint, ?_⟩
  unfold earlyNoise
  have e' : (fun x : ℝ => (((if t ≤ x then (1 : ℝ) else 0 : ℝ)) : ℂ) *
      (x : ℂ) ^ (-s - 1)) =
      (Set.Ici t).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) := e
  simp only [e']
  rw [setIntegral_indicator measurableSet_Ici]
  by_cases hta : t ≤ a
  · rw [if_pos hta, if_pos hta]
    have hI : ∫ x in Set.Ioc 1 a ∩ Set.Ici t, (x : ℂ) ^ (-s - 1) =
        ∫ x in t..a, (x : ℂ) ^ (-s - 1) := by
      rw [intervalIntegral.integral_of_le hta]
      rcases eq_or_lt_of_le ht with h1 | h1
      · subst h1
        rw [Set.inter_eq_left.mpr (fun x (hx : x ∈ Set.Ioc (1 : ℝ) a) =>
          (show x ∈ Set.Ici (1 : ℝ) from hx.1.le))]
      · have : Set.Ioc 1 a ∩ Set.Ici t = Set.Icc t a := by
          ext x; simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
          constructor
          · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h2, h3⟩; exact ⟨⟨by linarith, h3⟩, h2⟩
        rw [this, integral_Icc_eq_integral_Ioc]
    rw [hI]
    simp only [Complex.ofReal_one, one_mul]
    by_cases hs : s = 0
    · subst hs; simp
    · rw [integral_cpow (Or.inr ⟨fun h => hs (by linear_combination -h), by
        rw [Set.uIcc_of_le hta]; intro h; linarith [h.1]⟩)]
      have : -s - 1 + 1 = -s := by ring
      rw [this]
      field_simp
      ring
  · rw [if_neg hta, if_neg hta]
    have : Set.Ioc 1 a ∩ Set.Ici t = ∅ := by
      ext x; simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, h2⟩, h3⟩; exact hta (h3.trans h2)
    rw [this]; simp

/-- **Linearity of `D̂_{<a}`.** -/
lemma earlyNoise_sum_sub {ι : Type*} (S : Finset ι) (D : ι → ℝ → ℝ) (E : ℝ → ℝ) (a : ℝ) (s : ℂ)
    (hD : ∀ i ∈ S, IntegrableOn (fun x : ℝ => (D i x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 a))
    (hE : IntegrableOn (fun x : ℝ => (E x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 a)) :
    earlyNoise (fun x => ∑ i ∈ S, D i x - E x) a s =
      ∑ i ∈ S, earlyNoise (D i) a s - earlyNoise E a s := by
  unfold earlyNoise
  have e : ∀ x : ℝ, (((∑ i ∈ S, D i x - E x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∑ i ∈ S, (D i x : ℂ) * (x : ℂ) ^ (-s - 1) - (E x : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x; push_cast; rw [sub_mul, Finset.sum_mul]
  simp only [e]
  rw [integral_sub (integrable_finset_sum _ hD) hE, integral_finset_sum _ hD]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_add_distrib]
  ring

/-- **`D̂_{<a}` of a primitive**: if `C = 0` on `(1, c)` and `C(x) = ∫_c^x g` on `[c, a]`, then
`D̂_{<a} C (s) = ∫_{(c,a]} g(u) u^{-s} du` for `Re s > 0`. -/
lemma earlyNoise_primitive {g C : ℝ → ℝ} {c a : ℝ} (hc : 1 ≤ c) (hca : c ≤ a)
    (hg : IntegrableOn g (Ioc c a)) (hC0 : ∀ x, 1 < x → x < c → C x = 0)
    (hC : ∀ x ∈ Icc c a, C x = ∫ u in c..x, g u) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (C x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioc 1 a) ∧
      earlyNoise C a s = ∫ u in Ioc c a, (g u : ℂ) * (u : ℂ) ^ (-s) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  set g' : ℝ → ℝ := (Set.Ioc c a).indicator g with hg'
  have hg'int : Integrable g' := (integrable_indicator_iff measurableSet_Ioc).mpr hg
  set G : ℝ → ℝ := fun x => ∫ u in c..x, g' u with hG
  have hGC : ∀ x ∈ Set.Icc c a, G x = C x := by
    intro x hx
    rw [hC x hx, hG]
    simp only
    rw [intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_of_le hx.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [hg', indicator_of_mem (show u ∈ Set.Ioc c a from ⟨hu.1, hu.2.trans hx.2⟩)]
  have hGa : ∀ x, a ≤ x → G x = G a := by
    intro x hx
    simp only [hG]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (hg'int.intervalIntegrable) (hg'int.intervalIntegrable)]
    have : ∫ u in a..x, g' u = 0 := by
      rw [intervalIntegral.integral_of_le hx]
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [hg', indicator_of_notMem]
      intro h; linarith [h.2, hu.1]
    rw [this, add_zero]
  -- integrability for `mellin_primitive`
  have hgw : IntegrableOn (fun u => g' u * u ^ (-s.re)) (Set.Ioi c) := by
    have hcont : ContinuousOn (fun u : ℝ => u ^ (-s.re)) (Set.Icc c a) := fun u hu =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (lt_of_lt_of_le hc0 hu.1).ne')).continuousWithinAt
    have h1 : IntegrableOn (fun u => g u * u ^ (-s.re)) (Set.Ioc c a) :=
      (((integrableOn_Icc_iff_integrableOn_Ioc).mpr hg).mul_continuousOn hcont
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have e : (fun u => g' u * u ^ (-s.re)) =
        (Set.Ioc c a).indicator (fun u => g u * u ^ (-s.re)) := by
      funext u; by_cases hu : u ∈ Set.Ioc c a <;> simp [hg', hu]
    rw [e]
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr h1).integrableOn
  obtain ⟨hI1, hmel⟩ := mellin_primitive hc0 hs hgw
  have hmel' : ∫ u in Set.Ioi c, (g' u : ℂ) * (u : ℂ) ^ (-s) =
      ∫ u in Set.Ioc c a, (g u : ℂ) * (u : ℂ) ^ (-s) := by
    have e : (fun u : ℝ => (g' u : ℂ) * (u : ℂ) ^ (-s)) =
        (Set.Ioc c a).indicator (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ (-s)) := by
      funext u; by_cases hu : u ∈ Set.Ioc c a <;> simp [hg', hu]
    rw [e, setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
  -- the integrand on `(c, a]` and on `(1, c]`
  set F : ℝ → ℂ := fun x => (C x : ℂ) * (x : ℂ) ^ (-s - 1) with hF
  set FG : ℝ → ℂ := fun x => ((∫ u in c..x, g' u : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
    with hFG
  have hFeq : EqOn F FG (Set.Ioc c a) := by
    intro x hx
    simp only [hF, hFG]
    rw [← hGC x ⟨hx.1.le, hx.2⟩]
  have hF1 : ∀ x ∈ Set.Ioo 1 c, F x = 0 := by
    intro x hx; simp only [hF, hC0 x hx.1 hx.2]; simp
  have hFint1 : IntegrableOn F (Set.Ioc 1 c) := by
    rw [(integrableOn_Ioc_iff_integrableOn_Ioo)]
    exact (integrableOn_zero).congr_fun (fun x hx => (hF1 x hx).symm) measurableSet_Ioo
  have hFint2 : IntegrableOn F (Set.Ioc c a) :=
    (hI1.mono_set Set.Ioc_subset_Ioi_self).congr_fun (fun x hx => (hFeq hx).symm) measurableSet_Ioc
  have hunion : Set.Ioc 1 c ∪ Set.Ioc c a = Set.Ioc 1 a := Set.Ioc_union_Ioc_eq_Ioc hc hca
  have hFint : IntegrableOn F (Set.Ioc 1 a) := by rw [← hunion]; exact hFint1.union hFint2
  refine ⟨hFint, ?_⟩
  have hzero : ∫ x in Set.Ioc 1 c, F x = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    exact setIntegral_eq_zero_of_forall_eq_zero hF1
  have hsplit : ∫ x in Set.Ioc 1 a, F x = ∫ x in Set.Ioc c a, F x := by
    rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hFint1
      hFint2, hzero, zero_add]
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le hc0 hca
  have htail : ∫ x in Set.Ioi a, FG x = (G a : ℂ) * ((a : ℂ) ^ (-s) / s) := by
    have e : ∀ x ∈ Set.Ioi a, FG x = (G a : ℂ) * (x : ℂ) ^ (-s - 1) := by
      intro x hx
      simp only [hFG]
      rw [show (∫ u in c..x, g' u) = G x from rfl, hGa x (le_of_lt hx)]
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_Ioi_cpow_of_lt (by simp; linarith) ha0]
    congr 1
    rw [show -s - 1 + 1 = -s by ring]
    field_simp
  have hGaC : G a = C a := hGC a ⟨hca, le_rfl⟩
  unfold earlyNoise
  rw [show (∫ x in Set.Ioc 1 a, (C x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      ∫ x in Set.Ioc 1 a, F x from rfl,
    hsplit, setIntegral_congr_fun measurableSet_Ioc hFeq]
  have hmel2 := hmel
  rw [hmel', ← Set.Ioc_union_Ioi_eq_Ioi hca, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hI1.mono_set Set.Ioc_subset_Ioi_self)
    (hI1.mono_set (Set.Ioi_subset_Ioi hca)), htail] at hmel2
  rw [← hmel2, ← hGaC]
  field_simp

/-- **Logarithmic coordinates**:
`∫_{(c,a]} g(u) u^{-z} du = ∫_{[log c, log a]} g(e^t) e^{(1-z)t} dt`. -/
lemma integral_cpow_eq_exp (g : ℝ → ℝ) {c a : ℝ} (hc : 0 < c) (hca : c ≤ a) (z : ℂ) :
    ∫ u in Ioc c a, (g u : ℂ) * (u : ℂ) ^ (-z) =
      ∫ t in Icc (Real.log c) (Real.log a), (g (Real.exp t) : ℂ) * cexp ((1 - z) * t) := by
  have hc' : Real.exp (Real.log c) = c := Real.exp_log hc
  have ha0 : 0 < a := lt_of_lt_of_le hc hca
  have himg : Real.exp '' Set.Icc (Real.log c) (Real.log a) = Set.Icc c a := by
    ext y
    simp only [mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by rw [← hc']; exact Real.exp_le_exp.mpr h1,
        by rw [← Real.exp_log ha0]; exact Real.exp_le_exp.mpr h2⟩
    · rintro ⟨h1, h2⟩
      have hy : 0 < y := lt_of_lt_of_le hc h1
      exact ⟨Real.log y, ⟨Real.log_le_log hc h1, Real.log_le_log hy h2⟩, Real.exp_log hy⟩
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Set.Icc (Real.log c) (Real.log a))
    (f := Real.exp) (f' := Real.exp) measurableSet_Icc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ (-z))
  rw [himg, integral_Icc_eq_integral_Ioc] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp,
    Complex.ofReal_exp]
  rw [show (cexp (t : ℂ)) * ((g (Real.exp t) : ℂ) * cexp ((t : ℂ) * -z)) =
    (g (Real.exp t) : ℂ) * (cexp (t : ℂ) * cexp ((t : ℂ) * -z)) by ring, ← Complex.exp_add]
  congr 2
  ring

end Zeros48

end
