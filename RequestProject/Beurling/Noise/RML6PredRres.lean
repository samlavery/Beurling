module

public import RequestProject.Beurling.Noise.RML6Pred
public import RequestProject.Beurling.Noise.KRTrueSplit
public import RequestProject.Beurling.Noise.KRNear

/-!
# `R_res` of the kernels is the Neumann series of `(1 + K_pt B)⁻¹` (eq. (R-kernels))

The long operator of Proposition 5.26 is defined through the true kernels,
`Rres g (y) = g(y) + ∑_{n ≥ 2} n⁻¹ ∫ g dC_n^y` (`BridgeBR.lean`, densities `gK` with the filters
evaluated at the actual centres, `phiT`). This file proves the **last-step identity**

  `Rres (g + K_pt B g) = g`   (`Rres_last`),

from the last-step recursion of the kernels (`gK_eq`): the step `d → n` of the kernel, paired
with `g`, is `∫ φ_{d→n}(v/w) gK_d(v) (B g)(v/w) dv` (Fubini, `integral_mul_Qd`), and regrouping by
`n = d w` gives `K_pt B g` paired with `C_d`. With the Neumann series `Nop`
(`(1 + K_pt B) R g = g`, `Nop_spec`) this gives `Rres = R` on locally bounded measurable
functions (`Rres_eq_Nop`): the field `hRres`.
-/

@[expose] public section

open MeasureTheory Set Finset BeurlingSystem KR.Sharp

namespace KR.Ops

variable {H : ℝ → ℝ}

/-- `∫ f · kd(c, ·) = B f (c)`. -/
lemma integral_mul_kd (hH : WidthReg H) (f : ℝ → ℝ) (c : ℝ) :
    ∫ t, f t * kd H c t = Margin.Bavg (H c) f c := by
  have hHc := hH.pos c
  have e : (fun t => f t * kd H c t) =
      fun t => (H c)⁻¹ * (Ico (c - H c / 2) (c + H c / 2)).indicator f t := by
    funext t
    unfold kd Set.indicator
    split_ifs <;> ring
  rw [e, integral_const_mul, integral_indicator measurableSet_Ico,
    setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rfl

lemma abs_Bavg_le {f : ℝ → ℝ} {M h x : ℝ} (hh : 0 < h) (hM : ∀ t, |f t| ≤ M) :
    |Margin.Bavg h f x| ≤ M := by
  unfold Margin.Bavg
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x - h / 2) (b := x + h / 2)
    (C := M) (f := f) (fun s _ => by rw [Real.norm_eq_abs]; exact hM s)
  rw [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < x + h / 2 - (x - h / 2) by linarith)] at this
  rw [abs_mul, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * |∫ s in (x - h / 2)..(x + h / 2), f s| ≤ h⁻¹ * (M * (x + h / 2 - (x - h / 2))) :=
        mul_le_mul_of_nonneg_left this (inv_pos.mpr hh).le
    _ = M := by field_simp; ring

/-- **Fubini for the step**: `∫ f · Q_w ψ = ∫ ψ(v) (B f)(v/w) dv`. -/
lemma integral_mul_Qd (hH : WidthReg H) {ψ f : ℝ → ℝ} (hψ : Integrable ψ) (hψm : Measurable ψ)
    (hfm : Measurable f) {M : ℝ} (hfb : ∀ t, |f t| ≤ M) (w : ℝ) :
    ∫ t, f t * Qd H w ψ t = ∫ v, ψ v * Margin.Bavg (H (v / w)) f (v / w) := by
  have hint : Integrable (Function.uncurry fun t v => f t * (ψ v * kd H (v / w) t))
      (volume.prod volume) := by
    have h1 := integrable_prod_Qd hH w hψ hψm univ
    rw [Measure.restrict_univ] at h1
    refine h1.bdd_mul (c := M) (hfm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]; exact hfb p.1
  calc ∫ t, f t * Qd H w ψ t = ∫ t, ∫ v, f t * (ψ v * kd H (v / w) t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        unfold Qd; simp only; rw [integral_const_mul]
    _ = ∫ v, ∫ t, f t * (ψ v * kd H (v / w) t) := integral_integral_swap hint
    _ = ∫ v, ψ v * Margin.Bavg (H (v / w)) f (v / w) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only
        rw [← integral_mul_kd hH, ← integral_const_mul]
        congr 1; funext t; ring

/-! ## Supports and integrability -/

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m ε θ : ℝ}

lemma labelVal_two (hO : OpHyp P H X0m) : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun _ _ => hO.p2 _

/-- The support of the true kernel `C_n^y`: `gK ≠ 0` at `t` forces `0 < y`, `X₀⁻/2 ≤ y/n` and
`0.898 y/n ≤ t ≤ 1.102 y/n`. -/
lemma gK_supp (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {y : ℝ} {n : ℕ} {t : ℝ}
    (h : gK P.labelVal y H (phiT tw X0m) n t ≠ 0) :
    X0m / 2 ≤ y / Vl P n ∧ 0.898 * (y / Vl P n) ≤ t ∧ t ≤ 1.102 * (y / Vl P n) := by
  obtain ⟨h1, h2⟩ := gK_support hP (labelVal_two hO) (φ := phiT tw X0m)
    (fun d n c hc => trueFilter_ne_zero hc) n t h
  have hs := hP.small _ h1
  unfold posn at h1 h2 hs
  rw [abs_le] at h2
  exact ⟨h1, by constructor <;> nlinarith [h2.1, h2.2]⟩

lemma y_pos_of_gK (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {y : ℝ} {n : ℕ} {t : ℝ}
    (h : gK P.labelVal y H (phiT tw X0m) n t ≠ 0) : 0 < y := by
  have h1 := (gK_supp hO hP h).1
  have hX := hO.X0m_pos
  have hV := Vl_pos P n
  have : 0 < y / Vl P n := by linarith
  exact (div_pos_iff_of_pos_right hV).mp this

lemma integrable_mul_gK (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ} (hf : KR.BM f) (y : ℝ)
    (n : ℕ) : Integrable fun t => f t * gK P.labelVal y H (phiT tw X0m) n t := by
  obtain ⟨hfm, M, hM⟩ := hf
  exact (integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hP.reg n).1.bdd_mul
    (c := M) hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact hM t)

/-- `B f` is bounded and measurable for bounded measurable `f`. -/
lemma BM_Bavg (hO : OpHyp P H X0m) {f : ℝ → ℝ} (hf : KR.BM f) :
    KR.BM fun s => Margin.Bavg (H s) f s := by
  obtain ⟨hfm, M, hM⟩ := hf
  have hloc : f ∈ LocInt := fun a b =>
    (intervalIntegrable_const (c := M)).mono_fun hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        simp only [Real.norm_eq_abs]; exact (hM t).trans (le_abs_self M))
  exact ⟨(continuous_Bavg hO.cont hO.pos hloc).measurable, M, fun s =>
    abs_Bavg_le (hO.pos s) hM⟩

/-- On `(-∞, c]`, `K_pt g` agrees with a bounded measurable function, for `g` bounded measurable. -/
lemma Kpt_BM_on (hO : OpHyp P H X0m) {g : ℝ → ℝ} (hg : KR.BM g) (c : ℝ) :
    ∃ S : ℝ → ℝ, KR.BM S ∧ ∀ t ≤ c, Kpt P tw X0m g t = S t := by
  set S := ∑ w ∈ (NAll P c X0m).filter (2 ≤ ·),
      (Sw (P := P) (tw := tw) (X0m := X0m) w).indicator (fun t => g (t / Vl P w) / Vl P w)
  refine ⟨S, ?_, fun t ht => by simp only [S, Finset.sum_apply]; exact Kpt_eq_on hO.X0m_pos g ht⟩
  have hterm : ∀ w ∈ (NAll P c X0m).filter (2 ≤ ·), KR.BM
      ((Sw (P := P) (tw := tw) (X0m := X0m) w).indicator (fun t => g (t / Vl P w) / Vl P w)) := by
    intro w _
    obtain ⟨hgm, M, hM⟩ := hg
    have hV := Vl_pos P w
    refine ⟨((hgm.comp (measurable_id.div_const _)).div_const _).indicator (measurableSet_Sw w),
      M / Vl P w, fun t => ?_⟩
    unfold Set.indicator
    split_ifs
    · rw [abs_div, abs_of_pos hV]; exact div_le_div_of_nonneg_right (hM _) hV.le
    · simp only [abs_zero]; exact div_nonneg ((abs_nonneg _).trans (hM 0)) hV.le
  have := KR.BM.finset_sum _ hterm
  have e : S = fun t => ∑ w ∈ (NAll P c X0m).filter (2 ≤ ·),
      (Sw (P := P) (tw := tw) (X0m := X0m) w).indicator (fun t => g (t / Vl P w) / Vl P w) t := by
    funext t; simp only [S, Finset.sum_apply]
  rw [e]; exact this

/-- `K_pt g · C_d` is integrable for `g` bounded measurable. -/
lemma integrable_Kpt_mul_gK (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {g : ℝ → ℝ}
    (hg : KR.BM g) (y : ℝ) (d : ℕ) :
    Integrable fun t => Kpt P tw X0m g t * gK P.labelVal y H (phiT tw X0m) d t := by
  obtain ⟨S, hS, hSeq⟩ := Kpt_BM_on (tw := tw) hO hg (2 * |y|)
  have e : (fun t => Kpt P tw X0m g t * gK P.labelVal y H (phiT tw X0m) d t) =
      fun t => S t * gK P.labelVal y H (phiT tw X0m) d t := by
    funext t
    by_cases h : gK P.labelVal y H (phiT tw X0m) d t = 0
    · rw [h, mul_zero, mul_zero]
    · have hs := gK_supp (tw := tw) hO hP h
      have hy := y_pos_of_gK (tw := tw) hO hP h
      have hV : 1 ≤ Vl P d := LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)
      have : y / Vl P d ≤ y := div_le_self hy.le hV
      rw [hSeq t (by rw [abs_of_pos hy]; nlinarith [hs.2.2])]
  rw [e]
  exact integrable_mul_gK hP hS y d

/-! ## The kernel steps paired with `f` -/

lemma phiT_meas (d n : ℕ) : Measurable (phiT tw X0m d n) := ((trueFilter_ok tw X0m) d n).1

lemma phiT_abs (d n : ℕ) (c : ℝ) : |phiT tw X0m d n c| ≤ 1 := by
  have := ((trueFilter_ok tw X0m) d n).2 c
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

lemma stepK_integrable (hP : PaperWidth H X0m ε θ) (y : ℝ) (d n : ℕ) :
    Integrable (stepK P.labelVal y H (phiT tw X0m) d n) := by
  have hH := hP.reg
  by_cases h1 : d = 1
  · have e : stepK P.labelVal y H (phiT tw X0m) d n = fun t =>
        phiT tw X0m 1 n (posn P.labelVal y n) * kd H (posn P.labelVal y n) t := by
      funext t; unfold stepK; rw [if_pos h1]
    rw [e]; exact (integrable_kd hH _).const_mul _
  · have e : stepK P.labelVal y H (phiT tw X0m) d n = Qd H (LemmaM.valN P.labelVal (n / d))
        (fun v => phiT tw X0m d n (v / LemmaM.valN P.labelVal (n / d)) *
          gK P.labelVal y H (phiT tw X0m) d v) := by
      funext t; unfold stepK; rw [if_neg h1]
    rw [e]
    have hg := integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hH d
    exact integrable_Qd hH _ (integrable_mul_comp (phiT_meas d n) (phiT_abs d n) hg.1 _)
      (measurable_mul_comp (phiT_meas d n) hg.2 _)

/-- The step `1 → n` paired with `f`: `φ_{1→n}(y/n) (B f)(y/n)`. -/
lemma integral_step_one (hP : PaperWidth H X0m ε θ) (f : ℝ → ℝ) (y : ℝ) (n : ℕ) :
    ∫ t, f t * stepK P.labelVal y H (phiT tw X0m) 1 n t =
      phiT tw X0m 1 n (posn P.labelVal y n) *
        Margin.Bavg (H (posn P.labelVal y n)) f (posn P.labelVal y n) := by
  have e : (fun t => f t * stepK P.labelVal y H (phiT tw X0m) 1 n t) = fun t =>
      phiT tw X0m 1 n (posn P.labelVal y n) * (f t * kd H (posn P.labelVal y n) t) := by
    funext t; unfold stepK; rw [if_pos rfl]; ring
  rw [e, integral_const_mul, integral_mul_kd hP.reg]

/-- The step `d → n` (`d ≠ 1`) paired with `f`: `∫ φ_{d→n}(v/w) C_d(v) (B f)(v/w) dv`. -/
lemma integral_step (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ} (hf : KR.BM f) (y : ℝ) {d n : ℕ}
    (hd : d ≠ 1) :
    ∫ t, f t * stepK P.labelVal y H (phiT tw X0m) d n t =
      ∫ v, phiT tw X0m d n (v / LemmaM.valN P.labelVal (n / d)) *
        gK P.labelVal y H (phiT tw X0m) d v *
          Margin.Bavg (H (v / LemmaM.valN P.labelVal (n / d))) f
            (v / LemmaM.valN P.labelVal (n / d)) := by
  have hH := hP.reg
  obtain ⟨hfm, M, hM⟩ := hf
  have e : stepK P.labelVal y H (phiT tw X0m) d n = Qd H (LemmaM.valN P.labelVal (n / d))
      (fun v => phiT tw X0m d n (v / LemmaM.valN P.labelVal (n / d)) *
        gK P.labelVal y H (phiT tw X0m) d v) := by
    funext t; unfold stepK; rw [if_neg hd]
  have hg := integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hH d
  rw [e, integral_mul_Qd hH (integrable_mul_comp (phiT_meas d n) (phiT_abs d n) hg.1 _)
    (measurable_mul_comp (phiT_meas d n) hg.2 _) hfm hM]

/-- `∫ f C_n = -∑_{d ∣ n, d < n} ∫ f · step(d → n)` for `n ≥ 2`. -/
lemma integral_mul_gK_eq (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ} (hf : KR.BM f) (y : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    ∫ t, f t * gK P.labelVal y H (phiT tw X0m) n t =
      -∑ d ∈ n.properDivisors, ∫ t, f t * stepK P.labelVal y H (phiT tw X0m) d n t := by
  obtain ⟨hfm, M, hM⟩ := hf
  have e : (fun t => f t * gK P.labelVal y H (phiT tw X0m) n t) = fun t =>
      -∑ d ∈ n.properDivisors, f t * stepK P.labelVal y H (phiT tw X0m) d n t := by
    funext t; rw [gK_eq P.labelVal y H hn, mul_neg, Finset.mul_sum]
  rw [e, integral_neg, integral_finset_sum]
  intro d _
  exact (stepK_integrable hP y d n).bdd_mul (c := M) hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hM t)

/-! ## Regrouping by `n = d w` -/

lemma one_le_Vl (n : ℕ) : 1 ≤ Vl P n := LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)

lemma Vl_le_of_dvd {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) : Vl P d ≤ Vl P n :=
  LemmaM.valN_le_of_dvd _ (fun r _ => P.one_le_labelVal r) hd hn

lemma mem_levels {X0m y : ℝ} (hX : 0 < X0m) {n : ℕ} :
    n ∈ levels P X0m y ↔ 2 ≤ n ∧ Vl P n ≤ y / (X0m / 2) := by
  unfold levels
  rw [Finset.mem_filter, mem_NAll_iff P (by linarith : 0 < X0m / 2)]
  constructor
  · rintro ⟨⟨-, h⟩, h2⟩; exact ⟨h2, h⟩
  · rintro ⟨h2, h⟩; exact ⟨⟨by omega, h⟩, h2⟩

/-- The pairs `(n, d)` with `n` a level and `d ∣ n`, `1 < d < n`, are the pairs `(d w, d)` with
`d`, `w` levels and `d w` a level. -/
lemma regroup {y : ℝ} (hX : 0 < X0m) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ levels P X0m y, ∑ d ∈ (n.properDivisors).erase 1, F n d =
      ∑ d ∈ levels P X0m y, ∑ w ∈ (levels P X0m y).filter (fun w => d * w ∈ levels P X0m y),
        F (d * w) d := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 / p.2⟩) (fun q => ⟨q.1 * q.2, q.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_erase, Nat.mem_properDivisors] at hp
    obtain ⟨hn, hd1, hdn, hdlt⟩ := hp
    obtain ⟨hn2, hnV⟩ := (mem_levels (P := P) hX).mp hn
    have hn0 : n ≠ 0 := by omega
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
    have hd2 : 2 ≤ d := by omega
    have hk := Nat.mul_div_cancel' hdn
    have hw2 : 2 ≤ n / d := two_le_div_of_mem (Nat.mem_properDivisors.mpr ⟨hdn, hdlt⟩)
    simp only [Finset.mem_sigma, Finset.mem_filter]
    refine ⟨(mem_levels (P := P) hX).mpr ⟨hd2, (Vl_le_of_dvd (P := P) hdn hn0).trans hnV⟩,
      (mem_levels (P := P) hX).mpr ⟨hw2,
        (Vl_le_of_dvd (P := P) (Nat.div_dvd_of_dvd hdn) hn0).trans hnV⟩, ?_⟩
    rw [hk]; exact hn
  · rintro ⟨d, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter] at hq
    obtain ⟨hd, hw, hdw⟩ := hq
    obtain ⟨hd2, -⟩ := (mem_levels (P := P) hX).mp hd
    obtain ⟨hw2, -⟩ := (mem_levels (P := P) hX).mp hw
    simp only [Finset.mem_sigma, Finset.mem_erase, Nat.mem_properDivisors]
    refine ⟨hdw, by omega, dvd_mul_right d w, by nlinarith⟩
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_erase, Nat.mem_properDivisors] at hp
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact Nat.mul_div_cancel' hp.2.2.1
  · rintro ⟨d, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter] at hq
    have hd2 := ((mem_levels (P := P) hX).mp hq.1).1
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Nat.mul_div_cancel_left w (by omega)
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_erase, Nat.mem_properDivisors] at hp
    show F n d = F (d * (n / d)) d
    rw [Nat.mul_div_cancel' hp.2.2.1]

/-- At a point `v` of the support of `C_d`, `K_pt g (v)` is the sum over the cofactors `w` with
`d w` a level of the step filters `φ_{d → d w}(v/w) g(v/w)/w`. -/
lemma Kpt_eq_Wsum (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {y : ℝ} {d : ℕ}
    (hd : d ∈ levels P X0m y) {v : ℝ} (hv : gK P.labelVal y H (phiT tw X0m) d v ≠ 0)
    (g : ℝ → ℝ) :
    Kpt P tw X0m g v = ∑ w ∈ (levels P X0m y).filter (fun w => d * w ∈ levels P X0m y),
      phiT tw X0m d (d * w) (v / Vl P w) * g (v / Vl P w) / Vl P w := by
  classical
  have hX := hO.X0m_pos
  obtain ⟨hs1, -, hs3⟩ := gK_supp (tw := tw) hO hP hv
  have hy := y_pos_of_gK (tw := tw) hO hP hv
  obtain ⟨hd2, -⟩ := (mem_levels (P := P) hX).mp hd
  have hVd := Vl_pos P d
  have hsub : (NAll P v X0m).filter (2 ≤ ·) ⊆
      (levels P X0m y).filter (fun w => d * w ∈ levels P X0m y) := by
    intro w hw
    obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
    have hVw := ((mem_NAll_iff P hX).mp hwN).2
    have hw0 : w ≠ 0 := by omega
    have hd0 : d ≠ 0 := by omega
    have hVdw : Vl P (d * w) = Vl P d * Vl P w := Vl_mul P hd0 hw0
    have hbound : Vl P d * Vl P w ≤ y / (X0m / 2) := by
      rw [le_div_iff₀ (by linarith)]
      rw [le_div_iff₀ hX] at hVw
      have : Vl P d * v ≤ 1.102 * y := by
        have := mul_le_mul_of_nonneg_left hs3 hVd.le
        have e : Vl P d * (1.102 * (y / Vl P d)) = 1.102 * y := by field_simp
        rwa [e] at this
      nlinarith [Vl_pos P w]
    refine Finset.mem_filter.mpr ⟨(mem_levels (P := P) hX).mpr ⟨hw2, ?_⟩,
      (mem_levels (P := P) hX).mpr ⟨by nlinarith, by rw [hVdw]; exact hbound⟩⟩
    have := one_le_Vl (P := P) d
    nlinarith [Vl_pos P w]
  unfold Kpt
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
    have hcut := (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hwN).2
    have hVw := Vl_pos P w
    unfold phiT trueFilter
    rw [Nat.mul_div_cancel_left w (by omega)]
    by_cases hc : ∀ p ∈ w.primeFactors, tw p * Vl P w < v
    · rw [if_pos hc, if_pos ⟨fun p hp => by rw [lt_div_iff₀ hVw]; exact hc p hp, hcut⟩]; ring
    · rw [if_neg hc, if_neg (fun h => hc fun p hp => by
        have := h.1 p hp; rwa [lt_div_iff₀ hVw] at this)]; ring
  · intro w hw hnot
    obtain ⟨hwL, -⟩ := Finset.mem_filter.mp hw
    have hw2 := ((mem_levels (P := P) hX).mp hwL).1
    have hnc : ¬ X0m ≤ v / Vl P w := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨(mem_NAll_iff P hX).mpr ⟨by omega,
        (le_div_iff_cut P hX).mpr h⟩, hw2⟩)
    unfold phiT trueFilter
    rw [if_neg (fun h => hnc h.2)]; ring

/-! ## The last-step identity -/

/-- The steps `1 → n` regroup into `K_pt B f (y)`. -/
lemma sum_step_one (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (f : ℝ → ℝ) (y : ℝ) :
    ∑ n ∈ levels P X0m y, (∫ t, f t * stepK P.labelVal y H (phiT tw X0m) 1 n t) / Vl P n =
      Kpt P tw X0m (fun s => Margin.Bavg (H s) f s) y := by
  classical
  have hX := hO.X0m_pos
  simp_rw [integral_step_one hP f y]
  unfold Kpt
  have hsub : (NAll P y X0m).filter (2 ≤ ·) ⊆ levels P X0m y := by
    intro w hw
    obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
    have hV := ((mem_NAll_iff P hX).mp hwN).2
    have hVp := Vl_pos P w
    have hy : 0 ≤ y := by
      rw [le_div_iff₀ hX] at hV; nlinarith
    refine (mem_levels (P := P) hX).mpr ⟨hw2, hV.trans ?_⟩
    exact div_le_div_of_nonneg_left hy (by linarith) (by linarith)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hwN, -⟩ := Finset.mem_filter.mp hw
    have hcut := (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hwN).2
    have hVw := Vl_pos P w
    show trueFilter tw X0m 1 w (y / Vl P w) *
      Margin.Bavg (H (y / Vl P w)) f (y / Vl P w) / Vl P w = _
    unfold trueFilter
    rw [Nat.div_one]
    by_cases hc : ∀ p ∈ w.primeFactors, tw p * Vl P w < y
    · rw [if_pos hc, if_pos ⟨fun p hp => by rw [lt_div_iff₀ hVw]; exact hc p hp, hcut⟩]; ring
    · rw [if_neg hc, if_neg (fun h => hc fun p hp => by
        have := h.1 p hp; rwa [lt_div_iff₀ hVw] at this)]; ring
  · intro w hw hnot
    have hw2 := ((mem_levels (P := P) hX).mp hw).1
    have hnc : ¬ X0m ≤ y / Vl P w := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨(mem_NAll_iff P hX).mpr ⟨by omega,
        (le_div_iff_cut P hX).mpr h⟩, hw2⟩)
    show trueFilter tw X0m 1 w (y / Vl P w) *
      Margin.Bavg (H (y / Vl P w)) f (y / Vl P w) / Vl P w = 0
    unfold trueFilter
    rw [if_neg (fun h => hnc h.2)]; ring

/-- The steps `d → n`, `d ≠ 1`, regroup into `∑_d d⁻¹ ∫ (K_pt B f) dC_d`. -/
lemma sum_steps (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ} (hf : KR.BM f)
    (y : ℝ) :
    ∑ n ∈ levels P X0m y, ∑ d ∈ (n.properDivisors).erase 1,
        (∫ t, f t * stepK P.labelVal y H (phiT tw X0m) d n t) / Vl P n =
      ∑ d ∈ levels P X0m y, (∫ t, Kpt P tw X0m (fun s => Margin.Bavg (H s) f s) t *
        gK P.labelVal y H (phiT tw X0m) d t) / Vl P d := by
  classical
  have hX := hO.X0m_pos
  have hBf := BM_Bavg hO hf
  set Bf := fun s => Margin.Bavg (H s) f s
  -- the steps as integrals against `C_d`
  have hstep : ∀ n ∈ levels P X0m y, ∀ d ∈ (n.properDivisors).erase 1,
      (∫ t, f t * stepK P.labelVal y H (phiT tw X0m) d n t) / Vl P n =
        (∫ v, phiT tw X0m d n (v / Vl P (n / d)) * gK P.labelVal y H (phiT tw X0m) d v *
          Bf (v / Vl P (n / d))) / Vl P n := by
    intro n _ d hd
    rw [integral_step hP hf y (Finset.mem_erase.mp hd).1]
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl (hstep n hn)]
  rw [regroup (P := P) hX (fun n d => (∫ v, phiT tw X0m d n (v / Vl P (n / d)) *
    gK P.labelVal y H (phiT tw X0m) d v * Bf (v / Vl P (n / d))) / Vl P n)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd2 := ((mem_levels (P := P) hX).mp hd).1
  have hd0 : d ≠ 0 := by omega
  have hVd := Vl_pos P d
  have hg := integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hP.reg d
  obtain ⟨hBm, MB, hMB⟩ := hBf
  -- each term, rewritten with `d w / d = w`, `V (d w) = V d V w`
  have hterm : ∀ w ∈ (levels P X0m y).filter (fun w => d * w ∈ levels P X0m y),
      (∫ v, phiT tw X0m d (d * w) (v / Vl P (d * w / d)) * gK P.labelVal y H (phiT tw X0m) d v *
          Bf (v / Vl P (d * w / d))) / Vl P (d * w) =
        (∫ v, gK P.labelVal y H (phiT tw X0m) d v *
          (phiT tw X0m d (d * w) (v / Vl P w) * Bf (v / Vl P w) / Vl P w)) / Vl P d := by
    intro w hw
    have hw2 := ((mem_levels (P := P) hX).mp (Finset.mem_filter.mp hw).1).1
    have hw0 : w ≠ 0 := by omega
    have hVw := Vl_pos P w
    rw [Nat.mul_div_cancel_left w (by omega), Vl_mul P hd0 hw0]
    have e : (fun v => gK P.labelVal y H (phiT tw X0m) d v *
        (phiT tw X0m d (d * w) (v / Vl P w) * Bf (v / Vl P w) / Vl P w)) =
        fun v => (Vl P w)⁻¹ * (phiT tw X0m d (d * w) (v / Vl P w) *
          gK P.labelVal y H (phiT tw X0m) d v * Bf (v / Vl P w)) := by
      funext v; field_simp
    rw [e, integral_const_mul]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only
    by_cases hv : gK P.labelVal y H (phiT tw X0m) d v = 0
    · rw [hv]; simp
    · rw [Kpt_eq_Wsum hO hP hd hv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => by ring
  · intro w _
    have hb : ∀ v, ‖phiT tw X0m d (d * w) (v / Vl P w) * Bf (v / Vl P w) / Vl P w‖ ≤ MB := by
      intro v
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Vl_pos P w)]
      have h1 := phiT_abs (tw := tw) (X0m := X0m) d (d * w) (v / Vl P w)
      have h2 := hMB (v / Vl P w)
      have h3 := one_le_Vl (P := P) w
      have h4 : |phiT tw X0m d (d * w) (v / Vl P w)| * |Bf (v / Vl P w)| ≤ MB := by
        nlinarith [abs_nonneg (phiT tw X0m d (d * w) (v / Vl P w)), abs_nonneg (Bf (v / Vl P w))]
      calc |phiT tw X0m d (d * w) (v / Vl P w)| * |Bf (v / Vl P w)| / Vl P w ≤ MB / 1 := by
            apply div_le_div₀ (le_trans (by positivity) h4) h4 one_pos h3
        _ = MB := div_one _
    have hm : Measurable fun v => phiT tw X0m d (d * w) (v / Vl P w) * Bf (v / Vl P w) / Vl P w :=
      (((phiT_meas d (d * w)).comp (measurable_id.div_const _)).mul
        (hBm.comp (measurable_id.div_const _))).div_const _
    have := hg.1.bdd_mul (c := MB) hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only; ring

/-- **The last-step identity** `R_res (f + K_pt B f) = f` for bounded measurable `f`. -/
theorem Rres_last_bdd (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ}
    (hf : KR.BM f) (y : ℝ) :
    Rres P H tw X0m y (fun t => f t + Kpt P tw X0m (fun s => Margin.Bavg (H s) f s) t) =
      f y := by
  classical
  have hX := hO.X0m_pos
  have hBf := BM_Bavg hO hf
  set Bf := fun s => Margin.Bavg (H s) f s
  set L := levels P X0m y
  unfold Rres
  have hadd : ∀ n ∈ L, (∫ t, (f t + Kpt P tw X0m Bf t) * gK P.labelVal y H (phiT tw X0m) n t) /
      Vl P n = (∫ t, f t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n +
        (∫ t, Kpt P tw X0m Bf t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n := by
    intro n _
    rw [← add_div]
    congr 1
    rw [← integral_add (integrable_mul_gK hP hf y n) (integrable_Kpt_mul_gK hO hP hBf y n)]
    congr 1; funext t; ring
  rw [Finset.sum_congr rfl hadd, Finset.sum_add_distrib]
  -- `∑_n n⁻¹ ∫ f dC_n = -K_pt B f(y) - ∑_d d⁻¹ ∫ (K_pt B f) dC_d`
  have hsplit : ∀ n ∈ L, (∫ t, f t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n =
      -((∫ t, f t * stepK P.labelVal y H (phiT tw X0m) 1 n t) / Vl P n) -
        ∑ d ∈ (n.properDivisors).erase 1,
          (∫ t, f t * stepK P.labelVal y H (phiT tw X0m) d n t) / Vl P n := by
    intro n hn
    have hn2 := ((mem_levels (P := P) hX).mp hn).1
    rw [integral_mul_gK_eq hP hf y hn2]
    have h1 : 1 ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩
    rw [← Finset.add_sum_erase _ _ h1, neg_add, add_div, neg_div, neg_div, Finset.sum_div]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    sum_step_one hO hP f y, sum_steps hO hP hf y]
  ring

/-! ## Locally bounded functions and `R_res = R` -/

/-- Bounded and measurable on every half-line `(-∞, c]`. -/
def LBd (f : ℝ → ℝ) : Prop := ∀ c, ∃ g, KR.BM g ∧ ∀ t ≤ c, f t = g t

lemma LBd_of_BM {f : ℝ → ℝ} (hf : KR.BM f) : LBd f := fun _ => ⟨f, hf, fun _ _ => rfl⟩

lemma LBd.add {f g : ℝ → ℝ} (hf : LBd f) (hg : LBd g) : LBd fun t => f t + g t := by
  intro c
  obtain ⟨f', hf', e1⟩ := hf c
  obtain ⟨g', hg', e2⟩ := hg c
  exact ⟨fun t => f' t + g' t, hf'.add hg', fun t ht => by simp only; rw [e1 t ht, e2 t ht]⟩

lemma LBd.neg {f : ℝ → ℝ} (hf : LBd f) : LBd fun t => -f t := by
  intro c
  obtain ⟨f', hf', e1⟩ := hf c
  exact ⟨fun t => -f' t, hf'.neg, fun t ht => by simp only; rw [e1 t ht]⟩

lemma LBd.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, LBd (f i)) :
    LBd fun t => ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LBd_of_BM KR.BM_zero
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1.add h2

lemma window_le (hO : OpHyp P H X0m) {t c s : ℝ} (htc : t ≤ c) (hs : s ≤ t + H t / 2) :
    s ≤ max (1.05 * c) (c + X0m) := by
  have hX := hO.X0m_pos
  rcases le_or_gt (X0m / 2) t with h | h
  · have := hO.small t h
    have : s ≤ 1.05 * t := by linarith
    exact le_max_of_le_left (by nlinarith)
  · have := hO.low t h
    exact le_max_of_le_right (by linarith)

lemma LBd.Bavg (hO : OpHyp P H X0m) {f : ℝ → ℝ} (hf : LBd f) :
    LBd fun s => Margin.Bavg (H s) f s := by
  intro c
  obtain ⟨g, hg, e⟩ := hf (max (1.05 * c) (c + X0m))
  refine ⟨fun s => Margin.Bavg (H s) g s, BM_Bavg hO hg, fun t ht => ?_⟩
  exact Bavg_congr (hO.pos t).le fun s _ hs2 => e s (window_le hO ht hs2)

lemma LBd.Kpt (hO : OpHyp P H X0m) {f : ℝ → ℝ} (hf : LBd f) :
    LBd fun t => Kpt P tw X0m f t := by
  intro c
  obtain ⟨g, hg, e⟩ := hf |c|
  obtain ⟨S, hS, hSe⟩ := Kpt_BM_on (tw := tw) hO hg c
  refine ⟨S, hS, fun t ht => ?_⟩
  rw [← hSe t ht]
  refine Kpt_congr hO.X0m_pos hO.p2 fun u hu1 hu2 => e u ?_
  have hX := hO.X0m_pos
  have : 0 ≤ t := by linarith
  rw [abs_of_nonneg (by linarith)]; linarith

lemma LBd_Top_iter (hO : OpHyp P H X0m) (g : LocInt) (hg : LBd (g : ℝ → ℝ)) (k : ℕ) :
    LBd (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := ((ih.Bavg hO).Kpt (tw := tw) hO).neg
    intro c
    obtain ⟨G, hG, e⟩ := this c
    exact ⟨G, hG, fun t ht => by rw [Top_apply]; exact e t ht⟩

lemma LBd_Nop (hO : OpHyp P H X0m) (g : LocInt) (hg : LBd (g : ℝ → ℝ)) :
    LBd (Nop (tw := tw) hO g : ℝ → ℝ) := by
  intro c
  have hs := LBd.sum (Finset.range (⌈c⌉₊ + 1))
    (f := fun k => (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ))
    (fun k _ => LBd_Top_iter hO g hg k)
  obtain ⟨G, hG, e⟩ := hs c
  exact ⟨G, hG, fun t ht => by rw [← e t ht]; exact Nfun_eq_sum hO g ht⟩

/-- `R_res F (y)` reads `F` only on `(-∞, 1.2|y|]`. -/
lemma Rres_congr (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {F G : ℝ → ℝ} {y : ℝ}
    (hFG : ∀ t ≤ 1.2 * |y|, F t = G t) :
    Rres P H tw X0m y F = Rres P H tw X0m y G := by
  unfold Rres
  rw [hFG y (by have := le_abs_self y; have := abs_nonneg y; linarith)]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  by_cases h : gK P.labelVal y H (phiT tw X0m) n t = 0
  · rw [h, mul_zero, mul_zero]
  · have hs := (gK_supp (tw := tw) hO hP h).2.2
    have hy := y_pos_of_gK (tw := tw) hO hP h
    have : y / Vl P n ≤ y := div_le_self hy.le (one_le_Vl (P := P) n)
    rw [hFG t (by rw [abs_of_pos hy]; nlinarith)]

/-- **The last-step identity** `R_res (f + K_pt B f) = f` for `f` bounded and measurable on every
half-line. -/
theorem Rres_last (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) {f : ℝ → ℝ} (hf : LBd f)
    (y : ℝ) :
    Rres P H tw X0m y (fun t => f t + Kpt P tw X0m (fun s => Margin.Bavg (H s) f s) t) =
      f y := by
  obtain ⟨g, hg, e⟩ := hf (1.2 * |y| + X0m)
  have hX := hO.X0m_pos
  have hKB : ∀ t ≤ 1.2 * |y|, Kpt P tw X0m (fun s => Margin.Bavg (H s) f s) t =
      Kpt P tw X0m (fun s => Margin.Bavg (H s) g s) t := by
    intro t ht
    refine Kpt_congr hX hO.p2 fun u hu1 hu2 => ?_
    refine Bavg_congr (hO.pos u).le fun s _ hs2 => e s ?_
    have := window_le hO (c := u) le_rfl hs2
    have h0 : 0 ≤ t := by linarith
    have : max (1.05 * u) (u + X0m) ≤ 1.2 * |y| + X0m := by
      apply max_le <;> nlinarith [abs_nonneg y]
    linarith
  rw [Rres_congr (G := fun t => g t + Kpt P tw X0m (fun s => Margin.Bavg (H s) g s) t) hO hP
    (fun t ht => by rw [e t (by linarith), hKB t ht]), Rres_last_bdd hO hP hg y]
  exact (e y (by have := le_abs_self y; have := abs_nonneg y; linarith)).symm

/-- **The field `hRres`**: on a function `g ∈ LocInt` bounded and measurable on half-lines (e.g.
`T'`, bounded measurable), the long operator of the kernels is the Neumann series:
`R_res g = R g` (eq. (R-kernels)). -/
theorem Rres_eq_Nop (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (g : LocInt)
    (hg : LBd (g : ℝ → ℝ)) (y : ℝ) :
    Rres P H tw X0m y g = (Nop (tw := tw) hO g : ℝ → ℝ) y := by
  have hspec := congrArg (fun u : LocInt => (u : ℝ → ℝ)) (Nop_spec (tw := tw) hO g)
  have e : (g : ℝ → ℝ) = fun t => (Nop (tw := tw) hO g : ℝ → ℝ) t +
      Kpt P tw X0m (fun s => Margin.Bavg (H s) (Nop (tw := tw) hO g : ℝ → ℝ) s) t := by
    rw [← hspec]; rfl
  rw [e]
  exact Rres_last hO hP (LBd_Nop hO g hg) y

end KR.Ops

end
