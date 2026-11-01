module

public import RequestProject.Beurling.Noise.MarginChain

/-!
# Window integrability of `R_res T'` and `ρ^sh T'` (fields `intRT`, `intRS` of `ChainInputs`)

For a bounded measurable `g`, the functions `y ↦ (R_res g)(y)` and `y ↦ ρ^sh g(y)` are
interval-integrable on every interval:

* the level sets `levels P X₀⁻ y`, `NAll P y X₀⁻` grow with `y`, so on `y ≤ b` both sums run
  over the fixed finite set of levels at `b`, each term carrying the indicator of the
  measurable set `{y : V n ≤ y/c}`;
* each term is measurable in `y`: the true kernels `gK y n` are jointly measurable in the start
  and the point (`measurable_gK_startF`, for filters depending on the centre only), and the
  sharp coefficients `c_n(y)` are measurable in `y` (`measurable_coeff`);
* each term is bounded: `∫ |gK y n| ≤ H_ord(n)` uniformly in the start (`lintegral_gK_le_HordF`)
  and `|c_n(y)| ≤ H_ord(n)` (`abs_coeff_le_Hord`).

`intRT_of`, `intRS_of` give exactly the fields `intRT`, `intRS` of `KR.Chain.ChainInputs`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR.Int

variable {val : ℕ → ℝ} {H : ℝ → ℝ}

/-! ## The true kernels, uniformly in the start -/

lemma stepK_one_F (φ : ℕ → ℕ → ℝ → ℝ) (v : ℝ) (m : ℕ) (t : ℝ) :
    stepK val v H φ 1 m t = φ 1 m (posn val v m) * kd H (posn val v m) t := by
  unfold stepK; rw [if_pos rfl]

lemma stepK_ne_F (φ : ℕ → ℕ → ℝ → ℝ) {d : ℕ} (hd : d ≠ 1) (v : ℝ) (m : ℕ) (t : ℝ) :
    stepK val v H φ d m t = Qd H (LemmaM.valN val (m / d))
      (fun r => φ d m (r / LemmaM.valN val (m / d)) * gK val v H φ d r) t := by
  unfold stepK; rw [if_neg hd]

/-- **Joint measurability** of `(v, s) ↦ g_v(m)(s)` for filters depending on the centre. -/
theorem measurable_gK_startF (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ) :
    ∀ m, Measurable (Function.uncurry fun v s => gK val v H φ m s) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : (Function.uncurry fun v s => gK val v H φ m s) = fun _ => 0 := by
      funext p
      show gK val p.1 H φ m p.2 = 0
      rw [gK_le_one val p.1 H (show m ≤ 1 by omega)]
    rw [this]; exact measurable_const
  have e : (Function.uncurry fun v s => gK val v H φ m s) = fun p =>
      - ∑ d ∈ m.properDivisors, stepK val p.1 H φ d m p.2 := by
    funext p; exact gK_eq val p.1 H hm p.2
  rw [e]
  refine (Finset.measurable_sum _ fun d hd => ?_).neg
  by_cases h1 : d = 1
  · subst h1
    simp_rw [stepK_one_F]
    unfold posn
    exact ((hφ 1 m).1.comp (measurable_fst.div_const _)).mul ((measurable_kd hH).comp
      ((measurable_fst.div_const _).prodMk measurable_snd))
  · simp_rw [stepK_ne_F φ h1]
    unfold Qd
    have hF : Measurable (Function.uncurry fun (p : ℝ × ℝ) (r : ℝ) =>
        φ d m (r / LemmaM.valN val (m / d)) * gK val p.1 H φ d r *
          kd H (r / LemmaM.valN val (m / d)) p.2) := by
      refine (((hφ d m).1.comp (measurable_snd.div_const _)).mul
        ((ih d (Nat.mem_properDivisors.mp hd).2).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul ?_
      exact (measurable_kd hH).comp ((measurable_snd.div_const _).prodMk
        (measurable_snd.comp measurable_fst))
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- **The uniform bound** `∫ |g_v(m)| ≤ H_ord(m)` for filters with values in `[0, 1]`. -/
theorem lintegral_gK_le_HordF (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    (v : ℝ) : ∀ m, ∫⁻ s, ‖gK val v H φ m s‖ₑ ≤ (BSCert.X0Band.Hord m : ℝ≥0∞) := by
  have hb : ∀ d n c, ‖φ d n c‖ₑ ≤ 1 := fun d n c => by
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_one.mpr ?_
    rw [abs_le]; constructor <;> linarith [(hφ d n).2 c]
  have hmeas : ∀ m, Measurable (gK val v H φ m) := fun m =>
    (measurable_gK_startF hH hφ m).comp (measurable_const.prodMk measurable_id)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · simp [gK_le_one val v H (show m ≤ 1 by omega)]
  have e : gK val v H φ m = fun s => - ∑ d ∈ m.properDivisors, stepK val v H φ d m s :=
    funext (gK_eq val v H hm)
  rw [e, BSCert.X0Band.Hord_eq m, if_neg (by omega)]
  push_cast
  have hst : ∀ d ∈ m.properDivisors, Measurable (stepK val v H φ d m) ∧
      ∫⁻ s, ‖stepK val v H φ d m s‖ₑ ≤ (BSCert.X0Band.Hord d : ℝ≥0∞) := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      have e1 : stepK val v H φ 1 m = fun s => φ 1 m (posn val v m) * kd H (posn val v m) s :=
        funext (stepK_one_F φ v m)
      rw [e1]
      refine ⟨measurable_const.mul (measurable_kd_left hH _), ?_⟩
      simp_rw [enorm_mul]
      rw [lintegral_const_mul _ (measurable_kd_left hH _).enorm, lintegral_kd hH, mul_one,
        BSCert.X0Band.Hord_eq 1, if_pos le_rfl]
      simp only [Nat.cast_one]
      exact hb 1 m _
    · have e1 : stepK val v H φ d m = Qd H (LemmaM.valN val (m / d))
          (fun r => φ d m (r / LemmaM.valN val (m / d)) * gK val v H φ d r) :=
        funext (stepK_ne_F φ h1 v m)
      have hfm : Measurable fun r => φ d m (r / LemmaM.valN val (m / d)) * gK val v H φ d r :=
        ((hφ d m).1.comp (measurable_id.div_const _)).mul (hmeas d)
      rw [e1]
      refine ⟨measurable_Qd hH _ hfm, ?_⟩
      refine (lintegral_Qd_le hH _ hfm).trans ?_
      refine le_trans (lintegral_mono fun r => ?_) (ih d (Nat.mem_properDivisors.mp hd).2)
      rw [enorm_mul]
      calc ‖φ d m (r / LemmaM.valN val (m / d))‖ₑ * ‖gK val v H φ d r‖ₑ
          ≤ 1 * ‖gK val v H φ d r‖ₑ := by gcongr; exact hb _ _ _
        _ = ‖gK val v H φ d r‖ₑ := one_mul _
  calc ∫⁻ s, ‖-∑ d ∈ m.properDivisors, stepK val v H φ d m s‖ₑ
      ≤ ∫⁻ s, ∑ d ∈ m.properDivisors, ‖stepK val v H φ d m s‖ₑ := by
        refine lintegral_mono fun s => ?_
        rw [enorm_neg]; exact enorm_sum_le _ _
    _ = ∑ d ∈ m.properDivisors, ∫⁻ s, ‖stepK val v H φ d m s‖ₑ :=
        lintegral_finset_sum _ fun d hd => (hst d hd).1.enorm
    _ ≤ ∑ d ∈ m.properDivisors, (BSCert.X0Band.Hord d : ℝ≥0∞) :=
        Finset.sum_le_sum fun d hd => (hst d hd).2

/-- `|∫ g dC_n| ≤ M H_ord(n)` for `|g| ≤ M`. -/
lemma abs_integral_gK_le (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {g : ℝ → ℝ} (_hgm : Measurable g) {M : ℝ} (hgM : ∀ t, |g t| ≤ M) (v : ℝ) (m : ℕ) :
    |∫ t, g t * gK val v H φ m t| ≤ M * BSCert.X0Band.Hord m := by
  have hint := (integrable_gK (val := val) (x := v) hH hφ m).1
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  have h1 : |∫ t, g t * gK val v H φ m t| ≤ ∫ t, M * ‖gK val v H φ m t‖ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hint.norm.const_mul M)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs (g t)]
    exact mul_le_mul_of_nonneg_right (hgM t) (norm_nonneg _)
  have h2 : ∫ t, ‖gK val v H φ m t‖ ≤ (BSCert.X0Band.Hord m : ℝ) := by
    rw [integral_norm_eq_lintegral_enorm hint.1]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (lintegral_gK_le_HordF hH hφ v m).trans (le_of_eq ?_)
    simp
  rw [integral_const_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hM0)

/-! ## The sharp coefficients -/

/-- `y ↦ c_n(y)` is measurable. -/
theorem measurable_coeff (t : ℕ → ℝ) (val : ℕ → ℝ) (X0 : ℝ) :
    ∀ n, Measurable fun y : ℝ => (LemmaM.coeff t val X0 y n : ℝ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : (fun y : ℝ => (LemmaM.coeff t val X0 y n : ℝ)) =
        fun _ => ((if n = 1 then 1 else 0 : ℤ) : ℝ) := by
      funext y; rw [LemmaM.coeff, if_pos (by omega)]
    rw [this]; exact measurable_const
  have e : (fun y : ℝ => (LemmaM.coeff t val X0 y n : ℝ)) = fun y =>
      -∑ d ∈ n.properDivisors, (if LemmaM.filt t val y n d ∧ X0 ≤ y / LemmaM.valN val n then
        (LemmaM.coeff t val X0 y d : ℝ) else 0) := by
    funext y
    rw [LemmaM.coeff, if_neg (by omega)]
    push_cast
    congr 1
    rw [Finset.sum_attach n.properDivisors (fun d => (if LemmaM.filt t val y n d ∧
      X0 ≤ y / LemmaM.valN val n then (LemmaM.coeff t val X0 y d : ℝ) else 0))]
  rw [e]
  refine (Finset.measurable_sum _ fun d hd => ?_).neg
  refine Measurable.ite ?_ (ih d (Nat.mem_properDivisors.mp hd).2) measurable_const
  have hS : {y : ℝ | LemmaM.filt t val y n d ∧ X0 ≤ y / LemmaM.valN val n} =
      (⋂ p ∈ (n / d).primeFactors, {y : ℝ | t p * LemmaM.valN val n < y}) ∩
        {y : ℝ | X0 ≤ y / LemmaM.valN val n} := by
    ext y; simp [LemmaM.filt]
  rw [hS]
  refine MeasurableSet.inter ?_ (measurableSet_le measurable_const (measurable_id.div_const _))
  exact Finset.measurableSet_biInter _ fun p _ =>
    measurableSet_lt measurable_const measurable_id

/-- `|c_n(y)| ≤ H_ord(n)`. -/
theorem abs_coeff_le_Hord (t : ℕ → ℝ) (val : ℕ → ℝ) (X0 y : ℝ) :
    ∀ n, |(LemmaM.coeff t val X0 y n : ℝ)| ≤ BSCert.X0Band.Hord n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [LemmaM.coeff, BSCert.X0Band.Hord_eq]
  rw [LemmaM.coeff, if_neg (by omega), BSCert.X0Band.Hord_eq n, if_neg (by omega)]
  push_cast
  rw [abs_neg, Finset.sum_attach n.properDivisors (fun d => (if LemmaM.filt t val y n d ∧
      X0 ≤ y / LemmaM.valN val n then (LemmaM.coeff t val X0 y d : ℝ) else 0))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  split_ifs
  · exact ih d (Nat.mem_properDivisors.mp hd).2
  · simp

/-! ## The level sets -/

variable (P : BeurlingSystem)

lemma mem_NAll_iff {y c : ℝ} {n : ℕ} :
    n ∈ NAll P y c ↔ n ≠ 0 ∧ Vl P n ≤ y / c := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    rw [mem_elems] at he
    exact ⟨(iota_pos e).ne', by unfold Vl; rw [P.valN_iota]; exact he⟩
  · rintro ⟨hn, h⟩
    exact KR.mem_image_iota P hn h

lemma NAll_mono {c : ℝ} (hc : 0 < c) {y b : ℝ} (hyb : y ≤ b) : NAll P y c ⊆ NAll P b c := by
  intro n hn
  rw [mem_NAll_iff] at hn ⊢
  exact ⟨hn.1, hn.2.trans (div_le_div_of_nonneg_right hyb hc.le)⟩

/-- A finite sum over a growing index set, rewritten over the index set at `b`. -/
lemma sum_NAll_eq {c : ℝ} (hc : 0 < c) {y b : ℝ} (hyb : y ≤ b) (p : ℕ → Prop)
    [DecidablePred p] (F : ℕ → ℝ) :
    ∑ n ∈ (NAll P y c).filter p, F n =
      ∑ n ∈ (NAll P b c).filter p, (if Vl P n ≤ y / c then F n else 0) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, mem_NAll_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨⟨⟨h0, h1.trans (div_le_div_of_nonneg_right hyb hc.le)⟩, h2⟩, h1⟩
    · rintro ⟨⟨⟨h0, -⟩, h2⟩, h1⟩
      exact ⟨⟨h0, h1⟩, h2⟩
  · intro n _; rfl

/-! ## Interval integrability -/

/-- A function bounded on `[a, b]`'s `uIoc` and equal there to a measurable function is
interval-integrable. -/
lemma intervalIntegrable_of_eqOn {f G : ℝ → ℝ} {a b M : ℝ} (hG : Measurable G)
    (heq : ∀ y ∈ Set.uIoc a b, f y = G y) (hb : ∀ y ∈ Set.uIoc a b, |f y| ≤ M) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  have hGi : IntegrableOn G (Set.uIoc a b) volume := by
    refine Measure.integrableOn_of_bounded (M := M)
      ((measure_mono (μ := volume) (Set.uIoc_subset_uIcc (a := a) (b := b))).trans_lt
        isCompact_uIcc.measure_lt_top).ne hG.aestronglyMeasurable ?_
    refine (ae_restrict_mem (measurableSet_uIoc (a := a) (b := b))).mono fun y hy => ?_
    rw [Real.norm_eq_abs, ← heq y hy]; exact hb y hy
  exact hGi.congr_fun (fun y hy => (heq y hy).symm) measurableSet_uIoc

/-- **`y ↦ (R_res g)(y)` is interval-integrable** for bounded measurable `g`. -/
theorem intervalIntegrable_Rres (hH : WidthReg H) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m)
    {g : ℝ → ℝ} (hgm : Measurable g) {M : ℝ} (hgM : ∀ t, |g t| ≤ M) (a b : ℝ) :
    IntervalIntegrable (fun y => Rres P H tw X0m y g) volume a b := by
  classical
  have hφ := trueFilter_ok tw X0m
  set c := X0m / 2
  have hc : 0 < c := by positivity
  set B := max a b
  set Nb := (NAll P B c).filter (2 ≤ ·)
  set G : ℝ → ℝ := fun y => g y + ∑ n ∈ Nb,
    (if Vl P n ≤ y / c then (∫ t, g t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n else 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  refine intervalIntegrable_of_eqOn (G := G)
    (M := M + ∑ n ∈ Nb, M * BSCert.X0Band.Hord n / Vl P n) ?_ ?_ ?_
  · refine hgm.add (Finset.measurable_sum _ fun n _ => Measurable.ite ?_ ?_ measurable_const)
    · exact measurableSet_le measurable_const (measurable_id.div_const _)
    · have hJ : Measurable (Function.uncurry fun (y t : ℝ) =>
          g t * gK P.labelVal y H (phiT tw X0m) n t) :=
        (hgm.comp measurable_snd).mul (measurable_gK_startF hH hφ n)
      exact (hJ.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.div_const _
  · intro y hy
    have hyB : y ≤ B := by
      rw [Set.mem_uIoc] at hy
      rcases hy with h | h
      · exact h.2.trans (le_max_right _ _)
      · exact h.2.trans (le_max_left _ _)
    show g y + _ = G y
    unfold levels
    rw [sum_NAll_eq P hc hyB]
  · intro y hy
    have hyB : y ≤ B := by
      rw [Set.mem_uIoc] at hy
      rcases hy with h | h
      · exact h.2.trans (le_max_right _ _)
      · exact h.2.trans (le_max_left _ _)
    unfold Rres levels
    rw [sum_NAll_eq P hc hyB]
    refine (abs_add_le _ _).trans (add_le_add (hgM y) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    have hV := KR.valN_labelVal_pos P n
    split_ifs
    · rw [abs_div, abs_of_pos hV]
      exact div_le_div_of_nonneg_right (abs_integral_gK_le hH hφ hgm hgM y n) hV.le
    · simp only [abs_zero]
      positivity

/-- **`y ↦ ρ^sh g(y)` is interval-integrable** for bounded measurable `g`. -/
theorem intervalIntegrable_rhoSh (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m)
    {g : ℝ → ℝ} (hgm : Measurable g) {M : ℝ} (hgM : ∀ t, |g t| ≤ M) (a b : ℝ) :
    IntervalIntegrable (fun y => rhoSh P tw X0m y g) volume a b := by
  classical
  set B := max a b
  set Nb := NAll P B X0m
  set G : ℝ → ℝ := fun y => ∑ n ∈ Nb.filter (fun _ => True),
    (if Vl P n ≤ y / X0m then
      (LemmaM.coeff tw P.labelVal X0m y n : ℝ) * g (y / Vl P n) / Vl P n else 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  have hcN : ∀ y n, cN P tw X0m y n = (LemmaM.coeff tw P.labelVal X0m y n : ℝ) :=
    fun y n => mass_eq_coeff _ _ _ _ _
  have hfil : ∀ y, NAll P y X0m = (NAll P y X0m).filter (fun _ => True) := fun y => by simp
  refine intervalIntegrable_of_eqOn (G := G)
    (M := ∑ n ∈ Nb.filter (fun _ => True), BSCert.X0Band.Hord n * M / Vl P n) ?_ ?_ ?_
  · refine Finset.measurable_sum _ fun n _ => Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le measurable_const (measurable_id.div_const _)
    · exact ((measurable_coeff tw P.labelVal X0m n).mul
        (hgm.comp (measurable_id.div_const _))).div_const _
  · intro y hy
    have hyB : y ≤ B := by
      rw [Set.mem_uIoc] at hy
      rcases hy with h | h
      · exact h.2.trans (le_max_right _ _)
      · exact h.2.trans (le_max_left _ _)
    show rhoSh P tw X0m y g = G y
    unfold rhoSh
    rw [hfil y, sum_NAll_eq P hX hyB]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold posn
    rw [hcN]
  · intro y hy
    have hyB : y ≤ B := by
      rw [Set.mem_uIoc] at hy
      rcases hy with h | h
      · exact h.2.trans (le_max_right _ _)
      · exact h.2.trans (le_max_left _ _)
    unfold rhoSh
    rw [hfil y, sum_NAll_eq P hX hyB]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    have hV := KR.valN_labelVal_pos P n
    split_ifs
    · rw [abs_div, abs_of_pos hV, abs_mul, hcN]
      apply div_le_div_of_nonneg_right _ hV.le
      exact mul_le_mul (abs_coeff_le_Hord _ _ _ _ n) (hgM _) (abs_nonneg _) (by positivity)
    · simp only [abs_zero]
      positivity

/-! ## The fields of `ChainInputs` -/

lemma Tp_measurable {Tc : ℝ → ℝ} (hTm : Measurable Tc) (j0 X0 : ℝ) :
    Measurable fun t => Tc t + j0 * KR.Chain.ind X0 t :=
  hTm.add (measurable_const.mul (KR.Chain.ind_measurable X0))

lemma Tp_abs_le {Tc : ℝ → ℝ} (hTb : ∀ t, |Tc t| ≤ 2) (j0 X0 t : ℝ) :
    |Tc t + j0 * KR.Chain.ind X0 t| ≤ 2 + |j0| := by
  refine (abs_add_le _ _).trans (add_le_add (hTb t) ?_)
  rw [abs_mul]
  calc |j0| * |KR.Chain.ind X0 t| ≤ |j0| * 1 :=
        mul_le_mul_of_nonneg_left (KR.Chain.ind_abs_le X0 t) (abs_nonneg _)
    _ = |j0| := mul_one _

/-- **The field `intRT` of `ChainInputs`.** -/
theorem intRT_of (hH : WidthReg H) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {Tc : ℝ → ℝ}
    (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) (j0 X0 : ℝ) :
    ∀ x, IntervalIntegrable
      (fun y => Rres P H tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t))
      volume (x - H x / 2) (x + H x / 2) := fun _ =>
  intervalIntegrable_Rres P hH tw hX (Tp_measurable hTm j0 X0) (Tp_abs_le hTb j0 X0) _ _

/-- **The field `intRS` of `ChainInputs`.** -/
theorem intRS_of (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {Tc : ℝ → ℝ} (hTm : Measurable Tc)
    (hTb : ∀ t, |Tc t| ≤ 2) (j0 X0 : ℝ) :
    ∀ x, IntervalIntegrable
      (fun y => rhoSh P tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t))
      volume (x - H x / 2) (x + H x / 2) := fun _ =>
  intervalIntegrable_rhoSh P tw hX (Tp_measurable hTm j0 X0) (Tp_abs_le hTb j0 X0) _ _

end KR.Int

end
