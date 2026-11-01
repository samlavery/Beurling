module

public import RequestProject.Beurling.Noise.KRTrue

/-!
# Chains from a spread-out source: the kernel representation

For a source density `f` at the level `n'`, the nominal chain `𝒯_{n'→n} f` (`Tch`) is the
superposition over `v` of the nominal kernels started at `δ_v` with the frozen filters
`κ'_{d'→m} = κ_{n'd'→n'm}`:

  `𝒯_{n'→n'm} f (t) = ∫ f(v) g_v(m)(t) dv`,  `g_v = gK val v H (constF κ')`   (`Tch_rep`).

This is the linearity of the chain operator in the initial measure (the paper's "chains from
`δ_v` with frozen filters", proof of Proposition 5.18, step (ii)). It needs:

* the joint measurability of `(v, s) ↦ g_v(m)(s)` (`measurable_gK_start`);
* the uniform bound `∫ |g_v(m)| ≤ H_ord(m)` (`lintegral_gK_le_Hord`);
* Fubini for one step (`Qd_integral_swap`).

`lintegral_Tch_le` is the consequence used for the total variation:
`∫ |𝒯_{n'→n'm} f| ≤ ∫ |f(v)| ∫ |g_v(m)| dv`.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

variable {val : ℕ → ℝ} {H : ℝ → ℝ}

/-- The frozen filters of the chains from level `n'`: `κ'_{d'→m} = κ_{n'd'→n'm}`. -/
def kSh (κ : ℕ → ℕ → ℝ) (n' : ℕ) : ℕ → ℕ → ℝ := fun d m => κ (n' * d) (n' * m)

lemma stepK_one_const (κ : ℕ → ℕ → ℝ) (v : ℝ) (m : ℕ) (t : ℝ) :
    stepK val v H (constF κ) 1 m t = κ 1 m * kd H (v / LemmaM.valN val m) t := by
  unfold stepK constF posn; rw [if_pos rfl]

lemma stepK_const {κ : ℕ → ℕ → ℝ} {d : ℕ} (hd : d ≠ 1) (v : ℝ) (m : ℕ) (t : ℝ) :
    stepK val v H (constF κ) d m t =
      κ d m * Qd H (LemmaM.valN val (m / d)) (gK val v H (constF κ) d) t := by
  unfold stepK constF; rw [if_neg hd, ← Qd_const_mul]

/-- **Joint measurability** of `(v, s) ↦ g_v(m)(s)`. -/
theorem measurable_gK_start (hH : WidthReg H) (κ : ℕ → ℕ → ℝ) :
    ∀ m, Measurable (Function.uncurry fun v s => gK val v H (constF κ) m s) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : (Function.uncurry fun v s => gK val v H (constF κ) m s) = fun _ => 0 := by
      funext p
      show gK val p.1 H (constF κ) m p.2 = 0
      rw [gK_le_one val p.1 H (show m ≤ 1 by omega)]
    rw [this]; exact measurable_const
  have e : (Function.uncurry fun v s => gK val v H (constF κ) m s) = fun p =>
      - ∑ d ∈ m.properDivisors, stepK val p.1 H (constF κ) d m p.2 := by
    funext p; exact gK_eq val p.1 H hm p.2
  rw [e]
  refine (Finset.measurable_sum _ fun d hd => ?_).neg
  by_cases h1 : d = 1
  · subst h1
    simp_rw [stepK_one_const]
    exact measurable_const.mul ((measurable_kd hH).comp
      ((measurable_fst.div_const _).prodMk measurable_snd))
  · simp_rw [stepK_const h1]
    refine measurable_const.mul ?_
    unfold Qd
    have hF : Measurable (Function.uncurry fun (p : ℝ × ℝ) (r : ℝ) =>
        gK val p.1 H (constF κ) d r * kd H (r / LemmaM.valN val (m / d)) p.2) := by
      refine ((ih d (Nat.mem_properDivisors.mp hd).2).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul ?_
      exact (measurable_kd hH).comp ((measurable_snd.div_const _).prodMk
        (measurable_snd.comp measurable_fst))
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- **The uniform bound** `∫ |g_v(m)| ≤ H_ord(m)` (filters in `[-1, 1]`). -/
theorem lintegral_gK_le_Hord (hH : WidthReg H) {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, |κ d n| ≤ 1)
    (v : ℝ) : ∀ m, ∫⁻ s, ‖gK val v H (constF κ) m s‖ₑ ≤ (BSCert.X0Band.Hord m : ℝ≥0∞) := by
  have hmeas : ∀ m, Measurable (gK val v H (constF κ) m) := fun m =>
    (measurable_gK_start hH κ m).comp (measurable_const.prodMk measurable_id)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · simp [gK_le_one val v H (show m ≤ 1 by omega)]
  have e : gK val v H (constF κ) m = fun s =>
      - ∑ d ∈ m.properDivisors, stepK val v H (constF κ) d m s := funext (gK_eq val v H hm)
  rw [e, BSCert.X0Band.Hord_eq m, if_neg (by omega)]
  push_cast
  have hst : ∀ d ∈ m.properDivisors, Measurable (stepK val v H (constF κ) d m) ∧
      ∫⁻ s, ‖stepK val v H (constF κ) d m s‖ₑ ≤ (BSCert.X0Band.Hord d : ℝ≥0∞) := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      have e1 : stepK val v H (constF κ) 1 m = fun s =>
          κ 1 m * kd H (v / LemmaM.valN val m) s := funext (stepK_one_const κ v m)
      rw [e1]
      refine ⟨measurable_const.mul (measurable_kd_left hH _), ?_⟩
      simp_rw [enorm_mul]
      rw [lintegral_const_mul _ (measurable_kd_left hH _).enorm, lintegral_kd hH, mul_one,
        BSCert.X0Band.Hord_eq 1, if_pos le_rfl]
      simp only [Nat.cast_one]
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.mpr (hκ 1 m)
    · have e1 : stepK val v H (constF κ) d m = fun s =>
          κ d m * Qd H (LemmaM.valN val (m / d)) (gK val v H (constF κ) d) s :=
        funext (stepK_const h1 v m)
      rw [e1]
      refine ⟨measurable_const.mul (measurable_Qd hH _ (hmeas d)), ?_⟩
      simp_rw [enorm_mul]
      rw [lintegral_const_mul _ (measurable_Qd hH _ (hmeas d)).enorm]
      have h2 := (lintegral_Qd_le hH (LemmaM.valN val (m / d)) (hmeas d)).trans
        (ih d (Nat.mem_properDivisors.mp hd).2)
      calc ‖κ d m‖ₑ * ∫⁻ s, ‖Qd H (LemmaM.valN val (m / d)) (gK val v H (constF κ) d) s‖ₑ
          ≤ 1 * (BSCert.X0Band.Hord d : ℝ≥0∞) := by
            gcongr
            rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_one.mpr (hκ d m)
        _ = _ := one_mul _
  calc ∫⁻ s, ‖-∑ d ∈ m.properDivisors, stepK val v H (constF κ) d m s‖ₑ
      ≤ ∫⁻ s, ∑ d ∈ m.properDivisors, ‖stepK val v H (constF κ) d m s‖ₑ := by
        refine lintegral_mono fun s => ?_
        rw [enorm_neg]; exact enorm_sum_le _ _
    _ = ∑ d ∈ m.properDivisors, ∫⁻ s, ‖stepK val v H (constF κ) d m s‖ₑ :=
        lintegral_finset_sum _ fun d hd => (hst d hd).1.enorm
    _ ≤ ∑ d ∈ m.properDivisors, (BSCert.X0Band.Hord d : ℝ≥0∞) :=
        Finset.sum_le_sum fun d hd => (hst d hd).2

/-- Joint measurability of one step `(v, t) ↦ Qd_w(g_v(d))(t)`. -/
lemma measurable_Qd_start (hH : WidthReg H) (κ : ℕ → ℕ → ℝ) (w : ℝ) (d : ℕ) :
    Measurable (Function.uncurry fun v t => Qd H w (gK val v H (constF κ) d) t) := by
  unfold Qd
  have hF : Measurable (Function.uncurry fun (p : ℝ × ℝ) (r : ℝ) =>
      gK val p.1 H (constF κ) d r * kd H (r / w) p.2) := by
    refine ((measurable_gK_start hH κ d).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul ?_
    exact (measurable_kd hH).comp ((measurable_snd.div_const _).prodMk
      (measurable_snd.comp measurable_fst))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma integrable_gK_start (hH : WidthReg H) {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1)
    (v : ℝ) (m : ℕ) : Integrable (gK val v H (constF κ) m) :=
  (integrable_gK hH (constF_ok hκ) m).1

lemma abs_kappa {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) (d n : ℕ) :
    |κ d n| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hκ d n]

/-- `∫ |g_v(d)| ≤ H_ord(d)` as a Bochner integral. -/
lemma integral_norm_gK_le (hH : WidthReg H) {κ : ℕ → ℕ → ℝ}
    (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) (v : ℝ) (d : ℕ) :
    ∫ s, ‖gK val v H (constF κ) d s‖ ≤ (BSCert.X0Band.Hord d : ℝ) := by
  rw [integral_norm_eq_lintegral_enorm (integrable_gK_start hH hκ v d).1]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (lintegral_gK_le_Hord hH (abs_kappa hκ) v d).trans (le_of_eq ?_)
  simp

/-- `|Qd_w g (t)| ≤ (3/2) H(t)⁻¹ ∫ |g|`. -/
lemma abs_Qd_le (hH : WidthReg H) (w : ℝ) {g : ℝ → ℝ} (hg : Integrable g) (t : ℝ) :
    |Qd H w g t| ≤ 3 / 2 * (H t)⁻¹ * ∫ r, ‖g r‖ := by
  unfold Qd
  have hk : ∀ r, ‖g r * kd H (r / w) t‖ ≤ 3 / 2 * (H t)⁻¹ * ‖g r‖ := by
    intro r
    rw [norm_mul, Real.norm_eq_abs (kd H _ _), abs_of_nonneg (kd_nonneg hH _ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (kd_le_window hH _ _) (norm_nonneg _)
  calc |∫ r, g r * kd H (r / w) t| = ‖∫ r, g r * kd H (r / w) t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ r, ‖g r * kd H (r / w) t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, 3 / 2 * (H t)⁻¹ * ‖g r‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => norm_nonneg _)
          (hg.norm.const_mul _) (Filter.Eventually.of_forall hk)
    _ = 3 / 2 * (H t)⁻¹ * ∫ r, ‖g r‖ := integral_const_mul _ _

/-- **Fubini for one step**: `Qd_w(∫ f(v) g_v(d) dv)(t) = ∫ f(v) Qd_w(g_v(d))(t) dv`. -/
theorem Qd_integral_swap (hH : WidthReg H) {κ : ℕ → ℕ → ℝ}
    (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (d : ℕ) (w t : ℝ) :
    Qd H w (fun s => ∫ v, f v * gK val v H (constF κ) d s) t =
      ∫ v, f v * Qd H w (gK val v H (constF κ) d) t := by
  set G := fun v s => gK val v H (constF κ) d s
  set F : ℝ → ℝ → ℝ := fun v s => f v * G v s * kd H (s / w) t
  have hGm : Measurable (Function.uncurry G) := measurable_gK_start hH κ d
  have hFm : Measurable (Function.uncurry F) :=
    ((hfm.comp measurable_fst).mul hGm).mul ((measurable_kd hH).comp
      ((measurable_snd.div_const _).prodMk measurable_const))
  set C := 3 / 2 * (H t)⁻¹
  have hC : 0 ≤ C := by have := hH.pos t; positivity
  have hkb : ∀ s, ‖kd H (s / w) t‖ ≤ C := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (kd_nonneg hH _ _)]; exact kd_le_window hH _ _
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun v => ?_, ?_⟩
    · exact ((integrable_gK_start hH hκ v d).const_mul (f v)).mul_bdd
        (((measurable_kd hH).comp
          ((measurable_id.div_const w).prodMk measurable_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall hkb)
    · refine Integrable.mono' ((hf.norm.mul_const (C * (BSCert.X0Band.Hord d : ℝ))))
        ((hFm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun v => ?_)
      have h0 : 0 ≤ ∫ s, ‖F v s‖ := integral_nonneg fun _ => norm_nonneg _
      show |∫ s, ‖F v s‖| ≤ _
      rw [abs_of_nonneg h0]
      calc ∫ s, ‖F v s‖ ≤ ∫ s, ‖f v‖ * C * ‖G v s‖ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_gK_start hH hκ v d).norm.const_mul _)
              (Filter.Eventually.of_forall fun s => ?_)
            simp only [F, norm_mul]
            have h3 := mul_le_mul_of_nonneg_left (hkb s)
              (mul_nonneg (norm_nonneg (f v)) (norm_nonneg (G v s)))
            linarith
        _ = ‖f v‖ * C * ∫ s, ‖G v s‖ := integral_const_mul _ _
        _ ≤ ‖f v‖ * C * (BSCert.X0Band.Hord d : ℝ) :=
            mul_le_mul_of_nonneg_left (integral_norm_gK_le hH hκ v d) (by positivity)
        _ = ‖f v‖ * (C * (BSCert.X0Band.Hord d : ℝ)) := by ring
  unfold Qd
  have e1 : ∫ s, (∫ v, f v * G v s) * kd H (s / w) t = ∫ s, ∫ v, F v s := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F]; rw [← integral_mul_const]
  have e2 : ∫ v, f v * ∫ s, G v s * kd H (s / w) t = ∫ v, ∫ s, F v s := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [F]; rw [← integral_const_mul]; congr 1; funext s; ring
  simp only [G] at e1 e2
  rw [e1, e2, integral_integral_swap hint]

/-- `v ↦ f(v) · (step)` is integrable: the step is bounded by `(3/2)H(t)⁻¹ H_ord(d)`. -/
lemma integrable_f_stepK (hH : WidthReg H) {κ : ℕ → ℕ → ℝ}
    (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) {f : ℝ → ℝ} (hf : Integrable f) (d m : ℕ) (t : ℝ) :
    Integrable fun v => f v * stepK val v H (constF κ) d m t := by
  have hC : 0 ≤ 3 / 2 * (H t)⁻¹ := by have := hH.pos t; positivity
  by_cases h1 : d = 1
  · subst h1
    simp_rw [stepK_one_const]
    refine hf.mul_bdd (c := 1 * (3 / 2 * (H t)⁻¹))
      (measurable_const.mul ((measurable_kd hH).comp
        ((measurable_id.div_const _).prodMk measurable_const))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_mul, Real.norm_eq_abs (kd H _ _), abs_of_nonneg (kd_nonneg hH _ _)]
    exact mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_kappa hκ 1 m) (kd_le_window hH _ _)
      (kd_nonneg hH _ _) zero_le_one
  · simp_rw [stepK_const h1]
    refine hf.mul_bdd (c := 1 * (3 / 2 * (H t)⁻¹ * (BSCert.X0Band.Hord d : ℝ)))
      (measurable_const.mul ((measurable_Qd_start hH κ _ d).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    refine mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_kappa hκ d m) ?_ (norm_nonneg _)
      zero_le_one
    rw [Real.norm_eq_abs]
    exact (abs_Qd_le hH _ (integrable_gK_start hH hκ v d) t).trans
      (mul_le_mul_of_nonneg_left (integral_norm_gK_le hH hκ v d) hC)

/-- **The kernel representation** of the chains from level `n'`:
`𝒯_{n'→n'm} f (t) = ∫ f(v) g_v(m)(t) dv` for `m ≥ 2`, with the frozen filters `κ'`. -/
theorem Tch_rep (hH : WidthReg H) {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1)
    {n' : ℕ} (hn' : 1 ≤ n') {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f) :
    ∀ m, 2 ≤ m → ∀ t, Tch val H κ n' f (n' * m) t =
      ∫ v, f v * gK val v H (constF (kSh κ n')) m t := by
  have hκ' : ∀ d n, 0 ≤ kSh κ n' d n ∧ kSh κ n' d n ≤ 1 := fun d n => hκ _ _
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm t
  have hlt : n' < n' * m := by nlinarith
  rw [Tch_eq f hlt]
  -- the right side
  have hR : ∫ v, f v * gK val v H (constF (kSh κ n')) m t =
      - ∑ d ∈ m.properDivisors, ∫ v, f v * stepK val v H (constF (kSh κ n')) d m t := by
    simp_rw [gK_eq val _ H hm t, mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finset_sum _ fun d _ => integrable_f_stepK hH hκ' hf d m t]
  rw [hR]
  congr 1
  -- reindex the left side to the divisors of `m`
  set T : ℕ → ℝ := fun d => κ d (n' * m) *
    Qd H (LemmaM.valN val (n' * m / d)) (Tch val H κ n' f d) t
  have hinj : Set.InjOn (fun d' => n' * d') (m.properDivisors : Set ℕ) :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hsub : m.properDivisors.image (fun d' => n' * d') ⊆ (n' * m).properDivisors := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hd'
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left n' h1,
      Nat.mul_lt_mul_of_pos_left h2 (by omega)⟩
  have hzero : ∀ d ∈ (n' * m).properDivisors,
      d ∉ m.properDivisors.image (fun d' => n' * d') → T d = 0 := by
    intro d hd hnot
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hd
    have hnd : ¬ n' ∣ d := by
      rintro ⟨d', rfl⟩
      apply hnot
      refine Finset.mem_image.mpr ⟨d', Nat.mem_properDivisors.mpr
        ⟨(Nat.mul_dvd_mul_iff_left (by omega)).mp h1, ?_⟩, rfl⟩
      exact (Nat.mul_lt_mul_left (by omega)).mp h2
    simp only [T]
    rw [Tch_not_dvd f d hnd]
    unfold Qd; simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun d' hd' => ?_
  obtain ⟨hd'm, hd'lt⟩ := Nat.mem_properDivisors.mp hd'
  have hdiv : n' * m / (n' * d') = m / d' := Nat.mul_div_mul_left m d' (by omega)
  simp only [T]
  rw [hdiv]
  by_cases h1 : d' = 1
  · subst h1
    rw [mul_one, Tch_self]
    simp_rw [stepK_one_const]
    unfold Qd
    rw [Nat.div_one, ← integral_const_mul]
    congr 1; funext v; simp only [kSh, mul_one]; ring
  · have hd'2 : 2 ≤ d' := by
      rcases Nat.lt_or_ge d' 2 with h | h
      · interval_cases d'
        · simp at hd'm; omega
        · exact absurd rfl h1
      · exact h
    have hT : Tch val H κ n' f (n' * d') = fun s =>
        ∫ v, f v * gK val v H (constF (kSh κ n')) d' s := funext (ih d' hd'lt hd'2)
    rw [hT, Qd_integral_swap hH hκ' hf hfm d']
    simp_rw [stepK_const h1]
    rw [← integral_const_mul]
    congr 1; funext v; simp only [kSh]; ring

/-- **The total-variation consequence**: `∫ |𝒯_{n'→n'm} f| ≤ ∫ |f(v)| ∫ |g_v(m)| dv`. -/
theorem lintegral_Tch_le (hH : WidthReg H) {κ : ℕ → ℕ → ℝ}
    (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) {n' : ℕ} (hn' : 1 ≤ n') {f : ℝ → ℝ}
    (hf : Integrable f) (hfm : Measurable f) {m : ℕ} (hm : 2 ≤ m) :
    ∫⁻ t, ‖Tch val H κ n' f (n' * m) t‖ₑ ≤
      ∫⁻ v, ‖f v‖ₑ * ∫⁻ t, ‖gK val v H (constF (kSh κ n')) m t‖ₑ := by
  have hj : Measurable (Function.uncurry fun t v =>
      ‖f v‖ₑ * ‖gK val v H (constF (kSh κ n')) m t‖ₑ) :=
    (hfm.comp measurable_snd).enorm.mul
      ((measurable_gK_start hH (kSh κ n') m).comp (measurable_snd.prodMk measurable_fst)).enorm
  calc ∫⁻ t, ‖Tch val H κ n' f (n' * m) t‖ₑ
      ≤ ∫⁻ t, ∫⁻ v, ‖f v‖ₑ * ‖gK val v H (constF (kSh κ n')) m t‖ₑ := by
        refine lintegral_mono fun t => ?_
        rw [Tch_rep hH hκ hn' hf hfm m hm t]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1; funext v; rw [enorm_mul]
    _ = ∫⁻ v, ∫⁻ t, ‖f v‖ₑ * ‖gK val v H (constF (kSh κ n')) m t‖ₑ :=
        lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ v, ‖f v‖ₑ * ∫⁻ t, ‖gK val v H (constF (kSh κ n')) m t‖ₑ := by
        congr 1; funext v
        exact lintegral_const_mul _ ((measurable_gK_start hH (kSh κ n') m).comp
          (measurable_const.prodMk measurable_id)).enorm

end KR

end
