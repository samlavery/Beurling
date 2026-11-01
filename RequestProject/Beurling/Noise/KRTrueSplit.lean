module

public import RequestProject.Beurling.Noise.KRNear

/-!
# Proposition 5.18, proof: the split of the source into `τ`-near and `X₀`-near parts

For the true filters `φ = trueFilter` and the nominal filters `κ = nomFilter` (the true filter at
the nominal point), the Duhamel source `S_n = ∑_{d<n} (P_{d→n} - P^nom_{d→n}) C_d` is split as in
the paper: the `X₀`-near steps go to `S^{X₀}_n`, the others to `S^τ_n` (`SsrcP`). We prove:

* `srcStep_one` : the step from `C_1 = δ_x` has no source (its centre is the nominal point);
* `srcStep_eq_zero_far` : off `τ`-near and `X₀`-near steps the source vanishes
  (Lemma 5.12(i) with the support of the true kernels, `gK_support`);
* `lintegral_srcStep_le` : `∫ |(P - P^nom)C_d| ≤ TV(C_d)`, and it vanishes unless
  `x/n ≥ X₀⁻` on non-`X₀`-near steps (`srcStep_eq_zero_low`);
* `SX0_eq_zero` : `S^{X₀}_n = 0` at non-terminal levels (Lemma 5.12(ii));
* `Tch_terminal` : the nominal chains from a terminal level vanish (Lemma 5.12(iii)), so
  `Etil_split` : `Ẽ_n = ∑_{n' ∣ n} 𝒯^nom_{n'→n} S^τ_{n'} + S^{X₀}_n`.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ}

/-! ## Linearity of the chains -/

lemma Tch_add (hH : WidthReg H) (κ : ℕ → ℕ → ℝ) (n' : ℕ) {f g : ℝ → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (hg : Integrable g) (hgm : Measurable g) :
    ∀ n t, Tch val H κ n' (fun v => f v + g v) n t =
      Tch val H κ n' f n t + Tch val H κ n' g n t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t
  rcases lt_trichotomy n n' with h | h | h
  · rw [Tch_lt _ h, Tch_lt _ h, Tch_lt _ h]; ring
  · subst h; rw [Tch_self, Tch_self, Tch_self]
  · rw [Tch_eq _ h, Tch_eq _ h, Tch_eq _ h, ← neg_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdl := (Nat.mem_properDivisors.mp hd).2
    have e : Tch val H κ n' (fun v => f v + g v) d =
        fun v => Tch val H κ n' f d v + Tch val H κ n' g d v := funext (ih d hdl)
    rw [e, Qd_add hH _ (integrable_Tch hH κ n' hf hfm d).1 (integrable_Tch hH κ n' hg hgm d).1]
    ring

lemma Tch_zero_fun (κ : ℕ → ℕ → ℝ) (n' : ℕ) :
    ∀ n, Tch val H κ n' (fun _ => 0) n = fun _ => 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases lt_trichotomy n n' with h | h | h
  · exact Tch_lt _ h
  · subst h; exact Tch_self _ _ _
  · funext t
    rw [Tch_eq _ h, Finset.sum_eq_zero fun d hd => ?_, neg_zero]
    rw [ih d (Nat.mem_properDivisors.mp hd).2]
    unfold Qd; simp

lemma Tch_congr (κ : ℕ → ℕ → ℝ) (n' : ℕ) {f g : ℝ → ℝ} (h : ∀ v, f v = g v) (n : ℕ) :
    Tch val H κ n' f n = Tch val H κ n' g n := by
  rw [show f = g from funext h]

/-- If `x/n < X₀⁻` the nominal filters into `n` vanish, so every chain through a step into `n`
vanishes. -/
lemma Tch_eq_zero_low (hval : ∀ p, p.Prime → 1 ≤ val p) {tw : ℕ → ℝ} {X0m : ℝ} (n' : ℕ)
    (f : ℝ → ℝ) {n : ℕ} (hn : n' < n) (hlow : posn val x n < X0m) :
    Tch val H (nomFilter val x tw X0m) n' f n = fun _ => 0 := by
  funext t
  rw [Tch_eq _ hn, Finset.sum_eq_zero fun d _ => ?_, neg_zero]
  rw [nomFilter_eq_trueFilter hval]
  unfold trueFilter
  rw [if_neg (fun h => absurd h.2 (not_le.mpr hlow)), zero_mul]

/-- **Chains from a terminal level vanish** (Lemma 5.12(iii)). -/
theorem Tch_terminal {X0m X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {tw : ℕ → ℝ} {n' : ℕ} (hn'2 : 1 ≤ n')
    (hpos : X0m / 2 ≤ posn val x n') (hT : Terminal val x H X0m X0 n') (f : ℝ → ℝ)
    {n : ℕ} (hn : n ≠ n') : Tch val H (nomFilter val x tw X0m) n' f n = fun _ => 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  by_cases hd : n' ∣ n
  · rcases lt_or_gt_of_ne hn with h | h
    · exact Tch_lt _ h
    obtain ⟨m, rfl⟩ := hd
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · simp at h
        · simp at hn
      · exact hm
    apply Tch_eq_zero_low hval n' f h
    have hn0 : n' * m ≠ 0 := by positivity
    have hpm : posn val x (n' * m) = posn val x n' / LemmaM.valN val m := by
      have := posn_div (x := x) hval (dvd_mul_right n' m) hn0
      rw [Nat.mul_div_cancel_left m (by omega)] at this
      exact this.symm
    rw [hpm]
    have hw := two_le_valN hval2 hm2
    exact (near_iii hP hX0 hpos hT hw (v := posn val x n')
      (by rw [sub_self, abs_zero]; have := hP.reg.pos (posn val x n'); positivity)).2
  · exact Tch_not_dvd f n hd

/-! ## The source of a single step -/

variable (tw : ℕ → ℝ) (X0m : ℝ)

/-- The true filters. -/
noncomputable abbrev phiT : ℕ → ℕ → ℝ → ℝ := trueFilter tw X0m

/-- The nominal filters. -/
noncomputable abbrev kapN (val : ℕ → ℝ) (x : ℝ) : ℕ → ℕ → ℝ := nomFilter val x tw X0m

variable {tw X0m}

lemma kapN_mem (val : ℕ → ℝ) (x : ℝ) (d n : ℕ) :
    0 ≤ kapN tw X0m val x d n ∧ kapN tw X0m val x d n ≤ 1 := by
  unfold kapN nomFilter; split_ifs <;> norm_num

/-- The step from `C_1 = δ_x` has no source: its centre is the nominal landing point. -/
lemma srcStep_one (hval : ∀ p, p.Prime → 1 ≤ val p) (n : ℕ) (t : ℝ) :
    srcStep val x H (phiT tw X0m) (kapN tw X0m val x) 1 n t = 0 := by
  unfold srcStep
  rw [if_pos rfl, kapN, nomFilter_eq_trueFilter hval, sub_self, zero_mul]

lemma integrable_gKT (hH : WidthReg H) (n : ℕ) :
    Integrable (gK val x H (phiT tw X0m) n) ∧ Measurable (gK val x H (phiT tw X0m) n) :=
  integrable_gK hH (trueFilter_ok tw X0m) n

/-- A non-zero true filter at a centre `v/w` with `v` in the support of `C_d` forces
`x/n ≥ X₀⁻/2`. -/
lemma pos_of_centre {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ val p)
    {d n : ℕ} (hd : d ∈ n.properDivisors) {v : ℝ}
    (hposd : X0m / 2 ≤ posn val x d) (hvd : |v - posn val x d| ≤ 1.02 * H (posn val x d))
    (hc : X0m ≤ v / LemmaM.valN val (n / d)) : X0m / 2 ≤ posn val x n := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
  have hpd : posn val x d = posn val x n * LemmaM.valN val (n / d) := posn_mul hval hdn hn0
  have hsmd := hP.small (posn val x d) hposd
  have hXm := hP.X0m_pos
  have h1 : v ≤ 1.102 * posn val x d := by linarith [(abs_le.mp hvd).2]
  have h2 : X0m * LemmaM.valN val (n / d) ≤ v := by rwa [le_div_iff₀ hw0] at hc
  rw [hpd] at h1
  nlinarith

/-- **Off near steps the source vanishes** (Lemma 5.12(i)). -/
theorem srcStep_eq_zero_far {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {d n : ℕ} (hd : d ∈ n.properDivisors)
    (hτ : ¬ TauNear val x H tw d n) (hX : ¬ X0Near val x H X0m d n) (t : ℝ) :
    srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t = 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  by_cases h1 : d = 1
  · subst h1; exact srcStep_one hval n t
  unfold srcStep
  rw [if_neg h1]
  unfold Qd
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
  simp only [Pi.zero_apply]
  by_cases hg : gK val x H (phiT tw X0m) d v = 0
  · rw [hg]; ring
  obtain ⟨hposd, hvd⟩ := hsupp d v hg
  by_cases hφ : trueFilter tw X0m d n (v / LemmaM.valN val (n / d)) = 0
  · -- then the nominal filter vanishes too, unless `x/n ≥ X₀⁻/2`
    by_cases hpos : X0m / 2 ≤ posn val x n
    · rw [show phiT tw X0m d n (v / LemmaM.valN val (n / d)) =
          kapN tw X0m val x d n from near_i hP hval2 hd hpos hτ hX hvd]
      ring
    · have hk : kapN tw X0m val x d n = 0 := by
        unfold kapN; rw [nomFilter_eq_trueFilter hval]
        unfold trueFilter
        rw [if_neg (fun h => hpos (by linarith [h.2, hP.X0m_pos]))]
      rw [show phiT tw X0m d n (v / LemmaM.valN val (n / d)) = 0 from hφ, hk]; ring
  · have hpos := pos_of_centre hP hval2 hd hposd hvd (trueFilter_ne_zero hφ)
    rw [show phiT tw X0m d n (v / LemmaM.valN val (n / d)) =
        kapN tw X0m val x d n from near_i hP hval2 hd hpos hτ hX hvd]
    ring

/-- `∫ |(P_{d→n} - P^nom_{d→n}) C_d| ≤ TV(C_d)` (for `d ≥ 2`; the step from `d = 1` has no
source). -/
theorem lintegral_srcStep_le (hH : WidthReg H) {d n : ℕ} (hd1 : d ≠ 1) :
    ∫⁻ t, ‖srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t‖ₑ ≤
      ∫⁻ v, ‖gK val x H (phiT tw X0m) d v‖ₑ := by
  have e : srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n =
      Qd H (LemmaM.valN val (n / d)) (fun v => (phiT tw X0m d n (v / LemmaM.valN val (n / d)) -
        kapN tw X0m val x d n) * gK val x H (phiT tw X0m) d v) := by
    funext t; unfold srcStep; rw [if_neg hd1]
  rw [e]
  have hm := (integrable_gKT (val := val) (x := x) (tw := tw) (X0m := X0m) hH d).2
  refine (lintegral_Qd_le hH _ ?_).trans (lintegral_mono fun v => ?_)
  · exact (((trueFilter_ok tw X0m d n).1.comp (measurable_id.div_const _)).sub
      measurable_const).mul hm
  · rw [enorm_mul]
    have h1 : ‖phiT tw X0m d n (v / LemmaM.valN val (n / d)) - kapN tw X0m val x d n‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_one.mpr
      have := (trueFilter_ok tw X0m d n).2 (v / LemmaM.valN val (n / d))
      have := kapN_mem (tw := tw) (X0m := X0m) val x d n
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ 1 * ‖gK val x H (phiT tw X0m) d v‖ₑ := by gcongr
      _ = _ := one_mul _

/-- On a step that is not `X₀`-near, the source vanishes unless `x/n ≥ X₀⁻` (the paper: the
difference `(φ_τ - κ_τ) κ_{X₀}` carries the factor `κ_{X₀} = 1[x/n ≥ X₀⁻]`). -/
theorem srcStep_eq_zero_low {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {d n : ℕ} (hd : d ∈ n.properDivisors)
    (hX : ¬ X0Near val x H X0m d n) (hlow : posn val x n < X0m) (t : ℝ) :
    srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t = 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  by_cases h1 : d = 1
  · subst h1; exact srcStep_one hval n t
  have hk : kapN tw X0m val x d n = 0 := by
    unfold kapN; rw [nomFilter_eq_trueFilter hval]
    unfold trueFilter
    rw [if_neg (fun h => absurd h.2 (not_le.mpr hlow))]
  unfold srcStep
  rw [if_neg h1]
  unfold Qd
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
  simp only [Pi.zero_apply]
  by_cases hg : gK val x H (phiT tw X0m) d v = 0
  · rw [hg]; ring
  obtain ⟨hposd, hvd⟩ := hsupp d v hg
  rw [hk]
  by_cases hφ : trueFilter tw X0m d n (v / LemmaM.valN val (n / d)) = 0
  · rw [show phiT tw X0m d n (v / LemmaM.valN val (n / d)) = 0 from hφ]; ring
  · -- a non-zero true filter: `v/w ≥ X₀⁻ > x/n`, but `|v/w - x/n| ≤ R_d/w < |x/n - X₀⁻|`
    exfalso
    have hc := trueFilter_ne_zero hφ
    have hpos := pos_of_centre hP hval2 hd hposd hvd hc
    have hdn := (Nat.mem_properDivisors.mp hd).1
    have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
    have hw := two_le_valN hval2 (two_le_div_of_mem hd)
    have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
    have hpd : posn val x d = posn val x n * LemmaM.valN val (n / d) := posn_mul hval hdn hn0
    have hcc : |v / LemmaM.valN val (n / d) - posn val x n| ≤
        1.02 * H (posn val x d) / LemmaM.valN val (n / d) := by
      have e : v / LemmaM.valN val (n / d) - posn val x n =
          (v - posn val x d) / LemmaM.valN val (n / d) := by rw [hpd]; field_simp
      rw [e, abs_div, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right hvd hw0.le
    unfold X0Near at hX
    push_neg at hX
    rw [abs_of_neg (by linarith)] at hX
    linarith [(abs_le.mp hcc).2]

/-! ## The split -/

variable (val x H tw X0m)

/-- The part of the source on the steps satisfying `p`. -/
noncomputable def SsrcP (p : ℕ → ℕ → Prop) [DecidableRel p] (n : ℕ) (t : ℝ) : ℝ :=
  - ∑ d ∈ n.properDivisors.filter (fun d => p d n),
    srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t

/-- `S^τ_n`: the steps that are not `X₀`-near. -/
noncomputable def Stau (n : ℕ) (t : ℝ) : ℝ :=
  open scoped Classical in SsrcP val x H tw X0m (fun d n => ¬ X0Near val x H X0m d n) n t

/-- `S^{X₀}_n`: the `X₀`-near steps. -/
noncomputable def SX0 (n : ℕ) (t : ℝ) : ℝ :=
  open scoped Classical in SsrcP val x H tw X0m (fun d n => X0Near val x H X0m d n) n t

variable {val x H tw X0m}

lemma Ssrc_split (n : ℕ) (t : ℝ) :
    Ssrc val x H (phiT tw X0m) (kapN tw X0m val x) n t =
      Stau val x H tw X0m n t + SX0 val x H tw X0m n t := by
  classical
  unfold Ssrc Stau SX0 SsrcP
  rw [← neg_add, Finset.sum_filter_not_add_sum_filter]

lemma integrable_srcStep (hH : WidthReg H) (d n : ℕ) :
    Integrable (srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n) ∧
      Measurable (srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n) := by
  by_cases h1 : d = 1
  · have e : srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n = fun t =>
        (phiT tw X0m 1 n (posn val x n) - kapN tw X0m val x 1 n) * kd H (posn val x n) t := by
      funext t; unfold srcStep; rw [if_pos h1]
    rw [e]; exact ⟨(integrable_kd hH _).const_mul _, (measurable_kd_left hH _).const_mul _⟩
  · have e : srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n =
        Qd H (LemmaM.valN val (n / d)) (fun v => (phiT tw X0m d n (v / LemmaM.valN val (n / d)) -
          kapN tw X0m val x d n) * gK val x H (phiT tw X0m) d v) := by
      funext t; unfold srcStep; rw [if_neg h1]
    rw [e]
    obtain ⟨hi, hm⟩ := integrable_gKT (val := val) (x := x) (tw := tw) (X0m := X0m) hH d
    have hb' : ∀ c, |phiT tw X0m d n c - kapN tw X0m val x d n| ≤ 1 := fun c => by
      have := (trueFilter_ok tw X0m d n).2 c
      have := kapN_mem (tw := tw) (X0m := X0m) val x d n
      rw [abs_le]; constructor <;> linarith
    have hmf : Measurable fun c => phiT tw X0m d n c - kapN tw X0m val x d n :=
      (trueFilter_ok tw X0m d n).1.sub measurable_const
    have hm2 := measurable_mul_comp hmf hm (LemmaM.valN val (n / d))
    exact ⟨integrable_Qd hH _ (integrable_mul_comp hmf hb' hi _) hm2, measurable_Qd hH _ hm2⟩

lemma integrable_SsrcP (hH : WidthReg H) (p : ℕ → ℕ → Prop) [DecidableRel p] (n : ℕ) :
    Integrable (SsrcP val x H tw X0m p n) ∧ Measurable (SsrcP val x H tw X0m p n) := by
  have e : SsrcP val x H tw X0m p n = fun t => - ∑ d ∈ n.properDivisors.filter (fun d => p d n),
      srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t := rfl
  rw [e]
  exact ⟨(integrable_finset_sum _ fun d _ => (integrable_srcStep hH d n).1).neg,
    (Finset.measurable_sum _ fun d _ => (integrable_srcStep hH d n).2).neg⟩

lemma integrable_Stau (hH : WidthReg H) (n : ℕ) :
    Integrable (Stau val x H tw X0m n) ∧ Measurable (Stau val x H tw X0m n) := by
  classical
  exact integrable_SsrcP hH _ n

lemma integrable_SX0 (hH : WidthReg H) (n : ℕ) :
    Integrable (SX0 val x H tw X0m n) ∧ Measurable (SX0 val x H tw X0m n) := by
  classical
  exact integrable_SsrcP hH _ n

/-- **`S^{X₀}_n = 0` at non-terminal levels** (Lemma 5.12(ii)). -/
theorem SX0_eq_zero {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {n : ℕ} (hT : ¬ Terminal val x H X0m X0 n) (t : ℝ) :
    SX0 val x H tw X0m n t = 0 := by
  classical
  unfold SX0 SsrcP
  rw [Finset.sum_eq_zero fun d hd => ?_, neg_zero]
  obtain ⟨hdm, hXd⟩ := Finset.mem_filter.mp hd
  by_cases hpos : X0m / 2 ≤ posn val x n
  · exact absurd (near_ii hP hX0 hval2 hdm hpos hXd).2 hT
  · -- `x/n < X₀⁻/2`: the source of the step vanishes
    have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
    by_cases h1 : d = 1
    · subst h1; exact srcStep_one hval n t
    unfold srcStep
    rw [if_neg h1]
    unfold Qd
    have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
      (fun d n c h => trueFilter_ne_zero h)
    have hk : kapN tw X0m val x d n = 0 := by
      unfold kapN; rw [nomFilter_eq_trueFilter hval]
      unfold trueFilter
      rw [if_neg (fun h => hpos (by linarith [h.2, hP.X0m_pos]))]
    rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
    simp only [Pi.zero_apply]
    by_cases hg : gK val x H (phiT tw X0m) d v = 0
    · rw [hg]; ring
    obtain ⟨hposd, hvd⟩ := hsupp d v hg
    rw [hk]
    by_cases hφ : trueFilter tw X0m d n (v / LemmaM.valN val (n / d)) = 0
    · rw [show phiT tw X0m d n (v / LemmaM.valN val (n / d)) = 0 from hφ]; ring
    · exact absurd (pos_of_centre hP hval2 hdm hposd hvd (trueFilter_ne_zero hφ)) hpos

/-- **The split Duhamel form**:
`Ẽ_n = ∑_{n' ∣ n, n' ≥ 2} 𝒯^nom_{n'→n} S^τ_{n'} + S^{X₀}_n` (`n ≥ 2`). -/
theorem Etil_split {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    Etil val x H (phiT tw X0m) (kapN tw X0m val x) n t =
      ∑ n' ∈ n.divisors.filter (2 ≤ ·),
        Tch val H (kapN tw X0m val x) n' (Stau val x H tw X0m n') n t +
      SX0 val x H tw X0m n t := by
  have hH := hP.reg
  have hφ := trueFilter_ok tw X0m
  have hκ := kapN_mem (tw := tw) (X0m := X0m) val x
  rw [Etil_eq_chain hH hφ hκ n hn]
  simp only
  have hsplit : ∀ n' ∈ n.divisors.filter (2 ≤ ·),
      Tch val H (kapN tw X0m val x) n' (Ssrc val x H (phiT tw X0m) (kapN tw X0m val x) n') n t =
        Tch val H (kapN tw X0m val x) n' (Stau val x H tw X0m n') n t +
        Tch val H (kapN tw X0m val x) n' (SX0 val x H tw X0m n') n t := by
    intro n' _
    rw [Tch_congr _ n' (Ssrc_split (val := val) (x := x) (H := H) (tw := tw) (X0m := X0m) n') n]
    exact Tch_add hH _ n' (integrable_Stau hH n').1 (integrable_Stau hH n').2
      (integrable_SX0 hH n').1 (integrable_SX0 hH n').2 n t
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  have hn0 : n ≠ 0 := by omega
  have hmem : n ∈ n.divisors.filter (2 ≤ ·) := by simp [hn0, hn]
  rw [Finset.sum_eq_single n]
  · rw [Tch_self]
  · intro n' hn' hne
    have hn'2 := (Finset.mem_filter.mp hn').2
    by_cases hz : ∀ v, SX0 val x H tw X0m n' v = 0
    · rw [Tch_congr _ n' hz n, Tch_zero_fun]
    push_neg at hz
    obtain ⟨v, hv⟩ := hz
    -- a non-zero `S^{X₀}` sits at a terminal level with `x/n' ≥ X₀⁻/2`
    have hT : Terminal val x H X0m X0 n' := by
      by_contra hT; exact hv (SX0_eq_zero hP hX0 hval2 hT v)
    have hpos : X0m / 2 ≤ posn val x n' := by
      classical
      by_contra hpos
      apply hv
      unfold SX0 SsrcP
      rw [Finset.sum_eq_zero fun d hd => ?_, neg_zero]
      obtain ⟨hdm, -⟩ := Finset.mem_filter.mp hd
      have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
      by_cases h1 : d = 1
      · subst h1; exact srcStep_one hval n' v
      have hk : kapN tw X0m val x d n' = 0 := by
        unfold kapN; rw [nomFilter_eq_trueFilter hval]
        unfold trueFilter
        rw [if_neg (fun h => hpos (by linarith [h.2, hP.X0m_pos]))]
      unfold srcStep
      rw [if_neg h1]
      unfold Qd
      have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
        (fun d n c h => trueFilter_ne_zero h)
      rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)]
      simp only [Pi.zero_apply]
      by_cases hg : gK val x H (phiT tw X0m) d s = 0
      · rw [hg]; ring
      obtain ⟨hposd, hsd⟩ := hsupp d s hg
      rw [hk]
      by_cases hφ : trueFilter tw X0m d n' (s / LemmaM.valN val (n' / d)) = 0
      · rw [show phiT tw X0m d n' (s / LemmaM.valN val (n' / d)) = 0 from hφ]; ring
      · exact absurd (pos_of_centre hP hval2 hdm hposd hsd (trueFilter_ne_zero hφ)) hpos
    rw [Tch_terminal hP hX0 hval2 (by omega) hpos hT _ (Ne.symm hne)]
  · intro h; exact absurd hmem h

end KR

end
