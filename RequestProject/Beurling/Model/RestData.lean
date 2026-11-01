module

public import RequestProject.Beurling.Model.BtNT
public import RequestProject.Beurling.Model.TcMeas

/-!
# The data fields of `RestRes`: `ρ̃`, `T_c`, `NT = B NT_pt`, `ϑ = 0` as locally integrable
functions, and `T' = T_c + J` locally bounded

* `locInt_LBd_of` : a measurable function bounded on every half-line `(-∞, c]` is in `LocInt`
  and `LBd`;
* `measurable_Kpt` : `K_pt g` is measurable for measurable `g`;
* `ρLc`, `TcLc`, `NTptL` (`ρ̃`, `T_c`, `NT_pt`), `NTc = B NT_pt` (§5.3: `NT` is `NT_pt` after
  the `B`-average), `vtHc = 0` (`ϑ = 0`, eq. (Ttilde): the box term is in `ν`);
* `hTLBd_c` : `T' = T_c + j₀ 1_{[X₀,∞)}` is `LBd`; `LBd` and measurability of `ρ̃`, `T_c`,
  `NT_pt`, `NT`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- A measurable function bounded on every `(-∞, c]` is locally integrable and `LBd`. -/
lemma locInt_LBd_of {f : ℝ → ℝ} (hm : Measurable f) (hb : ∀ c, ∃ M, ∀ t ≤ c, |f t| ≤ M) :
    f ∈ KR.Ops.LocInt ∧ KR.Ops.LBd f := by
  have hL : KR.Ops.LBd f := by
    intro c
    obtain ⟨M, hM⟩ := hb c
    refine ⟨(Set.Iic c).indicator f, ⟨hm.indicator measurableSet_Iic, max M 0, fun t => ?_⟩,
      fun t ht => (Set.indicator_of_mem (Set.mem_Iic.mpr ht) f).symm⟩
    by_cases ht : t ∈ Set.Iic c
    · rw [Set.indicator_of_mem ht]; exact (hM t ht).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem ht]; simp
  refine ⟨fun a b => ?_, hL⟩
  obtain ⟨g, hg, hfg⟩ := hL (max a b)
  refine (hg.intervalIntegrable a b).congr fun t ht => (hfg t ?_).symm
  rcases le_total a b with h | h
  · rw [Set.uIoc_of_le h] at ht; exact ht.2.trans (le_max_right _ _)
  · rw [Set.uIoc_of_ge h] at ht; exact ht.2.trans (le_max_left _ _)

open Classical in
/-- `K_pt g` is measurable for measurable `g` (a locally finite sum over the labels). -/
lemma measurable_Kpt {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} (hX : 0 < X0m) {g : ℝ → ℝ}
    (hg : Measurable g) : Measurable (KR.Sharp.Kpt P tw X0m g) := by
  set F : ℕ → ℝ → ℝ := fun w y =>
    if w ∈ (NAll P y X0m).filter (2 ≤ ·) then
      (if ∀ p ∈ w.primeFactors, tw p * Vl P w < y then g (y / Vl P w) / Vl P w else 0)
    else 0 with hF
  have key : KR.Sharp.Kpt P tw X0m g = fun y => ∑' w, F w y := by
    funext y
    unfold KR.Sharp.Kpt
    rw [tsum_eq_sum (s := (NAll P y X0m).filter (2 ≤ ·)) (fun w hw => by
      simp only [hF]; exact if_neg hw)]
    exact Finset.sum_congr rfl fun w hw => by simp only [hF, if_pos hw]
  rw [key]
  refine measurable_tsum_of_finite_support (fun w => ?_) (fun y => ?_)
  · have hmem : MeasurableSet {y : ℝ | w ∈ (NAll P y X0m).filter (2 ≤ ·)} := by
      have e : {y : ℝ | w ∈ (NAll P y X0m).filter (2 ≤ ·)} =
          {y : ℝ | w ≠ 0 ∧ Vl P w ≤ y / X0m ∧ 2 ≤ w} := by
        ext y
        simp only [mem_setOf_eq, Finset.mem_filter, KR.Sharp.mem_NAll_iff P hX]
        tauto
      rw [e]
      exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const
        (measurable_id.div_const _)).inter (MeasurableSet.const _))
    have hcond : MeasurableSet {y : ℝ | ∀ p ∈ w.primeFactors, tw p * Vl P w < y} := by
      have e : {y : ℝ | ∀ p ∈ w.primeFactors, tw p * Vl P w < y} =
          ⋂ p ∈ w.primeFactors, {y : ℝ | tw p * Vl P w < y} := by
        ext y; simp
      rw [e]
      exact Finset.measurableSet_biInter _ fun p _ => measurableSet_lt measurable_const
        measurable_id
    exact Measurable.ite hmem (Measurable.ite hcond
      ((hg.comp (measurable_id.div_const _)).div_const _) measurable_const) measurable_const
  · refine ((NAll P y X0m).filter (2 ≤ ·)).finite_toSet.subset fun w hw => ?_
    by_contra hn
    exact hw (by simp only [hF]; exact if_neg hn)

section

variable (hc : Cond θ X₀)
include hc

/-- `ρ̃` is measurable and bounded (`0 ≤ ρ̃ ≤ 2`). -/
lemma rhoT_locBd (hev : Even X₀) (ω : JitterΩ) :
    rhoT θ X₀ ω ∈ KR.Ops.LocInt ∧ KR.Ops.LBd (rhoT θ X₀ ω) :=
  locInt_LBd_of (measurable_rhoT ω) fun _ => ⟨2, fun t _ => by
    rw [abs_of_nonneg (rhoT_nonneg ω t)]; exact rhoT_le_two hc hev ω t⟩

/-- `T_c` is measurable and bounded on half-lines. -/
lemma TcR_locBd (hev : Even X₀) (ω : JitterΩ) (j0 : ℝ) :
    TcR θ X₀ ω j0 ∈ KR.Ops.LocInt ∧ KR.Ops.LBd (TcR θ X₀ ω j0) := by
  refine locInt_LBd_of (measurable_TcR hc ω j0) fun c => ?_
  refine ⟨2 + ∑ w ∈ KR.NAll (PR θ X₀ ω) c (Xm X₀), 2 / Vl (PR θ X₀ ω) w + |j0|,
    fun t ht => ?_⟩
  have hρ2 : ∀ z, |rhoT θ X₀ ω z| ≤ 2 := fun z => by
    rw [abs_of_nonneg (rhoT_nonneg ω z)]; exact rhoT_le_two hc hev ω z
  have hK := KAbsR_abs_le hc ω hρ2 ht
  have hT := TpCont_abs_le hc ω t
  have hi : |KR.Chain.ind X₀ t| ≤ 1 := by
    unfold KR.Chain.ind
    by_cases h : t ∈ Set.Ici (X₀ : ℝ)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  have hj : |j0 * KR.Chain.ind X₀ t| ≤ |j0| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hi
  unfold TcR
  have := abs_sub (TpCont θ X₀ ω t + KAbsR θ X₀ ω (rhoT θ X₀ ω) t) (j0 * KR.Chain.ind X₀ t)
  have := abs_add_le (TpCont θ X₀ ω t) (KAbsR θ X₀ ω (rhoT θ X₀ ω) t)
  linarith

/-- `NT_pt = c - K_pt ρ̃ + K_𝒜 ρ̃` is measurable and bounded on half-lines. -/
lemma NTpt_locBd (hev : Even X₀) (ω : JitterΩ) :
    NTpt θ X₀ ω ∈ KR.Ops.LocInt ∧ KR.Ops.LBd (NTpt θ X₀ ω) := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hdm : Measurable (compDen θ X₀ ω) :=
    Measurable.ennreal_tsum fun k => compTerm_meas hc k ω
  refine locInt_LBd_of ?_ (NTpt_bdd hc hev ω)
  unfold NTpt KptR
  exact (hdm.ennreal_toReal.sub (measurable_Kpt hXm (measurable_rhoT ω))).add
    (measurable_KAbsR hc ω (measurable_rhoT ω))

variable (θ X₀) in
/-- `ρ̃` as a locally integrable function. -/
noncomputable def ρLc (hev : Even X₀) (ω : JitterΩ) : KR.Ops.LocInt :=
  ⟨rhoT θ X₀ ω, (rhoT_locBd hc hev ω).1⟩

variable (θ X₀) in
/-- `T_c` as a locally integrable function. -/
noncomputable def TcLc (hev : Even X₀) (ω : JitterΩ) : KR.Ops.LocInt :=
  ⟨TcR θ X₀ ω (jzX X₀), (TcR_locBd hc hev ω _).1⟩

variable (θ X₀) in
/-- `NT_pt` as a locally integrable function. -/
noncomputable def NTptL (hev : Even X₀) (ω : JitterΩ) : KR.Ops.LocInt :=
  ⟨NTpt θ X₀ ω, (NTpt_locBd hc hev ω).1⟩

/-- **`T' = T_c + j₀ 1_{[X₀,∞)}` is `LBd`** (the field `hTLBd`). -/
theorem hTLBd_c (hev : Even X₀) (ω : JitterΩ) :
    KR.Ops.LBd (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) := by
  refine (TcR_locBd hc hev ω _).2.add ?_
  refine KR.Ops.LBd_of_BM ⟨measurable_const.mul (KR.Chain.ind_measurable _), |jzX X₀|,
    fun t => ?_⟩
  have hi : |KR.Chain.ind X₀ t| ≤ 1 := by
    unfold KR.Chain.ind
    by_cases h : t ∈ Set.Ici (X₀ : ℝ)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hi

end

/-! ### `LBd` and measurability, closed under the operations -/

/-- `f ∈ LocInt` is locally bounded and measurable. -/
def LMb (f : KR.Ops.LocInt) : Prop := KR.Ops.LBd (f : ℝ → ℝ) ∧ Measurable (f : ℝ → ℝ)

lemma LMb.add {f g : KR.Ops.LocInt} (hf : LMb f) (hg : LMb g) : LMb (f + g) := by
  refine ⟨?_, hf.2.add hg.2⟩
  have := hf.1.add hg.1
  simpa [AddSubgroup.coe_add, Pi.add_def] using this

lemma LMb.neg {f : KR.Ops.LocInt} (hf : LMb f) : LMb (-f) := by
  refine ⟨?_, hf.2.neg⟩
  have := hf.1.neg
  simpa [Pi.neg_def] using this

lemma LMb.sub {f g : KR.Ops.LocInt} (hf : LMb f) (hg : LMb g) : LMb (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma LMb.zero : LMb (0 : KR.Ops.LocInt) :=
  ⟨by simpa [Pi.zero_def] using KR.Ops.LBd_of_BM KR.BM_zero, by
    simp only [ZeroMemClass.coe_zero]; exact measurable_zero⟩

lemma LMb.Bo {P : BeurlingSystem} {H : ℝ → ℝ} {X0m : ℝ} (hO : KR.Ops.OpHyp P H X0m)
    {f : KR.Ops.LocInt} (hf : LMb f) : LMb (KR.Ops.Bo hO f) :=
  ⟨KR.Ops.LBd.Bavg hO hf.1, (KR.Ops.continuous_Bavg hO.cont hO.pos f.2).measurable⟩

lemma LMb.Ko {P : BeurlingSystem} {H : ℝ → ℝ} {X0m : ℝ} {tw : ℕ → ℝ}
    (hO : KR.Ops.OpHyp P H X0m) {f : KR.Ops.LocInt} (hf : LMb f) :
    LMb (KR.Ops.Ko (tw := tw) hO f) :=
  ⟨KR.Ops.LBd.Kpt hO hf.1, measurable_Kpt hO.X0m_pos hf.2⟩

lemma LMb.JL (j0 : ℝ) : LMb (JL j0 X₀) :=
  ⟨KR.Ops.LBd_of_BM ⟨measurable_const.mul (KR.Chain.ind_measurable _), |j0|, fun t => by
    show |j0 * KR.Chain.ind X₀ t| ≤ |j0|
    rw [abs_mul]
    have := KR.Chain.ind_abs_le (X₀ : ℝ) t
    nlinarith [abs_nonneg j0, abs_nonneg (KR.Chain.ind (X₀ : ℝ) t)]⟩,
    measurable_const.mul (KR.Chain.ind_measurable _)⟩

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma LMb_ρLc (ω : JitterΩ) : LMb (ρLc θ X₀ hc hev ω) :=
  ⟨(rhoT_locBd hc hev ω).2, measurable_rhoT ω⟩

lemma LMb_TcLc (ω : JitterΩ) : LMb (TcLc θ X₀ hc hev ω) :=
  ⟨(TcR_locBd hc hev ω _).2, measurable_TcR hc ω _⟩

lemma LMb_NTptL (ω : JitterΩ) : LMb (NTptL θ X₀ hc hev ω) := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hdm : Measurable (compDen θ X₀ ω) :=
    Measurable.ennreal_tsum fun k => compTerm_meas hc k ω
  refine ⟨(NTpt_locBd hc hev ω).2, ?_⟩
  show Measurable (NTpt θ X₀ ω)
  unfold NTpt KptR
  exact (hdm.ennreal_toReal.sub (measurable_Kpt hXm (measurable_rhoT ω))).add
    (measurable_KAbsR hc ω (measurable_rhoT ω))

end

/-! ### The data, as functions of `(θ, X₀, ω)` only -/

open Classical in
variable (θ X₀) in
/-- `ρ̃ ∈ LocInt` (the field `ρL`). -/
noncomputable def ρLd (ω : JitterΩ) : KR.Ops.LocInt :=
  if h : Cond θ X₀ ∧ Even X₀ then ρLc θ X₀ h.1 h.2 ω else 0

open Classical in
variable (θ X₀) in
/-- `T_c ∈ LocInt` (the field `TcL`). -/
noncomputable def TcLd (ω : JitterΩ) : KR.Ops.LocInt :=
  if h : Cond θ X₀ ∧ Even X₀ then TcLc θ X₀ h.1 h.2 ω else 0

open Classical in
variable (θ X₀) in
/-- `NT_pt ∈ LocInt`. -/
noncomputable def NTptLd (ω : JitterΩ) : KR.Ops.LocInt :=
  if h : Cond θ X₀ ∧ Even X₀ then NTptL θ X₀ h.1 h.2 ω else 0

open Classical in
variable (θ X₀) in
/-- **`NT = B NT_pt`** (the field `NT`; §5.3). -/
noncomputable def NTd (ω : JitterΩ) : KR.Ops.LocInt :=
  if h : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) then KR.Ops.Bo h (NTptLd θ X₀ ω)
  else 0

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma ρLd_coe (ω : JitterΩ) : (ρLd θ X₀ ω : ℝ → ℝ) = rhoT θ X₀ ω := by
  unfold ρLd; rw [dif_pos ⟨hc, hev⟩]; rfl

lemma TcLd_coe (ω : JitterΩ) : (TcLd θ X₀ ω : ℝ → ℝ) = TcR θ X₀ ω (jzX X₀) := by
  unfold TcLd; rw [dif_pos ⟨hc, hev⟩]; rfl

lemma NTptLd_coe (ω : JitterΩ) : (NTptLd θ X₀ ω : ℝ → ℝ) = NTpt θ X₀ ω := by
  unfold NTptLd; rw [dif_pos ⟨hc, hev⟩]; rfl

lemma LMb_ρLd (ω : JitterΩ) : LMb (ρLd θ X₀ ω) := by
  unfold ρLd; rw [dif_pos ⟨hc, hev⟩]; exact LMb_ρLc hc hev ω

lemma LMb_TcLd (ω : JitterΩ) : LMb (TcLd θ X₀ ω) := by
  unfold TcLd; rw [dif_pos ⟨hc, hev⟩]; exact LMb_TcLc hc hev ω

lemma LMb_NTd (ω : JitterΩ) : LMb (NTd θ X₀ ω) := by
  unfold NTd
  split_ifs with h
  · refine LMb.Bo h ?_
    unfold NTptLd; rw [dif_pos ⟨hc, hev⟩]; exact LMb_NTptL hc hev ω
  · exact LMb.zero

end

lemma NTd_eq (ω : JitterΩ) (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    NTd θ X₀ ω = KR.Ops.Bo hO (NTptLd θ X₀ ω) := by
  unfold NTd; rw [dif_pos hO]

end BModel

end
