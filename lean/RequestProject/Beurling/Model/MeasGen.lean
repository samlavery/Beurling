module

public import RequestProject.Beurling.Model.Fix
public import RequestProject.Beurling.ZBConcrete

/-!
# Generic measurability lemmas for the construction

Tools for the measurability of the construction of §3 in the jitters:

* `measurable_uncurry_of_rcont` : measurable in `ω` and right-continuous in `x` gives joint
  measurability;
* `measurable_tsum_of_finite_support` : a sum over a countable index with finite support at every
  point;
* `measurable_ncard`, `measurable_ncard_image`, `measurable_tsum_image` : counts and sums over a
  measurable finite family and over its distinct values;
* `measurable_earlyNoise`, `continuous_earlyNoise` : the early transform `D̂_{<a}`;
* `measurable_chooseHeight` : the least good height of Lemma 4.8 is a measurable function of the
  data (§3.2: `γ_k` is a measurable function of the system on `[1, x_k)`).
-/

@[expose] public section

open Set Real MeasureTheory Filter Topology Complex Metric

namespace BModel

/-! ### Joint measurability from right-continuity -/

/-- The dyadic grid point `(⌊x 2^n⌋ + 1)/2^n` to the right of `x`. -/
noncomputable def dyadR (n : ℕ) (x : ℝ) : ℝ := ((⌊x * 2 ^ n⌋ : ℝ) + 1) / 2 ^ n

lemma dyadR_gt (n : ℕ) (x : ℝ) : x < dyadR n x := by
  unfold dyadR
  rw [lt_div_iff₀ (by positivity)]
  exact Int.lt_floor_add_one _

lemma dyadR_le (n : ℕ) (x : ℝ) : dyadR n x ≤ x + 1 / 2 ^ n := by
  unfold dyadR
  rw [div_le_iff₀ (by positivity)]
  have := Int.floor_le (x * 2 ^ n)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [add_mul, one_div_mul_cancel h2.ne']
  linarith

lemma tendsto_dyadR (x : ℝ) : Tendsto (fun n => dyadR n x) atTop (𝓝[>] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => dyadR_gt n x⟩
  have h : Tendsto (fun n : ℕ => x + 1 / (2 : ℝ) ^ n) atTop (𝓝 (x + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => (dyadR_gt n x).le) (fun n => dyadR_le n x)

/-- **Measurable in `ω` and right-continuous in `x` gives joint measurability.** -/
theorem measurable_uncurry_of_rcont {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hm : ∀ x, Measurable fun ω => f ω x) (hc : ∀ ω x, ContinuousWithinAt (f ω) (Set.Ici x) x) :
    Measurable (Function.uncurry f) := by
  have happ : ∀ n : ℕ, Measurable fun p : Ω × ℝ => f p.1 (dyadR n p.2) := by
    intro n
    have hF : Measurable fun q : Ω × ℤ => f q.1 (((q.2 : ℝ) + 1) / 2 ^ n) :=
      measurable_from_prod_countable_left fun k => by simpa using hm (((k : ℝ) + 1) / 2 ^ n)
    have hfl : Measurable fun p : Ω × ℝ => (p.1, ⌊p.2 * 2 ^ n⌋) :=
      measurable_fst.prodMk (Int.measurable_floor.comp (measurable_snd.mul_const _))
    exact hF.comp hfl
  refine measurable_of_tendsto_metrizable happ (tendsto_pi_nhds.mpr fun p => ?_)
  have h1 : ContinuousWithinAt (f p.1) (Set.Ioi p.2) p.2 :=
    (hc p.1 p.2).mono Set.Ioi_subset_Ici_self
  exact h1.tendsto.comp (tendsto_dyadR p.2)

/-! ### Sums and counts over countable families -/

/-- **A sum over a countable index with finite support at every point is measurable.** -/
theorem measurable_tsum_of_finite_support {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ} (hf : ∀ i, Measurable (f i))
    (hfin : ∀ x, (Function.support fun i => f i x).Finite) :
    Measurable fun x => ∑' i, f i x := by
  classical
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat ι
  set f' : ℕ → α → ℝ := fun n x => if h : ∃ i, enc i = n then f h.choose x else 0 with hf'
  have hf'm : ∀ n, Measurable (f' n) := by
    intro n
    simp only [hf']
    split_ifs
    · exact hf _
    · exact measurable_const
  have hre : ∀ x, ∑' n, f' n x = ∑' i, f i x := by
    intro x
    have hsupp : Function.support (fun n => f' n x) ⊆ Set.range enc := by
      intro n hn
      simp only [Function.mem_support, hf'] at hn
      split_ifs at hn with h
      · exact h
      · exact absurd rfl hn
    rw [← henc.tsum_eq hsupp]
    congr 1
    funext i
    have hex : ∃ j, enc j = enc i := ⟨i, rfl⟩
    simp only [hf', dif_pos hex]
    rw [henc hex.choose_spec]
  have hsum : ∀ x, HasSum (fun n => f' n x) (∑' n, f' n x) := by
    intro x
    apply Summable.hasSum
    apply summable_of_finite_support
    have : Function.support (fun n => f' n x) ⊆ enc '' Function.support (fun i => f i x) := by
      intro n hn
      simp only [Function.mem_support, hf'] at hn
      split_ifs at hn with h
      · exact ⟨h.choose, hn, h.choose_spec⟩
      · exact absurd rfl hn
    exact ((hfin x).image enc).subset this
  have hlim : Tendsto (fun N x => ∑ n ∈ Finset.range N, f' n x) atTop
      (𝓝 fun x => ∑' i, f i x) := by
    refine tendsto_pi_nhds.mpr fun x => ?_
    rw [← hre x]
    exact (hsum x).tendsto_sum_nat
  exact measurable_of_tendsto_metrizable (fun N => Finset.measurable_sum _ fun n _ => hf'm n) hlim

/-- **Counting a measurable finite subset of a countable type.** -/
theorem measurable_ncard {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {S : Ω → Set ι}
    (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) (hfin : ∀ ω, (S ω).Finite) :
    Measurable fun ω => ((S ω).ncard : ℝ) := by
  classical
  have he : ∀ ω, ((S ω).ncard : ℝ) = ∑' i, (if i ∈ S ω then (1 : ℝ) else 0) := by
    intro ω
    rw [tsum_eq_sum (s := (hfin ω).toFinset) (fun i hi => by
      simp only [Set.Finite.mem_toFinset] at hi; simp [hi])]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card _ (hfin ω)]
    congr 2
    ext i; simp
  simp_rw [he]
  refine measurable_tsum_of_finite_support (fun i => ?_) (fun ω => ?_)
  · exact Measurable.ite (hS i) measurable_const measurable_const
  · refine (hfin ω).subset fun i hi => ?_
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hi
    exact hi

/-- The first representatives of the values: `i ∈ S` such that no `j ∈ S` of smaller code has the
same value. -/
def firstRep {ι : Type*} (enc : ι → ℕ) (S : Set ι) (g : ι → ℝ) : Set ι :=
  {i | i ∈ S ∧ ∀ j ∈ S, enc j < enc i → g j ≠ g i}

lemma image_firstRep {ι : Type*} {enc : ι → ℕ} (S : Set ι) (g : ι → ℝ) :
    g '' firstRep enc S g = g '' S := by
  classical
  apply le_antisymm
  · exact Set.image_mono fun i hi => hi.1
  · rintro a ⟨i, hi, rfl⟩
    have hex : ∃ n, ∃ j ∈ S, g j = g i ∧ enc j = n := ⟨enc i, i, hi, rfl, rfl⟩
    obtain ⟨j, hj, hgj, hej⟩ := Nat.find_spec hex
    refine ⟨j, ⟨hj, fun j' hj' hlt hg => ?_⟩, hgj⟩
    have := Nat.find_min hex (hej ▸ hlt)
    exact this ⟨j', hj', hg.trans hgj, rfl⟩

lemma injOn_firstRep {ι : Type*} {enc : ι → ℕ} (henc : Function.Injective enc) (S : Set ι)
    (g : ι → ℝ) : Set.InjOn g (firstRep enc S g) := by
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (henc h)) with h | h
  · exact hj.2 i hi.1 h hij
  · exact hi.2 j hj.1 h hij.symm

lemma measurableSet_firstRep {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (enc : ι → ℕ)
    {S : Ω → Set ι} {g : Ω → ι → ℝ} (hS : ∀ i, MeasurableSet {ω | i ∈ S ω})
    (hg : ∀ i, Measurable fun ω => g ω i) (i : ι) :
    MeasurableSet {ω | i ∈ firstRep enc (S ω) (g ω)} := by
  have e : {ω | i ∈ firstRep enc (S ω) (g ω)} =
      {ω | i ∈ S ω} ∩ ⋂ j : ι, ({ω | j ∈ S ω}ᶜ ∪ {ω | ¬ enc j < enc i} ∪
        {ω | g ω j ≠ g ω i}) := by
    ext ω
    simp only [firstRep, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j => ?_⟩
      by_cases hj : j ∈ S ω
      · by_cases hlt : enc j < enc i
        · exact Or.inr (h2 j hj hlt)
        · exact Or.inl (Or.inr hlt)
      · exact Or.inl (Or.inl hj)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj hlt => ?_⟩
      rcases h2 j with (h | h) | h
      · exact absurd hj h
      · exact absurd hlt h
      · exact h
  rw [e]
  refine (hS i).inter (MeasurableSet.iInter fun j => ?_)
  refine ((hS j).compl.union ?_).union ?_
  · by_cases h : enc j < enc i
    · simp [h]
    · simp [h]
  · exact (measurableSet_eq_fun (hg j) (hg i)).compl

/-- **The number of distinct values of a measurable finite family.** -/
theorem measurable_ncard_image {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {S : Ω → Set ι} {g : Ω → ι → ℝ} (hS : ∀ i, MeasurableSet {ω | i ∈ S ω})
    (hg : ∀ i, Measurable fun ω => g ω i) (hfin : ∀ ω, (S ω).Finite) :
    Measurable fun ω => ((g ω '' S ω).ncard : ℝ) := by
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat ι
  have he : ∀ ω, ((g ω '' S ω).ncard : ℝ) = ((firstRep enc (S ω) (g ω)).ncard : ℝ) := by
    intro ω
    rw [← image_firstRep (enc := enc), (injOn_firstRep henc _ _).ncard_image]
  simp_rw [he]
  exact measurable_ncard (measurableSet_firstRep enc hS hg)
    (fun ω => (hfin ω).subset fun i hi => hi.1)

open Classical in
/-- **A sum over the distinct values of a measurable family** (support finite at every point). -/
theorem measurable_tsum_image {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {S : Ω → Set ι} {g : Ω → ι → ℝ} (hS : ∀ i, MeasurableSet {ω | i ∈ S ω})
    (hg : ∀ i, Measurable fun ω => g ω i) {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    (hfin : ∀ ω v, {i | i ∈ S ω ∧ F (g ω i) v ≠ 0}.Finite) :
    Measurable fun p : Ω × ℝ => ∑' a : ℝ, (if a ∈ g p.1 '' S p.1 then F a p.2 else 0) := by
  classical
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat ι
  set R : Ω → Set ι := fun ω => firstRep enc (S ω) (g ω)
  have he : ∀ p : Ω × ℝ, (∑' a : ℝ, (if a ∈ g p.1 '' S p.1 then F a p.2 else 0)) =
      ∑' i, (if i ∈ R p.1 then F (g p.1 i) p.2 else 0) := by
    intro p
    have hinj : Function.Injective fun t : R p.1 => g p.1 t.1 := fun t t' h =>
      Subtype.ext (injOn_firstRep henc _ _ t.2 t'.2 h)
    have hsupp : Function.support (fun a : ℝ => if a ∈ g p.1 '' S p.1 then F a p.2 else 0) ⊆
        Set.range fun t : R p.1 => g p.1 t.1 := by
      intro a ha
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
      obtain ⟨hmem, -⟩ := ha
      rw [← image_firstRep (enc := enc)] at hmem
      obtain ⟨i, hi, rfl⟩ := hmem
      exact ⟨⟨i, hi⟩, rfl⟩
    rw [← hinj.tsum_eq hsupp]
    have h1 : ∀ t : R p.1, (if g p.1 t.1 ∈ g p.1 '' S p.1 then F (g p.1 t.1) p.2 else 0) =
        F (g p.1 t.1) p.2 := fun t => if_pos ⟨t.1, t.2.1, rfl⟩
    rw [tsum_congr h1, tsum_subtype (R p.1) (fun i => F (g p.1 i) p.2)]
    rfl
  simp_rw [he]
  refine measurable_tsum_of_finite_support (fun i => ?_) (fun p => ?_)
  · refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_firstRep enc hS hg i).preimage measurable_fst
    · exact hF.comp ((hg i).comp measurable_fst |>.prodMk measurable_snd)
  · refine (hfin p.1 p.2).subset fun i hi => ?_
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hi
    exact ⟨hi.1.1, hi.2⟩

/-! ### The early transform -/

/-- **`D̂_{<a}(s)` is measurable in the data** for jointly measurable `D`. -/
theorem measurable_earlyNoise {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℝ → ℝ}
    (hD : Measurable (Function.uncurry D)) (a : ℝ) (s : ℂ) :
    Measurable fun ω => Decomp.earlyNoise (D ω) a s := by
  unfold Decomp.earlyNoise
  have hint : Measurable fun ω => ∫ x in Ioc 1 a, (D ω x : ℂ) * (x : ℂ) ^ (-s - 1) := by
    have hm : Measurable (Function.uncurry fun ω (x : ℝ) => (D ω x : ℂ) * (x : ℂ) ^ (-s - 1)) :=
      (Complex.measurable_ofReal.comp hD).mul
        ((Complex.measurable_ofReal.comp measurable_snd).pow_const _)
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc 1 a))).measurable
  have hDa : Measurable fun ω => D ω a := hD.comp (measurable_id.prodMk measurable_const)
  exact (measurable_const.mul hint).add ((Complex.measurable_ofReal.comp hDa).mul measurable_const)

/-- **`D̂_{<a}` is continuous** for `D` measurable and bounded on `[1, a]`. -/
theorem continuous_earlyNoise {D : ℝ → ℝ} {a : ℝ} (ha : 1 ≤ a) (hD : Measurable D)
    (hb : ∃ C, ∀ x ∈ Set.Icc 1 a, |D x| ≤ C) : Continuous (Decomp.earlyNoise D a) := by
  obtain ⟨C, hC⟩ := hb
  exact (Decomp.differentiable_earlyNoise ha hD (M := C)
    fun x hx => hC x ⟨hx.1.le, hx.2⟩).continuous

/-! ### The least good height -/

section Height

open GoodHeights DesignedZero BaseFactor

variable (X₀ : ℕ) (κ : ℝ)

/-- `Z_B` on the line `1 + γ i`. -/
noncomputable def zLine (γ : ℝ) : ℂ := ZBcont X₀ κ (1 + (γ : ℂ) * I)

lemma continuousAt_zLine (hκ : 0 < κ) {γ : ℝ} (hγ : 0 < γ) : ContinuousAt (zLine X₀ κ) γ := by
  have hre : 0 < (1 + (γ : ℂ) * I).re := by simp
  have hne : (1 + (γ : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hγ.ne' this
  have hd := (differentiableAt_ZBcont X₀ hκ hre hne).continuousAt
  have hl : ContinuousAt (fun γ : ℝ => 1 + (γ : ℂ) * I) γ := by fun_prop
  exact ContinuousAt.comp (g := ZBcont X₀ κ) (f := fun γ : ℝ => 1 + (γ : ℂ) * I) hd hl

/-- The rational points of the open ball of radius `1/8`. -/
def qBall : Set ℂ := {t | (∃ p : ℚ × ℚ, t = (p.1 : ℂ) + (p.2 : ℂ) * I) ∧ ‖t‖ < 1 / 8}

lemma qBall_countable : qBall.Countable := by
  refine (Set.countable_range fun p : ℚ × ℚ => (p.1 : ℂ) + (p.2 : ℂ) * I).mono ?_
  rintro t ⟨⟨p, rfl⟩, -⟩
  exact ⟨p, rfl⟩

lemma dense_qPoints : Dense {t : ℂ | ∃ p : ℚ × ℚ, t = (p.1 : ℂ) + (p.2 : ℂ) * I} := by
  rw [Metric.dense_iff]
  intro z r hr
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im by linarith)
  refine ⟨(a : ℂ) + (b : ℂ) * I, ?_, ⟨(a, b), rfl⟩⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  calc ‖(a : ℂ) + (b : ℂ) * I - z‖ ≤ |((a : ℂ) + (b : ℂ) * I - z).re| +
        |((a : ℂ) + (b : ℂ) * I - z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < r / 2 + r / 2 := by
        have h1 : ((a : ℂ) + (b : ℂ) * I - z).re = a - z.re := by simp
        have h2 : ((a : ℂ) + (b : ℂ) * I - z).im = b - z.im := by simp
        rw [h1, h2]
        have e1 : |(a : ℝ) - z.re| < r / 2 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
        have e2 : |(b : ℝ) - z.im| < r / 2 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
        linarith
    _ = r := by ring

lemma closedBall_subset_closure_qBall : closedBall (0 : ℂ) (1 / 8) ⊆ closure qBall := by
  have h1 : ball (0 : ℂ) (1 / 8) ⊆ closure (ball (0 : ℂ) (1 / 8) ∩
      {t : ℂ | ∃ p : ℚ × ℚ, t = (p.1 : ℂ) + (p.2 : ℂ) * I}) :=
    dense_qPoints.open_subset_closure_inter isOpen_ball
  have h2 : ball (0 : ℂ) (1 / 8) ∩ {t : ℂ | ∃ p : ℚ × ℚ, t = (p.1 : ℂ) + (p.2 : ℂ) * I} =
      qBall := by
    ext t; simp [qBall, and_comm]
  rw [h2] at h1
  rw [← closure_ball (0 : ℂ) (by norm_num : (1 / 8 : ℝ) ≠ 0)]
  exact closure_minimal h1 isClosed_closure

/-- The countable grid of `[Γ, c]`: its rational points and `c`. -/
def gridK (Γ c : ℝ) : Set ℝ := {q | q ∈ Icc Γ c ∧ (q ∈ Set.range ((↑) : ℚ → ℝ) ∨ q = c)}

lemma gridK_countable (Γ c : ℝ) : (gridK Γ c).Countable := by
  refine ((Set.countable_range ((↑) : ℚ → ℝ)).union (Set.countable_singleton c)).mono ?_
  rintro q ⟨-, h | h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- The relaxed goodness condition on the grid. -/
def RelGood (f : ℂ → ℂ) (q : ℝ) (n : ℕ) : Prop :=
  0.6 - 1 / ((n : ℝ) + 1) ≤ ‖zLine X₀ κ q‖ ∧
    ∀ t ∈ qBall, ‖f (1 + (q : ℂ) * I + t)‖ ≤ 1 / 16 + 1 / ((n : ℝ) + 1)

lemma goodHeight_iff {f : ℂ → ℂ} {Γ γ : ℝ} :
    GoodHeight X₀ κ f Γ γ ↔ γ ∈ Icc Γ (2 * Γ) ∧ 0.6 ≤ ‖zLine X₀ κ γ‖ ∧
      ∀ t ∈ closedBall (0 : ℂ) (1 / 8), ‖f (1 + (γ : ℂ) * I + t)‖ ≤ 1 / 16 := by
  unfold GoodHeight zLine
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h t ht => ?_, fun h s hs => ?_⟩)
  · apply h
    rw [mem_closedBall, dist_eq_norm] at ht ⊢
    simpa using ht
  · have := h (s - (1 + (γ : ℂ) * I)) (by
      rw [mem_closedBall, dist_eq_norm] at hs ⊢; simpa using hs)
    simpa using this

/-- **The existence of a good height below `c` is a countable condition** (for continuous `f`). -/
theorem exists_good_iff (hκ : 0 < κ) {f : ℂ → ℂ} (hf : Continuous f) {Γ c : ℝ} (hΓ : 0 < Γ)
    (hc : c ≤ 2 * Γ) :
    (∃ γ ∈ Icc Γ c, GoodHeight X₀ κ f Γ γ) ↔ ∀ n : ℕ, ∃ q ∈ gridK Γ c, RelGood X₀ κ f q n := by
  constructor
  · rintro ⟨γ, hγ, hgood⟩ n
    rw [goodHeight_iff] at hgood
    obtain ⟨-, hZ, hB⟩ := hgood
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hγ0 : 0 < γ := lt_of_lt_of_le hΓ hγ.1
    obtain ⟨δ1, hδ1, hZc⟩ := Metric.continuousAt_iff.mp (continuousAt_zLine X₀ κ hκ hγ0) _ hε
    have huc := (isCompact_closedBall (1 + (γ : ℂ) * I) 1).uniformContinuousOn_of_continuous
      hf.continuousOn
    obtain ⟨δ2, hδ2, hfc⟩ := Metric.uniformContinuousOn_iff.mp huc _ hε
    set δ := min δ1 (min δ2 (1 / 2)) with hδ
    have hδ0 : 0 < δ := lt_min hδ1 (lt_min hδ2 (by norm_num))
    obtain ⟨q, hqK, hqγ⟩ : ∃ q ∈ gridK Γ c, |q - γ| < δ := by
      rcases hγ.2.lt_or_eq with hlt | heq
      · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min hlt (show γ < γ + δ by linarith))
        refine ⟨r, ⟨⟨by linarith [hγ.1], (hr2.trans_le (min_le_left _ _)).le⟩,
          Or.inl ⟨r, rfl⟩⟩, ?_⟩
        rw [abs_lt]; constructor <;> linarith [min_le_right c (γ + δ)]
      · exact ⟨γ, ⟨hγ, Or.inr heq⟩, by simpa using hδ0⟩
    refine ⟨q, hqK, ?_, fun t ht => ?_⟩
    · have h1 := hZc (show dist q γ < δ1 by
        rw [Real.dist_eq]; exact lt_of_lt_of_le hqγ (min_le_left _ _))
      rw [dist_eq_norm] at h1
      have := norm_sub_norm_le (zLine X₀ κ γ) (zLine X₀ κ q)
      rw [norm_sub_rev] at h1
      linarith
    · have ht' : t ∈ closedBall (0 : ℂ) (1 / 8) := by
        rw [mem_closedBall, dist_zero_right]; exact ht.2.le
      have hy := hB t ht'
      have hdq : ‖((q : ℂ) - γ) * I‖ = |q - γ| := by
        rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      have hxmem : 1 + (q : ℂ) * I + t ∈ closedBall (1 + (γ : ℂ) * I) 1 := by
        rw [mem_closedBall, dist_eq_norm]
        have e : 1 + (q : ℂ) * I + t - (1 + (γ : ℂ) * I) = ((q : ℂ) - γ) * I + t := by ring
        rw [e]
        have := norm_add_le (((q : ℂ) - γ) * I) t
        have h12 : |q - γ| < 1 / 2 := lt_of_lt_of_le hqγ
          ((min_le_right _ _).trans (min_le_right _ _))
        linarith [ht.2]
      have hymem : 1 + (γ : ℂ) * I + t ∈ closedBall (1 + (γ : ℂ) * I) 1 := by
        rw [mem_closedBall, dist_eq_norm]
        simp only [add_sub_cancel_left]
        linarith [ht.2]
      have hd : dist (1 + (q : ℂ) * I + t) (1 + (γ : ℂ) * I + t) < δ2 := by
        rw [dist_eq_norm]
        have e : 1 + (q : ℂ) * I + t - (1 + (γ : ℂ) * I + t) = ((q : ℂ) - γ) * I := by ring
        rw [e, hdq]
        exact lt_of_lt_of_le hqγ ((min_le_right _ _).trans (min_le_left _ _))
      have h2 := hfc _ hxmem _ hymem hd
      rw [dist_eq_norm] at h2
      have := norm_sub_norm_le (f (1 + (q : ℂ) * I + t)) (f (1 + (γ : ℂ) * I + t))
      linarith
  · intro h
    choose q hqK hq using h
    have hK : ∀ n, q n ∈ Icc Γ c := fun n => (hqK n).1
    obtain ⟨γ, hγ, φ, hφ, hlim⟩ := (isCompact_Icc (a := Γ) (b := c)).tendsto_subseq hK
    refine ⟨γ, hγ, ?_⟩
    rw [goodHeight_iff]
    have hγ0 : 0 < γ := lt_of_lt_of_le hΓ hγ.1
    have hφt : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => (φ k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      simpa using (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 1 h1))
    refine ⟨⟨hγ.1, hγ.2.trans hc⟩, ?_, ?_⟩
    · have hZ : Tendsto (fun k => ‖zLine X₀ κ (q (φ k))‖) atTop (𝓝 ‖zLine X₀ κ γ‖) :=
        ((continuousAt_zLine X₀ κ hκ hγ0).norm).tendsto.comp hlim
      have hl : Tendsto (fun k => 0.6 - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (0.6 - 0)) :=
        tendsto_const_nhds.sub hφt
      rw [sub_zero] at hl
      exact le_of_tendsto_of_tendsto' hl hZ fun k => (hq (φ k)).1
    · have hQ : ∀ t ∈ qBall, ‖f (1 + (γ : ℂ) * I + t)‖ ≤ 1 / 16 := by
        intro t ht
        have hc' : Continuous fun x : ℝ => ‖f (1 + (x : ℂ) * I + t)‖ := by fun_prop
        have h1 : Tendsto (fun k => ‖f (1 + (q (φ k) : ℂ) * I + t)‖) atTop
            (𝓝 ‖f (1 + (γ : ℂ) * I + t)‖) := (hc'.tendsto γ).comp hlim
        have h2 : Tendsto (fun k => 1 / 16 + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (1 / 16 + 0)) :=
          tendsto_const_nhds.add hφt
        rw [add_zero] at h2
        exact le_of_tendsto_of_tendsto' h1 h2 fun k => (hq (φ k)).2 t ht
      have hcl : IsClosed {t : ℂ | ‖f (1 + (γ : ℂ) * I + t)‖ ≤ 1 / 16} :=
        isClosed_le (by fun_prop) continuous_const
      intro t ht
      exact (closure_minimal hQ hcl) (closedBall_subset_closure_qBall ht)

lemma measurableSet_relGood {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℂ → ℂ}
    (hm : ∀ s, Measurable fun ω => f ω s) (q : ℝ) (n : ℕ) :
    MeasurableSet {ω | RelGood X₀ κ (f ω) q n} := by
  unfold RelGood
  rw [Set.setOf_and]
  refine (MeasurableSet.const _).inter ?_
  have : {ω | ∀ t ∈ qBall, ‖f ω (1 + (q : ℂ) * I + t)‖ ≤ 1 / 16 + 1 / ((n : ℝ) + 1)} =
      ⋂ t ∈ qBall, {ω | ‖f ω (1 + (q : ℂ) * I + t)‖ ≤ 1 / 16 + 1 / ((n : ℝ) + 1)} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biInter qBall_countable fun t _ =>
    measurableSet_le (hm _).norm measurable_const

lemma measurableSet_exists_good {Ω : Type*} [MeasurableSpace Ω] (hκ : 0 < κ) {Γ c : ℝ}
    (hΓ : 0 < Γ) (hc : c ≤ 2 * Γ) {f : Ω → ℂ → ℂ} (hm : ∀ s, Measurable fun ω => f ω s)
    (hcont : ∀ ω, Continuous (f ω)) :
    MeasurableSet {ω | ∃ γ ∈ Icc Γ c, GoodHeight X₀ κ (f ω) Γ γ} := by
  have e : {ω | ∃ γ ∈ Icc Γ c, GoodHeight X₀ κ (f ω) Γ γ} =
      ⋂ n : ℕ, ⋃ q ∈ gridK Γ c, {ω | RelGood X₀ κ (f ω) q n} := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion, exists_prop]
    exact exists_good_iff X₀ κ hκ (hcont ω) hΓ hc
  rw [e]
  exact MeasurableSet.iInter fun n =>
    MeasurableSet.biUnion (gridK_countable Γ c) fun q _ => measurableSet_relGood X₀ κ hm q n

/-- The good set is closed (for continuous `f`). -/
lemma isClosed_good (hκ : 0 < κ) {f : ℂ → ℂ} (hf : Continuous f) {Γ : ℝ} (hΓ : 0 < Γ) :
    IsClosed {γ | GoodHeight X₀ κ f Γ γ} := by
  have e : {γ | GoodHeight X₀ κ f Γ γ} =
      (Icc Γ (2 * Γ) ∩ (fun γ => ‖zLine X₀ κ γ‖) ⁻¹' Ici 0.6) ∩
        ⋂ t ∈ closedBall (0 : ℂ) (1 / 8), {γ : ℝ | ‖f (1 + (γ : ℂ) * I + t)‖ ≤ 1 / 16} := by
    ext γ
    simp only [mem_setOf_eq, goodHeight_iff, mem_inter_iff, mem_preimage, mem_Ici, mem_iInter]
    tauto
  rw [e]
  refine IsClosed.inter ?_ (isClosed_biInter fun t _ => isClosed_le (by fun_prop)
    continuous_const)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc isClosed_Ici
  intro γ hγ
  exact ((continuousAt_zLine X₀ κ hκ (lt_of_lt_of_le hΓ hγ.1)).norm).continuousWithinAt

open Classical in
/-- For continuous `f` the chosen height is the least good height (or `Γ`). -/
lemma chooseHeight_eq (hκ : 0 < κ) {f : ℂ → ℂ} (hf : Continuous f) {Γ : ℝ} (hΓ : 0 < Γ) :
    chooseHeight X₀ κ f Γ = if ∃ γ, GoodHeight X₀ κ f Γ γ then
      sInf {γ | GoodHeight X₀ κ f Γ γ} else Γ := by
  unfold chooseHeight
  split_ifs with h h'
  · rfl
  · exfalso
    apply h'
    exact (isClosed_good X₀ κ hκ hf hΓ).csInf_mem h ⟨Γ, fun γ hγ => hγ.1.1⟩
  · rfl

/-- **The least good height is measurable in the data** (§3.2). -/
theorem measurable_chooseHeight {Ω : Type*} [MeasurableSpace Ω] (X₀ : ℕ) {κ Γ : ℝ}
    (hκ : 0 < κ) (hΓ : 0 < Γ) {f : Ω → ℂ → ℂ} (hm : ∀ s, Measurable fun ω => f ω s)
    (hc : ∀ ω, Continuous (f ω)) : Measurable fun ω => chooseHeight X₀ κ (f ω) Γ := by
  classical
  apply measurable_of_Iic
  intro c
  set E : ℝ → Set Ω := fun c => {ω | ∃ γ ∈ Icc Γ (min c (2 * Γ)), GoodHeight X₀ κ (f ω) Γ γ}
  have hE : ∀ c, MeasurableSet (E c) := fun c =>
    measurableSet_exists_good X₀ κ hκ hΓ (min_le_right _ _) hm hc
  have hex : ∀ ω, (∃ γ, GoodHeight X₀ κ (f ω) Γ γ) ↔ ω ∈ E (2 * Γ) := by
    intro ω
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, ⟨hγ.1.1, le_min hγ.1.2 hγ.1.2⟩, hγ⟩
    · rintro ⟨γ, -, hγ⟩; exact ⟨γ, hγ⟩
  have e : (fun ω => chooseHeight X₀ κ (f ω) Γ) ⁻¹' Iic c =
      ((E (2 * Γ))ᶜ ∩ {_ω | Γ ≤ c}) ∪ E c := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq]
    rw [chooseHeight_eq X₀ κ hκ (hc ω) hΓ]
    split_ifs with h
    · have hcl := isClosed_good X₀ κ hκ (hc ω) hΓ
      have hmem := hcl.csInf_mem h ⟨Γ, fun γ hγ => hγ.1.1⟩
      have hbdd : BddBelow {γ | GoodHeight X₀ κ (f ω) Γ γ} := ⟨Γ, fun γ hγ => hγ.1.1⟩
      have hinE := (hex ω).mp h
      constructor
      · intro hle
        right
        exact ⟨_, ⟨hmem.1.1, le_min hle hmem.1.2⟩, hmem⟩
      · rintro (⟨hn, -⟩ | ⟨γ, hγ, hg⟩)
        · exact absurd hinE hn
        · exact (csInf_le hbdd hg).trans (hγ.2.trans (min_le_left _ _))
    · have hn : ω ∉ E (2 * Γ) := fun hω => h ((hex ω).mpr hω)
      constructor
      · intro hle; exact Or.inl ⟨hn, hle⟩
      · rintro (⟨-, hle⟩ | ⟨γ, -, hg⟩)
        · exact hle
        · exact absurd ⟨γ, hg⟩ h
  rw [e]
  exact (((hE _).compl).inter (MeasurableSet.const _)).union (hE c)

end Height

end BModel

end
