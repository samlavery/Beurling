module

public import RequestProject.Beurling.Weights

/-!
# The absorbed part `Ê_A` and Lemma 4.4(a)

For the absorbed set `A ⊆ ℝ` (a locally finite set of values of elements) with forward-window
weights `w_a` (Section 4.1, after (14)),

  `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))`.

Given a counting bound `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}` with `ς` nondecreasing (the Rankin
bound of Lemma 6.26, used in the proof of Lemma 4.4), the weight bounds (ii) and (iv) and partial
summation give, for `1 - δ ≤ σ ≤ 2` and `|t| ≥ 2`, with `Y = |t|^{1/(1-b)}`:

  `|Ê_A(s)| ≤ 2.001 (Y^δ e^{-ς(log Y)} + ∫_1^Y v^{δ-1} e^{-ς(log v)} dv) + 5.4 Y^δ e^{-ς(log Y)}`.

This is the estimate in the proof of Lemma 4.4(a) (terms `a ≤ Y` and `a > Y`).
-/

@[expose] public section

open Complex Set Filter MeasureTheory Finset

namespace Absorbed

open scoped Classical

/-- `A ⊆ ℝ` is **locally finite**: it has finitely many elements below any bound. (The absorbed
set (5) is a set of values of elements of the semigroup, and there are finitely many elements of
value below any bound.) -/
def LocFin (A : Set ℝ) : Prop := ∀ x : ℝ, (A ∩ Iic x).Finite

/-- The counting function `#(A ∩ [1, x])` of `A ⊆ ℝ`. -/
noncomputable def countA (A : Set ℝ) (x : ℝ) : ℝ := ((A ∩ Set.Icc 1 x).ncard : ℝ)

/-- The elements of a locally finite `A` that are `≤ x`, as a finset. -/
noncomputable def below {A : Set ℝ} (hA : LocFin A) (x : ℝ) : Finset ℝ := (hA x).toFinset

@[simp] lemma mem_below {A : Set ℝ} (hA : LocFin A) {x a : ℝ} :
    a ∈ below hA x ↔ a ∈ A ∧ a ≤ x := by simp [below]

lemma LocFin.subset {A B : Set ℝ} (hB : LocFin B) (h : A ⊆ B) : LocFin A :=
  fun x => (hB x).subset (inter_subset_inter_left _ h)

lemma LocFin.countable {A : Set ℝ} (hA : LocFin A) : A.Countable := by
  have e : A = ⋃ n : ℕ, A ∩ Iic (n : ℝ) := by
    ext a
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iic]
    exact ⟨fun ha => ⟨⌈a⌉₊, ha, Nat.le_ceil a⟩, fun ⟨_, ha, _⟩ => ha⟩
  rw [e]
  exact Set.countable_iUnion fun n => (hA n).countable

lemma LocFin.finite_Icc {A : Set ℝ} (hA : LocFin A) (y x : ℝ) : (A ∩ Set.Icc y x).Finite :=
  (hA x).subset fun _ ha => ⟨ha.1, ha.2.2⟩

lemma countA_mono {A : Set ℝ} (hA : LocFin A) : Monotone (countA A) := by
  intro x y hxy
  unfold countA
  exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right _ (Set.Icc_subset_Icc_right hxy))
    (hA.finite_Icc 1 y)

lemma countA_nonneg (A : Set ℝ) (x : ℝ) : 0 ≤ countA A x := Nat.cast_nonneg _

/-- `#(A ∩ [1, s))`, the left limit of `countA A` at `s`. -/
noncomputable def countAlt (A : Set ℝ) (s : ℝ) : ℝ := ((A ∩ Set.Ico 1 s).ncard : ℝ)

/-- The jump of `countA A` at `s`: `#(A ∩ [1, s]) = #(A ∩ [1, s)) + [s ∈ A, s ≥ 1]`. -/
lemma countA_eq_countAlt_add {A : Set ℝ} (hA : LocFin A) (s : ℝ) :
    countA A s = countAlt A s + if s ∈ A ∧ 1 ≤ s then 1 else 0 := by
  classical
  unfold countA countAlt
  have hfin : (A ∩ Set.Ico 1 s).Finite := (hA.finite_Icc 1 s).subset
    (inter_subset_inter_right _ Set.Ico_subset_Icc_self)
  split_ifs with hs
  · have e : A ∩ Set.Icc 1 s = insert s (A ∩ Set.Ico 1 s) := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_insert_iff]
      constructor
      · rintro ⟨ha, h1, h2⟩
        rcases h2.lt_or_eq with h | h
        · exact Or.inr ⟨ha, h1, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨ha, h1, h2⟩)
        · exact ⟨hs.1, hs.2, le_rfl⟩
        · exact ⟨ha, h1, h2.le⟩
    rw [e, Set.ncard_insert_of_notMem (fun h => lt_irrefl s h.2.2) hfin]
    push_cast; ring
  · have e : A ∩ Set.Icc 1 s = A ∩ Set.Ico 1 s := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨ha, h1, h2⟩
        refine ⟨ha, h1, lt_of_le_of_ne h2 ?_⟩
        rintro rfl; exact hs ⟨ha, h1⟩
      · rintro ⟨ha, h1, h2⟩; exact ⟨ha, h1, h2.le⟩
    rw [e]; ring

/-- `countA A` is constant on `[x, x + δ)` for some `δ > 0` (right-continuity). -/
lemma countA_rconst {A : Set ℝ} (hA : LocFin A) (x : ℝ) :
    ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → countA A y = countA A x := by
  classical
  set G := (below hA (x + 1)).filter (fun a => x < a)
  have key : ∃ δ > 0, δ ≤ 1 ∧ ∀ a ∈ G, δ ≤ a - x := by
    rcases G.eq_empty_or_nonempty with hG | hG
    · exact ⟨1, one_pos, le_rfl, by simp [hG]⟩
    · obtain ⟨a₀, ha₀, hmin⟩ := G.exists_min_image (fun a => a - x) hG
      have : x < a₀ := (Finset.mem_filter.mp ha₀).2
      exact ⟨min 1 (a₀ - x), lt_min one_pos (by linarith), min_le_left _ _,
        fun a ha => (min_le_right _ _).trans (hmin a ha)⟩
  obtain ⟨δ, hδ, hδ1, hG⟩ := key
  refine ⟨δ, hδ, fun y hxy hy => ?_⟩
  unfold countA
  congr 2
  ext a
  simp only [Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨ha, h1, h2⟩
    refine ⟨ha, h1, ?_⟩
    by_contra hc
    push_neg at hc
    have hmem : a ∈ G := Finset.mem_filter.mpr ⟨(mem_below hA).2 ⟨ha, by linarith⟩, hc⟩
    have := hG a hmem
    linarith
  · rintro ⟨ha, h1, h2⟩; exact ⟨ha, h1, h2.trans hxy⟩

/-- `countA A` equals its left limit `countAlt A s` on `[s - δ, s)` for some `δ > 0`. -/
lemma countA_lconst {A : Set ℝ} (hA : LocFin A) (s : ℝ) :
    ∃ δ > 0, ∀ y, s - δ ≤ y → y < s → countA A y = countAlt A s := by
  classical
  set G := (below hA s).filter (fun a => a < s)
  have key : ∃ δ > 0, ∀ a ∈ G, δ < s - a := by
    rcases G.eq_empty_or_nonempty with hG | hG
    · exact ⟨1, one_pos, by simp [hG]⟩
    · obtain ⟨a₀, ha₀, hmax⟩ := G.exists_max_image (fun a => a) hG
      have : a₀ < s := (Finset.mem_filter.mp ha₀).2
      refine ⟨(s - a₀) / 2, by linarith, fun a ha => ?_⟩
      have := hmax a ha
      try simp only at this
      linarith
  obtain ⟨δ, hδ, hG⟩ := key
  refine ⟨δ, hδ, fun y hy hys => ?_⟩
  unfold countA countAlt
  congr 2
  ext a
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨ha, h1, h2⟩; exact ⟨ha, h1, lt_of_le_of_lt h2 hys⟩
  · rintro ⟨ha, h1, h2⟩
    refine ⟨ha, h1, ?_⟩
    have hmem : a ∈ G := Finset.mem_filter.mpr ⟨(mem_below hA).2 ⟨ha, h2.le⟩, h2⟩
    have := hG a hmem
    linarith

/-- `cnt F v = #{a ∈ F : a ≤ v}`. -/
noncomputable def cnt (F : Finset ℝ) (v : ℝ) : ℝ := ∑ a ∈ F, (if a ≤ v then (1 : ℝ) else 0)

lemma cnt_mono (F : Finset ℝ) : Monotone (cnt F) := fun x y hxy =>
  Finset.sum_le_sum fun a _ => by
    by_cases h1 : a ≤ x <;> by_cases h2 : a ≤ y <;>
      first | exact absurd (h1.trans hxy) h2 | simp [h1, h2]

lemma cnt_nonneg (F : Finset ℝ) (v : ℝ) : 0 ≤ cnt F v :=
  Finset.sum_nonneg fun a _ => by split_ifs <;> norm_num

lemma cnt_eq_card {F : Finset ℝ} {v : ℝ} (hF : ∀ a ∈ F, a ≤ v) : cnt F v = F.card := by
  unfold cnt
  rw [Finset.sum_congr rfl fun a ha => if_pos (hF a ha)]
  simp

/-- For `A ⊆ [1, ∞)` and a finset `F ⊆ A` containing `A ∩ (-∞, v]`: `#(A ∩ [1, v]) = cnt F v`. -/
lemma countA_eq_cnt {A : Set ℝ} (hA1 : ∀ a ∈ A, 1 ≤ a) (F : Finset ℝ) (hFA : ∀ a ∈ F, a ∈ A)
    {v : ℝ} (hF : ∀ a ∈ A, a ≤ v → a ∈ F) : countA A v = cnt F v := by
  unfold countA cnt
  rw [Finset.sum_boole]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp only [mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, -, hav⟩; exact ⟨hF a ha hav, hav⟩
  · rintro ⟨haF, hav⟩; exact ⟨hFA a haF, hA1 a (hFA a haF), hav⟩

/-- For a finset `F ⊆ A ⊆ [1, ∞)`: `cnt F v ≤ #(A ∩ [1, v])`. -/
lemma cnt_le_countA {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 ≤ a) {F : Finset ℝ}
    (hF : ∀ a ∈ F, a ∈ A) (v : ℝ) : cnt F v ≤ countA A v := by
  unfold cnt countA
  rw [Finset.sum_boole]
  norm_cast
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun a ha => ?_) (hA.finite_Icc 1 v)
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
  exact ⟨hF a ha.1, hA1 a (hF a ha.1), ha.2⟩

lemma integrableOn_Ioc_of_bdd {f : ℝ → ℝ} {a Y C : ℝ} (hf : Measurable f)
    (hb : ∀ v ∈ Ioc a Y, |f v| ≤ C) : IntegrableOn f (Ioc a Y) := by
  refine Integrable.mono' (g := fun _ => C) (integrableOn_const (by simp))
    hf.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun v hv => ?_
  simpa using hb v hv

lemma measurable_rpow_mul_exp {ς : ℝ → ℝ} (hς : Monotone ς) {p : ℝ} :
    Measurable fun v : ℝ => v ^ p * Real.exp (-ς (Real.log v)) := by
  have := hς.measurable
  fun_prop

/-- `a^p = Y^p - ∫_{(lo, Y]} 1[v ≥ a] p v^{p-1} dv` for `0 < lo < a ≤ Y`. -/
lemma rpow_eq_sub_integral {p lo hi a : ℝ} (hlo : 0 < lo) (ha : lo < a) (hahi : a ≤ hi) :
    a ^ p = hi ^ p - ∫ v in Ioc lo hi, (Set.Ici a).indicator (fun v => p * v ^ (p - 1)) v := by
  have hd : ∀ v ∈ Set.uIcc a hi, HasDerivAt (fun v : ℝ => v ^ p) (p * v ^ (p - 1)) v := by
    intro v hv; rw [Set.uIcc_of_le hahi] at hv
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [hv.1]))
  have hc : ContinuousOn (fun v : ℝ => p * v ^ (p - 1)) (Set.uIcc a hi) := by
    intro v hv; rw [Set.uIcc_of_le hahi] at hv
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
      (Or.inl (by linarith [hv.1])))).continuousWithinAt
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have hs : Ioc lo hi ∩ Set.Ici a = Set.Icc a hi := by
    ext v; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [setIntegral_indicator measurableSet_Ici, hs, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hahi, hF]
  ring

/-- **Partial summation over a finite set of reals**: for a finset `F ⊆ (lo, hi]`, `lo > 0`,
`∑_{a ∈ F} a^p = hi^p #F - ∫_{(lo, hi]} p v^{p-1} #{a ∈ F : a ≤ v} dv`. -/
lemma sum_rpow_eq (F : Finset ℝ) {p lo hi : ℝ} (hlo : 0 < lo)
    (hF : ∀ a ∈ F, lo < a ∧ a ≤ hi) :
    ∑ a ∈ F, a ^ p = hi ^ p * F.card - ∫ v in Ioc lo hi, p * v ^ (p - 1) * cnt F v := by
  have hc : ContinuousOn (fun v : ℝ => p * v ^ (p - 1)) (Set.Icc lo hi) := by
    intro v hv
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
      (Or.inl (by linarith [hv.1])))).continuousWithinAt
  have hint : ∀ a ∈ F, IntegrableOn ((Set.Ici a).indicator (fun v => p * v ^ (p - 1)))
      (Ioc lo hi) := fun a _ =>
    ((hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self).indicator
      measurableSet_Ici
  have e : (fun v => p * v ^ (p - 1) * cnt F v) =
      fun v => ∑ a ∈ F, (Set.Ici a).indicator (fun v => p * v ^ (p - 1)) v := by
    ext v; unfold cnt; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Set.indicator_apply, Set.mem_Ici]
    split_ifs <;> simp
  rw [e, integral_finset_sum _ hint,
    Finset.sum_congr rfl fun a ha => rpow_eq_sub_integral hlo (hF a ha).1 (hF a ha).2,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Partial summation over `A ∩ (1, Y]` for `a ↦ a^{-γ}`. -/
lemma head_sum_eq {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 < a) {γ Y : ℝ} :
    ∑ a ∈ below hA Y, a ^ (-γ) =
      Y ^ (-γ) * countA A Y + γ * ∫ v in Ioc 1 Y, v ^ (-γ - 1) * countA A v := by
  have hm : ∀ a ∈ below hA Y, a ∈ A ∧ a ≤ Y := fun a ha => (mem_below hA).1 ha
  have h := sum_rpow_eq (below hA Y) (p := -γ) one_pos fun a ha => ⟨hA1 a (hm a ha).1, (hm a ha).2⟩
  have hA1' : ∀ a ∈ A, 1 ≤ a := fun a ha => (hA1 a ha).le
  have hc : ∀ v ∈ Ioc 1 Y, -γ * v ^ (-γ - 1) * cnt (below hA Y) v =
      -γ * (v ^ (-γ - 1) * countA A v) := fun v hv => by
    rw [countA_eq_cnt hA1' (below hA Y) (fun a ha => (hm a ha).1)
      (fun a ha hav => (mem_below hA).2 ⟨ha, hav.trans hv.2⟩)]
    ring
  have hY' : ((below hA Y).card : ℝ) = countA A Y := by
    rw [countA_eq_cnt hA1' (below hA Y) (fun a ha => (hm a ha).1)
      (fun a ha hav => (mem_below hA).2 ⟨ha, hav⟩), cnt_eq_card fun a ha => (hm a ha).2]
  rw [h, setIntegral_congr_fun measurableSet_Ioc hc, integral_const_mul, hY']
  ring

lemma head_sum_le_aux {A : Set ℝ} (hA : LocFin A) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {δ Y : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hY : 1 ≤ Y) :
    Y ^ (-(1-δ)) * countA A Y + (1-δ) * ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v ≤
      Y ^ δ * Real.exp (-ς (Real.log Y)) +
        ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
  rw [intervalIntegral.integral_of_le hY]
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ (-(1-δ)) * countA A Y ≤ Y ^ δ * Real.exp (-ς (Real.log Y)) := by
    calc Y ^ (-(1-δ)) * countA A Y ≤ Y ^ (-(1-δ)) * (Y * Real.exp (-ς (Real.log Y))) :=
          mul_le_mul_of_nonneg_left (hN Y hY) (Real.rpow_nonneg hY0.le _)
      _ = (Y ^ (-(1-δ)) * Y ^ (1:ℝ)) * Real.exp (-ς (Real.log Y)) := by
          rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hY0]; ring_nf
  have hgi : IntegrableOn (fun v : ℝ => v ^ (δ - 1) * Real.exp (-ς (Real.log v))) (Ioc 1 Y) := by
    refine integrableOn_Ioc_of_bdd (C := Real.exp (-ς 0)) (measurable_rpow_mul_exp hς)
      fun v hv => ?_
    have hv1 : 1 ≤ v := hv.1.le
    rw [abs_of_nonneg (by positivity)]
    have : v ^ (δ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
    have : Real.exp (-ς (Real.log v)) ≤ Real.exp (-ς 0) := by
      rw [Real.exp_le_exp]; have := hς (Real.log_nonneg hv1); linarith
    have : 0 ≤ Real.exp (-ς (Real.log v)) := by positivity
    nlinarith
  have hfi : IntegrableOn (fun v : ℝ => v ^ (-(1-δ) - 1) * countA A v) (Ioc 1 Y) := by
    refine integrableOn_Ioc_of_bdd (C := countA A Y) ?_ fun v hv => ?_
    · have := (countA_mono hA).measurable; fun_prop
    · have hv1 : 1 ≤ v := hv.1.le
      rw [abs_of_nonneg (mul_nonneg (by positivity) (countA_nonneg A v))]
      have : v ^ (-(1-δ) - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
      have := countA_mono hA hv.2
      have := countA_nonneg A v
      nlinarith
  have h2 : ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v ≤
      ∫ v in Ioc 1 Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
    refine setIntegral_mono_on hfi hgi measurableSet_Ioc fun v hv => ?_
    have hv0 : 0 < v := by linarith [hv.1]
    calc v ^ (-(1-δ) - 1) * countA A v ≤ v ^ (-(1-δ) - 1) * (v * Real.exp (-ς (Real.log v))) :=
          mul_le_mul_of_nonneg_left (hN v hv.1.le) (Real.rpow_nonneg hv0.le _)
      _ = (v ^ (-(1-δ) - 1) * v ^ (1:ℝ)) * Real.exp (-ς (Real.log v)) := by
          rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hv0]; ring_nf
  have h3 : 0 ≤ ∫ v in Ioc 1 Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) :=
    setIntegral_nonneg measurableSet_Ioc fun v hv => by
      have : 0 < v := by linarith [hv.1]
      positivity
  have h4 : 0 ≤ ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v :=
    setIntegral_nonneg measurableSet_Ioc fun v hv => by
      have : 0 < v := by linarith [hv.1]
      have := countA_nonneg A v
      positivity
  nlinarith

/-- The head estimate: `∑_{a ∈ A, a ≤ Y} a^{δ-1} ≤ Y^δ e^{-ς(log Y)} + ∫_1^Y v^{δ-1} e^{-ς(log v)}`. -/
lemma head_sum_le {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 < a) {ς : ℝ → ℝ}
    (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {δ Y : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hY : 1 ≤ Y) :
    ∑ a ∈ below hA Y, a ^ (δ - 1) ≤
      Y ^ δ * Real.exp (-ς (Real.log Y)) +
        ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
  have e := head_sum_eq hA hA1 (γ := 1 - δ) (Y := Y)
  have key := head_sum_le_aux hA hς hN hδ0 hδ hY
  simp only [show -(1 - δ) = δ - 1 by ring] at e key
  linarith

/-- Partial summation over `A ∩ (Y, Z]` for `a ↦ a^{-β}`, `β > 1`. -/
lemma tail_Ioc_le {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 < a) {ς : ℝ → ℝ}
    (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y Z : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    ∑ a ∈ (below hA Z).filter (fun a => Y < a), a ^ (-β) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hA1' : ∀ a ∈ A, 1 ≤ a := fun a ha => (hA1 a ha).le
  set F := (below hA Z).filter (fun a => Y < a) with hFdef
  have hFm : ∀ a ∈ F, a ∈ A ∧ a ≤ Z ∧ Y < a := by
    intro a ha
    rw [hFdef, Finset.mem_filter, mem_below] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  have hFA : ∀ a ∈ F, a ∈ A := fun a ha => (hFm a ha).1
  rw [sum_rpow_eq F (p := -β) hY0 fun a ha => ⟨(hFm a ha).2.2, (hFm a ha).2.1⟩]
  set C := Real.exp (-ς (Real.log Y))
  have hC : 0 ≤ C := by positivity
  have hNY : ∀ t ≥ Y, countA A t ≤ C * t := by
    intro t ht
    have := hN t (hY.trans ht)
    have h2 : Real.exp (-ς (Real.log t)) ≤ C := by
      rw [Real.exp_le_exp]; have := hς (Real.log_le_log hY0 ht); linarith
    nlinarith
  have hint : ∫ v in Ioc Y Z, -β * v ^ (-β - 1) * cnt F v =
      -β * ∫ v in Ioc Y Z, v ^ (-β - 1) * cnt F v := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  rw [hint]
  have hfi : IntegrableOn (fun v : ℝ => v ^ (-β - 1) * cnt F v) (Ioc Y Z) := by
    refine integrableOn_Ioc_of_bdd (C := cnt F Z) ?_ fun v hv => ?_
    · have := (cnt_mono F).measurable; fun_prop
    · have hv1 : 1 ≤ v := hY.trans hv.1.le
      rw [abs_of_nonneg (mul_nonneg (by positivity) (cnt_nonneg F v))]
      have : v ^ (-β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
      have := cnt_mono F hv.2
      have := cnt_nonneg F v
      nlinarith
  have hgi : IntegrableOn (fun v : ℝ => C * v ^ (-β)) (Ioc Y Z) :=
    ((ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (by simp at hx ⊢; linarith [hx.1]))).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self).const_mul C
  have h2 : ∫ v in Ioc Y Z, v ^ (-β - 1) * cnt F v ≤ ∫ v in Ioc Y Z, C * v ^ (-β) := by
    refine setIntegral_mono_on hfi hgi measurableSet_Ioc fun v hv => ?_
    have hv0 : 0 < v := by linarith [hv.1]
    calc v ^ (-β - 1) * cnt F v ≤ v ^ (-β - 1) * (C * v) :=
          mul_le_mul_of_nonneg_left ((cnt_le_countA hA hA1' hFA v).trans (hNY v hv.1.le))
            (Real.rpow_nonneg hv0.le _)
      _ = C * (v ^ (-β - 1) * v ^ (1:ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hv0]; ring_nf
  have h3 : ∫ v in Ioc Y Z, C * v ^ (-β) = C * ((Z ^ (1 - β) - Y ^ (1 - β)) / (1 - β)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hYZ, integral_rpow]
    · ring_nf
    · right; refine ⟨by linarith, ?_⟩
      simp [Set.uIcc_of_le hYZ]; intro h; linarith
  have hNZ : (F.card : ℝ) ≤ C * Z := by
    rw [← cnt_eq_card fun a ha => (hFm a ha).2.1]
    exact (cnt_le_countA hA hA1' hFA Z).trans (hNY Z hYZ)
  have hZp : 0 ≤ Z ^ (-β) := Real.rpow_nonneg hZ0.le _
  have hZZ : Z ^ (-β) * (C * Z) = C * Z ^ (1 - β) := by
    rw [show (1 - β) = -β + 1 by ring, Real.rpow_add hZ0, Real.rpow_one]; ring
  have hZb : 0 ≤ Z ^ (1 - β) := Real.rpow_nonneg hZ0.le _
  have hb1 : β - 1 ≠ 0 := by intro h; linarith
  have hb1' : 1 - β ≠ 0 := by intro h; linarith
  have hb0 : 0 < β := by linarith
  have e : β * (C * ((Z ^ (1 - β) - Y ^ (1 - β)) / (1 - β))) =
      β / (β - 1) * C * Y ^ (1 - β) - β / (β - 1) * C * Z ^ (1 - β) := by
    field_simp; ring
  have hfin : Z ^ (-β) * (F.card : ℝ) ≤ C * Z ^ (1 - β) := by
    rw [← hZZ]; exact mul_le_mul_of_nonneg_left hNZ hZp
  have hβ1 : 1 ≤ β / (β - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
  rw [e] at h4
  have h5 : C * Z ^ (1 - β) ≤ β / (β - 1) * C * Z ^ (1 - β) := by
    have := mul_le_mul_of_nonneg_right hβ1 (mul_nonneg hC hZb)
    linarith
  linarith

/-- The tail estimate: for `β > 1`, the finite sums of `a^{-β}` over `a ∈ A`, `a > Y` are at most
`β/(β-1) · e^{-ς(log Y)} Y^{1-β}`. -/
lemma tail_partial_le {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 < a) {ς : ℝ → ℝ}
    (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) (s : Finset ℝ) :
    ∑ k ∈ s, (if k ∈ A ∧ Y < k then k ^ (-β) else 0) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  set Z := max Y (∑ k ∈ s, |k|)
  refine le_trans ?_ (tail_Ioc_le hA hA1 hς hN hβ hY (le_max_left Y (∑ k ∈ s, |k|)))
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, mem_below] at hk ⊢
    refine ⟨⟨hk.2.1, ?_⟩, hk.2.2⟩
    exact (le_abs_self k).trans ((Finset.single_le_sum (fun i _ => abs_nonneg i) hk.1).trans
      (le_max_right _ _))
  · intro k hk _
    simp only [Finset.mem_filter, mem_below] at hk
    exact Real.rpow_nonneg (by linarith [hA1 k hk.1.1]) _

lemma tail_summable {A : Set ℝ} (hA : LocFin A) (hA1 : ∀ a ∈ A, 1 < a) {ς : ℝ → ℝ}
    (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) :
    Summable (fun k : ℝ => if k ∈ A ∧ Y < k then k ^ (-β) else 0) ∧
    ∑' k : ℝ, (if k ∈ A ∧ Y < k then k ^ (-β) else 0) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  have hnn : ∀ k : ℝ, 0 ≤ (if k ∈ A ∧ Y < k then k ^ (-β) else 0) := fun k => by
    split_ifs with h
    · exact Real.rpow_nonneg (by linarith [h.2]) _
    · exact le_rfl
  exact ⟨summable_of_sum_le hnn (tail_partial_le hA hA1 hς hN hβ hY),
    Real.tsum_le_of_sum_le hnn (tail_partial_le hA hA1 hς hN hβ hY)⟩

/-- The standing hypotheses on the absorbed set `A ⊆ ℝ` (a set of values of elements): every
`a ∈ A` satisfies the hypotheses of the weight bounds, with `u a = u_a` (`u_a + u_a^b = a`,
`a ≥ 10⁶`, `0 < b ≤ 1/4`), and `A` is locally finite. -/
structure AbsorbedHyp (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) : Prop where
  b_pos : 0 < b
  b_le : b ≤ 1 / 4
  weight : ∀ a ∈ A, Weights.WeightHyp b a (u a)
  fin : LocFin A

/-- The term `a^{-s} (1 - w_a(s))` of `Ê_A` (zero off `A`). -/
noncomputable def absorbedTerm (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (s : ℂ) (a : ℝ) : ℂ :=
  if a ∈ A then (a : ℂ) ^ (-s) * (1 - Weights.weight b a (u a) s) else 0

/-- The absorbed part `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))` (a sum over the real values
`a ∈ A`). -/
noncomputable def absorbedHat (b : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑' a : ℝ, absorbedTerm b A u s a

/-- The explicit bound of Lemma 4.4(a). -/
noncomputable def absorbedBound (ς : ℝ → ℝ) (δ Y : ℝ) : ℝ :=
  2.001 * (Y ^ δ * Real.exp (-ς (Real.log Y)) +
    ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v))) +
  5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y)))

lemma AbsorbedHyp.two_le {b : ℝ} {A : Set ℝ} {u : ℝ → ℝ} (h : AbsorbedHyp b A u) :
    ∀ a ∈ A, 2 ≤ a := by
  intro a ha
  have := (h.weight a ha).a_ge
  linarith

lemma AbsorbedHyp.one_lt {b : ℝ} {A : Set ℝ} {u : ℝ → ℝ} (h : AbsorbedHyp b A u) :
    ∀ a ∈ A, 1 < a := fun a ha => by linarith [h.two_le a ha]

/-- The termwise majorant: `2.001 a^{δ-1}` for `a ≤ Y` (bound (ii)) and `2|t| a^{b+δ-2}` for
`a > Y` (bound (iv)). -/
lemma norm_absorbedTerm_le {b : ℝ} {A : Set ℝ} {u : ℝ → ℝ} (h : AbsorbedHyp b A u)
    {δ : ℝ} {s : ℂ} (hσ1 : 1 - δ ≤ s.re) (hσ2 : s.re ≤ 2) (hσ0 : 0 ≤ s.re)
    (ht : 2 ≤ |s.im|) (Y : ℝ) (n : ℝ) :
    ‖absorbedTerm b A u s n‖ ≤
      (if n ∈ A ∧ n ≤ Y then 2.001 * n ^ (δ - 1) else 0) +
        2 * |s.im| * (if n ∈ A ∧ Y < n then n ^ (-(2 - b - δ)) else 0) := by
  unfold absorbedTerm
  by_cases hn : n ∈ A
  · have hw := h.weight n hn
    have hn1 : (1 : ℝ) ≤ n := by have := hw.a_ge; linarith
    have hn0 : (0 : ℝ) < n := by linarith
    rw [if_pos hn, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    have hpow : n ^ (-s.re) ≤ n ^ (δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hp0 : 0 ≤ n ^ (-s.re) := Real.rpow_nonneg hn0.le _
    by_cases hY : n ≤ Y
    · rw [if_pos ⟨hn, hY⟩, if_neg (by intro h'; linarith [h'.2])]
      have hw1 := (hw.norm_weight_le hσ0 hσ2)
      have hε := hw.eps_le
      have h1w : ‖1 - Weights.weight b n (u n) s‖ ≤ 2.001 := by
        have := norm_sub_le (1 : ℂ) (Weights.weight b n (u n) s)
        rw [norm_one] at this
        have h2 : 1.02 * s.re * n ^ (b - 1) ≤ 0.001 := by
          have := hw.eps_pos
          nlinarith
        linarith [hw1.1, hw1.2]
      have := mul_le_mul hpow h1w (norm_nonneg _) (Real.rpow_nonneg hn0.le _)
      linarith
    · push_neg at hY
      rw [if_neg (by intro h'; linarith [h'.2]), if_pos ⟨hn, hY⟩, zero_add]
      have h1w := hw.norm_one_sub_weight_le' hσ0 hσ2 ht
      calc n ^ (-s.re) * ‖1 - Weights.weight b n (u n) s‖ ≤
            n ^ (δ - 1) * (2 * |s.im| * n ^ (b - 1)) :=
            mul_le_mul hpow h1w (norm_nonneg _) (Real.rpow_nonneg hn0.le _)
        _ = 2 * |s.im| * (n ^ (δ - 1) * n ^ (b - 1)) := by ring
        _ = 2 * |s.im| * n ^ (-(2 - b - δ)) := by
            rw [← Real.rpow_add hn0]; ring_nf
  · rw [if_neg hn, if_neg (by tauto), if_neg (by tauto)]; simp

/-- **Lemma 4.4(a), analytic estimate.** For `1 - δ ≤ σ ≤ 2`, `|t| ≥ 2`, `0 ≤ δ ≤ 1/100`, and
`Y = |t|^{1/(1-b)}`: the series `Ê_A(s)` converges absolutely and
`|Ê_A(s)| ≤ absorbedBound ς δ Y`. -/
theorem norm_absorbedHat_le {b : ℝ} {A : Set ℝ} {u : ℝ → ℝ} (h : AbsorbedHyp b A u)
    {ς : ℝ → ℝ} (hς : Monotone ς) (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x)))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) {s : ℂ} (hσ1 : 1 - δ ≤ s.re) (hσ2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) :
    Summable (fun n => ‖absorbedTerm b A u s n‖) ∧
    ‖absorbedHat b A u s‖ ≤ absorbedBound ς δ (|s.im| ^ (1 / (1 - b))) := by
  have hb0 := h.b_pos
  have hb := h.b_le
  set Y := |s.im| ^ (1 / (1 - b)) with hYdef
  have hσ0 : 0 ≤ s.re := by linarith
  have ht0 : 0 < |s.im| := by linarith
  have hY1 : 1 ≤ Y :=
    Real.one_le_rpow (by linarith) (by rw [one_div]; apply inv_nonneg.mpr; linarith)
  have hYt : Y ^ (1 - b) = |s.im| := by
    rw [hYdef, ← Real.rpow_mul ht0.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
  set β := 2 - b - δ with hβdef
  have hβ : 1 < β := by linarith
  -- the majorant
  set gH : ℝ → ℝ := fun n => if n ∈ A ∧ n ≤ Y then 2.001 * n ^ (δ - 1) else 0
  set gT : ℝ → ℝ := fun n => if n ∈ A ∧ Y < n then n ^ (-β) else 0
  have hgH : HasSum gH (∑ k ∈ below h.fin Y, gH k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    simp only [gH]
    rw [if_neg]
    rwa [mem_below] at hk
  have hgHsum : ∑ k ∈ below h.fin Y, gH k = 2.001 * ∑ k ∈ below h.fin Y, k ^ (δ - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_below] at hk
    simp only [gH, if_pos hk]
  obtain ⟨hTs, hTle⟩ := tail_summable h.fin h.one_lt hς hN hβ hY1
  have hg : HasSum (fun n => gH n + 2 * |s.im| * gT n)
      (∑ k ∈ below h.fin Y, gH k + 2 * |s.im| * ∑' n, gT n) :=
    hgH.add (hTs.hasSum.mul_left _)
  have hbound : ∀ n, ‖absorbedTerm b A u s n‖ ≤ gH n + 2 * |s.im| * gT n :=
    norm_absorbedTerm_le h hσ1 hσ2 hσ0 ht Y
  refine ⟨Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hg.summable, ?_⟩
  refine (tsum_of_norm_bounded hg hbound).trans ?_
  rw [hgHsum]
  have hHead := head_sum_le h.fin h.one_lt hς hN hδ0 (by linarith) hY1
  have hC : 0 ≤ Real.exp (-ς (Real.log Y)) := (Real.exp_pos _).le
  have hY0 : 0 < Y := by linarith
  have hTail : 2 * |s.im| * ∑' n, gT n ≤ 5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by
    have h1 : 2 * |s.im| * ∑' n, gT n ≤
        2 * |s.im| * (β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β)) :=
      mul_le_mul_of_nonneg_left hTle (by positivity)
    have h2 : |s.im| * Y ^ (1 - β) = Y ^ δ := by
      rw [← hYt, ← Real.rpow_add hY0]; congr 1; rw [hβdef]; ring
    have h3 : β / (β - 1) ≤ 2.7 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hYd : 0 ≤ Y ^ δ := Real.rpow_nonneg hY0.le _
    calc 2 * |s.im| * ∑' n, gT n ≤
        2 * |s.im| * (β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β)) := h1
      _ = 2 * (β / (β - 1)) * (Real.exp (-ς (Real.log Y)) * (|s.im| * Y ^ (1 - β))) := by ring
      _ = 2 * (β / (β - 1)) * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by rw [h2]; ring
      _ ≤ 2 * 2.7 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by
          gcongr
      _ = 5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by ring
  unfold absorbedBound
  linarith

/-- A sufficient condition for `absorbedBound` to be small: if `δ v - ς(v) ≤ -K` on
`0 ≤ v ≤ log Y`, then `absorbedBound ς δ Y ≤ (7.401 + 2.001 log Y) e^{-K}`. -/
lemma absorbedBound_le_of_gap {ς : ℝ → ℝ} (hς : Monotone ς) {δ Y K : ℝ} (hY : 1 ≤ Y)
    (hδ : δ < 1)
    (hgap : ∀ v ∈ Icc 0 (Real.log Y), δ * v - ς v ≤ -K) :
    absorbedBound ς δ Y ≤ (7.401 + 2.001 * Real.log Y) * Real.exp (-K) := by
  have hY0 : 0 < Y := by linarith
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have key : ∀ v, 1 ≤ v → v ≤ Y → v ^ δ * Real.exp (-ς (Real.log v)) ≤ Real.exp (-K) := by
    intro v hv1 hvY
    have hv0 : 0 < v := by linarith
    rw [Real.rpow_def_of_pos hv0, ← Real.exp_add, Real.exp_le_exp]
    have := hgap (Real.log v) ⟨Real.log_nonneg hv1, Real.log_le_log hv0 hvY⟩
    linarith
  have h1 := key Y hY le_rfl
  have hint : ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤
      Real.log Y * Real.exp (-K) := by
    have hle : ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤
        ∫ v in (1 : ℝ)..Y, Real.exp (-K) * v⁻¹ := by
      apply intervalIntegral.integral_mono_on hY
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
        refine integrableOn_Ioc_of_bdd (C := Real.exp (-ς 0)) (measurable_rpow_mul_exp hς)
          fun v hv => ?_
        have hv1 : 1 ≤ v := hv.1.le
        rw [abs_of_nonneg (by positivity)]
        have : v ^ (δ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
        have : Real.exp (-ς (Real.log v)) ≤ Real.exp (-ς 0) := by
          rw [Real.exp_le_exp]; have := hς (Real.log_nonneg hv1); linarith
        have : 0 ≤ Real.exp (-ς (Real.log v)) := by positivity
        nlinarith
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.inv₀ continuousOn_id
        intro v hv; rw [Set.uIcc_of_le hY] at hv; simp; linarith [hv.1]
      · intro v hv
        have hv0 : 0 < v := by linarith [hv.1]
        have := key v hv.1 hv.2
        rw [Real.rpow_sub hv0, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hv0]
        calc v ^ δ * Real.exp (-ς (Real.log v)) ≤ Real.exp (-K) := this
          _ = Real.exp (-K) * v⁻¹ * v := by field_simp
    refine hle.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hY0, div_one]
    ring
  unfold absorbedBound
  nlinarith [Real.exp_pos (-K)]

end Absorbed

end
