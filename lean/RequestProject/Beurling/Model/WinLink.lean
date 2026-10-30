module

public import RequestProject.Beurling.Model.JLaw
public import RequestProject.Beurling.RankFull.ModelCap

/-!
# The construction as a window model (Proposition 6.11, Theorem 6.23(a))

The window model of `RankFull/WindowModel.lean` has decided slots `dec ⊆ Fin N` and prime values
`q n`. For the construction, the decided slots are enumerated in decision order: the `n`-th slot
of the abstract law `constructionLaw` (a prime is placed, with a unit jump at the slot start) gets
the label `n` (`decN`), and `qN n` is the value of its prime.

* `decN_meas`, `qN_meas` : the labels and values are measurable;
* `qN_ge_one` (`hq1`), `qN_ge_Xm`, `tau_le_qN` (`hτq`, with `τl_ℓ = max(X₀⁻, (ℓ+1)/2)`): the
  model hypotheses; the label bound comes from the window count of §3.4 at the placed slot starts;
* `measurable_of_windowElems` : every function of the window elements is measurable, so
  `skelCount`, `rankFullCount`, `configCount`, `cfgSkelCount` are (`hXm`, `hmeasR`, `hmeas`,
  `hXm'`);
* `gridWin_sub` (`hJ`), `gridWin_le` (`hJz`) : the grid windows;
* `winCount_le_windowElems` : **the realised window counts are bounded by the window model**: on
  the good event (all stages good, jitters in `[0, 1]`), the elements of the realised system with
  value in `[a, b)` inject into `windowElems`, for `N`, `D`, `Dmax` large enough for `b`;
* `clusterUpTo_of_windows` : `ClusterUpTo` follows from the window-model cluster bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono RankFull.Config
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The decided slots of the abstract law. -/
def lawP (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (m : ℕ) : Prop := ω ∈ lawA θ X₀ m

open Classical in
/-- The rank of a decided slot in decision order. -/
noncomputable def lawRank (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (m : ℕ) : ℕ := Nat.count (lawP θ X₀ ω) m

open Classical in
/-- **The decided labels** `n < N`: the `n`-th decided slot exists. -/
noncomputable def decN (θ : ℝ) (X₀ : ℕ) (N : ℕ) (ω : JitterΩ) : Finset (Fin N) :=
  Finset.univ.filter fun n => ∃ m, lawP θ X₀ ω m ∧ lawRank θ X₀ ω m = n

open Classical in
/-- **The prime value of the `n`-th decided slot.** -/
noncomputable def qN (θ : ℝ) (X₀ : ℕ) (N : ℕ) (ω : JitterΩ) (n : Fin N) : ℝ :=
  ∑' m, if lawP θ X₀ ω m ∧ lawRank θ X₀ ω m = n then valF θ X₀ m ω else 0

lemma lawRank_inj {ω : JitterΩ} {m m' : ℕ} (hm : lawP θ X₀ ω m) (hm' : lawP θ X₀ ω m')
    (h : lawRank θ X₀ ω m = lawRank θ X₀ ω m') : m = m' := by
  classical
  unfold lawRank at h
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h (Nat.count_strict_mono hm hlt).ne
  · exact heq
  · exact absurd h (Nat.count_strict_mono hm' hgt).ne'

lemma qN_eq {N : ℕ} {ω : JitterΩ} {m : ℕ} {n : Fin N} (hm : lawP θ X₀ ω m)
    (hmn : lawRank θ X₀ ω m = n) : qN θ X₀ N ω n = valF θ X₀ m ω := by
  classical
  unfold qN
  rw [tsum_eq_single m]
  · rw [if_pos ⟨hm, hmn⟩]
  · intro m' hm'
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hm' (lawRank_inj h1 hm (h2.trans hmn.symm))

lemma mem_decN {N : ℕ} {ω : JitterΩ} {n : Fin N} :
    n ∈ decN θ X₀ N ω ↔ ∃ m, lawP θ X₀ ω m ∧ lawRank θ X₀ ω m = n := by
  simp [decN]

section Meas

variable (hc : Cond θ X₀)
include hc

lemma lawP_meas (m : ℕ) : MeasurableSet {ω | lawP θ X₀ ω m} :=
  jitterFiltration.le m _ (lawA_adapted hc m)

lemma lawRank_meas (m : ℕ) : Measurable fun ω => lawRank θ X₀ ω m := by
  classical
  apply measurable_to_countable'
  intro k
  have : (fun ω => lawRank θ X₀ ω m) ⁻¹' {k} = ⋃ T ∈ (Finset.range m).powerset,
      (if T.card = k then ⋂ i ∈ Finset.range m, ({ω | lawP θ X₀ ω i} ∩ {_ω | i ∈ T}) ∪
        ({ω | ¬ lawP θ X₀ ω i} ∩ {_ω | i ∉ T}) else ∅) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, Finset.mem_powerset]
    constructor
    · intro h
      refine ⟨(Finset.range m).filter (lawP θ X₀ ω), Finset.filter_subset _ _, ?_⟩
      rw [if_pos (by rw [← h, lawRank, Nat.count_eq_card_filter_range])]
      simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq, Finset.mem_filter]
      intro i hi
      by_cases hp : lawP θ X₀ ω i
      · exact Or.inl ⟨hp, hi, hp⟩
      · exact Or.inr ⟨hp, fun h => hp h.2⟩
    · rintro ⟨T, hT, hTk⟩
      split_ifs at hTk with hcard
      · rw [lawRank, Nat.count_eq_card_filter_range, ← hcard]
        congr 1
        ext i
        simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq] at hTk
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hi, hp⟩
          rcases hTk i hi with h | h
          · exact h.2
          · exact absurd hp h.1
        · intro hiT
          have hi := hT hiT
          rcases hTk i hi with h | h
          · exact ⟨hi, h.1⟩
          · exact absurd hiT h.2
      · exact absurd hTk (notMem_empty _)
  rw [this]
  refine Finset.measurableSet_biUnion _ fun T _ => ?_
  split_ifs
  · refine Finset.measurableSet_biInter _ fun i _ => ?_
    exact ((lawP_meas hc i).inter (MeasurableSet.const _)).union
      ((lawP_meas hc i).compl.inter (MeasurableSet.const _))
  · exact MeasurableSet.empty

lemma decN_meas (N : ℕ) (n : Fin N) : MeasurableSet {ω | n ∈ decN θ X₀ N ω} := by
  have : {ω | n ∈ decN θ X₀ N ω} =
      ⋃ m, {ω | lawP θ X₀ ω m} ∩ {ω | lawRank θ X₀ ω m = n} := by
    ext ω; simp [mem_decN]
  rw [this]
  exact MeasurableSet.iUnion fun m =>
    (lawP_meas hc m).inter (measurableSet_eq_fun (lawRank_meas hc m) measurable_const)

lemma qN_meas (N : ℕ) (n : Fin N) : Measurable fun ω => qN θ X₀ N ω n := by
  classical
  unfold qN
  refine measurable_tsum_of_finite_support (fun m => ?_) (fun ω => ?_)
  · exact Measurable.ite ((lawP_meas hc m).inter
      (measurableSet_eq_fun (lawRank_meas hc m) measurable_const))
      (valF_measurable hc (stageMeas hc) m) measurable_const
  · refine Set.Subsingleton.finite ?_
    intro m hm m' hm'
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hm hm'
    exact lawRank_inj hm.1.1 hm'.1.1 (hm.1.2.trans hm'.1.2.symm)

end Meas

/-! ### The model hypotheses -/

/-- The floor `X₀⁻ = X₀ - H(X₀)/2` of the jittered primes. -/
noncomputable def Xm (X₀ : ℕ) : ℝ := X₀ - capH X₀ X₀ / 2

/-- The label thresholds `τl_ℓ = max(X₀⁻, (ℓ + 1)/2)`. -/
noncomputable def tauL (X₀ : ℕ) {k : ℕ} (ℓ : Fin k) : ℝ :=
  max (Xm X₀) ((((ℓ : ℕ) : ℝ) + 1) / 2)

section Model

variable (hc : Cond θ X₀)
include hc

lemma valF_ge_slot (m : ℕ) (ω : JitterΩ) :
    slotF θ X₀ m ω - HF θ X₀ m ω / 2 ≤ valF θ X₀ m ω := by
  rw [valF_eq]
  exact (landing_mem_box (HF_pos hc m ω).le (clamp01_mem _)).1

lemma valF_ge_Xm (m : ℕ) (ω : JitterΩ) : Xm X₀ ≤ valF θ X₀ m ω := by
  have h1 := valF_ge_slot hc m ω
  have h2 := JitterFloor.capH_floor (Nat.cast_nonneg _) hc.hX (slotF_ge hc m ω)
  unfold Xm HF at *
  linarith

lemma valF_ge_78 (m : ℕ) (ω : JitterΩ) : 7 / 8 * slotF θ X₀ m ω ≤ valF θ X₀ m ω := by
  have h1 := valF_ge_slot hc m ω
  have h2 := four_capH_le (Nat.cast_nonneg _) hc.hX (slotF_ge hc m ω)
  unfold HF at h1
  linarith

/-- **`hq1`: the prime values are `≥ 1`.** -/
theorem qN_ge_one {N : ℕ} (ω : JitterΩ) (n : Fin N) (hn : n ∈ decN θ X₀ N ω) :
    1 ≤ qN θ X₀ N ω n := by
  obtain ⟨m, hm, hmn⟩ := mem_decN.mp hn
  rw [qN_eq hm hmn]
  have := valF_ge_78 hc m ω
  have := slotF_ge hc m ω
  linarith [X₀_ge_two_pow hc.hX]

theorem qN_ge_Xm {N : ℕ} (ω : JitterΩ) (n : Fin N) (hn : n ∈ decN θ X₀ N ω) :
    Xm X₀ ≤ qN θ X₀ N ω n := by
  obtain ⟨m, hm, hmn⟩ := mem_decN.mp hn
  rw [qN_eq hm hmn]; exact valF_ge_Xm hc m ω

variable (hev : Even X₀)
include hev

/-- **The rank of a decided slot is at most its window count** (§3.4). -/
theorem lawRank_le {ω : JitterΩ} {m : ℕ} :
    (lawRank θ X₀ ω m : ℝ) ≤ 1.01 * (slotF θ X₀ m ω - (X₀ - 1)) + 1 := by
  classical
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set S₀ := {m' | ω ∈ lawA θ X₀ m'}
  have hS₀ : ∀ m' ∈ S₀, placedAt h.limModel m' ∧
      UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m' + 1)) := by
    intro m' hm'
    have h1 := hm'.1
    have h2 := hm'.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨h1, h2⟩
  have hsX := slotF_ge hc m ω
  have hwin := window_count_on (winFacts h) S₀ hS₀ (limModel_slot_one h hev).1
    (a := (X₀ : ℝ) - 1) (b := slotF θ X₀ m ω) (by linarith)
  have hsub : ((Finset.range m).filter (lawP θ X₀ ω) : Set ℕ) ⊆
      {m' | m' ∈ S₀ ∧ (X₀ : ℝ) - 1 < h.limModel.slot (m' + 1) ∧
        h.limModel.slot (m' + 1) ≤ slotF θ X₀ m ω} := by
    intro m' hm'
    simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq] at hm'
    have h1 := slotF_ge hc m' ω
    have h2 : slotF θ X₀ m' ω ≤ slotF θ X₀ m ω :=
      (Mcl θ X₀ ω).slot_mono (by omega)
    simp only [slotF] at h1 h2 ⊢
    rw [hMe] at h1 h2 ⊢
    exact ⟨hm'.2, by linarith, h2⟩
  have hfin : {m' | m' ∈ S₀ ∧ (X₀ : ℝ) - 1 < h.limModel.slot (m' + 1) ∧
      h.limModel.slot (m' + 1) ≤ slotF θ X₀ m ω}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m' hm' => hm'.2.2
  have hc1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at hc1
  unfold lawRank
  rw [Nat.count_eq_card_filter_range]
  have : (((Finset.range m).filter (lawP θ X₀ ω)).card : ℝ) ≤
      ({m' | m' ∈ S₀ ∧ (X₀ : ℝ) - 1 < h.limModel.slot (m' + 1) ∧
        h.limModel.slot (m' + 1) ≤ slotF θ X₀ m ω}.ncard : ℝ) := by exact_mod_cast hc1
  exact this.trans hwin

/-- **The value of the `n`-th decided slot is `≥ (n + 1)/2`.** -/
theorem half_le_qN {N : ℕ} (ω : JitterΩ) (n : Fin N) (hn : n ∈ decN θ X₀ N ω) :
    (((n : ℕ) : ℝ) + 1) / 2 ≤ qN θ X₀ N ω n := by
  obtain ⟨m, hm, hmn⟩ := mem_decN.mp hn
  rw [qN_eq hm hmn]
  have h1 := lawRank_le hc hev (ω := ω) (m := m)
  rw [hmn] at h1
  have h2 := valF_ge_78 hc m ω
  have h3 := slotF_ge hc m ω
  have h16 := X₀_ge_two_pow hc.hX
  linarith

/-- **`hτq`: the label bound** `τl_ℓ ≤ q_n` for `ℓ ≤ #{decided slots before n}`. -/
theorem tau_le_qN {N k : ℕ} (ω : JitterΩ) (n : Fin N) (hn : n ∈ decN θ X₀ N ω) (ℓ : Fin k)
    (hℓ : ℓ.val ≤ ((decN θ X₀ N ω).filter (· < n)).card) : tauL X₀ ℓ ≤ qN θ X₀ N ω n := by
  have hcard : ((decN θ X₀ N ω).filter (· < n)).card ≤ n := by
    calc ((decN θ X₀ N ω).filter (· < n)).card ≤ (Finset.Iio n).card :=
          Finset.card_le_card fun i hi => Finset.mem_Iio.mpr (Finset.mem_filter.mp hi).2
      _ = n := Fin.card_Iio n
  have hℓn : ((ℓ : ℕ) : ℝ) ≤ (n : ℕ) := by exact_mod_cast hℓ.trans hcard
  have h1 := half_le_qN hc hev ω n hn
  have h2 := qN_ge_Xm hc ω n hn
  unfold tauL
  exact max_le h2 (by linarith)

end Model

/-! ### Measurability of the window counts -/

section WinMeas

variable (hc : Cond θ X₀)
include hc

lemma measurable_elemVal {N : ℕ} (p : (Fin N → ℕ) × ℕ) :
    Measurable fun ω => elemVal (qN θ X₀ N ω) p := by
  unfold elemVal
  exact measurable_const.mul (Finset.measurable_prod _ fun n _ => (qN_meas hc N n).pow_const _)

/-- **Every function of the window elements is measurable** (they range over the subsets of a
fixed finite set, each membership being measurable). -/
theorem measurable_of_windowElems {N D Dmax : ℕ} {J : Set ℝ} (hJ : MeasurableSet J)
    {β : Type*} [MeasurableSpace β] (f : Finset ((Fin N → ℕ) × ℕ) → β) :
    Measurable fun ω => f (windowElems (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax J) := by
  classical
  set C := (Fintype.piFinset fun _ : Fin N => Finset.range (D + 1)) ×ˢ
    Nat.smoothNumbersUpTo Dmax X₀
  set P : (Fin N → ℕ) × ℕ → JitterΩ → Prop := fun p ω =>
    (∀ n, p.1 n ≠ 0 → n ∈ decN θ X₀ N ω) ∧ ∑ n, p.1 n ≤ D ∧ elemVal (qN θ X₀ N ω) p ∈ J
  have hP : ∀ p, MeasurableSet {ω | P p ω} := by
    intro p
    refine MeasurableSet.inter ?_ ((MeasurableSet.const _).inter
      ((measurable_elemVal hc p) hJ))
    have : {ω | ∀ n, p.1 n ≠ 0 → n ∈ decN θ X₀ N ω} =
        ⋂ n, ({_ω | p.1 n = 0} ∪ {ω | n ∈ decN θ X₀ N ω}) := by
      ext ω
      simp only [mem_setOf_eq, mem_iInter, mem_union]
      exact ⟨fun h n => by by_cases hn : p.1 n = 0 <;> simp_all, fun h n hn =>
        (h n).resolve_left hn⟩
    show MeasurableSet {ω | ∀ n, p.1 n ≠ 0 → n ∈ decN θ X₀ N ω}
    rw [this]
    exact MeasurableSet.iInter fun n => (MeasurableSet.const _).union (decN_meas hc N n)
  have he : ∀ ω, windowElems (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax J =
      C.filter fun p => P p ω := fun ω => rfl
  simp_rw [he]
  intro B _
  have : (fun ω => f (C.filter fun p => P p ω)) ⁻¹' B =
      ⋃ T ∈ C.powerset.filter (fun T => f T ∈ B),
        ⋂ p ∈ C, ({ω | P p ω} ∩ {_ω | p ∈ T}) ∪ ({ω | ¬ P p ω} ∩ {_ω | p ∉ T}) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro hω
      refine ⟨C.filter fun p => P p ω, ⟨Finset.filter_subset _ _, hω⟩, ?_⟩
      simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq, Finset.mem_filter]
      intro p hp
      by_cases h : P p ω
      · exact Or.inl ⟨h, hp, h⟩
      · exact Or.inr ⟨h, fun h' => h h'.2⟩
    · rintro ⟨T, ⟨hTC, hfT⟩, hT⟩
      have : (C.filter fun p => P p ω) = T := by
        ext p
        simp only [mem_iInter, mem_union, mem_inter_iff, mem_setOf_eq] at hT
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hP'⟩
          rcases hT p hp with h | h
          · exact h.2
          · exact absurd hP' h.1
        · intro hpT
          have hp := hTC hpT
          rcases hT p hp with h | h
          · exact ⟨hp, h.1⟩
          · exact absurd hpT h.2
      rw [this]; exact hfT
  rw [this]
  refine Finset.measurableSet_biUnion _ fun T _ => ?_
  refine Finset.measurableSet_biInter _ fun p _ => ?_
  exact ((hP p).inter (MeasurableSet.const _)).union ((hP p).compl.inter (MeasurableSet.const _))

variable {N D Dmax : ℕ} {ι : Type*} {Jw : ι → Set ℝ} (hJw : ∀ J, MeasurableSet (Jw J))
include hJw

/-- `hXm`: the skeleton counts are measurable. -/
theorem meas_skelCount (r₀ : ℕ) (J : ι) (E : Matrix (Fin r₀) (Fin r₀) ℕ) (l : List ℕ) :
    Measurable fun ω =>
      skelCount (windowVecs (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Jw J)) E l := by
  have h := measurable_of_windowElems hc (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => skelCount ((T.filter fun p => p.1 ≠ 0).image Prod.fst) E l)
  exact h

/-- `hmeasR`: the rank-full counts are measurable. -/
theorem meas_rankFullCount (r₀ : ℕ) (J : ι) :
    Measurable fun ω => (rankFullCount r₀
      (windowVecs (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Jw J)) : ℝ≥0∞) := by
  have h := measurable_of_windowElems hc (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => (rankFullCount r₀ ((T.filter fun p => p.1 ≠ 0).image Prod.fst) : ℝ≥0∞))
  exact h

/-- `hmeas`: the configuration counts are measurable. -/
theorem meas_configCount (r₀ j k : ℕ) (J : ι) :
    Measurable fun ω => (configCount r₀ j k
      (windowVecs (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Jw J)) : ℝ≥0∞) := by
  have h := measurable_of_windowElems hc (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => (configCount r₀ j k ((T.filter fun p => p.1 ≠ 0).image Prod.fst) : ℝ≥0∞))
  exact h

open Classical in
/-- `hXm'`: the configuration skeleton counts are measurable. -/
theorem meas_cfgSkelCount (r₀ : ℕ) (J : ι) (r : ℕ) (C : Finset (Fin r))
    (lab : Finset (Fin (C.card * D))) (ex : Fin r → Fin r → ℕ)
    (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) :
    Measurable fun ω => cfgSkelCount D r₀ 0 0
      (tailOf (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Jw J))
      (windowVecs (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Jw J)) r C lab ex s4 := by
  have h := measurable_of_windowElems hc (N := N) (D := D) (Dmax := Dmax) (hJw J)
    (fun T => cfgSkelCount D r₀ 0 0
    (fun v => if h : ∃ d, (v, d) ∈ T then Classical.choose h else 0)
    ((T.filter fun p => p.1 ≠ 0).image Prod.fst) r C lab ex s4)
  exact h

end WinMeas

/-! ### The grid windows -/

lemma gridDelta_two_lt {z : ℝ} (hz : 2 ≤ Real.log z) : 2 * gridDelta z < 1 := by
  unfold gridDelta
  have h1 : (2 : ℝ) ^ 6 ≤ Real.log z ^ 6 := pow_le_pow_left₀ (by norm_num) hz 6
  rw [show 2 * (2 / Real.log z ^ 6) = 4 / Real.log z ^ 6 by ring, div_lt_one (by positivity)]
  linarith

/-- `hJ`: a grid window `[k δ, (k + 2) δ)` has length `2δ(z) < 1`. -/
lemma gridWin_sub (z : ℝ) (k : ℤ) :
    Ico (k * gridDelta z) ((k + 2) * gridDelta z) ⊆
      Ico (k * gridDelta z) (k * gridDelta z + 2 * gridDelta z) := by
  intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩

/-- `hJz`: a grid window starting below `2z` lies in `(-∞, 2z + 1]`. -/
lemma gridWin_le {z : ℝ} (hz : 2 ≤ Real.log z) {k : ℤ} (hk : k * gridDelta z < 2 * z) :
    Ico (k * gridDelta z) ((k + 2) * gridDelta z) ⊆ Iic (2 * z + 1) := by
  intro x hx
  have := gridDelta_two_lt hz
  simp only [mem_Iic]
  linarith [hx.2]

/-! ### The realised window counts are bounded by the window model -/

/-- The rational part `∏_{p < X₀} p^{e_p}` of an element, as an integer. -/
noncomputable def ratPart (e : PIdx X₀ →₀ ℕ) : ℕ :=
  e.prod fun i k => (match i with | Sum.inl p => p.1 | Sum.inr _ => 1) ^ k

open Classical in
/-- The exponent vector of an element over the decided labels. -/
noncomputable def winVec (θ : ℝ) (X₀ N : ℕ) (ω : JitterΩ) (e : PIdx X₀ →₀ ℕ) : Fin N → ℕ :=
  fun n => if n ∈ decN θ X₀ N ω then e (Sum.inr (Nat.nth (lawP θ X₀ ω) n)) else 0

lemma nth_of_mem_decN {N : ℕ} {ω : JitterΩ} {n : Fin N} (hn : n ∈ decN θ X₀ N ω) :
    lawP θ X₀ ω (Nat.nth (lawP θ X₀ ω) n) ∧
      lawRank θ X₀ ω (Nat.nth (lawP θ X₀ ω) n) = n := by
  classical
  obtain ⟨m, hm, hmn⟩ := mem_decN.mp hn
  have : Nat.nth (lawP θ X₀ ω) n = m := by
    rw [← hmn]; unfold lawRank; exact Nat.nth_count hm
  rw [this]; exact ⟨hm, hmn⟩

section Count

variable (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
  (hG : ∀ m, ω ∈ stageGood θ X₀ m)
include hc hev hG

/-- A jittered prime of an element of value `< b` is decided, with rank `< N`. -/
lemma jit_of_elem {N : ℕ} {b : ℝ} (hN : 1.01 * (8 / 7 * b - ((X₀ : ℝ) - 1)) + 1 < N)
    {e : PIdx X₀ →₀ ℕ} (he : Live (DF θ X₀ ω) e) (hb : eval (DF θ X₀ ω) e < b) {m : ℕ}
    (hm : e (Sum.inr m) ≠ 0) : lawP θ X₀ ω m ∧ lawRank θ X₀ ω m < N := by
  have hpl : placedAt (Mcl θ X₀ ω) m := he m hm
  have hP : lawP θ X₀ ω m := ⟨hpl, hG m⟩
  refine ⟨hP, ?_⟩
  have hpos : Pos (DF θ X₀ ω) := (pos2_DM hc.hX (U := Ucl ω) (fun j => clamp01_mem (ω j))
    (by rw [Mcl_eq hc]; exact (hc.std ω).limModel_low)).pos
  have hv := pval_le_eval hpos he (i := Sum.inr m) (Finsupp.mem_support_iff.mpr hm)
  have hv' : pval (X₀ := X₀) (DF θ X₀ ω) (Sum.inr m) = valF θ X₀ m ω := rfl
  have h78 := valF_ge_78 hc m ω
  have hr := lawRank_le hc hev (ω := ω) (m := m)
  have : (lawRank θ X₀ ω m : ℝ) < N := by
    rw [hv'] at hv
    linarith
  exact_mod_cast this

/-- The rational and jittered factors of a prime. -/
def ratF : PIdx X₀ → ℝ
  | Sum.inl p => (p.1 : ℝ)
  | Sum.inr _ => 1

def jitF (D : PrimeData) : PIdx X₀ → ℝ
  | Sum.inl _ => 1
  | Sum.inr m => D.v m

omit hc hev hG in
lemma pval_eq_mul (D : PrimeData) (i : PIdx X₀) : pval D i = ratF i * jitF D i := by
  cases i <;> simp [pval, ratF, jitF]

omit hc hev hG in
lemma ratPart_cast (e : PIdx X₀ →₀ ℕ) :
    (ratPart e : ℝ) = ∏ i ∈ e.support, ratF i ^ e i := by
  unfold ratPart Finsupp.prod
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  cases i <;> simp [ratF]

omit hc hev hG in
/-- `val(e) = ratPart(e) · ∏ (jittered values)`. -/
lemma eval_split (D : PrimeData) (e : PIdx X₀ →₀ ℕ) :
    eval D e = (ratPart e : ℝ) * ∏ i ∈ e.support, jitF D i ^ e i := by
  unfold eval Finsupp.prod
  rw [ratPart_cast, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  show pval D i ^ e i = _
  rw [pval_eq_mul, mul_pow]

/-- **The jittered part over the decided labels.** -/
lemma jit_prod_eq {N : ℕ} {b : ℝ} (hN : 1.01 * (8 / 7 * b - ((X₀ : ℝ) - 1)) + 1 < N)
    {e : PIdx X₀ →₀ ℕ} (he : Live (DF θ X₀ ω) e) (hb : eval (DF θ X₀ ω) e < b) :
    ∏ n : Fin N, qN θ X₀ N ω n ^ winVec θ X₀ N ω e n =
      ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i := by
  classical
  refine Finset.prod_bij_ne_one (fun n _ _ => Sum.inr (Nat.nth (lawP θ X₀ ω) n))
    (fun n _ hn => ?_) (fun n _ hn n' _ hn' h => ?_) (fun i hi hg => ?_) (fun n _ hn => ?_)
  · have hdec : n ∈ decN θ X₀ N ω := by
      by_contra hd; apply hn; simp [winVec, hd]
    rw [Finsupp.mem_support_iff]
    intro h0; apply hn; simp [winVec, hdec, h0]
  · have hd : n ∈ decN θ X₀ N ω := by
      by_contra hd; apply hn; simp [winVec, hd]
    have hd' : n' ∈ decN θ X₀ N ω := by
      by_contra hd'; apply hn'; simp [winVec, hd']
    simp only [Sum.inr.injEq] at h
    have h1 := (nth_of_mem_decN hd).2
    have h2 := (nth_of_mem_decN hd').2
    rw [h] at h1
    exact Fin.ext (h1.symm.trans h2)
  · cases i with
    | inl p => exact absurd (by simp [jitF]) hg
    | inr m =>
      have hm := Finsupp.mem_support_iff.mp hi
      obtain ⟨hP, hr⟩ := jit_of_elem hc hev hG hN he hb hm
      set n : Fin N := ⟨lawRank θ X₀ ω m, hr⟩
      have hdec : n ∈ decN θ X₀ N ω := mem_decN.mpr ⟨m, hP, rfl⟩
      have hnth : Nat.nth (lawP θ X₀ ω) n = m := by
        show Nat.nth (lawP θ X₀ ω) (lawRank θ X₀ ω m) = m
        unfold lawRank; exact Nat.nth_count hP
      refine ⟨n, Finset.mem_univ _, ?_, by simp only [hnth]⟩
      rw [qN_eq hP rfl]
      simp only [winVec, if_pos hdec, hnth]
      exact hg
  · have hdec : n ∈ decN θ X₀ N ω := by
      by_contra hd; apply hn; simp [winVec, hd]
    obtain ⟨hP, hr⟩ := nth_of_mem_decN hdec
    rw [qN_eq hP hr]
    simp only [winVec, if_pos hdec, jitF]
    rfl

omit hc hev hG in
lemma ratPart_pos (e : PIdx X₀ →₀ ℕ) : 0 < ratPart e := by
  unfold ratPart Finsupp.prod
  refine Finset.prod_pos fun i _ => pow_pos ?_ _
  cases i with
  | inl p => exact p.2.1.pos
  | inr _ => exact one_pos

omit hc hev hG in
/-- **Unique factorization for the rational part.** -/
lemma factorization_ratPart (e : PIdx X₀ →₀ ℕ) (p : {p : ℕ // p.Prime ∧ p < X₀}) :
    (ratPart e).factorization p.1 = e (Sum.inl p) := by
  classical
  unfold ratPart Finsupp.prod
  rw [Nat.factorization_prod fun i _ => (pow_pos (by cases i with
    | inl q => exact q.2.1.pos
    | inr _ => exact one_pos) _).ne']
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  have hterm : ∀ i ∈ e.support, ((match i with | Sum.inl p => p.1 | Sum.inr _ => 1) ^ e i :
      ℕ).factorization p.1 = if i = Sum.inl p then e i else 0 := by
    intro i _
    cases i with
    | inl q =>
      rw [Nat.factorization_pow, Finsupp.smul_apply, q.2.1.factorization]
      by_cases hq : q = p
      · subst hq; simp
      · have : q.1 ≠ p.1 := fun h => hq (Subtype.ext h)
        simp [this, hq]
    | inr _ => simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

omit hc hev hG in
lemma ratPart_smooth (e : PIdx X₀ →₀ ℕ) : ratPart e ∈ Nat.smoothNumbers X₀ := by
  classical
  rw [Nat.mem_smoothNumbers']
  intro q hq hdvd
  unfold ratPart Finsupp.prod at hdvd
  obtain ⟨i, _, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hdvd
  cases i with
  | inl p =>
    have := hq.dvd_of_dvd_pow hi
    rw [Nat.prime_dvd_prime_iff_eq hq p.2.1] at this
    rw [this]; exact p.2.2
  | inr _ =>
    have := hq.dvd_of_dvd_pow hi
    simp only [Nat.dvd_one] at this
    exact absurd this hq.one_lt.ne'

/-- **The element map into the window model.** -/
theorem mem_windowElems {N D Dmax : ℕ} {b : ℝ} {J : Set ℝ}
    (hN : 1.01 * (8 / 7 * b - ((X₀ : ℝ) - 1)) + 1 < N) (hD : b ≤ Xm X₀ ^ (D + 1))
    (hDmax : b ≤ Dmax) {e : PIdx X₀ →₀ ℕ} (he : Live (DF θ X₀ ω) e)
    (heJ : eval (DF θ X₀ ω) e ∈ J) (hb : eval (DF θ X₀ ω) e < b) :
    (winVec θ X₀ N ω e, ratPart e) ∈
      windowElems (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax J := by
  classical
  have hpos : Pos (DF θ X₀ ω) := (pos2_DM hc.hX (U := Ucl ω) (fun j => clamp01_mem (ω j))
    (by rw [Mcl_eq hc]; exact (hc.std ω).limModel_low)).pos
  have hsplit := eval_split (DF θ X₀ ω) e
  have hjp := jit_prod_eq hc hev hG hN he hb
  have hXm1 : 1 < Xm X₀ := by
    have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
    unfold Xm; linarith [X₀_ge_two_pow hc.hX]
  have hr1 : (1 : ℝ) ≤ ratPart e := by exact_mod_cast ratPart_pos e
  have hJ1 : 1 ≤ ∏ n : Fin N, qN θ X₀ N ω n ^ winVec θ X₀ N ω e n := by
    refine one_le_prod_of _ _ fun n _ => ?_
    by_cases hn : n ∈ decN θ X₀ N ω
    · exact one_le_pow₀ (qN_ge_one hc ω n hn)
    · simp [winVec, hn]
  -- the jittered degree
  have hdeg : ∑ n, winVec θ X₀ N ω e n ≤ D := by
    have h1 : Xm X₀ ^ (∑ n, winVec θ X₀ N ω e n) ≤
        ∏ n : Fin N, qN θ X₀ N ω n ^ winVec θ X₀ N ω e n := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by linarith) _) fun n _ => ?_
      by_cases hn : n ∈ decN θ X₀ N ω
      · exact pow_le_pow_left₀ (by linarith) (qN_ge_Xm hc ω n hn) _
      · simp [winVec, hn]
    have h2 : ∏ n : Fin N, qN θ X₀ N ω n ^ winVec θ X₀ N ω e n < Xm X₀ ^ (D + 1) := by
      rw [hjp]
      have : ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i ≤ eval (DF θ X₀ ω) e := by
        rw [hsplit]; nlinarith [show (0 : ℝ) ≤ ∏ i ∈ e.support, jitF (DF θ X₀ ω) i ^ e i by
          rw [← hjp]; linarith]
      linarith
    by_contra hc'
    push_neg at hc'
    have := pow_le_pow_right₀ hXm1.le (show D + 1 ≤ ∑ n, winVec θ X₀ N ω e n by omega)
    linarith
  rw [windowElems, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, hdeg, ?_⟩
  · refine Fintype.mem_piFinset.mpr fun n => Finset.mem_range.mpr ?_
    show winVec θ X₀ N ω e n < D + 1
    have := Finset.single_le_sum (f := winVec θ X₀ N ω e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ n)
    omega
  · rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨?_, ratPart_smooth e⟩
    have : (ratPart e : ℝ) ≤ Dmax := by
      have : (ratPart e : ℝ) ≤ eval (DF θ X₀ ω) e := by rw [hsplit, ← hjp]; nlinarith
      linarith
    exact_mod_cast this
  · intro n hn
    by_contra hd; exact hn (by simp [winVec, hd])
  · show elemVal (qN θ X₀ N ω) _ ∈ J
    unfold elemVal
    rw [hjp, ← hsplit]
    exact heJ

/-- **The element map is injective.** -/
theorem winVec_inj {N : ℕ} {b : ℝ} (hN : 1.01 * (8 / 7 * b - ((X₀ : ℝ) - 1)) + 1 < N)
    {e e' : PIdx X₀ →₀ ℕ} (he : Live (DF θ X₀ ω) e) (hb : eval (DF θ X₀ ω) e < b)
    (he' : Live (DF θ X₀ ω) e') (hb' : eval (DF θ X₀ ω) e' < b)
    (h : (winVec θ X₀ N ω e, ratPart e) = (winVec θ X₀ N ω e', ratPart e')) : e = e' := by
  classical
  simp only [Prod.mk.injEq] at h
  obtain ⟨hv, hd⟩ := h
  have key : ∀ {f f' : PIdx X₀ →₀ ℕ}, Live (DF θ X₀ ω) f → eval (DF θ X₀ ω) f < b →
      winVec θ X₀ N ω f = winVec θ X₀ N ω f' → ∀ m, f (Sum.inr m) ≠ 0 →
        f (Sum.inr m) = f' (Sum.inr m) := by
    intro f f' hf hfb hvv m hm
    obtain ⟨hP, hr⟩ := jit_of_elem hc hev hG hN hf hfb hm
    set n : Fin N := ⟨lawRank θ X₀ ω m, hr⟩
    have hdec : n ∈ decN θ X₀ N ω := mem_decN.mpr ⟨m, hP, rfl⟩
    have hnth : Nat.nth (lawP θ X₀ ω) n = m := by
      show Nat.nth (lawP θ X₀ ω) (lawRank θ X₀ ω m) = m
      unfold lawRank; exact Nat.nth_count hP
    have := congrFun hvv n
    simp only [winVec, if_pos hdec, hnth] at this
    exact this
  ext i
  cases i with
  | inl p => rw [← factorization_ratPart, ← factorization_ratPart, hd]
  | inr m =>
    by_cases hm : e (Sum.inr m) ≠ 0
    · exact key he hb hv m hm
    · by_cases hm' : e' (Sum.inr m) ≠ 0
      · exact (key he' hb' hv.symm m hm').symm
      · push_neg at hm hm'; rw [hm, hm']

/-- **The realised window counts are bounded by the window model**: on the good event, the
elements of the realised system with value in `[a, b)` inject into `windowElems`. -/
theorem winCount_le_windowElems {N D Dmax : ℕ} {a b : ℝ}
    (hN : 1.01 * (8 / 7 * b - ((X₀ : ℝ) - 1)) + 1 < N) (hD : b ≤ Xm X₀ ^ (D + 1))
    (hDmax : b ≤ Dmax) :
    (winCount (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) a b : ℝ) ≤
      (windowElems (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Ico a b)).card := by
  classical
  set M := Mcl θ X₀ ω
  set U := Ucl ω
  have hok : RealisedOK M (capH X₀) U := by
    rw [show M = (hc.std ω).limModel from Mcl_eq hc ω]
    exact limModel_realisedOK (hc.std ω)
  set S3 : Set (PIdx X₀ →₀ ℕ) := {e | Live (DM M U) e ∧ a ≤ eval (DM M U) e ∧
    eval (DM M U) e < b}
  have h12 : winCount (realisedSystem M (capH X₀) U) a b =
      {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < b}.ncard := by
    unfold winCount
    have himg : {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧
        idxVal M (capH X₀) U f < b} = (Finsupp.equivMapDomain hok.equiv) ''
          {e : ℕ →₀ ℕ | a ≤ (realisedSystem M (capH X₀) U).val e ∧
            (realisedSystem M (capH X₀) U).val e < b} := by
      ext f
      simp only [mem_setOf_eq, mem_image]
      constructor
      · intro hf
        refine ⟨Finsupp.equivMapDomain hok.equiv.symm f, ?_, by
          simp [← Finsupp.equivMapDomain_trans]⟩
        rw [val_eq_idxVal hok]; simpa [← Finsupp.equivMapDomain_trans] using hf
      · rintro ⟨e, he, rfl⟩
        rwa [← val_eq_idxVal hok]
    rw [himg, Set.ncard_image_of_injective _ (equivMapDomain_inj _)]
  have h23 : {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧
      idxVal M (capH X₀) U f < b}.ncard = S3.ncard := by
    refine ncard_eq_of_mapE (U := U) (fun f => ?_) (fun e he => he.1)
    simp only [S3, mem_setOf_eq, eval_mapE]
    exact ⟨fun h => ⟨live_mapE M U f, h⟩, fun h => h.2⟩
  rw [h12, h23]
  have hmaps : Set.MapsTo (fun e => (winVec θ X₀ N ω e, ratPart e)) S3
      (windowElems (decN θ X₀ N ω) (qN θ X₀ N ω) X₀ D Dmax (Ico a b) : Set _) := by
    intro e he
    exact mem_windowElems hc hev hG hN hD hDmax he.1 ⟨he.2.1, he.2.2⟩ he.2.2
  have hinj : Set.InjOn (fun e => (winVec θ X₀ N ω e, ratPart e)) S3 := by
    intro e he e' he' h
    exact winVec_inj hc hev hG hN he.1 he.2.2 he'.1 he'.2.2 h
  have := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at this
  exact_mod_cast this

end Count

/-! ### `ClusterUpTo` from the window-model cluster bounds -/

/-- **`ClusterUpTo` on the good event from the window-model counts**: if every grid window at a
dyadic height `z ≤ Z` holds at most `M₁` window-model elements (labels `N(z)`, degree `D(z)`,
rigid part `≤ Dmax(z)`, large enough for `2z + 1`), then the realised system satisfies
`ClusterUpTo` on the event that all stages are good and the jitters lie in `[0, 1]`. -/
theorem clusterUpTo_of_windows (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hU : ∀ j, ω j ∈ Icc (0 : ℝ) 1) (hG : ∀ m, ω ∈ stageGood θ X₀ m) {Z M₁ : ℝ}
    (Np Dp Dmaxp : ℝ → ℕ)
    (hpar : ∀ z, IsDyadicHeight X₀ z → z ≤ Z →
      1.01 * (8 / 7 * (2 * z + 1) - ((X₀ : ℝ) - 1)) + 1 < Np z ∧
        2 * z + 1 ≤ Xm X₀ ^ (Dp z + 1) ∧ 2 * z + 1 ≤ Dmaxp z)
    (hcl : ∀ z, IsDyadicHeight X₀ z → z ≤ Z → ∀ k : ℤ, z ≤ k * gridDelta z →
      k * gridDelta z < 2 * z →
      ((windowElems (decN θ X₀ (Np z) ω) (qN θ X₀ (Np z) ω) X₀ (Dp z) (Dmaxp z)
        (Ico (k * gridDelta z) ((k + 2) * gridDelta z))).card : ℝ) ≤ M₁) :
    ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀ Z M₁ := by
  intro z hz hzZ k hk1 hk2
  have hM : constructedModel θ X₀ ω = Mcl θ X₀ ω := by unfold Mcl; rw [Ucl_eq hU]
  rw [hM]
  obtain ⟨hN, hD, hDm⟩ := hpar z hz hzZ
  -- `log z ≥ 2`
  have hz2 : 2 ≤ Real.log z := by
    obtain ⟨m, rfl⟩ := hz
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have h16 := X₀_ge_two_pow hc.hX
    have h1 : Real.exp 2 ≤ (X₀ : ℝ) / 2 * 2 ^ m := by
      have he : Real.exp 2 ≤ 8 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith [Real.exp_pos 1]
      have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hδ := gridDelta_two_lt hz2
  have hb : (k + 2) * gridDelta z ≤ 2 * z + 1 := by
    have : (k + 2) * gridDelta z = k * gridDelta z + 2 * gridDelta z := by ring
    linarith
  have h := winCount_le_windowElems (N := Np z) (D := Dp z) (Dmax := Dmaxp z)
    (a := k * gridDelta z) (b := (k + 2) * gridDelta z) hc hev (ω := ω) hG (by nlinarith)
    (hb.trans hD) (hb.trans hDm)
  rw [Ucl_eq hU] at h
  exact h.trans (hcl z hz hzZ k hk1 hk2)

end BModel

end
