module

public import RequestProject.Beurling.Model.Init
public import RequestProject.Beurling.Model.Window

/-!
# Theorem 2.1 with the slot model of §3 constructed

`Theorem21InputsP` (Construction/JitterRegular.lean) asks for a family of slot models
`M : JitterΩ → SlotModel X₀` with, on the good event, the arrivals tied to the composites
(`ArrivalsLinked`), the slot facts (`SlotFacts`) and the target formula (first conjunct of
`PartIRestO`). Here `M` is **constructed** (`constructedModel θ X₀`, Model/Fix.lean) and these
conjuncts are **proved**:

* `ArrivalsLinked` (`limModel_linked`) and the target formula (`limModel_T_formula`) from the
  fixed-point equations;
* `SlotFacts`: the base case of Lemma 3.6 (`limModel_init_count`, `limModel_init_gap`) and the
  window count (`window_count`).

`Theorem21InputsQ` is `Theorem21InputsP` with `M` fixed to the construction and these conjuncts
removed. `theorem21InputsP_of_Q` derives `Theorem21InputsP` from it, from (84) of the paper
(`ShortIntervalPNT`, the Heath-Brown/Huxley short-interval prime number theorem, a named
hypothesis about ℕ), and from the paper's claim (§3.4) that the event `𝒩₌` that two distinct
elements of the constructed system have equal values is null (`TiesNull`). The target formula and
the window count are proved off `𝒩₌`; `𝒩₌` is added to the failure events, which costs no
probability in `TableBudget`.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono MeasureTheory

namespace BModel

variable {X₀ : ℕ}

/-- **No ties**: distinct elements of the realised system have distinct values (the complement of
the event `𝒩₌` of §3.4). -/
def TieFree (M : SlotModel X₀) (U : ℕ → ℝ) : Prop :=
  ∀ e e' : RealisedIdx M →₀ ℕ, idxVal M (capH X₀) U e = idxVal M (capH X₀) U e' → e = e'

/-- **The event `𝒩₌`** for the construction (where the standing conditions hold). -/
def tiesEvent (θ : ℝ) (X₀ : ℕ) : Set JitterΩ :=
  {ω | Std θ X₀ ω ∧ ¬ TieFree (constructedModel θ X₀ ω) ω}

/-- **§3.4: `𝒩₌` is null** ("after cancelling common factors, the latest-decided prime of such a
pair divides one side only, so it would have to land on a point fixed by the past, which has
probability `0` by the box-uniform landing law"). A named hypothesis: the paper's claim for the
constructed model. -/
def TiesNull : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → jitterMeasure (tiesEvent θ X₀) = 0

section Ties

variable {M : SlotModel X₀} {U : ℕ → ℝ}

lemma noCoincidence_of_tieFree (h : TieFree M U) : NoCoincidence M U := by
  intro k hk p hp hpX heq
  have := h (Finsupp.single (Sum.inr ⟨k, hk⟩) 1) (Finsupp.single (Sum.inl ⟨p, hp, hpX⟩) 1)
    (by rw [idxVal_single, idxVal_single]; exact heq)
  have h2 := congrArg (fun f => f (Sum.inr ⟨k, hk⟩)) this
  simp at h2

lemma unitJumps_of_tieFree (h : TieFree M U) : UnitJumps X₀ (DM M U) := by
  classical
  intro n _ hsm hA
  obtain ⟨e, hv, hrat⟩ := exists_rat_elem M U hsm
  obtain ⟨-, e', he', hval, k, hk, -, -⟩ := hA
  obtain ⟨f, rfl⟩ := exists_mapE (U := U) he'
  rw [eval_mapE] at hval
  have hkp : placedAt M k := he' k hk
  rw [mapE_apply_inr, dif_pos hkp] at hk
  have hef := h e f (by rw [hv, hval])
  subst hef
  obtain ⟨p, hp⟩ := hrat _ (Finsupp.mem_support_iff.mpr hk)
  cases hp

end Ties

section Constructed

variable {θ : ℝ} {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- **The slot facts hold for the constructed model** off `𝒩₌`. -/
theorem limModel_slotFacts (hev : Even X₀) (ht : TieFree h.limModel U) :
    SlotFacts h.limModel U :=
  ⟨limModel_init_count h hev, limModel_init_gap h hev,
    window_count (winFacts h) (unitJumps_of_tieFree ht) (limModel_slot_one h hev).1⟩

end Constructed

/-! ### The top-level hypothesis with the slot model constructed -/

/-- **Theorem 2.1, hypothesis on the concrete construction, with the slot model constructed.**
`Theorem21InputsP` with the slot model fixed to the construction of §3
(`constructedModel θ X₀`), and without the conjuncts `ArrivalsLinked`, `SlotFacts` and the target
formula of `PartIRestO`, which are proved. -/
def Theorem21InputsQ : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ) (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        (constructedModel θ X₀ ω).QueueWindowData ∧
        Theorem410RestM θ X₀ (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω)
          (realisedA (constructedModel θ X₀ ω) (capH X₀) ω) (fun n => solveU (θ / 2) n) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- **Adding a null event to the failure events preserves `TableBudget`.** -/
theorem tableBudget_add_null {ι : Type} {E : ι → Set JitterΩ} {time scale : ι → ℕ} {X₀ : ℝ}
    (htab : TableBudget jitterMeasure X₀ E time scale) {N : Set JitterΩ}
    (hN : jitterMeasure N = 0) :
    TableBudget jitterMeasure X₀ (Sum.elim E fun _ : Unit => Nᶜ) (Sum.elim time fun _ => 0)
      (Sum.elim scale fun _ => 0) := by
  intro m
  set E' := Sum.elim E fun _ : Unit => Nᶜ
  set time' := Sum.elim time fun _ : Unit => 0
  set scale' := Sum.elim scale fun _ : Unit => 0
  have hgood : ∀ t, goodBefore E' time' t ⊆ goodBefore E time t := by
    intro t ω hω
    simp only [goodBefore, mem_iInter] at hω ⊢
    exact fun i hi => hω (Sum.inl i) hi
  set f : {i' // scale' i' = m} → ENNReal :=
    fun x => jitterMeasure ((E' x.1)ᶜ ∩ goodBefore E' time' (time' x.1))
  set φ : {i // scale i = m} → {i' // scale' i' = m} := fun x => ⟨Sum.inl x.1, x.2⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Subtype.mk.injEq, Sum.inl.injEq] at hxy
    exact Subtype.ext hxy
  have hsupp : Function.support f ⊆ Set.range φ := by
    rintro ⟨i' | u, hi'⟩ hf
    · exact ⟨⟨i', hi'⟩, rfl⟩
    · exfalso
      apply hf
      simp only [f, E', Sum.elim_inr, compl_compl]
      exact measure_mono_null Set.inter_subset_left hN
  calc ∑' x : {i' // scale' i' = m}, f x = ∑' x : {i // scale i = m}, f (φ x) :=
        (hφ.tsum_eq hsupp).symm
    _ ≤ ∑' x : {i // scale i = m}, jitterMeasure ((E x.1)ᶜ ∩ goodBefore E time (time x.1)) :=
        ENNReal.tsum_le_tsum fun x => measure_mono (Set.inter_subset_inter_right _ (hgood _))
    _ ≤ _ := htab m

/-- **`Theorem21InputsQ` implies `Theorem21InputsP`**, given (84) (`ShortIntervalPNT`, the
Heath-Brown short-interval prime number theorem in Huxley's range) and the nullity of `𝒩₌`
(`TiesNull`, §3.4). -/
theorem theorem21InputsP_of_Q (hHB : ShortIntervalPNT) (hnull : TiesNull)
    (h : Theorem21InputsQ) : Theorem21InputsP := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max XHux x₁, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨ι, hι, E, time, ⟨scale, htab⟩, hP⟩ :=
    hX X₀ hev h1 ((le_max_left _ _).trans h2)
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hHB0 : ShortIntervalPNTFrom X₀ := hx₁.mono ((le_max_right _ _).trans h2)
  set N := tiesEvent θ X₀
  refine ⟨constructedModel θ X₀, ι ⊕ Unit, inferInstance, Sum.elim E fun _ => Nᶜ,
    Sum.elim time fun _ => 0, ⟨_, tableBudget_add_null htab (hnull θ hθ X₀ hev h1)⟩,
    fun ω hω hU => ?_⟩
  have hG : ω ∈ goodAll E := by
    simp only [goodAll, mem_iInter] at hω ⊢
    exact fun i => hω (Sum.inl i)
  have hNω : ω ∉ N := by
    simp only [goodAll, mem_iInter] at hω
    simpa using hω (Sum.inr ())
  have hstd : Std θ X₀ ω := ⟨hθ, hlog, hU, hHB0⟩
  have ht : TieFree (constructedModel θ X₀ ω) ω := by
    by_contra hc; exact hNω ⟨hstd, hc⟩
  obtain ⟨hq, hC, hcl⟩ := hP ω hG hU
  rw [constructedModel_eq hstd] at ht hq hC hcl ⊢
  exact ⟨limModel_linked hstd, limModel_slotFacts hstd hev ht,
    ⟨limModel_T_formula hstd (noCoincidence_of_tieFree ht), hq⟩, hC, hcl⟩

/-- Theorem 2.1 from `Theorem21InputsQ`, (84) and the nullity of `𝒩₌`. -/
theorem theorem21_of_Q (hHB : ShortIntervalPNT) (hnull : TiesNull) (h : Theorem21InputsQ) :
    Theorem21 :=
  theorem21_of_P (theorem21InputsP_of_Q hHB hnull h)

/-- **Corollary 2.2** from `Theorem21InputsQ`, (84) and the nullity of `𝒩₌`. -/
theorem corollary_2_2_of_Q (hHB : ShortIntervalPNT) (hnull : TiesNull)
    (h : Theorem21InputsQ) : ¬ QuestionQ :=
  corollary_2_2_of_P (theorem21InputsP_of_Q hHB hnull h)

end BModel

end
