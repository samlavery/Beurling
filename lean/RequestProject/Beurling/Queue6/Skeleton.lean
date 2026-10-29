module

public import RequestProject.Beurling.Construction.Budget

/-!
# The probability skeleton of §6.4 (Definition 6.8, Lemma 6.10): queue constraints as events

Definition 6.8 puts into `Good(<t)` both the events `E` with `t(E) < t` and the queue constraints
`Q_j ≤ B(s_j)` with `t_j < t`, where the time `t_j = ⌈s_{j+1}⌉ + 1` of a queue constraint is
random. The Lean good event `goodBefore E time t` (Construction/Greedy.lean) has deterministic
times only. The two are reconciled here, abstractly:

* `Queue6.QC ok tq t` : the queue constraints with time `< t`, `⋂_{tq j < t} ok j`;
* `Queue6.paperGood E time ok tq t` : the good event of Definition 6.8, `QC t ∩ goodBefore E t`;
* `Queue6.withQC` : the modified events `E'_i := E_i ∪ QC(t(E_i))ᶜ`. Then
  - `withQC_fail` : `E'_iᶜ ∩ Good'(<t(E_i)) = E_iᶜ ∩ Good(<t(E_i))` with the paper's `Good`, so the
    terms of `TableBudget` for `E'` are exactly the failure probabilities of Table 1;
  - `goodAll_withQC` : on `goodAll E'` every `E_i` and every queue constraint holds, provided
    `Good(<t_j) ∩ ⋂_{t(E) = t_j} E ⊆ {Q_j ≤ B(s_j)}` ((D) in the proof of Lemma 6.10).
* `Queue6.tableBudget_sum` : `TableBudget` for the union of two families from per-scale bounds.
-/

@[expose] public section

open MeasureTheory Set Construction

namespace Queue6

section Skeleton

variable {Ω ι κ : Type*}

/-- The queue constraints with time `< t`. -/
def QC (ok : κ → Set Ω) (tq : κ → Ω → ℕ) (t : ℕ) : Set Ω :=
  {ω | ∀ j, tq j ω < t → ω ∈ ok j}

/-- **The good event of Definition 6.8**: the events with time `< t` and the queue constraints
with time `< t`. -/
def paperGood (E : ι → Set Ω) (time : ι → ℕ) (ok : κ → Set Ω) (tq : κ → Ω → ℕ) (t : ℕ) :
    Set Ω :=
  QC ok tq t ∩ goodBefore E time t

/-- The modified events `E'_i := E_i ∪ QC(t(E_i))ᶜ`. -/
def withQC (E : ι → Set Ω) (time : ι → ℕ) (ok : κ → Set Ω) (tq : κ → Ω → ℕ) (i : ι) :
    Set Ω :=
  E i ∪ (QC ok tq (time i))ᶜ

variable (E : ι → Set Ω) (time : ι → ℕ) (ok : κ → Set Ω) (tq : κ → Ω → ℕ)

lemma QC_anti {s t : ℕ} (hst : s ≤ t) : QC ok tq t ⊆ QC ok tq s :=
  fun _ hω j hj => hω j (lt_of_lt_of_le hj hst)

lemma goodBefore_withQC_inter (t : ℕ) :
    goodBefore (withQC E time ok tq) time t ∩ QC ok tq t = paperGood E time ok tq t := by
  ext ω
  simp only [paperGood, goodBefore, withQC, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
  constructor
  · rintro ⟨h, hq⟩
    refine ⟨hq, fun i hi => ?_⟩
    rcases h i hi with h | h
    · exact h
    · exact absurd (QC_anti ok tq hi.le hq) h
  · rintro ⟨hq, h⟩
    exact ⟨fun i hi => Or.inl (h i hi), hq⟩

/-- **The failure terms of `E'` are those of Table 1**: `E'_iᶜ ∩ Good'(<t(E_i))` is
`E_iᶜ ∩ Good(<t(E_i))` with the good event of Definition 6.8. -/
lemma withQC_fail (i : ι) :
    (withQC E time ok tq i)ᶜ ∩ goodBefore (withQC E time ok tq) time (time i) =
      (E i)ᶜ ∩ paperGood E time ok tq (time i) := by
  rw [← goodBefore_withQC_inter]
  ext ω
  simp only [withQC, mem_inter_iff, mem_compl_iff, mem_union, not_or, not_not]
  tauto

/-- **First failure, pathwise** (proof of Lemma 6.10): if every queue constraint holds on
`Good(<t_j) ∩ ⋂_{t(E) = t_j} E` ((D) of the proof of Lemma 6.10; here
`QC(t_j) ∩ goodBefore E (t_j + 1)`), then on `goodAll E'` every
queue constraint and every event `E_i` holds. -/
theorem goodAll_withQC
    (hstep : ∀ j ω, ω ∈ QC ok tq (tq j ω) → ω ∈ goodBefore E time (tq j ω + 1) → ω ∈ ok j)
    {ω : Ω}
    (hω : ω ∈ goodAll (withQC E time ok tq)) :
    (∀ t, ω ∈ QC ok tq t) ∧ ω ∈ goodAll E := by
  have hω' : ∀ i, ω ∈ withQC E time ok tq i := by simpa [goodAll] using hω
  have key : ∀ t, ω ∈ QC ok tq t := by
    intro t
    induction t with
    | zero => intro j hj; omega
    | succ t ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact ih j h
      · apply hstep j ω (by rw [h]; exact ih)
        rw [h]
        simp only [goodBefore, mem_iInter]
        intro i hi
        rcases hω' i with h' | h'
        · exact h'
        · exact absurd (QC_anti ok tq (Nat.lt_succ_iff.mp hi) ih) h'
  refine ⟨key, ?_⟩
  simp only [goodAll, mem_iInter]
  intro i
  rcases hω' i with h | h
  · exact h
  · exact absurd (key _) h

end Skeleton

section Budget

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω}

lemma goodBefore_sum_inl (E : ι → Set Ω) (F : κ → Set Ω) (tE : ι → ℕ) (tF : κ → ℕ) (t : ℕ) :
    goodBefore (Sum.elim E F) (Sum.elim tE tF) t ⊆ goodBefore E tE t := by
  intro ω hω
  simp only [goodBefore, mem_iInter] at hω ⊢
  exact fun i hi => hω (Sum.inl i) hi

lemma goodBefore_sum_inr (E : ι → Set Ω) (F : κ → Set Ω) (tE : ι → ℕ) (tF : κ → ℕ) (t : ℕ) :
    goodBefore (Sum.elim E F) (Sum.elim tE tF) t ⊆ goodBefore F tF t := by
  intro ω hω
  simp only [goodBefore, mem_iInter] at hω ⊢
  exact fun i hi => hω (Sum.inr i) hi

/-- The per-scale failure sum of a family on a good event `Good` (a function of the time). -/
noncomputable def scaleSum (μ : Measure Ω) (E : ι → Set Ω) (time : ι → ℕ) (scale : ι → ℕ)
    (Good : ℕ → Set Ω) (m : ℕ) : ENNReal :=
  ∑' i : {i // scale i = m}, μ ((E i)ᶜ ∩ Good (time i))

lemma tsum_subtype_sum {f : ι ⊕ κ → ENNReal} (s : ι ⊕ κ → ℕ) (m : ℕ) :
    ∑' x : {x // s x = m}, f x =
      ∑' x : {i // s (Sum.inl i) = m}, f (Sum.inl x.1) +
        ∑' x : {i // s (Sum.inr i) = m}, f (Sum.inr x.1) := by
  have e : ∑' x : {x // s x = m}, f x = ∑' x : ι ⊕ κ, {x | s x = m}.indicator f x :=
    (tsum_subtype {x | s x = m} f)
  have e1 := tsum_subtype {i | s (Sum.inl i) = m} (fun i => f (Sum.inl i))
  have e2 := tsum_subtype {i | s (Sum.inr i) = m} (fun i => f (Sum.inr i))
  change ∑' x : {i // s (Sum.inl i) = m}, f (Sum.inl x.1) = _ at e1
  change ∑' x : {i // s (Sum.inr i) = m}, f (Sum.inr x.1) = _ at e2
  rw [e, Summable.tsum_sum ENNReal.summable ENNReal.summable, e1, e2]
  rfl

/-- **`TableBudget` for the union of two families**, from per-scale bounds of each family on
the good event of the union (bounded through any larger good events). -/
theorem tableBudget_sum (μ : Measure Ω) {X₀ : ℝ} (E : ι → Set Ω) (F : κ → Set Ω)
    (tE : ι → ℕ) (tF : κ → ℕ) (sE : ι → ℕ) (sF : κ → ℕ) (bE bF : ℕ → ENNReal)
    (hE : ∀ m, ∑' i : {i // sE i = m},
      μ ((E i)ᶜ ∩ goodBefore (Sum.elim E F) (Sum.elim tE tF) (tE i)) ≤ bE m)
    (hF : ∀ m, ∑' i : {i // sF i = m},
      μ ((F i)ᶜ ∩ goodBefore (Sum.elim E F) (Sum.elim tE tF) (tF i)) ≤ bF m)
    (hsum : ∀ m, bE m + bF m ≤ ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 +
      3.2 / (2 ^ m * X₀) ^ 2)) :
    TableBudget μ X₀ (Sum.elim E F) (Sum.elim tE tF) (Sum.elim sE sF) := by
  intro m
  rw [tsum_subtype_sum (f := fun x => μ ((Sum.elim E F x)ᶜ ∩
    goodBefore (Sum.elim E F) (Sum.elim tE tF) (Sum.elim tE tF x))) (Sum.elim sE sF) m]
  exact (add_le_add (hE m) (hF m)).trans (hsum m)

end Budget

end Queue6

end
