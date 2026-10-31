module

public import RequestProject.Beurling.Construction.LandingCount
public import RequestProject.Beurling.Construction.RealisedLow

/-!
# Counting the elements of the realised system

The elements of the realised system are counted over its primes themselves (`RealisedIdx`): the
rational primes `p < X₀` and the placed primes. Here:

* `realised_N_eq`: `N(x) = 1 + #(primes ≤ x) + #(composites ≤ x)`;
* `realised_primes_eq`: for `x ≥ X₀`, the primes `≤ x` are the rational primes, plus the primes
  placed at relative slots `< k`, minus those of them landing above `x` (`E₋`), plus the primes
  placed later landing at or below `x` (`E₊`);
* `realised_comp_eq`: the composites `≤ x` are the composites `< y` minus those in `(x, y)`.
-/

@[expose] public section

open Set Real CaplLink SlotModel Target Oscillation Absorbed Filter QueueMono Greedy Bookkeeping
  DesignedZero GoodHeights Decomp

namespace Construction

section Counts

variable {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ)

/-- The composite elements of value `≤ x`. -/
def compLe (x : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | 2 ≤ e.sum (fun _ n => n) ∧ idxVal M H U e ≤ x}

/-- The composite elements of value `< x`. -/
def compLt (x : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | 2 ≤ e.sum (fun _ n => n) ∧ idxVal M H U e < x}

/-- The composite elements of value in `(a, b)`. -/
def compIoo (a b : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | 2 ≤ e.sum (fun _ n => n) ∧ a < idxVal M H U e ∧ idxVal M H U e < b}

/-- The relative slots `m < k` at which a prime is placed (the prime of slot `m + 1 ≤ k`). -/
def placedBefore (k : ℕ) : Set ℕ := {m | placedAt M m ∧ m < k}

/-- `E₋`: primes placed at relative slots `≤ k` that land above `x`. -/
def emSet (k : ℕ) (x : ℝ) : Set ℕ := {m | placedAt M m ∧ m < k ∧ x < primeValueOf M H U m}

/-- `E₊`: primes placed at relative slots `> k` that land at or below `x`. -/
def epSet (k : ℕ) (x : ℝ) : Set ℕ := {m | placedAt M m ∧ k ≤ m ∧ primeValueOf M H U m ≤ x}

end Counts

/-- The standing hypotheses: the target of `M` is the paper's target for the realised system, the
arrivals are its composites, and the jitters lie in `[0, 1]`. -/
structure LinkedModel (θ : ℝ) (X₀ : ℕ) (M : SlotModel X₀) (U : ℕ → ℝ) (a : ℕ → ℝ) : Prop where
  hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)
  hX : 10 ^ 8 ≤ Real.log X₀
  hU : ∀ j, U j ∈ Icc (0 : ℝ) 1
  hT : ∀ x, M.T x = target X₀ (kappaParam X₀) (countA (realisedA M (capH X₀) U))
      (absorbedDensityCap (thetaB θ) (realisedA M (capH X₀) U) (fun n => solveU (thetaB θ) n))
      (osc θ (designedAlpha (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (thetaB θ) n) kappa0Param (switchOn X₀) a)
        (designedGamma (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (thetaB θ) n) kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x
  hlink : ArrivalsLinked M (capH X₀) U

section Basic

variable {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}

lemma LinkedModel.hTlow {θ : ℝ} {a : ℕ → ℝ} (L : LinkedModel θ X₀ M U a) :
    ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
  intro x hx
  rw [L.hT x]
  simp only [target, if_pos hx]

/-- The value of an element is the value of its transport to the realised index set. -/
lemma val_eq_idxVal (h : RealisedOK M H U) (e : ℕ →₀ ℕ) :
    (realisedSystem M H U).val e = idxVal M H U (Finsupp.equivMapDomain h.equiv e) := by
  unfold BeurlingSystem.val idxVal
  rw [Finsupp.prod_equivMapDomain]
  refine Finsupp.prod_congr fun j _ => ?_
  rw [realisedSystem_p h]

lemma sum_equivMapDomain_eq (h : RealisedOK M H U) (e : ℕ →₀ ℕ) :
    (Finsupp.equivMapDomain h.equiv e).sum (fun _ n => n) = e.sum (fun _ n => n) := by
  rw [Finsupp.sum_equivMapDomain]

lemma idxVal_le_eq_image (h : RealisedOK M H U) (x : ℝ) :
    {f : RealisedIdx M →₀ ℕ | idxVal M H U f ≤ x} =
      (Finsupp.equivMapDomain h.equiv) '' {e | (realisedSystem M H U).val e ≤ x} := by
  ext f
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro hf
    refine ⟨Finsupp.equivMapDomain h.equiv.symm f, ?_, by simp [← Finsupp.equivMapDomain_trans]⟩
    rw [val_eq_idxVal h]; simpa [← Finsupp.equivMapDomain_trans] using hf
  · rintro ⟨e, he, rfl⟩
    rwa [← val_eq_idxVal h]

/-- The elements of value `≤ x` over the realised index set are finitely many. -/
lemma finite_idxVal_le (h : RealisedOK M H U) (x : ℝ) :
    {f : RealisedIdx M →₀ ℕ | idxVal M H U f ≤ x}.Finite := by
  rw [idxVal_le_eq_image h]
  exact ((realisedSystem M H U).finite_val_le x).image _

lemma idxVal_zero : idxVal M H U 0 = 1 := by simp [idxVal]

lemma idxVal_single (i : RealisedIdx M) :
    idxVal M H U (Finsupp.single i 1) = realisedVal M H U i := by
  simp [idxVal, Finsupp.prod_single_index]

lemma toMultiset_inj {α : Type*} : Function.Injective (Finsupp.toMultiset (α := α)) := by
  classical
  exact Function.LeftInverse.injective (g := Multiset.toFinsupp) Finsupp.toMultiset_toFinsupp

lemma equivMapDomain_inj {α β : Type*} (e : α ≃ β) :
    Function.Injective (Finsupp.equivMapDomain e (M := ℕ)) := fun a b hab => by
  simpa [← Finsupp.equivMapDomain_trans] using congrArg (Finsupp.equivMapDomain e.symm) hab

lemma finsupp_sum_eq_one_iff {α : Type*} (f : α →₀ ℕ) :
    f.sum (fun _ n => n) = 1 ↔ ∃ i, f = Finsupp.single i 1 := by
  constructor
  · intro h1
    have hc : Multiset.card (Finsupp.toMultiset f) = 1 := by
      rw [Finsupp.card_toMultiset]; exact h1
    obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hc
    refine ⟨i, ?_⟩
    apply toMultiset_inj
    rw [hi, Finsupp.toMultiset_single, one_nsmul]
  · rintro ⟨i, rfl⟩
    simp

lemma finsupp_sum_eq_zero_iff {α : Type*} (f : α →₀ ℕ) :
    f.sum (fun _ n => n) = 0 ↔ f = 0 := by
  constructor
  · intro h0
    have hc : Multiset.card (Finsupp.toMultiset f) = 0 := by
      rw [Finsupp.card_toMultiset]; exact h0
    rw [Multiset.card_eq_zero] at hc
    exact toMultiset_inj (by simpa using hc)
  · rintro rfl
    simp

/-- **`N(x) = 1 + #(primes ≤ x) + #(composites ≤ x)`.** -/
theorem realised_N_eq (h : RealisedOK M H U) {x : ℝ} (hx : 1 ≤ x) :
    (realisedSystem M H U).N x =
      1 + ({i | realisedVal M H U i ≤ x}.ncard : ℝ) + ((compLe M H U x).ncard : ℝ) := by
  classical
  set S := {f : RealisedIdx M →₀ ℕ | idxVal M H U f ≤ x}
  have hSfin := finite_idxVal_le h x
  have hN : (realisedSystem M H U).N x = (S.ncard : ℝ) := by
    unfold BeurlingSystem.N
    rw [show S = _ from idxVal_le_eq_image h x, Set.ncard_image_of_injective _ (equivMapDomain_inj _)]
  set T1 := (fun i => Finsupp.single i 1) '' {i | realisedVal M H U i ≤ x}
  have hdecomp : S = ({0} ∪ T1) ∪ compLe M H U x := by
    ext f
    simp only [S, T1, compLe, mem_setOf_eq, mem_union, mem_singleton_iff, mem_image]
    constructor
    · intro hf
      rcases Nat.lt_or_ge (f.sum fun _ n => n) 2 with h2 | h2
      · interval_cases hs : (f.sum fun _ n => n)
        · exact Or.inl (Or.inl ((finsupp_sum_eq_zero_iff f).mp hs))
        · obtain ⟨i, rfl⟩ := (finsupp_sum_eq_one_iff f).mp hs
          refine Or.inl (Or.inr ⟨i, ?_, rfl⟩)
          rwa [idxVal_single] at hf
      · exact Or.inr ⟨h2, hf⟩
    · rintro ((rfl | ⟨i, hi, rfl⟩) | ⟨-, hf⟩)
      · rw [idxVal_zero]; exact hx
      · rw [idxVal_single]; exact hi
      · exact hf
  have hT1 : T1.ncard = {i | realisedVal M H U i ≤ x}.ncard :=
    Set.ncard_image_of_injective _ (Finsupp.single_left_injective one_ne_zero)
  have hd1 : Disjoint ({0} : Set (RealisedIdx M →₀ ℕ)) T1 := by
    rw [Set.disjoint_left]
    rintro f rfl ⟨i, -, hi⟩
    exact Finsupp.single_ne_zero.mpr one_ne_zero hi
  have hd2 : Disjoint ({0} ∪ T1) (compLe M H U x) := by
    rw [Set.disjoint_left]
    rintro f (rfl | ⟨i, -, rfl⟩) ⟨h2, -⟩
    · simp at h2
    · simp at h2
  have hsub1 : ({0} ∪ T1) ⊆ S := by rw [hdecomp]; exact subset_union_left
  have hsub2 : compLe M H U x ⊆ S := by rw [hdecomp]; exact subset_union_right
  have hsub0 : T1 ⊆ S := subset_union_right.trans hsub1
  rw [hN, hdecomp, Set.ncard_union_eq hd2 (hSfin.subset hsub1) (hSfin.subset hsub2),
    Set.ncard_union_eq hd1 (Set.finite_singleton 0) (hSfin.subset hsub0), Set.ncard_singleton, hT1]
  push_cast
  ring

end Basic

end Construction

end
