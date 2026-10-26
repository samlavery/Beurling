module

public import RequestProject.Beurling.Model.Fix

/-!
# The prime data of a slot model and its realised system

For a slot model `M` with jitter width `H = capH X₀` and jitters `U`, the elements of the realised
system (exponent vectors over `RealisedIdx M`, `Construction/Realised.lean`) are the elements of
the prime data `DM M U` over the fixed index set `PIdx X₀`, via the embedding
`RealisedIdx M ↪ PIdx X₀` (`toPIdx`). Hence (`RealisedOK`):

* `ncard_compositeSet` : the composites in `[a, b)` are counted by `compCount`;
* `realisedSystem_N` : `N_{P(ω)} = NCount (DM M U)`;
* `realisedA_eq` : the realised absorbed set (5) is `absSet (DM M U)` when no rational prime
  `p < X₀` is a value of a placed prime (off the null event `𝒩₌` of §3.4; with ties, the latest
  prime of a product of rational primes depends on a choice);
* `realised_T_eq` : the target of the data is the paper's target for the realised system.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono

namespace BModel

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- The embedding of the realised primes into the fixed index set. -/
def toPIdx (M : SlotModel X₀) : RealisedIdx M → PIdx X₀
  | Sum.inl p => Sum.inl p
  | Sum.inr k => Sum.inr k.1

lemma toPIdx_injective (M : SlotModel X₀) : Function.Injective (toPIdx M) := by
  rintro (p | k) (q | l) h <;> simp_all [toPIdx, Subtype.ext_iff]

lemma pval_toPIdx (M : SlotModel X₀) (U : ℕ → ℝ) (i : RealisedIdx M) :
    pval (X₀ := X₀) (DM M U) (toPIdx M i) = realisedVal M (capH X₀) U i := by
  cases i <;> rfl

/-- The transport of an exponent vector. -/
noncomputable def mapE (M : SlotModel X₀) (e : RealisedIdx M →₀ ℕ) : PIdx X₀ →₀ ℕ :=
  Finsupp.mapDomain (toPIdx M) e

lemma mapE_injective (M : SlotModel X₀) : Function.Injective (mapE M) :=
  Finsupp.mapDomain_injective (toPIdx_injective M)

lemma eval_mapE (M : SlotModel X₀) (U : ℕ → ℝ) (e : RealisedIdx M →₀ ℕ) :
    eval (DM M U) (mapE M e) = idxVal M (capH X₀) U e := by
  unfold eval mapE idxVal
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  refine Finsupp.prod_congr fun i _ => ?_
  rw [pval_toPIdx]

lemma sum_mapE (M : SlotModel X₀) (e : RealisedIdx M →₀ ℕ) :
    (mapE M e).sum (fun _ n => n) = e.sum (fun _ n => n) := by
  unfold mapE
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

open Classical in
lemma mapE_apply_inr (M : SlotModel X₀) (e : RealisedIdx M →₀ ℕ) (k : ℕ) :
    mapE M e (Sum.inr k) = if hk : placedAt M k then e (Sum.inr ⟨k, hk⟩) else 0 := by
  classical
  unfold mapE
  split_ifs with hk
  · have : Sum.inr k = toPIdx M (Sum.inr ⟨k, hk⟩) := rfl
    rw [this, Finsupp.mapDomain_apply (toPIdx_injective M)]
  · rw [Finsupp.mapDomain_notin_range]
    rintro ⟨i, hi⟩
    cases i with
    | inl p => simp [toPIdx] at hi
    | inr l =>
      simp only [toPIdx, Sum.inr.injEq] at hi
      exact hk (hi ▸ l.2)

lemma live_mapE (M : SlotModel X₀) (U : ℕ → ℝ) (e : RealisedIdx M →₀ ℕ) :
    Live (DM M U) (mapE M e) := by
  intro k hk
  rw [mapE_apply_inr] at hk
  split_ifs at hk with h
  · exact h
  · exact absurd rfl hk

/-- Every live exponent vector is a transport. -/
lemma exists_mapE {e : PIdx X₀ →₀ ℕ} (he : Live (DM M U) e) : ∃ f, mapE M f = e := by
  classical
  refine ⟨Finsupp.comapDomain (toPIdx M) e (toPIdx_injective M).injOn, ?_⟩
  unfold mapE
  apply Finsupp.mapDomain_comapDomain _ (toPIdx_injective M)
  intro i hi
  cases i with
  | inl p => exact ⟨Sum.inl p, rfl⟩
  | inr k =>
    have hk : placedAt M k := he k (Finsupp.mem_support_iff.mp hi)
    exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩

lemma image_mapE_eq {S : Set (RealisedIdx M →₀ ℕ)} {T : Set (PIdx X₀ →₀ ℕ)}
    (hST : ∀ f, f ∈ S ↔ mapE M f ∈ T) (hT : ∀ e ∈ T, Live (DM M U) e) :
    mapE M '' S = T := by
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩; exact (hST f).mp hf
  · intro he
    obtain ⟨f, rfl⟩ := exists_mapE (U := U) (hT e he)
    exact ⟨f, (hST f).mpr he, rfl⟩

lemma ncard_eq_of_mapE {S : Set (RealisedIdx M →₀ ℕ)} {T : Set (PIdx X₀ →₀ ℕ)}
    (hST : ∀ f, f ∈ S ↔ mapE M f ∈ T) (hT : ∀ e ∈ T, Live (DM M U) e) :
    S.ncard = T.ncard := by
  rw [← image_mapE_eq (U := U) hST hT, Set.ncard_image_of_injective _ (mapE_injective M)]

/-- **The composites in `[a, b)` are counted by `compCount`.** -/
theorem ncard_compositeSet (M : SlotModel X₀) (U : ℕ → ℝ) (a b : ℝ) :
    (compositeSet M (capH X₀) U a b).ncard = (compSet X₀ (DM M U) a b).ncard := by
  refine ncard_eq_of_mapE (U := U) (fun f => ?_) (fun e he => he.1)
  simp only [compositeSet, compSet, mem_setOf_eq, eval_mapE, sum_mapE]
  exact ⟨fun h => ⟨live_mapE M U f, h⟩, fun h => h.2⟩

/-- The elements of value `≤ x`. -/
theorem ncard_idxVal_le (M : SlotModel X₀) (U : ℕ → ℝ) (x : ℝ) :
    {f : RealisedIdx M →₀ ℕ | idxVal M (capH X₀) U f ≤ x}.ncard =
      (elemsLe X₀ (DM M U) x).ncard := by
  refine ncard_eq_of_mapE (U := U) (fun f => ?_) (fun e he => he.1)
  simp only [elemsLe, mem_setOf_eq, eval_mapE]
  exact ⟨fun h => ⟨live_mapE M U f, h⟩, fun h => h.2⟩

/-- **`N` of the realised system is `NCount` of the prime data.** -/
theorem realisedSystem_N (h : RealisedOK M (capH X₀) U) :
    (realisedSystem M (capH X₀) U).N = NCount X₀ (DM M U) := by
  funext x
  unfold BeurlingSystem.N NCount
  rw [← ncard_idxVal_le, idxVal_le_eq_image h,
    Set.ncard_image_of_injective _ (equivMapDomain_inj _)]

/-! ### The absorbed set -/

/-- **No coincidence**: no placed prime has the value of a rational prime `p < X₀` (off the null
event `𝒩₌` of §3.4). -/
def NoCoincidence (M : SlotModel X₀) (U : ℕ → ℝ) : Prop :=
  ∀ k, placedAt M k → ∀ p : ℕ, p.Prime → p < X₀ → primeValueOf M (capH X₀) U k ≠ p

lemma keyOf_inl (h : RealisedOK M (capH X₀) U) {j : ℕ} {p : {p : ℕ // p.Prime ∧ p < X₀}}
    (hj : h.equiv j = Sum.inl p) : keyOf (realisedSrc M (capH X₀) U) j = 0 := by
  unfold keyOf
  rw [realisedSrc_eq h, hj]; rfl

lemma keyOf_inr (h : RealisedOK M (capH X₀) U) {j : ℕ} {k : {k : ℕ // placedAt M k}}
    (hj : h.equiv j = Sum.inr k) : keyOf (realisedSrc M (capH X₀) U) j = k.1 + 1 := by
  unfold keyOf
  rw [realisedSrc_eq h, hj]; rfl

/-- **The realised absorbed set (5) is the absorbed set of the prime data.** -/
theorem realisedA_eq (h : RealisedOK M (capH X₀) U) (hnc : NoCoincidence M U) :
    realisedA M (capH X₀) U = absSet X₀ (DM M U) := by
  classical
  set P := realisedSystem M (capH X₀) U
  set src := realisedSrc M (capH X₀) U
  ext n
  constructor
  · rintro ⟨hlog, e, hval, hjit, hy⟩
    by_cases hne : e.support.Nonempty
    · have hlat : latestIdxOf src e = (e.support.exists_max_image (keyOf src) hne).choose := by
        unfold latestIdxOf; rw [dif_pos hne]
      obtain ⟨hjs, hjmax⟩ := (e.support.exists_max_image (keyOf src) hne).choose_spec
      rw [← hlat] at hjs hjmax
      set j := latestIdxOf src e
      have hpj : P.p j = realisedVal M (capH X₀) U (h.equiv j) := realisedSystem_p h j
      -- the latest prime is jittered
      obtain ⟨⟨k, hk⟩, hjk⟩ : ∃ k : {k // placedAt M k}, h.equiv j = Sum.inr k := by
        rcases hq : h.equiv j with p | k
        · exfalso
          rw [hpj, hq] at hjit
          obtain ⟨k, hk, hkv⟩ := hjit
          exact hnc k hk p.1 p.2.1 p.2.2 hkv.symm
        · exact ⟨k, rfl⟩
      set f := Finsupp.equivMapDomain h.equiv e
      refine ⟨hlog, mapE M f, live_mapE M U f, ?_, k, ?_, fun k' hk' => ?_, ?_⟩
      · rw [eval_mapE, ← val_eq_idxVal h]; exact hval
      · rw [mapE_apply_inr, dif_pos hk]
        show e (h.equiv.symm _) ≠ 0
        rw [← hjk, Equiv.symm_apply_apply]
        exact Finsupp.mem_support_iff.mp hjs
      · rw [mapE_apply_inr] at hk'
        split_ifs at hk' with hpl
        · have hmem : h.equiv.symm (Sum.inr ⟨k', hpl⟩) ∈ e.support :=
            Finsupp.mem_support_iff.mpr hk'
          have := hjmax _ hmem
          rw [keyOf_inr h (Equiv.apply_symm_apply _ _), keyOf_inr h hjk] at this
          dsimp only at this
          omega
        · exact absurd rfl hk'
      · show primeValueOf M (capH X₀) U k < absorbY X₀ n
        rw [hpj, hjk] at hy
        exact hy
    · exfalso
      have he0 : e = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hne; exact hne
      rw [he0] at hval
      simp only [BeurlingSystem.val, Finsupp.prod_zero_index] at hval
      have : (n : ℝ) = 1 := hval.symm
      rw [this, Real.log_one] at hlog
      norm_num at hlog
  · rintro ⟨hlog, e', he', hval, k, hk, hmax, hy⟩
    obtain ⟨f, rfl⟩ := exists_mapE (U := U) he'
    have hkp : placedAt M k := he' k hk
    set e := Finsupp.equivMapDomain h.equiv.symm f
    have hfe : Finsupp.equivMapDomain h.equiv e = f := by
      simp [e, ← Finsupp.equivMapDomain_trans]
    have hj0 : h.equiv.symm (Sum.inr ⟨k, hkp⟩) ∈ e.support := by
      rw [Finsupp.mem_support_iff]
      show f (h.equiv (h.equiv.symm _)) ≠ 0
      rw [Equiv.apply_symm_apply]
      rw [mapE_apply_inr, dif_pos hkp] at hk
      exact hk
    have hne : e.support.Nonempty := ⟨_, hj0⟩
    have hlat : latestIdxOf src e = (e.support.exists_max_image (keyOf src) hne).choose := by
      unfold latestIdxOf; rw [dif_pos hne]
    obtain ⟨hjs, hjmax⟩ := (e.support.exists_max_image (keyOf src) hne).choose_spec
    rw [← hlat] at hjs hjmax
    set j := latestIdxOf src e
    have hkey := hjmax _ hj0
    rw [keyOf_inr h (Equiv.apply_symm_apply _ _)] at hkey
    -- the chosen latest prime is the prime of slot `k`
    have hjk : h.equiv j = Sum.inr ⟨k, hkp⟩ := by
      have hjf : f (h.equiv j) ≠ 0 := by
        have := Finsupp.mem_support_iff.mp hjs
        simpa [e] using this
      rcases hq : h.equiv j with p | ⟨k', hk'⟩
      · rw [keyOf_inl h hq] at hkey; omega
      · rw [keyOf_inr h hq] at hkey
        dsimp only at hkey
        have hk'f : mapE M f (Sum.inr k') ≠ 0 := by
          rw [mapE_apply_inr, dif_pos hk']; rw [hq] at hjf; exact hjf
        have := hmax k' hk'f
        have hkk : k' = k := by omega
        subst hkk; rfl
    have hpj : P.p j = primeValueOf M (capH X₀) U k := by
      rw [realisedSystem_p h, hjk]; rfl
    refine ⟨hlog, e, ?_, ?_, ?_⟩
    · rw [val_eq_idxVal h, hfe, ← eval_mapE]; exact hval
    · rw [hpj]; exact ⟨k, hkp, rfl⟩
    · rw [hpj]; exact hy

/-! ### The constructed model -/

section Constructed

variable {θ : ℝ} (h : Std θ X₀ U)
include h

/-- **The arrivals of the constructed model are the composites of its realised system** (§3.4:
`A_j` is the number of composite elements with value in `J_j`). -/
theorem limModel_linked : ArrivalsLinked h.limModel (capH X₀) U := by
  intro k
  rw [h.limModel_arr k]
  unfold compositeArr compCount
  rw [ncard_compositeSet]

/-- **The greedy rule places infinitely many primes** in the constructed model. -/
theorem limModel_placed_infinite : {k | placedAt h.limModel k}.Infinite :=
  placed_infinite_of_growth h.hU h.hX h.limModel_low
    (fun x hx => by
      rw [h.limModel_T_eq x]; exact targetD_ge_linear (by linarith [h.hθ.2]) h.hX _ hx)
    (limModel_linked h)

/-- **The realised system of the constructed model is a Beurling system.** -/
theorem limModel_realisedOK : RealisedOK h.limModel (capH X₀) U :=
  realisedOK_of h.limModel h.hU h.hX h.limModel_low (limModel_placed_infinite h)

/-- **The target of the constructed model is the paper's target (6) for its realised system**
(the first conjunct of `PartIRestO`), off the null event `𝒩₌` (`NoCoincidence`). -/
theorem limModel_T_formula (hnc : NoCoincidence h.limModel U) (x : ℝ) :
    h.limModel.T x = target X₀ (kappaParam X₀)
      (countA (realisedA h.limModel (capH X₀) U))
      (absorbedDensityCap (θ / 2) (realisedA h.limModel (capH X₀) U) (fun n => solveU (θ / 2) n))
      (osc θ (designedAlpha (realisedSystem h.limModel (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA h.limModel (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param
          (switchOn X₀) (constructionScale X₀))
        (designedGamma (realisedSystem h.limModel (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA h.limModel (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param
          (switchOn X₀) (constructionScale X₀))
        (switchOn X₀)) x := by
  have hok := limModel_realisedOK h
  rw [h.limModel_T_eq x, realisedA_eq hok hnc]
  unfold designedAlpha
  rw [designedGamma_eq_N, realisedSystem_N hok]
  rfl

end Constructed

end BModel

end
