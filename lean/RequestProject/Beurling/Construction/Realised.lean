module

public import RequestProject.Beurling.Construction.Top

/-!
# The realised system, the absorbed set, `u_a` and the latest-prime map built from the jitters

In `Theorem21InputsSp` the system `P(ω)`, the origin of its primes, the absorbed set `A`, the
weights `u_a` and the latest-prime map were supplied as data, related by `AbsorbedCoupling`.
Here they are **constructed** from the slot model `M`, the jitter width `H` and the jitters `U`:

* `realisedSystem M H U`: the Beurling system whose primes are the rational primes `p < X₀`
  together with the primes placed by the greedy rule, the prime decided at relative slot `k + 1`
  landing at `s + H(s)(U_{k+1} - 1/2)` (`primeValueOf`), listed in non-decreasing order
  (`exists_mono_equiv_nat`);
* `realisedSrc M H U`: the origin of each prime (rational, or the slot at which it was decided);
* `realisedA`: the absorbed set (5), `A = {n : log n ≥ L*, n is the value of an element whose
  latest prime (in the decision order) is jittered and below y(n)}`;
* `realisedLatest`: the latest prime of a chosen such element;
* `solveU b n`: the solution `u ≥ 0` of `u + u^b = n`.

`realisedOK_of`: for `H = max(H_std, M̄₁²)`, jitters in `[0, 1]`, the target `⌊x⌋` below `X₀`
and infinitely many slots placing a prime, the placed primes together with the rational primes form
a Beurling system (values `> 1`, finitely many below any bound). `realisedCoupling` gives the
`AbsorbedCoupling` for the realised data, and `realisedU_spec` proves `X₀ ≤ u_a`,
`u_a + u_a^{θ/2} = a` for every `a ∈ A`.

`Theorem21InputsJ` is `Theorem21InputsSp` with `P(ω)`, `A`, `u_a`, the latest-prime map and the
coupling no longer supplied (they are the constructed ones), and with the conditions
`X₀ ≤ u_a`, `u_a + u_a^{θ/2} = a` removed (proved). It adds the condition that the greedy rule
places infinitely many primes (needed for the realised primes to tend to infinity).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex Metric Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize CaplLink
  QueueBound LagSplit SlotModel Decomp QueueMono Bookkeeping

namespace Construction

/-- **Listing a locally finite family in non-decreasing order**: a countably infinite family of
reals with finitely many members below any bound can be enumerated by `ℕ` in non-decreasing
order. -/
theorem exists_mono_equiv_nat {I : Type*} [Countable I] [Infinite I] (f : I → ℝ)
    (hf : ∀ b, {i | f i ≤ b}.Finite) : ∃ e : ℕ ≃ I, Monotone (f ∘ e) := by
  classical
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat I
  let key : I → ℝ ×ₗ ℕ := fun i => toLex (f i, enc i)
  have hkey : Function.Injective key := by
    intro i j h
    exact henc (congrArg (fun p => (ofLex p).2) h)
  letI : LinearOrder I := LinearOrder.lift' key hkey
  have hle : ∀ i j : I, i ≤ j ↔ key i ≤ key j := fun _ _ => Iff.rfl
  have hfle : ∀ i j : I, i ≤ j → f i ≤ f j := by
    intro i j h
    rw [hle] at h
    rcases (Prod.Lex.le_iff).mp h with h | h
    · exact h.le
    · exact h.1.le
  have hIic : ∀ a : I, (Set.Iic a).Finite := fun a =>
    (hf (f a)).subset (fun j hj => hfle j a hj)
  letI : LocallyFiniteOrder I := LocallyFiniteOrder.ofIcc I
    (fun a b => (hIic b).toFinset.filter (fun x => a ≤ x))
    (fun a b x => by simp [and_comm])
  letI : SuccOrder I := LinearLocallyFiniteOrder.succOrder I
  letI : PredOrder I := LinearLocallyFiniteOrder.predOrder I
  haveI : NoMaxOrder I := ⟨fun a => by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (hIic a |>.subset fun x _ => h x)⟩
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  have hne : (hIic i0).toFinset.Nonempty := ⟨i0, by simp⟩
  letI : OrderBot I :=
    { bot := (hIic i0).toFinset.min' hne
      bot_le := fun x => by
        rcases le_total x i0 with h | h
        · exact Finset.min'_le _ _ (by simpa using h)
        · exact (Finset.min'_le _ _ (by simp)).trans h }
  let o : I ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  exact ⟨o.symm.toEquiv, fun n m hnm => hfle _ _ (o.symm.monotone hnm)⟩

section Realised

variable {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ)

/-- The realised primes, indexed: the rational primes `p < X₀`, and the relative slots `k` at which
the greedy rule places a prime. -/
abbrev RealisedIdx : Type := {p : ℕ // p.Prime ∧ p < X₀} ⊕ {k : ℕ // placedAt M k}

/-- The value of a realised prime: `p` for a rational prime, `primeValueOf M H U k` for the prime
decided at relative slot `k + 1`. -/
noncomputable def realisedVal : RealisedIdx M → ℝ
  | Sum.inl p => (p.1 : ℝ)
  | Sum.inr k => primeValueOf M H U k.1

/-- The realised primes form a Beurling system: every value is `> 1`, there are finitely many
below any bound, and infinitely many in all. -/
structure RealisedOK : Prop where
  one_lt : ∀ i, 1 < realisedVal M H U i
  finite_le : ∀ b, {i | realisedVal M H U i ≤ b}.Finite
  infinite : Infinite (RealisedIdx M)

variable {M H U}

/-- The enumeration of the realised primes in non-decreasing order. -/
noncomputable def RealisedOK.equiv (h : RealisedOK M H U) : ℕ ≃ RealisedIdx M :=
  haveI := h.infinite
  (exists_mono_equiv_nat (realisedVal M H U) h.finite_le).choose

lemma RealisedOK.equiv_mono (h : RealisedOK M H U) : Monotone (realisedVal M H U ∘ h.equiv) := by
  haveI := h.infinite
  exact (exists_mono_equiv_nat (realisedVal M H U) h.finite_le).choose_spec

/-- The realised system (under `RealisedOK`). -/
noncomputable def RealisedOK.system (h : RealisedOK M H U) : BeurlingSystem where
  p := realisedVal M H U ∘ h.equiv
  one_lt _ := h.one_lt _
  mono := h.equiv_mono
  tendsto := by
    rw [Filter.tendsto_atTop]
    intro b
    have hfin : {n : ℕ | realisedVal M H U (h.equiv n) < b}.Finite :=
      ((h.finite_le b).preimage h.equiv.injective.injOn).subset (fun n hn => by
        simp only [mem_preimage, mem_setOf_eq] at hn ⊢
        exact hn.le)
    obtain ⟨N, hN⟩ := hfin.bddAbove
    rw [Filter.eventually_atTop]
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := hN hlt
    omega

/-- A fixed Beurling system (`p_j = j + 2`), used only when `RealisedOK` fails. -/
noncomputable def defaultSystem : BeurlingSystem where
  p j := j + 2
  one_lt j := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  mono a b h := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only
    linarith
  tendsto := Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop

variable (M H U)

open Classical in
/-- **The realised system `P(ω)`**: the rational primes `< X₀` together with the primes placed by
the greedy rule with jitter width `H` and jitters `U`, in non-decreasing order. -/
noncomputable def realisedSystem : BeurlingSystem :=
  if h : RealisedOK M H U then h.system else defaultSystem

/-- The origin of a realised prime: `none` for a rational prime, `some k` for the prime decided at
relative slot `k + 1`. -/
def srcOfIdx : RealisedIdx M → Option ℕ
  | Sum.inl _ => none
  | Sum.inr k => some k.1

open Classical in
/-- **The origin of the primes of the realised system.** -/
noncomputable def realisedSrc (j : ℕ) : Option ℕ :=
  if h : RealisedOK M H U then srcOfIdx M (h.equiv j) else none

variable {M H U}

lemma realisedSrc_eq (h : RealisedOK M H U) (j : ℕ) :
    realisedSrc M H U j = srcOfIdx M (h.equiv j) := by
  simp only [realisedSrc, dif_pos h]

lemma realisedSystem_p (h : RealisedOK M H U) (j : ℕ) :
    (realisedSystem M H U).p j = realisedVal M H U (h.equiv j) := by
  simp only [realisedSystem, dif_pos h]
  rfl

/-- The realised system with its origin data. -/
noncomputable def realisedOrigin (h : RealisedOK M H U) :
    PrimeOrigin (realisedSystem M H U) M H U where
  src := realisedSrc M H U
  rational_lt j hj := by
    rw [realisedSrc_eq h] at hj
    rw [realisedSystem_p h]
    generalize h.equiv j = i at hj ⊢
    cases i with
    | inl p =>
      show ((p.1 : ℕ) : ℝ) < X₀
      exact_mod_cast p.2.2
    | inr k => simp [srcOfIdx] at hj
  jittered_eq j k hj := by
    rw [realisedSrc_eq h] at hj
    rw [realisedSystem_p h]
    generalize h.equiv j = i at hj ⊢
    cases i with
    | inl p => simp [srcOfIdx] at hj
    | inr k' =>
      simp only [srcOfIdx, Option.some.injEq] at hj
      subst hj
      exact ⟨k'.2, rfl⟩

end Realised

/-! ### The latest prime and the absorbed set (5) -/

/-- The decision key of a prime with origin `src` (rational first, then slot order). -/
def keyOf (src : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  match src j with
  | none => 0
  | some k => k + 1

/-- The index of the latest prime of `e` in the decision order given by `src`. -/
noncomputable def latestIdxOf (src : ℕ → Option ℕ) (e : ℕ →₀ ℕ) : ℕ :=
  if h : e.support.Nonempty then (e.support.exists_max_image (keyOf src) h).choose else 0

lemma PrimeOrigin.latestPrime_eq {P : BeurlingSystem} {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ}
    {U : ℕ → ℝ} (O : PrimeOrigin P M H U) (e : ℕ →₀ ℕ) :
    O.latestPrime e = P.p (latestIdxOf O.src e) := rfl

/-- **The absorbed set (5)** of a system `P` with prime origins `src`: the real values `n` with
`log n ≥ L* = 10⁷` of the elements `e` of the semigroup (with any cofactor) whose latest prime is
jittered (in `jit`) and below `y(n)`. -/
def absorbedSetOf (P : BeurlingSystem) (src : ℕ → Option ℕ) (X₀ : ℕ) (jit : Set ℝ) : Set ℝ :=
  {n | 10 ^ 7 ≤ Real.log n ∧ ∃ e : ℕ →₀ ℕ, P.val e = n ∧ P.p (latestIdxOf src e) ∈ jit ∧
    P.p (latestIdxOf src e) < absorbY X₀ n}

open Classical in
/-- **The latest-prime map** of the absorbed set: the latest prime of a chosen element witnessing
`n ∈ A`. -/
noncomputable def latestOf (P : BeurlingSystem) (src : ℕ → Option ℕ) (X₀ : ℕ) (jit : Set ℝ)
    (n : ℝ) : ℝ :=
  if h : ∃ e : ℕ →₀ ℕ, P.val e = n ∧ P.p (latestIdxOf src e) ∈ jit ∧
      P.p (latestIdxOf src e) < absorbY X₀ n then P.p (latestIdxOf src h.choose) else 0

/-- **The coupling for the canonical absorbed set**: given the origin of the primes, the absorbed
set (5) and its latest-prime map satisfy `AbsorbedCoupling`. -/
def absorbedCouplingOf {P : BeurlingSystem} {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ}
    {U : ℕ → ℝ} (O : PrimeOrigin P M H U) :
    AbsorbedCoupling P M H U (absorbedSetOf P O.src X₀ (jitteredPrimesOf M H U))
      (latestOf P O.src X₀ (jitteredPrimesOf M H U)) where
  origin := O
  rule := by
    rintro n ⟨hlog, hex⟩
    have h := hex.choose_spec
    refine ⟨hlog, ?_, ?_⟩
    · simp only [latestOf, dif_pos hex]
      exact h.2.1
    · simp only [latestOf, dif_pos hex]
      exact h.2.2
  rep := by
    rintro n ⟨-, hex⟩
    refine ⟨hex.choose, hex.choose_spec.1, ?_⟩
    simp only [latestOf, dif_pos hex]
    rfl

section Realised

variable {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ)

/-- **The realised absorbed set `A`** (5), for the realised system and its prime origins. -/
noncomputable def realisedA : Set ℝ :=
  absorbedSetOf (realisedSystem M H U) (realisedSrc M H U) X₀ (jitteredPrimesOf M H U)

/-- **The realised absorbed set is locally finite**: its members are values of elements, and there
are finitely many elements of value below any bound. -/
lemma realisedA_locFin : LocFin (realisedA M H U) := fun x =>
  (((realisedSystem M H U).finite_val_le x).image (realisedSystem M H U).val).subset
    fun n hn => by
      obtain ⟨-, e, hev, -⟩ := hn.1
      exact ⟨e, by rw [Set.mem_setOf_eq, hev]; exact hn.2, hev⟩

/-- **The realised latest-prime map.** -/
noncomputable def realisedLatest : ℝ → ℝ :=
  latestOf (realisedSystem M H U) (realisedSrc M H U) X₀ (jitteredPrimesOf M H U)

variable {M H U}

/-- The coupling of the realised absorbed set with the realised system. -/
noncomputable def realisedCoupling (h : RealisedOK M H U) :
    AbsorbedCoupling (realisedSystem M H U) M H U (realisedA M H U) (realisedLatest M H U) :=
  absorbedCouplingOf (realisedOrigin h)

end Realised

/-! ### `u_a` -/

open Classical in
/-- The solution `u ≥ 0` of `u + u^b = n` (`0` if there is none), for a real value `n`. -/
noncomputable def solveU (b : ℝ) (n : ℝ) : ℝ :=
  if h : ∃ u : ℝ, 0 ≤ u ∧ u + u ^ b = n then h.choose else 0

lemma solveU_nonneg (b n : ℝ) : 0 ≤ solveU b n := by
  unfold solveU
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

lemma solveU_spec {b : ℝ} (hb : 0 < b) {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ solveU b n ∧ solveU b n + solveU b n ^ b = n := by
  have hex : ∃ u : ℝ, 0 ≤ u ∧ u + u ^ b = n := by
    have hc : ContinuousOn (fun u : ℝ => u + u ^ b) (Icc 0 n) :=
      (continuousOn_id.add (continuousOn_id.rpow_const fun _ _ => Or.inr hb.le))
    have hivt := intermediate_value_Icc hn hc
    have hmem : n ∈ Icc ((fun u : ℝ => u + u ^ b) 0) ((fun u : ℝ => u + u ^ b) n) := by
      simp only [Real.zero_rpow hb.ne', add_zero]
      exact ⟨hn, by linarith [Real.rpow_nonneg hn b]⟩
    obtain ⟨u, hu, hu'⟩ := hivt hmem
    exact ⟨u, hu.1, hu'⟩
  unfold solveU
  rw [dif_pos hex]
  exact hex.choose_spec

lemma le_solveU {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) {X : ℝ} (hX : 1 ≤ X) {n : ℝ}
    (hn : 2 * X < n) : X ≤ solveU b n := by
  obtain ⟨h0, heq⟩ := solveU_spec hb0 (show 0 ≤ n by linarith)
  by_contra hlt
  push_neg at hlt
  have h1 : solveU b n ^ b ≤ X ^ b := Real.rpow_le_rpow h0 hlt.le hb0.le
  have h2 : X ^ b ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hb1
  rw [Real.rpow_one] at h2
  linarith

/-! ### The realised system is a Beurling system -/

/-- For `H = max(H_std, M̄₁²)` and jitters in `[0, 1]`, the prime decided at relative slot
`k + 1` is at least `7/8` of its slot start, which is `≥ X₀`. -/
lemma primeValueOf_ge {X₀ : ℕ} (M : SlotModel X₀) {U : ℕ → ℝ} (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (k : ℕ) :
    (X₀ : ℝ) ≤ M.slot (k + 1) ∧ 7 / 8 * M.slot (k + 1) ≤ primeValueOf M (capH X₀) U k := by
  have hs : (X₀ : ℝ) ≤ M.slot (k + 1) := GreedyRun.slot_ge ⟨M, capH X₀, U, hTlow⟩ (k + 1)
  refine ⟨hs, ?_⟩
  have h1 := (landing_mem_box (s := M.slot (k + 1)) (capH_nonneg X₀ (M.slot (k + 1)))
    (hU (k + 1))).1
  have h4 := four_capH_le (Nat.cast_nonneg _) hX hs
  unfold primeValueOf
  linarith

/-- The relative slots whose start is below a bound are finitely many. -/
lemma finite_slot_le {X₀ : ℕ} (M : SlotModel X₀) (hX : 1 ≤ X₀) (c : ℝ) :
    {k : ℕ | M.slot (k + 1) ≤ c}.Finite := by
  refine (Set.finite_Iic ⌈M.T c⌉₊).subset fun k hk => ?_
  have h1 := M.level_le_T_slot (k + 1)
  have h2 := M.T_mono (show M.slot (k + 1) ≤ c from hk)
  have hX1 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  have hϑ := M.hϑ0
  unfold SlotModel.level at h1
  push_cast at h1
  have hk' : (k : ℝ) ≤ M.T c := by linarith
  exact Nat.cast_le.mp (hk'.trans (Nat.le_ceil _))

/-- **The realised primes form a Beurling system** for `H = max(H_std, M̄₁²)`, jitters in `[0,1]`,
the target `⌊x⌋` below `X₀` and infinitely many slots placing a prime. -/
theorem realisedOK_of {X₀ : ℕ} (M : SlotModel X₀) {U : ℕ → ℝ} (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊)
    (hinf : {k | placedAt M k}.Infinite) : RealisedOK M (capH X₀) U := by
  have hX1 : (1 : ℝ) < X₀ := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hX2 : (2 : ℝ) ≤ X₀ := by
    have : 1 < X₀ := by exact_mod_cast hX1
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rintro (p | k)
    · simp only [realisedVal]
      exact_mod_cast p.2.1.one_lt
    · simp only [realisedVal]
      obtain ⟨hs, hv⟩ := primeValueOf_ge M hU hX hTlow k.1
      show 1 < primeValueOf M (capH X₀) U k.1
      linarith
  · intro b
    haveI : Finite {p : ℕ // p.Prime ∧ p < X₀} :=
      Finite.of_injective (fun p => (⟨p.1, p.2.2⟩ : Fin X₀))
        (fun p q h => Subtype.ext (by simpa using congrArg Fin.val h))
    have hA : (range (Sum.inl : {p : ℕ // p.Prime ∧ p < X₀} → RealisedIdx M)).Finite :=
      Set.finite_range _
    have hB : {k : {k : ℕ // placedAt M k} | M.slot (k.1 + 1) ≤ 8 * b / 7}.Finite :=
      (finite_slot_le M hX1n (8 * b / 7)).preimage Subtype.val_injective.injOn
    refine (hA.union (hB.image Sum.inr)).subset ?_
    rintro (p | k) hi
    · exact Or.inl ⟨p, rfl⟩
    · right
      refine ⟨k, ?_, rfl⟩
      have hv := (primeValueOf_ge M hU hX hTlow k.1).2
      simp only [mem_setOf_eq, realisedVal] at hi ⊢
      linarith
  · haveI : Infinite {k : ℕ // placedAt M k} := Set.infinite_coe_iff.mpr hinf
    infer_instance

/-! ### Elements of `A` are large, and `u_a` -/

/-- `n ∈ A`, `n ≥ 1` gives `#(A ∩ [1, n]) ≥ 1` (for `A` locally finite). -/
lemma one_le_countA {A : Set ℝ} (hA : LocFin A) {n : ℝ} (hn : n ∈ A) (hn1 : 1 ≤ n) :
    1 ≤ Absorbed.countA A n := by
  unfold Absorbed.countA
  have := (Set.ncard_pos (hA.finite_Icc 1 n)).mpr ⟨n, hn, hn1, le_rfl⟩
  exact_mod_cast this

/-- **Elements of the realised absorbed set are large**: `log n > (log X₀)²` for `n ∈ A`, and so
`n > 2X₀`. -/
theorem realisedA_large {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ} (h : RealisedOK M (capH X₀) U)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {n : ℝ} (hn : n ∈ realisedA M (capH X₀) U) :
    Real.log X₀ ^ 2 < Real.log n ∧ 2 * (X₀ : ℝ) < n := by
  let R : GreedyRun X₀ := ⟨M, capH X₀, U, hTlow⟩
  have C : AbsorbedCoupling (realisedSystem M (capH X₀) U) R.M R.H R.U
      (realisedA M (capH X₀) U) (realisedLatest M (capH X₀) U) := realisedCoupling h
  have hA : ∀ a ∈ realisedA M (capH X₀) U,
      ∃ r : ℝ, (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ r ∧ r < absorbY X₀ a := fun a ha =>
    ⟨_, C.latest_ge rfl hU hX ha, (C.rule ha).2.2⟩
  have hlogn : 10 ^ 7 ≤ Real.log n := hn.1
  have hn1 : (1 : ℝ) ≤ n := by
    obtain ⟨e, hev, -⟩ := hn.2
    rw [← hev]
    exact (realisedSystem M (capH X₀) U).one_le_val e
  have hbig : Real.log X₀ ^ 2 < Real.log n := by
    by_contra hle
    push_neg at hle
    have h0 := countA_eq_zero_of_low (Nat.cast_nonneg _) hX hA n hn1 hle
    have h1 := one_le_countA C.locFin hn hn1
    linarith
  refine ⟨hbig, ?_⟩
  have hX1 : (1 : ℝ) < X₀ := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hl2 : Real.log (2 * X₀) < Real.log n := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    nlinarith
  exact (Real.log_lt_log_iff (by linarith) (by linarith)).mp hl2

/-- **`u_a` for the realised absorbed set**: `X₀ ≤ u_a` and `u_a + u_a^{θ/2} = a`, with
`u_a = solveU (θ/2) a`, for `θ ∈ (0, 2]`. -/
theorem realisedU_spec {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ} (h : RealisedOK M (capH X₀) U)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 2) :
    ∀ n ∈ realisedA M (capH X₀) U,
      (X₀ : ℝ) ≤ solveU (θ / 2) n ∧ solveU (θ / 2) n + solveU (θ / 2) n ^ (θ / 2) = n := by
  intro n hn
  have hX1 : (1 : ℝ) < X₀ := one_lt_of_logX (Nat.cast_nonneg _) hX
  exact ⟨le_solveU (by linarith) (by linarith) hX1.le (realisedA_large h hU hX hTlow hn).2,
    (solveU_spec (by linarith) (by linarith [(realisedA_large h hU hX hTlow hn).2])).2⟩

/-! ### The top-level hypothesis with the coupling constructed -/

/-- `PartIRestSp` for the constructed `u_a`, without the condition `X₀ ≤ u_a`,
`u_a + u_a^{θ/2} = a` (proved, `realisedU_spec`). -/
def PartIRestJ (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ)
    (M : SlotModel X₀) : Prop :=
  (∀ x, M.T x = target X₀ (kappaParam X₀) (countA A) (absorbedDensityCap (θ / 2) A u)
      (osc θ (designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x) ∧
    M.QueueWindowData ∧
    ∃ κp : ℝ → ℝ,
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (P.N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)

/-- **Theorem 2.1, hypothesis on the concrete construction, with the realised system, the absorbed
set, `u_a` and the latest-prime map constructed from the jitters.** For each `ω` in the good event
(with jitters in `[0, 1]`), the system is `P(ω) = realisedSystem (M ω) H ω` (`H = capH X₀`), the
absorbed set is `realisedA (M ω) H ω`, `u_a = solveU (θ/2) a`, and the latest-prime map is
`realisedLatest (M ω) H ω`. Still supplied: the slot model `M ω`, the construction scales `a`, and
the hypotheses on them (`PartIRestJ`, `Theorem410RestSp`, `SparsityInputs`), the failure events
with their adaptedness and the per-scale bounds of Table 1, and the condition that the greedy rule
places infinitely many primes. -/
def Theorem21InputsJ : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      FailureAdapted jitterFiltration E time ∧
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        {k | placedAt (M ω) k}.Infinite ∧
        ∃ a : ℕ → ℝ,
          PartIRestJ θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (θ / 2) n) a (M ω) ∧
          Theorem410RestSp θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
            (fun n => solveU (θ / 2) n) a ∧
          SparsityInputs X₀ (realisedSystem (M ω) (capH X₀) ω)

/-- **`Theorem21InputsJ` gives `Theorem21InputsSp`**: the system, the origin of its primes, the
absorbed set, `u_a`, the latest-prime map and the coupling are the constructed ones
(`realisedOK_of`, `realisedCoupling`, `realisedU_spec`). -/
theorem theorem21InputsSp_of_J (h : Theorem21InputsJ) : Theorem21InputsSp := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, hE, htab, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨fun ω => realisedSystem (M ω) (capH X₀) ω, ι, hι, E, time, hE, htab, fun ω hG hω => ?_⟩
  obtain ⟨hinf, a, hI, hC, hS⟩ := hP ω hG hω
  obtain ⟨hT, hq, κp, hκp, hland, hinit⟩ := hI
  have hTlow : ∀ x : ℝ, x < X₀ → (M ω).T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hok := realisedOK_of (M ω) hω hlog hTlow hinf
  refine ⟨realisedA (M ω) (capH X₀) ω, fun n => solveU (θ / 2) n, a, M ω,
    realisedLatest (M ω) (capH X₀) ω,
    ⟨realisedU_spec hok hω hlog hTlow (by linarith [hθ.1]) (by linarith [hθ.2]), hT, hq, κp, hκp,
      hland, hinit⟩, hC, ⟨realisedCoupling hok⟩, hS⟩

/-- Theorem 2.1 from `Theorem21InputsJ`. -/
theorem theorem21_of_J (h : Theorem21InputsJ) : Theorem21 :=
  theorem21_of_sp (theorem21InputsSp_of_J h)

/-- **Corollary 2.2** from `Theorem21InputsJ`. -/
theorem corollary_2_2_of_J (h : Theorem21InputsJ) : ¬ QuestionQ :=
  corollary_2_2_of_sp (theorem21InputsSp_of_J h)

end Construction

end
