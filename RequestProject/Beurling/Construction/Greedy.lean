module

public import RequestProject.Beurling.Construction.Jitter
public import RequestProject.Beurling.SlotModel
public import RequestProject.Beurling.GoodEvent

/-!
# The greedy rule with box-centred jitter, the absorbed set (5), and the failure events

Pathwise data of the construction of Section 3.4 (for one `ω`):

* `GreedyRun X₀`: a slot model (target `T`, slots, composite arrivals, greedy queue), together
  with the jitter width `H` and the jitters `U`, and the target being `⌊x⌋` below `X₀` (6);
* the primes placed by the rule: at relative slot `k + 1` a prime is placed iff
  `P = max(0, 1 - Q - A) = 1`, and it lands at `s + H(s) (U - 1/2)`, `s` the slot start;
* `GreedyRun.slot_ge`: every slot start is `≥ X₀`;
* `GreedyRun.jittered_ge`: every placed (jittered) prime is `≥ X₀ - H(X₀)/2`, provided the jitters
  lie in `[0, 1]` and `v ↦ v - H(v)/2` is non-decreasing (§3.4);
* `absorbedRule`: the absorbed set (5), `A = {n : log n ≥ L*, the latest prime r of n is jittered,
  r < y(n)}`, and `absorbedRule_placement`: every `n ∈ A` has a prime `r` with
  `X₀ - H(X₀)/2 ≤ r < y(n)`.

Failure events (Definition 6.8): a countable family of events `E i` with times `t(E i)`, each
`E i` measurable with respect to `F_{t(E i)}`. `goodBefore t = Good(< t)` is the intersection of the
events with time `< t`, `failTime` is the first failure time `τ`, and `goodAll = {τ = ∞}`.
`goodAll_prob_ge` is the probability budget of Lemma 6.10 (a union bound).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Greedy

namespace Construction

/-- **One run of the greedy rule with box-centred jitter.** -/
structure GreedyRun (X₀ : ℕ) where
  /-- the target, the slots, the composite arrivals and the greedy queue -/
  M : SlotModel X₀
  /-- the jitter width `H(x)` -/
  H : ℝ → ℝ
  /-- the jitters `U_j` (relative slot index) -/
  U : ℕ → ℝ
  /-- the target is `⌊x⌋` below `X₀` (6) -/
  T_low : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊

/-- A prime is placed at relative slot `k + 1` (the decision `P = 1` of the hard greedy rule). -/
def placedAt {X₀ : ℕ} (M : SlotModel X₀) (k : ℕ) : Prop := greedyPrime M.arr k = 1

/-- The value of the prime decided at relative slot `k + 1`: it lands at
`s + H(s) (U - 1/2)`, `s = s_{k+1}` the slot start. -/
noncomputable def primeValueOf {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ) (k : ℕ) : ℝ :=
  landing (M.slot (k + 1)) (H (M.slot (k + 1))) (U (k + 1))

/-- The jittered primes: the values of the primes placed by the greedy rule with jitter width `H`
and jitters `U`. -/
def jitteredPrimesOf {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ) : Set ℝ :=
  {r | ∃ k, placedAt M k ∧ r = primeValueOf M H U k}

namespace GreedyRun

variable {X₀ : ℕ} (R : GreedyRun X₀)

/-- The jittered primes of the run. -/
def jitteredPrimes : Set ℝ := jitteredPrimesOf R.M R.H R.U

/-- Every slot start is `≥ X₀`, since `T = ⌊x⌋ ≤ X₀ - 1` below `X₀`. -/
lemma slot_ge (k : ℕ) : (X₀ : ℝ) ≤ R.M.slot k := by
  refine le_csInf (R.M.slotSet_nonempty k) (fun x hx => ?_)
  by_contra hlt
  push_neg at hlt
  have hx1 : (1 : ℝ) ≤ x := hx.1
  have hlev : R.M.level k ≤ R.M.T x := hx.2
  rw [R.T_low x hlt] at hlev
  have hfl : ⌊x⌋₊ < X₀ := (Nat.floor_lt (by linarith)).mpr hlt
  have hfl' : (⌊x⌋₊ : ℝ) + 1 ≤ X₀ := by exact_mod_cast hfl
  have hϑ := R.M.hϑ0
  unfold SlotModel.level at hlev
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- **Placement of the jittered primes**: if the jitters lie in `[0, 1]`, `H ≥ 0` and
`v ↦ v - H(v)/2` is non-decreasing on `[X₀, ∞)`, then every jittered prime is
`≥ X₀ - H(X₀)/2`. -/
theorem jittered_ge (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1) (hH : ∀ v, 0 ≤ R.H v)
    (hmono : MonotoneOn (fun v => v - R.H v / 2) (Ici (X₀ : ℝ))) :
    ∀ r ∈ R.jitteredPrimes, (X₀ : ℝ) - R.H X₀ / 2 ≤ r := by
  rintro r ⟨k, -, rfl⟩
  have hs := R.slot_ge (k + 1)
  have h1 := (landing_mem_box (s := R.M.slot (k + 1)) (hH (R.M.slot (k + 1))) (hU (k + 1))).1
  have h2 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
  simp only at h2
  unfold primeValueOf
  linarith

end GreedyRun

/-- **The absorbed set (5)**: `n` with `log n ≥ L*` whose latest prime `latest n` is jittered and
below `y(n)`. -/
def absorbedRule (Lstar : ℝ) (jit : Set ℝ) (latest : ℝ → ℝ) (y : ℝ → ℝ) : Set ℝ :=
  {n | Lstar ≤ Real.log n ∧ latest n ∈ jit ∧ latest n < y n}

/-- **The placement fact for `A`**: if every jittered prime is `≥ c`, every `n ∈ A` has a prime `r`
with `c ≤ r < y(n)`. -/
theorem absorbedRule_placement {Lstar c : ℝ} {jit : Set ℝ} {latest y : ℝ → ℝ}
    (hjit : ∀ r ∈ jit, c ≤ r) :
    ∀ n ∈ absorbedRule Lstar jit latest y, ∃ r : ℝ, c ≤ r ∧ r < y n :=
  fun n hn => ⟨latest n, hjit _ hn.2.1, hn.2.2⟩

section Failure

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- The failure events are adapted: `E i` is `F_{t(E i)}`-measurable. -/
def FailureAdapted (F : Filtration ℕ mΩ) (E : ι → Set Ω) (time : ι → ℕ) : Prop :=
  ∀ i, MeasurableSet[F (time i)] (E i)

/-- `Good(< t)`: every event with time `< t` holds. -/
def goodBefore (E : ι → Set Ω) (time : ι → ℕ) (t : ℕ) : Set Ω :=
  ⋂ i, ⋂ (_ : time i < t), E i

/-- The good event `G = ⋂ E`. -/
def goodAll (E : ι → Set Ω) : Set Ω := ⋂ i, E i

/-- The first failure time `τ(ω)`: the least time of an event that fails at `ω` (`⊤` if none). -/
noncomputable def failTime (E : ι → Set Ω) (time : ι → ℕ) (ω : Ω) : ℕ∞ :=
  ⨅ i, ⨅ (_ : ω ∉ E i), (time i : ℕ∞)

/-- `Good(< t) = {τ ≥ t}`. -/
theorem goodBefore_eq (E : ι → Set Ω) (time : ι → ℕ) (t : ℕ) :
    goodBefore E time t = {ω | (t : ℕ∞) ≤ failTime E time ω} := by
  ext ω
  simp only [goodBefore, failTime, mem_iInter, mem_setOf_eq, le_iInf_iff]
  constructor
  · intro h i hi
    by_contra hlt
    push_neg at hlt
    exact hi (h i (by exact_mod_cast hlt))
  · intro h i hi
    by_contra hE
    have := h i hE
    have : t ≤ time i := by exact_mod_cast this
    omega

/-- `G = {τ = ∞}`. -/
theorem goodAll_eq (E : ι → Set Ω) (time : ι → ℕ) :
    goodAll E = {ω | failTime E time ω = ⊤} := by
  ext ω
  simp only [goodAll, failTime, mem_iInter, mem_setOf_eq, iInf_eq_top]
  constructor
  · intro h i hi; exact absurd (h i) hi
  · intro h i
    by_contra hE
    exact ENat.coe_ne_top _ (h i hE)

/-- `Good(< t)` is `F_t`-measurable (for a countable family of adapted events). -/
theorem goodBefore_measurable [Countable ι] (F : Filtration ℕ mΩ) {E : ι → Set Ω}
    {time : ι → ℕ} (hE : FailureAdapted F E time) (t : ℕ) :
    MeasurableSet[F t] (goodBefore E time t) :=
  MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => F.mono hi.le _ (hE i)

/-- **The probability budget (Lemma 6.10)**: if the failure probabilities sum to at most `c`, then
`P(G) ≥ 1 - c`. -/
theorem goodAll_prob_ge [Countable ι] (F : Filtration ℕ mΩ) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : ι → Set Ω} {time : ι → ℕ} (hE : FailureAdapted F E time)
    {c : ℝ} (hc : 0 ≤ c) (hsum : ∑' i, μ (E i)ᶜ ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (1 - c) ≤ μ (goodAll E) := by
  have hm : ∀ i, MeasurableSet (E i) := fun i => F.le (time i) _ (hE i)
  refine GoodEvent.ofReal_one_sub_le (MeasurableSet.iInter hm) hc ?_
  rw [compl_iInter]
  exact (measure_iUnion_le _).trans hsum

end Failure

end Construction

end
