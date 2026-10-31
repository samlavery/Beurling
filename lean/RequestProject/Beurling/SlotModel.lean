module

public import RequestProject.Beurling.QueueMono
public import RequestProject.Beurling.QueueDeterministic
public import RequestProject.Beurling.LagSplit

/-!
# The slot model of Section 3.4 and the queue bound in the slot data

Section 3.4 of the paper defines, from the target `T` (non-decreasing, right-continuous,
unbounded), the slots

  `s_j := min{x ≥ 1 : T(x) ≥ j + ϑ_s}`,   `J_j := [s_j, s_{j+1})`,

and runs the hard greedy rule on the composite arrivals `A_j`:
`P_j = max(0, 1 - Q_{j-1} - A_j)`, `Q_j = Q_{j-1} + A_j + P_j - 1`, from `Q_{j₀-1} = 0`, `j₀ = X₀`.

Here this model is formalized (`SlotModel`), with slots indexed relative to the first slot:
relative slot `k ≥ 1` is the paper's slot `j = X₀ - 1 + k`, with level `X₀ - 1 + k + ϑ`, and
`k = 0` is the paper's `j₀ - 1`.

* `SlotModel.slot` : the slot starts `s_k`, defined as an infimum, with `slot_mem`
  (`T(s_k) ≥` level, the minimum is attained by right-continuity), `slot_mono`;
* `SlotModel.slotIdx` : the slot containing a height `x ≥ X₀`, with `mem_slot`
  (`s_k ≤ x < s_{k+1}` and `T(x) ∈ [j + ϑ, j + 1 + ϑ)`);
* `SlotModel.queue` : the queue of the construction, **defined** as the greedy queue of the
  arrivals; `SlotModel.count_identity` is Lemma 3.6 (`V_j = j + 1 + Q_j`);
* `SlotModel.queue_le_frozen` : Theorem 6.6(ii), deterministic part, for the model's queue with
  the bound frozen per dyadic scale: `Q_j ≤ B(s_j)`;
* `SlotModel.queue_le_queueB` : `max_{s_j ≤ x} Q_j ≤ B(x)` (Remark 6.9(ii)), using that `B` is
  non-decreasing (Theorem 6.23(c), `QueueMono`);
* `PartIInputsSlotModel` : the inputs of Theorem 2.1(i) in which the queue of the slot data is the
  model's queue. The top-level queue hypothesis `0 ≤ Q_max ≤ B(x)` is no longer assumed; it is
  derived (`PartIInputsSlotModel.toSplit`). Corollary 2.2 follows (`corollary_2_2_of_slotModel`).
-/

@[expose] public section

open Finset Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound
  Greedy QueueDet QueueMono

/-- **The slot model of Section 3.4.** `T` is the target, `ϑ = ϑ_s ∈ (0, 1/2]`, `arr k` the number
of composite arrivals in relative slot `k ≥ 1` (paper's slot `X₀ - 1 + k`), and `V k` the count
`V_j` of Lemma 3.6 (composites below `s_{j+1}`, plus primes decided at slots `≤ j`, plus one),
which starts at `V_{j₀-1} = j₀ = X₀` and increases by `A_j + P_j` at slot `j`. -/
structure SlotModel (X₀ : ℕ) where
  ϑ : ℝ
  T : ℝ → ℝ
  arr : ℕ → ℤ
  V : ℕ → ℤ
  hϑ0 : 0 < ϑ
  hϑ : ϑ ≤ 1 / 2
  T_mono : Monotone T
  T_rcont : ∀ x, ContinuousWithinAt T (Set.Ici x) x
  T_unbdd : ∀ y, ∃ x, y ≤ T x
  T_start : (X₀ : ℝ) ≤ T X₀
  arr_nonneg : ∀ k, 0 ≤ arr k
  V_zero : V 0 = X₀
  V_step : ∀ k, V (k + 1) = V k + arr (k + 1) + greedyPrime arr k

namespace SlotModel

variable {X₀ : ℕ} (M : SlotModel X₀)

/-- The level `j + ϑ` of relative slot `k` (paper's slot `j = X₀ - 1 + k`). -/
noncomputable def level (k : ℕ) : ℝ := (X₀ : ℝ) - 1 + k + M.ϑ

/-- The heights `x ≥ 1` with `T(x) ≥ j + ϑ`. -/
def slotSet (k : ℕ) : Set ℝ := {x | 1 ≤ x ∧ M.level k ≤ M.T x}

/-- **The slot start** `s_j = min{x ≥ 1 : T(x) ≥ j + ϑ}`. -/
noncomputable def slot (k : ℕ) : ℝ := sInf (M.slotSet k)

/-- **The queue** `Q_j` of the hard greedy rule (Lemma 3.7), `Q_{j₀ - 1} = 0`. -/
def queue (k : ℕ) : ℤ := greedyQueue M.arr k

/-- The arrivals at relative slot `k`, with no arrivals at `k = 0` (the paper's `j₀ - 1`). -/
def slotArr (k : ℕ) : ℤ := if k = 0 then 0 else M.arr k

/-- The (relative) slot containing the height `x`: `⌊T(x) - ϑ - X₀ + 1⌋`. -/
noncomputable def slotIdx (x : ℝ) : ℕ := ⌊M.T x - M.ϑ - X₀ + 1⌋₊

lemma slotSet_nonempty (k : ℕ) : (M.slotSet k).Nonempty := by
  obtain ⟨x, hx⟩ := M.T_unbdd (M.level k)
  exact ⟨max x 1, le_max_right _ _, hx.trans (M.T_mono (le_max_left _ _))⟩

lemma slotSet_bddBelow (k : ℕ) : BddBelow (M.slotSet k) := ⟨1, fun _ hx => hx.1⟩

lemma slot_le {k : ℕ} {x : ℝ} (hx : x ∈ M.slotSet k) : M.slot k ≤ x :=
  csInf_le (M.slotSet_bddBelow k) hx

/-- **The minimum is attained**: `s_j ≥ 1` and `T(s_j) ≥ j + ϑ` (by right-continuity of `T`). -/
lemma slot_mem (k : ℕ) : M.slot k ∈ M.slotSet k := by
  set s := M.slot k
  have h1 : 1 ≤ s := le_csInf (M.slotSet_nonempty k) (fun _ hx => hx.1)
  refine ⟨h1, ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (M.T_rcont s)
    (M.level k - M.T s) (by linarith)
  have hlow : s + δ ≤ s := by
    apply le_csInf (M.slotSet_nonempty k)
    intro x hx
    have hsx : s ≤ x := M.slot_le hx
    by_contra hxδ
    push_neg at hxδ
    have hd : dist x s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have := hball (Set.mem_Ici.mpr hsx) hd
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith [hx.2]
  linarith

lemma level_le_T_slot (k : ℕ) : M.level k ≤ M.T (M.slot k) := (M.slot_mem k).2

lemma one_le_slot (k : ℕ) : 1 ≤ M.slot k := (M.slot_mem k).1

/-- Below the slot start, `T` is below the level. -/
lemma T_lt_level {k : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hx : x < M.slot k) : M.T x < M.level k := by
  by_contra h; push_neg at h
  exact absurd (M.slot_le ⟨hx1, h⟩) (not_le.mpr hx)

/-- The slot starts are non-decreasing. -/
lemma slot_mono : Monotone M.slot := by
  intro k k' hkk
  apply csInf_le_csInf (M.slotSet_bddBelow k) (M.slotSet_nonempty k')
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2⟩
  unfold level
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  linarith

/-- **The slot of a height** `x ≥ X₀` (`X₀ ≥ 1`): with `k = slotIdx x` and `j = X₀ - 1 + k`,
`s_k ≤ x < s_{k+1}` and `T(x) ∈ [j + ϑ, j + 1 + ϑ)`. -/
theorem mem_slot (hX₀ : 1 ≤ X₀) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    M.slot (M.slotIdx x) ≤ x ∧ x < M.slot (M.slotIdx x + 1) ∧
      ((X₀ : ℝ) - 1 + M.slotIdx x) + M.ϑ ≤ M.T x ∧
      M.T x < ((X₀ : ℝ) - 1 + M.slotIdx x) + 1 + M.ϑ := by
  have hX1 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX₀
  have hT : (X₀ : ℝ) ≤ M.T x := M.T_start.trans (M.T_mono hx)
  have hϑ := M.hϑ
  have hz : 0 ≤ M.T x - M.ϑ - X₀ + 1 := by linarith
  have hfl := Nat.floor_le hz
  have hfl2 := Nat.lt_floor_add_one (M.T x - M.ϑ - X₀ + 1)
  unfold slotIdx
  set k := ⌊M.T x - M.ϑ - X₀ + 1⌋₊
  have hlev : M.level k ≤ M.T x := by unfold level; linarith
  have hlev2 : M.T x < M.level (k + 1) := by unfold level; push_cast; linarith
  refine ⟨M.slot_le ⟨by linarith, hlev⟩, ?_, by linarith, by linarith⟩
  by_contra h; push_neg at h
  have := (M.level_le_T_slot (k + 1)).trans (M.T_mono h)
  linarith

/-- **Lemma 3.6 (count identity)**: `V_j = j + 1 + Q_j`; in relative indexing,
`V k = X₀ + k + Q k`. -/
theorem count_identity (k : ℕ) : M.V k = X₀ + k + M.queue k := by
  induction k with
  | zero => simp [M.V_zero, queue, greedyQueue]
  | succ k ih =>
    rw [M.V_step, ih]
    unfold queue greedyPrime
    simp only [greedyQueue]
    push_cast; ring

/-- `Q_j - A_j = Q_{j-1} + P_j - 1 ≥ -1` (proof of Corollary 3.8). -/
lemma queue_sub_slotArr (k : ℕ) : -1 ≤ M.queue k - M.slotArr k := by
  cases k with
  | zero => simp [queue, slotArr, greedyQueue]
  | succ k =>
    unfold queue slotArr
    simp only [Nat.succ_ne_zero, if_false, greedyQueue]
    have := greedyQueue_nonneg M.arr k
    have := le_max_left 0 (1 - greedyQueue M.arr k - M.arr (k + 1))
    linarith

lemma queue_nonneg (k : ℕ) : 0 ≤ M.queue k := greedyQueue_nonneg M.arr k

/-- The per-window inputs of Theorem 6.6(ii) for the model's arrivals, with the bound frozen per
dyadic scale `B(s_j)` (`queueBScale`): at every slot `j`, either every window `(i, j]` carries the
short-window inputs, or there is a last full block `(i, j]` carrying the full-block inputs and
every window `(i', j]`, `i ≤ i'`, carries the short-window inputs. -/
def QueueWindowData : Prop :=
  ∀ k, (∀ i, i ≤ k → ShortWindowData M.arr i k (queueBScale X₀ (M.slot k))) ∨
    ∃ i < k, FullBlockData M.arr i k ∧
      ∀ i', i ≤ i' → i' ≤ k → ShortWindowData M.arr i' k (queueBScale X₀ (M.slot k))

/-- **Theorem 6.6(ii), deterministic part, for the model's queue**: `Q_j ≤ B(s_j)`, with `B`
frozen per dyadic scale. -/
theorem queue_le_frozen (hX : 10 ^ 8 ≤ Real.log X₀) (h : M.QueueWindowData) (k : ℕ) :
    (M.queue k : ℝ) ≤ queueBScale X₀ (M.slot k) := by
  have hB : Monotone (fun k => queueBScale X₀ (M.slot k)) :=
    (queueBScale_monotone (Nat.cast_nonneg _) hX).comp M.slot_mono
  exact queue_bound_deterministic M.arr _ hB h k

/-- **`max_{s_j ≤ x} Q_j ≤ B(x)`** (Remark 6.9(ii)): every slot starting at or below `x ≥ X₀`
has queue at most `B(x)`, since `B` is non-decreasing (Theorem 6.23(c)). -/
theorem queue_le_queueB (hX : 10 ^ 8 ≤ Real.log X₀) (h : M.QueueWindowData) {k : ℕ} {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hk : M.slot k ≤ x) : (M.queue k : ℝ) ≤ queueB X₀ x :=
  (M.queue_le_frozen hX h k).trans (queueBScale_le (Nat.cast_nonneg _) hX hx hk)

/-- The landing data of the proof of Corollary 3.8 at a height `x` in the model: with
`k = slotIdx x`, the decomposition `N(x) = V_j - C((x, s_{j+1})) + E₊ - E₋`, `0 ≤ C ≤ A_j`, and the
primes counted by `E₊` (resp. `E₋`) placed at distinct continuous-slot starts `S₊ ⊆ [x, x + ℓ₊]`
(resp. `S₋ ⊆ [x - ℓ₋, x]`), one unit of continuous mass `F` apart, with slope at most `c` on
these windows and `c ℓ± ≤ W + ε`, `ε ≤ 1/2`. -/
def Landing (N W x : ℝ) : Prop :=
  ∃ (C Ep Em ε c lp lm : ℝ) (F : ℝ → ℝ) (Sp Sm : Finset ℝ),
    Monotone F ∧ N = (M.V (M.slotIdx x) : ℝ) - C + Ep - Em ∧
    0 ≤ C ∧ C ≤ (M.slotArr (M.slotIdx x) : ℝ) ∧ 0 ≤ lp ∧ 0 ≤ lm ∧
    (∀ s ∈ Sp, x ≤ s ∧ s ≤ x + lp) ∧ (∀ s ∈ Sm, x - lm ≤ s ∧ s ≤ x) ∧
    (∀ s ∈ Sp, ∀ t ∈ Sp, s < t → 1 ≤ F t - F s) ∧
    (∀ s ∈ Sm, ∀ t ∈ Sm, s < t → 1 ≤ F t - F s) ∧
    F (x + lp) - F x ≤ c * lp ∧ F x - F (x - lm) ≤ c * lm ∧
    0 ≤ Ep ∧ Ep ≤ Sp.card ∧ 0 ≤ Em ∧ Em ≤ Sm.card ∧
    c * lp ≤ W + ε ∧ c * lm ≤ W + ε ∧ ε ≤ 1 / 2

/-- In the model, the landing data at `x ≥ X₀` give the slot data of Corollary 3.8 with the
model's queue and the bound `Q_max = B(x)`: the slot index, the position of `T(x)` in its slot,
the count identity (Lemma 3.6), `Q_j - A_j ≥ -1` and `Q_j ≤ B(x)` are all derived. -/
theorem Landing.toSlotData (hX : 10 ^ 8 ≤ Real.log X₀) (hq : M.QueueWindowData) {N W x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (h : M.Landing N W x) : SlotData N (M.T x) (queueB X₀ x) W x := by
  have hX₀ : 1 ≤ X₀ := by
    have := one_lt_of_logX (Nat.cast_nonneg _) hX
    exact_mod_cast this.le
  obtain ⟨C, Ep, Em, ε, c, lp, lm, F, Sp, Sm, hF, hN, hC0, hCA, hlp, hlm, hSp, hSm, hgp, hgm,
    hcp, hcm, hEp0, hEp, hEm0, hEm, hWp, hWm, hε⟩ := h
  obtain ⟨hs1, -, hT1, hT2⟩ := M.mem_slot hX₀ hx
  set k := M.slotIdx x
  have hV := M.count_identity k
  have hQA := M.queue_sub_slotArr k
  refine ⟨(X₀ : ℝ) - 1 + k, M.queue k, M.slotArr k, C, Ep, Em, M.ϑ, ε, c, lp, lm, F, Sp, Sm,
    hF, ?_, hT1, hT2, M.hϑ0, M.hϑ, hC0, hCA, by exact_mod_cast hQA,
    M.queue_le_queueB hX hq hx hs1, hlp, hlm, hSp, hSm, hgp, hgm, hcp, hcm, hEp0, hEp, hEm0,
    hEm, hWp, hWm, hε⟩
  rw [hN, hV]; push_cast; ring

end SlotModel

open SlotModel

/-- **The inputs of Theorem 2.1(i) with the slot model of Section 3.4.** As
`PartIInputsSlotsSplit`, except that the slot data come from a `SlotModel` whose target is the
paper's `T`:
* the queue of the slot data is the model's greedy queue, and the per-window inputs of
  Theorem 6.6(ii) are stated for its arrivals with the bound `B(s_j)` frozen per dyadic scale;
* for `x ≥ X₀ + 2H(x)`, only the landing data of Corollary 3.8 are assumed (`Landing`);
* the top-level queue bound `0 ≤ Q_max(x) ≤ B(x)` is **not** assumed.
On `[X₀, X₀ + 2H(x))` the paper's bound from the proof of Proposition 4.1 is assumed, as in
`PartIInputsSlotsSplit`. -/
def PartIInputsSlotModel (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (κp : ℝ → ℝ) (M : SlotModel X₀),
    0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (thetaB θ) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (thetaB θ) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x, M.T x = target X₀ κ (countA A) (absorbedDensityCap (thetaB θ) A u) (osc θ α γ xp) x) ∧
    M.QueueWindowData ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (thetaB θ) A u) (osc θ α γ xp) x| ≤
        queueB X₀ X₀ + capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀) + 5)

/-- **The slot model gives the split inputs**, with `Q_max(x) := B(x)`: the queue bound
`0 ≤ Q_max ≤ B(x)` holds trivially, and the slot data follow from `Landing.toSlotData`. -/
theorem PartIInputsSlotModel.toSplit {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hX : 10 ^ 8 ≤ Real.log X₀) (h : PartIInputsSlotModel θ X₀ P) :
    PartIInputsSlotsSplit θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, κp, M, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hT, hq, hκp, hland,
    hinit⟩ := h
  refine ⟨κ, A, u, α, γ, xp, queueB X₀, κp, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ,
    fun x hx => ⟨queueB_nonneg (Nat.cast_nonneg _) hX hx, le_rfl⟩, hκp, fun x hx hlate => ?_,
    hinit⟩
  have := (hland x hx hlate).toSlotData M hX hq hx
  rwa [hT x] at this

/-- Refined inputs for one system: `PartIInputsSlotModel` and `Theorem410InputsRankin`. -/
def TheoremAInputsSlotModel (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotModel θ X₀ P ∧ Theorem410InputsRankin θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsSplit`, with the slot data coming
from the slot model of Section 3.4 and without the top-level queue bound. -/
def Theorem21InputsSlotModel : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsSlotModel θ X₀ (P ω)

theorem theorem21InputsSplit_of_slotModel (h : Theorem21InputsSlotModel) :
    Theorem21InputsSplit := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1.toSplit hlog, (hP ω hω).2⟩⟩

/-- The refined hypothesis `Theorem21InputsSlotModel` implies Theorem 2.1. -/
theorem theorem21_of_slotModel (h : Theorem21InputsSlotModel) : Theorem21 :=
  theorem21_of_split (theorem21InputsSplit_of_slotModel h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsSlotModel`. -/
theorem corollary_2_2_of_slotModel (h : Theorem21InputsSlotModel) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_slotModel h)

end
