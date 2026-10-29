module

public import RequestProject.Beurling.QueueDeterministic

/-!
# Theorem 6.6(ii): from the per-window facts to the window data, by induction over slots

The proof of Theorem 6.6(ii) at a slot `j` uses, for every slot window `W = (i, j]` with
integer hull `I`:

* the excess identity (Lemma 3.9) with the sandwich: `exc(W) ≤ C_jit(I) - ℓ_jit(I) + 6`, and
  `C_jit(I) = S₁ + S₂` (latest prime dividing once, resp. at least squared);
* the edge counts `ℓ_jit(W) - 1 ≤ ℓ_jit(I) ≤ ℓ_jit(W) + 4`;
* the event `Fr(I)`(a) (for `ℓ_jit(I) ≤ K₀ + 5`), the drift bound R1′ (Corollary 5.40), and
  `Fr(I)`(b) with Corollary 6.12: `S₂ ≤ 8 M₁ L (L/Λ + 1)`.

R1′ holds on `Good(< max I)`, which contains the queue constraints at the earlier slots. So the
per-window facts at slot `j` are available once `Q_i ≤ B(s_i)` is known for `i < j`; the queue
bound and the window data are then proved together by strong induction over the slots.

* `Queue6.WindowFacts` : the facts above for one window, with `ℓ_jit(W)` given;
* `Queue6.SlotInputs` : the frozen parameters `M₁, L, Λ` at slot `j` (with `L² ≤ M₁`,
  `B(x) ≤ B_j`), the continuous-slot counts `ℓ_jit((i, j])` (steps of `0` or `1` as `i`
  decreases, `0` at `i = j`), and `WindowFacts` for every window ending at `j`;
* `Queue6.slotData_of_inputs` : `SlotInputs` at `j` gives the window data of Theorem 6.6(ii) at
  `j`: all windows short, or a last full block `(k', j]` with `ℓ_jit = K₀ := ⌊48 M₁ L³/c'²⌋`
  followed by short windows (the choice of `k'` in the Lindley step);
* `Queue6.queue_and_data` : if `SlotInputs` at `j` holds whenever `Q_i ≤ B_i` for all `i < j`,
  then `Q_j ≤ B_j` and the window data hold at every slot.
-/

@[expose] public section

open Finset Real QueueBound Greedy QueueDet

namespace Queue6

/-- The integer block length `K₀ = ⌊48 M₁ L³ / c'²⌋` (`c' = 0.15`; `L₀ = 48 M₁ L³/c'²` since
`M₁ ≥ L²`). -/
noncomputable def blockK (M1 L : ℝ) : ℕ := ⌊48 * M1 * L ^ 3 / 0.15 ^ 2⌋₊

/-- **The facts of the proof of Theorem 6.6(ii) for one slot window** `(i, j]` with
`ℓ_jit((i, j]) = ℓW`: an integer hull with `ℓ_jit(I) = ℓI`, the excess identity with the
sandwich, the edge counts, `Fr(I)`(a) for `ℓI ≤ K₀ + 5`, R1′ and `Fr(I)`(b) with
Corollary 6.12. -/
def WindowFacts (A : ℕ → ℤ) (j i : ℕ) (M1 L Λ : ℝ) (ℓW : ℕ) : Prop :=
  ∃ (ℓI : ℕ) (C S1 S2 Comp : ℝ),
    (exc A i j : ℝ) ≤ C - ℓI + 6 ∧ C = S1 + S2 ∧ ℓI ≤ ℓW + 4 ∧ ℓW ≤ ℓI + 1 ∧
    (ℓI ≤ blockK M1 L + 5 →
      S1 - Comp ≤ Real.sqrt (2 * (2 * M1 * (ℓI + 3)) * (4 * L)) + 4 / 3 * M1 * (4 * L)) ∧
    Comp ≤ ℓI * (1 - 0.15 / L) + 3 ∧ S2 ≤ 8 * M1 * L * (L / Λ + 1)

/-- **The inputs of Theorem 6.6(ii) at slot `j`**, with the bound `B_j`. -/
def SlotInputs (A : ℕ → ℤ) (Bj : ℝ) (j : ℕ) : Prop :=
  ∃ (M1 L Λ : ℝ) (ℓW : ℕ → ℕ), 10 ^ 8 ≤ L ∧ 10 ^ 8 ≤ Λ ∧ L ^ 2 ≤ M1 ∧
    queueBound75 M1 L Λ 0.15 3 ≤ Bj ∧ ℓW j = 0 ∧
    (∀ i < j, ℓW (i + 1) ≤ ℓW i ∧ ℓW i ≤ ℓW (i + 1) + 1) ∧
    ∀ i ≤ j, WindowFacts A j i M1 L Λ (ℓW i)

/-- The window data of Theorem 6.6(ii) at slot `j` (the body of `SlotModel.QueueWindowData`). -/
def SlotData (A : ℕ → ℤ) (Bj : ℝ) (j : ℕ) : Prop :=
  (∀ i, i ≤ j → ShortWindowData A i j Bj) ∨
    ∃ i < j, FullBlockData A i j ∧ ∀ i', i ≤ i' → i' ≤ j → ShortWindowData A i' j Bj

lemma one_le_of_sq_le {M1 L : ℝ} (hL : 10 ^ 8 ≤ L) (hM : L ^ 2 ≤ M1) : 1 ≤ M1 := by nlinarith

lemma blockK_ge {M1 L : ℝ} (hL : 10 ^ 8 ≤ L) (hM : L ^ 2 ≤ M1) : 1 ≤ blockK M1 L := by
  unfold blockK
  apply Nat.le_floor
  have h1 := one_le_of_sq_le hL hM
  have : (1 : ℝ) ≤ L ^ 3 := by nlinarith
  push_cast
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma short_of_facts {A : ℕ → ℤ} {j i : ℕ} {M1 L Λ Bj : ℝ} {ℓW : ℕ} (hL : 10 ^ 8 ≤ L)
    (hM : L ^ 2 ≤ M1) (hB : queueBound75 M1 L Λ 0.15 3 ≤ Bj) (hℓ : ℓW ≤ blockK M1 L)
    (h : WindowFacts A j i M1 L Λ ℓW) : ShortWindowData A i j Bj := by
  obtain ⟨ℓI, C, S1, S2, Comp, hexc, hC, hI1, -, hFr, hR1, hS2⟩ := h
  exact ⟨M1, L, Λ, ℓI, C, S1, S2, Comp, one_le_of_sq_le hL hM, hL, Nat.cast_nonneg _, hexc, hC,
    hFr (by omega), hR1, hS2, hB⟩

lemma full_of_facts {A : ℕ → ℤ} {j i : ℕ} {M1 L Λ : ℝ} {ℓW : ℕ} (hL : 10 ^ 8 ≤ L)
    (hΛ : 10 ^ 8 ≤ Λ) (hM : L ^ 2 ≤ M1) (hℓ : ℓW = blockK M1 L)
    (h : WindowFacts A j i M1 L Λ ℓW) : FullBlockData A i j := by
  obtain ⟨ℓI, C, S1, S2, Comp, hexc, hC, hI1, hI2, hFr, hR1, hS2⟩ := h
  have h0 : 0 ≤ 48 * M1 * L ^ 3 / 0.15 ^ 2 := by
    have := one_le_of_sq_le hL hM
    positivity
  have hK1 := Nat.floor_le h0
  have hK2 := Nat.lt_floor_add_one (48 * M1 * L ^ 3 / 0.15 ^ 2)
  set K := blockK M1 L with hK
  have hKr : (K : ℝ) = (⌊48 * M1 * L ^ 3 / 0.15 ^ 2⌋₊ : ℕ) := by rw [hK, blockK]
  have hI1' : (ℓI : ℝ) ≤ K + 4 := by rw [← hℓ]; exact_mod_cast hI1
  have hI2' : (K : ℝ) - 1 ≤ ℓI := by
    have : (ℓW : ℝ) ≤ ℓI + 1 := by exact_mod_cast hI2
    rw [hℓ] at this; linarith
  refine ⟨M1, L, Λ, ℓI, K, C, S1, S2, Comp, hL, hΛ, hM, by rw [hKr]; linarith,
    by rw [hKr]; exact hK1, hI2', hI1', hexc, hC, hFr (by omega), hR1, hS2⟩

/-- **The window data from the inputs at one slot** (proof of Theorem 6.6(ii), choice of the
last full block `k' = max{k < j : ℓ_jit((k, j]) = K₀}`). -/
theorem slotData_of_inputs {A : ℕ → ℤ} {Bj : ℝ} {j : ℕ} (h : SlotInputs A Bj j) :
    SlotData A Bj j := by
  obtain ⟨M1, L, Λ, ℓW, hL, hΛ, hM, hB, h0, hstep, hfacts⟩ := h
  set K := blockK M1 L
  -- `ℓW` is antitone in `i` on `[0, j]`
  have hanti : ∀ i i', i ≤ i' → i' ≤ j → ℓW i' ≤ ℓW i := by
    intro i i' hii' hi'j
    induction i' with
    | zero => rw [Nat.le_zero.mp hii']
    | succ n ih =>
      rcases Nat.lt_or_ge n i with hn | hn
      · rw [show i = n + 1 by omega]
      · exact (hstep n (by omega)).1.trans (ih hn (by omega))
  by_cases hsmall : ℓW 0 < K
  · left
    intro i hi
    exact short_of_facts hL hM hB ((hanti 0 i (Nat.zero_le _) hi).trans hsmall.le) (hfacts i hi)
  · right
    push_neg at hsmall
    -- the set of `i ≤ j` with `ℓW i ≥ K` contains `0`; take its largest element `k'`
    set S := (range (j + 1)).filter fun i => K ≤ ℓW i
    have hS : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.succ_pos _), hsmall⟩⟩
    obtain ⟨k, hkdef⟩ : ∃ k, k = S.max' hS := ⟨_, rfl⟩
    have hkS : k ∈ S := hkdef ▸ S.max'_mem hS
    rw [mem_filter, mem_range] at hkS
    have hkmax : ∀ i ≤ j, K ≤ ℓW i → i ≤ k := fun i hi hK => hkdef ▸
      S.le_max' i (mem_filter.mpr ⟨mem_range.mpr (by omega), hK⟩)
    have hK1 : 1 ≤ K := blockK_ge hL hM
    have hkj : k < j := by
      rcases Nat.lt_or_ge k j with h | h
      · exact h
      · have : k = j := by omega
        rw [this, h0] at hkS; omega
    have hkeq : ℓW k = K := by
      have h1 := hkS.2
      have h2 := (hstep k hkj).2
      have h3 : ℓW (k + 1) < K := by
        by_contra hc; push_neg at hc
        have := hkmax (k + 1) (by omega) hc; omega
      omega
    refine ⟨k, hkj, full_of_facts hL hΛ hM hkeq (hfacts k hkj.le), fun i' h1 h2 =>
      short_of_facts hL hM hB ((hanti k i' h1 h2).trans hkeq.le) (hfacts i' h2)⟩

/-- The queue bound at slot `j` from the window data at `j` and the bounds at earlier slots. -/
lemma queue_le_of_slotData {A : ℕ → ℤ} {B : ℕ → ℝ} (hB : Monotone B) {j : ℕ}
    (hprev : ∀ i < j, (greedyQueue A i : ℝ) ≤ B i) (h : SlotData A (B j) j) :
    (greedyQueue A j : ℝ) ≤ B j := by
  rcases h with h | ⟨k, hkj, hfull, hshort⟩
  · rw [greedyQueue_eq_sup_exc]
    have : ((range (j + 1)).sup' nonempty_range_add_one (fun i => exc A i j) : ℤ) ≤ ⌊B j⌋ := by
      rw [sup'_le_iff]
      intro i hi
      exact Int.le_floor.mpr ((h i (Nat.lt_succ_iff.mp (mem_range.mp hi))).le)
    exact (Int.cast_le.mpr this).trans (Int.floor_le _)
  · have hQk := hprev k hkj
    have hBk := hB hkj.le
    have hk0 := hfull.exc_nonpos
    have key : greedyQueue A j ≤ ⌊B j⌋ := by
      refine greedyQueue_le_split A hkj.le ?_ fun i h1 h2 => Int.le_floor.mpr (hshort i h1 h2).le
      apply Int.le_floor.mpr
      push_cast
      have : (exc A k j : ℝ) ≤ 0 := by exact_mod_cast hk0
      linarith
    exact (Int.cast_le.mpr key).trans (Int.floor_le _)

/-- **Theorem 6.6(ii) by induction over the slots.** If the inputs at slot `j` hold whenever
`Q_i ≤ B_i` for all `i < j` (R1′ holds on `Good(< max I)`, which contains these queue
constraints), then at every slot the window data hold and `Q_j ≤ B_j`. -/
theorem queue_and_data {A : ℕ → ℤ} {B : ℕ → ℝ} (hB : Monotone B)
    (h : ∀ j, (∀ i < j, (greedyQueue A i : ℝ) ≤ B i) → SlotInputs A (B j) j) :
    ∀ j, SlotData A (B j) j ∧ (greedyQueue A j : ℝ) ≤ B j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hprev : ∀ i < j, (greedyQueue A i : ℝ) ≤ B i := fun i hi => (ih i hi).2
    have hd := slotData_of_inputs (h j hprev)
    exact ⟨hd, queue_le_of_slotData hB hprev hd⟩

end Queue6

end
