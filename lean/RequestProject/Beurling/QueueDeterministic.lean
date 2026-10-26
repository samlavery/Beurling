module

public import RequestProject.Beurling.QueueBound75

/-!
# Theorem 6.6(ii): the deterministic part of the queue bound

The proof of Theorem 6.6(ii) has three deterministic steps, which are formalized here.

* **Short windows.** For a slot window `W` with `ℓ := ℓ_jit(I) ≥ 0` continuous slots in its
  integer hull `I`, the excess identity, the event `Fr(I)` (a), (b) and the drift bound `R1'` give
  `exc(W) ≤ -c'ℓ/L + √(16 M₁ L (ℓ + K_d)) + 16 M₁ L / 3 + (a ≥ 2 part) + K_d + 6`; maximising over
  `ℓ ≥ 0` gives `exc(W) ≤ B(x)` (`QueueDet.short_window_le_queueBound75`,
  `QueueDet.short_window_excess_le`).
* **Full blocks.** Inequality (76): with `L₀ = 48 M₁ L³ / c'²`, `L₀ - 1 ≤ K₀ ≤ L₀`, `M₁ ≥ L²`, the
  left side `c'(K₀ - 1)/L` exceeds the right side, so `exc(W) ≤ 0` on full blocks
  (`QueueDet.full_block_ineq`).
* **Lindley.** For the greedy queue, `Q_j ≤ max(Q_k + exc((k, j]), max_{k ≤ i ≤ j} exc((i, j]))`
  (`QueueDet.greedyQueue_le_split`), and the induction over slots that gives `Q_j ≤ B(s_j)` from the
  short-window and full-block bounds, with `B` non-decreasing (`QueueDet.greedyQueue_le_of_blocks`).
* `QueueDet.queue_bound_deterministic` : the three steps combined. From the per-window inputs
  (`ShortWindowData`, `FullBlockData`: the excess identity with the sandwich, the conclusions of
  the event `Fr(I)`, the drift bound `R1'`), the greedy queue satisfies `Q_j ≤ B j`.
-/

@[expose] public section

open Finset Real QueueBound Greedy

namespace QueueDet

/-- AM–GM in the form `√(b y) ≤ a y + b/(4a)` for `a > 0`, `b, y ≥ 0`. -/
lemma sqrt_mul_le_affine {a b y : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hy : 0 ≤ y) :
    Real.sqrt (b * y) ≤ a * y + b / (4 * a) := by
  have h0 : 0 ≤ a * y + b / (4 * a) := by positivity
  rw [Real.sqrt_le_left h0]
  have key : (a * y + b / (4 * a)) ^ 2 - b * y = (a * y - b / (4 * a)) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (a * y - b / (4 * a))]

/-- **Maximisation over `ℓ`**: `-c'ℓ/L + √(16 M₁ L (ℓ + K)) ≤ 4 M₁ L²/c' + c' K / L` for all
`ℓ ≥ 0` (`c', L > 0`, `M₁, K ≥ 0`). -/
theorem neg_lin_add_sqrt_le {c' L M1 K ℓ : ℝ} (hc : 0 < c') (hL : 0 < L) (hM : 0 ≤ M1)
    (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ) :
    -(c' * ℓ / L) + Real.sqrt (16 * M1 * L * (ℓ + K)) ≤ 4 * M1 * L ^ 2 / c' + c' * K / L := by
  have ha : 0 < c' / L := div_pos hc hL
  have h := sqrt_mul_le_affine ha (by positivity : (0 : ℝ) ≤ 16 * M1 * L)
    (by linarith : (0 : ℝ) ≤ ℓ + K)
  have e1 : 16 * M1 * L / (4 * (c' / L)) = 4 * M1 * L ^ 2 / c' := by field_simp; ring
  have e2 : c' / L * (ℓ + K) = c' * ℓ / L + c' * K / L := by field_simp
  rw [e1, e2] at h
  linarith

/-- **Short windows, after maximising over `ℓ`** (proof of Theorem 6.6(ii)): for `c' = 0.15`,
`K_d = 3`, `M₁ ≥ 1`, `L ≥ 10⁸`, `ℓ ≥ 0` and an `a ≥ 2` part at most `8 M₁ L (L/Λ + 1)`,
`-c'ℓ/L + √(16 M₁ L (ℓ + K_d)) + 16 M₁ L/3 + a₂ + K_d + 6 ≤ B` with `B` the right side of (75). -/
theorem short_window_le_queueBound75 {M1 L Λ ℓ a2 : ℝ} (hM : 1 ≤ M1) (hL : 10 ^ 8 ≤ L)
    (hℓ : 0 ≤ ℓ) (ha2 : a2 ≤ 8 * M1 * L * (L / Λ + 1)) :
    -(0.15 * ℓ / L) + Real.sqrt (16 * M1 * L * (ℓ + 3)) + 16 * M1 * L / 3 + a2 + 3 + 6 ≤
      queueBound75 M1 L Λ 0.15 3 := by
  have hL0 : 0 < L := by linarith
  have h := neg_lin_add_sqrt_le (c' := 0.15) (K := 3) (M1 := M1) (by norm_num) hL0
    (by linarith) (by norm_num) hℓ
  have hsmall : 0.15 * 3 / L ≤ 1 := by
    rw [div_le_one hL0]; linarith
  unfold queueBound75
  have hs : 0 ≤ Real.sqrt (M1 * L * (3 + 4)) := Real.sqrt_nonneg _
  set s := Real.sqrt (M1 * L * (3 + 4))
  set t := 8 * M1 * L * (L / Λ + 1)
  linarith

/-- **Short windows** (proof of Theorem 6.6(ii)). Let `W` be a slot window and `I` its integer hull
with `ℓ = ℓ_jit(I) ≥ 0` continuous slots. Suppose
* the excess identity with the sandwich: `exc(W) ≤ C_jit(I) - ℓ + 6`;
* `C_jit(I) = S₁ + S₂` (latest prime exactly once / at least squared);
* event `Fr(I)`(a), with `λ = 4L` and `v_ℓ = 2 M₁ (ℓ + K_d)`: `S₁ - Comp ≤ √(2 v_ℓ λ) + (4/3) M₁ λ`;
* the drift bound `R1'`: `Comp ≤ ℓ (1 - c'/L) + K_d`;
* event `Fr(I)`(b) with Corollary 6.12: `S₂ ≤ 8 M₁ L (L/Λ + 1)`.

Then `exc(W) ≤ B(x)`, the right side of (75) (`c' = 0.15`, `K_d = 3`, `M₁ ≥ 1`, `L ≥ 10⁸`). -/
theorem short_window_excess_le {M1 L Λ ℓ exc C S1 S2 Comp : ℝ} (hM : 1 ≤ M1)
    (hL : 10 ^ 8 ≤ L) (hℓ : 0 ≤ ℓ)
    (hexc : exc ≤ C - ℓ + 6) (hC : C = S1 + S2)
    (hS1 : S1 - Comp ≤ Real.sqrt (2 * (2 * M1 * (ℓ + 3)) * (4 * L)) + 4 / 3 * M1 * (4 * L))
    (hComp : Comp ≤ ℓ * (1 - 0.15 / L) + 3)
    (hS2 : S2 ≤ 8 * M1 * L * (L / Λ + 1)) :
    exc ≤ queueBound75 M1 L Λ 0.15 3 := by
  have hB := short_window_le_queueBound75 hM hL hℓ hS2
  have e : 2 * (2 * M1 * (ℓ + 3)) * (4 * L) = 16 * M1 * L * (ℓ + 3) := by ring
  rw [e] at hS1
  have e2 : ℓ * (1 - 0.15 / L) = ℓ - 0.15 * ℓ / L := by ring
  rw [e2] at hComp
  linarith

/-- **Inequality (76)** (full blocks, proof of Theorem 6.6(ii)). With `c' = 0.15`, `K_d = 3`,
`L ≥ 10⁸`, `Λ ≥ 10⁸`, `M₁ ≥ L²`, `L₀ = 48 M₁ L³ / c'²` and `L₀ - 1 ≤ K₀ ≤ L₀`:
`c'(K₀ - 1)/L ≥ √(16 M₁ L (K₀ + 4 + K_d)) + 16 M₁ L/3 + 8 M₁ L (L/Λ + 1) + L³ + K_d + 10`.
Hence `exc(W) ≤ 0` on full blocks. -/
theorem full_block_ineq {M1 L Λ K0 : ℝ} (hL : 10 ^ 8 ≤ L) (hΛ : 10 ^ 8 ≤ Λ)
    (hM : L ^ 2 ≤ M1) (hK1 : 48 * M1 * L ^ 3 / 0.15 ^ 2 - 1 ≤ K0)
    (hK2 : K0 ≤ 48 * M1 * L ^ 3 / 0.15 ^ 2) :
    Real.sqrt (16 * M1 * L * (K0 + 4 + 3)) + 16 * M1 * L / 3 + 8 * M1 * L * (L / Λ + 1) +
        L ^ 3 + 3 + 10 ≤ 0.15 * (K0 - 1) / L := by
  have hL0 : 0 < L := by linarith
  have hL2 : 10 ^ 16 ≤ L ^ 2 := by nlinarith
  have hM0 : 0 < M1 := by nlinarith
  set m := M1 * L ^ 2 with hm
  have hm0 : 0 < m := by positivity
  -- `M₁ L ≤ m / 10⁸`, `L³ ≤ M₁ L`
  have hML : M1 * L * 10 ^ 8 ≤ m := by
    rw [hm]; have := mul_le_mul_of_nonneg_left hL hM0.le; nlinarith
  have hL3 : L ^ 3 ≤ M1 * L := by
    have := mul_le_mul_of_nonneg_right hM hL0.le; nlinarith
  -- the square root term
  have hsqrt : Real.sqrt (16 * M1 * L * (K0 + 4 + 3)) ≤ 186 * m := by
    rw [Real.sqrt_le_left (by positivity)]
    have hK0 : K0 + 7 ≤ 48 * M1 * L ^ 3 / 0.15 ^ 2 + 7 := by linarith
    have h16 : 16 * M1 * L * (K0 + 4 + 3) ≤ 16 * M1 * L * (48 * M1 * L ^ 3 / 0.15 ^ 2 + 7) := by
      have : 0 ≤ 16 * M1 * L := by positivity
      nlinarith
    have e : 16 * M1 * L * (48 * M1 * L ^ 3 / 0.15 ^ 2 + 7) =
        (16 * 48 / 0.15 ^ 2) * m ^ 2 + 112 * (M1 * L) := by rw [hm]; ring
    rw [e] at h16
    have hML' : M1 * L ≤ m ^ 2 := by
      have : 1 ≤ m := by nlinarith
      nlinarith
    nlinarith
  -- the `a ≥ 2` part
  have hΛ0 : 0 < Λ := by linarith
  have hLΛ : L / Λ ≤ L / 10 ^ 8 := div_le_div_of_nonneg_left hL0.le (by norm_num) hΛ
  have ha2 : 8 * M1 * L * (L / Λ + 1) ≤ 8 * m / 10 ^ 8 + 8 * (M1 * L) := by
    have h1 : 8 * M1 * L * (L / Λ) ≤ 8 * M1 * L * (L / 10 ^ 8) :=
      mul_le_mul_of_nonneg_left hLΛ (by positivity)
    have e : 8 * M1 * L * (L / 10 ^ 8) = 8 * m / 10 ^ 8 := by rw [hm]; ring
    nlinarith
  -- the left side
  have hlhs : 0.15 * (K0 - 1) / L ≥ 320 * m - 1 := by
    have e : 0.15 * (48 * M1 * L ^ 3 / 0.15 ^ 2 - 2) / L = 320 * m - 0.3 / L := by
      rw [hm]; field_simp; ring
    have h1 : 0.15 * (48 * M1 * L ^ 3 / 0.15 ^ 2 - 2) / L ≤ 0.15 * (K0 - 1) / L := by
      apply div_le_div_of_nonneg_right _ hL0.le; linarith
    have h2 : 0.3 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have h1m : 1 ≤ m := by nlinarith
  nlinarith

/-- The window excess `exc((i, j]) = ∑_{l ∈ (i, j]} A_l - (j - i)`. -/
def exc (A : ℕ → ℤ) (i j : ℕ) : ℤ := ∑ l ∈ Ioc i j, A l - ((j : ℤ) - i)

/-- Additivity of the excess over slots: `exc((i, j]) = exc((i, k]) + exc((k, j])` for
`i ≤ k ≤ j`. -/
lemma exc_add (A : ℕ → ℤ) {i k j : ℕ} (hik : i ≤ k) (hkj : k ≤ j) :
    exc A i j = exc A i k + exc A k j := by
  unfold exc
  rw [← Finset.sum_Ioc_consecutive A hik hkj]
  ring

/-- Lindley's formula in terms of `exc`: `Q_j = max_{i ≤ j} exc((i, j])`. -/
lemma greedyQueue_eq_sup_exc (A : ℕ → ℤ) (j : ℕ) :
    greedyQueue A j = (range (j + 1)).sup' nonempty_range_add_one (fun i => exc A i j) :=
  greedyQueue_lindley A j

lemma exc_le_greedyQueue (A : ℕ → ℤ) {i j : ℕ} (hij : i ≤ j) : exc A i j ≤ greedyQueue A j := by
  rw [greedyQueue_eq_sup_exc]
  exact le_sup' (fun i => exc A i j) (mem_range.mpr (Nat.lt_succ_of_le hij))

/-- **The Lindley step** of the proof of Theorem 6.6(ii): for `k ≤ j`,
`Q_j ≤ max(Q_k + exc((k, j]), max_{k ≤ i ≤ j} exc((i, j]))`; in the form: if `Q_k + exc((k,j]) ≤ B`
and `exc((i, j]) ≤ B` for every `k ≤ i ≤ j`, then `Q_j ≤ B`. -/
theorem greedyQueue_le_split (A : ℕ → ℤ) {k j : ℕ} (hkj : k ≤ j) {B : ℤ}
    (hk : greedyQueue A k + exc A k j ≤ B) (hshort : ∀ i, k ≤ i → i ≤ j → exc A i j ≤ B) :
    greedyQueue A j ≤ B := by
  rw [greedyQueue_eq_sup_exc, sup'_le_iff]
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rcases le_or_gt k i with h | h
  · exact hshort i h hij
  · rw [exc_add A h.le hkj]
    have := exc_le_greedyQueue A h.le
    linarith

/-- **Theorem 6.6(ii), deterministic part (Lindley induction).** Let `B` be non-decreasing in the
slot index and nonnegative. Suppose that for every slot `j` either
* every window `(i, j]` has `exc((i, j]) ≤ B j` (no full block ends at `j`), or
* there is a `k < j` (the start of the last full block, `k'` of the paper) with
  `exc((k, j]) ≤ 0` (inequality (76)) and `exc((i, j]) ≤ B j` for every `k ≤ i ≤ j` (short
  windows).

Then the greedy queue satisfies `Q_j ≤ B j` for every `j`. -/
theorem greedyQueue_le_of_blocks (A : ℕ → ℤ) (B : ℕ → ℤ) (hB : Monotone B)
    (hblock : ∀ j, (∀ i, i ≤ j → exc A i j ≤ B j) ∨
      ∃ k < j, exc A k j ≤ 0 ∧ ∀ i, k ≤ i → i ≤ j → exc A i j ≤ B j) :
    ∀ j, greedyQueue A j ≤ B j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases hblock j with h | ⟨k, hkj, hk0, hshort⟩
    · rw [greedyQueue_eq_sup_exc, sup'_le_iff]
      intro i hi
      exact h i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    · have hQk := ih k hkj
      have hBk := hB hkj.le
      exact greedyQueue_le_split A hkj.le (by linarith) hshort

/-- `greedyQueue_le_of_blocks` with a real-valued bound `B` (the queue is integer-valued). -/
theorem greedyQueue_le_of_blocks_real (A : ℕ → ℤ) (B : ℕ → ℝ) (hB : Monotone B)
    (hblock : ∀ j, (∀ i, i ≤ j → (exc A i j : ℝ) ≤ B j) ∨
      ∃ k < j, exc A k j ≤ 0 ∧ ∀ i, k ≤ i → i ≤ j → (exc A i j : ℝ) ≤ B j) :
    ∀ j, (greedyQueue A j : ℝ) ≤ B j := by
  have hB' : Monotone (fun j => ⌊B j⌋) := fun a b hab => Int.floor_mono (hB hab)
  have key := greedyQueue_le_of_blocks A (fun j => ⌊B j⌋) hB' (fun j => by
    rcases hblock j with h | ⟨k, hkj, hk0, hshort⟩
    · exact Or.inl fun i hi => Int.le_floor.mpr (h i hi)
    · exact Or.inr ⟨k, hkj, hk0, fun i h1 h2 => Int.le_floor.mpr (hshort i h1 h2)⟩)
  intro j
  exact (Int.cast_le.mpr (key j)).trans (Int.floor_le _)

/-- The inputs of the short-window estimate for the window `(i, j]` (proof of Theorem 6.6(ii)),
with the bound `B(x)` of (75) at most `Bj`: see `short_window_excess_le`. -/
def ShortWindowData (A : ℕ → ℤ) (i j : ℕ) (Bj : ℝ) : Prop :=
  ∃ M1 L Λ ℓ C S1 S2 Comp : ℝ, 1 ≤ M1 ∧ 10 ^ 8 ≤ L ∧ 0 ≤ ℓ ∧
    (exc A i j : ℝ) ≤ C - ℓ + 6 ∧ C = S1 + S2 ∧
    S1 - Comp ≤ Real.sqrt (2 * (2 * M1 * (ℓ + 3)) * (4 * L)) + 4 / 3 * M1 * (4 * L) ∧
    Comp ≤ ℓ * (1 - 0.15 / L) + 3 ∧ S2 ≤ 8 * M1 * L * (L / Λ + 1) ∧
    queueBound75 M1 L Λ 0.15 3 ≤ Bj

/-- The inputs of the full-block estimate for the window `(k, j]` (proof of Theorem 6.6(ii)):
the same inputs as for a short window, with `K₀ - 1 ≤ ℓ ≤ K₀ + 4`, `L₀ = 48 M₁ L³/c'²`,
`L₀ - 1 ≤ K₀ ≤ L₀`, `M₁ ≥ L²` and `Λ ≥ 10⁸`. -/
def FullBlockData (A : ℕ → ℤ) (k j : ℕ) : Prop :=
  ∃ M1 L Λ ℓ K0 C S1 S2 Comp : ℝ, 10 ^ 8 ≤ L ∧ 10 ^ 8 ≤ Λ ∧ L ^ 2 ≤ M1 ∧
    48 * M1 * L ^ 3 / 0.15 ^ 2 - 1 ≤ K0 ∧ K0 ≤ 48 * M1 * L ^ 3 / 0.15 ^ 2 ∧
    K0 - 1 ≤ ℓ ∧ ℓ ≤ K0 + 4 ∧
    (exc A k j : ℝ) ≤ C - ℓ + 6 ∧ C = S1 + S2 ∧
    S1 - Comp ≤ Real.sqrt (2 * (2 * M1 * (ℓ + 3)) * (4 * L)) + 4 / 3 * M1 * (4 * L) ∧
    Comp ≤ ℓ * (1 - 0.15 / L) + 3 ∧ S2 ≤ 8 * M1 * L * (L / Λ + 1)

lemma ShortWindowData.le {A : ℕ → ℤ} {i j : ℕ} {Bj : ℝ} (h : ShortWindowData A i j Bj) :
    (exc A i j : ℝ) ≤ Bj := by
  obtain ⟨M1, L, Λ, ℓ, C, S1, S2, Comp, hM, hL, hℓ, hexc, hC, hS1, hComp, hS2, hB⟩ := h
  exact (short_window_excess_le hM hL hℓ hexc hC hS1 hComp hS2).trans hB

/-- **Full blocks have nonpositive excess** (proof of Theorem 6.6(ii), via (76)). -/
lemma FullBlockData.exc_nonpos {A : ℕ → ℤ} {k j : ℕ} (h : FullBlockData A k j) :
    exc A k j ≤ 0 := by
  obtain ⟨M1, L, Λ, ℓ, K0, C, S1, S2, Comp, hL, hΛ, hM, hK1, hK2, hℓ1, hℓ2, hexc, hC, hS1,
    hComp, hS2⟩ := h
  have h76 := full_block_ineq hL hΛ hM hK1 hK2
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ M1 := le_trans (sq_nonneg L) hM
  have e : 2 * (2 * M1 * (ℓ + 3)) * (4 * L) = 16 * M1 * L * (ℓ + 3) := by ring
  rw [e] at hS1
  have hsq : Real.sqrt (16 * M1 * L * (ℓ + 3)) ≤ Real.sqrt (16 * M1 * L * (K0 + 4 + 3)) := by
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 16 * M1 * L := by positivity
    nlinarith
  have hlin : 0.15 * (K0 - 1) / L ≤ 0.15 * ℓ / L := by
    apply div_le_div_of_nonneg_right _ hL0.le; linarith
  have e2 : ℓ * (1 - 0.15 / L) = ℓ - 0.15 * ℓ / L := by ring
  rw [e2] at hComp
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hreal : (exc A k j : ℝ) ≤ 0 := by
    set q := Real.sqrt (16 * M1 * L * (ℓ + 3))
    set q' := Real.sqrt (16 * M1 * L * (K0 + 4 + 3))
    set t := 8 * M1 * L * (L / Λ + 1)
    linarith
  exact_mod_cast hreal

/-- **Theorem 6.6(ii), deterministic part.** Let `A` be the composite arrivals, `Q` the greedy
queue (Lemma 3.7) and `B` a non-decreasing bound on slots (`B(s_j)` of (75), non-decreasing
because `M₁` is). Suppose that for every slot `j`, either every window `(i, j]` carries the
short-window inputs with `B(x) ≤ B j`, or there is a last full block `(k, j]`, `k < j`, carrying
the full-block inputs, and every window `(i, j]` with `k ≤ i` carries the short-window inputs.
Then `Q_j ≤ B j` for every slot `j`. -/
theorem queue_bound_deterministic (A : ℕ → ℤ) (B : ℕ → ℝ) (hB : Monotone B)
    (hdata : ∀ j, (∀ i, i ≤ j → ShortWindowData A i j (B j)) ∨
      ∃ k < j, FullBlockData A k j ∧ ∀ i, k ≤ i → i ≤ j → ShortWindowData A i j (B j)) :
    ∀ j, (greedyQueue A j : ℝ) ≤ B j :=
  greedyQueue_le_of_blocks_real A B hB fun j => by
    rcases hdata j with h | ⟨k, hkj, hfull, hshort⟩
    · exact Or.inl fun i hi => (h i hi).le
    · exact Or.inr ⟨k, hkj, hfull.exc_nonpos, fun i h1 h2 => (hshort i h1 h2).le⟩

end QueueDet

end
