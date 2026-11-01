module

public import RequestProject.Beurling.Queue6.Excess
public import RequestProject.Beurling.Queue6.Params

/-!
# Slot lengths and window lengths (proof of Theorem 6.6, "Windows")

For the constructed model (`ExcFacts`):

* `Queue6.ellI_le` : `ℓ_jit([a, b)) ≤ 1.01 |[a, b) ∩ [X₀, ∞)| + 1` (Corollary 5.40,
  `ℓ_jit(I) ≤ 1.01 |I ∩ [X₀, ∞)| + 1`);
* `Queue6.window_len` : a slot window `(i, j]` with `ℓ_jit ≤ K` has physical length
  `s_{j+1} - s_{i+1} ≤ 12.5 (K + 1) log s_{j+1}` (its continuous mass is at most `K + 1`, and
  `T'_cont ≥ 0.08/log`);
* `Queue6.slot_succ_le` : `s_{j+1} ≤ 3u` if `s_j < 2u`, `u ≥ X₀`.
-/

@[expose] public section

open Set Real Construction BModel SlotModel QueueDet

namespace Queue6

variable {X₀ : ℕ} {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

/-- **The number of continuous slots in a window** is at most `1.01 |I ∩ [X₀, ∞)| + 1`. -/
theorem ellI_le {a b : ℝ} (hab : a ≤ b) (hb : (X₀ : ℝ) ≤ b) :
    (ellI θ M U a b : ℝ) ≤ 1.01 * (b - max a X₀) + 1 := by
  classical
  set S := {l | ContSlot θ M U l ∧ a ≤ M.slot l ∧ M.slot l < b}
  have hfin : S.Finite := ellI_finite θ M U a b
  have hab' : 0 ≤ b - max a X₀ := by have := max_le hab hb; linarith
  rcases S.eq_empty_or_nonempty with h0 | hne
  · have : ellI θ M U a b = 0 := by
      unfold ellI; rw [show {l | ContSlot θ M U l ∧ a ≤ M.slot l ∧ M.slot l < b} = S from rfl,
        h0, Set.ncard_empty]
    rw [this]; push_cast; linarith
  · set T := hfin.toFinset
    have hTne : T.Nonempty := by
      obtain ⟨l, hl⟩ := hne; exact ⟨l, hfin.mem_toFinset.mpr hl⟩
    have hmem : ∀ l ∈ T, ContSlot θ M U l ∧ a ≤ M.slot l ∧ M.slot l < b := fun l hl =>
      hfin.mem_toFinset.mp hl
    have hm := cont_mass_card F T (fun l hl => (hmem l hl).1) hTne
    have h1 := hmem _ (T.max'_mem hTne)
    have h2 := hmem _ (T.min'_mem hTne)
    have hs2 := slot_gt F h2.1.1
    have hcup := F.win.cup _ _ hs2.le (M.slot_mono (T.min'_le_max' hTne))
    have hcard : ellI θ M U a b = T.card := by
      unfold ellI; exact Set.ncard_eq_toFinset_card _ hfin
    rw [hcard]
    have hmx : max a X₀ ≤ M.slot (T.min' hTne) := max_le h2.2.1 hs2.le
    linarith

/-- **The physical length of a slot window** with at most `K` continuous slots. -/
theorem window_len {i j K : ℕ} (hij : i ≤ j) (hK : ellW θ M U i j ≤ K) :
    M.slot (j + 1) - M.slot (i + 1) ≤ 12.5 * (K + 1) * Real.log (M.slot (j + 1)) := by
  have hm := mass_le F hij
  have hs1 := slot_gt F (Nat.le_add_left 1 i)
  have hss : M.slot (i + 1) ≤ M.slot (j + 1) := M.slot_mono (by omega)
  have hlow := F.lower _ _ hs1.le hss
  have hX1 : (1 : ℝ) < X₀ := by have := F.win.big; linarith
  have hlog : 0 < Real.log (M.slot (j + 1)) := Real.log_pos (by linarith)
  have hK' : (ellW θ M U i j : ℝ) ≤ K := by exact_mod_cast hK
  rw [div_le_iff₀ hlog] at hlow
  have : 0.08 * (M.slot (j + 1) - M.slot (i + 1)) ≤ (K + 1) * Real.log (M.slot (j + 1)) := by
    have := mul_le_mul_of_nonneg_right (hm.trans (by linarith : (ellW θ M U i j : ℝ) + 1 ≤ K + 1))
      hlog.le
    linarith
  linarith

omit F in
/-- `t ≥ 75 log t` for `t ≥ 10⁵`. -/
lemma log_le_div75 {t : ℝ} (ht : 10 ^ 5 ≤ t) : 75 * Real.log t ≤ t := by
  have h1 := sq_log_le (show (1 : ℝ) ≤ t by linarith)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  by_contra hc; push_neg at hc
  have h2 : t ^ 2 < (75 * Real.log t) ^ 2 := by
    have : 0 ≤ t := by linarith
    nlinarith
  nlinarith

omit F in
/-- `t ≥ 150 log t` for `t ≥ 5·10⁴`. -/
lemma log_le_div150 {t : ℝ} (ht : 50000 ≤ t) : 150 * Real.log t ≤ t := by
  have h1 := sq_log_le (show (1 : ℝ) ≤ t by linarith)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  by_contra hc; push_neg at hc
  have h2 : t ^ 2 < (150 * Real.log t) ^ 2 := by
    have : 0 ≤ t := by linarith
    nlinarith
  nlinarith

/-- **Slots are short**: if `s_j < 2u` (`j ≥ 1`, `X₀ ≤ u`) then `s_{j+1} ≤ 3u - 1`. -/
theorem slot_succ_le {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : (X₀ : ℝ) ≤ u)
    (hsj : M.slot j < 2 * u) : M.slot (j + 1) ≤ 3 * u - 1 := by
  classical
  have hK : ellW θ M U (j - 1) j ≤ 1 := by
    unfold ellW
    have : (Finset.Ioc (j - 1) j) = {j} := by
      ext l; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [this]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have h := window_len F (Nat.sub_le j 1) hK
  rw [Nat.sub_add_cancel hj] at h
  have hX := F.win.big
  have hs := slot_gt F (Nat.le_add_left 1 j)
  have h150 := log_le_div150 (t := M.slot (j + 1)) (by linarith)
  push_cast at h
  linarith

end Queue6

end
