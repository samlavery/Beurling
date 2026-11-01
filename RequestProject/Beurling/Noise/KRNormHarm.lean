module

public import RequestProject.Beurling.Noise.Lemma53Sums

/-!
# The harmonic bound `∑_{n ∈ 𝒩, n ≤ X} 1/n ≤ log X + B₁`, `B₁ = 1` (§5.1, "Constants")

Under (HBS) on `[1, Z]`, for `1 ≤ X ≤ Z`:

  `∑_{n ∈ 𝒩, n ≤ X} 1/n ≤ log X + 1`  (`BeurlingSystem.HBS.harm_le`).

The proof is the paper's: by partial summation (`GenPartial.sum_inv_window`) the difference
from `ℕ` is `E₁(X)/X + ∫ E₁(t) dt/t²`, `E₁ = N - ⌊·⌋`, which vanishes below `X₀⁻`; the boundary
term is at most `η₁`, and the integral, split into the dyadic blocks `[X 2^{-k-1}, X 2^{-k}]`,
is at most `η₁ log 2` by the definition of `η₁` (the block suprema of `|E₁(t)|/t ≤ ε₁(t)` sum to
at most `η₁`, `sum_blockSup_le`). For `ℕ`, `H_n ≤ log n + 2/3` for `n ≥ 6` (Mathlib's
`eulerMascheroniSeq'`), and `H_n ≤ 1 + log n` always.
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace BeurlingSystem

variable {P : BeurlingSystem}

/-! ## `ℕ` -/

lemma sum_Icc_inv_eq_harmonic (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 : ℝ) / n = (harmonic N : ℝ) := by
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

lemma natHarm_le_one_add_log {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n ≤ 1 + Real.log X := by
  rw [sum_Icc_inv_eq_harmonic]
  refine (harmonic_le_one_add_log _).trans ?_
  have h1 : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    have := Nat.floor_pos.mpr hX; omega)
  have := Real.log_le_log (by linarith) (Nat.floor_le (by linarith : (0 : ℝ) ≤ X))
  linarith

lemma natHarm_le_log_add {X : ℝ} (hX : 6 ≤ X) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n ≤ Real.log X + 2 / 3 := by
  rw [sum_Icc_inv_eq_harmonic]
  have h6 : 6 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hanti := Real.strictAnti_eulerMascheroniSeq'.antitone h6
  have h23 := Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hne : ⌊X⌋₊ ≠ 0 := by omega
  have e : Real.eulerMascheroniSeq' ⌊X⌋₊ = (harmonic ⌊X⌋₊ : ℝ) - Real.log ⌊X⌋₊ := by
    simp [Real.eulerMascheroniSeq', hne]
  have hl := Real.log_le_log (by exact_mod_cast (show 0 < ⌊X⌋₊ by omega))
    (Nat.floor_le (by linarith : (0 : ℝ) ≤ X))
  linarith

/-- Partial summation for `ℕ ∩ (1/2, X]`. -/
lemma natHarm_partial {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n =
      (⌊X⌋₊ : ℝ) / X + ∫ t in (1 / 2 : ℝ)..X, (⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hw := GenPartial.sum_inv_window (Icc 1 ⌊X⌋₊) (fun n : ℕ => (n : ℝ)) (Y := 1 / 2) (X := X)
    (by norm_num) (by linarith)
    (fun n hn => by
      have := (mem_Icc.mp hn).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith)))
    (fun n hn => by
      have := (mem_Icc.mp hn).1
      show (0 : ℝ) < (n : ℝ)
      exact_mod_cast (show 0 < n by omega))
  have hcard : ∀ t : ℝ, 0 ≤ t → t ≤ X →
      (((Icc 1 ⌊X⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t)).card : ℝ) = ⌊t⌋₊ := by
    intro t ht0 htX
    have : (Icc 1 ⌊X⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t) = Icc 1 ⌊t⌋₊ := by
      ext n
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, Nat.le_floor h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, h2.trans (Nat.floor_le_floor htX)⟩, ?_⟩
        exact (Nat.cast_le.mpr h2).trans (Nat.floor_le ht0)
    rw [this, Nat.card_Icc]; simp
  have hfil : (Icc 1 ⌊X⌋₊).filter (fun n : ℕ => (1 / 2 : ℝ) < n) = Icc 1 ⌊X⌋₊ := by
    apply Finset.filter_true_of_mem
    intro n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    linarith
  rw [hfil] at hw
  rw [hw, hcard X (by linarith) le_rfl, hcard (1 / 2) (by norm_num) (by linarith)]
  have h0 : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  rw [h0]
  simp only [Nat.cast_zero, zero_div, sub_zero]
  congr 1
  apply integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by linarith)] at ht
  simp only
  rw [hcard t (by linarith [ht.1]) ht.2]

/-- Partial summation for `𝒩 ∩ (1/2, X]`. -/
lemma harm_partial (P : BeurlingSystem) {X : ℝ} (hX : 1 ≤ X) :
    ∑ e ∈ P.elems X, 1 / P.val e = P.N X / X + ∫ t in (1 / 2 : ℝ)..X, P.N t / t ^ 2 := by
  have hw := GenPartial.sum_inv_window (P.elems X) P.val (Y := 1 / 2) (X := X) (by norm_num)
    (by linarith) (fun e he => (P.mem_elems).mp he) (fun e _ => P.val_pos e)
  have hcard : ∀ t, t ≤ X →
      (((P.elems X).filter (fun e => P.val e ≤ t)).card : ℝ) = P.N t := by
    intro t ht
    rw [N_eq_card]
    congr 2
    ext e; simp only [mem_filter, mem_elems]
    exact ⟨fun h => h.2, fun h => ⟨h.trans ht, h⟩⟩
  have hfil : (P.elems X).filter (fun e => (1 / 2 : ℝ) < P.val e) = P.elems X := by
    apply Finset.filter_true_of_mem
    intro e _; have := P.one_le_val e; linarith
  rw [hfil] at hw
  rw [hw, hcard X le_rfl, hcard (1 / 2) (by linarith), P.N_eq_zero (x := 1 / 2) (by norm_num)]
  simp only [zero_div, sub_zero]
  congr 1
  apply integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by linarith)] at ht
  simp only
  rw [hcard t ht.2]

lemma intervalIntegrable_E_div_sq (P : BeurlingSystem) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc a b) := by
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero _ (lt_of_lt_of_le ha ht.1).ne'
  have h1 : IntervalIntegrable (fun t => P.N t - (⌊t⌋₊ : ℝ)) volume a b :=
    (P.N_mono.intervalIntegrable).sub
      (Monotone.intervalIntegrable fun s t h => by exact_mod_cast Nat.floor_le_floor h)
  have := h1.mul_continuousOn hc
  simpa [div_eq_mul_inv] using this

/-- The difference from `ℕ`: `∑_{𝒩, n ≤ X} 1/n - H(X) = E₁(X)/X + ∫ E₁(t) dt/t²`. -/
lemma harm_sub_natHarm (P : BeurlingSystem) {X : ℝ} (hX : 1 ≤ X) :
    ∑ e ∈ P.elems X, 1 / P.val e - ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n =
      (P.N X - ⌊X⌋₊) / X + ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 := by
  rw [harm_partial P hX, natHarm_partial hX]
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 / 2) X) := by
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact pow_ne_zero _ (by linarith [ht.1])
  have hi1 : IntervalIntegrable (fun t => P.N t / t ^ 2) volume (1 / 2) X := by
    have := (P.N_mono.intervalIntegrable (μ := volume) (a := 1 / 2) (b := X)).mul_continuousOn hc
    simpa [div_eq_mul_inv] using this
  have hi2 : IntervalIntegrable (fun t => (⌊t⌋₊ : ℝ) / t ^ 2) volume (1 / 2) X := by
    have hm : Monotone (fun t : ℝ => (⌊t⌋₊ : ℝ)) := fun s t h => by
      simp only; exact_mod_cast Nat.floor_le_floor h
    have := (hm.intervalIntegrable (μ := volume) (a := 1 / 2) (b := X)).mul_continuousOn hc
    simpa [div_eq_mul_inv] using this
  have : ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 =
      (∫ t in (1 / 2 : ℝ)..X, P.N t / t ^ 2) - ∫ t in (1 / 2 : ℝ)..X, (⌊t⌋₊ : ℝ) / t ^ 2 := by
    rw [← integral_sub hi1 hi2]
    congr 1; funext t; ring
  rw [this]; ring

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- `φ(t) = |E₁(t)|/t`. -/
noncomputable def phiE (P : BeurlingSystem) (t : ℝ) : ℝ := |P.N t - (⌊t⌋₊ : ℝ)| / t

/-- The block `[X 2^{-k-1}, X 2^{-k}] ∩ [X₀⁻, ∞)`. -/
def blk (X X0m : ℝ) (k : ℕ) : Set ℝ :=
  {t | X / 2 ^ (k + 1) ≤ t ∧ t ≤ X / 2 ^ k ∧ X0m ≤ t}

/-- The block supremum of `φ` (`0` for an empty block). -/
noncomputable def bsup (P : BeurlingSystem) (X X0m : ℝ) (k : ℕ) : ℝ :=
  sSup (insert 0 (phiE P '' blk X X0m k))

lemma phiE_le (h : P.HBS X0m Z η1 η2 ε1) {t : ℝ} (ht : 0 < t) (htZ : t ≤ Z) :
    phiE P t ≤ η1 := by
  unfold phiE
  rw [div_le_iff₀ ht]
  exact h.abs_E_le ht.le htZ

lemma bdd_blk (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) (k : ℕ) :
    BddAbove (insert 0 (phiE P '' blk X X0m k)) := by
  refine ⟨η1, ?_⟩
  rintro y (rfl | ⟨t, ⟨h1, h2, h3⟩, rfl⟩)
  · exact h.eta1_nonneg
  · have hX := h.X0m_pos
    have hX2 : X / 2 ^ k ≤ X := by
      have : (0 : ℝ) ≤ X := by
        have : (0 : ℝ) < X / 2 ^ k := by linarith
        by_contra hc; push_neg at hc
        have : X / 2 ^ k < 0 := div_neg_of_neg_of_pos hc (by positivity)
        linarith
      exact div_le_self this (one_le_pow₀ (by norm_num))
    exact h.phiE_le (by linarith) (by linarith)

lemma le_bsup (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) {k : ℕ} {t : ℝ}
    (ht : t ∈ blk X X0m k) : phiE P t ≤ bsup P X X0m k :=
  le_csSup (h.bdd_blk hXZ k) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩)

lemma bsup_nonneg (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) (k : ℕ) :
    0 ≤ bsup P X X0m k :=
  le_csSup (h.bdd_blk hXZ k) (Set.mem_insert _ _)

/-- **The block suprema sum to at most `η₁`** (the definition (24) of `η₁`). -/
lemma sum_blockSup_le (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) (K : ℕ) :
    ∑ k ∈ range K, bsup P X X0m k ≤ η1 := by
  classical
  apply le_of_forall_pos_lt_add
  intro δ hδ
  set K1 := (range K).filter (fun k => (blk X X0m k).Nonempty)
  have hsplit : ∑ k ∈ range K, bsup P X X0m k = ∑ k ∈ K1, bsup P X X0m k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [Set.not_nonempty_iff_eq_empty] at hk
      unfold bsup; rw [hk, Set.image_empty]; simp
  rw [hsplit]
  have hK1 : (0 : ℝ) < K1.card + 1 := by positivity
  set δ' := δ / (K1.card + 1)
  have hδ' : 0 < δ' := div_pos hδ hK1
  -- choose near-maximal points
  have hex : ∀ k ∈ K1, ∃ t ∈ blk X X0m k, bsup P X X0m k - δ' < phiE P t := by
    intro k hk
    obtain ⟨t0, ht0⟩ := (Finset.mem_filter.mp hk).2
    have hlt : bsup P X X0m k - δ' < bsup P X X0m k := by linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty _ _) hlt
    rcases hy with rfl | ⟨t, ht, rfl⟩
    · refine ⟨t0, ht0, lt_of_lt_of_le hylt ?_⟩
      unfold phiE
      have : 0 < t0 := lt_of_lt_of_le h.X0m_pos ht0.2.2
      positivity
    · exact ⟨t, ht, hylt⟩
  choose! w hw hwlt using hex
  have hsum := h.eta1 X K1 w (by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hw k hk
    refine ⟨h1, h2, h3, ?_⟩
    have : X / 2 ^ k ≤ X := by
      have hX0 : 0 ≤ X := by
        have : (0 : ℝ) < X / 2 ^ k := by linarith [h.X0m_pos]
        by_contra hc; push_neg at hc
        have : X / 2 ^ k < 0 := div_neg_of_neg_of_pos hc (by positivity)
        linarith
      exact div_le_self hX0 (one_le_pow₀ (by norm_num))
    linarith)
  have hphi : ∀ k ∈ K1, phiE P (w k) ≤ ε1 (w k) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hw k hk
    have hw0 : 0 < w k := lt_of_lt_of_le h.X0m_pos h3
    have hwX : w k ≤ X := by
      have hX0 : 0 ≤ X := by
        by_contra hc; push_neg at hc
        have : X / 2 ^ k < 0 := div_neg_of_neg_of_pos hc (by positivity)
        linarith
      exact h2.trans (div_le_self hX0 (one_le_pow₀ (by norm_num)))
    unfold phiE
    rw [div_le_iff₀ hw0]
    exact h.err (w k) h3 (hwX.trans hXZ)
  calc ∑ k ∈ K1, bsup P X X0m k < ∑ k ∈ K1, (phiE P (w k) + δ') + δ' := by
        have : ∑ k ∈ K1, bsup P X X0m k ≤ ∑ k ∈ K1, (phiE P (w k) + δ') :=
          Finset.sum_le_sum fun k hk => by linarith [hwlt k hk]
        linarith
    _ = ∑ k ∈ K1, phiE P (w k) + (K1.card + 1) * δ' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ η1 + δ := by
        have : (K1.card + 1) * δ' = δ := by
          simp only [δ']; field_simp
        rw [this]
        linarith [Finset.sum_le_sum hphi]

/-- On a block, `E₁(t)/t² ≤ M_k/t`. -/
lemma E_div_sq_le (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) {k : ℕ} {t : ℝ}
    (ht1 : X / 2 ^ (k + 1) ≤ t) (ht2 : t ≤ X / 2 ^ k) (ht0 : 0 < t) :
    (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 ≤ bsup P X X0m k / t := by
  have htX : t ≤ X := by
    have hX0 : 0 ≤ X := by
      by_contra hc; push_neg at hc
      have : X / 2 ^ k < 0 := div_neg_of_neg_of_pos hc (by positivity)
      linarith
    exact ht2.trans (div_le_self hX0 (one_le_pow₀ (by norm_num)))
  rcases lt_or_ge t X0m with hlt | hge
  · rw [h.E_zero ht0.le hlt (htX.trans hXZ), zero_div]
    exact div_nonneg (h.bsup_nonneg hXZ k) ht0.le
  · have hb := h.le_bsup hXZ (k := k) (t := t) ⟨ht1, ht2, hge⟩
    unfold phiE at hb
    rw [div_le_iff₀ ht0] at hb
    rw [div_le_div_iff₀ (by positivity) ht0]
    have := le_abs_self (P.N t - (⌊t⌋₊ : ℝ))
    nlinarith

/-- **The integral term**: `∫_{1/2}^X E₁(t) dt/t² ≤ η₁ log 2`. -/
lemma integral_E_le (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) :
    ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 ≤ η1 * Real.log 2 := by
  -- the number of blocks
  obtain ⟨K, hK⟩ : ∃ K : ℕ, X / 2 ^ K ≤ 1 / 2 := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * X) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, ?_⟩
    rw [div_le_iff₀ (by positivity)]; linarith
  set a : ℕ → ℝ := fun k => X / 2 ^ (K - k)
  have hX0 : 0 < X := by linarith
  have ha0 : ∀ k, 0 < a k := fun k => by simp only [a]; positivity
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    simp only [a]
    apply div_le_div_of_nonneg_left hX0.le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hint : ∀ k < K, IntervalIntegrable (fun t => (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2) volume
      (a k) (a (k + 1)) := fun k _ => intervalIntegrable_E_div_sq P (ha0 k) (hmono k)
  have haK : a K = X := by simp [a]
  have ha0' : a 0 = X / 2 ^ K := by simp [a]
  -- the part `[a 0, 1/2]` vanishes
  have hlow : ∫ t in a 0..(1 / 2 : ℝ), (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by rw [ha0']; exact hK)] at ht
      simp only
      have ht0 : 0 < t := lt_of_lt_of_le (ha0 0) ht.1
      have htX : t < X0m := by
        have := h.X0m_ge; norm_num at this; linarith [ht.2]
      rw [h.E_zero ht0.le htX (by linarith [ht.2]), zero_div]
  have hsplit : ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 =
      ∑ k ∈ range K, ∫ t in a k..a (k + 1), (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 := by
    rw [sum_integral_adjacent_intervals hint, haK]
    rw [← integral_add_adjacent_intervals (b := (1 / 2 : ℝ))
      (intervalIntegrable_E_div_sq P (ha0 0) (by rw [ha0']; exact hK))
      (intervalIntegrable_E_div_sq P (by norm_num) (by linarith)), hlow, zero_add]
  rw [hsplit]
  have hblock : ∀ k ∈ range K, ∫ t in a k..a (k + 1), (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 ≤
      bsup P X X0m (K - 1 - k) * Real.log 2 := by
    intro k hk
    have hkK := mem_range.mp hk
    have e1 : a (k + 1) = X / 2 ^ (K - 1 - k) := by
      simp only [a]; congr 2; omega
    have e2 : a k = X / 2 ^ (K - 1 - k + 1) := by
      simp only [a]; congr 2; omega
    calc ∫ t in a k..a (k + 1), (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2
        ≤ ∫ t in a k..a (k + 1), bsup P X X0m (K - 1 - k) / t := by
          apply integral_mono_on (hmono k) (hint k hkK)
          · apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.div continuousOn_const continuousOn_id
            intro t ht
            rw [Set.uIcc_of_le (hmono k)] at ht
            exact (lt_of_lt_of_le (ha0 k) ht.1).ne'
          · intro t ht
            have ht0 : 0 < t := lt_of_lt_of_le (ha0 k) ht.1
            exact h.E_div_sq_le hXZ (by rw [← e2]; exact ht.1) (by rw [← e1]; exact ht.2) ht0
      _ = bsup P X X0m (K - 1 - k) * Real.log 2 := by
          rw [show (fun t : ℝ => bsup P X X0m (K - 1 - k) / t) =
              fun t => bsup P X X0m (K - 1 - k) * t⁻¹ by funext t; ring,
            intervalIntegral.integral_const_mul, integral_inv_of_pos (ha0 k) (ha0 (k + 1))]
          congr 2
          rw [e1, e2, pow_succ]
          field_simp
  calc ∑ k ∈ range K, ∫ t in a k..a (k + 1), (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2
      ≤ ∑ k ∈ range K, bsup P X X0m (K - 1 - k) * Real.log 2 := Finset.sum_le_sum hblock
    _ = (∑ k ∈ range K, bsup P X X0m k) * Real.log 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact Finset.sum_range_reflect (bsup P X X0m) K
    _ ≤ η1 * Real.log 2 :=
        mul_le_mul_of_nonneg_right (h.sum_blockSup_le hXZ K) (Real.log_nonneg (by norm_num))

/-- **The harmonic bound** (§5.1, "Constants", `B₁ = 1`): under (HBS) on `[1, Z]`, for every
`1 ≤ X ≤ Z`, `∑_{n ∈ 𝒩, n ≤ X} 1/n ≤ log X + 1`. -/
theorem harm_le (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) :
    ∑ e ∈ P.elems X, 1 / P.val e ≤ Real.log X + 1 := by
  have hd := harm_sub_natHarm P hX
  rcases lt_or_ge X X0m with hlt | hge
  · -- below `X₀⁻` the system is `ℕ`
    have hE0 : (P.N X - ⌊X⌋₊) / X = 0 := by
      rw [h.E_zero (by linarith) hlt hXZ, zero_div]
    have hI0 : ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 = 0 := by
      rw [integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        simp only
        rw [h.E_zero (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hlt) (ht.2.trans hXZ), zero_div]
    rw [hE0, hI0, add_zero] at hd
    have := natHarm_le_one_add_log hX
    linarith
  · have hX6 : 6 ≤ X := by have := h.X0m_ge; norm_num at this; linarith
    have h1 := natHarm_le_log_add hX6
    have h2 : (P.N X - ⌊X⌋₊) / X ≤ η1 := by
      rw [div_le_iff₀ (by linarith)]
      have := h.abs_E_le (by linarith) hXZ
      linarith [le_abs_self (P.N X - ⌊X⌋₊)]
    have h3 := h.integral_E_le hX hXZ
    have hl : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hη := h.eta1_le
    have hη0 := h.eta1_nonneg
    nlinarith

end HBS

end BeurlingSystem

end
