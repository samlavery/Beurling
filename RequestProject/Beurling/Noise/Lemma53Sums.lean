module

public import RequestProject.Beurling.Noise.BSDefs
public import RequestProject.BSCert.Finite.SmallCert

/-!
# Lemma 5.3: dyadic harmonic sums of the system, and Hildebrand's identity

* `GenPartial.sum_inv_window`: partial summation for `∑_{Y < a_i ≤ X} 1/a_i`;
* `BeurlingSystem.harmBlock_sub_harmWin`: `∑_{𝒩 ∩ (Y,2Y]} 1/n - ∑_{ℕ ∩ (Y,2Y]} 1/n` is
  `[E₁(v)/v]_Y^{2Y} + ∫_Y^{2Y} E₁(v) dv/v²`, `E₁ = N - ⌊·⌋`;
* `BeurlingSystem.HBS.smallHeights`: the small-height bound in the proof of Lemma 5.3,
  `∑_{n ∈ 𝒩 ∩ (Y, 2Y]} 1/n ≤ C₀ = 0.70` for `Y ≥ 72`; also `≤ 5/6` on `[1, 72)` and `≤ 1` always;
* `BeurlingSystem.hildebrand`: **Hildebrand's identity**
  `∑_{n ∈ (Y,2Y], P⁺(n) ≤ z} log n / n = ∑_{p ≤ z, k ≥ 1} (log p / p^k) v(Y/p^k, z)`.
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace GenPartial

lemma intervalIntegrable_indicator_inv_sq {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable ((Set.Ici c).indicator (fun t : ℝ => 1 / t ^ 2)) volume a b := by
  have hc : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero _ (lt_of_lt_of_le ha ht.1).ne'
  rw [intervalIntegrable_iff] at hc ⊢
  exact hc.indicator measurableSet_Ici

lemma integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / t ^ 2 = 1 / a - 1 / b := by
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    have := (hasDerivAt_inv ht0).neg
    convert! this using 1
    · ext s; simp [one_div]
    · field_simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero _ (lt_of_lt_of_le ha ht.1).ne'

/-- `∫_Y^X 1_{t ≥ c} dt/t² = 1/max(c, Y) - 1/X` for `c ≤ X`. -/
lemma integral_indicator_inv_sq {c Y X : ℝ} (hY : 0 < Y) (hYX : Y ≤ X) (hcX : c ≤ X) :
    ∫ t in Y..X, (Set.Ici c).indicator (fun t : ℝ => 1 / t ^ 2) t =
      1 / max c Y - 1 / X := by
  set m := max c Y
  have hYm : Y ≤ m := le_max_right _ _
  have hmX : m ≤ X := max_le hcX hYX
  rw [← integral_add_adjacent_intervals (b := m)
    (intervalIntegrable_indicator_inv_sq hY hYm)
    (intervalIntegrable_indicator_inv_sq (by linarith) hmX)]
  have h1 : ∫ t in Y..m, (Set.Ici c).indicator (fun t : ℝ => 1 / t ^ 2) t = 0 := by
    rw [integral_of_le hYm, setIntegral_indicator measurableSet_Ici]
    apply setIntegral_measure_zero
    apply measure_mono_null (t := {m})
    · intro t ht; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici] at ht
      apply le_antisymm ht.1.2
      rcases le_total c Y with h | h
      · have : m = Y := max_eq_right h
        rw [this]; exact ht.1.1.le
      · have : m = c := max_eq_left h
        rw [this]; exact ht.2
    · exact Real.volume_singleton
  have h2 : ∫ t in m..X, (Set.Ici c).indicator (fun t : ℝ => 1 / t ^ 2) t =
      ∫ t in m..X, 1 / t ^ 2 := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hmX] at ht
    simp [Set.indicator_of_mem (show t ∈ Set.Ici c from (le_max_left c Y).trans ht.1)]
  rw [h1, h2, integral_inv_sq (by linarith) hmX]
  ring

/-- **Partial summation for `∑ 1/a_i`**: for points `0 < a_i ≤ X` and `0 < Y ≤ X`,
`∑_{Y < a_i} 1/a_i = N(X)/X - N(Y)/Y + ∫_Y^X N(t) dt/t²`, `N(t) = #{i : a_i ≤ t}`. -/
theorem sum_inv_window {ι : Type*} (s : Finset ι) (a : ι → ℝ) {Y X : ℝ} (hY : 0 < Y)
    (hYX : Y ≤ X) (hs : ∀ i ∈ s, a i ≤ X) (hpos : ∀ i ∈ s, 0 < a i) :
    ∑ i ∈ s.filter (fun i => Y < a i), 1 / a i =
      ((s.filter (fun i => a i ≤ X)).card : ℝ) / X - ((s.filter (fun i => a i ≤ Y)).card : ℝ) / Y
        + ∫ t in Y..X, ((s.filter (fun i => a i ≤ t)).card : ℝ) / t ^ 2 := by
  have hfun : (fun t : ℝ => ((s.filter (fun i => a i ≤ t)).card : ℝ) / t ^ 2) =
      fun t => ∑ i ∈ s, (Set.Ici (a i)).indicator (fun t : ℝ => 1 / t ^ 2) t := by
    funext t
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : a i ≤ t
    · simp [h, Set.indicator_of_mem (show t ∈ Set.Ici (a i) from h)]
    · simp [h, Set.indicator_of_notMem (show t ∉ Set.Ici (a i) from h)]
  rw [hfun, integral_finset_sum (fun i _ => intervalIntegrable_indicator_inv_sq hY hYX)]
  rw [Finset.sum_congr rfl (fun i hi => integral_indicator_inv_sq hY hYX (hs i hi))]
  simp only [Finset.card_filter, Nat.cast_sum, Finset.sum_div, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hX : a i ≤ X := hs i hi
  by_cases h : Y < a i
  · have hm : max (a i) Y = a i := max_eq_left h.le
    simp [h, hX, not_le.mpr h, hm]
  · push_neg at h
    have hm : max (a i) Y = Y := max_eq_right h
    simp [not_lt.mpr h, hX, h, hm]

end GenPartial

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `harmWin` as a sum over `Icc 1 ⌊2Y⌋`. -/
lemma harmWin_eq_Icc {Y : ℝ} (hY : 0 ≤ Y) :
    BSCert.FiniteN.harmWin Y =
      ∑ n ∈ (Icc 1 ⌊2 * Y⌋₊).filter (fun n : ℕ => Y < n), (1 : ℝ) / n := by
  unfold BSCert.FiniteN.harmWin
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, by omega⟩, h2⟩
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at h2; linarith
    · exact h
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h3⟩

/-- `harmWin` by partial summation. -/
lemma harmWin_partial {Y : ℝ} (hY : 0 < Y) :
    BSCert.FiniteN.harmWin Y = (⌊2 * Y⌋₊ : ℝ) / (2 * Y) - (⌊Y⌋₊ : ℝ) / Y +
      ∫ t in Y..2 * Y, (⌊t⌋₊ : ℝ) / t ^ 2 := by
  rw [harmWin_eq_Icc hY.le]
  have hX : 0 ≤ 2 * Y := by linarith
  have hcard : ∀ t, 0 ≤ t → t ≤ 2 * Y →
      (((Icc 1 ⌊2 * Y⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t)).card : ℝ) = ⌊t⌋₊ := by
    intro t ht0 htX
    have : (Icc 1 ⌊2 * Y⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t) = Icc 1 ⌊t⌋₊ := by
      ext n; simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (Nat.floor_le_floor htX)⟩, (Nat.le_floor_iff ht0).mp h2⟩
    rw [this, Nat.card_Icc, add_tsub_cancel_right]
  rw [GenPartial.sum_inv_window (Icc 1 ⌊2 * Y⌋₊) (fun n : ℕ => (n : ℝ)) (X := 2 * Y) hY
    (by linarith)]
  · rw [hcard _ hX le_rfl, hcard _ hY.le (by linarith)]
    congr 1
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [hcard t (by linarith [ht.1]) ht.2]
  · intro n hn; rw [mem_Icc] at hn; exact (Nat.le_floor_iff hX).mp hn.2
  · intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.1

/-- `harmBlock` by partial summation. -/
lemma harmBlock_partial {Y : ℝ} (hY : 0 < Y) :
    P.harmBlock Y = P.N (2 * Y) / (2 * Y) - P.N Y / Y +
      ∫ t in Y..2 * Y, P.N t / t ^ 2 := by
  unfold harmBlock
  have hcard : ∀ t, t ≤ 2 * Y →
      (((P.elems (2 * Y)).filter (fun e => P.val e ≤ t)).card : ℝ) = P.N t := by
    intro t ht
    rw [N_eq_card]
    congr 2
    ext e; simp only [mem_filter, mem_elems]
    exact ⟨fun h => h.2, fun h => ⟨h.trans ht, h⟩⟩
  rw [GenPartial.sum_inv_window (P.elems (2 * Y)) P.val (X := 2 * Y) hY (by linarith)
    (fun e he => (P.mem_elems).mp he) (fun e _ => P.val_pos e)]
  rw [hcard _ le_rfl, hcard _ (by linarith)]
  congr 1
  apply integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by linarith)] at ht
  simp only
  rw [hcard t ht.2]

/-- `∑_{𝒩 ∩ (Y,2Y]} 1/n - ∑_{ℕ ∩ (Y,2Y]} 1/n = [E₁(v)/v]_Y^{2Y} + ∫_Y^{2Y} E₁(v) dv/v²`. -/
lemma harmBlock_sub_harmWin {Y : ℝ} (hY : 0 < Y) :
    P.harmBlock Y - BSCert.FiniteN.harmWin Y =
      (P.N (2 * Y) - ⌊2 * Y⌋₊) / (2 * Y) - (P.N Y - ⌊Y⌋₊) / Y +
        ∫ t in Y..2 * Y, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 := by
  rw [P.harmBlock_partial hY, harmWin_partial hY]
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc Y (2 * Y)) := by
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact pow_ne_zero _ (lt_of_lt_of_le hY ht.1).ne'
  have hi1 : IntervalIntegrable (fun t => P.N t / t ^ 2) volume Y (2 * Y) := by
    have := (P.N_mono.intervalIntegrable (μ := volume) (a := Y) (b := 2 * Y)).mul_continuousOn hc
    simpa [div_eq_mul_inv] using this
  have hi2 : IntervalIntegrable (fun t => (⌊t⌋₊ : ℝ) / t ^ 2) volume Y (2 * Y) := by
    have hm : Monotone (fun t : ℝ => (⌊t⌋₊ : ℝ)) := fun s t h => by
      simp only; exact_mod_cast Nat.floor_le_floor h
    have := (hm.intervalIntegrable (μ := volume) (a := Y) (b := 2 * Y)).mul_continuousOn hc
    simpa [div_eq_mul_inv] using this
  have : ∫ t in Y..2 * Y, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 =
      (∫ t in Y..2 * Y, P.N t / t ^ 2) - ∫ t in Y..2 * Y, (⌊t⌋₊ : ℝ) / t ^ 2 := by
    rw [← integral_sub hi1 hi2]
    congr 1; funext t; ring
  rw [this]
  ring

lemma harmBlock_nonneg (Y : ℝ) : 0 ≤ P.harmBlock Y :=
  Finset.sum_nonneg fun e _ => by have := P.val_pos e; positivity

/-- `v(log Y, z) ≤ ∑_{𝒩 ∩ (Y,2Y]} 1/n`. -/
lemma vSmooth_le_harmBlock (Y z : ℝ) : P.vSmooth Y z ≤ P.harmBlock Y := by
  unfold vSmooth harmBlock
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he; simp only [mem_filter] at he ⊢; exact ⟨he.1, he.2.1⟩
  · intro e _ _; have := P.val_pos e; positivity

lemma vSmooth_nonneg (Y z : ℝ) : 0 ≤ P.vSmooth Y z :=
  Finset.sum_nonneg fun e _ => by have := P.val_pos e; positivity

/-- For `2Y < 1` there is no element in `(Y, 2Y]`. -/
lemma harmBlock_eq_zero {Y : ℝ} (hY : 2 * Y < 1) : P.harmBlock Y = 0 := by
  unfold harmBlock
  rw [Finset.sum_eq_zero]
  intro e he
  simp only [mem_filter, mem_elems] at he
  linarith [P.one_le_val e]

namespace HBS

variable {P} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- Below `X₀⁻` the window sums are those of `ℕ`. -/
lemma harmBlock_eq_harmWin (h : P.HBS X0m Z η1 η2 ε1) {Y : ℝ} (hY : 0 < Y)
    (h2Y : 2 * Y < X0m) (hZ : 2 * Y ≤ Z) : P.harmBlock Y = BSCert.FiniteN.harmWin Y := by
  have hdiff := P.harmBlock_sub_harmWin hY
  have h0 : ∀ t, 0 ≤ t → t ≤ 2 * Y → P.N t - (⌊t⌋₊ : ℝ) = 0 := fun t ht0 ht =>
    h.E_zero ht0 (lt_of_le_of_lt ht h2Y) (ht.trans hZ)
  have hint : ∫ t in Y..2 * Y, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [h0 t (by linarith [ht.1]) ht.2, zero_div]
  rw [hint, h0 _ (by linarith) le_rfl, h0 _ hY.le (by linarith)] at hdiff
  simp at hdiff
  linarith

/-- Above: `|∑_{𝒩 ∩ (Y,2Y]} 1/n - ∑_{ℕ ∩ (Y,2Y]} 1/n| ≤ (2 + log 2) η₁`. -/
lemma harmBlock_le_harmWin_add (h : P.HBS X0m Z η1 η2 ε1) {Y : ℝ} (hY : 0 < Y)
    (hZ : 2 * Y ≤ Z) :
    P.harmBlock Y ≤ BSCert.FiniteN.harmWin Y + (2 + Real.log 2) * η1 := by
  have hdiff := P.harmBlock_sub_harmWin hY
  have hE : ∀ t, 0 ≤ t → t ≤ 2 * Y → |P.N t - (⌊t⌋₊ : ℝ)| ≤ η1 * t := fun t ht0 ht =>
    h.abs_E_le ht0 (ht.trans hZ)
  have hη := h.eta1_nonneg
  have b1 : (P.N (2 * Y) - ⌊2 * Y⌋₊) / (2 * Y) ≤ η1 := by
    rw [div_le_iff₀ (by linarith)]
    have := hE (2 * Y) (by linarith) le_rfl
    linarith [le_abs_self (P.N (2 * Y) - ⌊2 * Y⌋₊)]
  have b2 : -((P.N Y - ⌊Y⌋₊) / Y) ≤ η1 := by
    rw [neg_le, neg_le_iff_add_nonneg, ← sub_nonneg]
    rw [show (P.N Y - ⌊Y⌋₊) / Y + η1 - 0 = ((P.N Y - ⌊Y⌋₊) + η1 * Y) / Y by field_simp; ring]
    apply div_nonneg _ hY.le
    have := hE Y hY.le (by linarith)
    linarith [neg_abs_le (P.N Y - ⌊Y⌋₊)]
  have b3 : ∫ t in Y..2 * Y, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 ≤ η1 * Real.log 2 := by
    have hle : ∫ t in Y..2 * Y, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 ≤ ∫ t in Y..2 * Y, η1 / t := by
      apply integral_mono_on (by linarith)
      · have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc Y (2 * Y)) := by
          apply ContinuousOn.inv₀ (continuousOn_pow 2)
          intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact pow_ne_zero _ (lt_of_lt_of_le hY ht.1).ne'
        have h1 : IntervalIntegrable (fun t => P.N t - (⌊t⌋₊ : ℝ)) volume Y (2 * Y) :=
          (P.N_mono.intervalIntegrable).sub
            (Monotone.intervalIntegrable fun s t h => by exact_mod_cast Nat.floor_le_floor h)
        have := h1.mul_continuousOn hc
        simpa [div_eq_mul_inv] using this
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact (lt_of_lt_of_le hY ht.1).ne'
      · intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hY ht.1
        have := hE t ht0.le ht.2
        rw [div_le_div_iff₀ (by positivity) ht0]
        have := le_abs_self (P.N t - (⌊t⌋₊ : ℝ))
        nlinarith
    have hint : ∫ t in Y..2 * Y, η1 / t = η1 * Real.log 2 := by
      rw [show (fun t : ℝ => η1 / t) = fun t => η1 * t⁻¹ by funext t; ring,
        intervalIntegral.integral_const_mul, integral_inv_of_pos hY (by linarith)]
      congr 2; field_simp
    linarith
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

lemma harmBlock_le_C0 (h : P.HBS X0m Z η1 η2 ε1) {Y : ℝ} (hY : 72 ≤ Y) (hZ : 2 * Y ≤ Z) :
    P.harmBlock Y ≤ BSaias.C0 := by
  have hX := h.X0m_ge
  rcases lt_or_ge Y (10 ^ 4) with h1 | h1
  · rw [h.harmBlock_eq_harmWin (by linarith) (by norm_num at hX ⊢; linarith) hZ]
    have := BSCert.FiniteN.harmWin_le_mid hY h1
    show _ ≤ (0.70 : ℝ); linarith
  · have h2 := h.harmBlock_le_harmWin_add (by linarith) hZ
    have h3 := BSCert.FiniteN.harmWin_le_large' h1
    have hl : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hη := h.eta1_le
    have hη0 := h.eta1_nonneg
    show _ ≤ (0.70 : ℝ)
    nlinarith


/-- `∑_{𝒩 ∩ (Y,2Y]} 1/n ≤ 1` for all `Y` (with `2Y ≤ Z`). -/
lemma harmBlock_le_one (h : P.HBS X0m Z η1 η2 ε1) {Y : ℝ} (hZ : 2 * Y ≤ Z) :
    P.harmBlock Y ≤ 1 := by
  have hX := h.X0m_ge
  rcases lt_or_ge (2 * Y) 1 with h1 | h1
  · rw [P.harmBlock_eq_zero h1]; norm_num
  rcases lt_or_ge Y 1 with h2 | h2
  · rw [h.harmBlock_eq_harmWin (by linarith) (by linarith) hZ, harmWin_eq_Icc (by linarith)]
    have hfl : ⌊2 * Y⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]; constructor <;> push_cast <;> linarith
    rw [hfl]
    have : (Icc 1 1).filter (fun n : ℕ => Y < n) = {1} := by
      ext n; simp only [mem_filter, mem_Icc, mem_singleton]
      constructor
      · rintro ⟨⟨a, b⟩, -⟩; omega
      · rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, by push_cast; linarith⟩
    rw [this]; simp
  rcases lt_or_ge Y 72 with h3 | h3
  · rw [h.harmBlock_eq_harmWin (by linarith) (by linarith) hZ]
    linarith [BSCert.FiniteN.harmWin_le_five_sixths h2 h3]
  · have := h.harmBlock_le_C0 h3 hZ
    linarith [show BSaias.C0 = 0.70 from rfl]

/-- `∑_{𝒩 ∩ (Y,2Y]} 1/n ≤ 5/6` for `1 ≤ Y < 72`. -/
lemma harmBlock_le_five_sixths (h : P.HBS X0m Z η1 η2 ε1) {Y : ℝ} (hY1 : 1 ≤ Y) (hY2 : Y < 72)
    (hZ : 2 * Y ≤ Z) : P.harmBlock Y ≤ 5 / 6 := by
  have hX := h.X0m_ge
  rw [h.harmBlock_eq_harmWin (by linarith) (by linarith) hZ]
  exact BSCert.FiniteN.harmWin_le_five_sixths hY1 hY2

/-- **Small heights (proof of Lemma 5.3)**: `∑_{n ∈ 𝒩 ∩ (Y, 2Y]} 1/n ≤ C₀` for `Y ≥ 72`. -/
theorem smallHeights (h : P.HBS X0m Z η1 η2 ε1) : P.SmallHeights Z :=
  fun _ hY hZ => h.harmBlock_le_C0 hY hZ

end HBS

end BeurlingSystem

end
