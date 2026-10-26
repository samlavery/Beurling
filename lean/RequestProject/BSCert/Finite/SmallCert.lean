module

public import RequestProject.BSCert.Finite.Small
meta import RequestProject.BSCert.Finite.Small

/-!
# `finite_checks.py`, lines 3a, 3b, 4 and 5
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction

lemma win3b_checks : ∀ k ∈ Icc 2 143, win3bCheck k = true := by native_decide

lemma win3a_checks : winLoop (19999 - 143) 143 (winU 143) = true := by native_decide

lemma f12_checks : sumLoop (fun _ => 0) f12Hi f12Ok (10 ^ 6) 1 0 0 = true := by native_decide

lemma thr_checks : ∀ p ∈ (range 400).filter Nat.Prime, thrCheck p = true := by native_decide

lemma floor_two_mul_bounds {Y a b : ℝ} {ka kb : ℕ} (hY1 : a ≤ Y) (hY2 : Y < b)
    (ha : (ka : ℝ) ≤ 2 * a) (hb : 2 * b ≤ (kb : ℝ) + 1) :
    ka ≤ ⌊2 * Y⌋₊ ∧ ⌊2 * Y⌋₊ ≤ kb := by
  constructor
  · exact Nat.le_floor (by linarith)
  · have : ⌊2 * Y⌋₊ < kb + 1 := by
      rw [Nat.floor_lt (by linarith)]; push_cast; linarith
    omega

/-- **`finite_checks.py`, line 3b** (Lemma 5.3, small heights): for `1 ≤ Y < 72`,
`∑_{Y < n ≤ 2Y} 1/n ≤ 5/6`. -/
theorem harmWin_le_five_sixths {Y : ℝ} (hY1 : 1 ≤ Y) (hY2 : Y < 72) : harmWin Y ≤ 5 / 6 := by
  obtain ⟨h1, h2⟩ := floor_two_mul_bounds (ka := 2) (kb := 143) hY1 hY2 (by norm_num)
    (by norm_num)
  rw [harmWin_eq (by linarith)]
  have hc := win3b_checks _ (mem_Icc.mpr ⟨h1, h2⟩)
  simp only [win3bCheck, decide_eq_true_eq] at hc
  have := winR_eq_winQ ⌊2 * Y⌋₊
  unfold winR at this
  rw [this]
  have h3 := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at h3
  exact h3

/-- The value `5/6` of line 3b is attained (for `Y ∈ [1.5, 2)`). -/
theorem harmWin_three_halves : harmWin (3 / 2) = 5 / 6 := by
  rw [harmWin_eq (by norm_num)]
  have : ⌊(2 : ℝ) * (3 / 2)⌋₊ = 3 := by norm_num
  rw [this]
  have e : Ioc (3 / 2 : ℕ) 3 = {2, 3} := by decide
  rw [e, Finset.sum_pair (by norm_num)]
  norm_num

/-- **`finite_checks.py`, line 3a, first part** (Lemma 5.3, small heights): for
`72 ≤ Y < 10⁴`, `∑_{Y < n ≤ 2Y} 1/n ≤ 0.69659`. -/
theorem harmWin_le_mid {Y : ℝ} (hY1 : 72 ≤ Y) (hY2 : Y < 10 ^ 4) : harmWin Y ≤ 0.69659 := by
  obtain ⟨h1, h2⟩ := floor_two_mul_bounds (ka := 144) (kb := 19999) hY1 hY2 (by norm_num)
    (by norm_num)
  rw [harmWin_eq (by linarith)]
  exact winR_le_of_winU (winLoop_spec _ _ win3a_checks _ (by omega) (by omega))

/-- **`finite_checks.py`, line 3a, second part**: for `Y ≥ 10⁴`,
`∑_{Y < n ≤ 2Y} 1/n ≤ log 2 + 10⁻⁴ ≤ 0.6933`. -/
theorem harmWin_le_large' {Y : ℝ} (hY : 10 ^ 4 ≤ Y) :
    harmWin Y ≤ Real.log 2 + 1 / 10 ^ 4 ∧ Real.log 2 + 1 / 10 ^ 4 ≤ 0.6933 := by
  refine ⟨harmWin_le_large hY, ?_⟩
  have := Real.log_two_lt_d9
  linarith

/-- **`finite_checks.py`, line 4** (`F_{1/2}`, Section 5.8): for `1 ≤ y ≤ 10⁶`,
`y^{-1/2} ∑_{n ≤ y} μ²(n) n^{-1/2} ≤ 1.32964`. -/
theorem F12_le {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 10 ^ 6) : F12 y ≤ 1.32964 :=
  f12_of_check f12_checks hy1 hy2

/-- **`finite_checks.py`, line 5** (Lemma 5.23, threshold mass): for every prime `p < 400`,
`∏_{q < p prime} (1 - 1/q)⁻¹ - 1.8 log p ≤ 0.25`. -/
theorem threshold_mass_small {p : ℕ} (hp : p.Prime) (hp4 : p < 400) :
    ∏ q ∈ (range p).filter Nat.Prime, (1 - 1 / (q : ℝ))⁻¹ - 1.8 * Real.log p ≤ 0.25 :=
  thr_of_check thr_checks hp hp4

end BSCert.FiniteN
