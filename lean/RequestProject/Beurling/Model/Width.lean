module

public import RequestProject.Beurling.Model.TargetLocal

/-!
# Estimates on the jitter width `H` and the absorption threshold `y` used for causality

* `capH_lip` : `H(s) ≤ H(x) + (s - x)/2 + 1/4` for `X₀ ≤ x ≤ s` (from the slow variation of `H`,
  Theorem 6.23(c), `JitterRegular.capH_regular`, applied in steps of `H(x)/2`);
* `floor_quasi_mono` : the box floor `s - H(s)/2` is non-decreasing up to `1/8` (the paper's
  "`v - H(v)/2` increases", proof of Lemma 3.5);
* `scale_add_two_capH_le` : `a_k + 2H(a_k) ≤ x⁺_k + 3` for the construction scale `a_k`;
* `absorbYAt_le_sqrt`, `absorbY_le_sqrt` : `y(n) ≤ max(X₀, n)^{1/2}` (Lemma 3.2: `y(n) ≤ n^{o(1)}`);
* `log_le_capH` : `200 log x + 200 ≤ H(x)`.
-/

@[expose] public section

open Set Real CaplLink Construction AbsorbEmpty QueueMono

namespace BModel

variable {X₀ : ℝ}

lemma capH_ge_one (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x) :
    1 ≤ capH X₀ x := InitialRange.one_le_capH hX0 hX hx

/-- One step: within `H(x)/2` of `x`, `H` grows by at most `1/4`. -/
lemma capH_step (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x s : ℝ} (hx : X₀ ≤ x)
    (hxs : x ≤ s) (hs : s ≤ x + capH X₀ x / 2) : capH X₀ s ≤ capH X₀ x + 1 / 4 := by
  have hmono := capH_monotoneOn hX0 hX (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxs)) hxs
  exact JitterRegular.capH_regular hX0 hX hx hxs (by linarith)

/-- `n` steps of length `H(x)/2`. -/
lemma capH_steps (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x) (n : ℕ) :
    ∀ s, x ≤ s → s ≤ x + n * (capH X₀ x / 2) → capH X₀ s ≤ capH X₀ x + n / 4 := by
  have hH1 := capH_ge_one hX0 hX hx
  induction n with
  | zero =>
    intro s hxs hs
    simp only [Nat.cast_zero, zero_mul, add_zero] at hs
    have : s = x := le_antisymm hs hxs
    subst this; simp
  | succ n ih =>
    intro s hxs hs
    by_cases hsn : s ≤ x + n * (capH X₀ x / 2)
    · have := ih s hxs hsn
      push_cast; linarith
    · push_neg at hsn
      set x' := x + n * (capH X₀ x / 2) with hx'
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hxx' : x ≤ x' := by rw [hx']; nlinarith
      have h1 := ih x' hxx' le_rfl
      have hm := capH_monotoneOn hX0 hX (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxx')) hxx'
      have h2 := capH_step hX0 hX (hx.trans hxx') hsn.le (by push_cast at hs; linarith)
      push_cast; linarith

/-- **`H` is `1/2`-Lipschitz up to `1/4`** on `[X₀, ∞)`. -/
theorem capH_lip (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x s : ℝ} (hx : X₀ ≤ x)
    (hxs : x ≤ s) : capH X₀ s ≤ capH X₀ x + (s - x) / 2 + 1 / 4 := by
  have hH1 := capH_ge_one hX0 hX hx
  set n := ⌈(s - x) / (capH X₀ x / 2)⌉₊ with hn
  have hn1 : (s - x) / (capH X₀ x / 2) ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < (s - x) / (capH X₀ x / 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) (by linarith))
  have hsle : s ≤ x + n * (capH X₀ x / 2) := by
    rw [div_le_iff₀ (by linarith)] at hn1; linarith
  have h := capH_steps hX0 hX hx n s hxs hsle
  have h3 : (n : ℝ) / 4 ≤ (s - x) / 2 + 1 / 4 := by
    have : (s - x) / (capH X₀ x / 2) ≤ 2 * (s - x) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  linarith

/-- **The box floor is quasi-monotone**: `x - H(x)/2 - 1/8 ≤ s - H(s)/2` for `X₀ ≤ x ≤ s`;
more precisely `s - H(s)/2 ≥ x - H(x)/2 + (3/4)(s - x) - 1/8`. -/
theorem floor_quasi_mono (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x s : ℝ} (hx : X₀ ≤ x)
    (hxs : x ≤ s) : x - capH X₀ x / 2 + 3 / 4 * (s - x) - 1 / 8 ≤ s - capH X₀ s / 2 := by
  have := capH_lip hX0 hX hx hxs
  linarith

/-- The construction scale satisfies `a_k + 2H(a_k) ≤ x⁺_k + 3`. -/
theorem scale_add_two_capH_le (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (k : ℕ) :
    constructionScale X₀ k + 2 * capH X₀ (constructionScale X₀ k) ≤ switchOn X₀ k + 3 := by
  obtain ⟨hXa, ha0, -, hxa⟩ := constructionScale_spec hX0 hX k
  set a := constructionScale X₀ k
  have hX1 := one_lt_of_logX hX0 hX
  -- `a ≥ X₀ + 1`
  have hX2 : X₀ ^ 2 + 1 ≤ switchOn X₀ k := by
    have h0 : X₀ ^ 2 + 1 ≤ switchOn X₀ 0 := by
      show X₀ ^ 2 + 1 ≤ Real.exp (X₀ ^ 2)
      linarith [Real.add_one_le_exp (X₀ ^ 2)]
    exact h0.trans (switchOn_mono X₀ (Nat.zero_le k))
  have h3 : 3 * X₀ ≤ X₀ ^ 2 := by
    have : (3 : ℝ) ≤ X₀ := by have := two_pow_le_of_logX hX0 hX; linarith
    nlinarith
  have ha1 : X₀ ≤ a - 1 := by nlinarith
  have h1 := add_two_capH_le_of_lt_constructionScale hX0 hX ha1 (by linarith)
  have h2 := capH_lip hX0 hX ha1 (by linarith : a - 1 ≤ a)
  linarith

/-- `11 log ℓ + 8 ≤ 5ℓ/16` for `ℓ ≥ 10⁸`. -/
lemma log_bound_aux {ℓ : ℝ} (hℓ : 10 ^ 8 ≤ ℓ) : 11 * Real.log ℓ + 8 ≤ 5 * ℓ / 16 := by
  have he := exp_ten_ge
  have h := Real.log_le_sub_one_of_pos (show 0 < ℓ / Real.exp 10 by positivity)
  rw [Real.log_div (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h
  have h2 : ℓ / Real.exp 10 ≤ ℓ / 17073 := div_le_div_of_nonneg_left (by linarith) (by norm_num) he
  nlinarith

/-- `2135 ≤ e⁸`. -/
lemma exp_eight_ge : (2135 : ℝ) ≤ Real.exp 8 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h.le 8
  linarith [show (2135 : ℝ) ≤ (2.7182818283 : ℝ) ^ 8 by norm_num]

/-- **`y(x) ≤ x^{1/2}`** for `x ≥ X₀` (Lemma 3.2: the absorption threshold is `x^{o(1)}`). -/
theorem absorbYAt_le_sqrt (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x) :
    absorbYAt X₀ x ≤ x ^ (1 / 2 : ℝ) := by
  obtain ⟨hℓ, -, -⟩ := logs_of_ge hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  have hx0 : 0 < x := by linarith
  set ℓ := Real.log x with hℓdef
  have hH := InitialRange.capH_le_rpow hX0 hX hx
  have hH1 := capH_ge_one hX0 hX hx
  have hM0 := capM1_pos hX0 hX hx
  have hMH := (capH_conditions hX0 hX hx).1
  set H := capH X₀ x
  set M := capM1 X₀ x
  -- `M ≤ x^{1/16}`
  have hM : M ≤ x ^ (1 / 16 : ℝ) := by
    have h1 : M ^ 2 ≤ (x ^ (1 / 16 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)), ← Real.rpow_mul hx0.le]
      norm_num
      exact hMH.trans hH
    exact (pow_le_pow_iff_left₀ hM0.le (by positivity) (by norm_num)).mp h1
  have hx16 : 1 ≤ x ^ (1 / 16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ35 : ℓ ^ 3 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hL0 : absorbL0 X₀ x ≤ 2135 * x ^ (1 / 16 : ℝ) * ℓ ^ 5 := by
    unfold absorbL0
    rw [← hℓdef]
    apply max_le
    · have : ℓ ^ 5 ≤ x ^ (1 / 16 : ℝ) * ℓ ^ 5 := le_mul_of_one_le_left (by positivity) hx16
      nlinarith [pow_pos (by linarith : (0 : ℝ) < ℓ) 5]
    · have h1 : 48 * M * ℓ ^ 3 / 0.15 ^ 2 ≤ 48 * x ^ (1 / 16 : ℝ) * ℓ ^ 5 / 0.15 ^ 2 := by
        gcongr
      have h2 : 48 * x ^ (1 / 16 : ℝ) * ℓ ^ 5 / 0.15 ^ 2 ≤ 2135 * x ^ (1 / 16 : ℝ) * ℓ ^ 5 := by
        rw [div_le_iff₀ (by norm_num)]
        have : 0 ≤ x ^ (1 / 16 : ℝ) * ℓ ^ 5 := by positivity
        nlinarith
      linarith
  have hL00 : 0 ≤ absorbL0 X₀ x := le_trans (by positivity) (le_max_left _ _)
  -- `2135 ℓ^11 ≤ x^{5/16}`
  have hkey : 2135 * ℓ ^ 11 ≤ x ^ (5 / 16 : ℝ) := by
    have h1 := log_bound_aux hℓ
    have h2 : Real.log (2135 * ℓ ^ 11) ≤ 5 * ℓ / 16 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have : Real.log 2135 ≤ 8 := by
        rw [← Real.log_exp 8]; exact Real.log_le_log (by norm_num) exp_eight_ge
      push_cast; linarith
    have h3 : x ^ (5 / 16 : ℝ) = Real.exp (5 * ℓ / 16) := by
      rw [Real.rpow_def_of_pos hx0, hℓdef]; ring_nf
    rw [h3, ← Real.exp_log (show 0 < 2135 * ℓ ^ 11 by positivity)]
    exact Real.exp_le_exp.mpr h2
  have hsplit : x ^ (1 / 2 : ℝ) = x ^ (1 / 8 : ℝ) * x ^ (1 / 16 : ℝ) * x ^ (5 / 16 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  unfold absorbYAt
  rw [← hℓdef, hsplit]
  calc H * absorbL0 X₀ x * ℓ ^ 6
      ≤ x ^ (1 / 8 : ℝ) * (2135 * x ^ (1 / 16 : ℝ) * ℓ ^ 5) * ℓ ^ 6 := by gcongr
    _ = x ^ (1 / 8 : ℝ) * x ^ (1 / 16 : ℝ) * (2135 * ℓ ^ 11) := by ring
    _ ≤ x ^ (1 / 8 : ℝ) * x ^ (1 / 16 : ℝ) * x ^ (5 / 16 : ℝ) := by gcongr

/-- **`y(n) ≤ x^{1/2}`** for `n ≤ x`, `x ≥ X₀`. -/
theorem absorbY_le_sqrt (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x)
    {n : ℝ} (hn : n ≤ x) : absorbY X₀ n ≤ x ^ (1 / 2 : ℝ) :=
  (absorbY_le_absorbYAt hX0 hX hn hx).trans (absorbYAt_le_sqrt hX0 hX hx)

/-- **`H` dominates `log`**: `200 log x + 200 ≤ H(x)` for `x ≥ X₀`. -/
theorem log_le_capH (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : X₀ ≤ x) :
    200 * Real.log x + 200 ≤ capH X₀ x := by
  obtain ⟨hℓ, -, hl0⟩ := logs_of_ge hX0 hX hx
  obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
  set ℓ := Real.log x
  set l := Real.log ℓ with hl
  have hl18 : 18 ≤ l := BSCert.Capl.log_ge_18 (by linarith)
  -- `e^{8 l²} ≥ e^{2 l} e^{6} ≥ ℓ² · 400 ≥ 200 ℓ + 200`
  have h1 : Real.exp (2 * l + 6) ≤ Real.exp (8 * l ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (2 * l + 6) = ℓ ^ 2 * Real.exp 6 := by
    rw [Real.exp_add, show 2 * l = l * 2 by ring, Real.exp_mul, Real.exp_log (by linarith)]
    norm_num
  have h3 : (400 : ℝ) ≤ Real.exp 6 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
    linarith [show (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 by norm_num]
  have h4 : 200 * ℓ + 200 ≤ ℓ ^ 2 * 400 := by nlinarith
  have h5 : ℓ ^ 2 * 400 ≤ ℓ ^ 2 * Real.exp 6 := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

end BModel

end
