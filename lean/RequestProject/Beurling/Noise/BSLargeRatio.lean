module

public import RequestProject.Beurling.Noise.BSLargePos

/-!
# Lower bounds for the Dickman ratio used in Lemma 5.7

* `ratio_ge_log`: `r(x) ≥ log x` for every `x ≥ 2` (04c-saias.tex, lines 355-356: it holds on
  `[2, 3]` since `r(2) ≥ log 3`, and `r(x) ≥ log(x-1)·(x-1)/(x-2) ≥ log x` by (R3));
* `ratio_ge_12_82`: `r(v) ≥ 12.82` for `v ≥ 31620` (the `r_low` table).
-/

@[expose] public section

open Real

namespace BSaias.Large

lemma ratio_ge_12_82 {v : ℝ} (hv : 31620 ≤ v) : 12.82 ≤ Dickman.ratio v := by
  have := ratio_ge_of_tabF (x := 31620) (q := 1282 / 100) (by norm_num) (by decide +kernel)
    (by exact_mod_cast hv)
  norm_num at this ⊢; linarith

/-- `r(2) = 1/(2(1 - log 2)) ≥ log 3`. -/
lemma ratio_two_ge : Real.log 3 ≤ Dickman.ratio 2 := by
  rw [Dickman.ratio_one_two (by norm_num) le_rfl]
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have h3 : Real.log 3 < 1.1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.add_one_le_exp (1.1 : ℝ)
    have h := Real.exp_one_gt_d9
    -- `e^{1.1} ≥ e · (1 + 0.1) > 3`
    have e : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
    have h01 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.1 by norm_num)
    rw [e]; nlinarith [Real.exp_pos 1]
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- The step of the induction: if `r(x-1) ≥ log(x-1)` and `x ≥ 3`, then `r(x) ≥ log x`. -/
lemma ratio_step {x : ℝ} (hx : 3 ≤ x) (h : Real.log (x - 1) ≤ Dickman.ratio (x - 1)) :
    Real.log x ≤ Dickman.ratio x := by
  set y := x - 1 with hy
  have hy2 : 2 ≤ y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hrec := Dickman.ratio_recursion (v := x) (by linarith)
  rw [← hy] at hrec
  have hmono := BSCert.div_one_sub_exp_neg_mono hly h
  have he : Real.exp (-Real.log y) = 1 / y := by
    rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
  rw [he] at hmono
  have e2 : Real.log y / (1 - 1 / y) = Real.log y * y / (y - 1) := by
    have : y - 1 ≠ 0 := by linarith
    field_simp
  rw [e2] at hmono
  -- `log(y+1) ≤ log y · y/(y-1)`, i.e. `(y-1) log(y+1) ≤ y log y`
  have hkey : Real.log x ≤ Real.log y * y / (y - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have hx' : x = y * (1 + 1 / y) := by field_simp; ring
    have hl : Real.log x = Real.log y + Real.log (1 + 1 / y) := by
      rw [hx', Real.log_mul (by linarith) (by positivity)]
    have h1 : Real.log (1 + 1 / y) ≤ 1 / y := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / y by positivity); linarith
    have hl3 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have h1' : (y - 1) * Real.log (1 + 1 / y) ≤ 1 := by
      have : (y - 1) * Real.log (1 + 1 / y) ≤ (y - 1) * (1 / y) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have : (y - 1) * (1 / y) ≤ 1 := by
        rw [mul_one_div, div_le_one (by linarith)]; linarith
      linarith
    rw [hl] at hl3 ⊢
    nlinarith
  linarith

/-- **`r(x) ≥ log x` for every `x ≥ 2`.** -/
theorem ratio_ge_log {x : ℝ} (hx : 2 ≤ x) : Real.log x ≤ Dickman.ratio x := by
  -- induction on `n` with `x ≤ n + 3`
  suffices H : ∀ n : ℕ, ∀ x : ℝ, 2 ≤ x → x ≤ n + 3 → Real.log x ≤ Dickman.ratio x by
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact H n x hx (by linarith)
  intro n
  induction n with
  | zero =>
    intro x hx2 hx3
    have h1 : Real.log x ≤ Real.log 3 :=
      Real.log_le_log (by linarith) (by norm_num at hx3; linarith)
    have h2 := BSCert.dickmanRatioFacts.mono (Set.mem_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2))
      (Set.mem_Ici.mpr (by linarith : (1 : ℝ) ≤ x)) hx2
    linarith [ratio_two_ge]
  | succ n ih =>
    intro x hx2 hx3
    rcases le_or_gt x 3 with h3 | h3
    · exact ih x hx2 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    · exact ratio_step h3.le (ih (x - 1) (by linarith) (by push_cast at hx3; linarith))

end BSaias.Large

end
