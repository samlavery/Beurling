module

public import RequestProject.BSCert.Finite.KArith

/-!
# Rational enclosures of `log a` (`a : ℚ`) from the fixed-point `log`

`logLoQF a ≤ log a ≤ logHiQF a` for `a > 0`, computed with `BSCert.FX` (no floating point;
evaluable by the kernel), with the elementary fallbacks `1 - 1/a ≤ log a ≤ a - 1`.
-/

@[expose] public section

namespace BSCert.FX

open BSCert.FiniteN

/-- `2^128` as a rational. -/
def zqF : ℚ := 340282366920938463463374607431768211456

lemma toR_eq_qF (X : ℤ) : toR X = (((X : ℚ) / zqF : ℚ) : ℝ) := by
  unfold toR ZI zqF; push_cast; rfl

/-- A lower bound for `log a`. -/
def logLoQF (a : ℚ) : ℚ :=
  if 0 < qLo a then
    match logLo (qLo a) with
    | some l => (l : ℚ) / zqF
    | none => 1 - 1 / a
  else 1 - 1 / a

/-- An upper bound for `log a`. -/
def logHiQF (a : ℚ) : ℚ := if 0 < qHi a then (K.logHiX (qHi a) : ℚ) / zqF else a - 1

lemma logLoQF_le {a : ℚ} (ha : 0 < a) : ((logLoQF a : ℚ) : ℝ) ≤ Real.log a := by
  have hfb : (((1 - 1 / a : ℚ)) : ℝ) ≤ Real.log a := by
    have := Real.one_sub_inv_le_log_of_pos (x := (a : ℝ)) (by exact_mod_cast ha)
    push_cast; simpa [one_div] using this
  unfold logLoQF
  split_ifs with h
  · split
    · rename_i l hl
      have h1 := logLo_le h hl
      rw [toR_eq_qF l] at h1
      have h2 : Real.log (toR (qLo a)) ≤ Real.log a :=
        Real.log_le_log (toR_pos.mpr h) (qLo_le a)
      exact h1.trans h2
    · exact hfb
  · exact hfb

lemma le_logHiQF {a : ℚ} (ha : 0 < a) : Real.log a ≤ ((logHiQF a : ℚ) : ℝ) := by
  unfold logHiQF
  split_ifs with h
  · have h1 := K.le_logHiX h
    rw [toR_eq_qF (K.logHiX _)] at h1
    have h2 : Real.log a ≤ Real.log (toR (qHi a)) :=
      Real.log_le_log (by exact_mod_cast ha) (le_qHi a)
    exact h2.trans h1
  · have := Real.log_le_sub_one_of_pos (x := (a : ℝ)) (by exact_mod_cast ha)
    push_cast; exact this

end BSCert.FX
