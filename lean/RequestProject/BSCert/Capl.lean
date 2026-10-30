module

public import RequestProject.BSCert.Expr
public import RequestProject.BSCert.FX.Expr
public import RequestProject.BSCert.FX.LogQ

/-!
# The capacity parameter of Theorem 6.23: definitions

These are the quantities of Theorem 6.23 of the paper (the capacity theorem), as evaluated
by the scripts `analytic_capl.py`, `caplw_check_independent.py` and `raise_max.py`:
* `A(Λ, s) = log(2Λ³e^{2s}/(2 log Λ + s))`;
* `G(Λ, s) = 2√(A(A+1)) e^{s/2} / √(Λ - A - 1)`;
* `Λ_s = max(10⁸, e^{-s})` and `γ*(s) = 1.3 G(Λ_s, s)`;
* `γ(s)`: `γ*(s)` for `s ≤ s_H`, the linear ramp to `7.5` on `[s_H, s_H + 1]`, and `7.5` beyond.
-/

@[expose] public section

namespace BSCert.Capl

open Real

/-- `A(Λ, s) = log(2Λ³e^{2s}/(2 log Λ + s))`. -/
noncomputable def A (Λ s : ℝ) : ℝ :=
  Real.log (2 * Λ ^ 3 * Real.exp (2 * s) / (2 * Real.log Λ + s))

/-- `G(Λ, s) = 2√(A(A+1)) e^{s/2} / √(Λ - A - 1)`. -/
noncomputable def G (Λ s : ℝ) : ℝ :=
  2 * Real.sqrt (A Λ s * (A Λ s + 1)) * Real.exp (s / 2) / Real.sqrt (Λ - A Λ s - 1)

/-- `Λ_s = max(10⁸, e^{-s})`. -/
noncomputable def LamS (s : ℝ) : ℝ := max 100000000 (Real.exp (-s))

/-- `γ*(s) = 1.3 G(Λ_s, s)`. -/
noncomputable def gstar (s : ℝ) : ℝ := 1.3 * G (LamS s) s

/-- `γ(s)` with break point `sH`. -/
noncomputable def gam (sH s : ℝ) : ℝ :=
  if s ≤ sH then gstar s
  else if s ≤ sH + 1 then gstar sH + (7.5 - gstar sH) * (s - sH) else 7.5

/-- `A` split into its pieces (for `Λ, ℓ > 0`). -/
lemma A_eq {Λ s : ℝ} (hΛ : 0 < Λ) (hl : 0 < 2 * Real.log Λ + s) :
    A Λ s = Real.log 2 + 3 * Real.log Λ + 2 * s - Real.log (2 * Real.log Λ + s) := by
  unfold A
  rw [Real.log_div (by positivity) hl.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
  push_cast; ring

end BSCert.Capl
