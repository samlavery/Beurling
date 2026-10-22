module

public import Mathlib

/-!
# Discrete Beurling generalized number systems

Basic definitions from Section 1.1 of the paper: a discrete Beurling system is a
non-decreasing sequence `p 0 ≤ p 1 ≤ …` of reals `> 1` tending to infinity. Its elements are
exponent vectors `e : ℕ →₀ ℕ` (counted with multiplicity), with value `∏ p j ^ e j`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

/-- A discrete Beurling generalized prime system. -/
structure BeurlingSystem where
  /-- The generalized primes. -/
  p : ℕ → ℝ
  one_lt : ∀ j, 1 < p j
  mono : Monotone p
  tendsto : Tendsto p atTop atTop

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The value `∏ⱼ pⱼ ^ eⱼ` of the element with exponent vector `e`. -/
noncomputable def val (e : ℕ →₀ ℕ) : ℝ := e.prod fun j k => P.p j ^ k

/-- The integer counting function `N_P(x)`: number of elements of value `≤ x`,
counted with multiplicity. -/
noncomputable def N (x : ℝ) : ℕ := {e : ℕ →₀ ℕ | P.val e ≤ x}.ncard

/-- The zeta function `ζ_P(s) = ∑ₙ n^{-s}` (as a Dirichlet series; meaningful for `Re s > 1`). -/
noncomputable def zeta (s : ℂ) : ℂ := ∑' e : ℕ →₀ ℕ, ((P.val e : ℝ) : ℂ) ^ (-s)

/-- The continuation of `ζ_P` given by partial summation (with `A = 1`):
`ζ_P(s) = s/(s-1) + s ∫₁^∞ (N_P(x) - x) x^{-s-1} dx`.
When `N_P(x) = x + O(x^θ)`, this is holomorphic on `Re s > θ`, `s ≠ 1`
(`differentiableAt_zetaCont`) and agrees with `zeta` on `Re s > 1` (`zeta_eq_zetaCont`). -/
noncomputable def zetaCont (s : ℂ) : ℂ :=
  s / (s - 1) + s * ∫ x in Ioi (1 : ℝ), (((P.N x : ℝ) : ℂ) - x) * (x : ℂ) ^ (-s - 1)

end BeurlingSystem

end
