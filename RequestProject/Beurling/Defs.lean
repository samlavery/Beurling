module

public import Mathlib

/-!
# Discrete Beurling generalized number systems

Basic definitions from Section 1.1 of the paper
*Discrete Beurling number systems with integer error `O(x^θ)`, `θ < 1/2`, whose zeta
function has no zero-free half-plane* (S. Lavery).

* `BeurlingSystem` : a non-decreasing sequence of reals `p j > 1` with `p j → ∞`.
* `BeurlingSystem.N` : the integer counting function `N_P(x)`; elements are exponent
  vectors (counted with multiplicity), i.e. finitely supported `e : ℕ →₀ ℕ`.
* `BeurlingSystem.psi` : the Chebyshev function `ψ_P(x) = ∑_{p_j^k ≤ x} log p_j`.
* `BeurlingSystem.zeta` : the zeta function `ζ_P(s) = ∑_n n^{-s}` (meaningful for `Re s > 1`).
* `BeurlingSystem.IsZetaContinuation` : `F` is holomorphic on the punctured half-plane
  `{Re s > a} \ {1}` and agrees with `ζ_P` on `Re s > 1`.
* `BeurlingSystem.HasZeroFreeHalfPlane` : `ζ_P` is zero-free on some half-plane `Re s > 1 - ε`.
* `QuestionQ` : Definition 1.1 of the paper.
* `logStar` : the iterated logarithm.
-/

@[expose] public section

open Complex

/-- A discrete Beurling generalized number system: a non-decreasing sequence of real numbers
`p j > 1` tending to infinity (the generalized primes). -/
structure BeurlingSystem where
  /-- the generalized primes -/
  p : ℕ → ℝ
  one_lt : ∀ j, 1 < p j
  mono : Monotone p
  tendsto : Filter.Tendsto p Filter.atTop Filter.atTop

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The value `∏ p_j ^ e_j` of the element of the multiplicative semigroup with exponent
vector `e`. Different exponent vectors are different elements, even if their values coincide. -/
noncomputable def val (e : ℕ →₀ ℕ) : ℝ := e.prod fun j k => P.p j ^ k

/-- The integer counting function `N_P(x) = #{n ∈ 𝒩 : n ≤ x}` (with multiplicity). -/
noncomputable def N (x : ℝ) : ℝ := ({e : ℕ →₀ ℕ | P.val e ≤ x}.ncard : ℝ)

/-- The Chebyshev function `ψ_P(x) = ∑_{p_j^k ≤ x, k ≥ 1} log p_j`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ᶠ jk ∈ {jk : ℕ × ℕ | 1 ≤ jk.2 ∧ P.p jk.1 ^ jk.2 ≤ x}, Real.log (P.p jk.1)

/-- The zeta function `ζ_P(s) = ∑_{n ∈ 𝒩} n^{-s}`. -/
noncomputable def zeta (s : ℂ) : ℂ := ∑' e : ℕ →₀ ℕ, ((P.val e : ℝ) : ℂ) ^ (-s)

/-- The punctured half-plane `{s : Re s > a} \ {1}`. -/
def puncturedHalfPlane (a : ℝ) : Set ℂ := {s : ℂ | a < s.re} \ {1}

/-- `F` is an analytic continuation of `ζ_P` to the punctured half-plane `Re s > a`, `s ≠ 1`. -/
def IsZetaContinuation (a : ℝ) (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F (puncturedHalfPlane a) ∧ ∀ s : ℂ, 1 < s.re → F s = P.zeta s

/-- `ζ_P` is zero-free on some half-plane `Re s > 1 - ε`, `ε > 0` (away from its pole at
`s = 1`): it continues analytically there and the continuation has no zeros. -/
def HasZeroFreeHalfPlane : Prop :=
  ∃ ε > 0, ∃ F : ℂ → ℂ, P.IsZetaContinuation (1 - ε) F ∧
    ∀ s ∈ puncturedHalfPlane (1 - ε), F s ≠ 0

end BeurlingSystem

/-- **Question Q** (Definition 1.1): is it true that every discrete Beurling system with
`N_P(x) = A x + O(x^θ)` for some `A > 0` and some `θ < 1/2` has `ζ_P` zero-free on some
half-plane `Re s > 1 - ε`, `ε > 0`? (`QuestionQ` is the proposition that the answer is yes.) -/
def QuestionQ : Prop :=
  ∀ P : BeurlingSystem,
    (∃ A > 0, ∃ θ < (1 / 2 : ℝ), ∃ C : ℝ, ∀ x ≥ 1, |P.N x - A * x| ≤ C * x ^ θ) →
      P.HasZeroFreeHalfPlane

/-- The iterated logarithm `log* x`: the least `n` such that `log^[n] x ≤ 1`. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {n : ℕ | Real.log^[n] x ≤ 1}

end
