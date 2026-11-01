module

public import Mathlib

/-!
# Discrete Beurling number systems with integer error below every power and no zero-free half-plane

This file is the statement surface of the formalization of S. Lavery, *Discrete Beurling number
systems with integer error below every power of `x` and no zero-free half-plane*
(the PDF `beurling-paper.pdf` and the LaTeX sources `paper/` of this repository). The proofs are
in `RequestProject/`; `Solution.lean` imports them.

## Beurling systems

A discrete Beurling generalized number system `P` is a non-decreasing sequence of real numbers
`1 < p₀ ≤ p₁ ≤ ⋯ → ∞`, the generalized primes. Its generalized integers are the formal products
`∏ p_j ^ e_j`, one for each finitely supported exponent vector `e`, counted with multiplicity (two
different vectors with the same value are two integers). `N_P(x)` counts the generalized integers
`≤ x` and `ζ_P(s) = ∑ n^{-s}` is the zeta function. The rational primes give `N(x) = ⌊x⌋` and the
Riemann zeta function.

Following Broucke–Debruyne–Révész (Trans. AMS 2025), `P` is an `[α, β]`-system if
`ψ_P(x) = x + O(x^{α+ε})` and `N_P(x) = A x + O(x^{β+ε})` for every `ε > 0`, with `A > 0` and both
exponents optimal. A *`[1, 0]`-system* thus has integer error smaller than every power of `x`
while its prime error is as large as possible.

## The results

* `BModel.one_zero_system_exists` (Theorem A′ / Corollary `onezero` of the paper, the headline):
  there is a discrete Beurling system with `|N_P(x) - x| ≤ C_ε x^ε` for every `ε > 0` and all
  `x ≥ 1`, whose zeta function has no zero-free half-plane `Re s > 1 - ε`: for no `ε > 0` does
  `ζ_P` continue analytically to `{Re s > 1 - ε} \ {1}` without zeros. (No zero-free half-plane
  forces the prime exponent `α = 1`, since `ψ_P(x) = x + O(x^{α+ε})` makes `ζ_P` zero-free on
  `Re s > α`; and an integer-valued `N_P` has error exponent at least `0`. So this system is a
  discrete `[1, 0]`-system. These two remarks are standard and are not part of the Lean
  statement.) The integer error of the paper's system is in fact
  `O(exp(120 (log log x)⁴ / log log log x))`, and its zeros `ρ_k` satisfy
  `1 - Re ρ_k = (log log Im ρ_k + O(1)) / log Im ρ_k`.
* `BModel.corollary_2_2_complete` (Corollary 2.2): the answer to *Question Q* (Definition 1.1)
  is negative. Question Q asks whether every discrete Beurling system with
  `N_P(x) = A x + O(x^θ)` for some `A > 0` and some `θ < 1/2` must have `ζ_P` zero-free on some
  half-plane `Re s > 1 - ε`. (Applied to the rational primes, a positive answer would give a
  zero-free half-plane for the Riemann zeta function.) The project proves Theorem A for every
  `θ ∈ (0, 1/2 - 10⁻⁴]`, with zeros at distance `(log log x_k + O(1)) / log x_k` from the line
  `Re s = 1`; Corollary 2.2 is its consequence.

The systems are built "integer-first": a randomised greedy rule chooses each new generalized
prime so that the integer count `N_P` tracks a target `x + R(x)`, where the oscillation `R` plants
the zeros. The main work is a positive drift for the queue of composite elements at every scale,
resting on a resolvent bound of Beurling–Saias type, a local prime number theorem for the
realised system, and a counting theorem for clusters of composites in short windows. Every
realisation in an event of positive probability is a fixed system with the stated properties.

## The one hypothesis: eq. (84)

Both theorems assume `BaseRange.Huxley84`, eq. (84) of the paper, a statement about the
*rational* primes only: for large `q`, every interval `I ⊂ [q, 2q]` of length `≥ (2q)^{7/12}`
contains `(1 + O((log q)^{-3})) ∫_I dt / log t` primes, with the `O`-constant equal to `1`. This
is a known theorem: it follows from Heath-Brown's short-interval prime number theorem
(D. R. Heath-Brown, *The number of primes in a short interval*, J. reine angew. Math. 389 (1988),
22–63, Theorem, (1.2)) together with the de la Vallée Poussin error term in the prime number
theorem (§7.1 of the paper). It is not in Mathlib, so it is an explicit hypothesis of the Lean
theorems rather than an axiom. Nothing else is assumed: `#print axioms` of both theorems gives
`propext`, `Classical.choice` and `Quot.sound`.

The definitions below are copied verbatim, with the same namespaces and `open`s, from
`RequestProject/Beurling/Defs.lean` and `RequestProject/Beurling/BaseRange/Huxley.lean`.
-/

@[expose] public section

section Defs

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

end Defs

section Huxley

open Real MeasureTheory Set Filter

namespace BaseRange

/-- `π(I)` for `I = [a, b]`: the number of rational primes `p` with `a ≤ p ≤ b`. -/
noncomputable def primeCount (a b : ℝ) : ℕ := {p : ℕ | p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b}.ncard

/-- `∫_a^b dt/log t`. -/
noncomputable def liI (a b : ℝ) : ℝ := ∫ t in a..b, 1 / Real.log t

/-- The intervals `I = [a, b] ⊂ [q, 2q]` with `|I| ≥ (2q)^{7/12}` of (84). -/
def Admissible (q a b : ℝ) : Prop := q ≤ a ∧ b ≤ 2 * q ∧ (2 * q) ^ (7 / 12 : ℝ) ≤ b - a

/-- The relative error `|π(I)/∫_I dt/log t - 1|` of the interval `[a, b]`. -/
noncomputable def relErr (a b : ℝ) : ℝ := |(primeCount a b : ℝ) / liI a b - 1|

/-- (84) from `X` on: `|π(I)/∫_I dt/log t - 1| ≤ (log q)^{-3}` for every `q ≥ X` and every
admissible interval `I = [a, b] ⊂ [q, 2q]`. -/
def HuxleyFrom (X : ℝ) : Prop :=
  ∀ q a b : ℝ, X ≤ q → Admissible q a b → relErr a b ≤ Real.log q ^ (-3 : ℤ)

/-- **Eq. (84) of the paper** (a theorem about the rational primes, assumed here): for some
`X`, every interval `I ⊂ [q, 2q]` with `|I| ≥ (2q)^{7/12}` and `q ≥ X` has
`|π(I)/∫_I dt/log t - 1| ≤ (log q)^{-3}`. It follows from Heath-Brown 1988, (1.2), and the
de la Vallée Poussin prime number theorem; neither is in Mathlib. -/
def Huxley84 : Prop := ∃ X : ℝ, HuxleyFrom X

end BaseRange

end Huxley

/-- **Theorem A′: a discrete `[1, 0]`-system** (Corollary `onezero` of the paper), assuming
eq. (84) (`BaseRange.Huxley84`). There is a discrete Beurling system `P` such that for every
`ε > 0` there is `C` with `|N_P(x) - x| ≤ C x^ε` for all `x ≥ 1`, and whose zeta function has no
zero-free half-plane: for no `ε > 0` is there an analytic continuation of `ζ_P` to
`{Re s > 1 - ε} \ {1}` without zeros (`¬ P.HasZeroFreeHalfPlane`). -/
theorem BModel.one_zero_system_exists (h84 : BaseRange.Huxley84) :
    ∃ P : BeurlingSystem, (∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ ε) ∧
      ¬ P.HasZeroFreeHalfPlane := by
  sorry

/-- **Corollary 2.2**, assuming eq. (84) (`BaseRange.Huxley84`): the answer to Question Q is
negative. That is, there is a discrete Beurling system with `|N_P(x) - A x| ≤ C x^θ` for all
`x ≥ 1`, for some `A > 0`, `θ < 1/2` and `C`, whose zeta function has no zero-free half-plane
`Re s > 1 - ε`. -/
theorem BModel.corollary_2_2_complete (h84 : BaseRange.Huxley84) : ¬ QuestionQ := by
  sorry

end
