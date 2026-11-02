module

public import Mathlib

/-!
# The definitions of the advertised statements

`BeurlingSystem`, its counting and zeta functions, `QuestionQ`, and the definitions behind the
hypothesis (84) (`BaseRange.Huxley84`). This module is a verbatim copy of the definitions in
`Challenge.lean`, in the same order and in a single module importing only Mathlib, so that the
elaborated terms, including the auxiliary `_proof_` constants Lean generates and shares within a
module, are identical to the Challenge's (as `lake comparator` requires).
`RequestProject/Beurling/Defs.lean` and `RequestProject/Beurling/BaseRange/Huxley.lean` import it.
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

end
