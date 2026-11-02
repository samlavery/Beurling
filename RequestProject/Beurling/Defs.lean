module

public import RequestProject.Beurling.StatementDefs

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

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The Chebyshev function `ψ_P(x) = ∑_{p_j^k ≤ x, k ≥ 1} log p_j`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ᶠ jk ∈ {jk : ℕ × ℕ | 1 ≤ jk.2 ∧ P.p jk.1 ^ jk.2 ≤ x}, Real.log (P.p jk.1)

end BeurlingSystem

/-- The iterated logarithm `log* x`: the least `n` such that `log^[n] x ≤ 1`. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {n : ℕ | Real.log^[n] x ≤ 1}

end
