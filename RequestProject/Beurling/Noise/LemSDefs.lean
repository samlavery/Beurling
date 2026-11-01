module

public import RequestProject.Beurling.Noise.Lemma53Main

/-!
# Lemma 5.21 (filtered cofactor weight): definitions

For a start `y`, a scale `v` and decision times `t : ℕ → ℝ` (the decision slot `t(p_j)` of the
`j`-th prime of the system), the filtered cofactor weight is

  `ω_y(v) = ∑_{w ∈ 𝒩 : y/w ∈ [v, 2v), τ_w < y/w} 1/w`,   `τ_w = max_{p ∣ w} t(p)`, `τ_1 = 0`.

The filter `τ_w < y/w` is written as `t(p_j) < y/w` for every prime `p_j` of `w` (for `w = 1`
it is empty, which is the convention `τ_1 = 0 < y`).

The only property of the decision times that the proof uses (proof of (ii)) is
`DecidedSmall`: a prime decided before slot `2v` is at most `3v` (in the paper,
`p ≤ t(p) + H(p)` and `2v + H(2v) ≤ 3v`).
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The filtered cofactor weight `ω_y(v)` of Lemma 5.21. -/
noncomputable def omegaW (t : ℕ → ℝ) (y v : ℝ) : ℝ :=
  ∑ e ∈ (P.elems (y / v)).filter (fun e => v ≤ y / P.val e ∧ y / P.val e < 2 * v ∧
      ∀ j ∈ e.support, t j < y / P.val e), 1 / P.val e

/-- The property of the decision times used in Lemma 5.21(ii): every prime decided before
slot `2v` is `≤ 3v` (paper: `p ≤ 2v + H(2v) ≤ 3v`). -/
def DecidedSmall (t : ℕ → ℝ) (v : ℝ) : Prop := ∀ j, t j < 2 * v → P.p j ≤ 3 * v

end BeurlingSystem

end
