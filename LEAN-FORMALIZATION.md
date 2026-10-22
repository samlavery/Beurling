# Lean formalization: status and blockers

**Summary.** The main theorem is **not** formally verified. An automated Lean 4 formalization by
[Aristotle](https://aristotle.harmonic.fun) (Harmonic) reduced it to one unproved lemma, `exists_system_near_model`, and proved
everything around that lemma. That lemma is the whole analytic and probabilistic core of the paper, and it is out of reach in
Lean/Mathlib at present.

**Sources.** The Lean project is in [`lean/`](lean/), exactly as delivered by Aristotle (run
`dfbedf4a-6bed-4f51-ab86-61a2788664c2`), apart from two changes: Aristotle's own README is renamed `ARISTOTLE_README.md`, and
the copy of the paper PDF it bundled is omitted. The folder also contains Aristotle's summary (`ARISTOTLE_SUMMARY.md`) and its
full report (`VERIFICATION_REPORT.md`), which includes a hand reading of Sections 2–4 and parts of Section 6.

**Building.** The project uses Lean `v4.28.0` and Mathlib `v4.28.0`. To build it:

```
cd lean
lake exe cache get
lake build
```

Aristotle reports that the project builds and that `exists_system_near_model` is the only `sorry`. A search of the sources
for `sorry`, `axiom`, `native_decide`, `implemented_by` and `extern` finds only that one `sorry`. The build itself has not
been re-run independently for this repository.

## What is proved in Lean

| File | Results | Status |
|---|---|---|
| `Beurling/Defs.lean` | `BeurlingSystem` (non-decreasing p_j > 1 with p_j → ∞); the value of an exponent vector; `N` (counted with multiplicity); `zeta` (the Dirichlet series); `zetaCont` = s/(s−1) + s∫₁^∞ (N(x) − x)x^{−s−1} dx | definitions |
| `Beurling/Basic.lean` | `finite_le`; `differentiableAt_zetaCont` (if \|N(x) − x\| ≤ Cx^θ then `zetaCont` is holomorphic on Re s > θ, s ≠ 1); `zeta_eq_zetaCont` (it equals the Dirichlet series on Re s > 1) | proved |
| `Beurling/ZeroCriterion.lean` | `exists_zero_of_near_model`, a Rouché-type zero criterion, the final step of Theorem 4.9 | proved |
| `Beurling/Checks.lean` | `re_Phi_ge` (§4.2), `zeta2_pow4_div_zeta4_le` (Lemma 4.8(i)), `prop41_numeric` and `eta_ge` (the numerics of Proposition 4.1) | proved |
| `Beurling/MainTheorem.lean` | `exists_no_zeroFree_halfPlane`, the main theorem (Corollary 2.2), proved from `exists_system_near_model` | **conditional: `exists_system_near_model` is `sorry`** |

**The zero criterion.** `exists_zero_of_near_model` says: let f and g be holomorphic on a closed disc, with g vanishing at the
centre, and suppose that on the boundary circle |g| ≥ M and |f − g| ≤ m, where 2m < M. Then f has a zero inside the disc.
- Mathlib has no Rouché theorem, so it is proved from the maximum modulus principle, applied to f − g and to 1/f.
- It uses only Lean's standard axioms.
- The paper's constants satisfy its hypotheses: |Z_B + M_k| ≥ 1/4 on the circle, and the perturbation is at most
  1/16 + o(1) < 1/8.

**The main theorem, as stated in Lean.** `zetaCont` is the continuation of ζ_P to Re s > θ.

```lean
theorem exists_no_zeroFree_halfPlane :
    ∃ P : BeurlingSystem, ∃ θ C : ℝ, θ < 1 / 2 ∧
      (∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ) ∧
      ∀ ε > 0, ∃ s : ℂ, s ≠ 1 ∧ θ < s.re ∧ 1 - ε < s.re ∧ P.zetaCont s = 0
```

## The blocker: `exists_system_near_model` (the only `sorry`)

```lean
theorem exists_system_near_model :
    ∃ P : BeurlingSystem, ∃ θ C : ℝ, θ < 1 / 2 ∧
      (∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ) ∧
      ∀ ε > 0, ∃ (c : ℂ) (r m M : ℝ) (g : ℂ → ℂ), 0 < r ∧ 2 * m < M ∧
        closedBall c r ⊆ {s : ℂ | θ < s.re ∧ 1 - ε < s.re ∧ s ≠ 1} ∧
        DifferentiableOn ℂ g (closedBall c r) ∧ g c = 0 ∧
        (∀ z ∈ sphere c r, ‖P.zetaCont z - g z‖ ≤ m) ∧
        (∀ z ∈ sphere c r, M ≤ ‖g z‖)
```

**What it contains.** This lemma is everything in the paper before the Rouché step:
- the randomised greedy construction (Section 3);
- the lag bound (Proposition 4.1), which rests on Sections 5–7, Appendix A, and the computer-assisted certificates of
  Appendix B;
- Lemmas 4.2–4.8: the base factor, the absorbed part, the designed zeros, late noise and good heights.

In the paper the model for the k-th designed zero is g = Z_B + M_k. Its centre is s*_k, its radius is 1/log x_k, and the
constants are M = 1/4 and m = 1/16 + o(1).

**Why it is out of reach.** Formalizing the lemma means formalizing all of the above. It also needs two classical analytic
inputs that are not in Mathlib:
- the Huxley–Heath-Brown short-interval prime number theorem;
- the Montgomery–Vaughan mean value theorem.

The certificates of Appendix B would also have to be imported into Lean or re-proved there.

## Status

- **The main theorem is not formally verified.** Its Lean proof depends on the one unproved lemma above, and Aristotle's
  Properties table marks it as in progress.
- **What the formalization does confirm:**
  - the definitions;
  - the analytic continuation of ζ_P to Re s > θ;
  - a few numerical steps of Section 4 and Proposition 4.1;
  - the logical skeleton of the final step. Once the paper's analytic output is given (a holomorphic model with a zero, close
    to ζ_P on a small circle, with the stated constants), ζ_P has a zero there.
- **What it does not cover.** It says nothing about the correctness of Sections 3 and 5–7 or of the appendices. Those parts
  have so far been checked only by AI agents (see `review/`). Independent human review is pending.
