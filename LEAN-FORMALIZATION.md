# Lean formalization: status and blockers

**Summary.** The main theorem is **not** formally verified. An automated Lean 4 formalization attempt by Aristotle reduced it
to one unproved lemma, `exists_system_near_model`, and proved everything around that lemma. That lemma is the whole
analytic and probabilistic core of the paper, and it is out of reach in Lean/Mathlib at present.

The Lean sources come from Aristotle's project (`RequestProject/Beurling/…`) and are not yet included in this repository.
Aristotle's own verification report (`VERIFICATION_REPORT.md` in that project) describes the same split.

## What is proved in Lean

- **`exists_zero_of_near_model`** (`RequestProject/Beurling/ZeroCriterion.lean`): a Rouché-type zero criterion. It is the
  final step of Theorem 4.9 of the paper.
  - **Statement:** let f and g be holomorphic on a closed disc, with g vanishing at the centre. Suppose that on the boundary
    circle |g| ≥ M and |f − g| ≤ m, with 2m < M. Then f has a zero inside the disc.
  - **Proof:** Mathlib has no Rouché theorem, so this is proved from the maximum modulus principle.
  - **Axioms:** only Lean's standard ones.
  - **Fit with the paper:** the paper's constants satisfy the hypotheses. On the circle |Z_B + M_k| ≥ 1/4, and the
    perturbation is at most 1/16 + o(1) < 1/8.
- **`exists_no_zeroFree_halfPlane`** (`RequestProject/Beurling/MainTheorem.lean`): the main theorem, which is Corollary 2.2 of
  the paper. Its statement is unchanged. It is derived in Lean from three inputs:
  - the criterion above;
  - the existing holomorphy result `differentiableAt_zetaCont`;
  - the single remaining input `exists_system_near_model`, described below.

  The theorem says: there is a discrete Beurling system with |N(x) − x| ≤ Cx^θ, θ < 1/2, whose zeta function has zeros with
  real part arbitrarily close to 1.

## The blocker: `exists_system_near_model` (the only `sorry`)

**Statement.** There is a discrete Beurling system with |N(x) − x| ≤ Cx^θ, θ < 1/2, with the following property. For every
ε > 0 there is a closed disc inside {s : θ < Re s, 1 − ε < Re s, s ≠ 1}, and a holomorphic model function on it, such that:
- the model function vanishes at the centre of the disc;
- it is close to ζ_P on the boundary circle.

**What it contains.** This lemma is everything in the paper before the Rouché step:
- the randomised greedy construction (Section 3);
- the lag bound, which is Sections 5–7, Appendix A, and the computer-assisted certificates of Appendix B;
- Lemmas 4.2–4.8 (the base factor, the absorbed part, the designed zeros, late noise, good heights).

**Why it is out of reach.** Formalizing it means formalizing all of the above. It also needs two classical analytic inputs
that are not in Mathlib:
- the Huxley–Heath-Brown short-interval prime number theorem;
- the Montgomery–Vaughan mean value theorem.

## Status

- The main theorem is not formally verified. Its Lean proof depends on the one unproved lemma above, and Aristotle's
  Properties table marks it as in progress.
- The formalization confirms the logical skeleton of the last step only. It holds once the paper's analytic output is given:
  a zero of a holomorphic model near ζ_P on a small disc, with the stated constants, forces a zero of ζ_P.
- It says nothing about the correctness of Sections 3 and 5–7 or of the appendices. Those parts have been checked only by
  AI agents so far (see `review/`). Independent human review is pending.
