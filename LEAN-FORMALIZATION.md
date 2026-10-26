# Lean formalization: status and what remains

**Summary.** The main theorem is **not** formally verified. The Lean 4 project in [`lean/`](lean/) proves Corollary 2.2
(the answer to Question Q is negative) from one explicit hypothesis, `Theorem21InputsR`. That hypothesis still contains
most of the paper's analytic and probabilistic content: about 90 of the roughly 128 pages of proof in Sections 2–7 and
Appendix A. Everything outside it is proved in Lean with no `sorry`.

**Sources.**
- The project is by [Aristotle](https://aristotle.harmonic.fun) (Harmonic), archive `75307cfd-…-aristotle.tar.gz` of
  2026-10-26. It replaces an earlier, much smaller run that reduced the theorem to a single `sorry`; that run is in the git
  history.
- Aristotle's README is renamed `lean/ARISTOTLE_README.md`. Its summary of the last step is `lean/ARISTOTLE_SUMMARY.md`.
  Its notes mapping every Lean result to the paper and the certificate scripts are in `lean/BSCERT_NOTES.md`.
- The archive also bundled a copy of the paper and of the certificate scripts. They are omitted here: the PDF is the
  repository's `beurling-paper.pdf` at 9ac0624, and every script is byte-identical to its copy under `certificates/`.

**Building.** Lean `v4.28.0`, Mathlib `v4.28.0`:

```
cd lean
lake exe cache get
lake build
```

- The full build was re-run for this repository on 2026-10-26 and completed successfully (8237 jobs).
- `lakefile.toml` passes `--tstack=262144` to Lean. Without it, the `native_decide` checks in
  `BSCert/Consts/MarginCert.lean` hit Lean's interpreter recursion limit with the default 8 MB thread stack on macOS.
- `#print axioms Construction.corollary_2_2_of_P` gives `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`
  and `Lean.trustCompiler`. The last two come from the 77 uses of `native_decide` in the certificates.
- A search of the sources finds no `sorry`, `admit`, `axiom`, `implemented_by` or `extern`.

## The top-level statement

```lean
theorem Construction.corollary_2_2_of_P (h : Theorem21InputsR) : ¬ QuestionQ
```

`QuestionQ` is Definition 1.1 (`Beurling/Defs.lean`). `Theorem21InputsR` (`Beurling/Zeros48/Inputs.lean`) is
Aristotle's `Theorem21InputsO` (`Beurling/Construction/LandingDerive.lean`) without two of its conditions, both now
proved here (see below): `JitterWidthRegular` (`Theorem21InputsP` drops it) and `Theorem410RestM` (Lemma 4.8(ii)). It says the following. For every θ ∈ [1/4, 1/2 − 10⁻⁴] and every even X₀ ≥ e^{10⁸} beyond some threshold, there is:
- a slot model M(ω) on the jitter space;
- a countable family of failure events satisfying the per-scale budget of Table 1;

such that on the good event the hypotheses listed below hold. The realised system P(ω), the absorbed set, the designed
heights and amplitudes, the parameters and the construction scales are all *defined* in Lean from M and the jitters, not
assumed.

## What is proved

The full map, result by result, is in `lean/BSCERT_NOTES.md`. In outline:
- **Section 4.**
  - The decomposition (14) and Lemmas 4.2, 4.4, 4.6 and 4.7.
  - Lemma 4.8(i), including the Montgomery–Vaughan mean-value theorem (Hilbert's inequality) and the Paley–Zygmund step.
  - The analytic tools of Lemma 4.8(ii).
  - Theorem 4.10 and the deduction of Corollary 2.2 (via Rouché's theorem, proved from the maximum modulus principle).
- **Section 3.**
  - The target and the target error (Lemma 3.4).
  - The slot model, the greedy rule, Lemmas 3.6 and 3.7, Corollary 3.8 and Proposition 4.1.
  - The design of γ_k and α_k (the recursion and its fixed point).
- **Section 5.** Lemma 5.1 for every system satisfying (HBS), and (HBS) itself for the constructed system.
- **Section 6.**
  - The deterministic part of Theorem 6.6(ii) and the queue bound (75).
  - The first-failure argument and the summation of Lemma 6.10.
  - Lemma 6.26 and Lemma 6.27(a).
  - Most of Theorem 6.23(b),(c).
- **Added in this repository** (`Beurling/Construction/JitterRegular.lean`, 2026-10-26): `jitterWidthRegular`, the slow
  variation of the jitter width (Theorem 6.23(c)). It says H(y) ≤ H(x) + 1/4 whenever x ≥ X₀ and y − H(y)/2 ≤ x ≤ y.
  - It was a hypothesis of `Theorem21InputsO`.
  - The proof needs a Lipschitz bound for γ(s), proved as `BSCert.Capl.gam_lip`: γ(t) − γ(s) ≤ 8(t − s) for
    s ≤ t ≤ s + 10⁻³.
  - That bound gives H(y) ≤ e^{48Δ}H(x), with Δ = log y − log x ≤ x^{−7/8}.
- **Added in this repository: Lemma 4.8(ii)** (`Beurling/Zeros48/`, 1878 lines). `theorem410RestM_of_inputs` derives
  `Theorem410RestM` from the other conditions on the same path. It splits the elements into rigid, absorbed and residual
  ones, proves the short-interval count of the residual elements from the lag bound and T′_cont ≤ 1.01, and checks the
  final numerical inequality. It departs from the paper's wording in a few sound ways, listed in the module docstrings.
  For example, all of T′_cont is put in the Fourier part, and the coincidence null event 𝒩₌ is not needed, because the
  elements are exponent vectors.
- **Added in this repository: Appendix A and §6.5–6.7, standalone** (`Beurling/RankFull/`, 2692 lines, standard axioms
  only).
  - Proved outright: Lemma A.2 (volume), Lemma A.3, the run-structure sum of Theorem R (H_K(0) = K^K/K!,
    corrections #48 and #55), Lemma A.6 (S3) summed over all contents, the identity of Theorem A.10, Corollary A.13 and
    Proposition 6.19. Proposition 6.11 and Theorem 6.23(a) are proved over an abstract probability space.
  - They rest on named hypotheses: the probabilistic content of the Pivot-Integration Lemma A.5 (`SkeletonBound`,
    `CoverSkeletonBound`), the reduction to skeletons (`SkeletonReduction`), Lemma 6.21(ii) (`TypeUnionBound`), the
    criterion (80) and Lemma A.6 (S3)(d).
  - They are not yet connected to `ClusterUpTo`.
- **Added in this repository: the construction of §3** (`Beurling/Model/`, 3947 lines). `constructedModel θ X₀ ω` builds
  the slot model from the jitters as the limit of a causal iteration.
  - Lemma 3.5 is formalized as `causal`: agreement up to z − 1 propagates to agreement up to z.
  - Proved for this model: Lemma 3.3 (positivity, slope ≥ 0.08/log), the target formula (6), the arrival link and the
    slot facts.
  - `BModel.corollary_2_2_of_Q` derives Corollary 2.2 from `Theorem21InputsQ`. That hypothesis has the model fixed,
    and its only remaining conditions are the queue window data, Lemma 4.8(ii) and the cluster event. Two named
    hypotheses remain:
    - `ShortIntervalPNT`: a consequence of (84), Heath-Brown's theorem, stated about ℕ.
    - `TiesNull`: the paper's claim in §3.4 that the coincidence event 𝒩₌ is null for the constructed model. The
      event 𝒩₌ is added to the event family; `tableBudget_add_null` shows this preserves the budget.
  - The slot offset is fixed at ϑ_s = 1/2.
- **Appendix B.** Nearly all the certificates: bs-cert (region Z2 and the auxiliary checks), finite-n, x0-band, the
  constants, the bounds on φ, and rankin_R. Dickman's function is constructed and its facts (R1)–(R4) are proved.

Some results are proved but not yet used by the top-level theorem, because the steps that use them are still inside the
hypothesis. They are 75 of the 211 modules, about 10.7k of 44k lines. Examples:
- Lemma 5.5 (Lemma M), Freedman's inequality and Lemma 6.1;
- Lemmas 6.14–6.17 and parts of 6.21–6.22;
- Lemma A.8;
- the bs-cert, Lemma 5.3 and margin certificates.

## What remains (the content of `Theorem21InputsR`)

| Hypothesis | Paper content behind it |
|---|---|
| `QueueWindowData` (excess bound on every queue window) | Section 5 except Lemma 5.1: Theorem 5.6's analytic reduction, the kernel theorems, the local PNT, the bridge, R1′. Also Theorem 6.6(i), Corollaries 6.3 and 6.12, Lemma 3.9, and Section 7 |
| `TableBudget` | the per-event failure bounds of Table 1, i.e. Freedman applied with the construction's filtration |
| `ClusterUpTo` | Proposition 6.11 with Sections 6.5–6.7: Theorem 6.18, Proposition 6.19, Theorem 6.23(a), Propositions 6.28–6.29, and Appendix A (Volume Lemma, A.5, A.6, the identity of A.10, Theorem R) |
| the existence of the slot model `M` | the construction recursion itself (Lemmas 3.2 and 3.5, Section 2.4, the choice of ϑ_s), and Lemma 3.3 (positivity of the target), which uses the Heath-Brown short-interval prime number theorem |
| `ArrivalsLinked`, `SlotFacts` | pathwise slot facts (the base case of Lemma 3.6, the window count of placed slot starts). These hold for the model once it is constructed; `SlotFacts` holds off the null event 𝒩₌, which can be added to the event family |

Notes:
- **External input.** The Heath-Brown short-interval prime number theorem (used through (84) in Lemma 3.3 and Section 7)
  is not in Mathlib. It should be kept as a named hypothesis; formalizing it from scratch is a project of its own.
- **Packaging.** The hypotheses only fix the interfaces between parts of the proof. For example, `ShortWindowData`
  quantifies its constants existentially, so `QueueWindowData` amounts to assuming the excess bound itself.

## Status

- **The main theorem is not formally verified.** It is proved in Lean only from `Theorem21InputsR`.
- The parts of the paper behind that hypothesis have so far been checked only by AI agents (see `review/`). Independent
  human review is pending.
