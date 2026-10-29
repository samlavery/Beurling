# Lean formalization: status and what remains

**Summary.** The main theorem is **not** formally verified. The Lean 4 project in [`lean/`](lean/) proves Corollary 2.2
(the answer to Question Q is negative) from one explicit hypothesis, `Theorem21InputsS`. That hypothesis still contains
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
theorem BModel.corollary_2_2_of_S_HB (hHB : ShortIntervalPNT) (h : Theorem21InputsS) : ¬ QuestionQ
```

- `QuestionQ` is Definition 1.1 (`Beurling/Defs.lean`).
- `ShortIntervalPNT` (`Beurling/Model/Slope.lean`) is a consequence of the Heath-Brown short-interval prime number
  theorem (84), stated about ℕ: for q beyond a threshold, every interval in [q, 2q] of length at least (2q)^{7/12}
  contains at least (1 − (log q)^{−3})·length/log 2q primes.
- `Theorem21InputsS` (`Beurling/Model/TopS.lean`) fixes the slot model to the construction `constructedModel` built from
  the jitters. For every θ ∈ [1/4, 1/2 − 10⁻⁴] and every even X₀ ≥ e^{10⁸} beyond some threshold, it asks for a
  countable family of failure events E with the per-scale budget of Table 1 (`TableBudget`). On the good event it asks
  for exactly two things: the queue window data and the cluster event.
- Everything else Aristotle's `Theorem21InputsO` assumed is now proved for the construction: the slot model, the arrival
  link, the slot facts, the target formula, the slow variation of H, Lemma 4.8(ii) and the null coincidence event 𝒩₌.

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
  - **Round 2** (1565 lines):
    - e^γ < 1.79, which gives the numeric part of Lemma A.6 (S3)(d).
    - Lemma 6.21(ii): the skeleton sum, and `TypeUnionBound` from the per-skeleton bound.
    - Lemma 6.22(a),(b) for (s4).
    - Theorem 6.23(a) in the Step 2 range s ≤ s_H + 1 (`theorem_6_23a_step2_full`), linked to the capacity
      certificates.
  - **Round 3** (2266 lines):
    - Lemma 6.22(d) and (e).
    - Theorem 6.23(a) for every s ≥ −log Λ (`theorem_6_23a_all`), from the skeleton inputs.
    - The join list of Proposition 6.19, with s_R ≤ |R|, proved from the staging.
    - The Pivot-Integration Lemma A.5 for one run, over an abstract filtration with box-uniform conditional laws
      (`iterated_pivots`, `pil_volume`).
    - Still open: the multi-run recursion of Lemma A.5, with the stagewise change of variables of Theorem A.10.
      These discharge `SkeletonBound` and `CoverSkeletonBound`. Also open: the pathwise skeleton reduction.
  - **Round 4** (250 lines):
    - The probabilistic skeleton of the multi-run recursion of Lemma A.5: `label_replace`, step (i), in the corrected
      order of #48/#55, and `pil_chain`.
    - The stage change of variables of Theorem A.10(i) with real exponents, and |det E| = ∏|det S_t| via Schur
      complements.
    - Still open: a pathwise model of the realised configurations (window sets, skeletons, the integrands), which
      instantiates `pil_chain` and proves the skeleton reductions.
  - **Round 5** (1085 lines): the realised-configuration model (`RankFull/Config.lean`, `WindowModel.lean`,
    `ConfigReduction.lean`, `ModelCap.lean`).
    - Window sets, skeletons from the greedy pivots, and (V1).
    - Both skeleton reductions, proved pathwise.
    - Proposition 6.11 and Theorem 6.23(a) for this model (`prop_6_11_window`, `theorem_6_23a_model`).
    - The remaining named inputs are `SkeletonBound` and `CoverSkeletonBound`, i.e. Lemma A.5 + Theorem A.10 applied to
      the model. Also needed: measurability of the counts, the model hypotheses linking it to the construction, and the
      parameter bounds.
  - **Round 6** (1354 lines): `SkeletonBound` for one run (C = B′, run structure [k]), over any `JitterLaw`, from
    Lemma A.5, the Volume Lemma with per-pivot caps and Lemma A.6 (S3)(c) for one run (`skeletonBound_oneRun`).
    - Still open: the multi-run case (`MultiRunSkeletonBound`, T ≥ 2) and `CoverSkeletonBound`.
    - The construction's `JitterLaw` instance has slot constant θ = 2, but Proposition 6.11 needs the paper's
      θ = 1 + 1/Λ from (F1). The slot count must be sharpened.
- **Added in this repository: the construction of §3** (`Beurling/Model/`, 3947 lines). `constructedModel θ X₀ ω` builds
  the slot model from the jitters as the limit of a causal iteration.
  - Lemma 3.5 is formalized as `causal`: agreement up to z − 1 propagates to agreement up to z.
  - Proved for this model: Lemma 3.3 (positivity, slope ≥ 0.08/log), the target formula (6), the arrival link and the
    slot facts.
  - `BModel.corollary_2_2_of_Q` derives Corollary 2.2 from `Theorem21InputsQ`. That hypothesis has the model fixed,
    and its only remaining conditions are the queue window data, Lemma 4.8(ii) and the cluster event. Two named
    hypotheses remain:
    - `ShortIntervalPNT`: a consequence of (84), Heath-Brown's theorem, stated about ℕ.
    - `TiesNull`: the paper's claim in §3.4 that the coincidence event 𝒩₌ is null for the constructed model. It is
      now proved (`BModel.tiesNull`, round 3); see the next item.
  - The slot offset is fixed at ϑ_s = 1/2.
- **Added in this repository: the queue skeleton of Theorem 6.6, standalone** (`Beurling/Queue6/`, ~700 lines,
  standard axioms only). Proved:
  - Freedman's inequality on a good event (`freedman_good`, `freedman_peel`);
  - the event Fr(I) and its failure bound, Theorem 6.6(i) for one window (`frEvent_fail`);
  - the queue constraints of Definition 6.8 reconciled with the first-failure budget (`withQC_fail`);
  - the deterministic part of Theorem 6.6(ii) as an induction over slots (`queue_and_data`), which produces the queue
    window data from per-window facts.

  The per-window facts (Lemma 3.9, Corollary 6.12, R1′) and the adaptedness of the window counts are parameters, to be
  instantiated once the absorbed set is corrected (see the defects below).
- **Added in this repository: §5.1–5.5, standalone** (`Beurling/Noise/`, 52 files, 13.4k lines). For any system
  satisfying (HBS) on [1, Z]:
  - Lemma 5.3 (smooth-v), with no residual hypotheses.
  - Theorem 5.6 (Beurling–Saias) and Lemma 5.8: the analytic reduction, regions Z1 and Z2 (the latter through the
    bs-cert certificate), and the large-ℓ decomposition of Lemma 5.7.
  - Corollary 5.9, from Lemma M.
  - Theorem 5.14 (the KR bound) with nominal filters and frozen widths.

  Round 2 (89 files, 24.5k lines in all):
  - The remainder bounds of Lemma 5.7 are proved. So Theorem 5.6, Lemma 5.8 and Corollary 5.9 now need only (HBS)
    (`theorem_5_6_hbs_full`, `lemma_5_8_full`, `cor_5_9_full`).
  - Proved outright: Theorem 5.15 (random widths), Lemma 5.12 and Lemma 5.21.
  - Proved from named inputs: Corollary 5.17, Proposition 5.18, Lemma 5.23, and the deterministic assembly of Lemma 5.22.
    The inputs are the transfer of A₀, A₁ to 𝒩, step (ii) of Proposition 5.18, Lemma 5.20, and the local counts of
    Corollary 6.3.

  None of these results involves the absorbed set.
- **Added in this repository: measurability and the jitter law of the construction** (`Beurling/Model/`, round 3, about
  2700 lines).
  - The construction is measurable in ω, stage by stage. This includes the heights γ_k, through the least-good-height
    rule.
  - Its slot data are adapted to the jitter filtration.
  - It is an instance of the abstract process `RankFull.JitterLaw` (`constructionLaw`): the box-uniform landing law is
    proved from the independence of the jitters, and there are nested adapted good events.
  - The coincidence event 𝒩₌ is null (`tiesNull`). Each tie pattern is a single point for the latest jitter, given the
    past.
- **Added in this repository: the link from the construction to the Appendix A window model** (`Beurling/Model/`, round
  4, about 1750 lines).
  - `constructionLaw2` is the jitter law with the paper's slot constant θ = 1 + 1/Λ of (F1), proved from the sharp slot
    density.
  - Every model hypothesis of the one-run skeleton bound is proved for the construction
    (`skeletonBound_construction`).
  - The realised grid-window counts are bounded by the window model, by unique factorisation
    (`winCount_le_windowElems2`). So `ClusterUpTo` holds on the good event once the cluster events and a target-size
    event `tBound` are in the event family (`clusterUpTo_of_windows2`).
  - Residual inputs: Lemma A.6 (S3)(d) (`S3dHyp`), the multi-run skeleton bound, and the conditions `SlotHyp` on H.
- **Appendix B.** Nearly all the certificates: bs-cert (region Z2 and the auxiliary checks), finite-n, x0-band, the
  constants, the bounds on φ, and rankin_R. Dickman's function is constructed and its facts (R1)–(R4) are proved.

Some results are proved but not yet used by the top-level theorem, because the steps that use them are still inside the
hypothesis. They are 75 of the 211 modules, about 10.7k of 44k lines. Examples:
- Lemma 5.5 (Lemma M), Freedman's inequality and Lemma 6.1;
- Lemmas 6.14–6.17 and parts of 6.21–6.22;
- Lemma A.8;
- the bs-cert, Lemma 5.3 and margin certificates.

## What remains (the content of `Theorem21InputsS`)

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

## Defects found in the Aristotle formalization

- **Height rule (fixed 2026-10-26).** `chooseHeight` took an arbitrary good height (`Classical.choose`). The paper takes
  γ_k := min S_k (§3.2, correction #76), which is needed for γ_k to be a measurable function of the data. It now takes
  the least good height whenever it is attained, which is always the case for the construction, since D̂_{<a_k} is
  continuous and the good set is closed. The arbitrary choice remains only as a total fallback.
- **Absorbed set (fixed 2026-10-28).** The paper's absorbed set (5) is a set of generalized integers, 𝒜 ⊂ 𝒩, with real
  values. The Lean development modelled it as a `Set ℕ` of integer values.
  - For the constructed system this set was almost surely empty, so the Lean target lacked the absorbed jumps of (6). The
    queue agent found the problem.
  - It is now a `Set ℝ` of element values, with u_a : ℝ → ℝ and a local-finiteness condition `LocFin`, which is proved for
    the realised set. The change touches 57 files.
  - Where a proof had used integrality, it was replaced by an argument for real values: summing Ê_A over the countable set
    𝒜, and showing that the jumps of T are locally constant from local finiteness. No new hypotheses were needed at the
    top level.

## Status

- **The main theorem is not formally verified.** It is proved in Lean only from `Theorem21InputsS`.
- The parts of the paper behind that hypothesis have so far been checked only by AI agents (see `review/`). Independent
  human review is pending.
