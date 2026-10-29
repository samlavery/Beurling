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
theorem BModel.corollary_2_2_final (hHB : ShortIntervalPNT) (h : Theorem21InputsFinal) : ¬ QuestionQ
```

- `QuestionQ` is Definition 1.1 (`Beurling/Defs.lean`).
- `ShortIntervalPNT` (`Beurling/Model/Slope.lean`) is a consequence of the Heath-Brown short-interval prime number
  theorem (84), stated about ℕ. `BaseRange.shortIntervalPNT_of_huxley84` derives it from the full two-sided (84).
- `Theorem21InputsFinal` (`Beurling/Model/MarginTop.lean`) is about the construction built in Lean from the jitters.
  Everything outside Proposition 5.38 for the construction's margin density is proved. Proposition 5.38's §5 chain is
  assembled and instantiated at the realised system; its remaining inputs are the open fields of the structures
  `RestBase`, `RestBridge`, `RestRes` and `RestMargin` (collected as `OthersInputs`), plus `Lemma73Low`, the low-height
  case b < 4X₀ + 2 of Lemma 7.3's inputs. Each open field is a statement of the paper, cited in its docstring.
- Earlier top levels (`Construction.corollary_2_2_of_O`, …, `BModel.corollary_2_2_of_P`) are kept. Each one implies
  the previous. `BModel.corollary_2_2_of_P` takes Proposition 5.38 at every height. That input is unprovable on the good
  event, so `corollary_2_2_final` replaces it with the local form.

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
      θ = 1 + 1/Λ from (F1). The slot count must be sharpened. Done in construction round 4 (`constructionLaw2`).
  - **Round 7** (3669 lines): `MultiRunSkeletonBound` is proved, so `SkeletonBound` (Lemma A.5 + Theorem A.10 with
    C = B′) holds for every run structure (`skeletonBound_all`, `multiRunSkeletonBound`, `hbound_window`).
    - **This proof does not follow the paper's proof of Theorem A.10, so a reviewer should check it.** The caps
      1(q_j ≥ τ_j) are replaced pathwise by weights ∏(q_j/τ_j)^{s_j−1}. Factorisation (FAC) becomes a translation of
      the log-coordinates, which preserves Lebesgue measure. One global change of variables u = Ex replaces the
      stagewise Schur complements, Proj_t and (B1).
    - The bound obtained is the paper's. The Lean kernel checks the proof, so what needs review is that the Lean
      statement of `SkeletonBound` is the paper's.
    - Still open: `CoverSkeletonBound` (Proposition 6.19).
  - **Round 8** (3047 lines): `CoverSkeletonBound` is proved for every cover skeleton in the window model, by the same
    route (`coverSkeletonBound_all`, `hcov_window`).
    - No Appendix A statement remains assumed.
    - The model inputs are those of `skeletonBound_all`, plus two more: the windows lie in [z, ∞), and the caps for τ.
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

  Round 3 (133 files, 34.9k lines in all):
  - Corollary 5.17(b) in full, with a bounded transfer of A₀ and A₁ to 𝒩.
  - Proposition 5.18 (transfer bound and ∞-norm bound).
  - The bridge, §5.8: Proposition 5.26, Lemma 5.27, Lemma 5.32, Lemma 5.34 and Proposition 5.35 (ranges (A) and (B)).
  - The assembly of Theorem 5.37 and Proposition 5.38 (§5.9).
  - **Corollary 5.40, packaged as exactly the R1′ and Comp⁽²⁾ inputs of the top level** (`Margin.r1Field_of`,
    `comp2Field_of`). Their remaining inputs are the identification of the construction's window compensators
    (`R1Ident`, `Comp2Ident`).
  - The operator K_pt and the edge expansion of Lemma 7.3.
  - Named inputs still open in this chain:
    - Lemma 5.20 (τ-near energy), which is common to Propositions 5.18 and 5.26 and Lemma 5.27;
    - the Step 1–2 recursion of Proposition 5.38;
    - the wiring of Theorem 5.37's three inputs;
    - Lemma 7.3(b), (c) and (d)(iii).

  Round 4 (146 files, 38.7k lines in all):
  - The chain Bridge → Theorem 5.37 → Proposition 5.38 → Corollary 5.40 is assembled (`KR.Chain.ChainInputs`).
  - (1 + K_pt)∘R_sh = id is proved, so R_sh is a two-sided inverse.
  - Lemma 5.20 is proved in four of its five forms (`KR.TNP`). Its remaining input is Corollary 6.3(ii) for the
    realised system.
  - The Step 1–5 recursion of Proposition 5.38 is proved from the paper's Step 2 bullets.

  Round 5 (163 files, 43.7k lines in all):
  - **Interface fix.** The top-level input `PointwiseMargin` asked for the margin at every height on Good(<b). That is not
    provable, since (HBS) holds only up to the horizon. It is replaced by the local form `PointwiseMarginOn m X₀ b`,
    which is all Corollary 5.40 reads (`r1Ident_of_marginOn`, `corollary_2_2_of_MOn`, `Noise/MarginRealTop.lean`).
  - The chain is localized: Lemma 5.20 now reads 𝒩 only up to 3√(2v).
  - Proved: EtaX0Sum, window integrability, Step 2's exact form, and PaperWidth for the realised width (from Theorem
    6.23(c) in integrated form).
  - The §5 chain is instantiated at the realised system (`BModel.pointwiseMarginOn_of_loc`). Its remaining inputs form
    one structure, `RealMarginLoc`, whose fields are paper statements, each cited:
    - construction facts;
    - Lemma 7.3's inputs;
    - the bridge sizes;
    - the Prop 5.35 residuals;
    - the §5.3 identities;
    - the internal steps of Proposition 5.38.
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
  - **Round 5:**
    - `SlotHyp (capH X₀) X₀` is proved outright (`slotHyp_capH`, including that H(v)/v is antitone).
    - (S3)(d) is proved (`s3d_sure`, `skeletonBound_construction_S3`) on the event where Lemma 5.1(iv) holds for the
      realised system. That event follows from the Part I conclusions and the cluster event (`sparsEv_of_cluster`).
    - Round 6 removed the Rosser–Schoenfeld input. Lean uses the Mertens product bound ∏_{p<X}(1 − 1/p)^{−1} ≤ 1.8 log X
      (`Mertens.ZinfR_one_le`) in place of the paper's citation of [RS62, (3.29)].
      - The paper is unchanged: its route through e^γ and [RS62] is correct.
      - With 1.8 in place of e^γ, the paper's closing inequality A_top ≤ A_R·e^{2.2/Λ} fails for very large z. The Lean
        route uses instead A_R = 1.8(log z + 0.7) and b = e^{2.21/Λ+10⁻⁶}, which Proposition 6.11's condition
        θe^{(3H+2)/X₀}b ≤ 1.01 allows (`Queue6/ClusterV.lean`).
      - Round 6 also proved T₀ monotone for the construction (`T0_mono_designed`). So Theorem 5.24 holds for the constructed
        system with only (84) as a standing hypothesis (`theorem_5_24_data`).
- **Added in this repository: the local prime number theorem, §5.7** (`Beurling/LocalPNT/`, 45 files, 13.4k lines).
  - Theorem 5.24, parts (i)–(iii), with the paper's constants (`LPHyp.theorem_5_24`), and on Good(<z) up to the horizon
    from the lag bound (`theorem_5_24_of_lag`).
  - Lemma 4.3.
  - The zero-free region out to T_y + 1 (correction #92).
  - (LP-a) and (LP-c).
  - The only remaining input on this route is the monotonicity of T₀, i.e. Lemma 3.3.
  - The formalization found the slip logged as correction #104.
- **Added in this repository: Theorem 6.6, Table 1 and the event family** (`Beurling/Queue6/`, 19 files, 5.6k lines).
  `Queue6.corollary_2_2_of_T : ShortIntervalPNT → Theorem21InputsT → ¬ QuestionQ`.
  - Proved for the construction:
    - Lemma 3.9 with the sandwich, Corollary 6.12, and the adaptedness of the window counts;
    - Theorem 6.6(i), via Freedman on Good(<b), and Theorem 6.6(ii), giving the queue window data and `ClusterUpTo`
      on the good event;
    - Lemma 6.1;
    - Proposition 6.11 at every z ≥ X₀;
    - the full event family, with the queue constraints folded in, and `TableBudget`.
  - `Theorem21InputsT` (structure `QueueInputs`) contains only named statements from other parts of the paper:
    - the landing compensator bound (F1)–(F2);
    - the §5 events E3/E3′ and their budget (Lemma 5.22);
    - Corollary 5.40 (R1′, and Comp⁽²⁾ ≤ s₂|I| ≤ 1);
    - Lemma 3.4 on the good event (T(x) ≤ 3x);
    - Appendix A's `MultiRunSkeletonBound`, `CoverSkeletonBound` and (S3)(d);
    - Proposition 6.11 at the lowest height z = X₀/2.

    Queue round 3 removed the Appendix A fields except the cover bound. It proves (S3)(d) on Good(<t(E1)) with a
    position cut-off, as in the paper's (F3′), and plugs in the multi-run skeleton bound. The current top level is
    `Queue6.corollary_2_2_of_V : ShortIntervalPNT → Theorem21InputsV → ¬ QuestionQ` (`Queue6/TopV.lean`). Its remaining
    inputs are:
    - the §5 events E3/E3′ and their budget (Lemma 5.22);
    - Corollary 5.40 (R1′ and Comp⁽²⁾);
    - the Cover Bound (`CoverV`, Proposition 6.19).

    Queue round 4 constructed the E3/E3′ events of Lemma 5.22 for the construction and proved their budget
    (`e3Family`, `e3_budget`). The new top level is `Queue6.corollary_2_2_of_W` (`Queue6/TopW.lean`), whose remaining
    inputs are:
    - the two variance bounds in the proof of Lemma 5.22: Comp(W) ≤ 50 log(2u)|W| (`E3CompBound`), and (s2)
      (`E3S2Bound`);
    - Corollary 5.40;
    - the Cover Bound. This is now proved in `RankFull/CoverCount.lean`, but not yet wired in.

    Construction round 7 then proved:
    - The landing compensator bound, i.e. the `land` field (`BModel.land_compensator`). The paper's μ̄ is correct: below
      x₁ the slot density is at most 1 exactly, and above it the growth of H absorbs the excess.
    - Proposition 6.11 at z = X₀/2 (`Queue6.cluster0_of`), by the paper's low-height argument: capacity 0, then
      Theorem R.
    - T(x) ≤ 3x on the good event (`tbound_of_lemma626`), from Lemma 6.26 on Good(<t).

    Construction round 8 proved (HBS) and Lemma 6.26 on Good(<t) from strictly earlier events, as in Remark horizon
    (`hbs_local`, `lemma626_G0`, `tbound_G0`), and assembled the top level
    `Queue6.corollary_2_2_of_U : ShortIntervalPNT → Theorem21InputsU → ¬ QuestionQ` (`Model/TopU.lean`). The remaining
    inputs of `Theorem21InputsU` are:
    - §5: the E3/E3′ events and their budget (Lemma 5.22), R1′ and Comp⁽²⁾ (Corollary 5.40);
    - Appendix A: (S3)(d) as stated on `goodLt`, `MultiRunSkeletonBound` (now proved, still to be plugged in) and
      `CoverSkeletonBound`.
- **Added in this repository: §7, the base range** (`Beurling/BaseRange/`, 10 files, 3k lines).
  - (84) in both directions, and its equivalence with η_H(q) ≤ (log q)^{−3}; it implies `ShortIntervalPNT`.
  - Lemma 7.1.
  - Lemma 7.3(a), (d)(i)–(ii), and (c) ⟹ (87) with the certified integrals (constant 689.0 against 690).
  - The edge numerics and §7.3.
  - `lemma_7_3` packages Lemma 7.3 in the form Propositions 5.35 and 5.38 consume.
  - Named inputs: Lemma 7.3(b), (c) pointwise and (d)(iii), and the edge expansion. All of these need the realised
    operator K_pt of §5, which is not yet defined in Lean.
  - No errors in §7; the formalization found the definitional slip logged as #105.
  - **Round 2** (3.2k lines):
    - Lemma 7.3(c) for the realised μ₁, proved outright (`kptF1Bound`, `kshQF1Second`, `lemma73c_realised`).
    - The realised μ₀ and the decomposition (86) (`mu0R`, `shdecomp`).
    - Lemma 7.3(b) from `Lemma73bCore`, i.e. Steps 1–3 of its proof together with the decision-order mismatch.
    - `lemma73Inputs_full` assembles Lemma 7.3's inputs for the realised system, from `Lemma73bCore` and (d)(iii).
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

- **Vacuous input structure (fixed 2026-10-29).** `BModel.RealMarginLoc`, as committed in aaec2e3, was empty. It required
  an additive operator `B` with `B g x = Bavg (H x) g x`, which is impossible because Lean's Bochner integral is 0 on
  non-integrable functions (`Margin.no_additive_Bavg`). So the implication `hPM_of_loc` built on it proved nothing.
  - The §5 agent found this.
  - The fix states the Lemma 5.34 operators on locally integrable functions and proves their four fields.
  - The other fields were then checked for the same failure mode (integrals of non-integrable functions, unbounded
    suprema, division by zero). A field-by-field satisfiability argument is in the agent's report; it is not a formal
    proof of non-emptiness.
  - Two further fields were found unsatisfiable as stated and corrected: `hhead` (its constant ignored the positive
    𝒩-tail) and the global `hTb`/`X0S.Hyp.count` (stated at all heights; now restricted to the horizon).

- **Lossy G-term constant (fixed 2026-10-29).** The first Lean proof of the Lemma 5.36 G-term bound (`gScaleBound_Kpt`)
  had constant 70 where correction #110 states 35.8. Its `scale_sum_le` covered each scale window [0.89u, 2.21u] by up
  to three dyadic Lemma-S blocks and paid each one about twice, so neighbouring blocks were counted several times. No
  paper step was wrong. The replacement (`RML8GSum.scale_sum_tight`, `RML8GMain.reindex7`,
  `RML8GField.hG_field_paper`) assigns each block its own kernel mass and reindexes once (factor 7.0001). It proves the
  bound with 35.8·C_N·C_S′, as #110 states.

## Status

- **The main theorem is not formally verified.** It is proved in Lean only from `Theorem21InputsS`.
- The parts of the paper behind that hypothesis have so far been checked only by AI agents (see `review/`). Independent
  human review is pending.
