# Follow-up: designed zeros at 1·log log (branch followup-landau)

Scope: paper only. Plan: /tmp/rhscratch/ext/landau.md. Lean is NOT updated (see "Not done").

## New statement

Theorem A(ii), Theorem zeros, Lemma designedzero:

    Re ρ_k = 1 − (log log x_k + O_{X_0}(1)) / log x_k,   i.e.  1 − Re ρ_k ≍ (1−θ) log log γ_k / log γ_k.

Before, it was 3 log log x_k. The O_{X_0}(1) lies in [log κ_0 − log(2Λ) − 1.5, log κ_0 + 0.72], as before (designedzero step 6).

## The design change

- eq:ampl (02-construction): α_k γ_k x_k^{θ−1} = κ'_k / log x_k.
  - Now κ'_k := κ_0 with κ_0 ∈ [X_0⁻¹, Λ⁻⁵].
  - Before, κ'_k = κ_0/log²x_k with κ_0 ∈ [X_0⁻¹, ¼].
  - The plan fixed κ_0 = X_0⁻¹. I kept a range that contains X_0⁻¹, so the lemmas that use κ_0 ≥ X_0⁻¹ are unchanged.
  - The upper end Λ⁻⁵ is used only in Prop g1(B) Step 4/5. Elsewhere, "κ_0 ≤ ¼" was used only for the sign of the O(1) in designedzero step 6, and Λ⁻⁵ also works there.
- Derived quantities:
  - κ_k = 2κ_0/log x_k (eq:Rkprime, 04a-setup).
  - Γ_k = κ_0 x_k^{1−θ}/(2 log x_k).
  - α_k = κ_0 x_k^{1−θ}/(γ_k log x_k) ∈ [1,2].
- These are updated in: the params table (01-setup), 04a-setup, the Design facts list (04f), Lemma goodheights, Theorem zeros, and the "as u^{1−θ}/log u increases" sentence (02-construction, after eq:ampl).

## The one estimate that changed: Prop g1(B) Step 4 "Pointwise" (04f-bridge.tex)

Old proof:
- Crude weight: |ρ_osc^{(k)}(x)| ≤ κ_k F_θ.
- Two x-ranges: x ≤ x_k², and x_k² < x < exp(C' log²x_k) with C' = (4(1−θ)/c_LP)².
- This needed κ'_k log x_k → 0.

New proof, valid at every x ≥ x_k with no case split:
- Only levels x/e ≥ x_k^+ contribute, since R_k' = 0 on [1, x_k^+].
- Group them into the cells [v_j, 2v_j) with v_j := 2^{j−1} x_k^+ (j ≥ 1). Cor saias (start x) applies, since v_j ≥ x_k^+ ≥ X_0⁻/2. It gives
  log x·|ρ_osc^{(k)}(x)| ≤ C_S Σ_j log(2v_j) sup_{[v_j,2v_j)} |R_k'|.
- Exactly, for every ω: |R_k'(v)| ≤ 2κ_0 (v/x_k^+)^{θ−1}/log x_k^+. This comes from eq:Rk and eq:ampl at x_k^+, the same bound as in the proof of Lemma G1. Hence sup ≤ 2κ_0 r^{j−1}/log x_k^+ with r = 2^{θ−1} ≤ 2^{−1/2}.
- Also log(2v_j) = log x_k^+ + j log 2. So

      log x·|ρ_osc^{(k)}(x)| ≤ 2C_S κ_0 (1/(1−r) + log2/((1−r)² log x_k^+)) ≤ 2·77·(3.41422 + 8.08/X_0²) κ_0 ≤ 526 κ_0.

**Where the constant comes from:** 526 = ⌈2 · C_S · 1/(1−2^{−1/2})⌉, with C_S ≤ 77 (Cor saias) and 1/(1−2^{−1/2}) = 3.41421…. The second term is ≤ 8.1/X_0², which is negligible.
- The plan's 527 is the same figure, from rounding 3.414 up to 3.42.
- The grid must be aligned with x_k^+. With an arbitrary dyadic grid the cell that contains x_k^+ adds a full extra log x_k, and the constant becomes 1 + 3.414 = 4.414, i.e. ≈ 680κ_0. That would also be fine, but the aligned grid is what the text uses.
- No doubling is needed. Step 4 bounds ρ_osc(x) and avg_J ρ_osc separately ("Average" is unchanged). The plan's "count it twice" (1054) is not needed.

Consequences inside Step 4:
- The C' definition and the "x ≥ exp(C' log²x_k)" bullet are deleted.
- That bullet is replaced by: "If γ_k is resolvable at x, Step 3 covers it, as for the old oscillations." Step 3's resolvable R_j' item already covered this case before.
- Old oscillations j < k remain in Step 3, verbatim. Their bound 2κ_j/((1−θ)γ_j log⁴x) is summable for any amplitude; Σ_j κ_j ≤ 4κ_0/X_0².
- "Separation": log Γ_j ≥ (1−θ)log x_j − Λ − log log x_j − 1 (was −3 log log x_j). This is the only edit there.

Step 5 tally:
- The item "≤ 2·10⁴Λ²X_0⁻² (pointwise)" becomes "≤ 526κ_0 ≤ 526Λ⁻⁵".
- Total: o(1) ≤ 1.5·10⁻³Λ⁻⁴ + 526Λ⁻⁵ + e^{−0.01Λ} ≤ 1.6·10⁻³Λ⁻⁴. Since 526Λ⁻⁵ ≤ 5.3·10⁻⁶Λ⁻⁴ for Λ ≥ 10⁸, the stated total is unchanged.
- So the convention o(1) ≤ Λ⁻³ (04a-setup), and 0.97/0.96/0.82 − o(1), are unchanged downstream: Thm g2, Prop pointwise, Cor r1.
- Why Λ⁻⁵ and not ¼: with κ_0 = ¼ the new item would be ≈ 131, a constant. That does not fit o(1), and the slack is only 0.8 even with a constant budget. Λ⁻⁵ keeps it at the level of the existing total.

## Other edits

- Lemma G1 (02-construction):
  - Before: |R'(x)| ≤ 16κ_0/log³x + ….
  - Now: |R'(x)| ≤ 4κ_0/log x + 4κ_0 x^{−(1−θ)/2} ≤ 5κ_0/log x ≤ κ_+/log x. κ_+ = 0.8 is unchanged.
  - Γ_k ≥ X_0⁻¹x_k^{1/2}/(2 log x_k) still gives θ + 2 ≤ Γ_k.
- 03-zeros:
  - ZBlow proof: κΓ_1 ≥ x_1^{1−θ}/(2X_0² log x_1) (was log³).
  - Lemma ZA: log Γ_k ≥ (1−θ)log x_k − 2 log log x_k (was −4). log Y ≥ 0.66 log x_k still holds.
  - "Γ_k ≍ x_k^{1−θ}/log x_k".
  - eq:Gammalow: Γ ≥ a_k^{1−θ}/(2X_0V) ≥ a_k^{1−θ}/(2X_0V³). The weaker V³ form is kept, so the downstream bounds in goodheights(ii) are unchanged. Monotonicity is now that of u^{1−θ}/log u for log u ≥ 2.
  - designedzero step 2: α_kγ_k = κ_0x_k^{1−θ}/log x_k, so log|G| = (1−θ)log x_k − log log x_k + O(1).
  - designedzero step 6: (log log x_k + log(1/κ_0) + log 2Λ + 5.7)/log x_k ≤ δ_k = 9 log log x_k/log x_k. This still holds because log(1/κ_0) ≤ Λ ≤ ½ log log x_k. δ_k is unchanged, so ZA's x_k^{δ_k} ≤ log⁹x_k is unchanged.
  - The O(1) is negative, as κ_0 ≤ Λ⁻⁵.
- 04f:
  - Step 3: Γ_1 ≥ X_0⁻¹x_1^{1/2}/(2 log x_1).
  - Design facts now also state the exact bound on R_k' at x_k^+.
- 04a-setup: "Y' = x/x_j for F_θ, used only in Step 3 (resolvable R_j')". The old line said "Step 4 only". F_θ is now used only in Step 3, and Step 3 already used it before, so the old line was already imprecise.
- Remarks:
  - The Remark after Theorem zeros, now labelled rem:landau, is rewritten. It says the loss is the single factor log log, coming from the relative amplitude κ_0/log x_k at switch-on, with the response bounded by 526κ_0/log x for all x ≥ x_k.
  - It adds one paragraph on why log log cannot be removed with absolute (Saias-type) response bounds. This is the §3 barrier of the plan: split at V, compare |R̂_k(1−δ+iγ_k)| ≳ ½ with C_S Σ log(2v) sup|R_k'| ≤ b, and get V^δ ≳ log V. It is explicitly labelled "a reason, not a theorem".
  - Remark notshown (00-intro) is rewritten to match and points to rem:landau.
  - The text of correction #111 is superseded; a whole-line comment says so.
- The 3 log log → log log change is made in: 00-intro Theorem A (informal), 01-setup Theorem A(ii), designedzero, thm:zeros, and README.md:162.
- LABELS.md: appended rem:landau.

## Checked: nothing else uses the decaying amplitude

I grepped `3\log\log`, `log^3`, `\log^{3}`, `kappa'_k`, `kappa_k`, `kappa_0`, `Gamma_k`, `R_k`, `R'`, `kappa_+` over all sections, and read each hit. The ones below are unaffected:
- Table 1 / §5 / §6 / App A: they see the oscillation only through κ_+ = 0.8 (F1, slot-density excess 7·0.8H/L, T'_cont ≤ 1.0001), or through |R| ≤ 2u^θ log* u (Lemma T1, which needs only α_k ≤ 2).
- eq:osc, ε_N, E_BR: they see R only through o_R, which needs γ_kκ_k ≤ x_k^{1−θ}. Now γ_kκ_k ≤ 2κ_0²x_k^{1−θ}/log²x_k, so this still holds.
- E_S: no amplitude.
- Prop g1(B) Step 4 "Average": it needs only κ_k ≤ 1 and γ_kδ ≥ e^{c√/5}. Its tally items (e^{−c√/6} + 40 log^{−1.5}x) are unchanged.
- Thm lp: |R̂_k| ≤ Cα_k|s|x_k^{θ−σ}, with α_k ≤ 2.
- G1 positivity: κ_+ = 0.8, with even more slack than before.
- Lemmas ZB, ZA, latenoise, goodheights(i),(ii): only α_k ∈ [1,2], κ_0 ≥ X_0⁻¹ and lower bounds on Γ_k are used, and those bounds only improve.
- The `3\log\log v` hits in 01-setup:81 and 05-queue:50,88 are the queue parameter r̄_0, which is unrelated.
- depcheck graph: no new edge. Prop g1 already depends on cor:saias and eq:ampl. The R_k' bound is cited "as in the proof of Lemma G1", the same way Step 3 already cites G1 for Γ_1.

## Build

`latexmk -pdf … -outdir=/tmp/wt-landau-build main.tex`: exit 0, 0 undefined references/citations, 14 overfull boxes (the same as the baseline of 14). All added LaTeX comments are whole-line.

## Not done / doubts

- **Lean is out of sync.** These still use log³ and the old design:
  - `Beurling/Theorem410Design.lean` (`heightScale`, `amplitudeOf`);
  - `G1BRprime` (it uses an all-k Saias route that, with a constant κ'_k, would diverge in k);
  - the DesignedZero numerics.
  Either variant A (κ'_k = X_0⁻¹/log log x_k) or variant B (this paper's version; it needs Step 3's resolvable change formalized) is needed. Nothing was attempted.
- CORRECTIONS-vs-v3.md was not updated. #111 now reads as historical; whether this follow-up gets a correction number is for the lead to decide.
- The barrier paragraph in rem:landau is heuristic (an order-of-magnitude argument, not a proved lower bound). It assumes the response is controlled only through absolute weights. I did not check whether W^sh is also bounded below by ≍ log v/log y.
- Cor saias is used at start x on Good(<x), exactly as it already is for μ_1 and σ_A in Prop g1. I did not re-audit its event or horizon conditions beyond 04a-setup's Y' list (Y' = x/v ≤ 2x/X_0⁻).
- Historical review files (review/*.md, review/subchecks/*) still mention 3 log log and log³. I left them unedited.
