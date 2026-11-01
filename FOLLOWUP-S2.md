# Follow-up S2: a single discrete [1,0]-system (Theorem A′, branch followup-s2)

Status (2026-10-31): paper and certificates; formalized in Lean (branch lean-s2, see *Lean* below). One AI agent (Claude) wrote it, on top of S1 (development a7bcdc6).
The design was scoped (/tmp/rhscratch/ext/onezero.md, plan S2) and adversarially checked (/tmp/rhscratch/ext/onezero_check.md:
"S2 holds (fixable)") by two earlier AI agents. **The text written here has been checked by the agent that made it and one independent AI check (PASS, no mathematical
error; six wording fixes applied, below); no human review.** Theorem A and its proof are unchanged.

## Result

**Theorem A′** (paper, 01-setup `thm:Aprime`; proof in the new §8, `sections/07-onezero.tex`). Same X₀ regime
(X₀ ≥ max(e^{10⁸}, X_Hux)), switch-on points subject only to x₁ ≥ exp(X₀²) and x_{k+1} ≥ exp(x_k). On 𝒢, with P(𝒢) ≥ 1 − 1.5/log X₀:

- (i) |N(x) − x| ≤ Ψ(2x, X₀) + D_max(x) + h(x)Λ⁻⁸ + 2.01e^{18ℓ²}·1[x > x₁⁺] for all x ≥ 1, with Ψ(2x, X₀) ≤ (2 log x)^{π(X₀)}.
  Hence N(x) = x + O_{X₀}(exp(120ℓ⁴/log ℓ)) (ℓ = log log x), and N(x) = x + O_ε(x^ε) for every ε > 0.
- (ii) zeros ρ_k with Re ρ_k = 1 − (log log x_k + O_{X₀}(1))/log x_k, |Im ρ_k − γ_k| ≤ 1/8, and
  log γ_k = log x_k − 9(log log x_k)² + O(log log x_k). Equivalently, 1 − Re ρ_k = (log log|Im ρ_k| + O(1))/log|Im ρ_k|.

**Corollary `cor:onezero`.** A discrete [1,0]-system exists. The exponent 0 for N is optimal, since N is integer-valued. The
exponent 1 for ψ follows from Remark equiv (b)⇒(a) with β = 1/4. So an integer error smaller than every power does not force a
zero-free half-plane.

The constant in exp(Cℓ⁴/log ℓ) is explicit: C = 120. The constant C_{X₀} in front is finite but not computed.

## Design (§8.1)

- θ_k := 9ℓ_k²/L_k with L_k := log x_k⁺ and ℓ_k := log L_k. This is deterministic, θ_k ≤ θ_max := 36Λ²X₀⁻², and θ_kL_k = 9ℓ_k²
  exactly.
- y_k := (x_k⁺)² and ψ_k(t) := φ(t − log x_k⁺) − φ(t − log y_k).
- R_k^♭ := α_k x^{θ_k} cos(γ_k log x) ψ_k(log x).
- Amplitude condition α_kγ_k(x_k⁺)^{θ_k−1} = κ₀/log x_k⁺, and Γ_k^♭ := κ₀x_k^{1−θ_k}/(2 log x_k).
- Everything else is the construction of Theorem A: the same H, c, M₁, y, B, the window h, Abs, slots, jitter and good event.

## The proof, item by item (§8.2–8.4)

### Lemma `onezero-osc`
- (a) 0 ≤ ψ_k ≤ 1. ‖ψ_k′‖ ≤ 2 and ‖ψ_k″‖ ≤ 10, because the two steps have disjoint supports [a, a+1] and [2a, 2a+1].
  - So the bound in Prop g1(B) Step 3 keeps its factor (1 + 6/γ_j). The checker's (1 + 12/γ_j) is not needed.
- (b) supp R_k^♭ ⊂ (x_k⁺, e·y_k). These intervals are disjoint, since x_{k+1} ≥ exp(x_k) > e(x_k⁺)².
  - On the k-th interval, |R^♭| ≤ 2x^{θ_k} ≤ 2.01e^{18ℓ²}.
  - Everywhere, |R^♭| ≤ 2x^{θ_max}.
- (c) |R^♭′| ≤ 4.01κ₀/log x ≤ κ₊/log x, so Lemma G1 holds.
- (d) The R″ bound.
- (e) R̂_k^♭ is entire:
  (αs/2)[(x_k^{−w} − y_k^{−w})Φ(w)/w + conj], with w = s − θ_k − iγ_k.

### Lemma `onezero-transfer` (Sections 3, 5, 6, 7 and App. A for P′)

Every place where R or θ enters was located by grep (R, R′, R_k, κ_k, x_k, x₁, o_R, θ) and handled.

- **G1, slots, lag, horizon, the landing μ̄ excess.** These read only |R′| ≤ κ₊/log x and R′ = 0 below x₁⁺.
- **Adaptedness.** θ_k and y_k are deterministic.
- **Target error.** eq:T1flat gives |T^♭ − x − R^♭| ≤ Ψ(2x, X₀) + hΛ⁻⁸, from eq:Erig and the S1 absorbed part. Rankin's C_{X₀}x^θ was
  read only by Theorem A(i).
- **|R| ≤ 2u^θ log*u.** Its three readers (04a (H_BS); 04e Steps 2–3; §6 margin(b) Step 1) use it only as an upper bound with
  θ ≤ ½. They hold with 2u^{θ_max}.
- **eq:Rkprime with θ_k.** Its readers use θ only as an upper bound:
  - Step 4: r = 2^{θ_k−1} ≤ 2^{−1/2}, and 1/(1 − θ_k) ≤ 2 with |R_k^♭| ≤ α_k v^{θ_k};
  - Step 3: F_{θ_j} ≤ F_{1/2};
  - the separation bound, and Step 5 (1 − θ_j ≥ ½).
- **LP-c and Rhatbound.** The off-terms satisfy |y_k^{−w}| ≤ |x_k^{−w}|, so |R̂_k^♭| ≤ 10|s|x_k^{−0.4}, and the sum is still
  ≤ |s|e^{−0.39X₀²}.
- **o_R: a new per-k argument.** This replaces the S1 paragraph, which used one θ for all k.
  - o_{R,k}(u) ≤ 26Λ⁻¹⁰H(u)(x_k⁺)^{−θ_k}x_k⁺/u for u ≥ x_k⁺/3, and o_{R,k}(u) = 0 below.
  - The dyadic ratio is ≤ 0.51, so Σ_u log²(3u)o_{R,k} ≤ 6.2L_k²e^{−ℓ_k²} ≤ e^{−ℓ_k²/2}.
  - The sum over k is ≤ e^{−Λ²}.
  - This needs H(x_k⁺) = H_std = e^{8ℓ_k²} exactly, which is the checker's precision condition.

### Lemma `onezero-zeros` (§4 for P′)
- **ZB, ZBlow, ZA.** These do not involve R. Their θ-reads (κΓ₁, |t| ≤ x_k^{1−θ}, log(Γ_k/2) ≥ ½ log x_k) hold with θ_k.
- **R̂ bullets.** Each bound at most doubles, giving a total ≤ 6e^{−0.49X₀²}. The resonant off-term is M_k^off = −x_k^{−w}M_k, with
  |M_k| ≤ 5.5Λ on the circle, so |M_k^off| ≤ 5.5Λx_k^{−0.98}.
- **Designed zero with θ_k.**
  - Step 6: 2δ_k ≤ θ_k, from 9ℓ_k² ≥ 18ℓ_k. So Re w ∈ [0.49, 1 − δ_k] and |w| ≤ 1.
  - The O(1) interval [log κ₀ − log 2Λ − 1.7, log κ₀ + 0.72] is unchanged.
  - θ_k cancels in Re s* = θ_k + Re w*.
- **Late noise.** 171Λe^{8ℓ_k² − θ_kL_k} = 171Λe^{−ℓ_k²}. This needs the exact D_max ≤ 3.01e^{8ℓ²} (eq:Dmaxstd), as the checker
  required.
- **Goodheights (ii) with Γ_k^♭.**
  - Gammalow holds, as does (θ_k + η)/2 − ¼ < 0.
  - In the R′ part, |R̂_j^♭| ≤ 4.02x_j^{−1/4}, and the tail beyond a_k is 0, since ey_j < a_k.
- **Rouché tally.** 7e^{−0.49X₀²} + 1/16 + 171Λe^{−4Λ²} + e^{−10¹⁰} < ¼.

### Theorem A′(ii): the height relation
- log γ_k = (1 − θ_k)L_k − ℓ_k + O(Λ) = L_k − 9ℓ_k² − ℓ_k + O(Λ).
- With g := log|Im ρ_k| this gives 1 − Re ρ_k = (log g + O(1) + O(ℓ_k³/L_k))/g.
- The constant in front is 1. For Theorem A it is (1 − θ).
- The scoping note's "L_k − 10ℓ_k²" was a slip; the correct value is 9ℓ_k² + ℓ_k.

## Error floors (Remark `onezero-floors`)

| term | size | source |
|---|---|---|
| absorption | h(x)Λ⁻⁸ = exp(120ℓ⁴/log ℓ)Λ⁻⁸ eventually | (12.2): 0.9u₀ log u₀ ≥ 16ℓ² with log 2y ≈ 12ℓ² forces log h ≥ (320/3 + o(1))ℓ⁴/log ℓ (scoping fit 108.8 at finite ℓ); ratio at 120 → 1.125, min 1.104 |
| oscillation | 2.01e^{18ℓ²} | switch-off at x_k²; at x_k^{1+ε} it would be e^{9(1+ε)ℓ²} |
| lag | 3.01e^{8ℓ²} | landing lag H/2, H ≥ M̄₁² |
| queue | 17L²e^{4ℓ²} (inside D_max) | B ≤ 5M₁L²/c′ |
| rigid | (2 log x)^{π(X₀)} = e^{π(X₀)(ℓ+log 2)} | X₀-smooth count |

**New observation (not in the scoping notes).** The rigid term is the largest term of (i) for a very long range. It dominates the
absorption term until ℓ³ ≈ π(X₀) log ℓ/120, i.e. log ℓ ≈ Λ/3 (s2_check.py at Λ = 10⁸: log ℓ = 3.333·10⁷), far beyond x₁. So the
bound "exp(120ℓ⁴/log ℓ)" is the eventual form only. The asymptotic statement is unaffected, since the bound carries O_{X₀}. The
scoping note's claim that the rigid term "dominates only on a finite range" is right but understates how long that range is.

## Paper changes

| file | change |
|---|---|
| 01-setup | New §2.2 "A single system with integer error smaller than every power": Theorem A′, Corollary onezero, pointer to §8. New logic-table row. Graph counts 83 nodes / 211 edges / 28 ↓. |
| 07-onezero (new, §8) | §8.1 definitions (eq:thetak, eq:Rkflat, eq:thetastar), Lemma onezero-osc. §8.2 Lemma onezero-transfer (eq:T1flat, the o_R argument). §8.3 Lemma onezero-zeros. §8.4 proofs of Theorem A′ and Corollary onezero. Remark onezero-floors. |
| main.tex | Inputs 07-onezero; new environment theoremAp. |
| abstract, 00-intro | Abstract sentence. Informal Theorem A′ with a short design paragraph. rem:notshown bullet (β = 0 reached with α = 1). Outline sentence. |
| B-certificates | New §B.8 (onezero, s2_check.py). Cross-check list. depcheck output and comment. |
| C-ai-statement | Records S2 and its review status (the agent that made it and one independent AI check; formalized in Lean, branch lean-s2). |
| LABELS.md | New labels. |
| README.md | Theorem A′ informal paragraph, status, and Q sentence. |
| CORRECTIONS-vs-v3.md | #116 (strengthening, not an error). |

Theorem A, its statement (i) with C_{X₀}x^θ, and all of §§3–7 are untouched. Comments added in the paper are whole-line only.

## Certificates

- **certificates/onezero/s2_check.py** (new; standard library only; < 1 s). It covers Λ ∈ {1e8, …, 1e100} and ℓ_k from 2Λ to 1e300,
  all in logarithms, and checks:
  - eq:thetastar;
  - 2δ_k ≤ θ_k and Re w ≥ 0.49;
  - the constants 2.01, 26, 6.2 and 0.51;
  - the o_R per-k and k-sum bounds;
  - 4.01κ₀ ≤ κ₊;
  - Rhatbound;
  - the bound on M_k and M_off;
  - the Rouché tally;
  - the goodheights R′ part;
  - the window floor K > 320/3.

  It also compares the four terms of (i) at Λ = 1e8 and locates the rigid/absorption crossover.

  ```
  Theorem A'(i) at Lambda = 1e8: absorption overtakes rigid at log ell = 3.33333e+07
    (from ell^3 = pi(X_0) log ell/120: log ell = 3.33333e+07)
    ... (7 sample lines)
  TOTAL FAILURES: 0
  ```
- **certificates/depcheck/depcheck.py.** It gains the nodes lem:onezero-osc, lem:onezero-transfer, lem:onezero-zeros, thm:Aprime
  and cor:onezero (13 edges). It reports: `same-time subgraph acyclic: True | nodes 83 | edges 211 | strictly-earlier edges 28`.
  The transfer lemma reads the whole existing graph for P′; this is recorded in a comment, not encoded node by node.
- The S1 scripts are unchanged and were not rerun. window_check.py already covers the window h used here.

## Build

`cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/wt-s2-build main.tex` gives 0 undefined references
and 14 overfull boxes, the same count as the S1 build. The checked-in beurling-paper.pdf was not rebuilt.

## Open points (honest)

1. **One independent AI check only; no human review.** The check PASSED with no mathematical error. It confirmed the transfer
   lemma by reading every use of θ, the per-k o_R argument, the doubling of the R̂ bounds, M_off, late noise, the Rouché tally,
   the disjoint supports and the R″ factor (1+6/γ), one active R_k at a time, the rigid bound and the asymptotics, and 120 vs 320/3.
   Its six fixes were applied: "the exponent θ" in the transfer search sentence; θ_* renamed θ_max (it clashed with the θ_* of
   04k); "Steps 1–2" of Lemma margin(b); the S2 sentence moved to the end of its paragraph in App. C, with "not yet in Lean"; "eventually"
   in rem:notshown; and these status lines.
2. **Transfer by reading rule.** Lemma onezero-transfer asserts that §§3–7 hold for P′ "with θ_k for θ". It is not a rewritten
   proof. A reader must accept the list of the places where R enters. For the claims behind it, see the S1 grep in FOLLOWUP-S1.md
   and onezero_check.md (b).
3. **C_{X₀}** in N = x + O_{X₀}(exp(120ℓ⁴/log ℓ)) is not computed. The rigid term (2 log x)^{π(X₀)} dominates up to log ℓ ≈ Λ/3.
4. **The floor exp(≈107ℓ⁴/log ℓ)** is a property of Lemma P's divisor trick. Lowering it to the lag floor e^{8ℓ²} would need a new
   count of Abs in short windows. This is not attempted.
5. **Lean.** Formalized (branch lean-s2). See *Lean* below.
6. **Lemma ZA(b)** keeps its o(1) and is unused, as before.
7. The checked-in PDF and README page count are not updated (left to the merge, as for S1).

## Lean (branch lean-s2, 2026-10-31)

`lake build` is green (10148 jobs). `#print axioms` of `BModel.theoremAprime`, `BModel.one_zero_system_exists`,
`BModel.corollary_2_2_complete`, `BModel.theoremA_full` and `BModel.theoremA_ii_complete` gives
[propext, Classical.choice, Quot.sound]. `Main.lean`, `Defs.lean`, `Huxley.lean` and `MarginComplete.lean` are unchanged.
Statements (`RequestProject/Beurling/OneZero/TheoremAprime.lean`):

- `theoremAprime : Huxley84 → ∃ XHux, ∀ X₀ even, e^{10⁸} ≤ X₀ → XHux ≤ X₀ → ∃ Ω μ P G, μ G ≥ 1 − 1.5/log X₀ ∧
  ∀ ω ∈ G, TheoremAprimeConclusion (P ω)`. The conclusion is:
  - (i) ∀ ε > 0, ∃ C, ∀ x ≥ 1, |N(x) − x| ≤ C x^ε, and ∃ C, ∀ x ≥ e^{e^e}, |N(x) − x| ≤ C exp(120ℓ⁴/log ℓ) (ℓ = log log x);
  - (ii) a continuation F on Re s > 1/2 and zeros ρ_k of F with |(1 − Re ρ_k) log x_k − log log x_k| ≤ C and
    |log Im ρ_k − (log x_k − 9(log log x_k)² − log log x_k)| ≤ C. This is the paper's height relation with O(1) in place of
    O(log log x_k).
- `one_zero_system_exists : Huxley84 → ∃ P, (∀ ε > 0, ∃ C, ∀ x ≥ 1, |N_P(x) − x| ≤ C x^ε) ∧ ¬ P.HasZeroFreeHalfPlane`.
- The constants C depend on X₀ and ω and are not computed (point 3).

How it is built. S2 is the design θ = 0 of the existing construction. Every intermediate `Theorem21Inputs*` (down to
`Theorem21InputsTarget`), `Cond`, `Std`, `LPHyp`, `ElemCount`, `LinkedModel` and `TiesNull` now quantify over
θ ∈ [0, 1/2 − 10⁻⁴]. The public `Theorem21`, `Theorem21Inputs'` and `Theorem21Inputs` keep (0, 1/2 − 10⁻⁴], so the fixed-θ
results are untouched. The per-zero exponent is `thK θ x` (= 9(log log x)²/log x for θ = 0, = θ otherwise), and the
oscillation is `oscK` (for θ = 0, `oscTermS`: the oscillation minus its copy started at (x_k⁺)²). Theorem A′(i) runs through
`Theorem21InputsSplit` at θ = 0, where D_max = `lagMax X₀` is explicit (`PartIInputsTargetLag`).

Where the Lean differs from §8, or §8 left something unspecified (no mathematical error was found in §8):
- **Late noise.** The late-lag exponent is per k: η_k = 8.5ℓ_k²/log x_k for θ = 0 (θ/2 otherwise), with
  150Λ x_k^{η_k − θ_k} ≤ 1/100 (`OneZero/Numerics.late_numeric`). This replaces the route through the exact D_max.
- **o_R.** The R′ modulus for θ = 0 is a single density g(x) = exp(−9(log log x − 1.1)²) on all active windows
  (`OscD2.gS`, `mS`), not the per-k computation of Lemma onezero-transfer. It needs no H = H_std at x_k⁺. Summed over dyadic
  scales it is ≤ 10⁻⁸⁰ (`OscR.sum_oscModU_le_zero`).
- **Switch-off terms.** In the Rouché tally of Theorem 4.10 the switched-off copies contribute ≤ 1/40
  (`norm_tsum_oscHatK_sub_Mk_le`). The R̂ bounds are doubled (constant 20 in `norm_tsum_oscHatK_le`), as in §8.
- **|R|.** Lean proves |R(x)| ≤ 2e^{27ℓ²} (`abs_osc_zero_le`), cruder than the text's 2.01e^{18ℓ²}. Both are below exp(120ℓ⁴/log ℓ).
- **Rigid term.** Ψ(2x, X₀) ≤ (log 2x/log 2 + 1)^{π(X₀)} ≤ 4^{π(X₀)}(log x)^{π(X₀)} (`smoothCount_le_pow`), in place of
  (2 log x)^{π(X₀)}.
- **Explicit form.** It is proved for x ≥ e^{e^e} (ℓ ≥ e), so that log ℓ ≥ 1. It uses a ℓ² ≤ 120ℓ⁴/log ℓ + a³/14400
  (`sq_le_main`) for each of D_max = O(e^{8ℓ²}) (`lagMax_le_exp`), the rigid term, h(x) (`winH_le_three`) and |R|.

Checked only by the Lean kernel and the AI agent that wrote it; no human review.
