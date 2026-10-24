# Re-check of the paper after the fixes from the first paper check

**What this is.** The first check (`review/paper-check.md`) found the paper faithful to the refereed working draft v3, but not
yet self-contained:
- one BLOCKING item, B1: the Beurling–Saias remainder lemma for ℓ ≥ 10¹⁸ was only a sketch;
- 36 FIXABLE items.

After the authors' fixes, three fresh, independent AI checkers re-checked every changed passage, following
`review/RECHECK-BRIEF.md`. Their full reports are in `review/recheck/`:

| Report | Scope | Verdict |
|---|---|---|
| `R1.md` | Beurling–Saias part: Lemmas V, M and CM; Theorem bs with regions Z1, Z2 and the remainder lemma; Corollary saias | B1 RESOLVED. 0 BLOCKING, 1 FIXABLE, 13 COSMETIC. |
| `R2.md` | Rest of the noise section: Theorem lp with Landau's lemma, the kernel theorems, the X₀ band, Lemma SI, the bridge and the margin | 0 BLOCKING, 4 FIXABLE, 10 COSMETIC. |
| `R3.md` | Introduction, setup, construction, zeros, queue section, base range, Appendices A–C, README, build, certificates, literature | 0 BLOCKING, 3 FIXABLE, 18 COSMETIC. Two targeted follow-up checks are in §13–§14. |

**Main results.**
- **B1, the remainder lemma.** Every inequality was re-derived and every constant recomputed in ball arithmetic. The induction
  slack ℓΣ was also evaluated directly from its definition by quadrature, at 68 extreme points:
  - ℓ ∈ {10¹⁸, 10¹⁰⁰};
  - τ ∈ {10⁸, ℓ/30};
  - u near 2, 27, u₀ − 2 and U(ℓ).

  The lemma held at every point. The check confirms that correction #23 is needed. With v3's error term ℓ^{−1/4}, the tail
  term exceeds the allowance by a factor of several hundred at ℓ = 10¹⁰⁰ (R1 §2.2).
- **Euler-chain bookkeeping in Appendix A (first check I5, correction #27).** The rewrite is correct. A follow-up repair made
  the integrand of every label sum independent of its label, at both ends of the chains. A targeted re-check confirmed this
  (R3 §13).
- **Newly explicit constants:**
  - Theorem lp: the constant 442, c_zf = 0.088/Λ, the bound on G(L) and the threshold 76Λ³;
  - Lemma SI: both cases;
  - Theorem caplw: Steps 0–6;
  - the landing windows (correction #20);
  - Lemma ZBlow: C₀ = 2.1, giving log C₈ = 439.33.

  Each was recomputed independently and confirmed.
- **Certificates.** Every certificate in Appendix B reproduces its quoted output exactly. This includes the scripts that were
  renamed or had internal labels removed.
- **Build.** Clean, with no undefined or multiply defined references or citations and no warnings.
- **Literature.** BDR (arXiv 2309.01567) and Broucke (arXiv 2507.13780) were checked at source, and the quotations and
  attributions are accurate. The paper cites Rosser–Schoenfeld (3.29); this equation number was confirmed only through a
  secondary source.

**What the re-check found, and what was done.**
- **FIXABLE items, all applied.** Each was then confirmed either by the checker that found it or in a targeted follow-up:
  - Source comments swallowed rendered text in three places in Section 6, including part of the statement of Theorem
    6.22(c). The text is restored, and a scan of every section file finds no other case.
  - Four constants or ranges were slightly wrong in the local prime number theorem, the kernel section and the margin
    section: 50.342 → 50.35; the stated range of the G(L) bound; P′ := 0.51P; the constant 8.5, now derived explicitly as
    ≤ 8.4912.
  - The ends of the Euler chains in Appendix A (see above).
  - Region Z1's tail bounds are now uniform in ℓ.
  - The AI-use statement had described the review status of the newest text inaccurately.
- **New log entries.** The corrections log `CORRECTIONS-vs-v3.md` gained entries #23–#30 during the fixes and re-check. None
  changes a conclusion of the paper.
- **COSMETIC items.** Most were applied. A few deliberately remain, and they are listed in the reports.

**Verdict of the re-check.** No checker found a BLOCKING item. With the FIXABLE items applied, each checker judged its files a
complete and faithful presentation of its part of the proof of Theorem A.

**Caveat.** Every check of this paper, and every referee of v3, has been an AI agent. No human expert has verified the
argument. The authors regard the result as unconfirmed until a specialist has read it.

## Addendum: defects found after the re-check (corrections #31–#101)

After the first public version, a reader reported forty-nine defects that all the AI checks above had missed. Repairing them, and
re-checking the repairs, two end-to-end checks (R14, R15) and an audit of the certificate code (R30), turned up twenty-one more. The full list, with each repair, is entries #31–#101 of `CORRECTIONS-vs-v3.md` (number 94 is unused):

| # | Where | Defect | Found by |
|---|---|---|---|
| 31 | Prop. pointwise margin, Step 2 | strip identity used as exact although box widths vary | reader |
| 32 | jitter width H; Thm 6.22(c) | H jumped (ceiling in r₀; per-scale freeze), breaking its regularity | reader |
| 33 | decomposition of ζ_P | absorbed-element weight bound \|w_a\| ≤ 1 false | reader |
| 34 | Lemma T1, absorbed part | smoothed elements assumed to have unit mass | reader |
| 35 | Lemma ZA(a) | statement stronger than proof; saving not monotone on the ramp | repair of #33 |
| 36 | Lemma count, Cor lag, X₀ | unproved initial value; lag's lower constant; initialisation at X₀ | reader |
| 37 | Cor localcount | proved for dyadic P, used at non-dyadic P and below X₀ | re-check |
| 38 | Lemma threshold-mass | stated for x ≥ X₀, valid for x ≥ X₀³ (all uses) | repair of #37 |
| 39 | Lemma designedzero | unspecified constant C₁; now C₁ := 0 with κ₀ ≥ X₀⁻¹ | re-check |
| 40 | Thm bs, t-dense | definition omitted the j = 0 condition p₁ ≤ t | reader |
| 41 | standing fact (F2) | claimed the slots of distinct primes are independent; only the conditional jitter law holds (and is all that is used) | reader |
| 42 | App. A slot positions τ_j | lower bound X₀ for pivot values; jittered primes can land in [X₀⁻, X₀) | reader |
| 43 | standing fact (F3′); λ_D; degree cap D; Lemma rowweights | Euler-product partition missed jittered primes in [X₀⁻, X₀); a "read X₀ as X₀⁻" convention replaced by explicit X₀⁻ bounds | reader |
| 44 | Prop cover, Lemma 4.14(ii) | uniform excess weight X₀⁻¹ does not give the claimed pattern-sum bound; per-index weights τ_j⁻¹ needed | re-check |
| 45 | Thm 3.13(iii) (LP⁺), Step 10 | unspecified smoothing window; high-frequency Mellin tail beyond T₁ never bounded; now an explicit k-fold box kernel with T₁ ∝ k and every contour piece bounded | reader |
| 46 | Prop cover (Cover Bound) | right side was a sum over the realised (random) primes, compared with an expectation; now a deterministic envelope Σ̄_τ (per-row chain bound Ch, R-row labels at τ_j) | reader |
| 47 | margin decomposition; Prop g1, Thm g2, Prop pointwise(b), Cor r1 | no support convention for MA[ℙ] and f₀ at X₀; the exact convention gives an edge term just below small multiples of X₀; margin constant 0.97 → 0.82 up to X₀^1.01 (new Lemma margin(d)); c′ = 0.15 and K_d = 3 stand | reader |
| 48 | App. A Pivot-Integration Lemma, label sum | the label sum needs the integrand free of the slot label pointwise, but the carried Euler factors cancel only after integration; re-proved with the label sum first (at the first slot u_t after the latest free column f_t, with support indicator χ_t), then the pivot integrals, then a joint block bound; no constant changes | re-check |
| 49 | Lemma rowweights(c), (e) | (e) claimed its Rankin bound for every η ∈ [¼, 1), but the rigid Euler product diverges as η → 1; (c) was claimed up to σ ≈ ½, where the prime-power terms exceed its allowance; (e) now at η = ¼ (its only use), (c) for u ≤ X₀^0.3 (all uses), with explicit proofs and a new certificate `rankin_R.py` | reader |
| 50 | Lemma T1, rigid part | explicit Rankin constant at σ = θ < ½ false as written (it defines only the finite C_{X₀}); now the Euler product itself | sweep for #49 |
| 51 | (H_BS) verification (§4a); Lemma T1 | the rigid error's decay 2κu·min(1, Cρ) was asserted (in v3 too) but never proved, and without decay η₁ is unbounded; now eq:Erig plus Rankin at σ = 1 − 1/Λ give η₁, η₂ ≤ κΛ² + X₀^{−1/2} | re-check |
| 52 | square-prime source s₂ (eq:s2, §4d) | Γ factor up to 1.129 and range starting at X₀ instead of X₀⁻ (reader); the repair also found the Dickman variable applied the wrong way, e^{a_V} not small, an unchecked range, and an unproved a ≥ 3 claim; re-derived with real constant 0.73 against 9 | reader |
| 53 | Lemma margin(b) Step 3, (d)(iii) | the one-variable-at-a-time replacement made mixed realised/rational sums that the one-system multiset argument does not cover; now a symmetric telescoping over ordered tuples, with a better bound | independent check R7 |
| 54 | certificates (App B), quoted constants | finite-n rigour rested on libm and hard-coded error strings; about a dozen constants quoted as "ball arithmetic" had no certificate; bs-cert's bound S was specified only in code; two quoted decimals were not upper bounds; now an arb finite-n, a new constants certificate, S written into §4c | independent check R8 |
| 55 | App. A Lemma pil, (S3), Thm R, cor:R-Ecl; Prop cover, Lemma reduction(ii) | closes the #48 union gap: block bound summed over every block content (eq:A-Grec); Thm R gains k^k/k! ≤ e^k (eq:A-HK, generating function); Cover Bound's R-only stages pulled out as (1+κλ) and absorbed by the R rows' δ; skeletons in decision order; caps q_j ≥ τ_j | independent checks R6/R6b/R6c |
| 56 | Thm lp (ii), Step 9 | Perron kernel ĥ₀((s−1)/T) did not match the smoothing defined in 9(i), which gives ĥ₀(s/T); (ii) now follows from (i) by partial summation | reader |
| 57 | Thm lp, Step 2 | N_y := exp*(Π\|_{[1,y]}) called the y-smooth counting measure (false: p² gets ½ for √y < p ≤ y); now a positive Euler proxy with the four properties used | reader |
| 58 | Lemma threshold-mass, case (ii) | interval coefficient 0.6 not given by the written factor 1 ± 0.11δ (0.6385 at δ = ¼); now the centred jitter gives 0.5826, and m′ = 1 in case (ii) | reader |
| 59 | Lemma threshold-mass, statement | allowed every δ ∈ (0, ¼] although case (ii) needs δ ≥ 6H(x)x^{−1/3}; now a hypothesis, checked at its one use | reader |
| 60 | Thm lp, Steps 2–3 | the T₀-tail bounds beyond y were credited to (LP-a), which says nothing past y; now dT₀ ≥ 0 and T₀ − u = E_rig + R (eq:Erig, Lemma T1); (H_BS) sourced to eq:Erig, not eq:T1; Rankin split dropped; F bound extended to all σ | independent check R10 |
| 61 | Lemma threshold-mass, case (i) | counted cofactors m′ by the lag bound alone, without bounding T on intervals possibly shorter than the absorption scale; now split: p ≤ 1.01x^{1/4} (h-windows, Lemma P) and p larger (m′ a single prime, counted by slots); 2.1δx/p² ≤ 4δx/p² | reader |
| 62 | Lemma margin(d)(ii), proof | the length bound κx/X₀ ≤ X₀^{−0.38} < 1 was written for all x ≤ X₀^{1.9}, where it fails (X₀^{0.503}); now stated for x ≤ X₀^{1.01}, the range of (ii) | reader |
| 63 | Lemma margin(c), proof | Σ_{m≤t}1/m = log t + γ + O(2κ) cited from the element-count estimate, which gives only O(κ log t); the bound used is now proved from (H_BS): \|S(t) − log t\| ≤ 1.002, then ≤ log U + 2.004/log y | reader |
| 64 | Lemma goodheights | bad-height density < 0.018 relied on Broucke's mean value theorem with an unspecified constant and "once X₀ is large"; now explicit for every admissible X₀ via Montgomery–Vaughan (constant 3π/2), a class split with spacing > 2, and explicit bounds for every other term | reader |
| 65 | Lemma P, step (v); Lemma ZA proof | Rankin bound Ψ(Y,2y)/Y ≤ e^{−0.9u log u} stated for every Y, false for large Y (exponent goes negative); now under (∗) (exponent ≥ 0.69), checked at both uses (Y = 2yh, and Y = x in ZA), where the exponent is ≥ 0.99999 | reader |
| 66 | Lemma P, rhoA, T1, depcheck | from R11: the proof of Lemma P covered Good(<u) but the statement Good(<t_u); depcheck omitted three real edges; an unchecked localcount aside; plus cosmetic items | independent check R11 |
| 67 | §2–§3 (Thm zeros, Lemmas ZB, designedzero, latenoise, adapted), (G1), Lemma blin(3) | unquantified o(1) terms made explicit for every admissible X₀; found a gap in Lemma ZB (Z_max assumed, not proved), (G1)'s step false for large u, and blin(3)'s order wrong; none changes a conclusion | sweep (#64) |
| 68 | §5 (Freedman inputs, budget, Prop ecl, parameter sizes) | load-bearing ≪/o(1) in §5 made explicit (e.g. s₂\|I\| ≤ e^{−√L}) | sweep (#67) |
| 69 | §4 (noise section) | the stated o(1) convention was smaller than the terms it covered; now o(1) ≤ Λ⁻³ with every term itemised in Prop g1(B) Step 5; other ≪/o(1) explicit | sweep (#67) |
| 70 | Thm lp | log K = O(Λ) made explicit: log K ≤ 98 + 5.9 log Λ (box-spline kernel, explicit contour constants) | sweep (#69) |
| 71 | Prop ecl, low heights | "direct (F1)–(F2) count (1.01\|J\|)^{r₀}/r₀!" omitted the rigid-cofactor sums Σ1/d; the case is now handled by Theorem R, which includes them | reader |
| 72 | Thm caplw, Steps 1 and 5 | "log(2Λ/ℓ) ≥ 16" (actually 15.357) and "107.6(0.334+7.17t)² ≤ 6053" (6058.96 at t = 1) false at Λ = 10⁸; replaced by ≥ 15.3 > 6 and 107.6γ² ≤ 6052.5 | reader |
| 73 | Def good and its consumers; new Remark horizon | Good(<z) certifies queue bounds only up to ž = z − 12 log z − 3 (slots can be ≈ 11 log z long), but the lag bound, (H_BS), Lemma cm, (LP-a) and others were claimed up to z; 10 sites had insufficient written margin (one feeds the E3/E3′ event); now stated once and swept (66 sites) | reader |
| 74 | Lemma margin, μ₀/μ₁ and (c) | μ₁ used the window-filtered K_ℚ, so it contained ν₁ partial windows its proof did not bound; μ₁ now uses the sharp operator and the partial windows sit in μ₀ (already budgeted) | end-to-end check R15 |
| 75 | grid windows; Thm R, PIL, Prop ecl, Cor increment, Lemma P(iv), rowweights | windows near 2z stuck out of J ⊂ [z,2z]; now assigned by left end, J ⊂ [z,2z+1], D = log(2z+1)/log X₀⁻, explicit margins; boundary coverage in Cor increment and Lemma P(iv) repaired | end-to-end check R14 |
| 76 | §2 choice of γ_k; Lemmas goodheights, latenoise; Thm zeros | with "in §3 x_k means x_k⁺", γ_k was chosen from data that depend on R_k(γ_k): circular; and γ_k was not defined pathwise; now chosen below the unshifted scale a_k by an explicit measurable rule | reader |
| 77 | §2 Slots (ϑ_s, s_j) | "only countably many ϑ_s are excluded" false once Abs or R is active; a tie made J_j empty; slots are now hitting times, defined for every ϑ_s and ω | independent check R17 |
| 78 | E3/E3′ (04d), Def good, Table events, Lemma budget | E3/E3′ defined as whole-scale conjunctions but used as per-window events with their own times; now one event E3_W per window, t(W) = max W, measurability shown, every consumer's window times checked | reader |
| 79 | Cor increment; Thm queue (ii); Prop S1S2 | queue windows can begin below x, where the corollary was not stated and the threshold is y(x/2); corollary extended to [u/2, 2u+…], \|I\| ≤ 2H, q ≥ y(u/2), with explicit cofactor bound 2.00002L⁻¹¹ | reader |
| 80 | Cor increment proof; Lemma P (i); 04d s₂ | "q-smooth, so decided no later than q" confuses decision and value order; two more value-from-decision inferences lacked the H/2 allowance | reader |
| 81 | Lemma S (ii), (iii) | smooth-v applied at u_y < 1; (ii) now from (i) there; (iii) sum-to-integral made explicit (7.10486L² + 4L ≤ 7.11L²) | reader |
| 82 | Lemma tau-near, V_P | second dyadic block beyond smooth-v's range near u = L; split at L − 1, Rankin above | reader |
| 83 | X_q, Fr(I), Comp^{(2)}, S1S2 | per-prime counts ran over all latest primes, including rational ones, for which E2(b) is unproved; now jittered only, = C_jit; Comp^{(2)} made the true compensator | reader |
| 84 | Prop g1(B) Step 4 | k := max{j : x_j ≤ x} undefined on [X_sw, x₁); there R' = 0 and the step is void; k = 1 case stated | reader |
| 85 | Lemma heavy (ii) | "< φ, so ≤ φ − 1" with real-valued φ; (ii)'s ≥ Q+r+1 false (counterexample c = 100.2, 155 vectors in ℤ³); now > Q+r, which is all (iii) needs | reader |
| 86 | Thm queue: full blocks, Lindley, peel | real L₀ compared with integer slot counts (the Lindley cut never exists for non-integer L₀); K₀ = ⌊L₀⌋ for counts; Fr(I)(a) restricted to the peeled range | reader |
| 87 | Thm queue, Windows; slot length | density 0.09/L read off eq:G1 without −1/(κu) and with log x for log u; now 0.0899/log u, length ≤ 11.13L·L₀ | reader |
| 88 | Lemma tau-near | p₀ ≥ X₀⁻ false for a rational latest prime just below X₀⁻; now p₀ > X₀/2, already covered by the counting | reader |
| 89 | Lemma noise E(I); Prop pointwise Step 2 | E-bound proved for slot windows, applied to physical intervals A±; extended to all intervals with a 70 log²(2u) boundary term, absorbed by ν̂'s constant | reader |
| 90 | Cor kr-weights(b); Lemma xb; Prop br | stated from X₀ (resp. 2X₀) but applied at τ-near starts ≥ X₀⁻ (resp. points of W_x ≥ 2X₀ − H/2); ranges extended (identity kernel below X₀) | reader |
| 91 | Lemmas ZB, ZBlow | truncated-ramp transform written as (X₀^{−s} − n^{−s})/(sκ) (vanishes at n = X₀); ZBlow's 3n^{−σ} fails for large σ; corrected formula and a support-based bound, allowances unchanged | reader |
| 92 | Thm lp Steps 7–9 | Step 8 discs reached above T_y, where Step 7's zero-free region was not proved; region extended to T_y + 1; a threshold claim reworded | reader |
| 93 | Prop g1(B) Steps 3, 5 | ρ_det and R′_j smooth-change bounds stated at displacement δ, applied at 2δ; restated at 2δ, budgets unchanged | reader |
| 95 | eq:bookkeeping, margin identity, Lemma noise | slot-window bookkeeping applied to physical windows (a slot can carry composites past the window's end); edge residual defined (≤ B + 1) and put in ν with the box term, so the identity is exact | reader |
| 96 | decision order τ_w | τ₁ undefined although Comp^{(2)} uses m = 1; τ₁ := 0 | reader |
| 97 | short-recip; Cor localcount; 04f, 04k | T(J) ≤ 2\|J\| + 2 used on long windows (crude bounds give 2.0001\|J\| + 1); the reported one-copy summation was valid by absorption | reader (diagnosis refined by R29) |
| 98 | Lemma si, Region 1 | e^Q ≤ e²ℓ/τ dropped e^A; A ≤ 2·10⁻³ kept, tail and 60.786 unchanged | reader |
| 99 | Lemma margin(b), decision-order mismatch | \|P − √(u/w′)\| ≤ H/4 fails below P; now H/4 + H²/(8P), prime count derived (≤ 1.51H + 2) | reader |
| 100 | Lemma cm proof | blocks [A, 2A) with ψ(2A) − ψ(A), which counts (A, 2A]; blocks now (A, 2A] | reader |
| 101 | Thm bs Step 7(iii) β_a; App. B bs-cert | printed β_a lacks the code's v + c_u ≤ 0 condition (literal formula fails 44,861 u-cells); code and run descriptions corrected; certificate re-run, unchanged | bs-cert audit R30 |

**Repairs and their check.** All are repaired. #48's first repair covered one configuration type only; #55 closes it (below). A fresh AI checker checked #31–#47, #49–#53, #56–#59, #61–#64, #67, #71 and #72 in twenty-two passes
(`review/recheck/R4.md` §§1–29); #54, #60, #65, #66 and #68–#70 were checked by the checkers of R8 §9, R10, R11 §§12–13, R12 and R13; #74 and #75 by R16, #73 and #76 by R17, and #77 with R17's items by R18, #78 by R19, #79–#82 by R20, #83–#85 by R21, #86 and #87 by R22, #88 and #89 by R23, #90 by R24, #91 by R25, #92 by R26, #93 by R27, #95 and #96 by R28, #97–#100 by R29, and #101 came from the bs-cert code audit R30; the repair of #48 had a separate adversarial check (`review/recheck/R5-pil-repair.md`,
about 107k exact and float checks, including the counterexample that made the support indicator χ_t explicit). R4's work included:
- a toy simulation of the #31 identity;
- arb scans of the new H for 10⁸ ≤ Λ ≤ 10⁵⁰;
- an independent derivation of the count identity's initial value;
- whole-paper sweeps for the patterns behind these defects:
  - variable widths treated as constant;
  - ceilings or freezes inside regular parameters;
  - kernels assumed to have unit mass;
  - unchecked induction bases and omitted base conditions;
  - statement constants stronger than the proof;
  - comments that hide rendered text.

Pass 9 ended with one FIXABLE item (N20, a displayed identity in Lemma margin(d)(iii) that was false although the bounds
hold). Its fix was confirmed in pass 10 (§17). Pass 11 (§18) found #51 (N26); passes 11 and 12 ended with nothing else blocking or
fixable. R5 found the #48 repair CORRECT
WITH FIXES; the fixes were applied, and the same checker then found the live text CORRECT.

**Effect on the conclusions.** None of the one hundred corrections changes a conclusion of the paper. Several required new
arguments, not just new constants: #31, #32, #36, #37, #40, #43, #44, #45, #46, #47, #48, #49, #51 and #52.

**#48: a gap found and closed.** Two later independent checks reached the same conclusion: `review/recheck/R6-cond-check.md` and
`review/recheck/R6b-pil-o3b.md`.
- **The repair holds only per type.** The #48 repair of the Pivot-Integration Lemma is valid for each full configuration
  type.
- **The paper needs more.** Theorem R and Lemma reduction(ii) use the bound summed over all free-prime structures. Summed
  that way, the step loses a factor of about log D per block boundary, and the per-type envelopes exceed Theorem R's
  A_top^k by up to k^k/k!. Exact toys break the old step by up to 1.87×.
- **A partial argument.** R6b's Crossing and Charging Lemmas, not yet checked, close the chain only up to finite heights:
  log L ≤ 51Λ for cor:R-Ecl, and L ≤ (Λ²/29)^10 for the Cover Bound.
- **Consequence and repair.** Theorem A's proof was incomplete until correction #55. #55 sums the block bound over every
  block content. It passed two independent adversarial checks with nothing blocking or fixable: `review/recheck/R9-cond-check-55.md`
  and `review/recheck/R9b-pil-o3b-55.md`, the second by the agent that found the gap. R9b also withdraws the finite-height
  limits of R6b.

**Other independent checks.**
- `review/recheck/R7-margin-var.md` checked #47's large-range estimate: CORRECT WITH FIXES. Its fix is #53.
- `review/recheck/R8-cert-repro.md` reproduced every certificate and independently re-implemented the four proof-step
  certificates. All agree, with no blocking items. Its fixable items are fixed as #54, and the fixes were verified by the same checker (R8 §9).

**Caveat.** These defects survived five rounds of AI checking. The paper should not be regarded as verified until a human
expert has read it.

**Reported but not a defect.** The reader also asked whether Lemma 4.14(ii)'s free-prime factor Σ_k λ_D^k/k! ≤ e^{λ_D}
undercounts repeated free-prime powers, which would need the Euler product ∏(1 − 1/q)⁻¹. It does not. In the allocation of
Prop. cover, each free prime keeps exactly one occurrence, in one row of C. Free primes belong to P(C), and their further
occurrences (counted with multiplicity, including repeated powers in one row) are excess, weighted by ∏_j τ_j^{−e_j} in the
next factor. The text now says this explicitly. No constant changes. (The factor e^{λ_D} itself was later replaced by the
per-row chain bound Ch, in the repair of #46.)
