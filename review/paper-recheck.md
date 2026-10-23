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

## Addendum: defects found after the re-check (corrections #31–#52)

After the first public version, a reader reported fourteen defects that all the AI checks above had missed. Repairing them, and
re-checking the repairs, turned up eight more. The full list, with each repair, is entries #31–#52 of `CORRECTIONS-vs-v3.md`:

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

**Repairs and their check.** All twenty-two are repaired. A fresh AI checker checked #31–#47 and #49–#52 in twelve passes
(`review/recheck/R4.md` §§1–19); the repair of #48 had a separate adversarial check (`review/recheck/R5-pil-repair.md`,
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

**Effect on the conclusions.** None of the fifty-two corrections changes a conclusion of the paper. Several required new
arguments, not just new constants: #31, #32, #36, #37, #40, #43, #44, #45, #46, #47, #48, #49, #51 and #52.

**Caveat.** These defects survived five rounds of AI checking. The paper should not be regarded as verified until a human
expert has read it.

**Reported but not a defect.** The reader also asked whether Lemma 4.14(ii)'s free-prime factor Σ_k λ_D^k/k! ≤ e^{λ_D}
undercounts repeated free-prime powers, which would need the Euler product ∏(1 − 1/q)⁻¹. It does not. In the allocation of
Prop. cover, each free prime keeps exactly one occurrence, in one row of C. Free primes belong to P(C), and their further
occurrences (counted with multiplicity, including repeated powers in one row) are excess, weighted by ∏_j τ_j^{−e_j} in the
next factor. The text now says this explicitly. No constant changes. (The factor e^{λ_D} itself was later replaced by the
per-row chain bound Ch, in the repair of #46.)
