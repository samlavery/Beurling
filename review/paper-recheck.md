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
