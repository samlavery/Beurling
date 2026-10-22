# Brief: final check of the paper against the refereed v3

**Objects.**
- The paper: `~/work/beurling-paper/paper/`. `main.tex` and `sections/*.tex` build to about 94 pp.
- The refereed source: `~/work/rh/notes/v3/beurling-greedy-v3.FINAL-2026-10-22.md` (3072 lines, sha256 b6c6bcda…). It is read-only.
- The approved deviations: `~/work/beurling-paper/CORRECTIONS-vs-v3.md` (entries 1–10).
- Certificates: `~/work/beurling-paper/certificates/`. Appendix B of the paper gives the run commands. python-flint is at
  `/tmp/rhscratch/flintenv/bin/python`; if that has gone, run `pip install python-flint` into a fresh venv under /tmp.

**Tasks.** Write the report to `~/work/beurling-paper/review/paper-check.md`, in sections of at most about 150 lines each.

1. **Drift.** Compare every theorem, lemma, proposition, corollary, definition and displayed constant in the paper with v3. The
   `% v3: …` comments map paper items to v3 labels. Every mathematical difference must be either:
   - (a) a logged entry in CORRECTIONS-vs-v3.md;
   - (b) an inlined proof of something v3 delegated to working notes; or
   - (c) pure rewording or notation.
   Anything else is DRIFT. Also check that each of the 10 logged entries is (i) applied correctly, consistently, wherever the
   quantity appears, and (ii) mathematically correct, with its stated "no downstream effect" true.
2. **Self-containedness.** The paper must be checkable from itself, the cited literature, and the certificates. Flag:
   - any proof step that only points elsewhere ("see notes", "as in [internal]");
   - any claim with neither a proof, a literature citation, nor a certificate;
   - any inlined proof that is incomplete.
   In particular, check the newly inlined proofs: Thm 3.4 (BS) and its Z1/Z2/ℓ ≥ 10¹⁸ parts, Thm 3.13 (LP/LP⁺) with its Landau
   lemma, Lemmas M/CM/V, Thm 3.6/3.6′ (KR), Prop. 3.8, Lemmas 3.14A/B, Thm 4.17, and Appendix A.
3. **Build.** Run `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/paper-check-build main.tex` from `paper/`.
   Report undefined references and citations, multiply defined labels, and the page count.
4. **Certificates.** Run every certificate exactly as Appendix B says. Confirm the printed outputs match the quoted ones.
5. **Presentation.** Flag:
   - leftover internal jargon: agent names, "referee A §17", "A10", "E2E", [P]/[S] tags, working-note file names in the text
     (source comments are fine);
   - anything a specialist reader would find unclear or misleading in the intro and the statement of Theorem A, including the
     novelty claims against the cited literature.

**Rules.**
- Classify each finding as BLOCKING (wrong or unproved main-line step, or unlogged drift that changes mathematics), FIXABLE, or
  COSMETIC, with file and line.
- Do not edit the paper, the notes, or the corrections log. Write only your report and scratch files under /tmp.
- Run Python with `-I`.
- You may split the work across sub-agents (for example one per paper section) if that helps. If you do, merge their findings into
  one report.
- End the report with a verdict: does the paper faithfully and self-containedly present the refereed proof of Theorem A?
