# Brief: re-check of the paper after the fixes from the first paper check

**Background.**
- A first check of the paper against the refereed source v3 is in `review/paper-check.md`, with sub-reports in
  `review/subchecks/`. Its verdict: faithful, but not yet self-contained. It found:
  - one BLOCKING item, B1: the Beurling–Saias remainder lemma for ℓ ≥ 10¹⁸ was only a sketch;
  - 36 FIXABLE items: D1–D4, I1–I12, S1–S14, P1–P4 and items in its §2–§3;
  - a number of COSMETIC items.
- The authors have since:
  - rewritten B1 in full;
  - applied the FIXABLE items;
  - logged the deviations from v3 as entries #11–#28 in `CORRECTIONS-vs-v3.md`.
- None of the new text has been checked by anyone.

**Objects.**
- The paper: `~/work/beurling-paper/paper/`, with `main.tex` and `sections/*.tex`.
- What changed since the first check: `git -C ~/work/beurling-paper diff HEAD -- paper/ certificates/`.
- The refereed source: `~/work/rh/notes/v3/beurling-greedy-v3.FINAL-2026-10-22.md`, 3072 lines (read-only).
- The approved deviations: `~/work/beurling-paper/CORRECTIONS-vs-v3.md`, entries 1–28.
- Certificates: `~/work/beurling-paper/certificates/`. Appendix B gives the run commands.
  - Use `/tmp/rhscratch/flintenv/bin/python` (python-flint 0.9.0).
  - Always run with `-I -B`, so that no `__pycache__` is written into the repository.

**Your part.** You are one of three checkers. Each owns a set of files and log entries, listed in your launch message. For
your part:

1. **New text, line by line.** Read every changed or new passage in your files, using the git diff to find them.
   - Check each new proof step completely.
   - Recompute every numeric constant independently: arb balls, exact rationals, or careful floats with stated error.
   - Do not trust the authors' numbers. Several earlier "verified" constants were wrong.
2. **First-check items.** For each item of `review/paper-check.md` and the sub-reports in your scope, give one status:
   - RESOLVED (state where);
   - PARTIAL (state what remains);
   - OPEN.
   Also check that the fix itself is correct.
3. **Log entries in your scope.** For each one:
   - (i) it is applied consistently wherever the quantity appears, including in other authors' files (grep the whole
     paper);
   - (ii) it is mathematically correct;
   - (iii) its "no downstream effect" claim is true.
4. **New drift.** Any mathematical difference from v3 in the changed text that is not one of the following is DRIFT:
   - a logged entry;
   - an inlined proof of something v3 delegated to working notes;
   - rewording or notation.
5. **Certificates in your scope.** Re-run them exactly as Appendix B says, and confirm that the quoted outputs match.

**Rules.**
- Classify each new finding as BLOCKING, FIXABLE or COSMETIC, with file:line. Use the definitions in
  `review/paper-check.md` §0.
- For every BLOCKING item, give a concrete failure scenario or counterexample.
- Be adversarial. The rewritten parts were produced under time pressure by the same authors whose earlier sketch failed.
- Do not edit the paper, the notes, the corrections log, or the certificates. Write only your report, and scratch files
  under `/tmp/recheck-<your id>/`.
- Write your report to `review/recheck/<your id>.md`, appending in pieces of at most about 150 lines.
- End with a verdict for your part: are the files in your scope now a complete and faithful presentation of their part of
  the proof of Theorem A?
