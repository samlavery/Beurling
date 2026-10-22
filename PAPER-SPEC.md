# Writing the paper: spec for the section authors (team lead, 2026-10-22)

**Goal.** Turn the refereed v3 (`~/work/rh/notes/beurling-greedy-v3.md`, sha256 b6c6bcda…; read-only) into a self-contained
LaTeX paper in `~/work/beurling-paper/paper/`. It must read like a mathematics paper, and a specialist must be able to check it
using only this paper, the cited literature, and the certificate scripts in `certificates/`.

**The single most important rule: no mathematical drift.** v3 is the refereed source of truth.
- Allowed: rewording, reorganising, LaTeX, better notation, and **inlining proofs that v3 delegated to working notes** (copy
  them from the cited note section, cleaned up).
- Not allowed: changing a statement, constant or hypothesis, or "improving" an argument. If you find an error or a gap while
  writing, STOP and message the lead. Do not fix it silently. Approved corrections are logged in `CORRECTIONS-vs-v3.md`
  (the lead maintains it); only logged deviations from v3 may appear in the paper.

## Ownership (each author writes ONLY their own files)

| File(s) in `paper/sections/` | Author | Content (v3 source) |
|---|---|---|
| `abstract.tex`, `00-intro.tex`, `01-setup.tex`, `02-construction.tex`, `03-zeros.tex`, `06-base-range.tex`, `C-ai-statement.tex`; also `refs.bib`, `../README.md` | beurling-lit | Abstract; introduction (question Q, Theorem A, prior work from v3 §7, novelty, what it does not prove, outline); §0 statement, parameters, non-circularity; §1 construction; §2 zeros; §5 base range; AI statement. §6 numerics: at most a short remark. §9 Lean: omit. |
| `04-noise.tex` (+ optional `04*-*.tex` sub-files that it `\input`s) | gap-localpnt | v3 §3, with the FULL proofs of Thm 3.4 (BS, from gap-localPNT §6.9.3′), Thm 3.13 (LP, gap-localPNT §2/§7′), Lemma M, CM, V. |
| `04x-x0band.tex`, `04k-kernels.tex` (input from `04-noise.tex`) | fix-bprime | Full proofs of Lemmas 3.4A/3.14A/3.14B (fix-Bprime §11–§12′) and of KR Thm 3.6, push-through, Prop 3.8 and Lemma S (fix-Bprime §7, §9, §10). |
| `05-queue.tex` | gap-g3 | v3 §4 in full, including Thm 4.17's analytic proof and Lemma 4.15. |
| `A-rankfull.tex` | verify-cl | Appendix A: Volume Lemma, PIL, FAC, SVL with B1–B3 and Proj_t, Lemma SC, Theorem R (from v3 App. A, verify-CL §R.8a–R.13, lead-notes L1). |
| `B-certificates.tex` | beurling-lit (owners send paragraphs) | One subsection per certificate: what it certifies, the method (arb balls, cell cover, seam handling), how to run it, and the expected output. |

## Conventions
- **Environments and labels.** Use the theorem environments in `main.tex`. Labels are `thm:`, `lem:`, `prop:`, `cor:`, `def:`,
  `eq:`, `sec:` plus a short name, e.g. `\label{lem:xb}`. Put labels that other parts cite into `paper/LABELS.md`
  (append-only; one line each: label, meaning, file).
- **Traceability.** Immediately after each `\begin{lemma}` and similar, add a comment such as `% v3: Lemma 3.14A`. The checker
  uses these to compare against v3.
- **No internal jargon.** Do not mention agent names, "referee A §17", "A10 item", "E2E", "[P]" / "[S]" tags or notes file names.
  Computer-assisted steps say "(computer-assisted; see Appendix~\ref{app:cert})".
- **Macros** go only in `macros.tex`. Append new ones there, with a comment, and avoid clashes.
- **Bibliography.** Append to `refs.bib` (keys like `DMV2006`, `HeathBrown1988`). Use the exact references already verified in
  v3 §7.3.
- **Building.** From `paper/`, run `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/paper-build-<yourname> main.tex`.
  Always use your OWN outdir, because builds run in parallel. Never leave the shared build broken. Write incrementally: one
  subsection per edit, ≤ 200 lines per append.
- **Length** is a guide, not a cap. Expect intro + setup + construction + zeros ≈ 20 pp, §4 noise ≈ 30–40 pp (with BS/LP/X₀ proofs),
  §5 queue ≈ 25 pp, App. A ≈ 15 pp, and App. B ≈ 4 pp.
- **Do not edit** anything in `~/work/rh/notes/`, or other authors' files.
- **When done,** message the lead with: the files, the page count of your part, any statement you could not inline (with
  reason), and any problem found.
