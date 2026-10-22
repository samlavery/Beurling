# Discrete Beurling number systems with integer error O(x^θ), θ < 1/2, whose zeta function has no zero-free half-plane

Samuel Lavery (sam.lavery@gmail.com)

> **Status: draft. The proof has not been verified by a human expert.**
> The construction, the proofs and the certificate code were developed with extensive use of AI agents (Claude). Every review
> so far was done by AI agents; the reports are in `review/`. The author takes responsibility for the manuscript and welcomes
> scrutiny. See the statement on AI use (Appendix C of the paper, `paper/sections/C-ai-statement.tex`).
>
> An AI consistency check of the LaTeX paper against the refereed draft is in `review/paper-check.md`, with its section
> reports in `review/subchecks/`. It found one blocking gap, a proof step that was only sketched, and 36 fixable items. After
> the fixes, three fresh AI checkers re-checked every changed passage (`review/paper-recheck.md`, reports in
> `review/recheck/`). They found nothing blocking. Every fixable item they raised has been fixed, as have most cosmetic ones. Writing and checking the paper
> turned up thirty logged slips in the refereed draft, none of which changes any conclusion. They are listed, with
> justifications, in `CORRECTIONS-vs-v3.md`.

## The result

A *discrete Beurling generalized number system* is a sequence of real numbers 1 < p₁ ≤ p₂ ≤ … → ∞ (generalized primes)
together with the multiplicative semigroup they generate. Let N(x) count its generalized integers up to x, and let ζ_P be its
zeta function.

**Question Q.** If N(x) = Ax + O(x^θ) for some θ < 1/2, must ζ_P be zero-free on some half-plane Re s > 1 − ε?

Applied to the ordinary integers, a positive answer would give a zero-free half-plane for the Riemann zeta function.

**Theorem A (informal).** Let θ ∈ [1/4, 1/2 − 10⁻⁴]. There is a discrete Beurling system with N(x) = x + O(x^θ log* x)
(log* the iterated logarithm), whose zeta function has zeros ρ_k with Re ρ_k = 1 − (3 log log x_k + O(1))/log x_k → 1.

So the answer to Q is negative. Equivalently, there is a discrete [1, β]-system with β ≤ θ < 1/2. The result says nothing about the
Riemann zeta function itself.

The system is built by a randomised greedy rule with feedback from the integer count. The main work is a positive drift for the
queue of composite elements at every scale. This rests on a sharp resolvent bound of Beurling–Saias type, a local prime number
theorem for the realised system, and a counting theorem for clusters of composites in short windows.

## Repository layout

| path | contents |
|---|---|
| `paper/` | the paper (LaTeX). `main.tex` inputs the files in `paper/sections/`. |
| `certificates/` | the computer-assisted parts and numerical cross-checks (Python 3), described in Appendix B of the paper |
| `review/` | the AI referee reports written while the proof was developed (two component referees and one end-to-end referee; they refer to working notes that are not included here), the AI consistency check of the paper (`paper-check.md`, `subchecks/`), and the re-check after the fixes (`paper-recheck.md`, `recheck/`) |
| `CORRECTIONS-vs-v3.md` | every deviation of the paper from the refereed draft ("v3"), with justification |
| `PAPER-SPEC.md`, `paper/LABELS.md`, `review/PAPER-CHECK-BRIEF.md`, `review/RECHECK-BRIEF.md` | process documents: the instructions given to the AI agents that wrote and checked the paper |

## Building the paper

From `paper/`:

```
make
```

or `latexmk -pdf main.tex`. A standard TeX Live installation (amsart, amsmath, mathtools, enumitem, hyperref, cleveref) is enough.

## Running the certificates

The certificates need Python 3 and, for the interval-arithmetic parts, `python-flint` (tested with 0.9.0). Commands and expected
outputs are listed in Appendix B of the paper:

| directory | what it checks |
|---|---|
| `certificates/bs-cert/` | the computer-assisted part of the Beurling–Saias bound (Arb ball arithmetic over a cell cover); see also its `README.md` |
| `certificates/finite-n/` | the finite computations on the integers used in Section 5 (Lemmas CM, V and threshold-mass, the squarefree average); standard library, exact or with stated rounding bounds |
| `certificates/x0-band/` | the small range of the bound for the jump of the target at X₀ (exact computation) |
| `certificates/capl-cert/` | a numerical cross-check of the capacity theorem, which is proved analytically |
| `certificates/lemma-sc/` | a numerical check of Lemma SC (exact rational arithmetic) |
| `certificates/svl-stress/` | numerical corroboration of the Staged Volume Lemma's structural claims; not part of the proof |
| `certificates/depcheck/` | that the same-time dependencies between the results of the paper form an acyclic graph |

## Licences

The paper (`paper/`, `review/`) is licensed under CC BY 4.0 (`LICENSE-paper.txt`). The code (`certificates/`) is licensed under
MIT (`LICENSE-code.txt`).
