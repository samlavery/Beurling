# Discrete Beurling number systems with integer error O(x^θ), θ < 1/2, whose zeta function has no zero-free half-plane

Samuel Lavery (sam.lavery@gmail.com)

> **Status: independent human review pending.** The proof has not been verified by a human expert, and it is not formally
> verified (see [Lean formalization](#lean-formalization)).
>
> **A gap found and closed after publication (corrections #48 and #55, 2026-10-22).**
> - Two independent AI checks found that the first repair of #48 (the label sum of Appendix A's Pivot-Integration Lemma)
>   held only for one configuration type. Theorem R and the Cover Bound use the bound summed over all free-prime structures
>   (`review/recheck/R6-cond-check.md`, `review/recheck/R6b-pil-o3b.md`). For a time, the proof of Theorem A was
>   therefore incomplete.
> - Correction #55 replaces the block bound with one that sums over every block content. Theorem R gains a factor
>   k^k/k! ≤ e^k, and the Cover Bound's extra factors are absorbed by the rows outside the cover. No conclusion changes.
> - #55 passed two further independent adversarial AI checks (`review/recheck/R9-cond-check-55.md`,
>   `review/recheck/R9b-pil-o3b-55.md`). One was by the agent that found the gap. Neither found anything blocking or fixable.
>   Like every other repair here, #55 has not been checked by a human.
>
> The construction, the proofs and the certificate code were developed with extensive use of AI agents (Claude). The systematic
> reviews so far were done by AI agents; their reports are in `review/`. A reader has also reported defects (below). The author takes responsibility for the manuscript and welcomes
> scrutiny. See the statement on AI use (Appendix C of the paper, `paper/sections/C-ai-statement.tex`).
>
> An AI consistency check of the LaTeX paper against the refereed draft is in `review/paper-check.md`, with its section
> reports in `review/subchecks/`. It found one blocking gap, a proof step that was only sketched, and 36 fixable items. After
> the fixes, three fresh AI checkers re-checked every changed passage (`review/paper-recheck.md`, reports in
> `review/recheck/R1–R3.md`). They found nothing blocking.
>
> **Defects found after the AI checks.** After the paper was first published here, a reader reported thirty-five further defects
> that every earlier AI check had missed:
> - a strip identity used as exact although the box widths vary;
> - a jitter width that jumps (through a ceiling and a per-scale freeze) although its regularity is used throughout;
> - two bounds for a smoothing kernel that wrongly assume unit mass and unit weight;
> - an unproved initial value in the count identity, and an initialisation issue at X₀;
> - a missing base condition in the definition of t-dense numbers;
> - an overstated independence claim (the slots of distinct primes are not independent; only the conditional jitter law
>   holds, and that is all the proofs use);
> - lower bounds on jittered primes written with X₀ where only X₀⁻ = X₀ − H(X₀)/2 holds (in Appendix A and in an
>   Euler-product bound);
> - a high-frequency Mellin tail in the short-window prime number theorem that was declared negligible but never bounded;
> - a Cover Bound whose right side was a sum over the realised (random) primes, compared with an expectation;
> - a missing support convention for the prime density at X₀. With the convention that makes the margin identity exact,
>   the margin has an edge term just below small multiples of X₀ (from 2X₀ on), and its constant drops from 0.97 to 0.82
>   up to X₀^1.01;
> - a Rankin bound in the row-weight lemma claimed for every exponent η ∈ [¼, 1), although its Euler product diverges as
>   η → 1 (it is used only at η = ¼);
> - a bound for the square-prime source s₂ in the noise section whose Γ factor exceeds 1 and whose range started at X₀
>   instead of X₀⁻; its repair also found the Dickman variable applied the wrong way round, so the bound is re-derived;
> - in the local prime number theorem, a Perron kernel that did not match the defined smoothing, and an auxiliary Euler
>   proxy misdescribed as the counting measure of y-smooth elements;
> - in the edge term of Lemma margin(d), a single-integer argument written over a wider range of x than the one
>   where it holds, and in Lemma margin(c) a harmonic-sum approximation cited from an estimate that does not give it;
> - a bad-height density bound in the good-heights lemma that rested on a mean value theorem with an unspecified
>   constant ("once X₀ is large"), now explicit via Montgomery–Vaughan;
> - a Rankin bound in Lemma P stated for every Y, although its exponent goes negative for large Y (it is used only where
>   the exponent is near 1);
> - in the cluster-event proposition, a "direct count" at low heights that omitted the sums over rigid cofactors (the
>   proof now uses Theorem R there, as elsewhere);
> - two intermediate numerical comparisons in the capacity theorem that fail at Λ = 10⁸ (the conclusions hold);
> - in the threshold-mass lemma, a statement wider than its proof (a missing lower bound on δ), an interval constant
>   that the written derivation did not give, and a count of cofactors that used the lag bound without bounding the
>   target on short intervals;
> - a stopping-time horizon: the good event Good(<z) certifies the queue bound only up to z − 12 log z − 3, because
>   a slot can be about 11 log z long, but several statements used queue-derived bounds right up to z (one of them
>   feeds a bad event). The certified horizon is now stated once and every use was checked;
> - a circular choice of the zero heights γ_k: under the convention "in Section 3, x_k means x_k + 2H(x_k)", the data
>   that chose γ_k included primes whose slots were driven by the oscillation R_k(γ_k) itself. γ_k is now chosen from
>   data below the unshifted scale, by an explicit rule defined on every sample path;
> - the noise events E3/E3′ defined as whole-scale conjunctions, while the stopping-time argument used each window's
>   bound as its own event at its own time; they are now one event per window, with time max W;
> - in the queue bound, windows that start below the dyadic scale x, where Corollary increment was not stated and the
>   absorption threshold is the lower block's y(x/2); the corollary now covers them;
> - a cofactor called "q-smooth" because its primes were decided before q (decision order is not value order for
>   jittered primes), and two other value bounds inferred from decision order without the jitter allowance;
> - two applications of the Dickman-quality smooth-number lemma outside its range 1 ≤ u ≤ log z (in Lemma S and in the
>   τ-near bound); both cases are covered by bounds already in the paper;
> - the per-prime counts of the queue martingale defined over all latest primes, including the rational primes of the
>   rigid base (for which the proof of one of the bad events does not apply); they are now restricted to jittered primes,
>   which is what the excess identity counts;
> - an oscillation index k := max{j : x_j ≤ x} used on a range that starts below x₁, where the set is empty (the
>   oscillation term is then simply 0);
> - in the Heavy Subspace Lemma, an integer rounding of a real-valued threshold ("< φ, so ≤ φ − 1"), which made one
>   part of the lemma false (with an explicit counterexample); the correct strict bound is all that is used.
>
> Repairing these and re-checking the repairs, and three further independent AI checks (R6–R8 in `review/recheck/`),
> turned up twenty more. The most serious were:
> - a gap in the label sum of the Pivot-Integration Lemma (Appendix A): the carried Euler factors cancel only after
>   integration, not pointwise as the argument needed. Its first repair (#48) covered one configuration type only. The
>   repair now in the paper (#55) covers the summed form the paper uses; see above;
> - a gap inherited from the refereed draft in the check of the Beurling–Saias hypothesis (H_BS): the decay of the rigid
>   error that it needs was asserted but never proved. It is now proved (Lemma T1, eq:Erig).
> - a sweep for unquantified "o(1)", "≪" and "once X₀ is large" (#67–#70), which made every such step explicit for every
>   admissible X₀. It found that the noise section's stated o(1) convention was smaller than the terms it covered, and
>   two inherited order-of-magnitude slips (in the positivity margin and in Lemma blin(3)); none changes a conclusion.
> - two end-to-end AI re-derivations, of Appendix A (R14) and of the base-range section (R15), found no blocking
>   defect. R15 found that the Huxley-error term μ₁ was defined with partial windows that its bound did not cover
>   (#74); R14 found that grid windows near 2z stick out of the range that Theorem R assumes (#75). The check of #76
>   found that the existence of the slot offset ϑ_s was unproved, and that a tie made a slot empty (#77).
>
> These are entries #31–#85 of `CORRECTIONS-vs-v3.md`. All are repaired.
> - **The repairs of #31–#47, #49–#53, #56–#59, #61–#64, #67, #71 and #72** were checked by a fresh AI checker in
>   twenty-two passes (`review/recheck/R4.md`). #65 and #66 were checked by the R11 checker (`review/recheck/R11-absorption.md` §§12–13);
>   #68, #69 and #70 by independent checks R12 and R13; #73–#77 by independent checks R16, R17 and R18; #78 by R19; #79–#82 by R20; #83–#85 by R21.
> - **The certificate fixes of #54** were checked by the R8 checker (`review/recheck/R8-cert-repro.md` §9).
> - **The repair of #60** was checked by the R10 checker (`review/recheck/R10-lp-transfer.md`, re-check of #60).
>   The passes ended with nothing blocking or fixable.
> - **The first repair of #48** passed one adversarial AI check (`review/recheck/R5-pil-repair.md`). Two later
>   independent checks found that it holds only per configuration type. Its replacement, #55, passed two independent
>   adversarial checks (R9, R9b).
> - **The reports.** Independent checks of #47's large-range estimate and of every certificate are in
>   `review/recheck/R7-margin-var.md` and `review/recheck/R8-cert-repro.md`. An independent check of the local prime
>   number theorem's positivity transfer is in `review/recheck/R10-lp-transfer.md`, and of the absorbed-element sparsity chain in
>   `review/recheck/R11-absorption.md`. End-to-end checks of Appendix A and of the base-range section are in
>   `review/recheck/R14-appA-e2e.md` and `review/recheck/R15-sec6-e2e.md`.
>
> None of the eighty-five logged corrections changes a conclusion of the paper. But these
> findings show that the AI checks are no substitute for expert review.

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

## Lean formalization

An automated Lean 4 formalization by [Aristotle](https://aristotle.harmonic.fun) (Harmonic) did not verify the main theorem. It
reduced the theorem to a single unproved lemma and proved everything around that lemma. The Lean project is in [`lean/`](lean/);
the status and blockers are in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).

- **Proved:**
  - a Rouché-type zero criterion, `exists_zero_of_near_model`. It is proved from the maximum modulus principle, since
    Mathlib has no Rouché theorem, and it is the last step of Theorem 4.9.
  - the derivation of the main theorem (Corollary 2.2) from that criterion and one remaining input.
- **Blocker, the only `sorry`: `exists_system_near_model`.** This is the existence of the system together with, for every
  ε > 0, a disc near Re s = 1 on which a holomorphic model with a zero at the centre is close to ζ_P. It is the whole of the
  paper before the Rouché step:
  - the construction (Section 3);
  - the lag bound (Sections 5–7, Appendices A and B);
  - Lemmas 4.2–4.8.

  Formalizing it would also need the Huxley–Heath-Brown short-interval prime number theorem and the Montgomery–Vaughan
  mean value theorem, neither of which is in Mathlib.

## Repository layout

| path | contents |
|---|---|
| `paper/` | the paper (LaTeX). `main.tex` inputs the files in `paper/sections/`. |
| `certificates/` | the computer-assisted parts and numerical cross-checks (Python 3), described in Appendix B of the paper |
| `review/` | the AI referee reports written while the proof was developed (two component referees and one end-to-end referee; they refer to working notes that are not included here), the AI consistency check of the paper (`paper-check.md`, `subchecks/`), and the re-check after the fixes (`paper-recheck.md`, `recheck/`) |
| `lean/` | the Lean 4 project from Aristotle (Lean/Mathlib v4.28.0): definitions, continuation of ζ_P, the zero criterion, the main theorem conditional on one `sorry`, and Aristotle's report |
| `LEAN-FORMALIZATION.md` | status of the Lean formalization: what is proved, and the one unproved lemma |
| `CORRECTIONS-vs-v3.md` | every deviation of the paper from the refereed draft ("v3"), with justification |
| `PAPER-SPEC.md`, `paper/LABELS.md`, `review/PAPER-CHECK-BRIEF.md`, `review/RECHECK-BRIEF.md` | process documents: the instructions given to the AI agents that wrote and checked the paper |

## Building the paper

A compiled copy is checked in as [`beurling-paper.pdf`](beurling-paper.pdf) (108 pages), built from the sources in this
repository. To rebuild it, run from `paper/`:

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
| `certificates/finite-n/` | the finite computations on the integers used in Section 5 (Lemmas CM, V and threshold-mass, the squarefree average); Arb balls and exact rationals (needs python-flint) |
| `certificates/x0-band/` | the small range of the bound for the jump of the target at X₀ (exact computation) |
| `certificates/constants/` | numerical constants quoted in Sections 5 and 7 (ordered factorisations, the X₀-band ranges, the integrals of eq:mu1sum); Arb balls (needs python-flint) |
| `certificates/capl-cert/` | a numerical cross-check of the capacity theorem, which is proved analytically; and `rankin_R.py`, a proof step: the Rankin constants of Lemma rowweights (needs python-flint) |
| `certificates/lemma-sc/` | a numerical check of Lemma SC (exact rational arithmetic) |
| `certificates/svl-stress/` | numerical corroboration of the Staged Volume Lemma's structural claims; not part of the proof |
| `certificates/depcheck/` | that the same-time dependencies between the results of the paper form an acyclic graph |

## Licences

The paper (`paper/`, `review/`) is licensed under CC BY 4.0 (`LICENSE-paper.txt`). The code (`certificates/`) is licensed under
MIT (`LICENSE-code.txt`).
