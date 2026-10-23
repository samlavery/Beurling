# R5 — independent adversarial check of the PIL label-sum repair (CORRECTIONS #48)

The checker was a fresh AI agent. It was not allowed to write files, so this report was saved by the lead from the checker's
messages. Its scratch scripts were in `/tmp/rhscratch/pil-check/`, which is temporary and not kept.

**Scope.** It checked two things:
- the repair proposed by the Appendix A author (route b″: label sum first, then a block bound with no localisation);
- that author's TeX draft of the repair.

The gap itself, reported by the re-check as R4 §15 "O3", is that the Pivot-Integration Lemma's label sum needs the integrand to
be free of the slot label pointwise in the pivot value, while the carried Euler factors cancel only after integration.

## Verdict on the mathematics: CORRECT WITH FIXES

The repair holds and no constant changes. One statement was false as written: the support restriction had to be carried
explicitly (Fix 1). The other fixes are wording.

**Step 1 (label sum at the last pivot of a run) holds pointwise.**
- *Where the label enters.* The checker went through every place the label s_t could appear. There are only four:
  - the window;
  - 1(G_{<s});
  - the carried 1/Eu_s(s), one per passing row;
  - the order constraint 1(σ(f₁) < s).

  τ_j, Proj_t and (B1) do not depend on the label.
- *Monotonicity.* Eu_s is non-decreasing and Good(<x) is non-increasing in x, so replacing s_t by u_t (the first slot after
  σ(f₁)) is a pointwise upper bound.
- *The factor θ.* (F1) gives θ.
- *Measurability.* u_t never needs to be measurable at the next pivot. Steps 1 and 2 are pathwise, and Step 2's output does not
  contain u_t.
- *The sure top bound.* (F3′)/(S3)(d) at a data-dependent u is legitimate, because it holds pathwise on G_{<u}.
- *The pinned value q*.* It is never used, so its non-monotonicity in the data, which defeats the localisation route, does not
  matter.

**Step 2 (the block bound) is correct.** The checker wrote it out independently.
- *Passing owner of f₁.* An exact count: Σ_S P(the r earliest elements of R are S) ≤ 1, since the events are disjoint. The bound
  is sharp; the ratio tends to 1 − ε.
- *Joining owner.* Telescoping, with one sure bound at the top.
- *Output.* Exactly one carried 1/Eu_s(s_{t+1}) per row, plus A_R e^{2.2/Λ} once per row. There is no 1 + Σ1/p loss. The crude
  per-row bound overshoots by 1.13–35×, which confirms the loss in the old route was real.
- *Hard family.* For n_i = A·f·q_i·d_i (k = 3..6, with Lemma SC's stage rows) the bound is θ^k A_R^k e^{2.2k/Λ}.

**End step.** It is correct, with Eu_s(X₀) = Eu_rat and u_T := X₀ when the early block is empty.

**Fix 1 (a real defect).** Without the restriction u_t ≤ s_max := 2z + 0.51H(2z), Step 2's claim "on every ω" is false.
- *Counterexample.* A joining owner, r = 1, primes 101..2·10⁶, s_max = 1 gives LHS 1.134 > A/E₀ = 1.010.
- *Why it must be stated.* The restriction holds automatically, since σ(f₁) < s_t ≤ s_max. But Step 1 discards s_t, so
  1(u_t ≤ s_max) has to be carried as a factor that depends only on the data.

**Other fixes (wording).**
- (S3)(d) is stated at any slot u ∈ [X₀, s_max] on G_{<u}, and is used once per row.
- The PIL runs in this order: label sum first, then the pivot integrals, then the block bound. The sup-sum example and all
  "cancels exactly" language are removed.
- (S3)(a) is a joint block bound, with the exact-count lemma and the telescoping lemma stated separately.
- SVL (ii) keeps only the structural fact Π g^{−a_g} with a_g ≥ 1.
- The Cover Bound proof and the preamble of Lemma 4.14(ii) now say that the free-prime sum does not factorise blockwise; only
  the per-row output does.

**Tests.** About 107k exact and float checks found 0 violations. They covered:
- Step 2 exactly and by dynamic programming;
- the Step 1 window, with random, non-monotone and adversarial q*;
- all combinations of passing and joining owners, and the end step.

## Verdict on the TeX draft: FAITHFUL, CORRECT WITH WORDING FIXES

There is no mathematical gap, and the constants are unchanged. The draft builds cleanly. Every block bound the paper uses
satisfies the monotonicity requirement:
- (S3)(a)'s right side is non-increasing in s_{t+1};
- the end-step bounds are deterministic;
- τ_j, Proj_t and (B1) are label-free;
- in Prop cover, the excess factor τ_j^{−e_j} is a constant.

**Wording fixes.** W1 and W3 are needed for the lemma as stated to be proved.
- **W1.** The admissible block bounds must be functions of s_{t+1}, of the unprocessed variables, and of the primes decided
  before s_{t+1}. The inherited wording, "decided before the first pivot of P_{t+1}", is too weak.
- **W2.** Restate the invariant: as a function of P_t's labels, the integrand depends only on s_t, through non-increasing factors
  and through s_t > σ(f_t).
- **W3.** At non-last pivots, also drop the order constraints between the pivot and the free data of F_t.
- **W4.** Add a sentence on why u_t needs no measurability.
- **W5.** State (S3)(a)'s summation range, and that the column-to-row assignment is fixed by the type.
- **W6.** Say the indicator is part of each summand, so the bound must hold for every ω.
- **W7.** Update the paragraph "order of decision versus order of value": the top is now at u.
- **W8.** Update the Prop cover proof (05-queue) in the same pass.

These fixes were passed to the authors of Appendix A and §6 for application.

## Hidden assumptions that the TeX must state

- **H1.** At the last pivot, the pending integrand depends on s_t only through:
  - (a) the window;
  - (b) 1(G_{<s_t});
  - (c) the carried factors;
  - (d) 1(σ(f_t) < s_t).

  Here (b) and (c) are non-increasing in s_t. Earlier tops are already constants, and τ_j and Proj_t do not depend on the
  labels.
- **H2.** There is one prime per slot, and f_t is the unique latest column of its block. Hence
  Eu_s(u_t) = Eu_s(σ(f_t))(1 − 1/f_t)⁻¹, and every admissible s_t is ≥ u_t.
- **H3.** Good(<x) is non-increasing in x.
- **H4.** The support restriction u_t ≤ s_max = 2z + 0.51H(2z) holds (Fix 1).
- **H5.** The second case of (F3′), that is (S3)(d), holds pathwise at every slot u ≥ X₀ on G_{<u}, and is used once per row.
- **H6.** For t < T, F_t is non-empty, because runs are maximal. Rational primes count as slot < X₀, so Eu_s(X₀) = Eu_rat and
  Σ_d 1/d = Eu_rat.
- **H7.** After the stage integrals and the τ_j replacement, F_t enters only through Π_g g^{−a_g}, with a_g ≥ 1. The owners
  are fixed by the type.
- **H8.** All terms are nonnegative, so Tonelli applies.
- **H9.** Joint caps, if they are ever used, contribute only a factor that does not depend on the data.

## Tests

The scripts were in `/tmp/rhscratch/pil-check/` and run with `python3 -I -B`.

| Script | What it checks | Result |
|---|---|---|
| `step2_exact.py` | Step 2 in exact rationals. Covers owners, exponents ≥ 1, empty slots, the s_max cut, nested G and w up to ½. Checks both lemmas separately. | 19,475 instances, 0 violations |
| `step2_dp.py`, `step2_sharp.py` | Step 2 at scale: primes up to 2·10⁶, random and decreasing weights, all owner mixes, sup over g. | 0 violations. The bound is sharp (ratio 0.9999 at w = 10⁻⁴). |
| `step1_window.py` | Steps 1 and 2 end to end. Real slots with spacing ≥ 0.99, varying H, θ computed pathwise. q* is random, multiplicative, non-monotone or adversarial. | 16,000 instances, 0 violations. Max true/Step 1 ratio is 0.98. |
| `types_check.py`, `types_check_early.py` | Step 2 and the end step on configurations from real rank-full types. Uses Lemma SC's lex-first stage rows, both C = B′ and random covers, and the hard family for k = 3..6. | 68,418 exact checks, 0 violations |
| `support_needed.py` | Step 2 without the restriction u ≤ s_max. | Fails, LHS 1.134 > 1.010. This is Fix 1. |

The paper with the draft builds with latexmk exit 0, 0 LaTeX warnings, and the baseline 18 overfull boxes.

## Confidence

The checker has high confidence that the repair, with Fix 1, is correct:
- Both new pathwise steps are elementary inequalities: a monotone replacement, and either the exact count or the
  telescoping.
- Each was proved by hand and tested exactly, adversarially and at scale.
- The probabilistic steps are unchanged by the repair: the conditional density at each pivot and the iterated conditioning.
- The only new obligation is that the block bound's output be measurable at the next pivot. The output of (S3)(a) is.

**Limitation.** The toys test only the pathwise steps, not the filtration. That part rests on the argument.

## Where a later checker should look hardest

1. The claim that the integrand depends on s_t only through (a)–(d) of H1. Enumerate every pending factor in Thm R and in
   Prop cover.
2. The measurability requirement in Lemma pil (W1).
3. That the support indicator survives the q-integral and the SVL cap-dropping, as a factor that depends only on the data.
4. The exact-count lemma's use of a column assignment fixed by the type.
5. The end step when F_T is empty: u_T = X₀ and Eu_s(X₀) = Eu_rat.
6. Consistency with 05-queue, in the Prop cover proof and Lemma 4.14(ii).

## Check of the applied text (first read)

The checker compared the live A-rankfull.tex with the pre-#48 file. The differences were exactly the supplied diff, in:
- Lemma pil;
- Lemma fac;
- one word of rem:widened;
- SVL (ii)/(iv).

The 05-queue changes were confined to three places:
- the Ch item and the proof of Prop cover;
- the preamble of Lemma 4.14(ii);
- the deletion of the λ_D definition.

A private copy built with exit 0, 0 warnings and 18 overfull boxes, and eq:A-exactcount and eq:A-telescope resolve.

**Fixes 1–5 are implemented correctly.**
- χ_t is carried through every step that needs it.
- (S3)(d) holds at any u ∈ [X₀, s_max], which also covers F_T = ∅ through u = X₀.
- The PIL order is right. Step (i) commutes with the run's integrals, because the factors it changes do not involve the
  run's pivot values.
- The exact count, with its sharpness remark (1 − ε)(1 − Π(1 − 1/p)), is correct.
- The telescoping is correct: χ is 1 on an initial segment, so the sum is ≤ Eu_s(u(g*)) ≤ A_top.
- The SVL trims are correct.
- Ch ≥ A_top.

That read ran just before the W1–W7 wording fixes landed, so it reported W1, W2, W3, W5 and W7 as still open. The re-read of
the live file after W1–W7 follows.

## Re-read of the live text after W1–W7

**Verdict: CORRECT.** All seven wording fixes are implemented as intended, including W1 and W3, so the lemma is now
literally right. Nothing else changed.

**Scope of the changes.** The checker rebuilt the live file from the pre-#48 file plus the repair diff plus the W diff, and
the result matched exactly.
- In Appendix A the changed lines are l.185–533 of the original: Lemma pil, Lemma fac, one word of rem:widened, and SVL
  (ii)/(iv).
- 05-queue.tex is unchanged since the first read.
- A private build exits 0 with 0 warnings and the baseline 18 overfull boxes.

**Each fix:**
- **W1.** Block bounds are functions of s_{t+1}, of the unprocessed variables and of the primes decided before s_{t+1}. This
  is what P_{t+1}'s other pivots need, and (S3)(b) satisfies it.
- **W2.** The restated invariant is correct.
- **W3.** All decision-order constraints involving s are dropped, except s > σ(f_t) at the last pivot. So "Ψ does not depend
  on s" is literally true at a non-last pivot.
- **W4–W7.** Correct.
- **New comment.** The added "Logged correction 48" comment is a whole-line comment.

**Assumptions H1–H9.** All are stated in the TeX. H6 was only partly explicit, and H9 does not arise because the main line
uses no capped cofactor.

**Two optional tightenings.** The lead applied both:
- "for t < T the block F_t is non-empty, since the runs are maximal";
- "(and of no other label)" in Lemma pil (iii).

The build is clean and both render.
