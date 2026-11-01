# Summary of changes for run 9b767914-9a7a-432a-9d56-6041fa3dd2f7
I now have `beurling-paper.pdf` and used it (§3.4–3.5, Lemma 3.6, Corollary 3.8, and the bound \(T'_{\mathrm{cont}} \le 1.01\)). Four items from your list are removed or reduced: the construction scales, infinitely many placed primes, `Landing` and `LandingInit`. The slot model, `QueueWindowData`, `Lemma48PiecesCount`, `TableBudget` and the cluster event are still assumed. The landing data now rest on two new, narrower assumptions (`SlotFacts` and `JitterWidthRegular`). The full project builds with no `sorry` and no new axioms, and Corollary 2.2 is proved from the new top-level hypothesis.

**New top-level hypothesis.** `Theorem21InputsO` (in `RequestProject/Beurling/Construction/LandingDerive.lean`) replaces `Theorem21InputsL`. `corollary_2_2_of_O` proves Corollary 2.2 from it, through the chain O → N → M → L.

**What was removed from the assumptions:**
- **Construction scales.** \(a_k\) is now defined as `constructionScale`. `constructionScale_spec` proves \(X_0 \le a_k\) and \(0 < a_k \le x_k \le 1.001\,a_k\) (`Construction/Scales.lean`).
- **The link to \(P(\omega)\).** `ArrivalsLinked` says each slot's arrivals \(A_j\) equal the number of composite elements of \(P(\omega)\) in that slot.
- **Infinitely many placed primes.** This is now proved from the link and the target formula (`placed_infinite_of_linked`, `Construction/Link.lean`).
- **`Landing` and `LandingInit`.** These are now proved for the construction (`landing_of_linked`, `landingInit_of_linked`). The steps, in `Construction/ElemCount.lean` and `Construction/SlotCounts.lean`:
  - \(N(x) = 1 + \#\text{primes} + \#\text{composites}\).
  - The split of the primes up to \(x\) into the counts \(E_\pm\).
  - Lemma 3.6, derived by induction from its base case.
  - \(C \le A_k\).
  - \(E_\pm \le H(x) + 3/2\).
  - \(H(x) \le H(X_0) + 2\) on the initial range, proved from the formula for \(H\) (`capH_initial_le`).

**Still assumed in `Theorem21InputsO`:**
- **The slot model \(M(\omega)\), as data.** It is tied to \(P(\omega)\) only through `ArrivalsLinked`. Building it slot by slot needs causality (Lemma 3.5) and slot-gap bounds, which are not formalized.
- **`SlotFacts`** (new):
  - the base case of Lemma 3.6;
  - no composite lies in \((X_0, s_{j_0})\);
  - a window \((a, b]\) contains at most \(1.01(b-a) + 1\) starts of slots that receive a prime.

  The paper proves these outside a probability-zero event; here they are required on the whole good event.
- **`JitterWidthRegular`** (new): if \(y - H(y)/2 \le x \le y\) then \(H(y) \le H(x) + 1/4\). This is a fixed property of \(H\) (Theorem 6.23(c)), but proving it needs estimates on the \(\bar M_1^2\) part of \(H\) that are not done.
- **`QueueWindowData`, `Lemma48PiecesCount`, `TableBudget`** and **the cluster event**, unchanged.

`BSCERT_NOTES.md` has a new section that maps each step to its Lean name. The Properties table has new rows for these results and definitions. All new and edited files are published.