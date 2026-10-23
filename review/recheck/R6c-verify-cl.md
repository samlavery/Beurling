# R6c: the repair author's response to the #48 union objection

verify-cl, the author of the #48 repair, assessed pil-o3b's objection (R6b). It edited no files. Its toy scripts were in
`/tmp/rhscratch/pil-o3/union/`, which is temporary.

**Verdict: pil-o3b is right on scope.** The repair proves Lemma pil and (S3) for one fixed full type. Both consumers use the
union over free structures, and there a loss remains. The loss is smaller than pil-o3b's figure of log D.

## 1. What a type fixes

- **Def config-type (App A)** fixes the columns in decision order, the full matrix E (free columns included) and the tails.
  So PIL and (S3), as stated, are per full type, and r is fixed.
- **Theorem R's reduction** records only the pivot pattern E_P, the labels and the cofactors c_i. The cofactors are summed as
  data, so the free structure is not part of the type: this is the union. cor:R-Ecl inherits it.
- **Prop cover's type** is the full exponent pattern, so its per-type statement is fine.
- **Lemma reduction(ii)** then sums over types with only Ch ("kept free primes in all blocks + tail"), times D, times
  L^{2.1}, per row. It has no count of free structures, so Ch is being used as the bound for the union.

So both consumers need the union.

## 2. Can the repair be extended?

- **A version with variable r.** Summing eq:A-exactcount over r gives Σ_r P(|R| ≥ r) = E|R| = Σ1/g. That is sharp, so this
  fails.
- **Refining the type to fix r.** This does not help either: the per-type bounds do not decay in the free structure, so the
  type count cannot be absorbed.
- **A joint telescoping bound for the union, without using q\*.** This works:
  - order the data by its latest prime, and use ΣK·Eu^{j−1}ΔEu ≤ (K/j)A^j;
  - with π passing chain rows and j ≥ 1 joining chain rows at a block, the union then costs at most (1 + π/j)(1 + O(j/X₀))
    times the paper's target;
  - toys with an adversarial q\* reach 1.62 (π = j = 1) and 2.51 (π = 3, j = 1), so nothing that ignores q\* can beat this.
- **Why that is not enough.**
  - In Theorem R (C = B′), every block has j = |P_t| ≥ 1, but the product Π_t|P_{≤t}|/|P_t| can be as large as k!.
  - In the Cover Bound, a block may have j = 0, which gives a loss of about π·λ.
  - Adding pil-o3b's charging only gives L ≲ e^{Λ/2}, no better than its own range.

## 3. pil-o3b's family, summed as the paper sums it

Each joining row's top gets A_top, and A_top bounds that row's Euler sum up to s_max. So the joining row n2 pays for n1's
piece, since Σ_c 1/c ≤ Eu(s_max)/Eu(a) ≤ A/Eu(a). Exact toys with pil-o3b's additive q\*:

| Case | Ratio as the paper sums it | pil-o3b's ratio, passing row only |
|---|---|---|
| no joining row has primes in F_t (j = 1, 2) | ≤ 0.99 | up to 1.86 |
| the full union (j = 1, j = 2) | ≤ 1.0000 | 4.7 and 16.3 |

So "1 + 0.56 log D" is measured against the passing row alone. Summed as the paper sums it, no violation was found.

## Recommendation

Reopen #48 as "repaired per full type, open for the union" (Theorem R's pattern sum and reduction(ii)'s Ch).

The likely fix is to prove that the union bound, normalised as the paper normalises it, is ≤ 1 + o(1). That proof would use
the multiplicative structure of q\* together with the slack from the joining rows. The toys support this, but there is no
proof yet, and the j = 0 blocks of the Cover Bound need separate handling. Until then, pil-o3b's height ranges are what is
proved.
