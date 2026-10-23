# R9b: pil-o3b's adversarial check of correction #55, the repair of the #48 union gap

The checker was pil-o3b, the agent that first raised the union objection (R6b). It worked independently of cond-check (R9),
on a read-only copy of the live tree, diffed against 26b0656. It was not allowed to write files, so the lead saved its
messages here.

## Verdict: CORRECT

There are three COSMETIC fixes (§3), and no BLOCKING or FIXABLE defects.

The core of #55 is sound:
- the variable-content block bound (S3)(a), eq:A-Grec;
- the sum over run structures, k^k/k! (eq:A-HK and the closed form via the tree function);
- the cor:R-Ecl arithmetic with 15e;
- the Cover-Bound charging (1+κλ)^{s_R}.

The new bound is pathwise and does not depend on q*, so it majorises the true union for every law of the pinned value. Every
toy agrees.

## 1. pil-o3b's family and the adversarial pinned values, and a correction to R6b

### (a) Majorisation holds

- The label step uses u_t, the first slot after the latest block prime. It is pointwise in q, in the block data and in ω.
- (S3)(a) is a pathwise inequality over all contents.
- So nothing depends on the pinned value q*, and neither the family nor the adversarial settings can break it.

**Numerical checks.**
- **block55_check.py** (2000 instances).
  - Contents are enumerated explicitly: every subset of primes, with every nonempty support pattern over the K chain rows and
    exact exponent sums.
  - The pinned value is q* = Q + Σ d·(supports), with d > 0 on passing rows, so q* increases with the passing pieces. This is
    the dangerous case.
  - Windows have half-width h, and the right side Φ_t(a) is integrated exactly.
  - Result: max LHS(a)/RHS = max LHS(label)/RHS = 1.000000000000. The maximum is attained only in equality cases (G constant,
    contents tiling [Eu(a), A]), and there are no violations.
- **block55_check_j2.py** (up to 2 joining rows, 2000 instances): the same result.
- **family55.py**, at the family's boundary: n_1 passing, with q*_{p_2} increasing in c; n_2 joining; the union over all
  contents of both rows; 400 instances.
  - true/(the v3 per-row target A²/E0²) ≤ 0.746;
  - true/(the #55 bound 2A(A−E0)/E0²) ≤ 0.750.

### (b) What was wrong in R6b

- The "intrinsic loss ≈ 1 + 0.56·log D" holds only at boundaries with j_t = 0, that is, where no chain row joins.
- The crossing toy in R6b (crossing_lemma_check.py, the figure 1.867) had exactly that shape: one passing row, and no joining
  row.
- At a boundary with j_t ≥ 1, the Crossing Lemma bounded the top Eu(s) of the joining rows by A_top, pointwise in s. That
  wastes their slack, because crossings at small s have small Eu(s)^j.
- #55 instead integrates over the top, through ∫_{E_1}^{E_2} K y^{j−1} G_{t−1}(y) dy. This absorbs the extra crossings of the
  passing rows.
- With singleton runs, the recursion gives G_t(E) = (A−E)^t exactly, so nothing is lost.
- In Theorem R every boundary has j_t = |P_t| ≥ 1, so there is no log D loss anywhere. The only cost is the global factor
  k^k/k! ≤ e^k from summing over run structures.
- So R6b's Monte Carlo figure, E[#crossings] ≈ 1 + 0.56·log D, is correct as stated, for one passing row. But it does not
  describe the union in Theorem R. R6b now carries a note saying this.

### (c) verify-cl's comparison of 5.26 with a true value of 6.5·10⁻⁴

pil-o3b did not rerun verify-cl's normalisation. Its family55 numbers above are the same comparison and point the same way.

## 2. The block lemma (S3)(a), A-rankfull.tex:412–439: correct

**Setting.** Fix the latest prime f of the content, and put x = 1/f, E_1 = Eu(σ), E_2 = Eu(u) = E_1/(1−x) (one prime per
slot), a = s_{t+1} and K = m + j.

**The sum over contents.**
- A prime g with slot in [a,σ) contributes (1−1/g)^{−K}, summing over all exponent vectors in the K chain rows, including the
  zero vector.
- f itself contributes (1−x)^{−K} − 1, which excludes the zero vector.
- Together with the carried factor G_{t−1}(E_2)/E_2^m, the identity E_1^K((1−x)^{−K} − 1)/E_2^m = E_1^j((1−x)^{−j} − (1−x)^m)
  is exact. pil-o3b re-derived it.

**The elementary inequalities.**
- j ≥ 1: e^{jv} − e^{−mv} ≤ (e^{jv}−1) + mv ≤ (1 + m/j)(e^{jv}−1), using jv ≤ e^{jv} − 1.
- j = 0, passing rows only: 1 − (1−x)^m ≤ mv = ∫_{E_1}^{E_2} (m/y) dy.
- G_{t−1}(E_2) ≤ G_{t−1}(y) on [E_1, E_2], because G_{t−1} is non-increasing.

**The Stieltjes comparison.**
- The intervals [Eu(σ_f), Eu(u_f)] for distinct primes f are disjoint up to their endpoints, since u_f ≤ σ_{f′} when
  σ_f < σ_{f′}.
- They lie in [Eu(a), A_top] whenever χ_t = 1, by (d) on G_{<u_f}, with u_f ≤ s_max. Terms with χ_t = 0 vanish.
- So Σ_f ≤ ∫_{Eu(a)}^{A_top} K y^{j−1} G_{t−1} dy = G_t(Eu(a)).
- In the degenerate case Eu(a) ≥ A_top, every f has E_2 > A_top, so χ_t = 0 and both sides are 0.

**Other points checked.**
- **Passing rows at j_t = 0** are handled correctly. In the Cover Bound, the condition K_t ≥ 1 at each stage holds by SC(3)
  applied to the pivot columns. So K = m ≥ 1, and the recursion is well defined.
- **Step (i) of the PIL** replaces Φ_{t−1}(s_t) by Φ_{t−1}(u_t). This is valid because Φ = G(Eu)/Eu^m, with G non-increasing
  and Eu non-decreasing, so Φ is non-increasing. As before, the only other dependence on s_t is through G_{<s} and the order
  constraint.
- **The end step (S3)(c)**, A-rankfull.tex:444–448, is correct:
  - the non-empty content gives Φ_T(X_0);
  - the empty content gives χ_T Φ_{T−1}(X_0);
  - the tails give Eu_rat^{K_T};
  - the sum is G_T(Eu_rat) + Eu_rat^{j_T} G_{T−1}(Eu_rat).

**Theorem R: the sum over run structures** (genfun55.py, exact rational polynomials, k ≤ 10).
- The sum of g_T over compositions equals H_k (eq:A-HK).
- H_k(0) = k^k/k! exactly.
- F_k(ρ) is non-increasing on a grid, and F_k(1) = 1.
- The sum of Fin over compositions equals F_k(ρ).
- The closed forms P = (1−Ez)/(1−T(ze^{−Ez})) and F_k = [z^k] 1/(1−T(ze^{−ρz})) match the recursion coefficient by coefficient,
  for K ≤ 10 and E ∈ {0, 1/3, 1/2, 9/10}.
- The derivation of the PDE ∂_E P = −z∂_z(zP/(1−Ez)), with P(1,z) = 1, from H_K′ = −K Σ_j E^{j−1} H_{K−j}, is correct.

**cor:R-Ecl**, A-rankfull.tex:785–799, is correct.
- log(15e)/3 = 1.23602 and 3·log(15e) = 11.124.
- f(465) = −59.1, and f′(L) ≤ −0.32666 + 1.2361/ℓ < 0 for ℓ > 3.79.
- The −11.94ℓ term is needed: without it, the left side at L = 465 is −10.3 against −4ℓ = −24.6.

## 3. Charging in the Cover Bound (05-queue.tex:795–808 and 887–900)

The factor is absorbed at every height L ≥ 60, including L ≥ X_0², where κ ≈ r_0.

**Pull-out at j_t = 0.**
- G_t(E) = ∫_E^A (K_t/x) G_{t−1} dx ≤ K_t λ G_{t−1}(E), using E ≥ Eu_rat. The end step gives (1+κλ)G_{T−1}.
- The recursion is a positive monotone operator, so these factors pull out. What remains is Theorem R's recursion for the
  non-zero parts, with the same K_t.
- Its Fin is at most F_κ(ρ) A^κ, since one composition is at most the sum over all of them.
- **Check** (cover55_check.py: 300 random compositions with zero parts, κ ≤ 5, quadrature on 4000 log points):
  max Fin/[(1+κλ)^{s_R} F_κ(ρ)] = 1.000000, attained only in the trivial case. No violations.

**Charging.**
- s_R ≤ |R|, because each stage with j_t = 0 adds at least one row, and all of those rows are R-rows.
- Each R-row then costs θδ·2·eD·κ·(1+κλ)·w_y ≤ 4θL^{−6}·2eL·L·L·w_y = 8eθL^{−3}w_y ≤ w_y.
- This holds at every height. It uses only δ = 4L^{−6}, D ≤ L, κ ≤ L, 1+κλ ≤ L and L ≥ 60, and never compares L with X_0.
- 1+κλ ≤ L holds for all L ≥ 60. The ratio (1+κλ)/L is at most 0.575, at L = 60, and falls to 0.34 as L grows. The stated
  reason for this bound is wrong for small L (defect C1 in §4).
- A cover row costs C′ = 2·eD·e·Ch·B² ≤ 131L^{4.04} ≤ 6L^{5.1}. Its only new factor is e, from κ^κ/κ!.

**Why the earlier limit L ≤ (Λ²/29)^{10} no longer applies.**
- It came from R6b's crude bound E2, which charged a crossing loss of about L/3 to every cover row at every boundary, against
  only about L^{0.9} of slack per cover row.
- Under #55 there is no loss per boundary at stages where a cover row joins. The integrated tops of the joining rows absorb it.
  In total the cost is κ^κ/κ! ≤ e^κ, about a factor e per cover row, which fits inside C′.
- The remaining loss appears only at stages with j_t = 0, which are exactly the stages where only R-rows join. Each R-row
  carries a δ = 4L^{−6} that is otherwise unused, and needs only about L³.
- **So no height limit remains, in the Cover Bound or in Theorem R.**

## 4. Leftover counts: none missing

### Theorem R

- Configurations map to pairs (ordering, skeleton). The skeleton is E_P in decision order, together with the run structure.
- **Free primes** are counted inside the content sums: any number per block, any slots, and every exponent vector over the
  K_t chain rows.
  - Entries in later rows are determined by the span (SVL(ii)).
  - A free prime of F_t can never be absent from R_{≤t} (SC(3), with C = B′).
- **Tails** are counted by (S3)(c).
- **Run structures** are counted by F_k.
- **Patterns** are counted by Lemma pattern.
- **Pivot labels** are counted by θ^k.
- The weight of a pattern depends only on E_P, and Fin only on the run structure, so the sum factorises.
- **Harmless over-counts:**
  - contents that are inconsistent with the span or with distinctness;
  - contents of the slots of the other pivots of P_{t+1};
  - run structures that are impossible for a given E_P.

### The Cover Bound

- (s1) r and the cover rows: 2^r.
- (s2) the pivot labels, that is, their ranks in P(C). These fix the run structure and the number of free primes in each
  block. Counted by C(κD, r) ≤ (eD)^r.
- (s3) the exponents of the pivots in cover rows: τ-weights. Pivots matched to R-rows contribute κ·(1−1/τ)^{−κ−1}.
- (s4) the R-row monomials and tails: w_y.
- The cover-row exponents of the free primes, and the cover-row tails, are inside Fin.
- The row–pivot matching is chosen canonically for each configuration, so it costs nothing.
- The number of free primes per block is fixed through (s2) while (S3)(a) also sums over all contents, so that number is
  counted twice. This is harmless, and fits inside the budgeted (eD)^r.
- Every free prime has an occurrence in a cover row, so no free structure escapes Fin.

## 5. Defects (all COSMETIC)

- **C1. 05-queue.tex:888** says "κ ≤ r_0 ≤ L/(2ℓ)". The middle inequality is false for L ∈ [60, about 101.6); for example, at
  L = 62, r_0 = 9 > 7.51.
  - The conclusion 1+κλ ≤ L still holds for every L ≥ 60, because κ < r_0 (the ratio is at most 0.575).
  - Thm caplw uses Lemma reduction only at L ≥ Λ, where r_0 ≤ L/(2ℓ) is true (05-queue.tex:1066).
  - **Status: fixed.** verify-cl applied this while fixing R9's item 3; the text is now κ ≤ r−1 ≤ r_0−2 ≤ L/(3ℓ)+2.
- **C2. A-rankfull.tex:193–194** says the PIL "also holds … when further data that are not block data are fixed in advance
  (as in Proposition cover)". But Proposition cover's (s2) fixes the number of free primes per block, and its (s4) fixes the
  R-row entries of block columns, and both are block data. The proof of Prop cover already handles this correctly
  (05-queue.tex:789: "bounded by the sums over all contents").
  - **Status: fixed**, as R9's item 1.
- **C3. 05-queue.tex:807–808**, the parenthetical "(A stage with K_t=0 gives G_t ≡ 0; its block would have no row of C to
  cover it …)". Read literally, it says that a nonempty sum is bounded by 0. The correct statement is that K_t ≥ 1 for every
  t ≥ 1, by SC(3) applied to the pivot columns of P_1, so such stages do not occur.
  - **Status: fixed by the lead.** The text now reads "Every stage has K_t ≥ 1, by Lemma SC(3) applied to the pivot columns
    of P_1; so no stage has K_t = 0."

## 6. Toys

The scripts were run with `python3 -I -B`; copies are in review/recheck/pil-o3b-55/.

| Script | What it checks | Result |
|---|---|---|
| block55_check.py | Explicit enumeration of contents (subsets × support patterns, with exact exponent sums), adversarial increasing q*, label windows, and the exact right side for j ∈ {0,1}, m ≤ 2 | 2000 instances. Max ratio 1.000000000000, no violations, equality cases only. An earlier reading of 1.00007 was an artefact of midpoint quadrature, and disappeared once the integral was made exact. |
| block55_check_j2.py | The same, with j ≤ 2 | 2000 instances, max 1.0 |
| family55.py | The boundary of pil-o3b's family | true/v3-target ≤ 0.746; true/#55 ≤ 0.750 |
| genfun55.py | Exact checks, for k ≤ 10, of eq:A-HK, H_k(0) = k^k/k!, the monotonicity of F_k, F_k(1) = 1, and both closed forms | all OK |
| cover55_check.py | The j_t = 0 pull-out, against (1+κλ)^{s_R} F_κ | 300 instances, max 1.0 |

## 7. Confidence, and where a later checker should look

- **High:** the block lemma (its algebra, and the exhaustive toys); the generating function; and the charging.
- **The PIL invariant under step (i).** A later checker should look hardest here. Apart from G_{<s} and the order constraint,
  Φ_{t−1}(s_t) must be the only factor that depends on the label. In particular, the caps ∏1(q_j ≥ τ_j) and Proj must be
  label-free. pil-o3b believes they are, and R9 §1 confirms it.
- **The claim that every j_t ≥ 1 in Theorem R.** It holds because every run adds |P_t| ≥ 1 stage rows, and when C = B′ all of
  these are chain rows.
