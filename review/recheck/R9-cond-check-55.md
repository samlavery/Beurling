# R9: cond-check's adversarial check of correction #55, the repair of the #48 union gap

The checker was cond-check, the agent that found the union gap (R6). It worked on a read-only copy of the live tree, diffed
against 26b0656, and wrote its checks independently of the author's scripts (it only skimmed those). It was not allowed to
write files, so the lead saved its messages here. A private build gave latexmk exit 0, no LaTeX warnings, and the baseline 18
overfull boxes.

## Verdict: CORRECT WITH FIXES

There are no BLOCKING and no FIXABLE defects; all the fixes are cosmetic.

## 1. Lemma pil for skeletons (A-rankfull:81–86, 188–322): correct

- **Caps (closes D2).** The caps ∏1(q_j ≥ τ_j) are in the initial Ψ (l.209). They are label-free, hold for every realised
  configuration, and survive step (i). So SVL(ii)'s τ-replacement (l.626–628) and (B1) are now valid pointwise.
- **Continuous slots (closes D4).** The label sums run over continuous slots (l.263, 282).
- **Tails (closes D5).** The tails are out of the type (l.50–51).
- **Block step (iii).** It now sums over every non-empty content (l.218–221). The invariant still holds:
  - the output Φ_t(s_{t+1}) depends only on Eu_s(s_{t+1}) and the deterministic A_top;
  - it is non-increasing, and measurable at every pivot of P_{t+1};
  - step (i) turns it into Φ_t(u_{t+1}).
- **Steps 1–3 of R6** (filtration, label replacement, Tonelli) carry over unchanged.

## 2. (S3)(a) with variable content (l.369–375, proof l.412–439): correct

The checker re-derived the proof line by line.
- **Exponent sums.** The sum over exponent vectors in the K chain rows is (1−1/g)^{−K}. For the latest prime f it is
  (1−x)^{−K} − 1.
- **Identity.** With E2 = E1/(1−x) and K = m + j, E1^K((1−x)^{−K} − 1)/E2^m = E1^j((1−x)^{−j} − (1−x)^m). This is correct.
- **Inequalities.**
  - For j ≥ 1: (e^{jv} − 1) + (1 − e^{−mv}) ≤ (K/j)(e^{jv} − 1).
  - For j = 0: 1 − e^{−mv} ≤ mv = ∫_{E1}^{E2}K/y dy.
- **Per-prime bound.** Since G_{t−1} is non-increasing, each f contributes at most Eu_a^{−K}∫_{E1}^{E2}Ky^{j−1}G_{t−1}.
- **Intervals.** The intervals [Eu(σ_f), Eu(u_f)] are disjoint, and they lie inside [Eu_a, A_top] whenever χ = 1, by (d).
  - In the edge case Eu_a ≥ A_top, both sides are 0.
  - The proof does not need χ = 1 to hold on an initial segment of the primes.
- **(c)** is correct, including the empty early block: u_T = X₀, χ_T = 1, and the tails give Eu_rat^{K_T}.
- **Discrete ≤ continuous** is now part of the proof itself, so no separate comparison lemma is needed.
- **Check `s3a_brute.py`.** This enumerates contents explicitly:
  - subsets, with exponent vectors up to 7 per row;
  - tiny primes from 2 upwards;
  - j_t = 0 allowed, and χ cut-offs;
  - G_{t−1} built by the recursion through random earlier compositions with zero parts.

  Result: 1500 cases, 0 violations, maximum LHS/RHS = 1.0000 (equality when m = 0, as expected).

## 3. Theorem R and the generating function (l.679–757): correct

- **Reduction to skeletons.** Every ordered configuration has exactly one skeleton, and the pattern sum (1/k!)Σ_{E_P} is
  unchanged.
- **K_t and j_t.** With C = B′, K_t = |P_{≤t}| and j_t = |P_t| for every E_P (Lemma SC(2)). So the run-structure sum is the
  same function F_k(ρ) for every pattern, and it factorises out.
- **F_k is non-increasing.** Re-derived: F_k′ = Σ_j(j−k)ρ^{j−1}H_{k−j} + Σ_jρ^jH′_{k−j} ≤ 0, using H_K ≥ 0 and H_K′ ≤ 0 by
  induction.
- **The PDE.** The coefficient comparison is correct: Σ_K Kz^K Σ_j E^{j−1}H_{K−j} = z∂_z(zP/(1−Ez)). With P(1,z) = 1, the
  series is determined coefficient by coefficient. The characteristics step checks by hand:
  - log ζ − ζ = log z − Ez;
  - ∂_Eζ = −zζ/(1−ζ), and ∂_zζ = ζ(1−Ez)/(z(1−ζ));
  - both sides equal −z/(1−ζ) − zζ(1−Ez)/(1−ζ)³;
  - T(ze^{−z}) = z gives P(1,z) = 1;
  - P(0,z) = 1/(1−T(z)) = Σ K^K z^K/K!, from zT′ = T/(1−T).
- **Check `genfun_check.py`**, in exact rational series:
  - [z^K](1−Ez)/(1−T(ze^{−Ez})) = H_K(E) as polynomials, for K ≤ 11;
  - F_k(ρ) = [z^k]1/(1−T(ze^{−ρz})) for k ≤ 11 and ρ ∈ {0, ⅓, ½, 1};
  - H_k(0) = k^k/k!, and F_k(1) = 1.

  This is consistent with R6's Stirling closed form for H_K.
- **The old toys against the new bound:**
  - pattern_sum's discrete ratios are 1.66, 3.20, 6.54 and 13.78 for k = 2, 3, 4, 5, all ≤ k^k/k!;
  - toy_family: the new bound 5.257 ≥ the #48 per-pattern value 3.464 ≥ the true E (≤ 6.5·10⁻⁴);
  - toy_pattern: the new bound 4.936 ≥ 3.860.

## 4. cor:R-Ecl and Prop ecl (A-rankfull:768–803; 05-queue:559–563): correct

- 1.8·4·2^{1.02}·1.01·e·(469/465) = 40.43 ≤ 15e = 40.77.
- log(15e)/3 = 1.23602 ≤ 1.2361, and 3·log(15e) = 11.124 ≤ 11.13.
- The displayed chain gives −83.7 at L = 465, against the required −24.6. With the exact r₀ it gives −99.5.
- The bound is monotone: f(465) = −59.1 ≤ −59, and f′(L) < 0 for ℓ > 3.78. The chain holds at every point checked:
  L = 470, 500, 600, 10³, …, 10²⁰.
- Prop ecl's factor e is applied consistently.

## 5. R3: Cover Bound skeletons (05-queue:733–757, Prop cover, Lemma reduction(ii)): correct

### (s1)–(s4) determine everything the PIL needs

- E_P comes from (s3) for the C rows, and from the pivot labels inside the R-row monomials M_y (s4).
- The run structure comes from the adjacency of the pivot labels (s2).
- The stage rows (Lemma SC), and hence K_t, j_t and s_R, follow from E_P and C.
- (s2) fixes the number of free primes in each block. The PIL sums over all contents, so summing over (s2) over-counts.
  That over-count costs C(π, r) ≤ (eπ/r)^r ≤ (eD)^r, using κ ≤ r, which is affordable.

### Nothing is left uncounted

| Piece of a configuration | Where it is counted |
|---|---|
| r, and which rows are C rows | (s1), 2^r |
| the decision order of the pivots | (s2) |
| the C-row exponents of the pivots | (s3), as a weighted sum |
| the R-row monomials and tails | (s4), via w_y |
| the C-row free primes, with their exponents and blocks | the PIL union, (S3)(a) |
| the C-row tails | (S3)(c) |
| the order of the free primes inside a block | the slots inside a content |
| the pivot values | integrated |
| the row order | canonical, through the matching |

### Fixing the R-row data by label inside the PIL union is valid

- Labels are global decision ranks. Once (s2) is fixed, the labels inside F_t are a fixed offset plus the position in the
  block, so they do not depend on unprocessed data.
- (s4)'s R-row entries in free columns, and (s2)'s block sizes, only restrict the contents. Their indicators are ≤ 1, and
  they are dropped when (S3)(a) sums over all contents. Prop cover's proof says exactly this (05-queue:775–777).
- R rows carry no block weight:
  - R rows in R_{≤t} are integration variables (weight 1/n_y), by SVL(ii);
  - for R rows outside R_{≤t}, the constraints do not involve the free primes once the pivots are substituted.
- Skeletons with M_y(τ)·d_y > 2z have X_s = 0, because the label of rank j has value ≥ τ_j. This is what turns (s4)'s sum
  into w_y.

### The Leibniz matching count needs nothing extra

- A nonzero Leibniz term exists because E_P is invertible. The matching is used only to index the rows and to decide which
  case of (s3) applies.
- If the matching is not chosen by a fixed rule, a configuration can receive several skeletons. That only over-counts, and
  every such skeleton is already counted in (ii).
- (s3) is right in both cases:
  - matched to a C row: Σ τ^{−(|v|−1)} over the vectors with the matched coordinate ≥ 1 equals (1−1/τ)^{−κ};
  - matched to an R row: τ((1−1/τ)^{−κ} − 1) ≤ κ(1−1/τ)^{−κ−1}.

  So (s3) is at most κ^{|R|}B^{κ+1} ≤ κ^{|R|}B^{2κ}.

### Pulling out the j_t = 0 stages is valid

- At such a stage, G_t(E) = ∫_E^A (K/x)G_{t−1} ≤ K_tλ·G_{t−1}(E) for E ≥ Eu_rat.
- If the last stage has j_T = 0, the end step gives Fin ≤ (1+κλ)·G_{T−1}.
- The operators are positive, so these factors can be pulled out. What remains is Theorem R's recursion, for the
  composition of κ formed by the nonzero parts, with the same K_t. Its Fin is ≤ F_κ(ρ)A^κ ≤ (κ^κ/κ!)A^κ.
- s_R ≤ |R|, because a run with no C row consists entirely of R stage rows.
- By Lemma SC(3), a run with no row of C cannot come first.

### An R row's δ absorbs (1+κλ) at every L

- (1+κλ) is already inside the bound 8eθL⁻³ in ℓ (05-queue:888–893): θδ·2·eD·κ·(1+κλ), with D ≤ L, κ ≤ L, 1+κλ ≤ L and
  δ = 4L⁻⁶.
- 1+κλ ≤ L holds because λ ≤ log(2L) (as Eu_rat ≥ 1 and A_top ≤ 2L) and κ ≤ r₀ − 1:
  - L = 60: 34.5 ≤ 60;
  - L = 100: 54 ≤ 100;
  - L = 10⁸: 3.5·10⁷ ≤ 10⁸.
- The full R-row factor is ≤ 6.8·10⁻⁶ at L = 60, so it is ≤ w_y.
- The worry that κλ ≈ r₀·log L breaks this does not apply, because κλ ≤ L/2 + O(L/ℓ).
- C-row cost: 2·eD·e·Ch·B² ≤ 2e²·2·4.41·L^{4.04} = 130.3·L^{4.04} ≤ 6L^{5.1} for L ≥ 18.4.
- (2z/δ)(θδC′)^κ ≤ 13L^{5.1}z, using κ ≥ 1. So (iii), the criterion and caplw are unchanged.

### The D3 concern is resolved, differently from R6's suggestion but correctly

- The free-prime excess in the C rows of R_{≤t} is summed exactly inside (S3)(a), through g^{−a_g} and (1−1/g)^{−K}.
- In C rows that join later, these entries are determined by the entries of R_{≤t} (SVL(ii)), so no sum is needed. Their
  weight through (B1) is (X₀⁻)^{−e} ≤ 1.
- Only the pivot excess remains, with τ_i by pivot rank. This is consistent with eq:A-tau and with B = ∏_{i≤r}(1−1/τ_i)^{−1}.
- The old π-label excess sum, where #44 applied, is gone.

## 6. Defects (all COSMETIC)

1. **A-rankfull:193–194.** The PIL allows fixing "further data that are not block data … (as in Proposition cover)". But
   Prop cover's (s2) (block sizes) and (s4) (R-row entries in free columns) are block data. The proof still works, because
   the restrictions are indicators that are dropped in (iii), and Prop cover's proof says so.
   **Fix:** "further data may be fixed in advance; where they restrict the block contents, (iii) may still sum over all
   contents."
2. **A-rankfull:536–537.** "The entries of the free columns in the rows outside C are part of the type τ" should read "are
   fixed in advance (skeleton (s4))". The same applies to "fixed by the type" in SVL(v), at A-rankfull:586 and 658–659.
3. **05-queue:888.** "κ ≤ r₀ ≤ L/(2ℓ)" is false for L between 60 and about 100: at L = 60, r₀ = 8 > 7.33. κ ≤ r₀ − 1 ≤ L/(2ℓ)
   is true, and in context L ≥ Λ anyway.
   **Fix:** write κ ≤ r₀ − 1. The same pre-existing claim is at 05-queue:1066, where L ≥ Λ makes it true.
4. **05-queue:737.** "Fix such a matching": say that it is chosen by a fixed rule, for example the lexicographically first
   nonzero Leibniz term. This is optional, since non-canonical choices only over-count.
5. **LABELS.md:174–175.** The old rows for eq:A-exactcount and eq:A-telescope are still there, next to the WITHDRAWN rows
   (180–181). Delete the old ones.
6. **Status text.** 00-intro.tex:51–53 and C-ai-statement.tex:19 and 25 still call #48 a known open gap. Update them if #55
   is accepted.

## 7. New toys

- **`s3a_brute.py`** (§2): 1500 cases, 0 violations.
- **`genfun_check.py`** (§3): every identity is exact.
- **`cover_disc.py`**: exact discrete content sums of the scheme, with all contents and exact carried functions.
  - Covers every C/R sequence of length ≤ 6 and every run structure, on 60 random prime sets that include 2 and 3.
  - Compared with (1+κλ)^{s_R}(κ^κ/κ!)A^κ, where λ = log(A/Eu_rat).
  - Result: 81,900 cases, 0 violations, maximum ratio 1.0000, with equality only in the trivial case κ = 1, s_R = 0.
- **cover_model, continuous, against the same bound**: 5460 cases, maximum ratio 1.0000.
- **`toy_cover_r3.py`**: the exact E for each Cover-Bound skeleton, in the jittered toy world.
  - Set-up: r = 2. A C row q_a·q_b·(free primes)·d_C, and an R row q_b²·(early free primes of the C row, by label)·d_R.
    Tails use the rational primes {2}. Every slot is decided and G = 1, which is the worst case over adaptive rules.
  - Both run structures are covered, including the uncompensated case where the R row joins alone at the end (s_R = 1).
  - Windows z = 60 to 800 give between 4 and 38 skeletons with E > 0 each, with 0 violations and maximum
    E/[(θδ)²Σ̄_s] = 0.093.
  - The bound is loose, so this checks the bookkeeping, not the sharpness.

## 8. Confidence and limitations

- **High** on R1 and R2. The proofs were re-derived by hand, the identities are exact, and the brute force found no
  violations.
- **High** on the bookkeeping of R3. Every piece of a configuration was traced to a count or a sum, the constants were
  checked numerically, and the exact toys found no violation.
- **Not checked:** the SVL linear algebra beyond what (ii) needs; Lemma SC; caplw's arithmetic, which #55 does not change;
  and the author's remaining scripts (adversarial.py, family_*.py).
- **Limitation:** the R3 toys cover configurations with r ≤ 2 exactly. Larger r is covered only by the checks at the level of
  the recursion (cover_disc and cover_model), not by an exact end-to-end expectation.
