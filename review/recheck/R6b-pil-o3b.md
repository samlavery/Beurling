# R6b: an independent attempt at #48, which finds the repair valid only per type

This report is by pil-o3b, a separate AI agent that attempted #48 independently of the author of the repair (verify-cl). It
read verify-cl's scratch notes, but its arguments and scripts are its own. It was not allowed to write files, so the lead
saved its messages here.

**Summary.**
- **Per type: correct.** The repair now in the paper (correction 48) is correct for one fixed full type.
- **As used: not covered.** Theorem R and the Cover Bound sum over every free structure, and the repair does not cover that
  sum. In that sum the loss is real. It appears in exact toys, in Monte Carlo, and in an exact random-set identity.
- **What it proves instead.** The step at each boundary costs θ₊(1 + m⁻_t·λ_t) (the Crossing Lemma), and the number of
  boundaries with a loss is at most the pattern excess (the Charging Lemma). Together these close the CL chain only up to a
  finite height:
  - log L ≤ 51Λ for cor:R-Ecl;
  - L ≤ (Λ²/(29θ))^{10} for the Cover Bound.

  Above those heights #48 is open.
- **Status of these findings.** They had not yet been checked independently when this report was saved. The lead also
  confirmed the identity "union over free structures = λ/Eu_s(a)" in an exact rational toy: review/recheck/pil-o3b/union_check_lead.py,
  which reproduces Σ1/g to 10⁻⁹.

## 1. What must be proved

At the last pivot p_t of run P_t, with label s and value q, the step below needs Ψ_s(q) to be free of s, pointwise in q:

  Σ_s H(s)⁻¹ ∫_{W_s} Ψ_s dq ≤ θ ∫ Ψ dq.

With carried factors 1/Eu_s(s) for passing rows, the block below p_t telescopes only after q has been integrated, because the
1/c weights come from the Jacobian.

The bound has to hold for the sum that Theorem R and the Cover Bound actually use:
- Theorem R reduces to pivot patterns E_P and sums the cofactors c_i freely (A-rankfull, proof of Thm R);
- Lemma reduction(ii) puts the kept free primes of each cover row inside Ch (05-queue).

So each row's chain has to absorb every free structure: any number of free primes, in any gap.

## 2. The live repair is right per type, but not as consumed

**Correct per full type.** The live (S3)(a) uses the exact count (eq:A-exactcount) for y₁, the row that owns the latest
block prime f_t, plus telescoping for joining rows.
- It needs y₁ and its column count r to be "fixed by the type, since the assignment is".
- With those fixed, the proof is correct. An exact-rational brute force (block_lemma.py, 3000 instances) gives
  max LHS/RHS = 0.62. An adversarial label-sum variant gives 0.40.

**Not valid for the union over free structures.** There, r is not fixed.
- Summing the exact count over r gives Σ_r P(|R ∩ [a,s_max]| ≥ r) = E|R| = Σ 1/g. That is the crude "1 + Σ1/p" loss again,
  now over the whole range [s_{t+1}, s_max].
- Applying the repair per full type does not help either: non-owner rows still get the full Euler ratio in every type, so
  summing over types overcounts.

**The loss is intrinsic.** It comes from the per-row harmonic accounting, not from this particular repair.
- **Random-set identity.** Let R be a random multiplicative set with independent geometric exponents. Then
  Σ_c c⁻¹·1(c ∈ ⟨[a,s)⟩)·Eu(a)/Eu(s)·F = E_R[F(R_{[a,s)})]. So Eu(a) × (label-summed block sum) ≈ E_R[#{s : s ≈ q*(R_{[a,s)})}],
  the expected number of self-consistent split points ("crossings").
- **Dangerous family.** Rows n₁ = p₁·g·c·d₁, n₂ = p₁·p₂·g·d₂, n₃ = p₃·d₃, with decision order p₁ > g > p₂ > c > p₃. The prefix
  inverse is [[1,0],[−1,1]], and q*_{p₂} = (n₂/n₁)·c·d₁/d₂, which increases with the passing row's piece c.
- **Monte Carlo** (crossings.py). E[#crossings] ≈ 1 + 0.56·log D, for example 8.4 at D = 10⁶. It stays bounded (about 1.12)
  only when q* depends weakly on the piece.
- **Exact toys** (crossing_lemma_check.py, 4000 cases). The v3 claim (≤ 1 after cancellation) fails by up to 1.867 when q*
  increases with the piece. It holds when q* is non-increasing.
- These are failures of the PIL step as written, not of Theorem R itself.
- The family A·f·q_i·d_i from the earlier check is harmless. There, the passing row's late piece is the rational tail d₁,
  which lies below every cut.

## 3. What can be proved instead

## Part 1/4: the Crossing Lemma, setting and statement

### Setting (union reading)
- A pivot pattern E_P (k×k) is fixed. The pivots are p_1 > … > p_k in decision order, latest first.
- Every gap is a block, possibly empty:
  - for t < k, F_t is the set of free primes decided between p_{t+1} and p_t;
  - F_k is the early block;
  - the tails come with F_k.
- So the runs are single pivots. A free column decided between p_{t+1} and p_t still satisfies e_f ∈ span{e_p : p ∈ P_{≤t}},
  so eq:A-span, Lemma SC and SVL apply unchanged.
- The stage rows R_{≤t} are the lexicographically first bases (Lemma SC), so C_t = {y_t} is a single new row.
- The chain rows are all rows in Thm R (C = B′), and the cover rows in the Cover Bound.
- Y_t := the chain rows in R_{≤t}. A chain row is "passing" at t if its chain started at an earlier stage; it then carries
  1/Eu_s(s_t) from the previous block bound, exactly as in v3 (S3)(a)/(b). Otherwise it is "joining".
- a := s_{t+1}, the label of the next pivot. For t = k, a := X₀, the first slot, so Eu_s(X₀) = Eu_rat.
- s* := max{s ≤ s_max : G_{<s} holds}, where s_max = 2z + 0.51H(2z).
- w_{y,t} := (E_{R≤t,P≤t}^{−1})_{p_t, y} for y ∈ R_{≤t}. This is the row p_t of the prefix inverse.
- Y⁻_t := {y ∈ Y_t : w_{y,t} < 0}, and m⁻_t := |Y⁻_t|. Trivially m⁻_t ≤ t.
- λ_t := Σ 1/g over the realised primes g with slot in [a, s*).
- θ₊ := θ(1 + o(1/Λ)), the same factor as the PIL's (F1) step, with H varying over about 2H.

### Crossing Lemma
Process boundary t in the v3 order:
1. the conditional density at the label s = s_t;
2. then the block F_t, summed pointwise in ω;
3. then the label sum.

Then

  Σ_s H(s)^{−1} ∫_{W_s} [ Σ_{F_t} Ψ_s ] dq_{p_t} ≤ θ₊ · (1 + m⁻_t λ_t) · Π_{y∈Y_t} Eu_s(a)^{−1} · Π_{y∈Y_t joining} A_top · Ψ_rest.

Here:
- the s-sum runs over the admissible labels: s later than every slot of F_t, s ≤ s*, and G_{<s} holds;
- Ψ_rest is the part of the stage-≤t Jacobian integrand that does not involve F_t, q_{p_t} or s;
- the window indicators, and the cofactor parts of F_{>t}, P_{>t} and the tails, stay in Ψ_rest;
- the factors q_j^{1−s_j^cov} have already been replaced by τ_j^{1−s_j^cov} on Proj, as in SVL(ii).

The output Π Eu_s(a)^{−1} = Π Eu_s(s_{t+1})^{−1} is the v3 carried factor. It is non-increasing in s_{t+1}, and it is a
function of the primes decided before s_{t+1}. So the next boundary sees exactly the v3 structure. Each row gets A_top once,
at its joining stage.

### Consequences
- If m⁻_t = 0, the boundary costs θ₊ and nothing more, which is the v3 constant. This covers:
  - the case where q*_{p_t} does not depend on the block;
  - verify-cl's one-crossing case, where every w_{y,t} ≥ 0;
  - every t with E_{y_t,P<t} = 0 (see the Charging Lemma).
- On G_{<s*}, λ_t ≤ log D + 3/Λ, with D := log 2z / log X₀⁻.

### Derivation of the bound on λ_t
- Primes with slot in [a, s*) have values in [X₀⁻, s* + H/2].
- Lemma cm(iv), with y = X₀⁻ − 1 and x = s* − H(s*), gives at most log(log s_max/(Λ − e^{−0.98Λ})) + 2.20/Λ.
- The at most 2H + 1 primes in (s* − H, s* + H/2] add at most (2H + 1)·2/s* ≤ 5H(X₀)/X₀.
- Finally, log s_max ≤ log 2z + e^{−10⁶}.
## Part 2/4: proof of the Crossing Lemma

**P0 (conditional density).** Condition on F_{s−} at the slot s of p_t. By (F2),

  E[Ψ 1(G_{<s}) | F_{s−}] ≤ 1(G_{<s}) H(s)^{−1} ∫_{W_s} Ψ dq.

The block data F_t are F_{s−}-measurable, so their sum stays inside. Take E and sum over s. Every step below is a pathwise
inequality inside E[·] on nonnegative terms, so Tonelli allows all the exchanges, and nothing data-dependent needs to be
measurable.

**P1 (per-row pieces).**
- After the integrals over P_{≤t}, write ∫dq ∫(inner) = ∫_{J^{R≤t}} dn J(n, F_t, rest), using the SVL change of variables.
- By SVL(ii), J ≤ Π_{y∈Y_t} c_y^{−1} · Φ(n, rest), where:
  - c_y is the F_t-piece of row y, that is, the product of the F_t primes in y with their exponents;
  - Φ does not involve F_t.
- Every F_t prime has total chain-row exponent ≥ 1 (SC(3)).
- The map from the F_t data to (c_y)_{y∈Y_t} is injective (SVL(ii)).
- Drop all consistency constraints. This gives an upper bound, and the c_y become independent over ⟨[a,s)⟩, the products of
  realised primes with slots in [a,s), with any exponents.
- The window indicator keeps the true q_{p_t} = q*(n, c, rest).
- Everything below is done pointwise in n, and no localisation of q is needed. Over n ∈ J^{R≤t}, the relative spread of q*
  is ‖E^{−1}‖·δ/z, which can be much larger than H in absolute terms. So a sup over n would not work.

**P2 (FAC shift).** Let g ∈ F_t. Then P_late(g) ⊇ P_{≤t}, and v_g = E_{R≤t,P≤t}^{−1} e_{g,R≤t}. The window constraints are
invariant under x_g → x_g + σ, x_{P≤t} → x_{P≤t} − σ v_g. Hence

  log q*_{p_t} = log Q(n, rest) − Σ_g v_{g,p_t} log g = log Q − Σ_{y∈R≤t} w_{y,t} log c_y,

with Q free of F_t.
- In Thm R, every row of R_{≤t} is a chain row.
- In the Cover Bound, the non-chain rows of R_{≤t} have F_t-entries fixed by the type. Use the conservative count m⁻_t ≤ t,
  which is all that bound E2 below needs.

**P3 (random-set device).** For y ∈ Y_t, let R_y be independent random multiplicative sets: each realised prime g with
slot ≥ a enters with exponent e ≥ 1 with probability (1 − 1/g)g^{−e}. Let R_{y,[a,s)} be its part with slots in [a,s). Then

  P(R_{y,[a,s)} = c) = c^{−1} Π_{slot∈[a,s)} (1 − 1/g) = c^{−1} Eu_s(a)/Eu_s(s).

- A passing row has the factor 1/Eu_s(s) = Eu_s(a)^{−1} · Eu_s(a)/Eu_s(s).
- For a joining row, insert 1 = (Eu_s(s)/Eu_s(a))·(Eu_s(a)/Eu_s(s)), and bound Eu_s(s) ≤ A_top on G_{<s} by (S3)(d) at
  s ≤ s_max. This is done inside the label sum, pointwise in s.

Hence the left side is at most

  Π_{Y_t} Eu_s(a)^{−1} Π_{join} A_top · ∫dn Φ · E_R[ Σ_{s≤s*} H(s)^{−1} 1( q*(n, R_{[a,s)}) ∈ W_s ) ].

**P4 (crossing count, for each fixed R and n).** Put φ(s) := s − q*(n, R_{[a,s)}).
- When s passes the slot of an R_y-prime g with exponent e, q* is multiplied by g^{−e·w_{y,t}}:
  - φ jumps up if w_{y,t} > 0;
  - φ jumps down if w_{y,t} < 0;
  - φ is unchanged if w_{y,t} = 0.
- Otherwise φ increases with s. So for slots s < s′ in a stretch with no down-jump, φ(s′) − φ(s) ≥ s′ − s.
- An admissible slot has q* ∈ W_s, that is, |φ(s)| ≤ H(s)/2. So two admissible slots of the same stretch satisfy
  s′ − s ≤ (H(s) + H(s′))/2.
- So the admissible slots of a stretch lie in one interval of length ≤ H·(1 + o(1/Λ)).
- By the slot density (F1), together with H(s) ≥ H(s₀) and the variation of H over about 2H, their weight Σ H(s)^{−1} is at
  most θ₊.
- The number of stretches is ≤ 1 + N⁻(R), where N⁻(R) := #{(y, g) : y ∈ Y⁻_t, g an R_y-prime with slot in [a, s*)}.

**P5 (expectation).** P(g ∈ R_y) = Σ_{e≥1} (1 − 1/g) g^{−e} = 1/g, so E N⁻ = m⁻_t λ_t. Hence E_R[·] ≤ θ₊(1 + m⁻_t λ_t),
uniformly in n. Integrate over n against Φ. ∎

**End step (t = k).** Put a = X₀. Hold the tails d_y fixed while P1–P5 act on the early-block pieces, then sum the tails:
Σ_d 1/d = Eu_rat, which cancels Eu_s(X₀)^{−1}.
- Tails lie below every cut, so they create no jumps.
- q* may depend on them, as in the family A·f·q_i·d_i. That is harmless, because P4 holds for each fixed tail tuple.

**Why this is sharp in the union reading.** P3 and P4 are exact up to θ₊: Eu_s(a) × (left side) ≈ θ·E_R[#crossings].
- Family n₁ = p₁·g·c·d₁, n₂ = p₁·p₂·g·d₂, n₃ = p₃·d₃, with decision order p₁ > g > p₂ > c > p₃.
- The prefix inverse is [[1,0],[−1,1]], so w_{n₁,2} = −1 and q*_{p₂} = (n₂/n₁)·c·d₁/d₂.
- Monte Carlo (crossings.py, 20000 trials per point) gives E[#crossings] ≈ 1 + 0.56·log D: for example 3.26 at D = 100 and
  8.44 at D = 10⁶.
- Exact rational toys with pieces of any size (crossing_lemma_check.py, 4000 instances):
  - the crossing bound holds, and is attained (max ratio 1.0);
  - v3's "≤ 1 after cancellation" fails by up to 1.867 when q* increases with the piece;
  - it holds when q* is non-increasing.
## Part 3/4: the Charging Lemma and the two height limits

### Charging Lemma
Use single-pivot runs and lexicographically first stage bases, so C_t = {y_t}. If m⁻_t > 0, then E_{y_t, j} ≥ 1 for some
j ∈ P_{<t}. Fix one such j_t. The map t ↦ (y_t, j_t) is injective, and for every column j, #{t : j_t = j} ≤ s_j − 1. Hence

  #{t : m⁻_t > 0} ≤ M := Σ_j (s_j − 1),

the pattern excess.

**Proof.**
- Write E_{≤t} = [[A, b], [c^T, d]] with:
  - A = E_{R<t,P<t}, invertible by SC(2);
  - b = E_{R<t,p_t};
  - c^T = E_{y_t,P<t};
  - d = E_{y_t,p_t}.
- The Schur complement σ := d − c^T A^{−1} b is nonzero.
- Row p_t of E_{≤t}^{−1} is σ^{−1}(−c^T A^{−1}, 1).
- If c = 0, then σ = d is a nonzero nonnegative integer. So the row is (0, …, 0, 1/d) ≥ 0, and m⁻_t = 0. Hence m⁻_t > 0 forces
  c ≠ 0.
- **Injectivity.** Each row joins only once (SC(1)), so distinct t have distinct new rows y_t.
- **Per-column bound.**
  - Let j ∈ P_{t_j}. Column j of the invertible E_{≤t_j} is nonzero, so some x ∈ R_{≤t_j} has E_{x,j} ≥ 1.
  - Every t with j_t = j has t > t_j, so y_t ∉ R_{≤t_j}; in particular y_t ≠ x.
  - The charged units therefore lie in distinct rows other than x, so their number is at most s_j − E_{x,j} ≤ s_j − 1. ∎

**The stronger statement Σ_t m⁻_t ≤ M is false.** Take the lower-bidiagonal pattern n₁ = q₁, n_{i+1} = q_i·q_{i+1}. Row t of
the prefix inverse alternates in sign, so m⁻_t ≈ (t − 1)/2 and Σ ≈ k²/4, while M = k − 1. (negscan.py did not find this
example; it was found by hand.)

### Bound E1 (charging; Theorem R)
- Put B := 1 + kλ, where λ := max_t λ_t ≤ log D + 3/Λ ≤ ℓ.
- Then Π_t (1 + m⁻_t λ_t) ≤ B^{#{t : m⁻_t>0}} ≤ B^M = Π_j B^{s_j−1}.
- So Thm R's ∏_j τ_j^{−(s_j−1)} becomes ∏_j (B/τ_j)^{s_j−1}. The proof of Lemma pattern then gives
  (1/k!) Σ ≤ ∏_j (1 − B/τ_j)^{−k}, valid for B < τ_j.
- The log of this is ≤ k Σ_j B/(τ_j − B) ≤ kB(1 + 2B/X₀)·[(3H(X₀)+2)/X₀ + 1.02 log(1 + k/X₀)].
- Relative to the paper, the extra factor per element is ≤ exp(1.01·B·(1.02k + 3H(X₀) + 2)/X₀).
- With k = r₀ ≤ L, this is ≤ exp(10^{−9}) once 1.04·L²ℓ ≤ 10^{−9}·X₀, that is, about log L ≤ Λ/2 − 11. Up to that height,
  Theorem R and cor:R-Ecl hold with unchanged constants.
- The scan in corR_range.py confirms that E1 works up to ℓ/Λ ≈ 0.501.

### Bound E2 (crude; any pattern)
- Since m⁻_t ≤ t: Π_t (1 + m⁻_t λ) ≤ Π_{t=1}^{k} (1 + tλ).
- Per element this is ≤ exp((1/k) ∫_1^{k+1} log(1 + xλ) dx), which is about (k+1)λ/e for large kλ.
- With k = r₀ ≈ L/(3ℓ) and λ ≈ ℓ − log Λ, that is about 0.12·L per element.

### Why cor:R-Ecl needs the true pattern factor
- The paper's per-element factor is 1.8(L+4)·4L^{−6}·(1 + r₀/X₀)^{1.02}·1.01. It bounds 1 + r₀/X₀ ≤ 2L, which gives
  15·L^{−3.98}.
- In log(2z/δ · RHS) ≤ L + 6ℓ + r₀·log(per element), the coefficient of L is then 1 − 3.98/3 = −0.3267.
- Multiplying by E2's factor of about 0.12·L gives about 1.8·L^{−2.98}. The coefficient becomes 1 − 2.98/3 = +0.0067 > 0, so
  the corollary fails for large L if 2L is kept.
- With the true factor:
  - if r₀ ≤ X₀, then (1 + r₀/X₀)^{1.02} ≤ 2.03. Per element this is about 14.8·L^{−5}; times 0.12·L it is about 1.8·L^{−4},
    and the coefficient is 1 − 4/3 < 0. Fine.
  - if r₀ ≫ X₀, then (1 + r₀/X₀)^{1.02} ≈ (L/(3ℓX₀))^{1.02}. The coefficient of L becomes about
    0.0067 − 0.34·(Λ + log 3ℓ)/ℓ, which is < 0 if and only if ℓ ≲ 51·Λ.
- Exact scan (corR_range.py, E2 with m⁻_t ≤ t, 6000 log-spaced points from L = 465 to ℓ = 100Λ):
  - the first failure is at ℓ/Λ = 51.085 for Λ = 10⁸, and at 51.164 for Λ = 10⁹;
  - the inequality holds at every grid point below that, and fails at every point above.
- Result: with the crossing loss included, cor:R-Ecl holds for log L ≤ 51·Λ. Above that it is open.

### Cover Bound limit (Lemma reduction(ii))
- The paper's C′ = e·D·D·L^{2.1}·2L uses D ≤ L twice. The CapL setting has D ≤ 2L/Λ, so in fact
  C′ ≤ 8e·L^{5.1}/Λ² ≈ 21.75·L^{5.1}/Λ².
- The crossing loss per row (E2, with r < r₀ rows and m⁻_t ≤ t) is at most 1 + rλ ≤ L/3 for L ≥ Λ.
- So C″ ≤ 7.25·L^{6.1}/Λ².
- The requirement θδC″ ≤ 1, with δ = 4L^{−6}, reads 29θ·L^{0.1}/Λ² ≤ 1, that is, L ≤ (Λ²/(29θ))^{10}. That is about
  10^{145.4} at Λ = 10⁸.
- The type-union output 2zθC″ is ≤ 13L^{5.1}z for L ≤ 0.89Λ².
- Above that, criterion (iii) needs (1+j) log(1/w) ≥ L + 10.1ℓ + 2.7 − 2 log Λ. This is implied by (iii)'s L + 10ℓ + 10 when
  ℓ ≤ 441, which covers the whole range L ≤ 10^{145}. So Thm caplw's criterion is unchanged in this range.
- E1-type charging does not apply to the Cover Bound as written. When y_t is an R-row, its old-pivot occurrence carries no
  τ-excess weight, because R-rows carry 1/n_y and the w_y count instead.
- Above (Λ²/29)^{10}, the Cover chain is open.

## Part 4/4: checker focus points, confidence and scripts

### Where a checker should look, hardest first
1. **The union reading.** The main claim is that the live repair is valid only per full type, because Thm R and the Cover
   Bound need the union over free structures. Check these against the source:
   - the Thm R proof, "Record … the cofactors c_1,…,c_k … sum over patterns": the free structure is not part of the pattern;
   - Lemma reduction(ii), "the Euler chain of a row of C, its kept free primes in all blocks together with its tail: at most
     Ch": the free-prime count is summed inside Ch;
   - the live (S3), "assigned, by the type alone … The row y_1 and the number r of its columns are fixed by the type";
   - the arithmetic: summing the exact count over r gives Σ_r P(|R ∩ [a,s_max]| ≥ r) = E|R| = Σ 1/g.
2. **Crossing Lemma, P1–P2.**
   - The bound J ≤ Π c_y^{−1}·Φ(n, rest) with Φ free of F_t. This is the τ_j replacement of SVL(ii), valid on Proj.
   - The formula log q*_{p_t} = log Q − Σ_y w_{y,t} log c_y, with Q free of F_t, from the FAC shift with
     v_g = E_{R≤t,P≤t}^{−1} e_{g,R≤t}.
   - The non-chain rows of R_{≤t} in the Cover Bound, where only m⁻_t ≤ t is used. Check that the per-row relaxation over
     cover pieces is consistent with type-fixed R-row entries in the union reading.
3. **P4.** The window weight of one stretch is ≤ θ₊ with H(s) varying: admissible slots satisfy |φ(s)| ≤ H(s)/2, φ increases
   by at least s′ − s within a stretch, and the (F1) slot count applies over an interval of length about H.
4. **P0/P3, order of operations.**
   - Joining-row tops are bounded by A_top at the label s, on G_{<s}, inside the label sum, and each row gets A_top once.
   - The carried output Eu_s(s_{t+1})^{−1} is non-increasing in s_{t+1}, and is a function of the primes decided before
     s_{t+1}.
5. **Charging Lemma.** Check the uncharged occurrence x of each column, and that m⁻_t > 0 implies E_{y_t,P<t} ≠ 0. This is
   where single-pivot runs are used: with longer runs, E_{C_t,P_t} can be non-monomial.
6. **Height limits.** The values 51·Λ and (Λ²/29)^{10} are numerical evaluations of closed-form inequalities (corR_range.py),
   and need a written verification. They rely on two changes:
   - the true pattern factor (1 + r₀/X₀)^{1.02} instead of 2L;
   - D ≤ 2L/Λ instead of D ≤ L.

   Also check whether the paper actually needs the CL chain at heights above log L = 51Λ or L = 10^{145}.
7. **Not checked:** whether Thm caplw has spare room if criterion (iii) has to change. In the range covered it does not
   change.

### Confidence
- High: the per-type correctness of the live repair; the union-reading objection; and that the loss is intrinsic (exact
  device identity, toy counterexample to the v3 step, Monte Carlo).
- Moderately high: the Crossing Lemma and the Charging Lemma.
- Medium: the exact height constants.
- #48 stays open above log L = 51Λ (Thm R, cor:R-Ecl), above L ≈ (Λ²/29)^{10} (Cover Bound), and for E1-type charging in the
  Cover Bound.

### Scripts
The scripts are kept in review/recheck/pil-o3b/; run them with python3 -I -B.

| Script | What it does | Result |
|---|---|---|
| block_lemma.py | Exact-rational brute force of the live (S3)(a) joint block bound for a **fixed** type. Covers random weights, passing and fresh rows, owners, exponents ≥ 1, nested good events, and A := Eu(g). Also runs an adversarial label-sum variant over pinned values q. | Over 3000 instances, max LHS/RHS = 0.62; label-sum variant 0.40. |
| crossing_lemma_check.py | Exact toys in the **union** reading, with a piece of any size. Additive toy for log q* (q* = Q + Σ d_i), window half-width h, one passing row. Checks LHS·E0 ≤ 1 + Σ_{d_i>0} w_i/(1+w_i) (the Crossing Lemma) and the v3 claim LHS·E0 ≤ 1. | Over 4000 instances, the crossing bound has max ratio 1.0. The v3 claim reaches 1.867 when q* is increasing and 1.689 for mixed signs, and holds (1.0) when q* is non-increasing. |
| crossings.py | Monte Carlo of E[#crossings] at one boundary. R-primes are modelled as a rate-1 Poisson process in log log g, with q* = K·c^β and log K = κ log a. | β = 1 gives about 1 + 0.56·log D (1.97, 3.26, 4.55, 5.85, 8.44 at D = 10, 10², 10³, 10⁴, 10⁶); β = 0.1 stays bounded, at about 1.12. |
| negscan.py | Random pivot patterns, k ≤ 8, single-pivot runs, lexicographically first bases. Compares Σ_t m⁻_t and #{t : m⁻_t > 0} with the excess M. | No violation of the Charging Lemma. (The counterexample to the stronger Σ_t m⁻_t ≤ M is the hand-made bidiagonal pattern in part 3.) |
| corR_range.py | Scans the cor:R-Ecl inequality over 465 ≤ L and ℓ ≤ 100Λ, for Λ = 10⁸ and 10⁹, in three modes: no loss, E1 (charging) and E2 (crude). | Gives the thresholds 0.50Λ (E1) and 51.1Λ (E2). The E2 run with m⁻_t ≤ t was an inline patch, and part 3 quotes its numbers; the file on disk still uses t − 1, which gave 51.2Λ. |
| notes.md | Working notes. | |
