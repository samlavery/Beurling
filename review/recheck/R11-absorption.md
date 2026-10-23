# R11: the absorbed-element sparsity chain

The checker was cond-check, a fresh AI agent independent of the authors of these sections. It worked on the frozen snapshot
98cae94. It was not allowed to write files, so the lead saved its messages here.

## Verdict: CORRECT WITH FIXES

There is no BLOCKING defect. There are two FIXABLE defects, one in the proof wording and one in the bookkeeping of the
dependency certificate, and some COSMETIC items. Lemma P step (v) is overbroad as stated; that was found separately by the
external reader and is now correction #65.

## 1. The absorption rule and adaptedness (02-construction:48–91): correct

- **The rule.** 𝒜 = {n : log n ≥ L_* = 10⁷, the latest prime r is jittered, r < y(n)}, with y frozen per dyadic scale. Since
  L_* < Λ, the condition log n ≥ L_* is inactive.
- **The smoothed density.** ρ_𝒜(u) = #(𝒜∩[u, u+h])/h, with h = u^b and b = θ/2.
  - T jumps at each a ∈ 𝒜.
  - T′_cont contains −ρ̄_𝒜, capped at 0.1/log u. The cap is inactive on the good event, because ρ_𝒜 ≤ L⁻⁴ there.
- **Causality.**
  - An element of 𝒜 ∩ [1, u+h] has all its primes below y(n) + H ≪ u − H(u).
  - So 𝒜 ∩ [1, u+h], and hence ρ_𝒜 on [X₀, u], is known before slot u − H(u).
  - Lemma adapted therefore holds, and so does the adaptedness of the cap.
- **Range.**
  - 𝒜 = ∅ at every scale with s = loglog z − 2 log Λ ≤ s_H. There y < X₀⁻ (caplw(b), Step 5, first bullet), so no jittered
    prime lies below y.
  - So absorbed elements exist only above exp(Λ²e^{s_H}), that is, for loglog > 42.81 at Λ = 10⁸.
- **Independent check of the parameters** (`params_twelvetwo.py`).
  - It implements c, γ, M₁, M̄₁, H, L₀ and y in log space, for Λ ∈ {10⁸, 10⁹, 10¹⁰, 10¹², 10¹⁶, 10²⁰}.
  - s_H = 5.974538.
  - For s ≤ s_H, the largest value of log y − log X₀⁻ is −2607, at Λ = 10⁸. The paper's bound is ≤ −2597, and the margin grows
    quickly with Λ.

## 2. Lemma P (05-queue:1234–1278): correct, with fix F1

Every step was re-derived.
- **(i) Smoothness.** A prime decided no later than r has value ≤ r + 1.01·H(r) < 2y, with y = sup_{[u,2u]} y(v). That covers
  the dyadic scale of n.
- **(ii)–(iii) The divisor trick.** d ∈ (h, 2yh] is a 2y-smooth element, and |I_d| < 1.
- **(iv) The window count.**
  - u/d ≤ u^{1−θ_b}, and u/d ≥ u^{1−θ_b}/(2y) ≫ X₀.
  - With overlapping grid windows, the cover needs at most L⁶/4 + 2 windows, below C_d/M₁ = L⁶/2.
  - M₁ is non-decreasing across scales.
- **(v) Rankin.**
  - π_NN(s) ≤ 2s/log s follows from Lemma cm(i) by dyadic summation (C1).
  - The partial summation gives 2(u_*/log u_*)(1 + 2/log u_*) + loglog 2y + O(1).
  - At the point used, η = log u_*/log 2y ≪ ½, so the prime-power terms are O(1). The O(1) fits in 0.09·u_*/log u_*.
  - The final step needs loglog 2y ≤ 1.79·u_*, and this holds.
- **(vi)** is exactly eq:twelvetwo.
- **eq:twelvetwo itself.** Checked at θ_b = 1/8, the worst case, with y = sup_{[u,2u]} (two adjacent scales):

  | Λ | Smallest LHS/RHS |
  |---|---|
  | 10⁸ | 3.60 (at the end of the ramp, s = s_H + 1) |
  | 10⁹ | 4.01 |
  | 10¹⁰ | 4.42 |
  | 10¹² | 5.24 |
  | 10¹⁶ | 6.88 |
  | 10²⁰ | 8.52 |

  Also, u₀ ≥ 5.94·Λ wherever 𝒜 ≠ ∅ (the paper claims ≥ 5Λ). On every grid point u₀ ≥ 100 and loglog 2y ≤ 1.79·u₀.
- **Lemma P holds at every u ≥ X₀.** Where 𝒜 does not meet [u, 2u], the conclusion is trivially 0.
- **F1 (FIXABLE).**
  - The statement claims the bound on Good(<t) for every t ≥ t_u = 9u/L¹¹ + H(u) (05-queue:1240). The proof (iv) only says
    "Good(<u) ⊂ E_cl^{(u)}".
  - The stronger form is the one that 04f-bridge:56–57 and rhoA(c) use, at heights up to t + 1.01H(t).
  - The stronger form is true. E1 at the dyadic scale x′ of u has time 8x′/L¹¹ + H(x′) ≤ 8.0001u/L¹¹ + H(u), which is below t_u.
    That E1 covers heights ≤ 2u/L¹¹, which contains every u/d ≤ u^{1−θ_b}. Lemma cm(i) at heights ≤ 2y also holds on Good(<t_u).
  - **Fix:** one line in the proof saying this.

## 3. Lemma rhoA, Prop S1S2, and the density and its smoothing: correct

- **(a)** is Lemma P.
- **(b)**
  - For an absorbed landing at height Y, the cofactors w are 2y(Y)-smooth with w ≥ Y/y(Y).
  - Rankin with u = L/log 2y ≥ 1.7·10⁹ (≥ 10⁸, as claimed) gives K_𝒜ρ̃ ≤ L⁻⁴.
  - With (a), |σ_𝒜| ≤ 2L⁻⁴.
- **(c)** 8L⁻³ ≤ e^{−126.4} wherever 𝒜 ≠ ∅, since L ≥ 3.93·10¹⁸ there.
- **S1/S2** are definitional, and S1 is vacuous because L_* < Λ.
- **Remark stopped (02-construction:73–74).** The cap is inactive, since ρ_𝒜 ≤ L⁻⁴ < 0.1/log u (C2).

## 4. The absorbed part of Lemma T1 (#34, 02-construction:158–175): correct

- **The identity.** #𝒜(≤x) − ∫^x ρ = Σ_{a≤x}(1 − M_a) − Σ_{u_a<x<a}∫_{u_a}^x du/h. This is exact, because a contributes to ρ(u)
  exactly when u ∈ [u_a, a].
- **The bounds on M_a.** (u_a/a)^b ≤ M_a ≤ 1, and 1 − M_a ≤ b·u_a^{b−1} ≤ 1.01·b·a^{b−1}.
- **The sum.** Σ a^{b−1} ≤ 1.001·∫u^{b−1}ρ ≤ 1.01·b⁻¹·x^b(log x)⁻⁴.
- **The derivative step.** 4/(b log u) ≤ 3.2·10⁻⁶.
- **The total.** 1.03 + 2 ≤ 3.1, and 3.1·x^{θ/2}(log x)⁻⁴ ≤ 2x^{θ/2}.

## 5. Lemma ZA (03-zeros:137–194), including #33, #35 and #39: correct

- **The bounds (i)–(iv) on w_a**, re-derived. The closed form is w_a = (a^{1−b} − a^s·u_a^{1−s−b})/(1−s−b), and
  |e^z − 1| ≤ |z|·e^{max(0, Re z)}.
- **The count.** #𝒜 ∩ [1,x] ≤ Ψ_NN(x, 2y(x)) ≤ x·e^{−ς_*(log x)}, with λ(v) = max(22.6Λ, 12 log²v + 9 log v + 8).
  - ς_* is increasing, because vλ′ = 24 log v + 9 < λ.
  - log 2y ≤ λ(v) wherever 𝒜 ≠ ∅, with margin ≥ 8.2·10⁶ on the grid.
  - 22.6Λ ≤ 12.1·ℓ_std², with ratio 1.0039.
- **Constants at Λ = 10⁸.** u_* = 1.7402·10⁹, and 0.45·u_*·log u_* = 1.6662·10¹⁰.
- **(a), the terms a ≤ Y.** These use |1 − w_a| ≤ 2.0001 and the split at V = e^{ℓ_std}:
  - δ_k·V ≤ 18Λe^{−2Λ}·V;
  - ς(v₀)/2 ≥ ℓ_std + 20;
  - 504·(loglog x_k)² ≤ log x_k.
- **(a), the terms a > Y.**
  - 2·(2−b)/(1−b) ≤ 4.67 ≤ 5.4.
  - log Y ≥ 0.66·log x_k, since (1−θ)/(1−θ/2) ≥ 0.6667, so these terms lie in the standard regime.
- **The region.** The Rouché circle lies in σ ≥ 1 − δ_k. Lemma designedzero step 6 gives |s*−(1+iγ_k)| + 1/log x_k ≤ δ_k;
  this is #39.
- **(b)**
  - Plancherel gives (2π/Γ_k)·L⁻⁴·Σ a^{1−2σ}.
  - At σ = ¾ this is ≤ x_k^{1/2−1/(14 loglog x_k)} + exp(e^{ℓ_std}/2).
  - Dividing by Γ_k gives x_k^{θ−1/2−o(1)}.

## 6. The consumers: all correct

- **The zeros theorem.** |Ê_𝒜| ≤ 2e^{−1.666·10¹⁰} + e^{−10¹¹} ≤ e^{−10¹⁰} on the discs, the Rouché circles and σ = 1. This holds
  on 𝒢, where the cap is inactive and the series Σa^{−s}(1 − w_a) converges absolutely.
- **goodheights(ii).** The ρ_𝒜 term is ZA(b), and the Dirichlet sum excludes 𝒜.
- **(H_BS), #51 (04a-setup:135–154).** The absorbed part gives ε₁ ≤ 2u^{θ/2−1}, and only above exp(Λ²e^{s_H}). Its contribution
  to η₁ and η₂ is astronomically small.
- **04f-bridge:229–235.** Covering I gives (2.01·δN_* + N_*^{θ/2})·L⁻⁴, using h(N_*)/h(N_*(1−2δ)) ≤ 1 + δ.
- **04x-x0band:155–158.** (4^{θ/2}|I| + (2M)^{θ/2})·L⁻⁴ ≤ 0.01|I| + (2M)^{θ/2}.
- **04k-kernels:364–365.** |I_v| ≤ 2.1·H(v)/X₀ is below h(v/X₀), so two windows suffice and #𝒜 ≤ 2(v/X₀)^{θ/2}. The heights
  v/X₀ ∈ [X₀/2, X₀) lie outside Lemma P's range u ≥ X₀, but 𝒜 is empty there (C5).
- **04e threshold-mass (#61).**
  - U ≥ 0.97√x ≥ X₀^{1.5}.
  - δU ≥ h(U), because U^{1−θ/2} ≥ 0.97·x^{3/8} ≥ 1/δ.
  - (1.08|J_p| + h(U))·(log 0.75U)⁻⁴ ≤ 0.01|J_p|.
  - Lemma P holds on Good(<x) at every v ≤ x.
- **caplw(b)** is verified numerically (§1–2).

## 7. Circularity: none, because the argument is an induction on height

**The chain.**
- Lemma P at u uses E_cl at heights ≤ u^{1−θ_b}, and Lemma cm(i) at heights ≤ 2y.
- E_cl at z uses (F1)–(F4) through the PIL, at heights ≤ 2z + H. (F1) needs only −ρ̄_𝒜 ≤ 0.
- Lemma cm at w uses (H_BS) on [1, w].
- (H_BS) uses the queue and the lag at lower scales, and Lemma T1 and Lemma P at heights ≤ w + h.

So Lemma P at u uses Lemma P only at heights ≤ 2u^{1−θ_b} + O(H), which is strictly lower. The base case is everything below
exp(Λ²e^{s_H}), where 𝒜 = ∅.

**What depcheck shows.** depcheck runs and reports the graph acyclic, but it omits three real edges (F2):
- eq:HBS → lem:T1 (04a:135–145);
- eq:HBS → cor:lag (04a:129–130);
- prop:g1 → lem:lemmaP (04f:233–235).

Adding all three, even as same-time edges, keeps the graph acyclic. With only the edge eq:HBS → lem:T1 added, however, making
lem:T1 → lem:lemmaP same-time creates the cycle lem:cm → HBS → T1 → lemmaP → lem:cm. So the "strictly earlier" marking on
T1 → lemmaP is load-bearing. That marking is correct: Lemma P at x uses only events whose times lie below t_x < x, and uses
lem:cm only at heights ≤ 2y ≪ x.

## 8. Defects

### FIXABLE

**F1. The proof of Lemma P covers a weaker statement than the one stated** (05-queue:1240–1241, against 1255–1256).
- The proof shows the bound only on Good(<u). The statement, and its uses at heights up to t + 1.01H(t) (04f-bridge:56–57,
  rhoA(c)), need Good(<t_u).
- **Fix:** say that Good(<t_u) contains E1 at the dyadic scale x′ of u. Its time is ≤ 8.0001u/L¹¹ + H(u) < t_u, and it covers
  heights ≤ 2u/L¹¹, which contains every u/d. Lemma cm(i) at heights ≤ 2y also holds on Good(<t_u).

**F2. depcheck omits real edges** (certificates/depcheck/depcheck.py:36 and 59, against B-certificates:380).
- The certificate claims to encode "the full dependency graph, one edge per internal input", but the three edges listed in §7
  are missing.
- **Fix:** add them; the graph stays acyclic. Optionally, mark lem:lemmaP → lem:cm as strictly earlier (heights ≤ 2y).

### COSMETIC

- **C1. 05-queue:1259–1261.** π_NN(s) ≤ 2s/log s is attributed to Lemma cm(i), which bounds ψ, not π. Add the dyadic step:
  ψ(x) − ψ(x/2) ≤ 0.71x gives π(s) ≤ 1.42s/log s·(1 + 3/log s) + π(e²⁰).
- **C2. 02-construction:73–74.** The text says "since its time is ≤ u − H(u) (Lemma adapted)". The real reason is
  t_u = 9u/L¹¹ + H(u) < u, from Lemma P, not Lemma adapted.
- **C3. 04f-bridge:231.** L_* := log(N_*/2) clashes with L_* = 10⁷ in eq:absorbed.
- **C4. 05-queue:1304.** "Cofactors w are y-smooth": they are 2y(·)-smooth. The letter y is also overloaded, standing for both
  a height and a threshold.
- **C5. 04k-kernels:364–365.** State that |I_v| ≤ h(v/X₀), and that 𝒜 = ∅ at heights below X₀, where Lemma P is not stated.
- **C6. 05-queue:1283.** "At every height": state the event, that is, on Good(<t) at heights ≤ t + 1.01H(t).
- **C7. 02-construction:165 and 175.** Only 𝒜 ∩ (x, x+h(x)) is needed in the second sum. The "+O(1)" is superfluous, since 𝒜 is
  empty near X₀.

## 9. Toys

- **`toy_lemmaP.py`.** A synthetic jittered system.
  - Set-up: rational primes below 40; adaptive slot coins with probability 1/log s; continuous box jitter with H = 6; elements
    ≤ 3·10⁵; 𝒜 = jittered latest prime < y, for y ∈ {60, 90, 120, 200} and b ∈ {0.2, 0.25, 0.3}.
  - Result: on 4752 windows, the exact count E is ≤ the divisor-trick sum DT, which is ≤ max_d N(I_d)·Ψ(2yh, 2y). There are
    0 violations, and the largest E/DT is 0.18.
- **`toy_T1_wa.py`, part 2a.** The identity for T1's absorbed part, and its bounds, on random absorbed sets: 428,330
  evaluations, 0 violations. The largest value of Σa^{b−1}/(1.001∫u^{b−1}ρ) is 0.9990.
- **`wa_flint.py`.** The w_a bounds (ii)–(iv) in arb at 400 bits.
  - Range: 1296 points, with a ∈ 10⁵–10²⁰, σ ∈ [0,2] and t up to 10¹², over a range of b.
  - Result: 0 violations. A float version showed false violations from cancellation, and the ball version settles them.
- **`params_twelvetwo.py`** gives the numbers in §§1, 2 and 5.

## 10. Confidence and limitations

- **High confidence** that the absorption chain is correct: the definitions, Lemma P, rhoA, T1, ZA, every consumer, the ranges
  and the non-circularity. Every constant was re-derived, and the parameter thresholds were checked independently and
  numerically for Λ from 10⁸ to 10²⁰.
- **Taken as inputs, not re-verified:**
  - Prop ecl and E_cl themselves;
  - the proof of Lemma cm;
  - the queue bound and the lag;
  - caplw(b) beyond the numerical grid;
  - the claim 2^{1e−5}(1+2c^{−1/2}) for y across scales, which the sup-over-[u,2u] computation makes unnecessary.
- **Limitation of the toys.** They are scaled-down synthetic systems. They test the structure (the divisor trick, the
  smoothing algebra, w_a), not the real parameter regime, which only the log-space parameter check covers.
- **Lemma P step (v).** The overbroad Rankin statement there was found separately by the external reader, and is correction
  #65. At the point used, Y = 2yh, the Rankin exponent is far from 0.

Copies of the scripts are in `review/recheck/r11/`.

## 11. Addendum: Lemma P step (v), correction #65

The defect itself was already known: the external reader had found it.

### Where the bound is used, the Rankin exponent is far above 0.69

**The analytic argument.** Wherever 𝒜 ≠ ∅, we have y ≥ X₀⁻ and H ≥ H_std, so log 2y ≥ max(Λ, 8ℓ²). The value actually used has
u_* ≤ L, so log u_* ≤ ℓ. Hence 1 − σ ≤ ℓ/max(Λ, 8ℓ²) ≤ 1/√(8Λ), and so σ ≥ 0.99996.

**The numerical check** (`sigma_check.py`). It uses the exact parameters, y = sup_{[u,2u]}, θ_b ∈ {1/8, θ₁/2}, and Λ from 10⁸ to
10²⁰. The smallest σ is 0.999994 at Λ = 10⁸, 0.999998 at Λ = 10⁹, and ≥ 0.999999 for Λ ≥ 10¹⁰.

The bound of step (v) has three uses:
- Lemma P (vi), at Y = 2yh;
- Lemma ZA's proof, at Y = x for every x up to 2x_k;
- Lemma rhoA(b), which has its own Rankin bound.

All three are safe, because the smoothness bound 2y(x) is tied to Y. The counterexample needs the smoothness bound fixed while
Y → ∞, and that never happens here.

### Other places where Lemma P's proof claims more than it uses or checks

1. **"As in Lemma rowweights(c)" is too broad a citation.**
   - Since #49, rowweights(c) covers only y = X₀ and the rational primes.
   - Lemma P needs the argument re-instantiated: the realised primes up to 2y, the constant 2 in place of 1.26, Λ replaced by
     log 2y, and Σ1/p from Lemma cm(iv).
   - The margins are ample.
   - **Status:** #65's rewrite of step (v) does this explicitly.
2. **The aside "Alternatively, use Corollary localcount at height u/d" in step (iv) is never checked.**
   - It is not checked against eq:twelvetwo with localcount's constant.
   - It would pass, with LHS/RHS ≥ about 2.9 at Λ = 10⁸.
   - It is also the only source of depcheck's edge lem:lemmaP → cor:localcount.
   - Either delete it or check it.
3. **"eq:twelvetwo holds wherever 𝒜 meets [u, 2u], by caplw(b)" is broader than caplw(b).**
   - caplw(b) is proved at dyadic z with y(z), but Lemma P uses non-dyadic u, with y the sup over two scales.
   - The claim is true by margin: the two-scale computation gives a smallest LHS/RHS of 3.60.
   - One sentence should say so.
4. **F1** (§8): the statement covers Good(<t_u), but the proof shows only Good(<u).

Steps (i)–(iii) and (vi) are used exactly as stated.

## 12. Check of the repair of #65 (live tree, diffed against 98cae94)

**Verdict: CORRECT.** 0 BLOCKING, 0 FIXABLE, 4 COSMETIC.

### The constants of the new step (v) all hold

- **Rankin.** Y^σ = Y·exp(−u_* log u_*).
- **The π bound.** Below X₀⁻, RS (3.6) gives 1.25506 ≤ 1.26. Above X₀⁻, 1.42/0.9 = 1.578, with plenty of room (see C2).
- **The remainder.** For the rational primes, R(0.69) ≤ 0.77, certified by rankin_R.py. The jittered primes contribute about
  10·X₀^{−0.38}. The total is ≤ 0.78.
- **Σ_{p<2y} 1/p** ≤ loglog x + 4.04.
- **The partial summation.** t₀ ∈ [e, e^{1.45}], and 2η/(1−η) ≤ 0.90. The Ein bound applies, since log u_* ≥ 19.11.
- **The total.** The constant is 5.88 ≤ 5.9 and the coefficient is 2.2093 ≤ 2.22. Since 5.9 ≤ 0.08u_*/log u_*, the coefficient
  becomes 2.30.
- **The final inequality.** 0.1x − 2.3/x is increasing in x, and equals 1.79105 at x = 19.1138 (C1).

### (∗) holds at Y = 2yh wherever 𝒜 meets [u, 2u]

- u_* = 1 + u₀ ≥ 5.94Λ, from the independent parameter script.
- loglog 2y ≈ 21.5, which is ≪ u_*.
- η ≤ (7.9(Λ−1))^{−1/2} ≤ 3.6·10⁻⁵. gap-g3's chain checks; numerically the smallest σ is 0.999994.

### (∗) also holds at Lemma ZA's use (Y = x)

- u ≥ u₀ ≥ 2Λ, because s is non-decreasing, and η ≤ 3.6·10⁻⁵.
- The elements of 𝒜 ∩ [1, x] are 2y(x)-smooth.
- The later majorant λ(v) uses only monotonicity in log 2y.

### The sweep is confirmed, with one exception (C3)

Every other Rankin bound uses a fixed exponent, either bounded away from 0 or near 1.

### Cosmetic items

- **C1.** Write log u_* ≥ 19.11. At 19.1, the left side of the final inequality is 1.7896 < 1.79.
- **C2.** "π(s^{0.9}) ≤ s^{0.9}" is not automatic for the realised system. Use π(t) ≤ ψ(t)/log 2 ≤ 2.05t instead, which gives
  π(s) ≤ 1.578s/log s + 2.05s^{0.9} ≤ 2s/log s.
- **C3.** In Lemma rhoA(b) (05-queue:1333–1335), the Rankin exponent is not stated, and the step cites only cm(i). It is true
  with exponent 1 − 1/log 2y, as in rankin-crude, or via step (v) itself.
- **C4.** ZA's "u ≥ 100" should be u ≥ 2Λ. beurling-lit is making this edit as part of #64.

## 13. Check of #66, the fixes of the R11 findings (live tree, diffed against 98cae94)

**Verdict: CORRECT.** 0 BLOCKING, 0 FIXABLE, 3 COSMETIC. A private build exits 0 with no warnings and 15 overfull boxes, and
pdftotext shows every changed passage in full.

### F1: Lemma P step (iv) is correct
- u/d ≤ u^{1−θ_b} ≤ 2u/L¹¹.
- E1 at the dyadic scale x′ ≤ u has time ≤ 8.0001u/L¹¹ + H(u) < t_u, and covers heights up to 4x′/L_{x′}¹¹ ≥ 2u/L¹¹.
- Lemma cm at heights ≤ 2y holds on Good(<t_u).

So the stated form, on Good(<t) for every t ≥ t_u, is now proved.

### F2: depcheck is correct
- **Rerun:** 78 nodes, 195 edges, 28 strictly earlier.
- **The counts reconcile.**
  - #64 removed 2 edges and 1 node.
  - #66 added 3 same-time edges, changed lemmaP → cm to '<', and removed lemmaP → localcount ('<').
  - These match App B's block and 01-setup:114.
- **The cycle cm → HBS → T1 → lemmaP → cm** is now broken twice, by two '<' edges.
- **Lemma P no longer uses localcount anywhere.** The remaining localcount edges are direct, legitimate uses.

### The other changes are all correct
- The sentence on eq:twelvetwo at non-dyadic u. The ratio at the end of the ramp is 3.56, and the checker's own two-scale
  computation gives 3.60.
- Remark stopped, Lemma T1's second sum, 04f's L_I, 04k's two windows, and rhoA(a)'s event.
- rhoA(b): the exponent 1 − 1/log 2y(v), the bound e^{8.2}log(2y)e^{−u}, and the result ≤ 0.45L⁻⁴.
- #65's C1 (19.11 gives 1.79105) and C2 (1.42/log 2 = 2.0486).

### Swallowed text: none
All 26 comment lines for corrections 60–67 are whole-line. gap-g3's four repaired #66 comments render correctly in the PDF.

### Cosmetic items
- **C1.** Row 66's section references should match this file. They do: the R11 addendum is §11 and the check of #65 is §12.
- **C2.** rhoA(b)'s "since u ≥ L/max(…)" holds only where K_𝒜 ≠ 0, that is, for s > s_H. **Fixed by the lead:** the sentence now
  reads "Wherever K_𝒜 ≠ 0 (so s > s_H)".
- **C3.** The non-dyadic sentence cites Lemma raisedy for y, which covers only the ramp. **Fixed by the lead:** it now also
  cites caplw(c), through L₀, for y in the standard regime.
