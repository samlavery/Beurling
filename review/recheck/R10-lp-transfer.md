# R10: Theorem lp, Steps 1–4 (positivity transfer), and the uses of eq:lp-transfer

The checker was margin-var-check, a fresh AI agent independent of the authors of this section. It worked on the snapshot
b14b955. It was not allowed to write files, so the lead saved its messages here.

## Verdict: CORRECT WITH FIXES

- **Bounds.** Every displayed bound of Steps 2–4 holds, and so does eq:lp-transfer, for every y ≥ X₀ and every η ∈ [η_y, 1/8].
  The 10⁻² claims and the (η log y)⁻¹ claim hold with an enormous margin.
- **One FIXABLE defect (F1).** The text attributes the T₀-tail part of the bounds on |Δ| and |Δ′| to "(LP-a)", which says
  nothing about T₀ on (y, ∞). The bound actually needs two facts: T₀ is non-decreasing (eq:G1), and T₀(u) − u = O(κu)
  (Lemma T1). The bound is true, with a factor 2 to spare, but its stated source cannot give it.
- **Three COSMETIC items (C1–C3).**
- **Counts:** 0 BLOCKING, 1 FIXABLE, 3 COSMETIC.

## Step 1 (04e:119–128): correct

- **D̂^♯.** D^♯ = D(min(u, y)) and D(X₀⁻−) = 0, so D̂^♯(s) = D(y)y^{−s} + s∫_{X₀⁻}^y D u^{−s−1} du. By (LP-a),
  |D̂^♯| ≤ |s|·X₀⁻^{θ′−σ}/(σ−θ′) + y^{θ′−σ}.
- **ζ^♯.** ζ^♯ = T̂₀ + D̂^♯, because N^♯ = T₀ + D^♯ on all of [1, ∞).
- **Π^♯.** Π^♯ = log*(dN^♯) converges for large σ: dN^♯ − δ₁ has no mass in (1, 2), so its σ-norm tends to 0. Since log* is
  causal, Π^♯ = Π on [1, y].

## Step 2 (04e:130–145)

- **N_y = exp*(Π|_{[1,y]}).** Properties (a)–(d) are correct. (d) holds term by term, because Π ≥ 0. N_y has finite mass at
  every σ ≥ 0, since Π|_{[1,y]} is finite.
- **∫_{[1,z]} dΠ/u ≤ log log z + 4.5.**
  - Lemma cm(iv) with y₀ = 2 gives 1/2 + log(1/log 2) + 2.20/log 2 + Σ_p Σ_{k≥2} 1/(kp^k) = 0.5 + 0.3665 + 3.1740 + 0.3157
    = 4.356 ≤ 4.5.
  - The large realised primes add ≤ 1/X₀.
  - For ℕ, the true maximum over z ≥ e is 0.7393, at z = 3.
- **P_y(1) ≤ e^{4.5} log y** follows from (c).
- **S(z) ≤ log z + 0.43** is Lemma cm(ii).
- **The chain of hypotheses.** Lemma cm needs (H_BS) on [1, y]. That comes from (LP-a) together with eq:Erig and
  |R| ≤ 2u^θ log* u, not from eq:T1 itself (C1).

## Step 3 (04e:147–171): every bound, its source and its constant

Write σ = 1 + η, with 0 < η ≤ 1/8, and L = log y.

**(1) P_y(σ) ≤ 1/η + 6 + y^{−η/2}P_y(1).**
- On [1, y], N_y = N. (H_BS) and Lemma cm give ∫_{[1,y]} u^{−σ} dN ≤ N(y)y^{−σ} + σ∫_1^y u^{−σ} du + σ·η₁ log 2
  ≤ 1/η + 2.01. The route through (LP-a) and the structure of T₀ gives the same.
- On (y, ∞), dN_y ≥ 0 and u^{−η} ≤ y^{−η/2}, so the tail is ≤ y^{−η/2}P_y(1).
- The "6" has room: 2.01 would do.

**(2) |Δ| ≤ 2y^{−η}/η + y^{−η/2}P_y(1).**
- **The N_y part** is ≤ ∫_{(y,∞)} u^{−σ} dN_y ≤ y^{−η}P_y(1). That is stronger than the stated y^{−η/2}P_y(1) (C2).
- **The T₀ part** is ∫_{(y,∞)} u^{−σ} dT₀.
  - dT₀ = dΨ(·, X₀) + (1 − ρ_det + R′)du ≥ 0, by eq:target and eq:G1.
  - T₀(u) − u = E_rig(u) + R(u), with |E_rig| ≤ κX₀ + 2 + κu (eq:Erig) and |R| ≤ 2u^θ log* u (Lemma T1).
  - Partial summation then gives ≤ y^{−η}/η·(1 + 2κ(η + σ) + O(y^{θ−1} log y)) ≤ (1+3κ)·y^{−η}/η. This is inside the
    stated 2y^{−η}/η, but its source is not (LP-a) (F1).

**(3) |Δ′| ≤ 2y^{−η}(L/η + 1/η²) + y^{−η/2}P_y(1)S(y).**
- **The T₀ part** is the same, with the weight log u: ∫_y^∞ log u·u^{−1−η} du = y^{−η}(L/η + 1/η²), times (1+3κ).
- **The N_y part:** ∫_{(y,∞)} log u·u^{−σ} dN_y ≤ y^{−η}·(−P_y′(1)) = y^{−η}P_y(1)S(y), because
  −P_y′/P_y(1) = ∫_{[1,y]} dψ/u = S(y).

**(4) |P_y(s)| ≥ 1/P_y(σ) and |P_y′/P_y| ≤ S(y).** Both follow from Π ≥ 0 and σ ≥ 1.

**(5) η_y and eq:lp-transfer.** With η_y = 17 log L/L, y^{−η_y/2} = L^{−8.5}. The checker evaluated, in arb, exactly the
displayed bounds, with P_y(1) ≤ e^{4.5}L and S ≤ L + 0.43:

| Bound | Worst ratio to its claim | Where |
|---|---|---|
| P_y(σ) ≤ 2/η | 0.875 (1/η + 6 = 14 against 16) | η = 1/8, every y |
| \|Δ/P_y\| ≤ \|Δ\|·P_y(σ) ≤ 10⁻² | 2.9·10⁻⁵¹ | y = X₀ (Λ = 10⁸), η = η_y = 3.13·10⁻⁶ |
| \|d/ds log(1+Δ/P_y)\| ≤ (\|Δ′\|P_y(σ) + \|Δ\|P_y(σ)S)/(1 − 10⁻²) ≤ (ηL)⁻¹ | 1.8·10⁻⁴² | y = X₀, η = η_y |

- **Why these are the worst points.** In each ratio every term is monotone in η. For the second and third bounds it decreases
  in η (because ηL ≥ 17 log L ≫ 2), so the maximum is at η = η_y. For the first it increases, so the maximum is at η = 1/8.
  The ratios also decrease in L: at L = 10⁹ the second and third ratios are 8·10⁻⁵⁸ and 6·10⁻⁴⁸, and at L = 10¹² they are
  2·10⁻⁷⁷ and 2·10⁻⁶⁴.
- **The range of y.**
  - [η_y, 1/8] is non-empty only for L ≥ 930, and all three bounds hold for every L ≥ 930.
  - ε_f = 5·10⁻⁴ ≥ 1/L needs L ≥ 2000.
  - The 10⁻⁸ in eq:lp-pole needs L ≥ 10⁸, with equality at Λ = 10⁸. This is the binding condition, and y ≥ X₀ gives it
    exactly.
  - Step 3 needs only y ≥ X₀. eq:lp-yrange is stronger, and only Step 7 needs it.

**(6) F and the conclusion (04e:159–161).**
- The σ-weighted norm is submultiplicative, and |(dN_y)^{*−1}| ≤ dN_y. So ‖F‖_σ ≤ [∫_{(y,∞)} u^{−σ}(dT₀ + dN_y)]·P_y(σ).
  This is the same majorant as |Δ|·P_y(σ), so it is ≤ 10⁻².
- dN^♯ = dN_y * (δ₁ + F) and F̂ = Δ/P_y. So ζ^♯ = P_y(1 + F̂) with |F̂| ≤ 10⁻², and ζ^♯ has no zeros there.
- log*(δ₁+F) converges, and Π^♯ = Π|_{[1,y]} + log*(δ₁+F) has ∫u^{−σ}|dΠ^♯| ≤ log P_y(σ) − log(0.99) < ∞.
- For σ > 9/8, the conclusion uses the fact that ‖F‖_σ is non-increasing in σ (C3).

**(7) The coefficients of −P_y′/P_y (04e:162–171).**
- −P_y′/P_y(s) = ∫_{[1,y]} u^{−s} dψ, which is a positive measure.
- The identity (1+cos φ)⁴ = (1/8)(35 + 56cos φ + 28cos 2φ + 8cos 3φ + cos 4φ) holds (arb, 1000 points, error 2·10⁻³⁴), and
  Σa_k = 128. So Σ a_k Re(−P_y′/P_y)(σ+ikt) = ∫u^{−σ}·8(1+cos(t log u))⁴ dψ ≥ 0.
- The error term is ≤ 128/(ηL) ≤ 128ε_f/η.
- eq:lp-341 is correct.

## Step 4 (04e:173–178): correct

- −P_y′/P_y(1+η) = ∫_{[1,y]} u^{−η} dS = y^{−η}S(y) + η∫_1^y S u^{−1−η} du.
- The tail η∫_y^∞(log u + 0.43)u^{−1−η} du equals y^{−η}(L + 0.43 + 1/η) ≥ y^{−η}S(y). So the whole is
  ≤ η∫_1^∞(log u + 0.43)u^{−1−η} du = 1/η + 0.43.
- Adding (ηL)⁻¹ ≤ 10⁻⁸/η, which holds because L ≥ 10⁸, gives eq:lp-pole.

## Defects

### F1 (FIXABLE): a true bound with the wrong justification

- **Where:** 04e-lp.tex:147–148, for the bounds displayed at 150–151.
- **Defect.** "Rankin's trick and (LP-a) give" does not support the T₀-tail terms 2y^{−η}/η and 2y^{−η}(L/η + 1/η²), because
  (LP-a) controls N − T₀ only on [X₀⁻, y].
- **Suggested fix.** Insert:

  > On (y,∞), dT₀ = dΨ(·,X₀) + (1−ρ_det+R′)du ≥ 0 (eq:target, eq:G1), and T₀(u) − u = E_rig(u) + R(u) with
  > |E_rig(u)| ≤ κX₀ + 2 + κu (eq:Erig) and |R(u)| ≤ 2u^θ log* u (Lemma T1). Partial summation gives
  > ∫_{(y,∞)} u^{−σ} dT₀ ≤ (1+3κ)y^{−η}/η and ∫_{(y,∞)} log u·u^{−σ} dT₀ ≤ (1+3κ)y^{−η}(log y/η + 1/η²). The N_y part uses
  > only dN_y ≥ 0 and u^{−η} ≤ y^{−η} for u > y. On [1,y], ∫u^{−σ}dN ≤ 1/η + 2.01 by (H_BS) (Lemma cm).

- **Impact:** none on any constant.

### C1 (COSMETIC): the source of (H_BS)

- **Where:** 04e:130, with the same pattern at 04a-setup.tex:133–135.
- **Defect.** The text says "(LP-a) and eq:T1 give (H_BS)". But eq:T1's bound C_{X₀}x^θ is useless near X₀, because
  C_{X₀} = 2∏_{p<X₀}(1 − p^{−θ})⁻¹ is about exp(X₀^{1/2}/Λ). (H_BS), with η₁, η₂ ≤ 10⁻³, needs the κ-form of eq:Erig.
- **Fix:** cite Lemma T1 (eq:Erig and the bound on |R|) in place of eq:T1.

### C2 (COSMETIC): an unneeded Rankin split

- **Where:** 04e:148–151.
- **Defect.** The split u^{−η} ≤ y^{−η/2}u^{−η/2} is not needed. u^{−η} ≤ y^{−η} for u > y already gives the stronger bounds
  y^{−η}P_y(1) and y^{−η}P_y(1)S(y). The stated bounds are valid, only weaker.
- **Fix (optional):** either use u^{−η} ≤ y^{−η}, or keep the split and say that it is not needed.

### C3 (COSMETIC): σ above 9/8

- **Where:** 04e:159–161.
- **Defect.** ∫u^{−σ}|dF| ≤ 10⁻² is derived only for σ ≤ 9/8, but "no zeros in σ ≥ 1+η_y" is claimed for every such σ, and
  Step 6 uses σ > 1.1.
- **Fix:** add "and for all larger σ, since ∫u^{−σ}|dF| is non-increasing in σ".

## The uses of Step 3 and eq:lp-transfer in Steps 6–10

None of them needs more than Step 3 provides, and their constants check.

- **Step 6 (04e:201–202).** "ζ^♯ ≠ 0 for σ > 1.1 by Step 3" is correct, given the monotonicity in C3.
- **Step 7, growth (04e:210–211).** |ζ^♯(z₀)| ≥ (1 − 10⁻²)/P_y(1+η) ≥ 0.495η, from P_y(σ) ≤ 2/η and |Δ/P_y| ≤ 10⁻². The range
  η_y ≤ η ≤ 10⁻³/Λ ≤ 1/8 is non-empty by eq:lp-yrange.
- **Step 7, the inequality (04e:226–227).** The dropped zero terms are ≥ 0, because there are no zeros in σ ≥ 1 + η_y.
  eq:lp-pole gives 35·0.43 = 15.05 and the 35(1 + 10⁻⁸) in N₀, and eq:lp-341 gives 128ε_f. All consistent.
- **Step 8, the anchor (04e:287–288).**
  - |log P_y(s₁)| ≤ ∫u^{−σ}dΠ = log P_y(σ) ≤ log(2/η_t), and |log(1+Δ/P_y)| ≤ −log 0.99 = 0.01005 ≤ 0.02.
  - η_t = 0.33769/(ΛY), so log(2/η_t) = log Λ + log Y + 1.78. Since Y ≥ 442 + 2 log Λ, 0.5Y − log Y ≥ log Λ + 221 − log Y,
    which is positive for every Y. So log(2/η_t) + 0.02 ≤ 0.5Y.
  - This needs η_t ≥ η_y, which holds for |t| ≤ T_y (the height constraint of Step 7).
- **Step 9 (04e:304–323).**
  - 𝔊 is the Mellin transform of (Π^♯ − Π₀)/u on Re s ≥ η_y, and Step 3 includes σ = 1 + η_y.
  - On that line, |𝔊| ≤ log(2/η_y) + 0.02 + O(1) = O(log log y).
  - v^{η_y} ≤ (log y)^{17} for v ≤ y.
  - y′ = v also satisfies log y′ ≥ 10⁸.
- **Step 10.**
  - c − 1 = 17 log Λ_p/Λ_p lies in [η_y, 1/8], since log log t/log t decreases and v ≤ y.
  - (B), above 1 + 2η_{T₁}: |𝔊₁| ≤ log(2/(σ−1)) + 0.02 + log(|s|/|s−1|) + π. Here |s| > |s−1|, and their ratio is ≈ 1 at
    |t| ≥ T₁ ≥ e⁴⁰. So this is ≤ log(1/(σ−1)) + 3.86 ≤ 2log(1/(σ−1)) + 4.
  - (B), below: the points with σ ≤ 1 + 2η + fδ are exactly those at distance ≤ r₁ from s₁.
  - (C): 2log(Λ_p/(17 log Λ_p)) + 4 ≤ 2 log Λ_p.

## The toy

**Set-up.**
- T₀ is the target of eq:target without R or Abs: the X₀-smooth integers plus the density 1 − ρ_det, with exact integrals of
  ρ_det.
- N is a synthetic Beurling system: the rational primes < X₀, plus a greedy rule that places a prime at n + U(0, H) whenever
  T₀(n) − N(n) ≥ 1/2. The full multiplicative closure is computed.
- ∫_{(y,∞)}u^{−s}dT₀ is computed exactly: the Euler product over p < X₀ minus partial sums, the linear part, and the
  closed-form ρ_det ramps.
- P_y, Δ and Δ′ are computed at σ = 1 + η for η ∈ {1/8, 0.06, 0.03, 0.015, 0.008} and t ∈ {0, 1, 3.7, 14.13, 50, 211, random}.

**Results.**
- **Runs.** X₀ = 50, H = 1, κ = 0.2, y = 10⁶: 1.0·10⁶ elements, 77.6k large primes, max|N − T₀|/√n = 0.199. X₀ = 100, H = 2,
  κ = 0.1: max|N − T₀|/√n = 0.212. Both are far inside u^{θ′}.
- **Step 2.** P_y(1) = 24.6, against e^{4.5} log y = 1244. max_z(∫dΠ/u − log log z) = 0.739 (at z = 3), against 4.5.
  S(y) = 13.18, against log y + 0.43 = 14.25.
- **All 11 displayed inequalities of Step 3 hold**, at all 35 points of each run:

| Inequality | Maximum of actual/bound |
|---|---|
| P_y(σ) ≤ 1/η + 6 + y^{−η/2}P_y(1) | 0.33 |
| \|Δ\| ≤ its bound | 0.42 |
| \|Δ′\| ≤ its bound | 0.49 |
| 1/P_y(σ) ≤ \|P_y(s)\| | 0.32 |
| \|P_y′/P_y\| ≤ S(y) | 0.94 (the tightest, at t = 0) |
| T₀ tail ≤ 2y^{−η}/η | 0.5001 |
| log-weighted T₀ tail ≤ 2y^{−η}(L/η + 1/η²) | 0.5001 |
| N_y tail ≤ y^{−η/2}P_y(1) | 0.36 |
| N_y tail ≤ y^{−η}P_y(1) (the sharper bound of C2) | 0.39 |
| log-weighted N_y tail ≤ y^{−η/2}P_y(1)S(y) | 0.61 |
| \|Δ/P_y\| ≤ \|Δ\|·P_y(σ) | 0.32 |

- **The T₀-tail ratio of 0.5001** means the tail is (1 + O(κ))·y^{−η}/η, exactly as derived in F1. The paper's factor 2 is
  pure slack.
- **The transfer itself fails at this scale, as expected.** Here log y = 13.8, far below 930, where η_y ≤ 1/8 first holds.
  max|Δ/P_y| is 0.074 at η = 1/8 and 4.65 at η = 0.008, and the dominant term is the T₀ tail times P_y(σ). This shows that
  the threshold scaling η_y = 17 log log y/log y is what makes the transfer work.

## Confidence and limitations

**Confidence: high.**
- Every bound of Steps 2–4 was re-derived from its source, and the arithmetic and the worst cases were checked in arb.
- The exact toy confirms each inequality, and the size of the T₀ tail.
- Nothing in Steps 6–10 relies on more than Step 3 provides.

**Limitations.**
- (H_BS) on [1, y] was taken as given, apart from the remark C1 on its source. Lemma cm, Lemma ZBlow, eq:Rhat and the rest of
  Step 7's Landau constant were not re-audited.
- The toy T₀ has no oscillation R and no absorbed set, and the toy N is synthetic rather than the queue construction.
- The worst-case search used a 400-point log grid in η together with the monotonicity argument. It is not a certified
  interval enclosure in η.

**Files.** Copies of the scripts (worst.py, step2_const.py, toy_transfer.py, misc.py) are in `review/recheck/r10/`.

## Re-check of #60, the fixes of the R10 findings

**Verdict: CORRECT.** 0 BLOCKING, 0 FIXABLE, 2 COSMETIC. F1, C1, C2 and C3 are all resolved. The check was read-only, on the
working tree against 801a263.

**1. The partial summation for the T₀ tail.** Write T₀ = u + G, with G = E_rig + R and |G| ≤ c₀ + κu + 2u^θ log*u, where
c₀ = κX₀ + 2.
- **f = u^{−σ}.** The u part gives exactly y^{−η}/η. The κu part gives κ(1+2η)·y^{−η}/η, the c₀ part (2c₀η/y)·y^{−η}/η, and
  the R part ≤ 6.5η·y^{θ−1}log y·y^{−η}/η.
- **f = u^{−σ}log u**, which is decreasing for u > e^{1/σ}, so ∫_y^∞|f′| = f(y). The κu part is
  κ(2yf(y) + ∫f) ≤ κ(1+2η)·main, because 2 log y/(log y/η + 1/η²) ≤ 2η. The c₀ part is ≤ (2c₀η/y)·main.
- **The total relative excess** is ≤ 1.5κ + X₀^{−0.48} ≤ 3κ, so the bound really is (1+3κ), not merely 2.

**2. The [1,y] bound.** ∫_{[1,y]} u^{−σ}dN ≤ ζ(σ) + η₁ + 0.78η₁ ≤ 1/η + 1.002 ≤ 1/η + 2.01.

**3. eq:lp-transfer under the new bounds**, computed in arb:

| Claim | Worst ratio | Old ratio |
|---|---|---|
| P_y(σ) ≤ 2/η | 0.6256, at η = 1/8 (P_y(σ) ≤ 10.01 against 16) | 0.875 |
| \|Δ/P_y\| ≤ 10⁻² | 2.9·10⁻¹¹⁹ | 2.9·10⁻⁵¹ |
| \|d/ds log(1+Δ/P_y)\| ≤ (η log y)⁻¹ | 1.8·10⁻¹¹⁰ | 1.8·10⁻⁴² |

The ratios are monotone in η on a 2001-point grid, and all three hold for every log y ≥ 930.

**4. Downstream uses.** No use of the old forms remains in Theorem lp or its consumers. CORRECTIONS row 57 and R4.md:2549
mention the old form, but only as records of earlier states.

**5. The toy, rerun.** Every new displayed bound holds at all points:

| Bound | Max actual/bound |
|---|---|
| P_y(σ) bound | 0.558 |
| \|Δ\| | 0.429 |
| \|Δ′\| | 0.492 |
| first inequality of the [1,y] chain | 0.9998 (tight, as expected) |
| T₀ tails, with the exact excess factor | 0.831–0.908 |
| N_y tails | 0.386 and 0.651 |

**6. C1 and C3.** Correct. 04a's (H_BS) text cites eq:Erig and Lemma T1.

**7. Row 60, the counts and the build.** All correct. The build has 0 warnings and no overfull box in 04e.

**Cosmetic items, both fixed by the lead:**
- **N1.** The row for Theorem lp in the dependency table of 01-setup now also lists Lemma G1, which gives dT₀ ≥ 0.
- **N2.** The README and paper-recheck.md now say where #60 was checked.
