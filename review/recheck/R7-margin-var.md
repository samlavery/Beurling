# R7: Lemma margin(b) Step 3 and (d)(iii), the large-range variation estimate (correction #47)

The checker was margin-var-check, a fresh AI agent, working on the snapshot `874bf72`. It was not allowed to write files, so
the lead saved its messages here. Its scripts were in `/tmp/rhscratch/margin-var-check/`, which is temporary.

## Verdict: CORRECT WITH FIXES

- **The bounds hold.** Every large-range bound holds as stated:
  - |μ₀′| ≤ 2κ(log u)³;
  - |(K′_ℚ − K_pt)g| ≤ 4κ(log u)³;
  - log x·|ρ_edge − g| ≤ 4.1κ(log x)⁵ ≤ X₀^{−0.34};
  - the piecewise constants 0.82, 0.97 and 0.399, and c′ = 0.15.
- **One FIXABLE defect (F1).** Step 3 bounds the sum over the other variables (Σ1/m_j) with a one-system multiset argument.
  In the variable-by-variable replacement, the intermediate sums mix realised and rational primes, and that argument does
  not cover them. The bound is true up to a factor 1 + O(1/Λ), which the constants absorb. Both (b) and (d)(iii) inherit the
  gap.
- **Four COSMETIC items.**
- **Toys.** An exact realised-versus-rational toy shows no failure. The identities hold to 10⁻¹⁶, and each step of the bound
  chain holds with the stated tightness.

## 1. Operators and identities

**The operators, written out.** The paper never defines K_ℚ and K′_ℚ by a formula (see C1).
- **K_pt.** K_pt h(y) = Σ_{w∈𝒩, w≥2} w⁻¹·1[τ_w < y/w]·1[y/w ≥ X₀⁻]·h(y/w).
  - Here τ_w is the largest decision time t(p) over p | w, with t(p) = p for rational p < X₀ and t(p) = slot for jittered
    primes.
  - Its cut-off is X₀⁻, so it never reads (X₀/(1+κ), X₀⁻).
  - Every function it is applied to (ρ^sh, MA·1_{≥X₀}, f₀1, f₁1, g) vanishes on [X₀⁻, X₀), so the cut-off is effectively X₀
    (06:126–128).
- **K_ℚ** (06:109–111, eq:ratid) is the rational latest-prime operator.
  - Its m′-component at q = x/m′ is m′⁻¹·MA_{κq}[primes ≥ max(P⁺(m′), X₀)](q).
  - It has no cut-off, so it reads the edge (X₀/(1+κ), X₀); that reading is exactly μ_edge.
  - Its sharp form, Σ_m m⁻¹·1[P⁺(m) ≤ y/m]·h(y/m), differs from this only by the partial windows of Lemma blin(3), which go
    into μ₀.
- **K′_ℚ.** K′_ℚ h(y) = Σ_{m∈ℕ, m≥2} m⁻¹·1[P⁺(m) < y/m]·1[y/m ≥ X₀]·h(y/m). The filter must be strict, as in Lemma M. That is
  needed for (d)(iii)'s coefficients, and for "agrees with K_pt below X₀⁻" to hold at every point (C1).

**Checks.**
- **eq:shdecomp.** The identity (1+K_ℚ)MA = (1+K_pt)(MA·1_{≥X₀}) + (K_ℚ−K_pt)(MA·1_{≥X₀}) + μ_edge holds on [X₀⁻, ∞), and both
  sides vanish on [X₀⁻, X₀).
- **Resolvent identity.** (1+K_pt)(ρ_edge − g) = μ_edge − (1+K_pt)g = (K′_ℚ − K_pt)g.
  - Both operators are Volterra-type: each cofactor at least halves the scale.
  - g is supported on (2X₀/(1+κ), ∞), so the two cut-offs never matter.
- **Agreement below X₀⁻.**
  - Cofactors w < X₀⁻ are rational integers in both systems, with τ_w = P⁺(w).
  - A cofactor that differs has w ≥ X₀⁻ and needs u/w > 2X₀/(1+κ). So D := (K′_ℚ − K_pt)g = 0 for u < 2X₀X₀⁻/(1+κ).
  - In the toy, D ≡ 0 exactly below that point in all 7 runs.

## 2. Step 3 of the proof of (b), re-derived

**One replacement.** For fixed other variables, the summand is G(p) = f₀(u/(m_jp))/(m_jp) on an interval [a, b].
- Since |qf₀′| ≤ f₀/log q ≤ f₀/Λ, we get |(G/log)′| ≤ (1 + 1/log p + 1/Λ)·G/(p log p) ≤ 1.1·G/(p log p).
- Abel summation against Δ_θ, with |Δ_ψ(t)| ≤ 5κt log²t, gives two parts:
  - boundary terms ≤ 2·5κ·f₀·log b/m_j;
  - integral ≤ 5.5κ(f₀/m_j)·∫_a^b (log t/t) dt ≤ 2.75κ·f₀·log²b/m_j.
- With f₀ ≤ 1/Λ the total is ≤ (2.75 + 10/log u)·κ log²u/(m_jΛ), inside the paper's 4.
- **Step 2 checks.** |h| ≤ 4κt log t + 2κt + κt·X₀^{−0.1} ≤ 5κt log t. Möbius inversion over v ≤ t/X₀⁻ gives the factor
  log t − Λ + 1 < log t.

**Summation (06:239–241).**
- Σ_{d∈𝒟} 1/d ≤ 1.01e^γΛ.
- Then Σ_k (k−1)·4κ(log²u/Λ)·1.01e^γΛ·ℓ^{k−2}/(k−2)! = 4.04e^γκ log²u·(1+ℓ_u)e^{ℓ_u}. Here 4·1.01·e^γ = 7.1955 (arb).
- With e^{ℓ_u} ≤ (log u/Λ)e^{2.2/Λ}, this is ≤ 7.4κ(log u)³(1 + log log u)/Λ.

**Range of validity.** For log log u ≤ Λ/8, 7.4(1 + Λ/8)/Λ = 0.925 ≤ 1. Also rb ≤ e^{−0.8Λ}, because r ≤ e^{Λ/8}. Range (A) has
log log x ≤ Λ/100.

**"The rest."** It is negligible. The checker bounded the decision-order mismatch directly, not by the paper's "H(q)/(κq)
per component" (see C3):
- Value order and decision order disagree only when u/w lies within H/2 of the top prime P. Even when two large primes swap
  order, τ_w stays in [P − H/2, P + H/2].
- That puts P in an interval of length about H around √(u/w′). Such an interval holds at most 2H + 2 realised primes, because
  slots are ≥ 1 − 10⁻⁸ apart and values lie within H/2 of slots.
- Summing over w′, using that H(v)/v is decreasing and Σ_{w′} 1/w′ ≤ log u + 1, gives ≤ 2.02(H(X₀)+1)(log u + 1)/(ΛX₀). This is
  ≪ 10⁻³κ(log u)³, and the same count works for f₀ and for g.
- The partial windows (Lemma blin(3)) cost ≲ κ log u/Λ². Prime powers cost a relative O(X₀^{−1/2}). Both are negligible.

### F1 (FIXABLE): the replacement step mixes the two systems, and the multiset argument does not cover it

**Where.** 06-base-range.tex:223 ("Replace the large-prime measure one variable at a time") and 06:231–238 (the Σ1/m_j bound
and its multiset justification). (d)(iii) inherits it at 06:311–316.

**What goes wrong.**
- Replacing the variables one at a time, in the order p₂ ≥ … ≥ p_k, makes each intermediate sum mixed. The variables above
  p_j are realised and those below are rational (or the reverse), and the two groups are ordered across.
- The justification at 06:234–238 covers only a multiset drawn from one system, with Σa_p ≤ ℓ_u.
- Dropping the cross-ordering gives Σ_j ℓ^{j−2}ℓ^{k−j}/((j−2)!(k−j)!) = (2ℓ)^{k−2}/(k−2)!. That turns e^{ℓ_u} ≈ log u/Λ into
  (log u/Λ)², so |μ₀| ≲ 7.4κ(log u)⁴(1 + log log u)/Λ². This is not ≤ 2κ(log u)³ on range (A), where log u reaches
  X₀^{1/100} ≫ Λ². Taking a_p over the union of both systems' primes (Σa_p ≤ 2ℓ_u) has the same loss.
- With the cross-ordering kept, the one-system bound is not literally true either. Toy T6b uses two systems with ℓ_A = ℓ_B and
  sup|L_A − L_B| = 0.024–0.08. There the mixed sum exceeds (ℓ + (r+s)b)^{r+s}/(r+s)! by 1.6% to 15.8%, for
  (r,s) ∈ {(1,1), (2,1), (1,2), (2,2)}.

**Why the conclusions survive.**
- Let λ(t) := log(log t/log X₀⁻) and c := 2.2/Λ (Lemma cm(iv) holds in each system), and put c′ := c + kb.
- Condition on y, the maximum of the lower group:
  - the upper group is bounded by (λ(u) − λ(y) + c′)^r/r!;
  - the rest of the lower group by (λ(y) + c′)^{s−1}/(s−1)!.
- Integrate F(λ(y)) against dL_B = dλ + dE with |E| ≤ c. F is log-concave, so TV(F) ≤ 2·max F.
- The Beta integral, together with max F ≤ (ℓ̃+2c′)^{r+s−1}/(r+s−1)! (a binomial probability is ≤ 1), gives
  S_mixed(r,s) ≤ (ℓ̃+2c′)^{k−2}/(k−2)! + 4c(ℓ̃+2c′)^{k−3}/(k−3)!.
- Summed over j and k, this multiplies (1+ℓ_u)e^{ℓ_u} by at most 1 + O(1/Λ).
- The constants absorb that factor:
  - in (b), 4·1.01·e^γ = 7.196 against the stated 7.4;
  - in (d)(iii), 17·1.01·e^γ·(1/Λ + 1/8) = 3.8226 against 4, unchanged at that precision by the factor 1 + 10/Λ.

**Preferred fix: symmetric telescoping.** Replace 06:223–241 by:

> Write the sum over multisets of k−1 large primes as 1/(k−1)! times the sum over ordered (k−1)-tuples, plus a diagonal term
> (some large prime repeated), whose total weight is ≤ 1.01e^γΛ·e^{ℓ_u}/(X₀⁻Λ) in each system. Telescope the product measure:
> the j-th intermediate sum has its first j−1 variables realised and its last k−1−j rational, with no ordering between them.
> For fixed other variables, the admissible set of the j-th variable p is an interval [X₀⁻, b]. With M′ the largest other
> variable, the filter max(p, M′)·m_jp ≤ u reads p ≤ √(u/m_j) if M′²m_j ≤ u and p ≤ u/(M′m_j) otherwise, and u/(m_jp) ≥ X₀
> reads p ≤ u/(X₀m_j). The other variables range over a product set, so Σ1/m_j ≤ 1.01e^γΛ·ℓ_u^{k−2}. The k−1 replacements
> against the 1/(k−1)! give 4κ(log²u/Λ)·1.01e^γΛ·ℓ_u^{k−2}/(k−2)! for each k, and the total is
> ≤ 4.1e^γκ log²u·e^{ℓ_u} ≤ 7.4κ(log u)³/Λ.

This is better than the stated bound: the factor (1+ℓ_u) disappears. In (d)(iii), 17 in place of 4 then gives
≤ 31κ(log u)³/Λ.

**Alternative fix.** Keep the ordered telescoping, and add the conditioning and Beta-integral argument above, stating the
factor 1 + O(1/Λ).

## 3. The adaptation in (d)(iii)

**The coefficient formula is correct.** g(x) = Σ_N (−μ(N)/(κx))·C_N(x), where C_N(x) counts the window primes
p ∈ [X₀, (1+κ)x/N] with s_p > 1 and χ_{ℓ_p}(x) = 1.
- C_N is non-decreasing in x. Primes enter at the fixed left end X₀, because x/N < X₀; χ_ℓ switches on monotonically; and s_p
  does not depend on x.
- Every N-term has sign −μ(N).

**The bounds on |g| check.**
- |N-term| ≤ MA(x/N)/N.
- The N with x/N on the edge lie in (x/X₀, (1+κ)x/X₀). There are ≤ κx/X₀ + 1 of them, each with 1/N < X₀/x, so
  Σ1/N ≤ κ + X₀/x.
- This gives |g| ≤ 1.0001(κ + X₀/x)/Λ, and |g| ≤ 0.51/Λ because x > 2X₀/(1+κ).
- At x = X₀^{1.01}/2, |g| log x ≤ 2.0202X₀^{−0.01} ≤ 3X₀^{−0.01} (arb).

**Variation of one N-term.** On (NX₀/(1+κ), NX₀), the N-term is −μ(N)C(x)/(κx), with C a non-decreasing step function.
- The rise is ≤ C_max[(1+κ)/(κNX₀) + 1/(NX₀)] = C_max(1+2κ)/(κNX₀).
- The drop to 0 at NX₀ is ≤ C_max/(κNX₀).
- With C_max ≤ π[X₀, (1+κ)X₀] ≤ 1.0001κX₀/Λ (Huxley at X₀), the total is ≤ 2.0002(1+κ)/(NΛ) ≤ 3.1/(NΛ).
- The term starts at 0: X₀ is even, so no prime sits at the left end.

**Variation on [α, β].** TV is subadditive. The N-terms meeting [α, β] have N ∈ (α/X₀, (1+κ)β/X₀), N ≥ 2, so
Σ1/N ≤ log(β/α) + κ + 1/2. Hence TV(g; [α, β]) ≤ (3.1/Λ)(log(β/α) + 1).

**Only |g| and its variation are needed, so a non-smooth g is fine.** "Integration by parts" is really discrete Abel
summation over the merged prime points t_i:
- Σ φ(t_i)·ΔΔ_θ(t_i) = boundary terms − Σ Δ_θ(t_i)(φ(t_{i+1}) − φ(t_i)), with φ = g̃·h, g̃(t) = g(u/(m_jt)) and
  h = 1/(m_j t log t).
- The product rule splits each difference into g̃·Δh + h(t_i)·Δg̃.
- |Δ_θ(t)|·h(t) ≤ 5κ log b/m_j. So no smoothness of g is used, only its total variation on [u/(m_jb), u/(m_ja)], where
  β/α = b/a.

**The constant 17, reconstructed.**
- Boundary: 2·5κ·0.51·log b/(Λm_j) = 5.1κ log b/(Λm_j).
- Smooth part: 5.5·0.51/2 = 1.40, times κ(log²b + 2 log b)/(Λm_j).
- Variation: 5κ log b·(3.1/Λ)(log(b/a) + 1)/m_j ≤ 15.5κ log²b/(Λm_j), since log a ≥ 1.
- Total ≤ (16.90 + 7.65/log u)·κ log²u/(Λm_j) ≤ 17 (arb).

**The sum over cofactors.** 17·1.01·e^γ·(1/Λ + 1/8) = 3.8226 ≤ 4 (arb). So |D(u)| ≤ 4κ(log u)³ for log log u ≤ Λ/8, with about
4% to spare. This still holds after F1's factor 1 + 10/Λ.

**The rest, for g.** The decision-order mismatch is bounded by the same count as in §2, with sup|g| ≤ 0.51/Λ. There are no
partial windows, since K′_ℚ is sharp, and prime powers are negligible.

## 4. The final chain and the piecewise constants

**The ρ_edge − g step.** Lemma M gives Σ|c_n|/n ≤ log x + 1, so log x·|ρ_edge − g| ≤ 4κ(log x)⁴(log x + 1) ≤ 4.1κ(log x)⁵.

**Exponents.** κ ≤ X₀^{−0.3967}. At log x = X₀^{1/100}, 4.1κ(log x)⁵ ≤ 4.1X₀^{−0.3467} ≤ X₀^{−0.34}, because log 4.1 ≤ 0.0067Λ.
So |ρ_edge| log x ≤ 3X₀^{−0.01} + X₀^{−0.34} on [X₀^{1.01}/2, X_sw].

**Beyond log x = X₀^{1/100}.** The edge term is not controlled there, and it does not need to be.
- Range (B) of Prop g1 (04f-bridge.tex:188–278) does not decompose ρ^sh, and does not use Lemma margin(b)–(d).
- It bounds ρ^sh(x) directly, through the J-average of ρ̃ (local prime number theorem), Prop BR, and pointwise-versus-average.
- What range (A) calls the edge appears there only through T′'s jump at X₀ (the item n ∈ [y/X₀, x/X₀]) and the smooth change
  of ρ_det. Step 3 of range (B) bounds both.
- (d)(iii)'s bound would in fact fail for log x ≳ X₀^{0.011}, so it is right that range (B) does not use it.

**The piecewise constants.**
- Range (A), on [X₀+H, X₀^{1.01}]: 0.99 − 0.167 − 6·10⁻⁴ = 0.8224, then minus X₀^{−0.34} and e^{−80}, gives ≥ 0.822.
- On [X₀^{1.01}/2, X_sw]: 0.99 − 6·10⁻⁴ − 2X₀^{−0.34} − 3X₀^{−0.01} − e^{−80} ≥ 0.989.
- On [X_sw, ∞), range (B): 0.97 − o(1).
- Together these cover x ≥ X₀ + H.

**The overlap [X₀^{1.01}/2, X₀^{1.01}].** Both pieces apply there, and each consumer reads the right one.
- Thm g2 (04g-margin.tex:13, 25–27) uses 0.97 only for x ≥ X₀^{1.01}, where W_x ⊂ [X₀^{1.01}/2, ∞), and 0.82 on
  [2X₀, X₀^{1.01}).
- Prop pointwise(b) (04g:55–56), on [2X₀, X₀^{1.01}]: 0.822 − 0.4209 − 10⁻¹² = 0.4011 ≥ 0.399. The bound j_{X₀} ≤ 0.4209 holds
  exactly for x ≤ X₀e^{0.01Λ} = X₀^{1.01}.
- Prop pointwise(a), for t ≥ X₀^{1.01}: j_{X₀} ≤ e^{−0.0009Λ} and V_{X₀} ≤ e^{−0.0015Λ}, giving 0.96 − o(1) ≥ 0.959.
- Prop pointwise(c), on [X₀, 2X₀): 0.73, without ρ^sh.

**Cor r1** (04g:248–249). m log t ≥ 0.399 on [X₀, ∞), and 0.399 ≥ 1.01c′ = 0.1515, so c′ = 0.15 and K_d = 3 stand.

## 5. The toy (exact, pure Python)

**Systems.** The rational system is compared with a synthetic realised system: the rational primes ≥ X₀, jittered by
U(−H/2, H/2), with slot = the rational prime. There are four variants:
- jitter only;
- add: extra primes, ε = 0.15;
- del: deletions, ε = 0.15;
- drift: Poisson extras at rate ε per unit length, modelling the +(κ/2)Ψ drift.

**Sizes.**
- Toy A: X₀ = 100, κ = 0.2, H = 2, u ≤ 4·10⁶. Cofactors with two large primes occur from u ≈ 10⁶ on.
- Toy B: X₀ = 1000, κ = 0.05, H = 4, u ≤ 3·10⁷.

**Toy constants that replace the Λ-dependent ones.**
- M_e := sup_edge MA (0.2655 in toy A, 0.1602 in toy B) replaces 1.0001/Λ.
- G∞ := M_e(κ + (1+κ)/2) replaces 0.51/Λ.
- T₁ := 3.1M_e/1.0001 replaces 3.1/Λ.
- C_Δ := sup|Δ_θ|/(t log²t), measured, replaces 5κ.

### Results

**T1: g.** The coefficient formula agrees with Lemma M (rational), and with the direct Neumann recursion
g = μ_edge − K′_ℚg, which does not use Lemma M.
- Over 900 points the maximum difference is 7·10⁻¹⁷.
- On v ∈ [10⁶, 2.5·10⁶], where N has two primes ≥ X₀, it is 1·10⁻¹⁶ (60 points, Lemma M) and 2.4·10⁻¹⁴ (8 points, Neumann).

**T2: variation.**
- max N·TV(N-term)/M_e is 2.12 at κ = 0.2 and 2.03 at κ = 0.1. The derived bound is 2 + 2κ, and the paper's is 3.10. The rise
  is ≤ 1.18 (bound 1 + 2κ) and the drop ≤ 0.96 (bound 1).
- TV(g; [α, β]) / (T₁(log(β/α) + 1)) ≤ 0.33 on 9 intervals.
- sup|g| / (M_e(κ + X₀/x)) ≤ 0.68 and 0.81 (3000 points each).

**T3: identities.**
- Lemma M with decision order (slots) in the realised system agrees with the direct recursion: 6.3k–11.6k coefficients per
  variant, including elements with two large primes, and 0 mismatches.
- D ≡ 0 below 2X₀X₀⁻/(1+κ), exactly, in all 7 runs.
- |ρ_edge − g − (1+K_pt)⁻¹D| ≤ 1.0·10⁻¹⁶ (toy A) and ≤ 1.6·10⁻¹⁷ (toy B).
- sup|D| on the grid ranges from 6.3·10⁻⁴ (jitter) to 4.4·10⁻³ (drift) in toy A, and from 4.9·10⁻⁵ to 1.2·10⁻⁴ in toy B.

**T4: the Step 3 chain.**
- The telescoping identity (k = 2, and the k = 3 ordered hybrids) equals −D_val exactly, at 205 values of u.
- The chain |D_val| ≤ exact Abel bound ≤ paper-form bound ≤ closed form holds everywhere:
  - |D_val|/Abel ≤ 1.00, attained at small u, where a single term contributes;
  - Abel/paper-form ≤ 0.046–0.125;
  - paper-form/closed ≤ 0.007–0.016.
- Example: toy A drift at u = 2.64·10⁶ gives |D_val| = 2.9·10⁻³, Abel 0.148, paper-form 1.56, closed form 241.

**T5: the Lemma M step.** |ρ_edge − g| ≤ Σ|c_n||D(x/n)|/n, with ratio ≤ 1.000, and that sum is
≤ (0.11 to 0.19)·(log x + 1)·sup|D|.

**T6: mixed hybrid sums (F1).** For the toy systems, the mixed ordered sums are ≤ 0.82 of the one-system bound, but only
because ℓ_A ≠ ℓ_B there. The adversarial version T6b, with ℓ_A = ℓ_B, exceeds the bound, with ratio 1.016–1.158.

### Where the bounds are tight
- The Abel step is tight.
- The paper's simplification costs a factor of 8 or more.
- The closed form (Σ over all d of 1/d, times (1+ℓ)e^ℓ) costs another factor of 60–150.

### Caveats
- In the jitter variant, the decision-order part is the whole of D (6.3·10⁻⁴). That is only because H/X₀ = 0.02 in the toy.
- The toys run with Λ ≈ 4.6–6.9, where log log u ≤ Λ/8 fails. So they were compared against the unsimplified closed form, not
  against 4κ(log u)³.

## Defects

**F1 (FIXABLE).** The replacement step mixes the two systems, and the one-system multiset argument does not cover it. See §2.

**C1 (COSMETIC).** 06-base-range.tex:109–111 and 291.
- **Defect.** K_ℚ and K′_ℚ are never given by a formula. Agreement with K_pt below X₀⁻ at every point needs K′_ℚ's filter to be
  strict, as in Lemma M.
- **Fix.** Display K′_ℚ h(y) := Σ_{m∈ℕ, m≥2} m⁻¹·1[P⁺(m) < y/m]·1[y/m ≥ X₀]·h(y/m). Give K_ℚ in component form,
  m′⁻¹·MA_{κq}[primes ≥ max(P⁺(m′), X₀)](q) at q = x/m′.

**C2 (COSMETIC).** 06:312–315.
- **Defect.** "Integration by parts uses its variation" is really discrete Abel summation over the merged prime points, and the
  constant 17 is not broken down.
- **Fix.** Say "Abel summation over the merged prime points, with |Δ_θ(t)|/(m_j t log t) ≤ 5κ log b/m_j taken out as a
  supremum", and add the breakdown 5.1 log b + 1.40(log²b + 2 log b) + 15.5 log²b ≤ 17 log²u.

**C3 (COSMETIC).** 06:248.
- **Defect.** "The decision-order mismatch, H(q)/(κq) per component" is not the natural quantity, although the conclusion
  holds.
- **Fix.** Use the direct count, ≤ 2.02(H(X₀)+1)(log u + 1)/(ΛX₀) times sup|h|, which applies to f₀ and to g alike.

**C4 (COSMETIC).** 06:294–299 against 06:232, and CORRECTIONS-vs-v3.md:54.
- **Defect.** The letter ℓ (the part of N above p) clashes with ℓ_u (Σ1/p). The log's "edge sum ≤ X₀^{−0.01}/Λ" holds only
  for x ≥ X₀^{1.01}, up to the factor 1.0001 and a +κ/Λ term; the paper's 3X₀^{−0.01} at 06:305 is right.
- **Fix.** Rename ℓ to N_>, and align the log text with 06:305.

**Counts:** 0 BLOCKING, 1 FIXABLE (F1), 4 COSMETIC (C1–C4).

## Confidence and limitations

**Confidence.** The checker has high confidence that (b) Step 3 and (d)(iii) are correct apart from F1, and that F1 changes
no stated constant or conclusion.
- Every constant was re-derived by hand, and the arithmetic checked in arb (`out/consts.txt`).
- The exact toys found no other discrepancy.

**Limitations.**
- Step 1 (|Δ| ≤ δ) was taken as given. Step 2 was re-derived from it.
- Range (B) of Prop g1 was checked only for its independence from (d).
- The decision-order mismatch was checked by the checker's own count, not by the paper's formula.
- The toys run with Λ ≈ 4.6–6.9, where log log u ≤ Λ/8 fails. So the last simplification, 7.4(1 + log log u)/Λ ≤ 1, was
  checked only by hand.
- The toy realised systems are synthetic perturbations, not the greedy construction.
- R4 §§16–17 did not examine the mixed sums, so F1 is new.

**Files.** The scripts and outputs are in `review/recheck/margin-var/`. The scripts are toy_common.py, t1_g_validate.py,
t1b.py, t2_tv.py, t3_realised.py, t4_bounds.py, t34_toyB.py, t5_lemmaM_step.py, t6_mixed.py, t6b_adversarial.py and
consts.py; the outputs are in out/.
