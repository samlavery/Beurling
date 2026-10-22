# Referee report A on `beurling-greedy-v2.md` (second pass)

Referee: beurling-referee (author of `beurling-greedy-referee.md` and Addenda A/B), 2026-10-20.
Scope: v2 (890 lines) together with the proofs it cites: `gap-G2R.md` §§1–2, 8–10;
`gap-localPNT.md` §§2–6.7; `gap-G3.md`; `revision-plan.md` §A–§L. I read the cited proofs, not
v2's summaries of them. Scratch work: `/tmp/rhscratch/referee2/`.

This file was written section by section; the verdict (§0) was written last.

## §0 Verdict and prioritised blockers (written last)

**Verdict: v2 does not establish Theorem A, even modulo the items it lists as open** (R1′-int,
R1′-echo, CL and SM as [S], and the soft-rule analysis). Beyond those it has one more
**fatal-as-written** defect and several serious ones.

**What v2 gets right.** v2 is a large improvement on v1, and several of its new pieces are correct
and valuable:
- **LP**, a local Landau PNT. Positivity is imported from the finite Euler product, and smoothing to
  the left keeps the argument inside [1, y]. I checked Steps 1–6. This closes my first report's
  item 1.
- **Lemma M**, c_n = μχ_x for every sharp filter. Checked.
- **Lemma B**, the scalar form.
- **The TC excess identity.** Exact.
- **CL's design.** It is queue-independent.
- **The integer-cofactor reference ρ_ref**, which closes item 2.
- **§2 under the Euler-product base factor.**
- **The §7 scope statements.**

**Prioritised blockers for Theorem A.**
1. **[New, top] G2-R / NV / BR / (6.1): the sup-norm route diverges (§1).**
   - The noise at scale u is set by the local H(u) and is fixed once u has been processed.
     Multiplied by (1 + log x)^{2K+1} it diverges as x → ∞.
   - The route is valid only for log x ≲ (log X₀)^{1.18}, far below x₁.
   - No absolute-value bound can fix this. A weighted repair (§6) looks feasible: Lemma M plus a
     Saias-type density of the support plus per-scale noise bounds. It would even restore polylog H.
     It is not written.
   - Until then G2-R, BR, G1′ and R1′-hi are **open**, and "Addendum B is moot" is false.
2. **R1′-int** (acknowledged open).
   - Of the five candidates, S(ε) and a randomised base are the most likely to work; B-lin is a
     solid third. D3+Cramér and Huxley-with-switch should be dropped (§5).
   - S(ε) additionally needs telescoping for all dilations m (only m = 2 is done) and the
     soft-rule bookkeeping.
3. **Lemma B′ in operator form (§3c).**
   - Its key identity b_d = Σ_e (A − κ_{d,e})c_e is false: the correct form has (M − A) on every
     pair, so the layer descent fails on rough inputs.
   - It is not needed if the §6 route (sharp inverse plus perturbative Δ) is used.
4. **NV step 2 at large scales (§3b(1)).** H(u) > X₀L^{−6} at every designed-zero scale, so the
   increment bound X_q ≤ 2M₁ for H-windows fails for latest primes q < H(u)L⁶. Needs an SM-type
   truncation.
5. **CL shape counting and Lemma SM are [S].** SM is needed at every designed-zero scale (Regime II).
6. **Minor.**
   - Z-estimate exponent (§3h).
   - ρ_det ≤ 1 + u^{−θ_b} (§3f).
   - Genericity of T.
   - The §7.3 Landau zero-free-region citation.
   - Diamond's "N = x + O(1) with zeros off the critical line" remark, which bears on novelty (§4).

**If blockers 1, 3 and 4 are repaired as suggested,** the open set for Theorem A is: R1′-int via
one of the candidates, the [S] bookkeeping of CL and SM, the Saias-type lemma, and the soft-rule
analysis if S(ε) is chosen.

---

## §1 The most important new finding: the sup-norm G2-R route fails at small scales

**Where.**
- v2 §3.4–§3.5: rows NV and G2-R in the §0.2 table.
- `gap-G2R.md` §8.0, eq. (8.1), and §8.1–§8.2.
- The same quantity appears as ν_* := sup_{u≤x/2}|ν(u)| in `gap-localPNT.md` (6.1), so it also
  feeds G1′ and LP⁺.
- The bridge BR (v2 §3.6) uses it too, through C(log⁴x/√H + √(λ/H)).

**The claim.** Iterating e = −Ke − ν gives
(Ke)(x) = Σ_{n≥2} c_n(x) ν(x/n)/n. Hence

  |(Ke)(x)| ≤ (Σ_n |c_n|/n) · sup_{u≤x/2}|ν(u)| ≤ (1 + log x)^{2K+1}·√(4M₁λ/H)(1 + o(1)).

The draft then requires this to be ≤ c′/(4 log x), "once log H ≥ 5.77ℓ² + 12ℓ + 13".

**What is wrong.** The inequality is correct. The way it is evaluated is not. The sup runs over
every scale u ∈ [X₀, x/2]. At scale u the noise is set by the jitter width *at that scale*:
- ν(u) = (Mart(W_u) − ΔQ(W_u) + edge)/H(u), where W_u is the H(u)-window.
- |Mart(W_u)| ≍ √(H(u)) typically, because the predictable variance is ≍ M₁·H(u)·(jittered
  density).
- So |ν(u)| ≍ (jittered density)^{1/2}/√H(u). On [3X₀, X₀²] this is ≍ 1/√H(X₀).
- `gap-G2R.md` itself says this at line 57: "Var ν(x/n) ≈ 1/H(x/n)".

This small-scale noise is a fixed random quantity, sitting at scales below x for every x. It does
not shrink as x grows. Meanwhile the factor it is multiplied by grows without bound:
log x·(1 + log x)^{2K+1}·√λ = exp(2.89ℓ² + O(ℓ)).

Therefore

  log x · sup_{u≤x/2}|ν(u)| · (1 + log x)^{2K+1} → ∞  as x → ∞ with X₀ fixed.

The displayed condition holds only while 8ℓ(X₀)² ≳ 5.77ℓ(x)². That means ℓ(x) ≲ 1.18ℓ(X₀), i.e.
log x ≲ (log X₀)^{1.18}.

**Size of the failure.**
- With log X₀ ≈ 10⁹ we have H(X₀) = e^{8·20.7²} ≈ e^{3430}. The bound is then valid only up to
  log x ≈ 4·10¹⁰.
- The designed zeros live at log x_k ≥ log x₁ ≥ X₀² = e^{2·10⁹}.
- At that scale the bound is about e^{10¹⁹}·e^{−1715}.

So rows G2-R, BR, NV-as-used, and G1′ (through (6.1)) are **not proved anywhere in the range where
Theorem A needs them.**

**No absolute-value bound can repair this; any repair needs cancellation.**
- Lemma M (sharp filter) gives c_n(x) = μ(n)χ_x(n). For n ≈ x/X₀ we have χ_x(n) = 1 on a positive
  proportion of squarefree n: those whose least prime factor is < X₀ and whose P⁺(n)² < x. So
  Σ_{n∈[x/2X₀, x/X₀]}|c_n|/n ≍ 1.
- Hence Σ_n |c_n||ν(x/n)|/n ≳ 1/√H(X₀) for every x.
- Making H grow faster does not help. H(u) ≤ u^η is forced by the lag row, so the small-scale
  noise always contributes a fixed amount, while the target c′/(4 log x) → 0.

**What does hold, heuristically.**
- The noises in distinct small-scale windows are nearly independent, and c_n changes sign.
- So the true contribution of scale u = x/N is ≈ |ν(u)|/√N (L² heuristic: Σc_n²/n² weighting),
  which is negligible.
- But proving it brings back exactly what the sup-norm route was designed to avoid:
  - **Predictability.** c_n for n > √x depends on primes decided after the primes generating
    ν(x/n). Through the greedy feedback, the realised integer set itself depends on U_q.
  - **Cross-scale covariances.** The C-κ kernel of Addendum B.
  - **Short-interval cancellation of c_n.** In the dense range n > √(x/H), consecutive n sample
    the same window, so one needs Σ c_n over runs of length ≈ N²H/x.

So the statement "Addendum B is moot" (v2 §3.5; revision-plan §C rows B1–B5) is false. The L²
issues were not bypassed. They were moved into a sup-norm bound that diverges.

**Verdict on this item.** G2-R is **[OPEN]** at all scales log x ≳ (log X₀)^{1.18}. It is the
**top blocker** of Theorem A. It is new: the first report checked the L² route (item 12,
Addendum B), and the sup-norm route did not exist then.

**Possible repair.** Split the noise response by scale:
- (a) Scales u = x/n with H(u) ≥ (1 + log x)^{2(2K+1)}·polylog, i.e. log u ≥ (log x)^{0.85}.
  Use sup-norm there. This is valid.
- (b) Smaller scales. Prove an L²/martingale bound with the dilation covariances, conditioning on
  a predictable proxy for c_n. A natural proxy is the coefficient computed from the integer set
  frozen at scale x/n. Alternatively, show that the small-scale contribution enters only through
  smooth (Riemann-sum) averages, as v1 §5.5(i) tried.

Part (b) is a real theorem, not bookkeeping.

---

## §2 Status of every item from the first report and the addenda

R = resolved, PR = partially resolved, NR = not resolved. I read the cited proofs, not v2's
summaries of them.

| # | first-report item | status | reason (with the proof actually read) |
|---|---|---|---|
| 1 | Circularity: v1 §5 used the global PNT | **R** (LP itself) / PR (downstream) | gap-localPNT §2: Landau's method on the N-side extension N♯, with positivity imported from the finite Euler product P_y (Steps 3–4) and smoothing to the left with G(0) = 0 (Step 6). I checked Steps 1–6 (details in §3e). This is a correct and genuinely new local PNT. But its downstream use (6.1) carries the ν_* defect of §1. |
| 2 | Continuous reference π_T is wrong | **R** | ρ_ref = (1+K)^{−1}T′_cont uses realised cofactors. The early-window bound is log x·\|ρ_osc^{(k)}\| ≤ κ′_k(1 + log y/log x_k)F_θ, using Lemma M (c_n = μ for n ≤ √x). With κ′_k = κ₀/log²x_k this is o(1). Checked. |
| 3 | H-pair insufficient | **PR** | Lemma CL is the constant-free local bound I asked for (k = 2 gives the pair bound). It is queue-independent (§3g). The shape counting is still [S] (gap-G3 §3 remark iii). |
| 4 | Tijdeman range | **R for G3**, relocated | TC plus the exact excess identity (checked, §3f) removes the rigid set from Lindley. The difficulty moves into R1′-int, which is open and acknowledged. |
| 5 | G3-sm not minor | **PR** | Lemma SM is [S]. It is vacuous only for x ≤ exp(X₀^{1/11}), and **it is needed at every designed-zero scale**, since x₁ ≥ exp(X₀²). |
| 6 | Novelty overclaims | **R** | v2 §7.2 withdraws open problem 1, BDR-unconditional, and dVP optimality, correctly. Minor points in §4. |
| 7 | (T1) log* | **R** | |
| 8 | κ, lag, numerics jitter | **R** | (L-a) is now in x^η form. The numerics are labelled proxy-regime. |
| 9 | Lemma 2.3 disc | **R**, minor residue | Radius ⅛. The "integral part" of (ii) on σ ∈ [¾, 1 − θ_b] needs the corrected ρ_det estimate (§3h). |
| 10 | D̂ absolute convergence | **R** | |
| 11 | f_II / nonlinearity | **R** | It is absorbed into ρ_ref, which uses realised cofactors. |
| 12 | G2-R | **NR** | Lemma B (scalar) is correct and Lean-checked. The L² route was replaced by the sup-norm route, which fails at small scales (§1). |
| 13 | Numerics overstated | **R** | §6 is labelled proxy; v1's "every gapped step agrees" is withdrawn. |
| A-a | Causality, centred jitter | **R** | C2 checked. |
| A-b | Two-sided Cor 1.2 | **R** | C3. |
| A-c1 | Adaptivity of γ_k | **R** | φ ≡ 0 on [x_k, x_k + H(x_k)]. The system on [1, x_k) is independent of γ_k. |
| A-c2 | Landing below X₀ | **R** | One-sided jitter until X₀ + H. |
| A-c3 | Recentring | **R** | |
| A-c4 | (L-a) only in x^η form | **R** | |
| B-1 | Predictability of c_n | **NR** | v2 calls it "moot" via the sup-norm route. That route fails (§1), and the issue comes back for the small-scale noise. |
| B-2 | Increment bound for the noise martingale | **R in G3**, **NR in NV** | G3 uses X_q ≤ 2M₁ from E_cl on L⁵-windows, which is correct. NV (v2 §3.4 step 2) claims H/q ≤ H/X₀ ≪ L^{−6}. That is false once H(u) > X₀L^{−6}, i.e. for log u ≳ exp(√(log X₀/8)), which includes **every** designed-zero scale. Fix: SM-type truncation for latest primes q ∈ [X₀, H(u)L⁶] (§3b). |
| B-3 | C-κ depends on H-pair | moot as written, but **returns** | Any repair of §1 at small scales needs a covariance or cancellation input of this kind. |
| B-4 | 0.48/H | **R** | Acknowledged in gap-G2R §8.4. |

---

## §3 Adversarial checks of the new material (most important first)

### §3a Non-circularity (§0.3: "only G3 uses current-scale data")

**Structurally correct. Quantitatively incomplete.**
- Every row reads only data at scales < y. I re-traced each one.
  - ρ_ref(y) uses cofactors ≤ y/X₀.
  - LP/LP⁺ use (H_y) on [1, y(1−2δ)].
  - K e uses ν on [X₀, y/2].
  - BR uses near-threshold primes at scales ≤ √y.
  - CL uses (F3), i.e. (L-a) below z only. The indicator 1(G_{<s_r}) ≥ 1(G_{<z}) is inserted at each
    peel, which is legitimate.
  - SM uses Chebyshev bounds at scales ≤ 2L¹¹.
  - G3 uses R1′(y) and E_cl(y). Both are functions of data below y.
- The first-failure-time argument (P(τ ∈ [x, 2x], G_{<τ}) ≤ 3x^{−2}, summed over dyadic x) is
  standard and correct.
- The adaptive choice of γ_k is predictable (A-c1 fixed). LP's constants are absolute, because
  (H_y) holds with (A, C, θ′) = (1, 1, ¾) uniformly in X₀. I checked the list of terms in v2 §5.2.

**What the non-circularity argument does not deliver.** The "< scale" inputs must also be small
*relative to the requirement at the current scale*. For NV/G2-R/BR/(6.1) they are not (§1): the
input at scale u ≈ X₀ is fixed, while the tolerance c′/(4 log x (1 + log x)^{2K+1}) → 0.
- This is not a cycle. It is a divergence of the induction constants.
- §0.3's sentence "So R1′(y), E_cl(y) and SM(y) hold on G_{<y} except on an event whose probability
  is controlled" is therefore false for R1′(y) once log y ≳ (log X₀)^{1.18}.

### §3b The sup-norm G2-R route, NV, and the bridge (U8)

See §1 for the main defect. Further points:

1. **NV step 2 (v2 §3.4) fails at large scales.** It says "every latest prime is jittered and
   ≥ X₀ ≫ H, so the cofactor window H/q ≤ H/X₀ ≪ L^{−6}".
   - With H(u) = exp(8ℓ(u)²) and log X₀ ≈ 10⁹, H(u) > X₀ as soon as ℓ(u) > 1.1·10⁴. That covers
     all u ≥ x₁.
   - There, latest primes q ∈ [X₀, H(u)L⁶] have cofactor windows of length ≥ L^{−6}.
     X_q(W_u) ≤ 2M₁ is then not available from E_cl, so Freedman's b is unbounded.
   - These composites are (H(u)L⁶)-smooth. Their density is ≈ ρ(log u/(8ℓ²)), which is tiny. So
     the fix is the same SM-type truncation as in G3.
   - "Under TC it is not needed" (v2 §3.4, last line) is wrong at these scales.
2. **The bridge (gap-G2R §10) has the same scale defect as §1.**
   - Step 1 multiplies sup_u|Δρ^{sh}(u)| by ‖(1+K_op)^{−1}‖ ≤ (1 + log x)^{2K+1}.
   - Δρ^{sh}(u) contains the near-threshold prime discrepancy (B + √(H(u)λ) + λ)/H(u), at the
     *local* H(u).
   - At u ≈ X₀ this is a fixed quantity ≍ H(X₀)^{−1/2}, so the bound diverges as in §1.
   - Step 1 also relies on Lemma B′ for operator weights, whose proof has a gap (§3c).
3. **Near-threshold weight.** gap-G2R §10 step 3 uses "Σ_{near w} 1/w ≤ η ≈ 2/log x".
   - The sum is a sum over primes p near the threshold √(x/m). Counting with P⁺(m) ≤ p, I get
     Σ_{near w} 1/w ≲ Σ_{p₀ ≥ x^{1/A}} H(p₀)ρ(u_{p₀})/(p₀ log p₀).
   - That is super-polynomially small, much smaller than 2/log x. Being smaller is fine for them.
   - The point matters for the repair in §6, where ‖Δ‖_∞ must be ≪ 1/log x.
4. **What is right in the route.** The algebra is correct: e = −Ke − ν, (Ke)(x) = Σ_{n≥2} c_nν(x/n)/n,
   and |Ke| ≤ Σ|c_n|/n · sup|ν|. The idea of avoiding L² is attractive. It works only for scales
   u = x/n with H(u) ≥ (1 + log x)^{2(2K+1)}·polylog.

### §3c Lemma B′ with operator weights: the key identity is false as stated

**Where.** gap-G2R §8.0″ (ii): "b_d := Σ_{e|d} c_e = Σ_e (A − κ_{d,e})∘c_e, with ‖A − κ‖ ≤ 1". v2
§3.3 builds on it.

**The scalar case is fine.** c_d = −Σ_{e<d, e∈F_d} c_e gives b_d = Σ_{e∉F_d} c_e, supported on bad
divisors. Lean `abs_cG_le_G` covers this.

**The operator case goes wrong.**
- In the operator case c_n is a functional acting on f near x/n. The recursion by last step is
  c_d[f] = −Σ_{e<d} c_e[κ_{d,e} f], where κ_{d,e} is the restricted H-average of f at scale x/d.
- To place b_d at one evaluation point, one must write b_d[f] = Σ_{e|d} c_e[M_{d/e} f], with M_m the
  *pure dilation*. That gives b_d = Σ_{e<d} c_e∘(M_{d/e} − κ_{d,e}) with
  M − κ = (M − A) + A∘1_{≤τ}.
- The term **M − A is present for every pair (d, e)**, good or bad. It is not small on rough f.
  - For ν, (M − A)ν = ν − Aν ≍ |ν|, since adjacent H-windows carry nearly independent noise.
  - So b_d is not supported on the bad layer, and the layer descent fails.
- Concrete case: n = pq with no threshold at all. The three chains give the kernels at scale x/(pq)
  −U_H + U_H*U_{H/q} + U_H*U_{H/p}.
  - In the scalar case these cancel to μ(pq) = +1.
  - As operators they are three different kernels. The cancellation is exact only on functions that
    are constant at scale H.
  - For small cofactors (H/2, H/3 smoothing) the defect is O(1) in total variation.

**Status.** Lemma B′ (operator form) is **unproved** on rough inputs. It does hold, up to O(ω_f)
errors, on inputs that are smooth at scale H (T′, R_j′, ρ^{sh} away from thresholds).
- That suffices for the bridge's *smooth* part.
- It does not suffice for the noise response, the bridge's discrepancy part, or (6.1).
- Together with §1, this means rows LB′ (operator form), G2-R and BR are not established.
- The repair in §6 avoids B′-op altogether: it inverts only the sharp operator and treats
  K_op − K_sh perturbatively.

### §3d Lemma M (gap-localPNT §5)

**Correct. I checked it line by line.**
- *Squarefree case.* Chains are ordered set partitions with block conditions max(B_i)·Π_i < x. The
  split/merge involution at the first deviation i, using the largest remaining prime q:
  - preserves validity in both directions (split: B_j∖q has smaller max and smaller product; merge:
    the merged block has max q and product Π_j);
  - changes k by ±1;
  - keeps the first deviation at i;
  - is an involution.
  The canonical decreasing-singleton chain is valid iff χ_x(n) = 1, with sign μ(n).
- *Non-squarefree case.* With s = max{p : p² | n}, F_n is d ↦ d△{s} stable (prime support of n/d is
  unchanged). χ_x(d) = χ_x(d△{s}): conditions at p > s involve only primes > s, and at p ≤ s,
  p·∏ ≤ s·rad(n) ≤ n < x. So the terms cancel in pairs.
- Remark M′ (arbitrary order weight t, ties broken by a fixed order) goes through verbatim.

**Additional fact the authors should use.** The support {χ_x = 1} is a "dense-divisor" set: for
n = p₁⋯p_r, χ_x(n) = 1 ⟺ p_i < (x/n)·p₁⋯p_{i−1} for all i. This is Tenenbaum's t-dense
criterion with t = x/n.
- By Saias (1997), #{n ≤ N : n t-dense} ≍ N log t/log N.
- Check for ℕ, x = 10⁷ (`/tmp/rhscratch/referee2/chi_density.py`): the density of χ_x = 1 on
  [N, 2N] divided by log(x/N)/log N is 0.25, 0.48, 0.56, 0.62, 0.38 for N = 10², …, 10⁶.
- So the coefficients at small scales u = x/n are supported on a set of relative density
  ≍ log u/log x. This is exactly what rescues the noise response (§6).

### §3e LP / LP⁺ (gap-localPNT §§2–3) and how their constants enter X_LP

**LP is correct as far as I can check, and it is the most valuable new ingredient.** Step by step:
- **Step 1.** N♯ = N on [1, y], then linear. So |D♯(u)| ≤ Cu^{θ′} uniformly, and
  ζ♯ = As/(s−1) + D̂♯, with D̂♯ entire and ≤ C|s|/(σ − θ′). Correct.
- **Step 2.** The local Chebyshev–Mertens bound from log·dN = dψ * dN, which is local. Correct.
- **Step 3 (the key idea).** P_y = exp(∫_{≤y} u^{−s}dΠ) is a genuine positive Euler product, and
  Δ = ζ♯ − P_y lives on (y, ∞).
  - Rankin gives |Δ| ≤ Ay^{−η}/η + y^{−η/2}P_y(1), with P_y(1) ≤ e^{K₀}(log y)^{a₁}.
  - P_y(σ) ≤ 2A/η.
  - So |Δ/P_y| ≤ (log y)^{−1} on σ ≥ 1 + η_y with η_y = K₂ log log y/log y, K₂ = 4a₁ + 20.
  - The 3-4-1 inequality (2.1) transfers with loss 8/(η log y). Correct.
- **Step 4.** Landau's lemma on discs of radius r = (1−θ′)/2, which stay in σ > θ′. Dropping the
  zero terms is legitimate because every zero has Re < 1 + η_y ≤ 1 + η. This gives a zero-free
  region σ ≥ 1 − c₂/(14 log(|t|+3)) for |t| ≤ T_y = exp(c₂ log y/(K₂ log log y)). Correct.
- **Steps 5–6.**
  - Smoothing to the left keeps everything in [1, y].
  - G(0) = 0 removes the residue.
  - Heights above T₁ = e^{2√log v}(log y)^{2/m} are handled on Re s = η_y. The kernel decay
    (T/T₁)^m beats v^{η_y} ≤ (log y)^{K₂} when log log y ≤ √log v. Otherwise y is replaced by v.
  - So there is no hidden use of data beyond y. My original worry (high zeros of the extension near
    height y) is answered: LP only claims precision e^{−c√log v}, so it never needs resolution finer
    than 1/T.
- **LP⁺ (3.2).** On (y, 2y), dN♯ = dN_y + dΠ♯, since the smallest element above 1 is 2. The
  composites in J ⊂ (y, 2y) are exactly N_y|_J. A contour estimate for ∫φ dΠ♯ (smooth φ, heights
  ≤ log²x/δ ≤ T_y) predicts C(J) to within K x e^{−c√log x}log²x. Correct.
  - It controls only windows of relative width δ ≥ e^{−c√log x/2}. These are astronomically long
    compared with Freedman blocks; this is fine, since it is used only for averages.

**How the constants enter X_LP.**
- (A, C, θ′) = (1, 1, ¾) uniformly, so K and c are absolute.
- The binding requirement is the LP⁺ term in (6.1) at δ = γ_*^{−2}log^{−4}x with γ_* ≤ e^{c√log x/4}.
  That term is K log⁸x·e^{−c√log x/2}, and requiring it ≤ e^{−7}-ish gives
  log X_LP = ((8 log log X_LP + 7)/c)², as stated. Consistent.
- The inequality X₀ ≥ X_LP is not circular *as long as C does not depend on X₀*.
  - It does depend on X₀ under candidate B-lin (gap-G3 §9.4, C_{X₀} = exp(O(X₀^{1−θ}))) and under
    Huxley widening.
  - In Landau's lemma M ≍ log C, so c ∝ 1/log C and log X_LP ∝ (log C)² ≍ X₀^{2(1−θ)} > log X₀.
  - LP therefore cannot be used on [X₀, X_LP(C_{X₀})], and another input is needed there (§5).
- Minor gaps:
  - U5 (c not computed) is harmless for existence.
  - The claim "C = 1 for X₀ ≥ X₀(θ)" needs the base-range queue bound in (H_y). Under S(ε) that
    is Q ≲ u^{θ/4}, which itself depends on the pending soft-rule analysis.

### §3f The target change TC and the exact excess identity

**The identity is correct.**
- #slots(W) = (#jumps in W) + ∫_W T′_cont ± 1 and C(W) = C_rigid(W) + C_jit(W), with
  C_rigid(W) = #jumps(W).
- A jump slot J_j = T^{−1}([j, j+1)) also contains a continuous piece of length < 1/T′_cont, where
  jittered composites can land. That does not affect the identity, and A_j ≥ 1 still holds there.

**Minor points.**
1. **"0 ≤ ρ_det ≤ 1" is not quite true.** A window (u, u + u^{θ_b}] can contain ⌊u^{θ_b}⌋ + 1
   rigid integers, so ρ_det ≤ 1 + u^{−θ_b}.
   - Excluding this needs a run of ≥ u^{θ_b} consecutive X₀-smooth integers *not* to exist. Near
     X₀ that is the statement "no prime gap of length X₀^{θ/2}", which is unproved.
   - So T′_cont can be slightly negative, and slots can be ill-defined.
   - Fix: cap ρ_det at 1, or normalise by ⌊w⌋ + 1. The cost to T1 is O(x^{θ_b}).
2. **"x is generic" is not available for a deterministic T.** T(d−) ∈ ℤ can occur. Add a fixed
   irrational offset to T on [X₀, ∞).
3. **Consequence the draft already sees.** TC makes the oscillation-free continuous density
   1 − ρ_det prime-gap driven. That is precisely why R1′-int becomes a short-interval statement
   about rational primes.

### §3g Lemma CL and E_cl: is E_cl really queue-independent?

**Yes, given the sketch.**
- CL inserts 1(G_{<s_r}) ≥ 1(G_{<z}) at every peel. The peeled primes are factors of elements of
  J ⊂ [z, 2z], so s_r ≤ z.
- It uses (L-a) only below z, through (F3) (harmonic sums and N(y) ≤ 2y).
- (F1) and (F2) are deterministic.
- E_cl at scale x is a statement about P(E_cl^c ∩ G_{<x}) ≤ x^{−3}, which involves no queue bound
  at x. The arithmetic checks: 2C₁Aδ₁ ≤ L^{−4} needs 256(L+2) ≤ L², i.e. L ≥ 260, and
  x²(L^{−4})^{M₁−1} ≤ x^{−3}.
- Unlike the multiplicity lemma of gap-G2R §8.3 (whose circularity gap-G3 §2.2 correctly
  identifies), CL does not feed the queue back into itself.

**Caveats.**
- (i) The shape counting is [S], as flagged. That is the place to look for an error: the claim that
  every admissible configuration is resolved by P-abs/P-rel/P-pass steps with ≤ 4^g split trees per
  block and ≤ 2^k block structures.
- (ii) The factor A ≈ log z (from ignoring the 1/log density of primes in (F1)) is harmless,
  because M₁ absorbs it.
- (iii) CL bounds expectations of *jittered* elements only. Its use for X_q^{(1)} on L⁵-windows in G3
  is correct. Its use in NV on H-windows is not, at large scales (§3b(1)).

### §3h §2 under the truncated-Euler-product base factor

**Correct in substance, with one wrong estimate.**
- (i) Z = E_{X₀} + X₀^{1−s}/(s−1) − ∫x^{−s}ρ_det dx is correct. But the bound
  |∫x^{−s}ρ_det| ≤ 4E_{X₀}(σ + θ_b)/|t| is not.
  - Integrating by parts puts x^{1−s} against dρ_det, so the triangle inequality gives
    (2/|t|)E_{X₀}(σ + θ_b − 1). This is **infinite for σ ≤ 1 − θ_b**, so the claim "for σ ≥ ¾" is
    false.
  - On σ ≥ 1 − θ_b/2 we have E_{X₀}(θ_b/2) ≤ e^{X₀} and |t| ≥ e^{X₀²/4}, so Z = E_{X₀} + O(e^{−X₀})
    still holds there. That covers the δ_k-disc and the Rouché circle.
  - For Lemma 2.3(ii)'s strip σ ∈ [¾, 5/4], use the split
    Σ_d d^{−σ}min(1, d^{1−θ_b}/|t|) with #𝒟 ∩ [1, Y] ≤ (2 log Y)^{π(X₀)}. It is still tiny.
  - Fixable, minor.
- (ii) Paley–Zygmund for E_{X₀} is correct.
  - Montgomery–Vaughan applies with Σ_d d^{−2}·d ≍ log X₀.
  - The fourth moment is ≤ ζ(2)⁴/ζ(4), and the density is ≥ 0.036, uniformly in X₀.
  - Also Z_max = 2 log X₀ (Mertens), and |E′| ≤ |E|·Σ_{p<X₀} log p/(p−1) ≤ 2 log²X₀.
- (iii) Lemma 2.1 with κ′_k = κ₀/log²x_k gives Re s* = 1 − (3 log log x_k + O(1))/log x_k. Correct.
- (iv) Lemma 2.2 needs |D| ≤ x^η only for x ≥ x_k. Lemma 2.3 needs only K(N) ≪ N^{1/2−ε} on the
  base range. So the base-range queue Q ≲ u^{θ/4} (under S(ε)) or ≲ u^{θ/2}/log u (telescoping) is
  acceptable for §2. "θ is not restricted" is right.
- (v) Theorem 2.4 is correct given (L-a).

**Under candidate B-lin.**
- Ê is huge at σ = ¾, so the strip in Lemma 2.3(ii) must shrink to σ ≥ 1 − 1/log X₀, with
  subharmonic radius ≍ 1/log X₀.
- The mean square is then ≍ X₀^{−1+O(1/log X₀)}·K, and the radius costs (log X₀)², so this still
  works.
- |Ê| ≤ 2κe^γ log X₀ near σ = 1 keeps |Z| ≥ ½.

---

## §4 Are the §7 scope statements now accurate?

**Mostly yes.** §7.1–§7.2 correct every scope issue from my first report.
- Q is refuted only conditionally.
- Q's refutation says nothing about ζ.
- Not de la Vallée Poussin optimality. Correct: 1 − β_k ≍ 3(1−θ) log log γ_k/log γ_k, and the
  log log loss is forced by (1.1).
- Not Broucke's App. A problem 1.
- No unconditional BDR systems. α = 1 even conditionally.

Remaining corrections:
1. **§7.3, Landau's PNT.** "ζ_P ≠ 0 for σ > 1 − c(1−θ)/log t … See Broucke's thesis, Thm 3.1.1;
   verified at source."
   - Thm 3.1.1 (thesis p. 35) states only π(x) = Li(x) + O(x exp(−c√log x)).
   - The zero-free region, and in particular its (1−θ)-dependence, comes from the proof (cf. LP
     Step 4, where r = (1−θ′)/2 enters c₂ non-linearly).
   - Mark it "from the proof", not "verified at source".
2. **§0.2/§8: "Everything else is [P] or [C]".** This is false. The following are not established:
   - G2-R and BR (§1);
   - NV at large scales (§3b);
   - LB′ in operator form (§3c);
   - G1′ through (6.1).
   - Minor items:
     - the Z-estimate exponent (§3h);
     - ρ_det ≤ 1 (§3f).
3. **§0.3.** "R1′(y) holds on G_{<y} except on a controlled event" needs the quantitative caveat of
   §3a.
4. **§7.3, novelty.** H. Diamond is quoted on M. Watkins' Beurling page
   (empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/beurling.htm): "there are quite simple
   Beurling-theory examples of nice counting functions N(x) for which such a good approximation as
   N(x) = x + O(1) exists, but for which the zeta function has zeros off the line Re s = 1/2."
   - No example or side of the line is given.
   - The novelty claim should acknowledge this remark, and ideally ask whether such examples can
     have zeros approaching Re s = 1. If simple examples did, Q would already be known false, and
     the greedy's contribution would be the method rather than the result.
   - I could not resolve this from the web.
5. **§0.4 "This regime is far outside anything numerically checkable."** Accurate and well put. The
   §6 numerics are honestly labelled.

---

## §5 The five repair candidates for R1′-base / R1′-int

I take the five to be:
1. soft feedback S(ε);
2. D3 plus a Cramér-type short-interval hypothesis;
3. Huxley widening on [X₀, X_*] with a switch back to x^{θ_b};
4. B-lin, a linear window κu at all scales (gap-G3 §9.4);
5. a randomised base below X₀.

Whichever candidate is used, the drift *above* the base range still needs the §6 repair of G2-R.
"ν small at every scale" is not enough by itself (§1).

**1. S(ε): viable, and the most developed. Moderate chance.**
- Under S(ε) the base-range queue is not controlled by drift: ερ_ref is far smaller than the
  sign-indefinite nested-window term. It is controlled by telescoping (D2) plus Brun–Titchmarsh,
  giving Q ≲ x^{θ/2}/log x unconditionally. That is acceptable, because §2 and LP need only
  |D| ≪ u^{1/2−ε} (resp. u^{3/4}) on the base range (§3h(iv)).
- **The weak point: D2 is exact only for m = 2.** On [2X₀, X_*], every dilation class p·m with
  m ≤ X_*/X₀ (and multi-prime classes) has its own nested bracket.
  - The endpoint terms sum to Σ_m (x/m)^{θ_b}/(m log x) ≍ x^{θ_b}/(θ_b log x), so the bound is
    plausible.
  - But the general-m telescoping, including how the soft rule's primes enter each class, is not
    written.
- The S(ε) bookkeeping (V_j = j + Q_j changes, because primes are placed while Q > 0) is
  [PENDING gap-g3].
- With the §6 weighted bound, ε need not be (1 + log x)^{−2K−1}/8. Any ε(u) with
  Σ_{dyadic u} ε(u) ≪ c′ over the scales where Q > 0 suffices, e.g. ε(u) = c/(log u)^{1+δ}. The
  queue above X_* is then polylog, not quasi-polylog.

**2. D3 plus a Cramér-type hypothesis: not useful.**
- A refutation of Q conditional on "primes of density ≫ 1/log x in every [x, x + x^{θ/2}]" (stronger
  than RH) has little value.
- gap-G3 §9.3(b) also shows that per-class dilation-consistent widths make T − x linear in x, with
  log-factor corrections that are not O(x^θ). So (T1) needs work even conditionally.

**3. Huxley widening on [X₀, X_*] with a switch back: does not close.**
- gap-G3 §9.3(a), (c) show two problems, and I agree with both:
  - components with large m′ see windows below Huxley's range;
  - switching back to x^{θ_b} at X_b reintroduces an O(1) mismatch just above X_b.
- The C(X₀)-dependence of LP is an additional problem (§3e).

**4. B-lin: a promising unconditional route, with one gap.**
- The exact dilation identity MA_{κx}[D_m h](x) = (1/m)·MA_{κ(x/m)}[h](x/m) is correct; I checked it.
  So the nested bracket vanishes for every class.
- Every component is in Huxley's range: κq ≥ q^{7/12+ε} for q ≥ X₀.
- The (T1) cost O_{X₀}(x^θ) is legal for Q, since constants are free.
- §2 survives with the strip shrunk to σ ≥ 1 − 1/log X₀ (§3h).
- **The gap.** The ℕ-coupled forcing bound |μ| ≤ … + (B + H)/(κX₀) fails once H(u) ≳ κX₀ = X₀^{7/12},
  i.e. once ℓ(u) ≳ 8.5·10³ for log X₀ ≈ 10⁹. LP with C_{X₀} = exp(O(X₀^{1−θ})) takes over only at
  log x ≈ X₀^{2(1−θ)}. So there is an uncovered window.
- **Proposed bridge.** Rerun LP Step 4 with discs of radius ≍ 1/log X₀ around 1 + η + iγ, where
  Ê is small, instead of radius (1−θ′)/2.
  - Landau's lemma then gives c ∝ 1/log X₀, so log X_LP ≍ (log X₀·log log)²/c², of order X_*.
  - That is far below the point where the ℕ-coupling fails.
  - This needs checking, but it is the kind of change LP can absorb.
- The same §6 weighting is needed for the e- and μ-responses, which currently use "Lemma M then
  gives |e| ≤ c′/(4L)" in sup-norm.

**5. Randomised base: unexamined, conceptually the cleanest. Worth a serious look.**
- The obstruction on [2X₀, X_*] is that ℕ's holes (rational primes) need short-interval control.
  With a random base (DMV/Zhang/Broucke–Vindas-type, N_base = u + O(u^{1/2+ε}) w.h.p., enough for
  (H_y) with θ′ = ¾), the hole densities in windows of length x^{θ/2} become averages of a random
  point process.
- The nested bracket ½[ρ^{(w/2)} − ρ^{(w(x/2))}] is then a fluctuation of size ≍ (w log x)^{−1/2},
  small next to c′/log x w.h.p. This is the same k-moment technology as CL, now applied to
  products of base primes.
- §2's Z becomes the random base's finite Euler product, and Lemma 2.3(i) goes through unchanged.
- The main work is a CL-type lemma for products of random base primes in short windows, plus a
  union bound over windows on [2X₀, X_*].

**Ranking.**
- S(ε) and the randomised base are the most likely to work. S(ε) is closer to written; the
  randomised base is more robust, since it needs no arithmetic of rational primes at all.
- B-lin is a solid third, provided the LP-with-small-discs bridge works.
- Candidates 2 and 3 should be dropped.

---

## §6 A suggested repair of G2-R (weighted sharp resolvent). Sketch, to be checked by the owners.

The goal is a bound log x·|e(x)| ≤ ε(X₀) → 0, uniformly in x. It needs neither Lemma B′ in operator
form nor M-op.

1. **Invert only the sharp operator.**
   - Write K = K_sh + Δ, where K is the operator of the exact margin identity
     ρ̃ = T′ − Kρ̃ − ν.
   - Put e_sh := ρ̃ − ρ^{sh}. Then e_sh = −(1 + K_sh)^{−1}(ν + Δρ̃), and Δρ̃ = Δρ^{sh} + Δe_sh.
2. **Use Lemma M.** It gives ((1 + K_sh)^{−1}g)(x) = Σ_n μ(n)χ_x(n)g(x/n)/n. Hence

     |e_sh(x)| ≤ Σ_{u dyadic} W_x(u)·sup_{[u,2u]}|g|,
     W_x(u) := Σ_{n∈[x/2u, x/u]} χ_x(n)/n ≪ min(1, log(2u)/log(x/u)).

   - The bound on W_x(u) is a Saias-type upper bound for t-dense elements (t = x/n) of the
     *realised* semigroup.
   - It can be proved by Rankin and sieve from the Chebyshev bounds that LP supplies.
   - This is new, but standard in shape. For ℕ it is Saias (1997); see §3d for numerics.
3. **Bound the noise per scale.** Use per-scale good events with λ(u) = 3 log u. Their failure
   probability is ≤ u^{−2}, which is summable over dyadic u. On them,

     |ν(u)| ≤ √(4M₁(u)λ(u)/H(u)) + O((B(u) + M₁λ(u))/H(u)).

   The NV step-2 truncation of §3b(1) is needed for latest primes q < H(u)L⁶.
4. **Sum.**
   - log x·Σ_{u≤√x} W_x(u)|ν(u)| ≲ Σ_{u ≥ X₀ dyadic} log u·|ν(u)| ≍ Σ_L L²/√H(L) + Σ_L L⁴/(H(L) log L).
     This is finite and → 0 as X₀ → ∞ as soon as **H(u) ≥ (log u)^{6+δ}**.
   - The scales u > √x contribute ≤ (log x)²·sup_{u>√x}|ν(u)|, which is fine for the same H.
5. **The Δ terms.**
   - Near-threshold cofactors w = pm have p ≈ √(x/m) and P⁺(m) ≤ p. Their weight at x is
     ≲ Σ_{p₀ ≥ x^{1/A}} H(p₀)ρ(u_{p₀})/(p₀ log p₀).
   - So |Δe_sh(x)| is super-polynomially small relative to sup|e_sh|.
   - Δρ^{sh} is handled by the bridge's antisymmetry argument (its smooth part). Its prime-discrepancy
     part is one more scale-local noise term, at scale p₀, to be put into g with the same weighting.
6. **The soft rule's deliberate deviation.** Under S(ε), e ⊇ −ε(u)ρ_ref(u) while Q > 0. Its weighted
   contribution is ≲ Σ_{u: Q(u)>0} ε(u). This needs Σ ε(u) ≪ c′, not ε ≤ (1 + log x)^{−2K−1}.
7. **The same weighting must replace ν_* in gap-localPNT (6.1) and in the bridge.** In (6.1) use the
   identity K_r e = −e − ν rather than a resolvent bound on K_r e.

**Consequences.**
- If this works, polylog H (≈ (log x)⁷) suffices. (L-a) then becomes polylog again in the queue
  part, and the binding threshold is X_LP alone.
- What remains genuinely open is R1′-int (§5) and the [S] items CL and SM.
- Risks:
  - (a) the Saias-type upper bound for the realised semigroup;
  - (b) whether the exact margin identity's operator K really splits as K_sh + Δ with Δ supported
    on near-threshold cofactors (v2 §3.6 says so);
  - (c) whether the edge terms in ν are scale-local.

---

## §7 Addendum: v2 as final for this round (§0.2 three R1′ rows, §1.2 PR, §5.2–§5.4)

I re-read the updated §0.2, §1.2, §1.3 and §5.2–§5.4 (file now 1021 lines). My verdict and
blockers are unchanged. Specific points:

1. **R1′-hi** is tagged "[P | G1′, G2-R, BR] for y ≥ X_* under S(ε), y ≥ X_** under G". **It is not
   proved under either rule.**
   - The divergence of §1 sets in at log x ≈ (log X₀)^{1.18} ≈ 4·10¹⁰ (for log X₀ ≈ 10⁹). That is far
     *below* X_*, where log X_* ≈ 10²⁴–10²⁹.
   - So the whole claimed range of R1′-hi lies where the sup-norm G2-R/BR/(6.1) bounds diverge.
   - The pending tagging fix (G1′ under G only for x ≥ X_**) is consistent with the draft's own
     analysis, but moot until §1 is repaired.
   - Under S(ε), "sup|ν| = O(ε/log x + √(λ/H)) at every scale" (§1.2) does not help. The √(λ/H(u))
     term at u ≈ X₀ is fixed, while the tolerance at x shrinks like (1 + log x)^{−2K−2}.
2. **§5.2 items tagged [P] "for all x".**
   - I agree for LP, LP⁺, Lemma M (sharp), Lemma B′ in **scalar** form for K^{jit}, and the R(δ)
     threshold part.
   - I do not agree for Lemma B′ in **operator** form (§3c).
   - **The window average of the actual margin** (via C(J) from LP⁺ and Mart(J)) indeed does not
     use ν_*, so I accept it, with one item to write out: Freedman for Mart(J) on these very long
     windows needs a per-prime increment bound.
     - For a small latest prime q, X_q(J) is huge. Its fluctuation, however, comes only from the two
       edges of J/q under the jitter U_q, i.e. ≲ (xH/q²)×(density of q-smooth cofactors).
     - That should be stated.
   - "Passing from the margin to ρ_ref uses |Ke| ≤ (1 + log x)^{2K+1}ν_*" is exactly the step that
     fails (§1).
3. **§1.2 / §1.3 placement rule PR with (PR1). Checked.**
   - Q_j = Q_{j−1} + A_j + P_j − 1 always.
   - V_j = j + Q_j (Lemma 1.1).
   - The A′-Lindley form under S(ε) holds in both cases of (PR1).
   - C3 is unaffected.
4. **Failed-routes table D1–D4.**
   - I agree with D1 (needs primes in [x, x + x^{θ/2}]) and with D4 (echo tower under G).
   - D2 is exact only for m = 2. The general-m telescoping is what S(ε)'s base-range queue bound
     rests on (§5, candidate 1).
   - D3 additionally has the (T1) problem of gap-G3 §9.3(b).
5. **Net.** The open set for Theorem A is the §0 list. The top item is the scale divergence of the
   noise response, for which §6 gives a candidate repair.

---

## §8 Cross-check with referee B (`beurling-greedy-v2-referee-B.md`)

**B's issues, one by one.**

| B item | verdict | reason |
|---|---|---|
| F1 sup-norm noise ignores that H(u) increases | **agree** | Independently my §1, with the same thresholds: log x ≈ (log X₀)^{1.18}. B's "even with M-op it fails from log log x ≈ 500–700" also holds, but only for bounds of the form Σ\|c_n\|/n·sup\|ν\|. See the repair discussion below. |
| F1, BR and (6.1) | **agree** | My §3b(2). |
| F1, "the weight Σ_{n∈[N,2N]}\|c_n\|/n at N ≍ x/X₀ is ≍ 1" | **disagree** for the sharp filter | χ_x(n) = 1 is the t-dense condition p_i < (x/n)·p₁⋯p_{i−1} for *all* i, not just P⁻(n) < x/n. By Saias its density is ≍ log u/log x with u = x/n. Measured for ℕ in `chi_density.py`: 0.05 at u ≈ 6.7, N = 10⁶. So the weight decays like log X₀/log x. For operator-valued coefficients (B′), B's statement stands. |
| F2 operator Lemma B′: step (ii) puts A in place of I | **agree** | Independently my §3c. B's TV numerics (TV(G_n) ≈ \|μ(n)\|(1 + o(1)) in the void-filter region) are a useful addition: the conclusion may be true there. |
| S1 NV step 2, "X₀ ≫ H", false at scales ≥ x₁ | **agree** | Independently my §3b(1). The same SM-type fix. |
| **S2** Thm 4.2′ step 5: M_sm = 100(2 + L⁵/X₀) > c′L⁴ once L > 0.0015X₀ | **agree, I missed it** | Checked in gap-G3 §5. D = 2 + L₀/X₀ counts every integer of a cofactor window of length L₀/X₀ as a possible deterministic cofactor. At L ≥ X₀² that is ≫ the drift, so full blocks have positive excess and the queue grows linearly. Easily fixable: at those scales the X₀-smooth integers have Tijdeman gaps ≥ n/(log n)^{c(S)} = n^{1−o(1)} (log n ≈ L ≥ X₀² ≫ c(S) log log n ≈ X₀ log X₀). So ≤ 1 per window and D → 2. The Tijdeman input returns, but only at large scales, where it is valid. |
| G1 R1′ above X_* depends on the base range (echo/tower) | **agree** | v2's final round added the R1′-echo row for G. Under S(ε), F1 still blocks it. |
| G2 exactness of e = −Ke − ν (the commutator A_x∘K vs K∘A on a rough measure) | **agree** (medium) | I had the same doubt (§3b, "edge terms"). This is also my risk (b) in §6. |
| G3 stopping-time form of Thm 4.2′; (6.1) uses current-scale Mart(J) | **agree** | My §7(2): the Mart(J) increment bound must be written. |
| **G4** union bound: x²·2e^{−3L} = 2x^{−1}, not ≤ 3x^{−2} | **agree** | The arithmetic is right. Σ_m 2(2^mX₀)^{−1} ≈ 4/X₀ is still < ½, so the first-failure argument survives. Restricting to ≤ L₀-slot windows gives ≈ 2L⁵x^{−2}. The NV continuum net and the extra events are also fine to fix. |
| G5 the multiplicity lemma §8.3 is used at smaller scales (R(δ), BR, (6.1)) | **agree** | R(δ) step (ii) indeed uses N(I′) ≤ 3\|I′\| + K_loc. This is not circular, but the dependency table should say so. |
| G6 Lean coverage of LB/LB′ (ℕ, scalar, layer-only) | not checked | Plausible. Consistent with my reading that LB′-op has no formal support. |
| **G7** Broucke arXiv 2507.13780, Thm 1.6 | **agree, verified at source** (pp. 5–6) | N = Ax + O_ε(x^{1/2+ε}); zeros on σ = 1 − f(log\|t\|) for any eventually C¹, decreasing, strictly convex f with 1/u = o(f), regularly varying of index −α ∈ (0, 1] or slowly varying; none to the right. f(u) = 3 log u/u is admissible, which is the greedy's contour. So it is the closest prior result. Theorem A's whole content is θ = ½ + ε → θ < ½, and §7.3 must cite it next to DMV and Zhang. |
| G8 CL writing points | **agree** | |
| M1 the E_{X₀}(σ + θ_b − 1) exponent | **agree** | Same as my §3h(i). |
| M2, M3, M5, M6, M8, M9, M10 | **agree** | Minor. |
| M4 BDR's α-range is "α < ⅔", not "α < 1" | **agree** | Minor. |
| M7 near-threshold weight ≈ H(X₀)/(X₀ log X₀), dominated by the smallest primes | **partly agree** | True for x ≤ X₀^{O(1)}. For log x ≫ log X₀, near-threshold w = pm with p ≈ X₀ needs m ≈ x/X₀² to be X₀-smooth, which costs a factor ρ(log x/log X₀). So the weight comes from p₀ ≥ x^{1/A} (my §3b(3)). |
| §5: "the first referee's own suggestion seeded F1" | **agree** | My Addendum B proposed bounding n > √Y by Σ\|c_n\|/n·sup\|ν\| "for quasi-polylog H", without noticing that H(x/n) is small at those n. That suggestion was wrong for the reason F1 gives. |

**Which G2-R repair is more promising?** I think the sparse-support route (my §6) is.
- It needs **no cancellation**, so neither predictability nor short-interval Möbius estimates.
- With the *sharp* filter, Lemma M gives |c_n| = |μχ_x(n)| ≤ 1. On top of that, the support
  density per dyadic n-block decays like log u/log x (u = x/n).
- So log x·|e_sh(x)| ≲ Σ_{u dyadic} log u·|ν(u)| + (log x)²sup_{u>√x}|ν(u)|. This converges, and
  → 0 as X₀ → ∞, for H(u) ≥ (log u)^{6+δ}.
- B's "uncovered range c√log x ≲ log v ≲ (log x)^{0.85}" disappears, because the weight there is
  already ≪ log v/log x.
- What remains is standard in shape:
  - (i) a Saias-type *upper* bound for t-dense elements of the realised semigroup, by Rankin plus
    the Chebyshev bounds from LP;
  - (ii) treating K_op − K_sh as a weighted-small perturbation, using the smoothness of near-
    threshold cofactors;
  - (iii) B's G2, the exactness of the margin identity, which both routes need.

B's route (a), martingale/L², must make c_n predictable relative to ν(x/n). For n > √x that
fails, because c_n depends on later primes and, through the greedy feedback, on U_q itself.
B's route (b), short-interval cancellation of μ_Pχ_x at relative length H(v)/v, is far below
LP's resolution e^{−c√log v}. Both look harder than (i)–(ii). If the operator coefficients are
kept instead of the sharp ones, B's diagnosis is right: then something like M-op plus thinning
would be required.

---

## §9 Targeted review: addendum §A4 (B-lin) and §A1 (§2 under B-lin)

Sources read: `beurling-greedy-v2-addendum.md` §A1, §A2.3, §A4–§A6, and `gap-G3.md` §9.4–§9.9.

**Verdict.** B-lin is the right repair for the base range, and the five claims hold up, subject to
fixable points.
- (1) Exact dilation commutation and Huxley/Heath-Brown coverage: **correct**. There is one
  normalisation slip (N1), which has to be routed through ρ_base.
- (2) My ℕ-coupling objection: **answered**, provided the per-component form H(q)/(κq) is used.
- (3) Heath-Brown's polylog error suffices with Saias weights and not with crude amplification:
  **correct**.
- (4) §2 survives with error O(e^{−X₀²/4}), and no step evaluates Z off the δ_k-discs or σ = 1:
  **correct**.
- (5) B-lin removes both R1′-int and R1′-echo under G, conditional on the A2.3(c) G2-R repair:
  **yes**, with the additional conditions listed under claim 5.

### Claim 1: the target, cancellation, uniformity, and edges

- **Dilation commutation is exact. I checked it.**
  - For any kernel of the form c·h([u, (1+κ)u])/u, the dilate satisfies
    MA_{κx}[D_m h](x) = (1/m)MA_{κq}[h](q) with q = x/m. This holds both for the log normalisation
    1/(uℓ_κ) and for the linear one 1/(κu).
  - Unique top-prime factorisation, non-rigid = ⊔_{m′} m′·ℙ_{≥max(P⁺(m′), X₀)}, then gives the
    component formula. So the nested-window term of D1/D2 vanishes for every m′, including
    multi-prime classes and prime powers (with ℙ_{≥P⁺(m′)} inclusive).
- **Huxley/Heath-Brown coverage is correct.**
  - κq ≥ q^{7/12+ε} ⟸ q ≥ X₀.
  - Heath-Brown (Crelle 389, 1988) with ε(x) = 0 covers y ≤ q/(log q)⁴, i.e. log q ≤ κ^{−1/4}.
  - The de la Vallée Poussin PNT covers e^{−c√log q} ≤ κ/5, i.e. log q ≥ ((log(1/κ) + 2)/c)².
  - The ranges overlap, since X₀^{5/48} ≫ log²X₀.
  - Everything is uniform in the component, because the short-interval PNT is uniform in q ≥ X₀.
    Using the backward-window form for a forward window is cosmetic.
- **(N1) Normalisation slip: "1 = MA[ℤ]" is false under the chosen normalisation.**
  - With the log-normalised kernel, MA[ℤ](x) = κx/(xℓ_κ) + O(1/(κx)) = 1 + κ/2 + O(κ²).
  - So T′_cont − R′ = 1 − ρ_det = MA[non-rigid] − κ/2 + O(κ²), and the "exact rational identity"
    T′_jit − R′ = (1 + K_ℚ)MA[ℙ] (gap-G3 §9.6 C1) misses an *absolute* constant source −κ/2.
  - At the zero scales κ = X₀^{−5/12} ≫ 1/log x. So this term must not go into μ, where it would be
    amplified.
  - It is harmless if routed through ρ_base. (1+K)^{−1}(−κ/2) = −(κ/2)ρ_base ≈ −(κ/2)/log x, and
    MA_log[ℙ] = (1 + κ/2)/log x. The two cancel to relative O(κ²). That requires the
    smooth-source resolution (LP⁺/R(δ)) of the constant, the same machinery as μ₀.
  - Alternative: use the linear normalisation 1/(κu). Then MA[ℤ] = 1 + O(1/(κu)). The ramp mass is
    ℓ_κ/κ = 1 − κ/2, so E drifts by ≈ (κ/2)Ψ(x, X₀) = x^{o(1)}, which is harmless for (T1).
  - Either fix is easy, but one must be stated.
- **(N2) Near-threshold restriction is not exact.** For P⁺(m′) ∈ (q, (1+κ)q] the component is a
  partial window. Those m′ = pm have p ∈ (√(x/m), √((1+κ)x/m)] and weight ≪ κ/log x, so the
  correction is relative O(κ) and negligible. Write "exact up to O(κ/log x)".
- **Edges near q ≈ X₀.** Ramps of non-rigid integers in [X₀, X₀(1+κ)) are truncated at X₀ (T = ⌊x⌋
  below), leaving a one-time slot deficit ≤ κX₀/log X₀ that only changes C_{X₀}. Its Möbius echo
  at x is, with Saias weights, ≪ κ/log x. ρ_det ≤ 1 holds automatically: Huxley puts primes in every
  window, and beyond log u ≈ X₀^{5/12} the rigid density is ≪ κ.

### Claim 2: my ℕ-coupling objection (H(u) > X₀^{7/12})

**Answered.**
- My objection read gap-G3 §9.4's term "H/(κX₀)" with H at the *composite* scale. But the jitter
  lives at the *latest prime's* scale q. The decision-order and U_H-smoothing mismatches are bands of
  relative width H(q)/q inside a κq-window, so per component they cost H(q)/(κq) (§9.6 C1 writes it
  this way).
- Since H(q)/q decreases, sup_{q≥X₀} H(q)/(κq) = H(X₀)/(κX₀) ≈ e^{3430}·X₀^{−7/12}, which is tiny
  for every x.
- The cofactor-scale terms (D, E, R against ∂_m(f/m)) are ∫(B(m) + H(m) + κmρ)/m²·dm/log x. These are
  dominated by m ≈ X₀ and are small.
- The merged text should state the per-component form explicitly and delete §9.4's
  "+ B/(κX₀) + H/(κX₀)".

### Claim 3: Heath-Brown's polylog error and μ₁

**Correct.**
- μ₁ = (K_ℚ − K_r)f₁ with |f₁(q)| ≤ η(q)/log q and η(q) ≍ (log log q/log q)⁴.
- Components with top prime q ≤ x^{1/U} need P⁺(m′) ≤ q, so their weight is ≤ ρ(U − 1)log U. This
  is a *source* restriction and legitimate, unlike the resolvent tail weight that A2.3(b)
  correctly withdraws.
- Hence |μ₁(u)| ≲ η(u^{1/U})log U + η(X₀)ρ(U − 1)log U.
- With the Saias-weighted resolvent, log x·|(1+K)^{−1}μ₁| ≲ Σ_{u dyadic} log u·|μ₁(u)|. With
  U ≈ 3(log log u)², the first term gives k^{−3}(log k)^{12} at log u ≍ k (summable), and the second
  gives k·k^{−c log k} (summable). The sum is (log X₀)^{−2+o(1)} ≪ c′.
- The large-u part, log²x·sup_{u>√x}|μ₁(u)|, tends to 0.
- Crude amplification e^{2.9ℓ²} beats the polylog η = e^{−4ℓ+…}, so the crude route would need
  Huxley with exponential error, which has no explicit constant. The claim is right.
- Caveat: this rests on A2.3(c)(i)–(ii). It is complete for ℕ-cofactors with sharp coefficients,
  given Saias.

### Claim 4: the (T1) cost and §2 under B-lin

**Correct, with one imprecision.**
- **A1.1.** E = Ψ − ∫ρ_det and ∫x^{−s}ρ_det = W(s)·S_{≥X₀}(s), with W = ((1+κ)^s − 1)/(sℓ_κ). So
  Z_B = Z_∞ + X₀^{1−s}/(s−1) − W·S_{≥X₀} + O(boundary). Checked.
- **A1.2.** |W| ≤ 6/(κ|t|) for σ ≤ 2, and |S| ≤ Z_∞(σ). At |t| ≥ Γ₁, with log Γ₁ ≥ (1−θ)X₀², and
  log Z_∞(½) ≈ 2X₀^{1/2}/log X₀, this gives |Z_B − Z_∞| ≤ exp(−X₀²/4) on σ ≥ ½. Checked.
- **A1.3 table, re-checked against v2 §2.** Lemma 2.1 uses Z on the δ_k-disc, with
  δ₁ ≤ (18 log X₀ + 3C₁)/X₀² ≪ 1/log²X₀. Lemma 2.2 uses only Z(s*), and 2.3(i) only σ = 1.
  Lemma 2.3(ii) never evaluates Z: its ρ_det part is ≤ 6Z_∞(¾)/(κΓ) ≤ e^{−X₀²/4} on σ ≥ ¾, where
  its ⅛-averaging stays. Theorem 2.4's circle is inside the δ_k-disc (Z_B′ − Z_∞′ tiny by Cauchy).
  So the claim is right, and my §3h strip-shrinking is unnecessary. Near s = 1,
  |Ê| ≤ Cκ(1+|s|)Z_∞(σ), so the residue and A = 1 are untouched.
- **(T1).** |E| ≤ in-flight rigid mass ≤ κx + 1, giving C_{X₀} ≤ κ·exp((1−θ)X₀^{1−θ}log X₀) on
  log x ≤ X₀^{1−θ}log X₀. Beyond that, Rankin gives
  Ψ(2x, X₀) ≤ (2x)^θ∏_{p<X₀}(1 − p^{−θ})^{−1} ≤ (2x)^θ·exp(X₀^{1−θ}/((1−θ)log X₀)).
  - That is C_{X₀}x^θ, **not "≤ x^θ"** as A1.6 writes. The constant is finite either way, which is
    all Q needs.
- **(N3) LP against T (gap-G3 §9.6 C2) is optimistic about the threshold.**
  - Landau's lemma in LP Step 4 uses discs of radius (1−θ′)/2. There T̂ ∋ Ê ≈ S·(1 − W) has size
    Z_∞((1+θ′)/2) ≈ exp(X₀^{(1−θ′)/2}). So the radius must shrink to ≍ 1/log X₀, where
    Z_∞ ≤ e·Z_∞(1).
  - Landau's lemma then gives c ∝ r ∝ 1/log X₀, and log X_LP ≍ (log X₀·log log)²/c². That is not
    "((8 log log X_LP + 7 + O(log log X₀))/c)²".
  - This is **not circular**: the crude or Saias-weighted handling of μ₀ (and of N1's −κ/2) covers
    log x ≲ X₀^{5/24}, far beyond X_LP(X₀).
  - But v2 §0.4's requirement "X₀ ≥ X_LP" must be restated as "LP is used only above X_LP(X₀)",
    with the overlap stated.

### Claim 5: are both base-range windows removed under G?

**Yes, conditionally.**
- **R1′-int.** The drift becomes h ≥ (1 − η)/log x − |ρ_osc| − |(1+K)^{−1}μ| − |Ke| ≥ 0.8/log x at
  every x ≥ X₀ + H. The fresh-prime term is a κx-window of rational primes (Heath-Brown/Huxley
  range), so the x^{θ/2}-window obstruction is gone. On [X₀, 2X₀), Comp_jit = 0.
- **R1′-echo.** It needs a seed: large base-range ν from prime-free stretches. With the drift at
  every scale ≥ X₀ + H, the induction keeps Q ≤ B, so stretches are ≤ BL and ν stays small everywhere.
  - The echo of that small ν is controlled by the Saias weights (Σ_v log v·sup|ν(v)| ≪ c′, independent
    of x).
  - gap-G3 §9.8's ρ(log x/log v − 1) tail weight is false (A2.3(b), and my §8 on B's weight claim),
    but it is not needed.
  - So the tower has no seed, and the hard greedy suffices. S(ε) is unnecessary.
- **Conditions for removing both windows:**
  - A2.3(c)(i) Beurling–Saias for the realised semigroup;
  - A2.3(c)(ii) the sharp-plus-Δ treatment (or M-op);
  - A2.3(c)(iii) NV small q;
  - the μ₀ and κ/2 (N1) smooth-source resolution above X_LP(X₀), plus LP against T with shrunken
    discs (N3), owner gap-localpnt;
  - X_Hux, effective in principle;
  - B's S2 fix (Tijdeman sparsity of 𝒟 in SM at large scales), together with CL/SM [S] and B's G2,
    which are not specific to B-lin.

**Net.** B-lin turns the base range from a beyond-RH obstruction into a theorem-backed statement
(Heath-Brown 1988) plus bookkeeping. I now rank it **first** among the repair candidates, ahead of
S(ε) and the randomised base (§5). The remaining blockers for Theorem A are the G2-R repair
(A2.3(c)), gap-localpnt's smooth resolution and LP-against-T items, and the [S] lemmas.

---

## §10 Two targeted checks: dropping the lag row (A13.2), and μ₀ below X_LP^{B-lin}

### §10.1 Dropping the e^{4915} lag row

**The drop is right, but two statements must change.**
- The e^{4915} row was "H(x)/2 + B + 2 ≤ x^η for all x ≥ X₀", which makes (L-a) hold in x^η form
  uniformly.
- At X₀ = e^{1100}, H(X₀) = e^{392}, while X₀^η ≤ e^{137} for η ≤ ⅛. So |D| ≤ x^η is **false on**
  [X₀, X_η], where X_η solves 8(log log x)² = η log x (log X_η ≈ 4·10³ at θ = ¼).

The uses of |D| that I found, and their status:
- **Lemma 2.2.** It uses |D| ≤ x^η only for x ≥ x_k ≥ x₁ ≫ X_η. Fine.
- **Lemma 2.3(ii).** It needs Σ_{N≥X₀ dyadic} K(N)N^{−1/2} ≪ 1, with K(N) ≤ 2 sup|D| + 8 ≈ H(N).
  H(N)N^{−1/2} decreases once 16 log log N/log N < ½, which holds at log N ≥ 1100. So the sum is
  ≈ e^{392−550} = e^{−158}. The N ≥ Γ blocks live at N ≈ x_k, where the x^η form holds. Fine. This
  is my §3h(iv).
- **LP's (H_y).** θ′ = max(θ + 0.01, θ′_H(X₀)) already absorbs H/2 ≤ u^{θ′} (θ′_H(e^{1100}) = 0.362).
  Fine.
- **CL (F3) and SM's Chebyshev input.** They need ∫(B + H)t^{−2} ≈ H(X₀)/X₀ = e^{−708}, and
  H(s) ≤ s/log²s. Fine.
- **§2's continuation of ζ_P to σ > θ.** D̂ over [X₀, X_η] is entire, and beyond X_η the x^η form
  holds. Fine.

**The two statements that must change.**
1. **(L-a) in v2 §2** must read: |D(x)| ≤ x^η for x ≥ X_η, and |D(x)| ≤ H(x)/2 + B + 2 ≤ x^{θ′_H} on
   [X₀, X_η].
2. **Theorem A(i)'s "+ x^η"** becomes "+ C′x^η", with C′ := sup_{[X₀,X_η]} x^{θ′_H − η} finite. So Q
   still gets exponent max(θ, η) < ½, with a larger constant.

I found **no other use** of the lag condition in v2 or the addendum. Both C2 (H ≤ y/8) and the
causality bound s_j > 2H + 4 are trivial.

### §10.2 μ₀ below X_LP^{B-lin}: what is actually needed

**Neither M^fuzz nor the Saias-weighted bridge is needed for μ₀ below X_LP^{B-lin}.** Lemma M
(sharp) plus a plain sup-norm Neumann series for Δ := K_op − K_sh suffices.
- **Δ is small in sup-norm, uniformly in scale.**
  - ‖Δ‖_∞ ≤ sup_x Σ_{near w} 1/w, because each near-threshold term is a difference of averages of
    f, which is ≤ (1/w)·sup|f|.
  - The near-threshold weight is ≲ Σ_{p₀≥X₀} H(p₀)ρ(u_{p₀})/(p₀ log p₀) ≤ C·H(X₀)/(X₀ log X₀)
    (B's M7, my §3b(3)). That is ≈ e^{392−1100−7} = e^{−715} at X₀ = e^{1100}.
- **The Neumann series converges.**
  (1 + K_op)^{−1} = Σ_j [−(1+K_sh)^{−1}Δ]^j (1+K_sh)^{−1} converges in sup-norm while
  (1 + log x)·e^{−715} < 1, i.e. log x ≲ e^{715}. Then
  ‖(1 + K_op)^{−1}‖_∞ ≤ 2(1 + log x).
- **The bound on μ₀.**
  - |(1+K_op)^{−1}μ₀(x)| ≤ 2(1 + log x)·sup_{u≤x}|μ₀(u)|.
  - **Correction to A13.1.** sup_u|μ₀(u)| is attained at u ≈ X₀, where μ₀ ≈ κe^γ log X₀/log u ≈ κe^γ.
    It is not κe^γ log X₀/L at the current scale. That is the F1 slip again, on a smooth source.
  - So the sup-norm bound is ≤ c′/(8L) for log x ≲ (c′/(16κe^γ))^{1/2} ≈ e^{226}, **not e^{430}**.
  - With Saias weights the range would be ≈ e^{446}, but it is not needed.
  - Either range covers log x ≤ log X_LP^{B-lin} ≈ 2.6·10⁸ ≈ e^{19.4}, with enormous room.
  - The N1 constant source −κ/2 (if log-normalised) obeys the same bound. N2 is relative O(κ).
- **Above X_LP^{B-lin}.** μ₀ and the κ/2 source sit inside T′. So they are inside LP⁺'s window
  averages of ρ_ref (gap-localPNT (6.1) with the actual margin) and need no separate resolvent bound.
- **What the weighted bridge (A2.3 (v)) is really needed for:** the pointwise transfer
  ρ^{sh} → ρ^{op} (R(δ), G1′) and G2-R at log x ≳ e^{715}. That includes every designed-zero scale,
  since log x₁ ≥ e^{2200}. It is not needed for μ₀ below X_LP^{B-lin}.
- **M^fuzz** (a scalar fractional-weight model, [P sketch]) is not the compensator's operator form
  anyway. It can stay unused. gap-g3's dependency should read "Lemma M (sharp) + sup-norm Neumann
  for Δ (‖Δ‖_∞ ≲ H(X₀)/(X₀ log X₀))", not "M^fuzz or the bridge".
- **Caveat.** This needs the operator of the exact margin identity to be K_sh + Δ, with Δ supported
  on near-threshold cofactors. That is B's G2, still open.

---

## §11 Targeted review: Lemma BS and per-scale NV (gap-localPNT §6.9, §6.9.5–6.9.7; addendum A17–A18)

**Verdict.**
- **Lemma BS** has a correct architecture, and the parts I checked are right: the recursion, the
  Jacobian, the critical fixed point, and why the exponent is exactly 1.
  - Its hypothesis must be restated as Chebyshev/Mertens bounds. A17.3 is right about this, and one
    line of §6.9.3(d) is false under B-lin.
  - The Z2/Z3 junction is a genuine but routine gap. The standard repair is outlined below.
- **Per-scale NV** is correct. The budget arithmetic undercounts slightly (harmlessly), and (SW) is
  ≈ e^{−175}, not ≤ e^{−200}.
- **(6.1) via η_SW** is correct for the *sharp* renewal. For the operator-valued compensator it still
  needs item (ii)/(v), and I give a short route below.
- Pointwise G1′ stands modulo those items.

### §11.1 Lemma BS

- **(a) The recursion is correct.**
  - If n is t-dense with p = P⁺(n), then m = n/p is t-dense, P⁺(m) < p, and p ≤ tm. The m-range
    (Y/p, 2Y/p] is a single dyadic block, so Fubini is exact.
  - Dropping p ≤ tm except through p ≤ √(2tY) gives an upper bound.
  - Primes n = p ∈ (Y, 2Y] are not t-dense for Y ≥ t, so m ≥ 2.
  - Base case: for ℓ′ < τ, W ≤ Σ_{(Y′,2Y′]}1/n ≤ log 2 + o(1).
- **(b) Log variables are correct.**
  - With σ = log p, w = (ℓ−σ)/σ, ℓ′ = ℓw/(1+w), u′ = w, one has dσ/σ = dw/(1+w).
  - The normalisation ratio max(1, ℓ/τ)/max(1, ℓ′/τ) is (1+w)/w when ℓ′ ≥ τ, and smaller
    otherwise. So the measure is ≤ dw/w.
  - Constraints: p < z ⟺ w > u − 1; p ≤ tm ⟺ σ ≤ (ℓ+τ)/2 ⟺ w ≥ w₁ = (ℓ−τ)/(ℓ+τ).
- **(c) The fixed point is right, with one wording fix.**
  - ∫_a^∞ρ(w−1)dw/w = ρ(a) for a ≥ 1: both sides have derivative −ρ(a−1)/a and vanish at ∞. So
    g(u) = ρ(u−1) is an exact fixed point for u ≥ 2, under the convention g ≡ 1 on [0, 2].
  - For u < 2 the recursion returns 1 + log(1/max(u−1, w₁)) ≤ 1 + log(1/w₁) = 1 + 2τ/ℓ + O(τ³/ℓ³).
    On (1 + w₁, 2) it is strictly between 1 and that. "∫_{w₁}^∞" should read ∫_{max(u−1,w₁)}^∞.
  - The u < 2 branch has w ≤ 1, i.e. ℓ′ ≤ ℓ/2, so the boundary factors multiply along halvings:
    ∏_j(1 + 2τ2^j/ℓ) ≤ e⁴.
  - The Z1 errors CK′_M(1+w)/ℓ sum along halvings to O(K_M/τ).
  - Steps with u ≥ 2 lose nothing at ε = 0. **Hence the exponent of log Y is exactly 1.** Correct.
- **(d) Prime inputs.**
  - §6.9.3(d)'s line "for x/a > X₀ the bracket is ≥ −3(x/a)^{θ′}" is **false under B-lin**, because
    N − v carries E with |E(v)| up to κv.
  - A17.3's replacement is right. The bracket is ≥ −3|E(x/a)| − (power-saving terms), and
    |E(v)| ≤ 2κv·min(1, Cρ̃(log v/log X₀)). Integrated against dψ(a), the ρ-decay concentrates the
    weight on log(x/a) ≍ log X₀, giving O(κx log X₀). So C_ψ ≤ 1.4 + O(κ log X₀), and likewise
    K_M ≈ 3.2 + O(κ log X₀).
  - Mertens' Σ_{p≤e^σ}1/p = log σ + M + O(K′_M/σ) follows from S(z) = log z + O(K_M) by partial
    summation, with M absorbing ∫R dv/(v log²v).
  - Below X₀, the Rosser–Schoenfeld input holds.
  - **So BS holds with the hypothesis "C_ψ ≤ 1.5, |S(z) − log z| ≤ K_M + 1 on [1, Y], ℕ below X₀"**,
    as A10 item 88 proposes. Adopt that formulation.
- **(e) Zones.**
  - *Z1:* correct.
  - *Z2 "[P to leading order]".* The omitted second-order term comes from the spread of the
    w-integral around u − 1. That spread has width ≍ 1/log u, because ρ(w−1) decays like e^{−v log u}
    in w = u − 1 + v. Combined with ∂_wA ≈ 3Bu² log u/ℓ, it is relative O(Bu²/ℓ). That is smaller
    than the increment 2Bu² log(2+u)/ℓ by a factor ≍ 1/log u, and is absorbed by B := 3K′_M. Fine,
    but write it.
  - *Z2/Z3 junction (the GAP).* The issue is real: crude Rankin exceeds ρ(w−1) by e^{(C₁+1)w log log w}
    at w ≈ ℓ^{1/4}, so feeding Z3 into Z2's ρ·e^A profile fails as written. I see a standard fix:
    1. **In Z3, replace crude Rankin by the de Bruijn-type Rankin bound.** Use σ = 1 − ξ(u)/log y,
       ξ ≈ log(u log u). It gives
       Σ_{n∈(Y,2Y], P⁺≤Y^{1/u}}1/n ≤ C·exp(−u(log u + log log u − 1 + o(1))) = ρ(u)e^{O(u)}.
       It needs only *upper* Chebyshev bounds for Σ_{p≤y}p^{−σ} with σ < 1, which hold for 𝒩 via C_ψ.
    2. **On u ∈ [½ℓ^{1/4}, 2ℓ^{1/4}], use the intermediate profile g̃ = ρ(u−1)e^{Cu}.** It has slack:
       ∫_{u−1}^∞ρ(w−1)e^{Cw}dw/w ≈ ρ(u−1)e^{C(u−1)}, a gain of e^{−C} per step. That absorbs the Z2
       errors and the junction mismatch.
    3. **Check that the profiles match.**
       - Lower edge: e^{A} ≤ e^{Cu}, since A = O(Bu³ log u/ℓ) = O(Bℓ^{−1/4}log ℓ)·u.
       - Upper edge: de Bruijn's ρ(u)e^{O(u)} ≤ ρ(u−1)e^{Cu} for C large.
    4. **Feedback into Z1** is ≤ ∫_{w≈ℓ^{1/4}} ρ(w−1)e^{Cw} ≈ e^{−ℓ^{1/4}log ℓ/5}, which is summable.

    So I rate the junction as technical, not structural, and BS as **[P mod a routine lemma]**. It
    should be written before it is tagged [P].
- **(f) Numerics.**
  - C_BS ≈ 3.55 in the pessimistic continuous model, and 1.69 without errors, is consistent.
  - On ℕ the ratio is ≈ 1.15 (lead).
  - My `chi_density.py` gives W·log N/log u ≈ 0.25–0.62 in the regime u ≪ N.
  - These are model checks of the recursion, not of realised counts.

### §11.2 Per-scale NV (§6.9.5)

- **G_u frozen at 2u: correct.**
  - Mart(W) for W ⊂ [u, 2u] involves latest primes ≤ u and their jitters, which are decided at slots
    ≤ u + H(u). V_W is predictable.
  - E_cl(u) concerns elements in [u, 2u].
  - So G_u ∈ σ(decisions at slots ≤ 2u).
  - Minor: windows at u′ ∈ [u, 2u] should have length H(u′) (a family), not H(u).
- **Budget: right in conclusion, slightly undercounted.**
  - Freedman with a *random* predictable variance needs peeling over ≲ log(M₁H(u)) dyadic levels of V.
  - The window positions need a unit grid plus a monotonicity step.
  - Both tails count.
  - So P(G_u^c) ≲ 8 log(M₁H(u))·u^{−2}(log u)^{−2} + P(E_cl(u)^c), not 2u^{−2}(log u)^{−2}. The sum
    over dyadic u ≥ X₀ is still ≪ X₀^{−1}.
- **(SW): ≈ e^{−175}, not ≤ e^{−200}.**
  - I summed log(2u)·√(4M₁(u)λ(u)/H(u)) exactly over dyadic u ≥ e^{1100}. The first term is
    e^{−181.7} and the sum is e^{−178.3}.
  - The sum is dominated by ≈ 30 dyadic scales near X₀, because H grows only by e^{0.07} per doubling
    there.
  - With C·C_BS ≈ 10–40 the sum is ≈ e^{−175}. That is still ≪ c′/8, so it is harmless.
  - The ΔQ/H and S1 terms are e^{−370} and X₀^{−0.4}.
- **B's §12 (window H/2, triangular jitter).** I did not check it. It changes ν̄ by a factor √2 and
  does not affect the per-scale structure. It bears on B's G2 (exactness of the margin identity),
  which remains open in my list.

### §11.3 (6.1) via η_SW, and pointwise G1′

- **For the sharp renewal, η_SW is correct.**
  - c_n(u) = μ(n)χ_u(n), and K_r e involves ν only at scales ≤ u/2.
  - BS weighting gives log u·|K_r e(u)| ≤ C·C_BS Σ_{v≤√u} log(2v)ν̄(v) + C log²u·ν̄(√u).
  - This is uniformly small in u. So η₁ → 0 is restored.
- **For the operator-valued compensator,** (6.1)'s K_r is "taken with the exact filter", which is
  operator-valued. So the Saias weighting needs item (ii)/(v).
  - Besides fix-bprime's operator dyadic weight, the Neumann route of my §10.2 also works in
    weighted form. Write
    (1+K_op)^{−1} = (1+K_sh)^{−1}Σ_{j≥0}(−Δ(1+K_sh)^{−1})^j.
    The j = 0 term is the BS-weighted bound.
  - For j ≥ 1, Δ acts on g := (1+K_sh)^{−1}ν, with |g(v)| ≤ η_SW(v)/log v. The output at scale w is
    ≲ (near-threshold weight at w)·sup|g|. That weight is
    ≲ Σ_{p₀≥w^{1/A}} H(p₀)ρ(u_{p₀})/(p₀ log p₀) ≤ e^{−715}, and it decays super-polynomially in w.
  - So every j ≥ 1 term is Saias-summable and ≤ e^{−800}/log x, uniformly in x.
  - The one lemma to write is this weighted near-threshold weight bound, with the smoothness factor
    ρ(u_{p₀}).
- **Pointwise G1′ (§6.4) stands, given:**
  - BS, including the junction;
  - the operator transfer, for the bridge step 1 and for (6.1), by fix-bprime or the Δ-route above;
  - B's G2/§12, the margin identity's exact operator and window.

  Below X_LP^{B-lin}, G1′ comes from Huxley (my §9) and is unaffected.

---

## §12 Re-check of Lemma BS, complete write-out (gap-localPNT §6.9.3′)

**Verdict.** BS is **[P mod one remainder lemma]**, plus the usual [P-CA] caveats. The ℓ > 10³⁰
remainder *can* be closed cheaply, but **not with the bound as displayed**: that bound has the
wrong exponent, and it is compared against the wrong quantity. The fix is a ratio-form estimate,
given in §12.4.

### §12.1 Lemma CM and the hypothesis (A), (A′): [P], and my objection is answered

- (H_BS) only asks |N − ⌊·⌋| ≤ ε₁v above X₀, through η₁ and η₂.
- **Chebyshev.** The ℕ-bracket ⌊v⌋ − 2⌊v/2⌋ ≥ 1_{[1,2)} gives ψ(x) − ψ(x/2) ≤ T(x) − 2T(x/2) + (E₁-terms).
  - The log-integral of dE₁, by parts, is ≤ 3x(η₂ + sup ε₁).
  - ∫|E₁(x/a)|dψ is ≤ 1.42xε₁ per dyadic a-block, so ≤ 1.42η₁x in total.
  - Hence 0.71x. Checked.
  - No power saving is used, so **my "−3(x/a)^{θ′}" objection is answered.**
- **Mertens.** (CM1) is a correct rearrangement of ∫log v dN = ∫N(x/a)dψ(a). Stirling plus
  0 ≤ ∫{x/a}dψ ≤ 1.42x gives S − log x ∈ [−1.004, 0.424].
- **(iv).** The partial summation range/σ bound is right: the constant part of E_p cancels between
  the two terms.
- **The local form (A′).** It uses no tail integral and only N|_{[1,x]}. Correct and needed.
- **Under B-lin and 𝒜,** η₁, η₂ = O(κ log X₀) + O(Σ_dyadic v^{−0.005}), which is negligible.

### §12.2 The ρ-facts (B) and Lemma V (C)

- **(R1)** is correct, including ∫_{u−1}^u ρ(w−1)(u−w)dw/w = ρ(u−1) − uρ(u). I derived it from the
  other two identities.
- **(R2), log-concavity.** The argument is correct.
  - On [1, 2], r is increasing, because v(1 − log v) is decreasing.
  - For v > 2, r = 1/I. The first-failure point v* would force I′(v*) < 0, hence r′(v*) > 0, a
    contradiction. This includes v* = 2⁺.
- **(R3)** follows from (R2).
- **(R4)** is right, but the route is not the one the note's one-liner suggests.
  - vρ(v) ≥ δρ(v−1+δ) gives exp(∫_{v−1+δ}^v r) ≤ v/δ, so (1−δ)r(v−1+δ) ≤ log(v/δ).
  - Bounding r(v) ≤ e^{δr}/δ instead is circular. State the correct derivation.
- **Lemma V.**
  - The Hildebrand identity is exact on dyadic windows in the free semigroup.
  - The partial summation ≤ ∫F + 2K_M F(L) holds for increasing F.
  - The u > 3000 slack/excess comparison is correct, with r(u) ≤ log u + log log u + 2.
  - **Caveat on the [P-CA] part.** The max ratio is 0.9985, a margin of 0.15%. That contradicts the
    preamble's "margins ≥ 10%" against ρ-table errors of 10⁻³. State where the max is attained.
    - If it is at u ≤ 2, where ρ is explicit, there is no issue.
    - Otherwise use exact ρ (the integral equation, with interval bounds) there.

### §12.3 (D)–(H): structure correct; [P-CA] coverage needs four sentences

- **Correct and checked:**
  - the discretisation (D1), where the f(σ_J) cancellation by parts is valid;
  - D2's terms;
  - the Φ-factor identity 1/m − 1/ℓ = 1/(wℓ);
  - the base region (F), using the convexity of (ℓ/τ)e^{κ_Φ/ℓ};
  - the tail (G). e^{a(U)} = e²ℓ/τ cancels the dropped density factor ℓ/τ, which is a nice
    implementation of the junction inflation.
- **The coverage of the computer checks should be stated:**
  1. Grid to continuum in u. ℓΣ is smooth in u, and the minima are ≥ 834, far from 0. One Lipschitz
     bound per zone suffices.
  2. Sparse ℓ grid (×3 steps). Interpolation in ℓ is justified by the same first-order ℓ-invariance
     as §12.4, so it inherits that lemma.
  3. **τ > 10⁸.** τ = log(2u) is unbounded. The dominant u < 2 terms (ℓμ₀ ≈ 2τ, κ_Φ j_Φ ≈ 4τ j_Φ) are
     linear in τ, so c(u)/τ has a τ → ∞ limit profile. Say so, and check the limit.
  4. No interval arithmetic.
- **C_BS is regime-dependent.** C_BS = C₀·max(e^{4+1500/τ}, (ℓ₁/τ)e^{κ_Φ/ℓ₁}) is ≈ 38 only for
  τ ≳ 2·10⁴ (where 10⁶/τ ≤ e⁴). Under A13.2's X₀ = e^{1100}, BS is applied down to τ ≈ 1100, where
  ℓ₁/τ = 10⁶/1100 gives **C_BS ≈ 640 (and C_S ≈ 1300)**. (SW) is still e^{−175}·640, which is
  negligible. But "≈ 38 canonical" should be tied to the regime.

### §12.4 The ℓ > 10³⁰ remainder: the displayed bound fails, and a ratio form closes it

- **What is written.** "|R| ≲ (B²/ℓ²)U⁶log²U + (U−u₀)²/ℓ + E₃ = O(ℓ^{−5/4}log³ℓ)", compared with
  c_min ≥ 834.
- **Why that fails.**
  - U ≈ ℓ^{1/4}(1 + √(2 log(ℓ/τ) + 4)), so (B²/ℓ²)U⁶log²U ≍ B²ℓ^{−1/2}log⁵ℓ, **not ℓ^{−5/4}**.
  - Then ℓ|R| ≍ ℓ^{1/2}log⁵ℓ ≫ 834. As an *absolute* bound against c_min it does not close.
  - The culprit is the sup over w ≤ U(m) of d(u,w)². At small u that sup is dominated by w ≈ U,
    where the weight ρ(w−1)/ρ(u−1) is astronomically small.
- **What does close it: a u-dependent ratio bound.**
  - On the support, the leading u³ terms of Q(m,w) and Q(ℓ,u) cancel. With w = u − 1 + v:
    D(w) = (B/ℓ)·[−2u² log u + 3u² log u·v + O(u log u (1+v)²)] − κ_Φ/(wℓ) + (a-terms).
  - By (R3), ρ(w−1)/ρ(u−1) ≤ e^{−r(u−1)v}. So
    ∫ρ(w−1)/ρ(u−1)·D²e^{D₊}dw/w ≤ C₂B²u⁴log²u/ℓ²·(1 + O(1/r)).
    Here e^{D₊} ≤ exp(BU³log U/ℓ) ≤ 1 + 10⁻⁶ for ℓ ≥ 10³⁰.
  - The first-order slack at u ≥ 2 is c(u)/ℓ ≥ c₃Bu² log u/ℓ, from c(u)/u² → B(2 − 3/r)log u − 2K′r.
  - **So remainder/slack ≤ (C₂B/c₃)·u² log u/ℓ ≤ (C₂B/c₃)·U² log U/ℓ ≍ ℓ^{−1/2}log²ℓ**, uniformly in
    u ∈ [2, U].
  - For u < 2, the remainder is O(B²/ℓ²), against c ≥ 834/ℓ.
  - The same ratio form handles:
    - the a-terms (second order (1+w)²|∂_wa|/ℓ against the a-slack a′(1 − 1/r − 7/12): ratio
      ≲ U²/ℓ);
    - E₃ (κ_Φ/m², |∂_mQ| and (1+w)²|∂_wQ|/ℓ, each ≲ U²·polylog/ℓ relative to its first-order term).
  - At ℓ ≥ 10³⁰, ℓ^{−1/2}log²ℓ ≈ 5·10⁻¹², so even C₂ ~ 10³ leaves a margin of 10⁸. The constants
    C₂ and c₃ need only crude explicit values. This is a page of bookkeeping, not new mathematics.
- **One more item for ℓ > 10³⁰: c(u) ≥ 0 beyond the CA range.**
  - The checks reach u ≤ U(10³⁰) ≈ 4·10⁸. For larger u, the asymptotic c(u)/u² → B(2 − 3/r)log u − 2K′r
    needs explicit error terms. Use (R4), r ≤ log u + log log u + 2, and an explicit expansion of j_A.
  - Since B = 5K′, the leading term is ≥ (22 − 4.4 − o(1))log u. Cheap.

**Bottom line.** Lemma BS is [P] modulo:
- (a) the ratio-form remainder lemma of §12.4 (cheap);
- (b) explicit asymptotics of c(u) for u > 4·10⁸ (cheap);
- (c) the [P-CA] coverage statements of §12.3, including the location of Lemma V's 0.15% margin.

None of these threatens the result. The constants are C_BS ≈ 38 for τ ≳ 2·10⁴ and ≈ 640 at
τ ≈ 1100.

---

## §13 Targeted review: fix-Bprime §10 (Participation, tree case, Participation⁺, TCL-poly)

**Verdict.**
- Participation, Participation⁺, the change of variables with corner maximisation, and TCL-poly are
  correct.
- Your free-prime question: the tree case is the β_f = 1, no-sharing case, so verify-CL's LBS caveat
  does not bite. The write-up needs the latest-first sure-pull step spelled out, though.
- Two new problems:
  - **(T1) Λ_A is not automatic on the whole closing range.** Only the margin-critical ranks were
    checked. Large feasible ranks are not [P].
  - **(T2) Regime conflict.** Every number in §10 assumes log X₀ = 10⁸. Under A13.2's X₀ = e^{1100}
    the tree case fails at every L I tested.
- M₁ ≤ 2H^{1/2} is tolerated (in fact M₁ ≤ 1.26H^{1/2}).

### §13.1 Participation Lemma (§10.2): [P]

- **Existence.** If N(J) ≥ r₀ + H^{1/2} + r₀² and rank < r₀, the full span has
  κ ≥ φ(rank). Minimal elements exist in the finite family.
- **The proof checks.** If U := span(extras) had dim U ≤ r − 1, then
  κ(U) ≥ φ(r) + r − r − dim U ≥ φ(r) − (r − 1) = H^{1/2} + r(r−1)/2 + 1 > φ(r − 1) ≥ φ(dim U),
  a contradiction. So the extras span V, and an invertible α-submatrix exists with no zero column.
- **Distinct extras have distinct α.** Equal α means equal jittered part Q ≥ X₀, so d ∈ J/Q has length < 1.
  This is B §15.2's retraction, and Participation⁺'s count uses it.

### §13.2 Tree bound (§10.3)

- **Integrality.** Disjoint squarefree supports force α ∈ ℤ_{≥0}^r and m_y ≥ 2. m_y = 1 forces equal
  jittered part, hence y = n_i. Checked.
- **Tail relation (10.3a).** It follows from M_y = ∏M_i^{α_i}. Checked.
- **Box corner: valid.** The bound only *enlarges* the sum, in three ways, so the maximisation is a
  legitimate upper bound:
  1. The extras' tails N_k range over all integers ≥ 1, not over X₀-smooth ones.
  2. The extras' caps d_y ≤ z/X₀^{m_y} are dropped. Only u ≥ 0 and v ∈ [0, log Y]^r are kept, and these
     already give u ≤ L.
  3. Every column of A is ≥ 1 entrywise-summed, so s − 𝟙 ≥ 0. The maximum is therefore at the corner
     v = log Y·𝟙. That corner is feasible: u_k = L − m_k log(X₀/2) ≥ 0, since m_k ≤ D.

  The value (2/X₀)^{𝟙ᵀm − r} checks.
- **A cleaner volume step.** Write Σ_N e^{−𝟙ᵀv(N)} = Σ_N F(N)/∏N_k ≤ max F·Σ_{N≤e^L}∏1/N_k ≤ (1+L)^r·max F.
  This needs no smoothness and avoids the "C^r overcount near u = 0" remark, which is shaky when A is
  ill-conditioned.
- **Λ_A** = ∏(1 + w_id_i) with w_i ≤ 2‖A^{−1}‖(D+1)ε, plus Hadamard. Correct as stated.
- **Free primes (verify-CL R.6 / LBS).**
  - In a tree basis each free prime lies in exactly one basis element's jittered part. Extras are
    never integrated, and their constraints 1[d_{y_k} ∈ ℤ] depend only on (z₀, d) up to O(ε).
  - So every free prime has β_f = 1 and no sharing. That is precisely verify-CL R.8(b)'s sufficient
    case: "(F4) + telescoping, summed per element".
  - The LBS caveat (β_f < 1, as in R a b / R a c / R e) needs *shared* free primes, which disjoint
    supports exclude.
  - **But (10.3b)'s one line "harmonic sums ≤ (log L)^{#free}" is not the proof.** Process payers
    latest-first. Before integrating payer q_j, pull out any free prime f of another element i
    decided after q_j by the sure local Mertens bound (gap-localPNT (A′), K′ = 2.20), carrying the
    pending e^{±E} factors so that they telescope (R.8(b)). State this.
  - Also **#free ≤ rD, so the factor is (log L)^{rD}, not (CL)^{Cr}.** At log X₀ = 10⁸ this is
    harmless (rD log log L ≈ 10¹¹ against gains ≈ 10¹⁵). It is not harmless at small X₀ (§13.5).

### §13.3 Participation⁺ (§10.7): [P], and the numerics re-checked

- **The inequality.** #(S∩V∖W) ≥ Q + r + 1 for every hyperplane W. Proof: S ∩ W = S ∩ span(S∩W),
  minimality gives < φ(r−1) + r − 1, and φ(r) − φ(r−1) = Q + r. Checked.
- **High-degree extras span.** Extras of degree ≤ m₀ number < binom(m₀+r, r) < Q, so some extra of
  degree > m₀ lies outside W. Hence Σm_k − r ≥ r·m₀(r). Checked.
- **Independent numeric re-check** (`/tmp/rhscratch/referee2/treegain_check.py`). Criterion:
  r·m₀·log(X₀/2) ≥ L − 6(r−1)log L + r log(C(L+1)) + rD log log L + 4 log L, with C = 10,
  Q = H^{1/2}/(4r₀), r₀ = L/(3 log L), worst feasible r.
  - At log X₀ = 10⁸ the margin is +1.7·10¹⁴ at L = 10¹⁵ and −3.6·10¹² at L = 1.2·10¹⁵.
  - So the crossover is ≈ 1.1·10¹⁵, **not "≤ 1.2·10¹⁵"**. That is borderline, and well within the
    slop of C.
  - The worst ranks are r ≈ 3.4·10³, m₀ ≈ 3.5·10³, which agrees with §10.7.

### §13.4 (T1) Λ_A is not automatic on the whole closing range

- §10.7 says "the worst ranks are r ≈ 1.6–3.5·10³ … so Λ_A is automatic there". But those are the
  ranks critical for the *gain margin*.
- Feasible ranks run up to r₀ ≈ L/(3 log L), about 10¹³ at L = 10¹⁵.
- The basis cost alone (δ^{r−1}) suffices only for r ≳ L/(5 log L).
- Λ_A is [P] only for r·log(D√r) ≤ 0.99 log X₀, i.e. **r ≲ 4·10⁶**. That is §10.3's own condition.
- For larger r, log Λ_A ≈ r·[(r−1)log(D√r) − log X₀]₊ grows *quadratically* in r, while the gain
  r·m₀(r)·log X₀ grows linearly, and m₀(r) even decreases.
- At L ≈ 10¹⁵ the gain still wins at r = 10⁹ (2.6·10¹⁰ against 3.2·10¹⁰ per unit r), but loses from
  r ≈ 3·10⁹ on.
- So ranks r ∈ [≈3·10⁹, L/(5 log L)] are **not covered**, and r ∈ [4·10⁶, 3·10⁹] are covered only via
  the explicit Hadamard comparison, which §10 does not do.
- **Possible fixes:**
  - choose a well-conditioned set of extras;
  - change variables on only r′ ≈ 2L/(m₀ log X₀) tails, using an invertible r′×r′ minor, and sum the
    remaining tails harmonically at cost (log Y)^{r−r′};
  - §10.6's sequential count.

  All look feasible, but none is written. Until then, mark the tree case
  **[P for r ≲ 4·10⁶; S beyond]** at every L.

### §13.5 (T2) Regime conflict, and the M₁ tolerance

- **M₁ ≤ H^{1/2} + r₀Q + r₀² ≤ 1.26H^{1/2}** with Q = H^{1/2}/(4r₀). So the "factor 2" is in fact 1.26.
  - gap-G3 §16.1's tolerance, with B §15.1's corrected binding conditions (M₁ ≤ H/L^{13.5} for the
    (SW)/BRG sums; Lemma P needs L ≳ 2.5·10⁷ at M₁ = H^{1/2} and ≳ 5·10⁷ at M₁ = H), is met with
    vast room.
  - B ≈ 21M₁L² ≈ 26H^{1/2}L², and (L-a) stays in quasi-polylog/x^η form. **Tolerated.**
- **But all of this, and §10, assumes log X₀ ≥ 10⁸.**
  - At A13.2's proposed **X₀ = e^{1100}**, my re-check gives the tree case **failing at every
    L ∈ [10¹¹, 10¹⁶]**: margins −10¹⁷ to −10²⁷. The reason is that D = L/1100 makes the feasible ranks
    huge and m₀ tiny.
  - Lemma P's L ≳ 2.5·10⁷ condition also fails on [1100, 2.5·10⁷].
  - Fix-Bprime's Prop. 9 constants are quoted as e^{−(10⁸−…)}.
- **So the lowering of X₀ in A13.2 (my §10.1 checked only the lag row) is incompatible with the
  CL/CapL-w chain.** Either keep log X₀ ≥ 10⁸, or re-run every CL-side threshold at e^{1100}.
  §0.4 must state a single regime.

### §13.6 TCL-poly (§10.4): [P]

- B ⊂ S covers P(S): span membership implies support containment.
- For an extra y, nonnegativity gives supp(e_y) ∪ ∪_{I₋}supp = ∪_{I₊}supp.
  - (a) gives |I₋| ≤ 1.
  - (b) gives |I₊| ≤ 2.
- So y ∈ span(T) with |T| ≤ 3. Injective projection to |T| coordinates in [0, D] gives ≤ (D+1)^{|T|}
  vectors per T, and distinct elements have distinct vectors (§13.1).
- The bound r³(D+1)³ follows, and it is < H^{1/2} for r, D ≤ L, L ≥ 5. Correct, and indeed ten lines.

---

## §14 Targeted review: verify-CL §R.9 (Pivot-Integration Lemma, FAC, (S1)–(S3), §11.3, LBS)

**Verdict.**
- **PIL is correct in substance.** As written, its measurability step has one real slip:
  "sup over ω ∈ G_{<z}" is not licensed after a pivot integration. It is fixed by carrying the
  progressive past-good events G_{<s_p} (§14.1).
- **FAC holds** as an upper-bound factorisation, with ε-slack in the caps.
- **(S3)** is right.
- **§11.3 is restored to [P]**, given PIL with that fix.
- **LBS is correctly isolated for the rank-full branch.** It is not the only remaining CL item: the
  Cover Bound's free sums in the rank-deficient branch must be redone in PIL order. The proposed
  shortcut is false as stated.

### §14.1 Measurability: is "sure on G and earlier-measurable" enough?

**Mostly. The step that matters is the pivot integration, not the SUP-SUM.**
- **The SUP-SUM step is fine.**
  - At block F_t the pending Ψ is a nonnegative function of the realised F_t-data and of
    variables decided before F_t's primes. Later pivots are already integrated out, and later blocks
    are already replaced by functions of their own earlier variables.
  - Replacing the realised sum by its sup over all continuations consistent with the earlier
    variables gives a valid pointwise upper bound on the good event. That sup is a deterministic
    function of the earlier variables.
  - Amended PIL also allows carried factors that depend on primes decided before the *next* pivot.
    This is legitimate: such a factor is F_{p−}-measurable at that pivot. The value-order versus
    decision-order fuzz (≤ H + 3 primes in (q−H, q]) costs e^{(H+3)/X₀}, as stated.
- **The pivot step needs the indicator handled explicitly.**
  - E[Ψ(q_p, earlier)·1(G_{<z}) | F_{p−}] ≤ (θ/H)∫Ψ dq_p requires the event multiplying Ψ to be
    F_{p−}-measurable, since U_p must be independent of everything else in the integrand.
  - G_{<z} is not F_{p−}-measurable: it constrains slots between s_p and z.
  - Dropping it (1(G) ≤ 1) is not an option either, because every later step (earlier blocks,
    and the final realised sums over F_r and the tails) uses bounds that are sure only on a good
    event.
  - **Fix**, CL §3's insertion convention made explicit:
    - Use 1(G_{<z}) ≤ 1(G_{<s_{p₁}}) ≤ 1(G_{<s_{p₂}}) ≤ … at successive pivots p₁ (latest), p₂, ….
      G_{<s_p} is F_{p−}-measurable, so U_p is independent of it.
    - Take each SUP-SUM for F_t, whose primes are decided before p_t, as a sup over ω ∈ G_{<s_{p_t}}.
    - Each SUP-SUM then needs its (F3)/(F4) inputs only at values ≤ s_{p_t} + H. Those are sure on
      G_{<s_{p_t}}, because LP/(A′) are pathwise on [1, y] (gap-localPNT (A′)). The final realised
      sums run on G_{<s_{p_r}}.
  - With this, PIL's conclusion E[X_τ 1(G_{<z})] ≤ θ^{|P|}·sup S_τ holds, with the sup taken over the
    progressive events. As written ("sup over ω ∈ G_{<z}" at every block, then E[·|F_{p−}]) the proof
    silently uses a non-adapted indicator.
  - **The same remark applies to every consumer** (§11.3, Theorem R, the Cover Bound): state the
    progressive events once, in PIL.

### §14.2 FAC: holds, as an upper bound

- Greedy latest-first gives e_f ∈ span(columns of the later pivots), and these are independent. So
  v_f is unique.
- Shifting x_f by s and the later pivots by −s·v_f leaves every row's Σ E x invariant. The Lebesgue
  integral over the later pivots, with weight ∏e^{x_p}, picks up e^{−sβ_f}, where β_f = 𝟙ᵀv_f. Checked.
- **Caveat: the caps are not shift-invariant, so FAC is a bound, not an exact identity.**
  - The caps are the later pivots' feasibility (q ≥ X₀, decision-order consistency).
  - Because the window constraints are thin, the integral is (ε-box volume)·∏e^{x_p*}·1(caps at
    x_p*(x_f)) up to ε-slack. The solution x_p* is affine in x_f, so the caps are half-spaces in x_f,
    widened by O(ε).
  - FAC therefore holds as "Ψ ≤ q_f^{−β_f}·1(caps_ε)·Ψ₀". That is all PIL needs.
- For several free primes in one block the factorisation multiplies, by linearity.
- The key consequence is right: late free primes never sit in a thin indicator. Non-greedy pivots
  would break this.

### §14.3 (S1)–(S3)

- **(S1) and (S2)** are immediate from (F3), with Σ_{c≤Y}c^{−β} ≤ Y^{1−β}S(Y) for β ≤ 1, and N(Y) ≤ 2Y.
- **(S3).** Σ over cofactors with primes in a range of 1/c equals ∏(1 − 1/p)^{−1} over those primes
  (all multiplicities). The pieces telescope to Eu(a₀)/Eu(a_m), and (A′) bounds that once:
  ≤ (log a₀/log a_m)e^{2.20/log a_m + 1/X₀}.
  - This also cures verify-CL Item 2 caveat (a): "kL/log X₀ sups" no longer multiply errors.
  - Correct.

### §14.4 Is §11.3 restored? Yes, given §14.1's fix

- **Pivots and frees.** In the compressed trie (latest prime at the root), greedy latest-first picks
  exactly the payers (top edges and non-anchor child edges) as pivots.
  - Pass primes above w have column leaves(w), the same as the later payer entering the chain. So
    they are free, with v = e_payer and **β = 1**: (S1)/(S3).
  - An anchor-edge prime has column leaves(w) − Σ(later non-anchor siblings). So it is free with
    **β = 1 − #sib ≤ 0**, capped by feasibility. Its weight q^{#sib−1} is exactly §11.3(b)'s
    V_w^{m−2} factor, and it is counted by N(Y/V) ≤ 2Y/V. So §11.3's accounting is precisely the
    (S2)/FAC SUP-SUM, in latest-first order. Leaves and tails are early.
- **Item 2 caveats.**
  - (a) is cured by (S3).
  - (b) (same edge prime, different exponents) still needs its written patch, but it is unaffected
    by PIL.
- **So §11.3's bound (95 max(1, 8A/X₀)Aδ)^k stands [P | PIL with progressive G].**

### §14.5 Is LBS the only remaining case? For rank-full CL yes; for CL as a whole no

- **Rank-full branch.** PIL + FAC reduce Theorem R to evaluating S_τ.
  - Pivots-last types: all blocks early, Volume Lemma. Correct.
  - Private-latest types: pivots are the latest primes, each pays its own abs constraint, and (S3)
    chains per element. Correct.
  - What remains is exactly LBS: summing θ^k sup S_τ over general types with late β < 1 cofactors and
    shared late primes, where the sharing pattern must be paid by caps. Correctly isolated.
- **Not the only remaining CL item.**
  - The rank-deficient branch (CapL-w via the Cover Bound, gap-G3 §16.6–16.10) uses free sums
    ("C-row free sums") that are valid only if performed as PIL SUP-SUMs in latest-first order with
    caps (consumer 4: "not read by me").
  - Until that check is done, the Cover Bound is [P | PIL-order check], independently of LBS.
- **The "possible shortcut" is false as stated.** Take n_i = A·f·q_i·d_i (i ≤ k) with decision
  order A > f > q_i, which is verify-CL's own two-element example extended.
  - Any subset of size ≥ 2 shares the latest prime A, so it is not private-latest.
  - Greedy makes A and the q_i pivots, and f free with column 𝟙 = e_A. But f is later than every q_i
    pivot, so no subset of size ≥ 2 is pivots-last.
  - It is a tree (pass prime f), so §11.3 covers it.
  - A valid shortcut must allow **tree** and pivots-last types as well, and needs c ≤ 3 to fit
    M₁ = L/log L + 6 at r₀ = L/(3 log L). This is unproved; do not rely on it.

---

## §15 Targeted review: fix-budget §6–§7 (probability skeleton, paste-ready v3 text)

**Verdict.** This is careful, correct work and can be pasted, after three small corrections and one
pending item:
- the Freedman deviation term λ/3 → 2λ/3 in two places;
- (F3′) should cite the local Mertens bound (CM/(A′)), not LP §3.1's e^{K+γ+1};
- PIL's (S2) counts need the F_{s−}-form;
- the pending item is E3/E3′'s A_E through Prop. 9 (§6.3).

The Good(<t)/first-failure induction is non-circular, and the event times are right. The budget
≤ 1.5/log X₀ is right.

### §15.1 Theorem 4.2′ with λ = 4L (7.1): [P]

- **Freedman form.** P(∃n: S_n ≥ a, V_n ≤ v) ≤ e^{−a²/(2v+2ab/3)} with a = √(2vλ) + 2bλ/3 gives
  exponent ≥ λ. Using it on Good(<t(W)), where V ≤ 2M₁Comp(W) ≤ v_W by R1′ on W, needs no
  predictability of {V ≤ v}. Correct. (a)'s 4M₁λ/3 = 2bλ/3 with b = 2M₁ is right.
- **(b) has the slip.** It states "1 + √(2λ) + λ/3". With b = 1 it should be 1 + √(2λ) + 2λ/3, which is
  still ≤ λ = 4L. Cosmetic.
- **B(x).** max_ℓ(−c′ℓ/L + √(16M₁Lℓ)) = 4M₁L²/c′. Hence B ≈ 26.7M₁L² ≈ 34L³/log L. Checked.
- **Full block.** c′L⁴ ≥ √(16M₁L⁶) + 16M₁L/3 + L³: ratio 2.9 at L = 1100. Checked.
- **The Lindley split** Q_j ≤ max(Q_k + exc(k, j], max_{ℓ<L₀} exc(j−ℓ, j]) with B non-decreasing is
  right. So only ≤ L₀-slot windows are needed, and #𝒲_x ≤ xL₀ gives 2L₀x^{−3}.
- **Dyadic union.** Correct, and correctly insists on dyadic scales: Σ over all x diverges.
  λ = 3L would also be summable, at 2/x per scale. 4L just gives margin.

### §15.2 Landing Lemma L (7.2): accounting checked; one constant slip

- **Candidates.** Selection by decision slot (|s − J| ≤ H(s)/2) is predictable. The landing indicators
  in slot order form a martingale with compensator μ(J).
- **The sure bound** μ ≤ μ̄ = (|J| + H₊ + 2)min(1, |J|/H₋) ≤ (1 + ρ_H)|J| + 2 holds in both cases
  |J| ≤ H₋ and |J| > H₋. A_E = Ω. Correct.
- **Slip.** Two-sided Freedman with b = 1 gives |Λ − μ| ≤ √(2μ̄λ) + **2λ/3**, not λ/3. The exact root is
  λ/3 + √(λ²/9 + 2μ̄λ), which exceeds √(2μ̄λ) + λ/3. Then Λ ≤ 2μ̄ + 7λ/6, not 2μ̄ + λ, and K_loc gains
  λ/3. **The failure probability 2P^{−4} is unchanged.**
- **Local count, re-derived from §8.3's identity N(y) − T(y) = Q_j + (j − T) − C(y, s_{j+1}) − L₊ + L₋.**
  - The pieces: |ΔQ| ≤ B, |ΔC| ≤ B + 1, |Δ(j − T)| ≤ 2.
  - L₊ and L₋ each change by ≤ Λ(J) + #slots(J), counting landings in J plus slots in J.
  - So |N(J) − T(J)| ≤ 2B + 2Λ + 2|J| + 5, and hence (4ρ_H + 6)|J| + 2B(4P) + 2λ_P + 13 + O(λ). Checked.
  - The "11.4|J|" needs ρ_H ≤ 1.35, which holds as stated.
  - B(4P) is correct, because the identity reads queue bounds at slots ≤ max J + H.
  - Minor: under B-lin, T(J) ≤ |J| + 1 + #𝒜(J) ignores the rigid jumps, which locally can add up to
    |J| + 1. Write T(J) ≤ 2|J| + 2 + #𝒜(J); only constants change.
- **Re-deriving was the right call.** §8.3's "μ + λ" form with failure e^{−λ} is indeed false for
  |J| ≈ H, and "given the decisions, independently" conditions on the future.

### §15.3 (F3′) and Lemma CL with a predictable indicator (7.3): fits my §14 fix exactly

- **(F3′) is precisely the progressive-G convention of my §14.1, made concrete.** It replaces
  1(Good(<t_J)) by 1(Good(<s)) ∈ F_{s−} at each peel (monotone, with integrand ≥ 0). It indexes peels
  by decision slot. It bounds harmonic sums over 𝒩_{≺s}, which is F_{s−}-measurable, surely on Good(<s).
  - Both cases check:
    - if Y + H(Y) ≤ s, everything ≤ Y is decided;
    - otherwise the Euler product over primes decided before s splits into those ≤ s − H(s), all
      decided, and ≤ 2H + 1 primes in (s − H, s + H/2], each ≥ X₀.
  - A′ = 1.8(log z + 4) checks: e^γ(log 2z + 3.2) ≤ 1.8(log z + 4).
- **Correction (citation).** The Mertens product for realised primes ≤ s − H should be bounded via
  gap-localPNT Lemma CM (A′): rational primes below X₀ exactly, then
  |Σ_{X₀≤p≤y}1/p − log(log y/log X₀)| ≤ 2.20/log X₀, giving ∏ ≤ e^γ log y·e^{2.2/log X₀ + o(1)}.
  - That is local, and sure on Good(<s).
  - "§3.1(d), K′_M ≈ 3.2" mixes two notes. §3.1 itself gives e^{K+γ+1} with LP's K ≈ 7·10⁹.
- **For PIL (verify-cl).** Adopt (F3′) verbatim as the "sure on Good(<s_p)" input of every SUP-SUM.
  - But (S2)'s counting bound N(Y) ≤ 2Y is sure on Good(<s) only if Y + H(Y) ≤ s.
  - Otherwise use N_{≺s}(Y) ≤ Y·Σ_{c∈𝒩_{≺s}, c≤Y}1/c ≤ A′Y (Rankin at σ = 1). This costs a factor
    ≈ log z per capped cofactor.
  - Check that LBS's budget (§R.9, "slack ~L² per element") absorbs this. It does if the number of
    capped cofactors per element is O(1), which is exactly LBS's open point.
- **The CL changes (i)–(iv) are right.** (ii) is B's G8(i), resolved. L ≥ 470 is vacuous canonically.

### §15.4 Good(<t) and the first-failure lemma (7.4): non-circular, and times right

- **Measurability.** Good(≤t) ∈ F_t, because each E is F_{t(E)}-measurable and Q_j ∈ F_{s_j}. So τ is a
  stopping time. The first-failure proof is correct: on {τ = t}, either an event with t(E) = t fails
  on Good(<t), or (D) is contradicted.
- **Event times, checked one by one against (*):**
  - **E1** (8u/L¹¹ + H). It is consumed at ≥ u. CL's own indicator Good(<t_J) has t_J ≤ t(E1).
  - **E2** (right end of W). Its A_E needs R1′ on W. For u ≤ t(W), R1′(u) reads E5(u) at u/2 + H, ν on
    [1, u/2], i.e. E3(v) for v ≤ u/4 at times 2v ≤ u/2, plus E4, E1 and LP data on [1, u(1−2δ)]. All
    are < t(W). No same-time dependence.
  - **E3** (2v). Its A_E needs R1′ on [v, 2v], which reads ν only on [1, v], i.e. E3(≤ v/2). No
    self-reference.
  - **E4** (max J + H). A_E = Ω. Consumers U1–U7 are at ≥ 4·height.
  - **E5** (v/2 + H). Mart(J) is F_{v/2+H}-measurable for J = [v(1−δ), v]. b_q uses (L-a) at heights
    ≤ 2v/Q₀ ≪ t(E5). The consumer is G1′(v). This also fixes A2.4's "J ⊂ [x/2, 2x]" timing error,
    correctly.
- **Pending (correctly flagged in §6.3).**
  - E3′'s, and also E3's, A_E use "Comp ≤ |I| + 2", i.e. margin positivity on [u, 2u] via Prop. 9.
  - Prop. 9's V(t) reads ε at heights up to 2u, which is E3′(u) itself.
  - Until fix-bprime's pointwise Prop. 9 lands, use the peeled rows (A_E = Ω,
    p ≤ 8u^{−2}L_u^{−1}). The total is unchanged.
  - The note says this for E3′. Apply it to E3 too: t(E3) = 2v was chosen for exactly this A_E.
- **(D)'s input list is complete,** given the above. All its inputs have time ≤ s_j.
  - The adapted-target clause (γ_k ∈ F_{x_k}, R_k ≡ 0 on [1, x_k + H], 𝒜 decided at r < y(n)) is
    needed and present.

### §15.5 Budget (6.2/7.4)

- Σ_j(log X₀ + j log 2)^{−2} = (1/log 2)/log X₀ + O(log^{−2}X₀). The x^{−2}-type rows give
  ≈ (4/3)X₀^{−2}. So the total is ≤ 1.5/log X₀ < ½. Correct.
- It is dominated by E1 at L^{−2} per scale. That requires CL/CapL-w to deliver L_u^{−2} per dyadic
  scale (not L^{−1}, which diverges). This is a constraint on the CapL-w owners, and it should be
  stated in their target.
- A18's "≤ X₀^{−1}" is wrong, as the note says.
- At log X₀ = 10⁸ the total is 1.5·10⁻⁸, so there is no tension with "positive probability".

---

## §16 Targeted review: fix-Bprime §9.7 (pointwise Prop. 9) and gap-G3 §16.19 (type union, PIL check)

**Verdict.**
- **§9.7(a) is correct.** The pointwise v(t) and start-time ordering do remove E3′'s self-reference,
  so E3′ can drop the peeled fallback.
- **E3 never needed Prop. 9.** Its A_E is an H-window margin statement, so it can drop the fallback
  too.
- **§9.7(b) is correct.**
- **§16.19.** The B′∖C tails, the Dickman gains and the C-row excess are PIL-safe, because they are
  deterministic or sure. One slip: the Rankin constant should use p ≥ X₀.
- **The open step is correctly located, but its fallback is mis-stated.** If stepwise compatibility
  fails, the obstruction is late free primes with FAC-weight β_f < 1 as well as sharing, not sharing
  alone.

### §16.1 §9.7(a): pointwise Prop. 9 and the E3′/E3 self-reference

- **Dependence, checked.**
  - m(t) = T′(t) − (K_ptρ̃)(t) − … reads ρ̃ only at t/w with w ≥ 2. ρ̃(z) = σ(W_z)/H(z) is fixed by
    decisions at slots ≤ z + H(z)/2.
  - So v(t) := sup_{|h|≤1.01H(t)}|m(t+h) − m(t)| reads m on [t − 1.01H, t + 1.01H], hence ρ̃ and noise
    only at points ≤ (t + 1.01H)/2 + H/2 ≤ t/2 + 2.1H(t/2) < t for t ≥ 6H. Correct.
- **Pointwise recursion and induction, checked.**
  - The recursion is v(t) ≤ S(t) + Σ_w 1.01κ_w(t)w^{ε−2}·sup{v(t′) : |t′ − t/w| ≤ 2.1H(t/w)}.
  - Well-founded induction on t, with the hypothesis v(t′) ≤ 6.5E_S/log t′, closes:
    Σ_w c_w·log t/log(t/w) ≤ 0.69(1 + O(log w/log t)) for w ≤ √t, and the tail w > √t carries weight
    ≤ t^{−0.45}log t/log X₀. That is the same 6.44 as Step 5's chain sum.
  - log t′ = log(t/w)(1 + o(1)), because t′ is within 2.1H of t/w.
- **The self-reference is gone, checked.**
  - The event for a short window I = [a, a+ℓ], ℓ ≤ H(a), needs V_I ≤ 2M₁(|I| + 2), i.e. m ≥ 0 on I.
  - m on I is (H-window margin at I) − v. The H-window margin reads ν at scales ≤ (a+ℓ)/2, i.e. E3 at
    times ≤ a/2 + H. v on I reads short-window events for windows ending ≤ (a+ℓ)/2 + 2.1H ≤ a/2 + 2.6H < a.
  - So **ordered by start time**, each short-window event's variance bound follows from strictly
    earlier events. This is a first-failure argument inside E3′(u), and it is legitimate: the union of
    time-ordered events has the same failure bound, ≤ 4u^{−2}(log u)^{−2} with λ′_u.
  - **E3′ may drop the peeled row (p ≤ 8u^{−2}L_u^{−1}) and use the deterministic row.**
- **E3 does not need Prop. 9 at all.**
  - E3's A_E is "Comp(W) ≤ H + 2 for H(t)-windows W ⊂ [u, 2u]". That is the **H-window** margin ≥ 0,
    which the margin identity gives from G1′ − |Ke| with ν read at scales ≤ t/2, i.e. E3 at ≤ u/2.
  - No pointwise margin is involved. fix-budget §6.3's remark that "E3 has the same feature" holds only
    if R1′ is routed through Prop. 9, which E3 does not need.
  - So E3 also keeps its deterministic row, with t(E3) = 2u.
- **One wording point.** Inside E3′(u) the time ordering is by window start a, while fix-budget's
  table gives t(E3′) = max I. Both are fine, since the consumer reads I at t ≥ 2a − 2H > max I. State
  that E3′(u) is internally first-failure ordered and externally frozen at its last window's end.

### §16.2 §9.7(b): the J-term

- **The correction to Step 4 is right.** "log y·2η ≤ 2θ_*" does not follow from §4.8, since θ_* carries
  log(v/w).
- **The replacement checks.**
  - Near-threshold w = pm at y have p ≈ p₀ = √(y/m) and P⁺(m) ≤ p + H.
  - For p₀ ∈ [P, 2P), m runs over one block (y/4P², y/P²] of (4P)-smooth elements, with 1/m-weight
    ≤ log 4·ϱ(log(y/P²)/log 4P), by Lemma V's dyadic bound, two blocks.
  - The near-threshold primes per m number ≤ 74.4H(P) + K_loc(P), by Lemma L at |J| ≈ 6.5H, each of
    weight ≈ 1/P.
  - Hence log y·η(y) ≤ Σ_P (74.4H(P) + K_loc(P))P^{−1}·log y·ϱ(log y/log 4P − 2).
  - For log y ≥ 3 log P, ϱ absorbs log y. Otherwise log y ≤ 3 log P. So the sum is ≤ C·H(P)log P/P,
    maximised at P ≈ X₀ because H(P)log P/P is decreasing.
  - At log X₀ = 10⁸: 3·74.4·e^{2715}·10⁸·e^{−10⁸} = e^{−(10⁸ − 2739)}, within the stated e^{−(10⁸−2770)}.
    Correct, uniformly in y.
- The extra remark (the filter of a fixed w switches on a τ-set of width ≤ 1.01H(y)/w ≪ 2H(p)) only
  helps.

### §16.3 gap-G3 §16.19: type union and the PIL check

- **(ii)(a) Rankin at ½ per B′∖C row.** #{M ≤ 2z made of primes of P(C)} ≤ (2z)^{1/2}∏_{p∈P(C)}(1 − p^{−1/2})^{−1}.
  - **Slip.** The note writes the product as e^{2.11√π} with π ≤ κD ≤ L². That bounds Σp^{−1/2} as if the
    primes were 1, 2, 3, …. With √π up to L it would read z^{2.11}, which is fatal.
  - Use p ≥ X₀ instead (distinct realised primes): Σ_{p∈P(C)}p^{−1/2} ≤ π·X₀^{−1/2} ≤ L²X₀^{−1/2} ≈ 0.
    Then the factor is ≤ 1 + o(1), and "≤ 3T·z^{−0.499} per row" stands.
- **(ii)(b) C-row excess.** ∏_{p∈P(C)}(1 − 1/p)^{−κ} is a **sure** bound, valid for every realisation
  (≤ e^{2κπ/X₀}, or ≤ L^{2.1κ} via Mertens). Sure bounds are always PIL-safe. Correct.
- **B′∖C tails and Dickman gains: PIL-safe.**
  - The tails are rigid X₀-smooth integers, summed as deterministic counts Ψ(2z/M, X₀).
  - The row types (which M) are a union bound outside the expectation.
  - Each row's thin constraint is paid by a pivot in P(C), inside PIL as usual.
  - Nothing here is a late realised sum. Correct.
  - Precision: "B′∖C rows carry no free primes" means none *outside* P(C). They may contain free primes
    of P(C) that are shared with C rows. That sharing is exactly what bears on the open step below.
- **The open step, correctly located.** The cover inequality ∏_{piv}q·∏_{free}q ≤ ∏_C M_y is a
  pointwise statement at the solved configuration. PIL instead bounds each late free block at its own
  step, in earlier variables.
  - FAC makes the integrand exact up to caps: ∏_{late f}q_f^{−β_f}·1(caps)·Ψ₀.
  - Compatibility holds iff the stepwise SUP-SUMs (each costing ≤ A·Y_f^{(1−β_f)₊}, with caps Y_f
    coming from the later pivots' feasibility) multiply to ≤ ∏_C(z₀/d_y)/∏_{free}q·(polylog)^{#free}.
- **But the fallback is mis-stated.** gap-g3 says that if compatibility fails, LBS is needed only for
  shared late free primes, because "after the cover substitution every free prime has β = 1". That
  does not follow.
  - β_f is fixed by FAC's linear algebra: e_f = Σ_{later piv}v_{f,p}e_p and β_f = 𝟙ᵀv_f. The cover
    substitution is an inequality used at the end, and it does not change the stepwise weight.
  - A late free prime with column e_{p} − e_{p′} (β = 0, verify-CL's R a b / R a c / R e pattern) can
    occur in Cover-Bound types, for instance when a C row and a B′∖C row share a non-pivot prime.
    Its SUP-SUM costs A·Y_f.
  - Whether the caps Y_f reproduce the cover bound's ∏_C M_y factors is exactly LBS's **β < 1** case,
    as well as sharing.
- **What would settle it cheaply:**
  - (1) show that in Cover-Bound types every late free prime has β_f ≥ 1, e.g. by choosing B′ ⊃ C and
    the decision-order structure so that each free prime's column equals a later pivot's column, as for
    pass primes; or
  - (2) show that the caps from the later pivots' feasibility give Y_f^{1−β_f} ≤ (the corresponding
    ∏_C M_y-factor)/q_f, which is the cover inequality applied stepwise along a triangular solve.
  - gap-g3's "pointwise + monotone + triangular ⇒ expect yes" is plausible for (2), but it is not a
    proof, and it is not "LBS only for sharing".

---

## §17 Targeted review: gap-G3 §16.22 (Cover Bound in PIL order), route H (fix-smooth §16, gap-G3 §16.21), route K

### §17.1 gap-G3 §16.22: [P | PIL with progressive G, FAC]. My §16 fallback objection is withdrawn

- **Monotonicity.** 𝒩_τ is a composition of sums over realised tuples and sups over ω of nonnegative
  integrands, with index sets that do not depend on the integrand. So Φ ≤ Ψ pointwise implies
  𝒩_τ[Φ] ≤ 𝒩_τ[Ψ]. Correct.
- **Applying 𝒩_τ to the full product Φ is equivalent to PIL's stepwise recursion.**
  - By FAC, every factor produced by a pivot integration depends only on variables earlier than that
    pivot.
  - So at a late block F_t, the factors still to come (from pivots earlier than F_t) do not depend
    on F_t-data, and they commute with F_t's sum and sup.
  - Hence E[X_τ 1(G)] ≤ θ^{|P|}ε^r𝒩_τ[Φ] with Φ = §11.9's summand. Correct.
- **The pointwise substitution, checked.**
  - Without caps, Φ = ∏_{piv}q* (§11.9: q-volume ε^r∏q̂/|det|).
  - The cover identity ∏_{p∈P}p = ∏_{y∈C}M_y·∏_p p^{−(e_C(p)−1)} is an *equality* of the exponent
    structure, valid for any positive values of the primes. It turns into the inequality
    ≤ ∏_C(2z₀/d_y)X₀^{−excess} using:
    - q* ≥ X₀ for the solved pivots (caps) and q ≥ X₀ for the realised free primes;
    - M_y d_y ∈ J for every y ∈ C ⊂ B′, which holds at the solved point because the pivots are solved
      from B′'s window constraints.
  - Dividing by ∏_f q_f, each free prime appears in Ψ with **exponent exactly −1**, and nowhere else,
    since C's M_y have been replaced by 2z₀/d_y. Off the caps Φ = 0 ≤ Ψ. Correct.
- **Widened caps.** On the O(ε)-widened region, q* ≥ X₀(1 − O(ε)) and M_y ≤ 2z₀(1 + ε)/d_y. So Ψ needs a
  factor (1 + O(ε))^{r + excess} = 1 + o(1). The caveat is right and harmless.
- **Evaluating 𝒩_τ[Ψ].** Ψ has no caps, so each late block's SUP-SUM ranges over all realised primes in
  its decision window.
  - Σ_{X₀≤q≤2z}1/q ≤ log(L/log X₀) + 2.2/log X₀ (A′), which is sure on G_{<s_{p_t}}.
  - Tuples sorted by decision order give (log L)^n/n!.
  - Free primes need no (S3) carry. Correct.
- **So my §16 point is resolved.**
  - I said that if stepwise compatibility failed, β_f < 1 would bite. But PIL's output is a *monotone
    functional of the final product*. Any pointwise majorant may replace Φ, so the stepwise
    distribution of the β_f is irrelevant.
  - **The Cover Bound needs no LBS.** Sharing is a type datum paid by §16.19's union, with the p ≥ X₀
    correction I gave in §16.3.
  - LBS remains only for the rank-full branch, Theorem R in general, which verify-CL §R.12 now
    addresses (referee B).

### §17.2 Route H (fix-smooth §16; gap-G3 §16.21): [P | inputs listed below]. The numbers reproduce

- **Participation+, checked.**
  - The set "V heavy of least dimension" exists because span(S) is heavy when N(J) ≥ r₀ + φ(r₀) and
    rank < r₀.
  - For any hyperplane W, W″ := span(S ∩ W) ⊊ V is element-spanned and light, so
    #(S∩V∖W) ≥ φ(r) − φ(r−1) + 1 = Q + r + 1.
  - Elements of degree ≤ D* are distinct exponent vectors in ℤ^m_{≥0} (B §15.2), so they number
    ≤ binom(m+D*, D*) ≤ Q. Hence the degree-(≥ D*+1) elements meet every complement of a hyperplane,
    so they span V.
  - Using m ≤ π ≤ r₀D in place of the true m only lowers D*. That is conservative.
- **Thin cover and Steinitz, checked.**
  - Cap(S∩V) ≥ φ(r) − r ≥ c, so Thm 11.3 gives κ ≤ r − 1 − j.
  - A minimum cover is independent (L. 11.1: a dependence Σ_{I₊} = Σ_{I₋} would let one drop I₊).
  - Steinitz extends it inside the spanning set of high-degree elements, giving |R| ≥ 1 + j.
- **Row weight, checked.**
  - Under §16.22's Ψ, each R row contributes z^{−1}·(types)·(tail count) with tail ≤ 2z/X₀^k. So
    w_row ≤ Σ_{k>D*} binom(π+k, k)·2X₀^{−k}.
  - Consecutive terms have ratio ≈ eπ/(kX₀) ≪ 1, so the sum is dominated by k = D*+1.
  - The C-row costs e^{3r log L}C^r and the free-prime sums (e^λ ≤ eD per row, sorted tuples) are
    absorbed by δ^{r−2} for log L ≥ 16. Ignoring δ^{r−1} in (16.1) is conservative.
- **Numbers, independently recomputed** (`/tmp/rhscratch/referee2/routeH.py`; entropy bound,
  r = r₀ = L/(4 log L), π = r₀D, log X₀ = 10⁸, O(1) = 10). Needed log c:

  | log L | needed log c |
  |---|---|
  | 31.4 | 4.87·10⁴ |
  | 35 | 3.39·10⁵ |
  | 38 | 1.69·10⁶ |
  | 41.9 | **1.355·10⁷ = 0.1355 log X₀** |
  | 45 | 7.0·10⁷ |

  - These match fix-smooth and gap-g3.
  - log y/log X₀ (tolerance A) is **0.4065 at the 41.9 edge**.
  - y crosses X₀ at log L ≈ 43.6, not 43.7: needed log c = 0.352 log X₀ at 43.7. Harmless, since
    §16.16 takes over from 41.9.
  - The result is insensitive to r (r₀/2 gives 0.1338) and to the O(1) (C₀ = 1000 gives 0.1355).
- **Tolerance with raised H = M₁² on the route-H range.**
  - log H ≤ 2.8·10⁷ at log L = 41.9, and d log H/d log x ≈ 10⁻¹¹. So the ramp, (R_H) and "H(q)/q
    decreasing" hold.
  - Lag and LP: log H ≪ 0.362·log u.
  - (SW) and NV: ν̄ ≈ √(4λ/M₁).
  - E3′: λ′ = λ + log H, and its failure probability is unchanged.
  - Prop. 9's o_v: T′ is smooth at scale κu ≫ H, R ≡ 0 below x₁, and 𝒜 = ∅.
  - The near-threshold weight is still dominated by p₀ ≈ X₀, where H is standard.
  - B ≈ 21M₁L² = x^{o(1)}.
  - All fine. With y < X₀ the absorbed set is empty, and Lemma P and A11 are vacuous.
- **Hand-off at 41.9, A11 with y = X₀^{O(1)}: checked.**
  - Elements of 𝒜 have log n ≥ e^{43.6}, and their density is ≈ ρ(u) with u = log n/log y ≥ 5·10¹⁰.
    So on Re s ≥ 1 − 1/log X₀:
    Σ_{n∈𝒜}n^{−σ} ≤ ∫exp(−(log n/log X₀)(log u/c_y − 1))dn/n, with c_y := log y/log X₀ ≤ 17.
  - This is astronomically small, since log u ≈ 24.6 > c_y.
  - Lemma 2.3(ii)'s mean-square bound only improves, since #𝒜 ∩ [1, x] ≤ xρ(log x/log y).
  - So A11's conclusions hold, with "exp(−X₀^{1/11}/12)" replaced by this bound. The margin is
    log u/c_y ≥ 1.4 at the very edge.
- **Residual dependencies of route H (nothing else hidden that I can find):**
  - (i) Thm 11.3 (fix-smooth), Lemma 11.1 and Participation+: checked above or by others.
  - (ii) The Cover Bound in PIL order: now [P] by §16.22. **The R.6/LBS dependency listed in §16.21
    for C-row free sums is gone.**
  - (iii) E_cl's **rank ≥ r₀ alternative**: Theorem R′ in general, i.e. LBS/SVL (verify-CL §R.12,
    with referee B). This is not part of route H, but CapL-w alone does not give E_cl without it.
  - (iv) The raised-H tolerance chain (§16.1, B §15.1, fix-budget E3/E3′).
  - (v) Hildebrand/Dickman counts, used only on the §16.16 side.

### §17.3 Route K (fix-Bprime §10.11–10.12): [S] overall. The pieces are mostly sound, with two gaps to route

- **(K1) adaptedness and (K2) sure increment bound: [P].**
  - Membership in 𝒦 is a function of F_{q−} (𝒩_{<q}, the grid, M₁) and of q's own landing.
  - Non-absorbed composites with latest prime q have cofactors m ∈ 𝒩_{<q} in non-overfull grid
    windows. So X_q^{na}(W) ≤ 2M₁ surely, even when W/q^a straddles an overfull window.
- **(K4′) Theorem R's applicability.**
  - Theorem R′ counts *all* rank-full k-subsets. PIL chooses greedy pivots intrinsically, so it
    applies to any basis of an overfull window. No ordering assumption or "EXT" is needed to *apply*
    it.
  - What is needed is Theorem R′ for **general types**, i.e. LBS/SVL (verify-CL §R.12, under
    referee B). fix-Bprime's line-1595 dependency note is right.
  - **Rank lower bound.** "Cap ≤ (2D+1)^{r−1}" is unjustified (B §15.3). Use instead the injective
    projection of the rank-r span onto r coordinates, together with distinct exponent vectors:
    N(G) ≤ (D+1)^r. So r ≥ log N/log(D+1). This differs from r(k) = 1 + log(k − r₀)/log 3D only
    by O(1), and K4′'s tail sum Σ_k k·k^{−3.9 log L/log(3D)} from M₁ is unaffected.
  - E[ρ_𝒪] ≤ e^{−10⁴} stands, given Theorem R general.
- **(K3) Freedman with b = 3h/y + K_loc: [P modulo bookkeeping].**
  - Y_q ≤ N(I/q) is bounded by §8.3's local count, split into ≤ 6H pieces when h/q > 6H, plus
    #𝒜′ by induction at u/q. That is fine.
  - The compensator ≤ 2hρ_𝒪/L and the form P(S ≥ a, V ≤ v) are fine.
  - Two fixes:
    - (a) {ρ_𝒪 ≤ e^{−1000}} is a *global* event with no time. For the first-failure lemma, use
      per-height cumulative pieces ρ_𝒪(≤ u/y), with Markov per dyadic height. The budget is
      unchanged.
    - (b) "o(h/L) at every scale" is loose. The bound is 2e^{−1000}h/L + hL^{−5}, i.e. O(h/L) with
      constant 2e^{−1000}. The margin needs ρ_𝒦 ≤ c′/(10L), which holds. Say that instead.
- **(K2)/(K6) induction: well-founded.**
  - The queue at z needs (K2) (sure), R1′(z) and T′ ∋ −ρ_𝒦.
  - ρ_𝒦 at z needs (K3), whose b comes from K_loc at heights z/q < z, i.e. queue bounds below z, and
    from (K4′) (CL rank-full, which needs no queue at z).
  - No cycle.
- **"Is every E_cl use a cofactor use?" No.** Besides the cofactor uses (Thm 4.2′, NV, Prop. 9's short
  windows), E_cl is used to count elements in the **unit edges of windows at the current height** in
  fix-budget's grid-to-continuum nets for E3, E3′ and E5 ("edges hold ≤ (L⁶/2+1)M₁ + 2 elements on E1").
  - These must be re-routed via §8.3's local count plus #𝒦 from (K3).
  - Timing: the local count at heights ≤ 2u is available only after 2u + 7H(2u), which is later than
    t(E3) = 2u.
  - So either set t(E3) := 2u + 7H(2u), which is harmless since its consumers run at ≥ 4u, or bound the
    edge counts by the sure lag form N(J) ≤ |J| + 2B + H + 4.
  - Lemma P(iv), (K5), is the other non-cofactor use, and is [S].
- **Still [S] (as fix-bprime says):**
  - (K5) Lemma P(iv).
  - (K6) the margin identity with the extra filter "m ∉ 𝒪_q". This filter is not of Lemma M's
    max t(p)·w₁⋯w_i < x form, so Lemma M/Theorem 1 do not obviously apply.
- **Residual dependencies of route K:**
  - Theorem R′ general (LBS/SVL);
  - (K5) and (K6);
  - the edge-count re-routing above;
  - the (K3) bookkeeping.

  As insurance it is weaker than route H, which needs none of (K5), (K6) or LBS.

**Verdicts:**

| item | verdict |
|---|---|
| §16.22 | **[P]**, and my §16 fallback objection is withdrawn |
| route H | **[P]** modulo Thm 11.3/Participation+/raised-H tolerance (checked) and E_cl's rank ≥ r₀ branch (Theorem R′ general = LBS/SVL), the latter outside route H itself. Numbers reproduce, and the 41.9 edge has log y = 0.4065 log X₀ |
| route K | **[S]** |

### §17.4 Lemma SC (lead-notes L1), gap-G3 §16.22′ (allocation), verify-CL §R.12″/§R.13: all three [P]. Cover Bound = PIL + SVL + Lemma SC

**(1) Lemma SC: [P].** I checked the proof line by line.
- (2) Rank M_t = |P_{≤t}|, because the columns P_{≤t} of the invertible E_P are independent.
- (1) Nesting. Restricting rows to fewer columns can only enlarge closures: cl_{M_{t+1}}(X) ⊆ cl_{M_t}(X).
  - A row is in the lex-first basis iff it is not in the closure of the rows before it.
  - The row order is the same for every t, so membership is monotone in t. ✓
- (3) Coverage. The C-first greedy basis maximises |C ∩ ℛ| (matroid greedy). Hence every y ∈ C ∖ ℛ_{≤t} lies in the span
  of C ∩ ℛ_{≤t} alone, by the exchange step as written.
  - Column j ∈ P_{≤t} ∪ F_{≤t} is E_{·,P≤t}v. So E_{y,j} = Σ_{w∈C∩ℛ≤t} α_w E_{w,j} ≠ 0, and some w ∈ C ∩ ℛ_{≤t} has E_{w,j} ≥ 1. ✓
  - The proof uses neither minimality of C nor κ ≤ r − 1, as the remark says.
- **Independent check** (/tmp/rhscratch/referee2/sc_check.py, exact rationals, written from the statement and not from the
  lead's scripts):
  - setup: r = 3..7, m = r+1..r+5 primes, entries 0..3, T ≥ 2 stages only, every minimal cover;
  - result: 842 configurations, 2342 (configuration, cover) pairs, **0 failures** of (1)–(3).
- **The C-first order is essential.** The same lex-first construction with B′∖C listed first violates (SC) on 1238 of the
  2342 pairs.
  - So SVL's stage rows must be *Lemma SC's* sequence. A generic "block-LU with row pivoting" (§R.12 Setup) is not
    enough.
  - §R.13's addendum already makes this choice. §R.12's Setup line should say so too.

**(2) gap-G3 §16.22′, the identity and the allocation: [P | SVL's Proj_t and slot chains, referee B].**
- **Identity.** d log n = E_P d log q_P at fixed free primes and tails. So vol = Π_P q/(|D| Π_y n_y) · δ^r.
  Π_y n_y = Π_p q_p^{s_p} · Π_y c_y, with s_p summed over all r rows. Hence vol/δ^r = |D|^{−1}Π c_y^{−1}Π q^{1−s}, exactly. ✓
- **Allocation.** Each prime has an occurrence in C, because C is a cover. Each pivot spends one C occurrence against its +1.
  Each free prime reserves one C occurrence (its home) for its harmonic sum. R-row occurrences stay in 1/n_y. This gives:
  - C row: d_y^{−1};
  - R row: 1/n_y ≤ 1/z₀;
  - each other unit: ≤ τ^{−1} ≤ X₀^{−1}.
  This is the bookkeeping behind §16.10(ii) (Π_P p ≤ Π_C M_y·X₀^{−excess}), now as an equality before the inequalities. ✓
- **Stagewise, class by class (the point I was asked to check).** I use stage rows ℛ_{≤t} from Lemma SC.
  - *Pivot j ∈ P_t.* Stage t's Jacobian numerator q_j cancels an occurrence in some C row of ℛ_{≤t}, by SC.
    - If that row joined earlier, the factor q_j^{−E} was carried exactly. P_t is outer at those stages, so it passes
      through the SUP-SUMs of F_{<t} as a constant.
    - The remaining C-row mass in ℛ_{≤t} gives q_j^{1−s^{cov}} ≤ τ_j^{1−s^{cov}}. This is F_t-free, as the SUP-SUM requires.
  - *Late f ∈ F_t.* Its home is a C row of ℛ_{≤t}, by SC. Other C rows of ℛ_{≤t} give q_f^{−(e−1)} ≤ X₀^{−(e−1)}.
    C rows joining after t lose f, but Proj_t gives X₀^{−e_y(F≤t)} (§R.13 addendum).
  - *R row y.* At stage t(y), y is a new Jacobian row. Its factor is 1/N_y with N_y = n_y ∈ J, so ≤ 1/z₀.
    - This needs **no** projected-feasibility input. R rows are the easy case.
    - Its pivot and free occurrences stay inside n_y. Its free primes are labels with homes in C.
    - So the row costs (monomial patterns over the π ≤ κD cover labels) × (rigid tail count Ψ(2z/X₀^k, X₀)), the tail
      being deterministic.
- **Weights match the consumers.** This is the §16.11 weight z^{−1}Σ_k(π^k/k!)Ψ(2z/X₀^k, X₀), my §17.2 and B §19.1 weight,
  and fix-smooth §16's Σ_k C(π+k−1,k)·2X₀^{−k}.
  - The R row's pivot mass is paid by its own count, and no X₀^{−deg} credit is taken on top. This answers §R.13 (1):
    no double count. ✓
- **Hence route H keeps its B′∖C gains exactly**, with no "≲ L per row" loss. Under SVL the plain-c weights give
  harmonic tails, but those are not the weights used here.

**(3) verify-CL §R.12″ (with §R.13's addenda): [P | Lemma SC].**
- The split into cover rows and non-cover rows is the stagewise form of (2). Its identity
  Π_{P≤t}q/Π_{ℛ≤t}n = W_t^{cov}·Π_{noncov}n_y^{−1}·Π_{P≤t}q^{1−s^{cov}} is exact (expand Π_{cov} n_y). ✓
- The requirement s_j^{cov} ≥ 1 is Lemma SC(3) for j ∈ P_{≤t}. ✓
- **The sub-case "late f only in non-cover rows → capped count via (F3′)" is vacuous under Lemma SC.**
  - Apply SC(3) at t = t(f): f has an entry ≥ 1 in a C row of ℛ_{≤t(f)}.
  - The sub-case is not vacuous for other stage sequences: see the R-first runs in (1).
  - It would also be lossy. Spending an R-row occurrence costs that row up to a factor z, as §16.22′ says.
  - **Recommendation:** delete the sub-case, or mark it "unreachable with ℛ from Lemma SC".
- **Wording.** "The free part and tail of a non-cover row are summed with weight 1" should read: "the tail is a rigid count,
  and the free part is a monomial pattern in cover labels". With SC every free prime has a home. If the free part were
  summed as free values, it would need B3's joint cap Y/Π c_t, with an Euler factor per row that route H does not budget.
  So B3 is not needed for non-cover rows here.
- §R.12″'s worked case (C = {q₁q₂d₁}, B′∖C = {q₁d₂}) gives δ²L·Ψ(2z/X₀, X₀)/z per height. ✓
- **Open (not mine):** §R.12(iii) and Proj_t (cover rows only), and B2's slot-indexed chains. Referee B owns both.

**Conclusion.** Cover Bound = PIL + SVL + Lemma SC [P | SVL items above]. No LBS is needed. Route H returns to my §17.2
status, now resting on SVL rather than on §16.22.

**My §17.1 reading no longer needs settling.** For the record, I accept verify-CL §R.13's correction to it: the
exchange needs the caps widened by the pinned range ρ_t of P_{>t}, not by O(ε) as I wrote. That holds only when ρ_t ≪ 1.
The stagewise route above has no such precondition.

### §17.5 Addendum A11.4(a) (A11.2 at y = X₀^{O(1)}, route H): [P]

**Verdict: [P].** The three inputs are checked.
- **Rankin.** 𝒜 is (y + H)-smooth with H ≤ exp(8·2900²) < X₀ ≤ y. Since u ≤ e^{2900} ≪ y, Rankin with Lemma CM's sure
  Chebyshev bound is valid.
- **Decay.** δ_k ≤ e^{−2·10⁸+22} at zero scales, while log(v/log y)/log y ≥ 4.5/(K·10⁸).
  - The a ≤ Y term is therefore ≤ 2exp(−½u₀ log u₀).
  - u₀ = v₀/(K log X₀) ≈ 960 at K = 10⁸. The stated "≥ 96" is a factor 10 conservative, and the term is ≈ e^{−3300},
    not just ≤ e^{−200}.
- **The a > Y term.** log Y ≍ log x_k ≥ e^{2·10⁸} ≫ e^{2900}, so it is in the canonical range. ✓
- **Lemma 2.3(ii).** The addition is ≤ 2exp(e^{2900}/2), negligible against x_k^{1/2−o(1)}. ✓
- **Sufficient condition.** The closing condition (y ≤ n^{o(1)}, log y ≤ e^{10⁸}) is sufficient. The 43.6 vs 43.7 point is
  already noted in the text and is immaterial.
- Nothing here touches route K. A11.4(b)'s caution stands.

### §17.4 (continued) verify-CL §R.13's concession, and the excess double-count question

**(4) §R.13 on my §17.1: agreed, with one refinement.**
- The literal exchange fails exactly where verify-cl says. In FAC, 1(caps(F_t, P_{>t})) couples a late block to
  later-integrated pivots. In the k = 2 example (n₁ = Rabd₁, n₂ = Racd₂), the cap of a moves with b. My §17.1 widened the
  caps by O(ε) only. That was wrong: the widening must be the pinned range ρ_t of P_{>t}, so that the caps are functions
  of outer variables.
- **Refinement.** The widened box also costs a factor on Π q* and on M_y ≤ 2z(1+ρ)/d_y, i.e. e^{O(kρ_t)} over k pivots and
  rows. So the clean precondition is kρ_t ≪ 1, not ρ_t ≪ 1.
  - With ρ_t ≤ ‖E_P^{−1}‖_∞ δ/z, everything turns on ‖E_P^{−1}‖_∞.
  - **§R.13's Hadamard bound ‖E_P^{−1}‖ ≤ m^{k/2} is false for general exponent rows.** It holds for 0/1 rows. For rows with
    sum ≤ m the row 2-norms are ≤ m, not √m, so Hadamard gives ‖E_P^{−1}‖_∞ ≤ k·m^{k−1}.
  - This is attained up to constants. Rows n_i = q_i q_{i+1}^{m−1}d_i (bidiagonal, det 1) give ‖E^{−1}‖_∞ ≈ (m−1)^{k−1}.
    For example k = 8, m = 8: 960800 vs m^{k/2} = 4096 (/tmp/rhscratch/referee2/inv_norm.py).
  - So the precondition is (k−1)log m + O(log k) ≪ log(z/δ). That is about twice as strict as the "(r/2)log m ≪ log z"
    now in the notes (§R.13, gap-G3 §16.24). The regime boundary should be restated.
- **Status.** §16.22 with ρ_t-widened caps is [P] in that regime. By (1)–(3), SVL + Lemma SC covers every regime without
  any precondition. So nothing downstream depends on the widened-cap route. It is an alternative proof, not an input.

**(5) Is "every remaining C-row occurrence is excess ≤ X₀^{−1}" compatible with paying the pattern factor via τ^{−(s−1)}?
Yes, provided the cover-restricted mass is used, and each unit is spent once.**
- In the identity, the only pivot-excess factor is Π_j q_j^{1−s_j}. Under the allocation it splits:
  - Π_j q_j^{1−s_j^{cov}}: C-row mass beyond the one cancelled occurrence, each unit ≤ τ_j^{−1} (in stage t(j) via
    q ≥ τ; after it via Proj_t / B1);
  - Π_j q_j^{−e_R(j)}: R-row mass, which stays inside 1/n_y.
  - The free-prime excess q_f^{−(e_C(f)−1)} is the analogous factor for free columns.
- "≤ X₀^{−1}" and "≤ τ_j^{−1}" are two bounds on the **same** factor. Compatibility means the factor pays exactly one thing.
  - It may pay the multiplicity of the C rows' *extra* mass. Each extra unit sits in one of ≤ κ·(#columns) cells and
    carries ≤ τ^{−1} ≤ X₀^{−1}. So the extra-mass sum is ≤ Σ_m C(κπ+m−1, m)X₀^{−m} = (1−1/X₀)^{−κπ} ≈ 1, R.8a-style.
    §16.19(b)'s Π(1−1/p)^{−κ} ≤ L^{2.1κ} and §16.10(ii)'s "X₀^{−1} against κD labels" are other forms of the same payment.
  - The minimal pattern (which C row and position pays each pivot, "≤ D per payer") is not excess. It is a separate type
    cost, absorbed by the C rows' e^{O(r log L)} budget against δ^{r−2}.
  - It may instead be credited as a gain. It may not do both.
- **What must not be done.** Apply R.8a with the full s_j (all r rows) and also give R rows their count cap M_y ≥ X₀^k.
  That spends R-row pivot mass twice: once as τ^{−e_R} in the pattern sum, and once as X₀^{−k} in 2/M_y.
  - In the Cover Bound, R rows' pivot patterns are paid by the monomial count C(π+k−1,k) against 2X₀^{−k}, not by R.8a.
- **Route H does it right.**
  - gap-G3 §16.24 says the tables never multiply by X₀^{−excess}. My own §17.2 recomputation (routeH.py) agrees: its gain is
    (1+j)·k·(log X₀ − log(eπ/k)) with k the row degree, the count cap with the monomial count, and it has no excess term.
  - C-row excess goes only to the C-row pattern sum.
  - **No double count. Route H's numbers stand.**
- **Theorem R (the E_cl rank ≥ r₀ branch)** is a separate estimate with no cover, so it may use R.8a with the full s_j.
  The two estimates are never multiplied together on the same configuration, so they do not interact.
