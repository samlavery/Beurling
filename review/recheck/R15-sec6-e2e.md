# R15: end-to-end check of Section 6 (base range) and its consumers

**Snapshot.** `27e6ba0`, extracted to `/tmp/rhscratch/r15/src`. All line numbers below refer to that snapshot.

**Verdict: CORRECT WITH FIXES.**
- No BLOCKING defect.
- One FIXABLE defect (F1): the ν₁ partial windows inside μ₁, Lemma margin(c). It changes no constant and no consumer.
- Six COSMETIC items (C1–C6).
- Every other step was re-derived from the definitions and holds. This includes the mixed-measure telescope of (b) Step 3
  together with the variation estimates of (d)(iii).

**Order of work.** The verdict was formed before reading R7-margin-var.md and correction #53. The (b) Step 3 and (d)(iii)
findings agree with R7. F1, C1 and C2 are new.

---

## 1. Definitions and the two identities

**The objects.**
- **Target.** T = ⌊x⌋ for x < X₀. Above X₀, T has the rigid jumps, the absorbed jumps, and the continuous part
  T′_cont = 1 − ρ_det − ρ̄_𝒜 + R′.
- **ρ_det(u)** = Ψ([u,(1+κ)u], X₀)/(κu).
- **MA_w[h](x)** = h([x, x+w])/w.
- **MA[ℙ](q)** = MA_{κq}[rational primes ≥ X₀](q), following correction #47:
  - it is 0 for (1+κ)q ≤ X₀;
  - it is a partial window for X₀/(1+κ) < q < X₀;
  - it is the full window for q ≥ X₀.
- **f₀ and f₁.** f₀(q) = MA_{κq}[ν₀](q) with ν₀ := 1_{t≥X₀} dt/log t. f₁ := MA[ℙ] − f₀ = MA[ν₁] with
  ν₁ := (rational primes − dt/log t)|_{[X₀,∞)}.
  - For q ≥ X₀: |f₁| ≤ η_H(q)f₀(q).
  - |q f₀′(q)| ≤ f₀(q)/log q. This follows from f₀(q) = κ⁻¹∫₁^{1+κ} ds/log(qs).

**The operators.**
- **K_pt.** K_pt h(y) = Σ_{w∈𝒩, w≥2} w⁻¹ 1[τ_w < y/w] 1[y/w ≥ X₀⁻] h(y/w), in decision order.
- **K_ℚ.** Component form, acting on the measure ν behind h = MA[ν]:
  (K_ℚh)(x) = Σ_{m′≥2} m′⁻¹ MA_{κq}[ν|_{[P⁺(m′),∞)}](q) at q = x/m′.
  - K_ℚ(h1_{[X₀,∞)}) keeps only the components with q ≥ X₀.
- **K_ℚ^sh.** The sharp form, Σ_{m≥2} m⁻¹ 1[P⁺(m) ≤ x/m] h(x/m). The paper does not name it (see F1).
  - K_ℚ − K_ℚ^sh consists exactly of the partial windows P⁺(m′) ∈ (q, (1+κ)q] of Lemma blin(3).
- **K′_ℚ.** Strict filter and cut-off X₀, as displayed at 06:332.
- **K_pt^val.** K_pt with the value-order filter P⁺(w) < y/w.

**The derived quantities.**
- μ_edge (06:154).
- μ₁ and μ₀ (06:156–157).
- ρ_edge = (1+K_pt)⁻¹μ_edge.
- g = (1+K′_ℚ)⁻¹μ_edge.

**eq:ratid (x ≥ X₀).** It is exact:
1 − ρ_det(x) − (1+K_ℚ)MA[ℙ](x) = (κx − #ℤ∩[x,(1+κ)x])/(κx), so the error has absolute value ≤ 1/(κx).
- The m′-component counts the non-rigid integers m′p ∈ [x,(1+κ)x] with p ≥ max(P⁺(m′), X₀).
- This decomposition is unique.
- Dilation (blin(2)) is exact.

**eq:shdecomp.**
- **The identity.** On [X₀⁻, ∞), (1+K_ℚ)MA[ℙ] = (1+K_pt)(MA·1_{≥X₀}) + (K_ℚ − K_pt)(MA·1_{≥X₀}) + μ_edge.
- **Both sides vanish on [X₀⁻, X₀).** MA·1 is 0 there, both K-terms live on ≥ 2X₀⁻, and μ_edge is 0 below 2X₀/(1+κ).
- **K_pt never reads (X₀/(1+κ), X₀⁻)**, since κX₀ ≫ H(X₀).
- **(1+K_pt)⁻¹ is Volterra.** Each cofactor at least halves the scale, so the inverse reads its argument only at points
  ≤ x. Applying it gives eq:shdecomp at every x ≥ X₀.
- **No norm or convergence argument is needed.** The bound used is Lemma M:
  |(1+K_pt)⁻¹h(x)| ≤ Σ_n |c_n(x)|/n · sup_{u≤x}|h| ≤ (log x − Λ + 1)·sup|h|.

## 2. Lemma blin

**(1)**
- ρ_det ≤ (κu+1)/(κu).
- 1 − ρ_det ≥ (#primes in the window − 1)/(κu) ≥ 0.99/log u − 1/(κu), by (a).

**(2)** MA_{κx}[h_(m)](x) = h([q,(1+κ)q])/(κx) = m⁻¹MA_{κq}[h](q). The m′-component equals m′⁻¹ times the fresh-prime
density at q = x/m′.

**(3)** (correction #67)
- **Which m′ are partial.** P⁺(m′) = p ∈ (q, (1+κ)q] with m′ = pm is equivalent to p ∈ (√(x/m), √((1+κ)x/m)]. That
  interval has length ≤ (κ/2)√(x/m).
- **The tail term is small.** q ≥ X₀ forces √(x/m) ≥ X₀, so x/m ≥ X₀² ≥ 10⁴κ⁻². Hence 1/√(xm) ≤ 0.01κ/m.
- **Weight.** Σ1/m′ ≤ 0.51κ(log x+1).
- **Density.** Each component is MA_{κq}[primes ≥ p](q) ≤ MA[ℙ](q) ≤ (1+Λ⁻³)/log q ≤ 1.01/Λ.
- **Total.** ≤ 0.5151κ(log x+1)/Λ ≤ κ log x/Λ.

**(4) and (5)** agree with eq:Erig and Lemma T1:
- E_rig = E₀ + E_dr − E_fl;
- E₀ ∈ [0, κX₀+1];
- E_dr ∈ [0, (κ/2)Ψ];
- E_fl ∈ [0, #𝒟∩(x,(1+κ)x)].

## 3. Lemma margin

### (a)
- |I| = κq ≥ q^{0.01}q^{7/12} ≥ (2q)^{7/12}.
- (1 − η_H)(1 − κ/log q) ≥ 1 − 10⁻²⁰.

### (b) Step 1
- |E_rig| ≤ κX₀ + 1 + max(κt/2, κt+1) ≤ 2κt + 2 for t ≥ X₀.
- |D| ≤ B + 3H + 3 (Prop La).
- |R| ≤ 2t^θ log*t, the absorbed part is ≤ 2t^{θ/2}, and {u} < 1.
- So δ(t) holds, including its constant 6.
- On [X₀⁻, X₀), Δ counts ≤ H/2+1 jittered primes.

### (b) Step 2
- **The identity.** log·dΔ = dΔ_ψ*dN_𝒩 + dψ*dΔ, so dΔ_ψ*dN_𝒩 = dh with h as displayed.
- **The κ-part of h.**
  - |Δ(t)| log t ≤ 2κt log t.
  - ∫|Δ|dv/v ≤ 2κt.
  - ∫|Δ(t/a)|dψ(a) ≤ 2κt(log(t/X₀⁻) + 0.43) ≤ 2κt log t.
  - Total: 4κt log t + 2κt.
- **The rest of δ.**
  - With (B+3H+3)(s) ≤ s^{2.82·10⁻⁵}, ∫(t/a)^θ dψ(a) over a ≤ t/X₀ is ≲ 2.84t X₀^{θ−1}.
  - This is ≤ tX₀^{−0.5001}·(const), which is ≪ κtX₀^{−0.1} = tX₀^{−0.4967}.
- **Inversion.** Möbius inversion over v ≤ t/X₀⁻ costs the factor log t − Λ + 1 < log t. So |Δ_ψ(t)| ≤ 5κt log²t.

### (b) Step 3, the mixed telescope
1. **Multisets to tuples.** For symmetric G, Σ_{multisets} G = (1/r!)·Σ_{ordered r-tuples} G + Σ_{multisets with a repeat} G·(1 − c(S)/r!),
   where c(S) is the number of distinct orderings. The correction is ≤ Σ_{repeats}|G|.
2. **The telescope.** Ordered_R − Ordered_Q = Σ_j (H_j − H_{j−1}), where H_j has its first j coordinates realised and the
   rest rational, with no cross-ordering. G depends only on the product and the maximum, so it is symmetric, and mixed
   tuples are well defined (values are reals).
3. **One replacement.** Fix the others, with m_j and M′.
   - The filter max(p, M′)m_jp < u gives p < √(u/m_j) if M′²m_j ≤ u, and p < u/(M′m_j) otherwise.
   - The support u/(m_jp) ≥ X₀ gives p ≤ u/(X₀m_j).
   - So the admissible set is [X₀⁻, b), as stated. Realised p start at X₀⁻ and rational p at X₀.
   - Since the base primes are common, π_𝒩 − π equals (jittered) − (rational ≥ X₀) exactly, and Δ_ψ differs from this
     only by prime powers of large primes.
4. **Abel summation.**
   - |(G/log)′| ≤ (1 + 1/Λ + 1/log p)·G/(p log p) ≤ 1.1·G/(p log p).
   - The boundary is ≤ 5κ f₀ log b/m_j. The paper's 10 is generous.
   - The integral is ≤ 5.5κ(f₀/m_j)·log²b/2 = 2.75κ f₀ log²b/m_j.
   - Prime powers: Σ_{p≥X₀⁻, k≥2} G(p^k) ≤ sup f₀/(m_jX₀⁻), which is negligible.
   - With f₀ ≤ 1/Λ, one replacement costs ≤ 4κ log²u/(m_jΛ).
5. **Product set.**
   - Σ_{d∈𝒟} 1/d = Π_{p<X₀}(1−1/p)⁻¹ ≤ 1.01e^γΛ.
   - ℓ_u: in the realised system, Lemma cm(iv) at y = X₀⁻ applies. Its sum includes the rational primes in (X₀⁻, X₀), so the
     jittered-only sum is smaller. In the rational system, Mertens applies.
   - Each other variable ranges over its own system, so Σ1/m_j ≤ 1.01e^γΛℓ_u^{r−1}.
   - Per r: (r/r!)·4κ(log²u/Λ)·1.01e^γΛℓ_u^{r−1}. Summed over r: 4.04e^γκ log²u·e^{ℓ_u}.
   - The diagonal is ≤ (1/Λ)·1.01e^γΛ·e^{ℓ_u}/(X₀⁻Λ).
   - Total ≤ 4.1e^γκ log²u·e^{ℓ_u} ≤ 7.4κ(log u)³/Λ. In arb, 4.1e^γ = 7.3024, with the factor e^{2.2/Λ} included.
   - **No range condition is used** (see C4).
6. **The rest.**
   - **Decision-order mismatch.**
     - |τ_w − P| ≤ H/2, because t(p*) ≤ p* + H/2 ≤ P + H/2 and τ_w ≥ t(P) ≥ P − H/2.
     - So a mismatch needs |u/w − P| ≤ H/2, which gives |P − √(u/w′)| ≤ H/4 + o(1).
     - At most 1.5H + 2 primes can lie there: they land from slots in an interval of length 1.5H.
     - Total ≤ 2.02(H(X₀)+1)(log u+1)X₀⁻¹ sup|h|.
     - Edge case: if the top prime is a rational prime in (X₀⁻, X₀), the same count applies.
   - **Partial windows.** blin(3).
   - **O(1/(κu)).**
   - All of these are ≤ 10⁻³κ(log u)³.

### (c)
- **The first-bullet bound.**
  - |S(t) − H_⌊t⌋| ≤ η₁(1 + log 2) and |H_⌊t⌋ − log t| ≤ 1, so |e| ≤ 1.002.
  - The Stieltjes step gives log U + 2.004/log y.
- **Rankin.**
  - Σ_{m′≥Z, P⁺≤y} 1/m′ ≤ Z^{−2/log y}Π_{p≤y}(1 − p^{2/log y−1})⁻¹ with Z = x/y, so Z^{−2/log y} = e^{−2(U−1)} = v⁻⁴.
  - The constant 2e^γe^{Ein(2)} is ample: for rational primes, Π/(e^γe^{Ein(2)}log y) = 0.883, 0.890, 0.905, 0.918, 0.930
    at y = 10³…10⁷.
- **Arithmetic.**
  - The second bound is applicable for v ≥ 4, since v ≥ 1 + 2 log v there.
  - Ein(2) (paper's convention) = 3.68387.
  - I₁ = 14.9154, I₂ = 214.771, I₃ = 6.6962. These are numerical Simpson values in arb, not interval-certified.
  - (2.02/log 2)(I₁+I₂+I₃) = 688.88 ≤ 690, and 690/Λ = 6.9·10⁻⁶.
- **But:** the ν₁ partial windows are not covered. See F1.

### (d)(i)
- μ_edge(x/n) ≠ 0 implies n < (1+κ)x/(2X₀) < X₀^{0.9}.
- n·P⁺(n) ≤ n² < x for x ≤ X₀^{1.9}, so c_n = μ(n).
- N < 1.01X₀^{0.9}.
- Proper divisors d have x/d > X₀ (the cut-off).
- Σ_{d|N, d<N} μ(d) = −μ(N).

### (d)(ii)
- The N lie in an open interval of length κx/X₀ ≤ X₀^{−0.3867} < 1.
- A negative term needs μ(N) = 1, so N ≥ 6.
- **Edge density.** On the edge, MA ≤ (1+Λ⁻³)/Λ: eq:huxley at X₀ applies with I = [X₀, (1+κ)q], since |I| < κq. A short I
  holds ≤ X₀^{−0.01}κq primes.
- **The bound.** (1.0001/6)(1 + 2/Λ) = 0.166683 ≤ 0.167, and the expression decreases in N.

### (d)(iii)
- **The coefficient formula.**
  - For n < N, n ≤ N/2, so x/n ≥ 2x/N > X₀.
  - For primes q ≤ p, q·n ≤ pN/2 ≤ (1+κ)x/2 < x, so χ depends only on N_>.
  - The coefficient is −μ(N)χ_{N_>}(x)·1[N_≤ > 1].
- **Monotone numerators.** Primes enter the window [X₀, (1+κ)x/N] and χ switches on, both monotone in x with sign −μ(N).
- **|g| bounds.**
  - Σ_{N∈(a,(1+κ)a)} 1/N ≤ κ + 1/a, so |g| ≤ 1.0001(κ + X₀/x)/Λ.
  - Since x > 2X₀/(1+κ), |g| ≤ 0.51/Λ.
  - At x = X₀^{1.01}/2, |g| log x ≤ 2.03X₀^{−0.01} ≤ 3X₀^{−0.01}.
- **Total variation.**
  - Per N-term: the rise is ≤ max|num|·(1+κ)²/(κx_start), and then there is the drop to 0. Total ≤ 2.0003(1+κ)²/(NΛ),
    against the paper's 3.1/(NΛ).
  - The term starts at 0, because X₀ is even.
  - TV(g; [α,β]) ≤ (3.1/Λ)(log(β/α)+1). Here g vanishes below 2X₀/(1+κ), and Σ1/N ≤ log(β/α) + κ + (1+κ)/2.
- **Resolvent identity.** A⁻¹ − B⁻¹ = A⁻¹(B − A)B⁻¹ with A = 1+K_pt and B = 1+K′_ℚ. Both are Volterra on functions on
  [X₀⁻, ∞), and g = 0 below 2X₀/(1+κ), so the cut-offs are immaterial.
- **Where the difference vanishes.** (K′_ℚ − K_pt)g(u) = 0 for u < 2X₀X₀⁻/(1+κ):
  - cofactors < X₀⁻ are rational, with τ = P⁺, and both filters are strict;
  - other cofactors are ≥ X₀⁻ and need u/w > 2X₀/(1+κ).
- **Discrete Abel summation over the merged atoms**, with φ = g̃·a, a(t) = 1/(m_jt log t), g̃(t) = g(u/(m_jt)):
  - boundary ≤ (0.51/Λ)·5κ log b/m_j = 2.55κ log b/(m_jΛ), against the paper's 5.1;
  - differences of a, ≤ (0.51/Λ)·5κ∫(log t + 1)dt/t, give ≤ 1.275κ(log²b + 2 log b)/(m_jΛ), against the paper's 1.40;
  - variation ≤ 5κ log b·(3.1/Λ)(log(b/X₀⁻)+1)/m_j ≤ 15.5κ log²b/(m_jΛ), since log X₀⁻ ≥ 1;
  - prime powers: ≤ sup|g|/(m_jX₀⁻), which is negligible (see C6).
- **The constant 17.** (5.1 log b + 1.40(log²b + 2 log b) + 15.5 log²b)/log²b equals exactly 17.000 at log b = 79, and it is
  smaller for log b ≥ 79. Here log b ≥ log X₀⁻ ≈ 10⁸, where the ratio is 16.90.
- **Summation.** As in Step 3, 17·1.01 = 17.17 ≤ 17.2, and 17.2e^γ = 30.634 ≤ 31.
- **The rest.** The mismatch is ≤ 2.02(H(X₀)+1)(log u+1)X₀⁻¹·0.51/Λ. There are no partial windows. So
  |(K′_ℚ − K_pt)g| ≤ 31κ(log u)³/Λ + tiny ≤ 4κ(log u)³.
- **Lemma M.**
  - log x·|ρ_edge − g| ≤ log x·(log x + 1)·4κ(log x)³ ≤ 4.1κ(log x)⁵.
  - With κ ≤ X₀^{−0.3966} and log x ≤ X₀^{0.01}, this is ≤ 4.1X₀^{−0.3466} ≤ X₀^{−0.34}.

## 4. The resolvent

- (1+K_pt)⁻¹ is used only through Lemma M: c_n = μ(n)χ^t_y(n)·1[y/n ≥ X₀⁻], so |c_n| ≤ 1, and
  Σ_{n≤y/X₀⁻} 1/n ≤ log y − Λ + 1.
- It is Volterra, so no Neumann norm is needed.
- The bound on |ρ_edge − g| needs the bound on (K′_ℚ − K_pt)g at every u ≤ x. That is available on Good(<x) for
  log x ≤ X₀^{1/100}.
- In the toy (§7), Lemma M agrees with the direct recursion in the realised system, in decision order.

## 5. The consumers

**Prop g1(A).**
- On [X₀+H, X₀^{1.01}]: 0.99 − 0.167 − 6·10⁻⁴ − X₀^{−0.34} − e^{−80} ≥ 0.8223, so ≥ 0.822.
- On [X₀^{1.01}/2, X_sw]: 0.99 − 6·10⁻⁴ − 2X₀^{−0.34} − 3X₀^{−0.01} − e^{−80} ≥ 0.989.
- μ₁'s response is C_S·7·10⁻⁶ ≤ 5.4·10⁻⁴ ≤ 6·10⁻⁴.
- μ₀'s response is 2κ(log x)⁴(log x + 1) ≤ 2.1κ(log x)⁵.

**Thm g2.**
- For x ≥ X₀^{1.01}: W_x ⊂ [X₀^{1.01}/2, ∞), which gives 0.97.
- For 2X₀ ≤ x < X₀^{1.01}: W_x ⊂ [X₀+H, X₀^{1.01}+H/2], and both of Prop g1's ranges give ≥ 0.82.
- The switch at X₀^{1.01} = X₀e^{0.01Λ} coincides with the end of j_{X₀}'s small range.

**Prop pointwise.**
- (a) For t ≥ X₀^{1.01}: j ≤ e^{−0.0009Λ}, which gives ≥ 0.96 − o(1).
- (b) 0.822 − 0.4209 − 10⁻¹² = 0.4011 ≥ 0.399. The edge dip, which is worst at N = 6, and the worst case of j_{X₀}, near 6X₀,
  are added, so their coincidence is already paid for.
- (c) 0.739 ≥ 0.73 on [X₀, 2X₀), with no use of Section 6 beyond (a).

**Cor r1.**
- m log t ≥ 0.399 on [X₀, ∞), and m = 0 below X₀.
- 0.399 ≥ 1.01c′ = 0.1515, so c′ = 0.15 and K_d = 3 stand.

**Ranges and overlaps.** All correct.

**The Use paragraph (06:376–384).**
- c′/(8·77) = 2.435·10⁻⁴, which is 34.8 times 7·10⁻⁶.
- The bound (0.0048/κ)^{1/5} = X₀^{0.0793} ≥ X₀^{0.01}.

---

## 6. Defects

### F1 (FIXABLE): the ν₁ partial windows inside μ₁

**Where.**
- 06-base-range.tex:156, the definition of μ₁.
- 06-base-range.tex:274–275, the proof of (c).
- The statement of (c) at 06:174–185, including eq:mu1sum, inherits the gap.

**What is wrong.**
- **What μ₁ contains.** μ₁ := (K_ℚ − K_pt)(f₁1_{[X₀,∞)}) uses the window-filtered K_ℚ, which acts through the measure ν₁. So
  μ₁ contains, for every m′ with P⁺(m′) ∈ (q, (1+κ)q] and q = x/m′ ≥ X₀, the partial-window components
  m′⁻¹·MA_{κq}[ν₁|_{[P⁺(m′),∞)}](q) = m′⁻¹·(π([P⁺(m′), (1+κ)q]) − ∫_{P⁺(m′)}^{(1+κ)q} dt/log t)/(κq).
- **What the proof charges.** It "drops the restrictions" and charges every component |f₁(q)|/m′ ≤ η_H(q)f₀(q)/m′.
- **Why that charge fails.** For partial windows, [P⁺(m′), (1+κ)q] can be shorter than (2q)^{7/12}. Then eq:huxley says
  nothing about it, and the interval always contains the prime P⁺(m′) itself.
- **The true size.**
  - Each such component is ≤ 1.01/Λ.
  - Their total weight is ≤ 0.51κ(log x+1) (blin(3)).
  - So their contribution is ≤ κ log x/Λ. This is negligible on range (A), where it is ≤ X₀^{−0.38}/Λ, but it grows with
    log x.
- **Consequence.** The statement "(c) for every x ≥ X₀", and eq:mu1sum summed over all dyadic u ≥ X₀, are not proved as
  written. Only u ≤ x ≤ X_sw is ever consumed: Prop g1(A), via Cor saias.
- **Toy evidence.** X₀ = 100, κ = 0.15, 400 points in [10⁴, 4·10⁶].
  - The ν₁ partial components exceed the |f₁(q)|/m′ charge at 123 of 400 points.
  - The ν₁ partial part reaches 2.0× the charge Σ|f₁(q)|/m′ over the partial m′.
- **The author's own descriptions** already put all partial windows in μ₀: 06:269 ("the partial windows of Lemma blin(3)"
  in μ₀'s "rest") and 04f:159 ("This smooth part contains … the partial windows"). Only the formal definition at 06:156–157
  disagrees.

**The fix.** Use the sharp rational operator in μ₁, and move the partial windows of the whole prime measure into μ₀.
The four edits below also absorb C2.

1. **06:156.** Current:
   ```
     \mu_1:=(K_{\mathbb Q}-K_{\mathrm{pt}})(f_1\mathbf 1_{[X_0,\infty)}),\\
   ```
   Replacement:
   ```
     \mu_1:=(K^{\mathrm{sh}}_{\mathbb Q}-K_{\mathrm{pt}})(f_1\mathbf 1_{[X_0,\infty)}),\\
   ```

2. **06:157.** Current:
   ```
     \mu_0:=(K_{\mathbb Q}-K_{\mathrm{pt}})(f_0\mathbf 1_{[X_0,\infty)})+(\text{decision-order mismatches})+O(1/(\kappa x)).
   ```
   Replacement:
   ```
     \mu_0:=(K^{\mathrm{sh}}_{\mathbb Q}-K_{\mathrm{pt}})(f_0\mathbf 1_{[X_0,\infty)})+(K_{\mathbb Q}-K^{\mathrm{sh}}_{\mathbb Q})(\mathrm{MA}[\mathbb P]\mathbf 1_{[X_0,\infty)})+O(1/(\kappa x)).
   ```

3. **Insert after 06:159** (the line `\]` that closes the display), before `So $\mu_{\mathrm{edge}}$ is the part ...`:
   ```
   Here $K^{\mathrm{sh}}_{\mathbb Q}h(x):=\sum_{m\ge2}m^{-1}\mathbf 1[P^+(m)\le x/m]\,h(x/m)$ is the sharp form of $K_{\mathbb Q}$. The
   difference $K_{\mathbb Q}-K^{\mathrm{sh}}_{\mathbb Q}$ consists exactly of the partial windows $P^+(m')\in(q,(1+\kappa)q]$ of
   Lemma~\ref{lem:blin}(3), so all partial windows of $\mathrm{MA}[\mathbb P]$ above $X_0$ are in $\mu_0$, and $\mu_0+\mu_1=(K_{\mathbb Q}-K_{\mathrm{pt}})(\mathrm{MA}[\mathbb P]\mathbf 1_{[X_0,\infty)})+O(1/(\kappa x))$.
   ```

4. **06:233–234.** Current:
   ```
   $(K_{\mathrm{pt}}-K_{\mathbb Q})f_0(u)=\sum_{w\in\NN}F(w)\chi_w-\sum_{m\in\N}F(m)\chi_m$, where $F(v):=f_0(u/v)/v$ and $\chi$ is the
   latest-prime filter ($P^+\le u/v$, in value order; the decision-order mismatch is treated below). Write each cofactor as
   ```
   Replacement:
   ```
   $(K_{\mathrm{pt}}-K^{\mathrm{sh}}_{\mathbb Q})(f_0\mathbf 1_{[X_0,\infty)})(u)=\sum_{w\in\NN}F(w)\chi_w-\sum_{m\in\N}F(m)\chi_m$, where $F(v):=f_0(u/v)/v$ and $\chi$ is the
   latest-prime filter ($P^+\le u/v$, in value order; the decision-order mismatch $K_{\mathrm{pt}}-K^{\mathrm{val}}_{\mathrm{pt}}$ is treated below). Write each cofactor as
   ```

5. **06:269–270.** Current:
   ```
   $h=g$ in (d)). The other items are the partial windows of Lemma~\ref{lem:blin}(3) (at most $\kappa\log u/\Lambda$),
   $|f_0-1/\log q|\le\kappa/\log^2q$, and $O(1/(\kappa u))$.
   ```
   Replacement (this also does C6a):
   ```
   $h=g$ in (d)). The other items are the partial windows $(K_{\mathbb Q}-K^{\mathrm{sh}}_{\mathbb Q})(\mathrm{MA}[\mathbb P]\mathbf 1_{[X_0,\infty)})$
   (at most $\kappa\log u/\Lambda$ by Lemma~\ref{lem:blin}(3), each component having density $\le1.01/\Lambda$) and $O(1/(\kappa u))$.
   ```

6. **06:274–275.** Current:
   ```
   $|\mu_1|\le|K_{\mathbb Q}f_1|+|K_{\mathrm{pt}}f_1|$, and both are bounded in the same way; the restrictions $P^+(m')\le x/m'$ are simply
   dropped.
   ```
   Replacement (this also does C3):
   ```
   $|\mu_1|\le|K^{\mathrm{sh}}_{\mathbb Q}(f_1\mathbf 1_{[X_0,\infty)})|+|K_{\mathrm{pt}}(f_1\mathbf 1_{[X_0,\infty)})|$. Both are sums of
   $|f_1(x/m')|/m'$ over cofactors with $x/m'\ge X_0$, with $|f_1(q)|\le\eta_{\mathrm H}(q)f_0(q)$ (both operators are sharp, so no
   partial window occurs), and both are bounded in the same way. The latest-prime filter is dropped in the first bullet and kept in
   the second, where it reads $P^+(m')\le y$ for $K^{\mathrm{sh}}_{\mathbb Q}$ and $P^+(w)<y+H(y)$ for $K_{\mathrm{pt}}$.
   ```

7. **06:290** (C3, continued). Current:
   ```
   \item Components with $q\in[X_0,y)$ have $\eta_{\mathrm H}\le\Lambda^{-3}$, $1/\log q\le1/\Lambda$, and $m'\ge x/y$ with $P^+(m')\le y$. Rankin's
   ```
   Replacement:
   ```
   \item Components with $q\in[X_0,y)$ have $\eta_{\mathrm H}\le\Lambda^{-3}$, $1/\log q\le1/\Lambda$, and $m'\ge x/y$ with $P^+(m')\le y+H(y)$
   (the primes in $(y,y+H(y)]$ change the Euler product below by a factor $\le\exp(8H(X_0)/X_0)\le1+e^{-0.9\Lambda}$, absorbed by its factor $2$). Rankin's
   ```

**Effect.**
- (c) and eq:mu1sum then hold as stated, for every x ≥ X₀ and over all dyadic u.
- μ₀ gains nothing new: its "rest" already budgeted κ log u/Λ for the partial windows of the prime measure. That is exactly
  (K_ℚ − K_ℚ^sh)(MA[ℙ]1), since the f₀ and f₁ partial parts add up to the prime-measure part.
- The bound |μ₀| ≤ 2κ(log u)³ is unchanged.
- No constant changes anywhere, and Prop g1, Thm g2, Prop pointwise and Cor r1 are unaffected.

**Minimal alternative.** Keep 06:156–157, and restrict (c) and eq:mu1sum to log x ≤ X₀^{1/100}, adding the term
0.52κ(log x+1)·2.02/Λ to the bound. This is negligible there.

### C1 (COSMETIC): ρ_osc in eq:shdecomp is identically 0 with the definition at 06:133

**The issue.**
- ρ^sh := (1+K_pt)⁻¹(T′_cont − R′ + ρ̄_𝒜) = (1+K_pt)⁻¹((1−ρ_det)1_{[X₀,∞)}) contains no R′.
- Yet eq:shdecomp carries ρ_osc, "the response to R′".
- The symbol also clashes with 04a's ρ^sh := Σc_nT′(·/n)/n, which includes R′ and σ_𝒜.
- Prop g1(A) (04f:149) uses the correct form, (1+K_pt)⁻¹(1−ρ_det) = MA + ρ_edge + (1+K_pt)⁻¹(μ₀+μ₁).

**Edits.**
- **06:146.** Current:
  ```
    \rho^{\mathrm{sh}}=\mathrm{MA}[\mathbb P]+\rho_{\mathrm{osc}}+\rho_{\mathrm{edge}}+(1+K_{\mathrm{pt}})^{-1}(\mu_0+\mu_1),\qquad
  ```
  Replacement:
  ```
    \rho^{\mathrm{sh}}=\mathrm{MA}[\mathbb P]+\rho_{\mathrm{edge}}+(1+K_{\mathrm{pt}})^{-1}(\mu_0+\mu_1),\qquad
  ```
- **06:149.** Current:
  ```
  where $\rho_{\mathrm{osc}}$ is the response to $R'$ and the absorbed source is carried in Section~\ref{sec:noise}. Here we split
  ```
  Replacement:
  ```
  so $\rho^{\mathrm{sh}}$ here is the part of the sharp reference of Section~\ref{sec:noise} that comes from $1-\rhodet$; the responses
  to $R'$ and to the absorbed source $\sigma_{\Abs}$ are carried in Section~\ref{sec:noise}. Here we split
  ```

### C2 (COSMETIC): μ₀ counts the decision-order mismatch twice (06:157)

**The issue.**
- (K_ℚ − K_pt) already contains the decision-order mismatch, because K_pt is the decision-order operator.
- Adding "(decision-order mismatches)" in the definition is redundant, or reads as a second copy.
- The mismatch belongs in the proof, through the split K_ℚ − K_pt = (K_ℚ − K_ℚ^sh) + (K_ℚ^sh − K_pt^val) + (K_pt^val − K_pt).

**Edit.** F1 item 2 removes it. If F1 is not adopted, use this instead.
- **06:157.** Current:
  ```
    \mu_0:=(K_{\mathbb Q}-K_{\mathrm{pt}})(f_0\mathbf 1_{[X_0,\infty)})+(\text{decision-order mismatches})+O(1/(\kappa x)).
  ```
  Replacement:
  ```
    \mu_0:=(K_{\mathbb Q}-K_{\mathrm{pt}})(f_0\mathbf 1_{[X_0,\infty)})+O(1/(\kappa x))\quad(\text{it contains the decision-order mismatch, since }K_{\mathrm{pt}}\text{ uses decision order}).
  ```

### C3 (COSMETIC): (c) says the filter is dropped, but bullet 2 uses it (06:274–275 against 06:290)

**The issue.**
- Rankin's bound in bullet 2 needs P⁺ ≤ y.
- For K_pt, the filter τ_w < q gives only P⁺(w) < q + H(q)/2 ≤ y + H(y).
- The extra primes are harmless: they change the Euler product by a factor ≤ 1 + e^{−0.9Λ}.

**Edit.** F1 items 6 and 7 give the exact replacement text.

**Also noted, no change proposed.** The statement's "log v + 1.01" and "log U + 1.01" (06:176, 06:180) are weaker than the
"+0.01" the proof gives. The certified I₁ uses 1.01, so leave them as they are.

### C4 (COSMETIC): leftover range condition "log log u ≤ Λ/8" (06:170, 06:372, 04f:158)

**The issue.**
- The condition dates from before correction #53, when the total carried the factor (1 + ℓ_u).
- With symmetric telescoping, the totals 7.4κ(log u)³/Λ and 31κ(log u)³/Λ need no range condition. Steps 1–2 and "the rest"
  hold for every u ≥ X₀ on Good(<u).
- The hypothesis is harmless: range (A) has log log x ≤ Λ/100. These edits are optional.

**Edits.**
- **06:170.** Current:
  ```
  \item \emph{(Smooth part.)} On $\Good(<u)$, for every $u\ge X_0$ with $\log\log u\le\Lambda/8$,
  ```
  Replacement:
  ```
  \item \emph{(Smooth part.)} On $\Good(<u)$, for every $u\ge X_0$,
  ```
- **06:372.** Current:
  ```
  $|(K'_{\mathbb Q}-K_{\mathrm{pt}})g(u)|\le4\kappa(\log u)^3$ for $\log\log u\le\Lambda/8$. By
  ```
  Replacement:
  ```
  $|(K'_{\mathbb Q}-K_{\mathrm{pt}})g(u)|\le4\kappa(\log u)^3$. By
  ```
- **04f:158.** Current:
  ```
  \item $|\mu_0(u)|\le2\kappa(\log u)^3$ for $u\ge X_0$ with $\log\log u\le\Lambda/8$, which contains range (A)
  ```
  Replacement:
  ```
  \item $|\mu_0(u)|\le2\kappa(\log u)^3$ for every $u\ge X_0$, in particular on range (A)
  ```

### C5 (COSMETIC): "Ein" uses a non-standard convention defined only in another section (06:181, 06:292)

**The issue.**
- The paper's Ein(a) := ∫₀^a (e^t − 1)dt/t (03-zeros:101) equals −Ein_std(−a). At a = 2 it is 3.68387.
- The standard Ein(2) = ∫₀²(1 − e^{−t})dt/t ≈ 1.32.
- Section 6 uses Ein without a definition.

**Edit.**
- **06:181.** Current:
  ```
    \qquad\operatorname{Ein}(2)<3.69.
  ```
  Replacement:
  ```
    \qquad\operatorname{Ein}(2):=\int_0^2(e^t-1)\,\frac{dt}t=3.6838\ldots<3.69.
  ```

### C6 (COSMETIC): a stray "rest" item, and prime powers not mentioned in (d)(iii)

**(a) 06:270.** "|f₀ − 1/log q| ≤ κ/log²q" is listed as a term of μ₀'s "rest", but μ₀ is built from f₀ itself, and no step
compares f₀ with 1/log q. The item is a leftover. F1 item 5 deletes it. If F1 is not adopted:
- Current:
  ```
  $|f_0-1/\log q|\le\kappa/\log^2q$, and $O(1/(\kappa u))$.
  ```
- Replacement:
  ```
  and $O(1/(\kappa u))$.
  ```

**(b) 06:360–361.** The discrete Abel summation of (d)(iii) runs over the atoms of ψ_𝒩 and ψ, but the sum to be bounded runs
over primes. The prime powers of the large primes are not mentioned, though Step 3 of (b) mentions them. Their cost is
≤ sup|g|/(m_jX₀⁻).
- Current:
  ```
  As $g$ is not smooth, the Abel summation of one replacement is done discretely, over the merged atoms of $\psi_{\NN}$ and $\psi$ in
  $[\Xm,b]$. With $\tilde g(t):=g(u/(m_jt))$, the product rule splits each difference of $\tilde g(t)/(m_jt\log t)$ into a
  ```
- Replacement:
  ```
  As $g$ is not smooth, the Abel summation of one replacement is done discretely, over the merged atoms of $\psi_{\NN}$ and $\psi$ in
  $[\Xm,b]$ (the prime powers of the large primes cost at most $\sup|g|/(m_j\Xm)$). With $\tilde g(t):=g(u/(m_jt))$, the product rule splits each difference of $\tilde g(t)/(m_jt\log t)$ into a
  ```

---

## 7. Toy results

**Setup.**
- The rational system ℕ.
- A synthetic realised system:
  - the rational primes < X₀, with t(p) = p;
  - jittered primes with value = slot + H(U − ½) and decision time = slot ≥ X₀;
  - slots at 90% of the rational primes ≥ X₀, plus extra slots at rate 0.1/log n;
  - two forced landings below X₀, at 98.9 and 99.6.
- Parameters: X₀ = 100, κ = 0.15, H = 4, X₀⁻ = 98. There are 5,323 jittered primes and 45,488 realised elements ≤ 4.3·10⁴.
- Every operator is implemented from the paper's definitions, with K_ℚ in component (measure) form.

**Identities (machine precision).**

| Check | Points | Max residual |
|---|---|---|
| Lemma M (realised, decision order) vs direct recursion (1+K_pt)ρ = h | 25, x ≤ 6·10⁴ | 1.4·10⁻¹³ |
| eq:ratid against the exact (κx − #ℤ)/(κx) | 300 | 7·10⁻¹⁵ |
| K_ℚMA − K_ℚ(MA·1) − μ_edge | 300 | 1·10⁻¹⁵ |
| eq:shdecomp | 15 | 2.5·10⁻¹⁶ |
| (d)(i) on [X₀, X₀^{1.9}] | 400 | 1.7·10⁻¹⁷ |
| (d)(iii) coefficient formula vs the Lemma-M expansion of g | 300, x ≤ 3·10⁵ | 5.4·10⁻¹⁷ |
| Resolvent identity ρ_edge − g = (1+K_pt)⁻¹(K′_ℚ − K_pt)g | 14, x ∈ [1.9·10⁴, 2.4·10⁵] | 1.2·10⁻¹⁷ |

- (K′_ℚ − K_pt)g ≡ 0 below 2X₀X₀⁻/(1+κ) = 17,043.5, at all 300 test points.
- |ρ_edge − g| ≤ (Σ1/n)·sup|(K′_ℚ − K_pt)g| at all 14 points, with ratio ≤ 0.17.

**g (d)(iii).**
- Monotone-numerator violations: 0, for N < 3000 at 3000 points per window.
- max N·TV(T_N)/max MA_edge = 2.12, against the paper's 3.1/1.0001.
- max |g|/(max MA·(κ + X₀/x)) = 0.42, over 2000 points.

**Telescope, h = f₀1** (11 values of u in [2.5·10⁵, 4.1·10⁶], two large primes from u ≈ 10⁶).
- Multiset = ordered/2 + diagonal, exactly.
- The telescope sum equals the direct difference (K_pt^val − K_ℚ^sh)(f₀1) to ≤ 6·10⁻¹⁵.
- The discrete Abel identity is exact to ≤ 9·10⁻¹⁸.
- Per replacement, 0 violations of |δ| ≤ the exact Abel bound, and 0 violations of |δ| ≤ the paper-form bound (5κ replaced
  by the measured sup|Δ_θ|/(t log²t) = 6.3·10⁻³).
- The chain of totals:
  - |direct| = 0.0154–0.0250;
  - ΣAbel = 0.0182–0.0297;
  - Σ paper-form = 0.154–0.230;
  - closed form = 2.9–4.7.
- Diagonal ≤ 2.6·10⁻⁴.
- Decision-order mismatch (K_pt − K_pt^val)f₀: 3·10⁻⁵–2·10⁻⁴.

**Telescope, h = g** (8 values of u in [10⁶, 4.1·10⁶]).
- The telescope identity holds to ≤ 7·10⁻¹⁷.
- |direct| = 3.7·10⁻⁴ to 6.6·10⁻⁴.
- ΣAbel = 0.030–0.037.
- Σ paper-form = 0.62–0.98. Here 0.51/Λ and 3.1/Λ are replaced by their toy values, 0.246 and 1.05.
- 0 violations per replacement.

**Partial windows (F1).**
- Partial weight 0.03–0.07, against the blin(3) count bound of 0.17–0.50.
- The ν₁ partial components exceed the |f₁|/m′ charge at 123 of 400 points, by up to 2.0×.

**Constants (python-flint arb).**
- Ein(2) = 3.68387.
- I₁ = 14.9154, I₂ = 214.771, I₃ = 6.6962 (Simpson; not interval-certified). (2.02/log 2)ΣI = 688.88, and 690/Λ = 6.9·10⁻⁶.
- 4.1e^γ = 7.3024.
- The 17 breakdown is 17.000 at log b = 79 and 16.90 at 10⁸.
- 17.2e^γ = 30.634.
- 0.166683; 0.8224; 0.4011; and c′/(8·77)/(7·10⁻⁶) = 34.8.
- The Rankin product ratio is 0.88–0.93, against the allowed 2.

## 8. Confidence and limitations

**Confidence.**
- High for the identities, the mixed telescope with its Abel and variation chain, (d)(i)–(iii), and the consumer
  arithmetic.
- High that F1 is a real gap in the written proof of (c) and that it is harmless to every consumer.

**Limitations.**
- The toys run at Λ ≈ 4.6 with a synthetic realised system. They test exact structure and intermediate inequalities, not
  the asymptotic constants.
- Taken as given: Lemma cm, Cor saias, Prop La/eq:lag, Lemma xb and j_{X₀}, eq:huxley/X_Hux, range (B) of Prop g1, and the
  noise terms.
- The integrals I₂ and I₃ were checked numerically only. Appendix B certifies them.

**Scripts** (all in `/tmp/rhscratch/r15/`):
- toy_ops.py
- t1_identities.py
- t2_edge_g.py
- t3_resolvent.py
- t4_telescope.py
- t4b_telescope.py
- t5_partial.py
- consts.py
- rankin.py
