# Follow-up S1: Theorem A for every fixed θ ∈ (0, ½ − 10⁻⁴] (branch followup-s1)

Status (2026-10-31): paper and certificates only. One AI agent (Claude) wrote it. The design was scoped
(/tmp/rhscratch/ext/onezero.md, plan S1) and adversarially checked (/tmp/rhscratch/ext/onezero_check.md: "holds with fixes")
by two earlier AI agents. **The text written here passed one independent AI check (every item, including Step 5 by hand with
the inherited raised-range bounds, and all scripts reproduced); no human review.** Formalized in Lean
(branch lean-s1, 2026-10-31): `BModel.theoremA_full : Huxley84 → Theorem21` with Theorem21 = ∃ X_Hux ∀ θ ∈ (0, ½ − 10⁻⁴]
(see *Lean* below).

Commits on followup-s1 (from development 37e7339): fe3cb23 (paper), ab8db31 (certificates, App. B, README, depcheck), and the
commit that adds this file.

## Result

Theorem A now covers **every fixed θ ∈ (0, θ₁], θ₁ = ½ − 10⁻⁴**, with the same X₀ regime (X₀ ≥ max(e^{10⁸}, X_Hux)). X₀ does
not depend on θ. The only θ-dependent choice is the first switch-on point: x₁ ≥ exp(X₀²) **and θ log x₁ ≥ 9(log log x₁)²**.
This is automatic for θ ≥ 36Λ²/X₀². Since L/ℓ² increases, it then holds at every x ≥ x₁.

Statement (i) is now explicit:

    |N(x) − x| ≤ C_{X₀}x^θ + 2x^θ log*x + D_max(x) + h(x)Λ⁻⁸   (x ≥ 1),

with these terms:
- C_{X₀} = 2∏_{p<X₀}(1 − p^{−θ})⁻¹ (Rankin). It depends on θ, as before.
- D_max(x) := B(x⁺) + 3H(x⁺) + 5, with x⁺ = max(x, X₀). Then D_max ≤ x^{3·10⁻⁵}, D_max ≤ 65X₀¹⁵ for ℓ ≤ ℓ_std, and
  D_max ≤ 3.01e^{8ℓ²} for ℓ ≥ ℓ_std.
- h is the θ-free absorption window below, with h ≤ x^{1/8} and h = x^{o(1)}.

Hence N = x + O_{X₀,θ}(x^θ log*x). Statement (ii), the zeros with Re ρ_k = 1 − (log log x_k + O(1))/log x_k, is unchanged.

## Design changes

1. **θ-free absorption window** (01-setup params row "window h"; 02-construction §target):

       h(u) := u^{1/8}                                          for L := log u ≤ 400Λ²,
       log h(u) := max(50Λ², 27Λℓ², 120ℓ⁴/log ℓ)               for L ≥ 400Λ²   (ℓ = log L).

   Its properties:
   - It is continuous: both pieces equal e^{50Λ²} at L = 400Λ², since 27Λℓ² ≤ 50Λ² there.
   - It is piecewise C¹, with b := d log h/d log u ∈ [0, 1/8]. Hence h is non-decreasing, h ≤ u^{1/8}, and h(u)/u is decreasing.
   - It replaces h = u^{θ_b}, θ_b = min(θ, max(θ/2, 1/8)).
2. **(La) in explicit form** (03-zeros Prop La, eq:La, new eq:Dmaxstd):
   - The bound is |D| ≤ D_max(x) = B(x⁺) + 3H(x⁺) + 5. It replaces |D| ≤ x^η, η = min(θ, ½−θ)/2.
   - D_max ≤ 3e^{8ℓ²} + 17e^{4ℓ²+2ℓ} + 5 ≤ 3.01e^{8ℓ²} for ℓ ≥ ℓ_std, using H = H_std and B ≤ 17L²H_std^{1/2} (Theorem queue).
   - The crude form log D_max ≤ 8ℓ² + 10⁻⁶L + 2 (≤ 3·10⁻⁵L) is kept, but only for goodheights and §6. The checker's warning
     is respected: the crude form is not enough for the late noise or for o_R. These now read eq:Dmaxstd.
3. **Switch-on**: θ log x₁ ≥ 9(log log x₁)² (01-setup params "switch-on", Theorem A statement).
4. **θ' := 0.26** in the local PNT (04e). It was max(θ + 0.01, 8(log log X₀)²/log X₀ + 0.005).
   - D₀ := B + 3H + 4 + h(u)Λ⁻⁸ ≤ u^{3·10⁻⁵} + u^{1/8} ≤ u^{0.26}.
   - Every other use of θ' needs only θ' ≤ 0.51 (σ − θ' ≥ 0.48, v^{θ'−1}).

## Where each change is made (paper/sections)

| file | change |
|---|---|
| abstract, 00-intro | θ ∈ (0, ½ − 10⁻⁴]. Remark that X₀ is θ-free. The "Zeros" sketch quotes D_max = e^{O(ℓ²)}. |
| 01-setup | Opening paragraph; Theorem A (new (i), condition on x₁); proof of (i) (N − x = D + E + R); params rows θ/θ′, window h, (La), switch-on; logic table (T1 ← caplw(b)); edge count 197 → 198. |
| 02-construction | h defined as the params window; T1 statement \|E\| ≤ C_{X₀}x^θ + h(x)Λ⁻⁸; **T1 deficit proof rewritten** (below); Rankin constant "depends on θ". |
| 03-zeros | **Prop La** restated and proved in D_max form, with eq:Dmaxstd and a remark on why. D̂ converges for σ > 3·10⁻⁵. **w_a (i)–(iv) for general h** with ε = h(a)/a. \|N − T₀\| line. **Lemma ZA(a)**: Y defined by Y/h(Y) = \|t\|; new a > Y bound. **Designed zero step 6**: \|w\| ≤ 1 from θ ≥ 2δ_k. **Late noise** rewritten (171Λe^{8ℓ_k²−θL_k} ≤ 171Λe^{−ℓ_k²}). Goodheights (ii): η := 3·10⁻⁵, K(N) = 2(2N+2)^η + 5. Rouché tally: 171Λe^{−4Λ²}. |
| 04a | Absorbed part ≤ h(u)Λ⁻⁸ ≤ u^{1/8}. |
| 04e | U/h(U) ≥ U^{7/8}; θ′ := 0.26; D₀ with h(u)Λ⁻⁸. |
| 04f | **o_R**: explicit sum bound for small θ (below). F_θ remark for every θ ∈ (0, θ₁]. Jump-at-X₀ item uses h(N_*). |
| 04k | **\|I_v\| ≤ 2.1H(v)/X₀ ≤ h(v/X₀)** re-argued with log H ≤ max(8(log L)², 15Λ + 1.4) (checker defect 2). #Abs(I_v) ≤ 2h(v/X₀). |
| 04x | h(2M), h(4X₀) in place of (2M)^{θ_b}, (4X₀)^{θ_b}; uses h ≤ u^{1/8}. |
| 05-queue | Opening and Lemma budget: ≤ D_max. Theorem caplw is stated θ-free. **Step 5 of (b) rewritten analytically** (checker defect 3). Remark caplw-numerics mentions window_check. Absorption intro. **Lemma P**: u₀ := log h(u)/log 2y in (12.2); the room statement; (iv) h ≥ 2L¹¹; 2y ≤ u^{1/100} via log 2y ≤ log h/100; (*) bullets; u_* ≤ 1 + L/8. Lemma raisedy (La) item. |
| 06-base-range | δ(t) with h(t)Λ⁻⁸; h(s) ≤ s^{1/8}. |
| B-certificates | capl_model note; caplw_check_independent output; **window_check.py** item; theta_ramp marked superseded; run list; depcheck output and comment. |
| C-ai-statement | Records the S1 extension and its review status. The Lean sentence is restricted to θ ∈ [1/20, ½ − 10⁻⁴]. |
| README.md | Theorem A line: θ ∈ (0, ½ − 10⁻⁴]. The S1 status and that it is not in Lean. |

`grep theta_b|1/20|theta_0` in paper/sections now hits only comments, the historical sentence in C-ai-statement and the
"superseded" item in App. B.

## The new proofs, with constants

### Lemma T1, absorbed part (checker defect 1)

The deficit is no longer bounded through the power form.
- h is non-decreasing, so M_a ≥ h(u_a)/h(a).
- Hence 0 ≤ 1 − M_a ≤ log(h(a)/h(u_a)) = ∫_{u_a}^a h′/h.
- Σ_a 1[u_a ≤ u ≤ a]/h(u) = ρ_Abs(u) ≤ (log u)⁻⁴, and ρ_Abs = 0 unless log u ≥ Λ²e^{s_H} − 1 ≥ 392Λ².
- So **Σ_{a ≤ x}(1 − M_a) ≤ ∫ h′ρ_Abs ≤ (392Λ²)⁻⁴h(x)**. This holds for every non-decreasing, piecewise-C¹ h; no lower bound on b
  is needed.
- The second sum is ≤ h(x)(log x)⁻⁴, as before.
- Total: **|#Abs(≤x) − ∫^xρ_Abs| ≤ 2(392Λ²)⁻⁴h(x) ≤ h(x)Λ⁻⁸**.

This is stronger than the checker's suggested 1.03h(392Λ²)⁻⁴ + 2.03hL⁻⁴ and is proved directly. The absorbed term is h(x)Λ⁻⁸
everywhere it is quoted: T1, 03 (N − T₀), 04a, 04e D₀, 06 δ(t).

### Theorem caplw(b) Step 5 (checker defect 3; the main risk)

Here log 2y ≤ 3.01γΛ and log C_d + 4ℓ ≤ 1.01γΛ on the raised range. These two bounds are taken unchanged from the existing
text and were not re-derived here. So the right side of (12.2) is ≤ 4.02γΛ, and u₀ ≥ U := log h/(3.01γΛ).
- **L ≤ 400Λ²** (u^{1/8} piece):
  - s ≤ log 400 ≤ s_H + 0.017 (s_H = 5.974538; log 400 = 5.991465), so γ ≤ 0.46.
  - log h = L/8 ≥ 49.1Λ², so U ≥ 35Λ.
  - 0.9U log U ≥ 689Λ ≫ 1.85Λ.
- **Raised range, L ≥ 400Λ²**:
  - log h ≥ 50Λ², so U ≥ 50Λ/(3.01γ) ≥ 2.214Λ.
  - The claim is log U ≥ 4.02·3.01γ²/45 (≤ 0.2689γ²).
  - log U ≥ log(2.214·10⁸) ≥ 19.21 and 0.2689·7.5² ≤ 15.13, so the **ratio is ≥ 1.26** (numerical minimum 1.2704).
- **Standard regime, ℓ ≥ ℓ_std ≥ 1.36·10⁴** (not 1.37·10⁴: ℓ_std(10⁸) = 13693):
  - log 2y ≤ 12ℓ² + 9ℓ + 8, and the right side is ≤ 16ℓ² + 19ℓ + 7 ≤ 16.002ℓ².
  - (*): log h ≥ 27Λℓ² gives u₀ ≥ 27Λ/(12 + 9/ℓ + 8/ℓ²) ≥ 2.249Λ.
  - (12.2): log h ≥ 120ℓ⁴/log ℓ gives u₀ ≥ v = 10ℓ²/(q log ℓ), q ≤ 1.0001.
  - Then 0.9v log v ≥ (18ℓ²/q)(1 − g(log ℓ)), with g(x) = (log x − 2.3024)/(2x) ≤ 1/(2e^{3.3024}) ≤ 0.0184 (the unique critical
    point).
  - So 0.9u₀ log u₀ ≥ 17.66ℓ² ≥ 1.10·16.002ℓ². The **ratio is ≥ 1.10**; the numerical minimum is 1.1043 at ℓ ≈ 6·10¹¹, and
    the ratio → 1.125.
- **Why 27Λℓ²**: just past ℓ_std, 120ℓ⁴/log ℓ alone gives u₀ ≈ 10ℓ²/log ℓ ≈ 1.97Λ < 2Λ.

The non-dyadic passage in Lemma P needs room for relative factors 1 + 10⁻⁵ and for L moving by log 2. The margins are 26% / 10%,
and 10.7% for (*) (u₀ ≥ 2.214Λ).

### Lemma P (iv), (v), (vi)
- (iv): u/d ≤ u/h(u) ≤ 2u/L¹¹, as log h = u₀ log 2y ≥ 500 log(L − 1) ≥ 11 log L + log 2.
- 2y ≤ u^{1/100}, from log 2y ≤ log h/100 ≤ L/800.
- (v) bullets: u_* = 1 + u₀ ≥ 2Λ by Step 5, and u_* ≤ 1 + L/8 ≤ L.
- (vi) is unchanged: Y = 2yh, and log Y/log 2y = 1 + u₀.

### w_a (i)–(iv) (03-zeros), general h, ε := h(a)/a ≤ a^{−7/8}
- (i) h(u_a)/h(a) ≤ M ≤ 1 and a/u_a ≤ (1 − ε)⁻¹.
- (ii) |w_a| ≤ 1 + 1.02σε.
- (iii) |w_a| ≤ 2.03/(ε|t|). This is proved by integrating by parts against the monotone g and using h(u_a) ≥ h(a)(1 − ε)^{1/8}.
  (iii) is not used in ZA.
- (iv) |1 − w_a| ≤ 1.01(|s| + ⅛)ε, so |1 − w_a| ≤ 2|t|h(a)/a for |t| ≥ 2. The bound 1 − M ≤ (1/8)log(a/u_a) uses b ≤ 1/8.

### Lemma ZA(a)

Y is defined by Y/h(Y) = |t|. It is unique, since log(u/h) has slope 1 − b ≥ 7/8. Then log|t| ≤ log Y ≤ (8/7)log x_k, and Y may
exceed x_k.
- **a ≤ Y**: |1 − w_a| ≤ 2.0001. On [V, log Y], log v ≤ log log x_k + 0.14, which is enough since 504ℓ_k(ℓ_k + 0.14) ≤ L_k.
- **a > Y**:
  - f(x) = h(x)x^{δ_k−2} is decreasing, with −xf′/f ∈ [1.87, 2].
  - Partial summation gives ≤ 4|t|∫_Y^∞ f e^{−ς_*} ≤ (4/0.87)|t|h(Y)Y^{δ_k−1}e^{−ς_*(log Y)} = 4.6Y^{δ_k}e^{−ς_*(log Y)}.
  - δ_k log Y ≤ 9ℓ_k + 1, because log h(Y) = 120ℓ_Y⁴/log ℓ_Y ≤ 121ℓ_k⁴ and L_k ≥ e^{ℓ_k}.
  - log Y ≥ log(Γ_k/2) ≥ ½L_k, so ς_*(log Y) ≥ L_k/(29ℓ_k).
- New constants: **12.6(log x_k)⁹exp(−log x_k/(29 log log x_k))**, which is still ≤ e^{−10¹¹}. The old constants were 5.4 and 22.

### Designed zero, step 6

Re w ∈ [1 − θ − δ_k, 1 − θ + δ_k] and |Im w| ≤ δ_k, with 2δ_k ≤ θ (from θL_k ≥ 9ℓ_k² ≥ 18ℓ_k). So Re w ∈ [0.49, 1 − δ_k] and
|w|² ≤ (1 − δ_k)² + δ_k² ≤ 1.
- The O(1) interval [log κ₀ − log 2Λ − 1.7, log κ₀ + 0.72] is unchanged: −log 2 − 1 − log 1 = −1.693 ≥ −1.7.
- The ReΦ_min bullet (0 ≤ Re w ≤ 1) still applies.
- Re s* = θ + Re w*, so θ cancels in Re ρ_k, as the scoping said.

### Late noise
- For x ≥ a_k/2, ℓ ≥ 2Λ − 1 > ℓ_std, so |D| ≤ D̄(x) := 3.01e^{8(log log x)²}, and log D̄ has slope ≤ 10⁻⁶ in log x.
- By parts: |∫_{[a_k,∞)} x^{−s}dD| ≤ D̄(a_k)a_k^{−σ}(1 + |s|/(σ − 10⁻⁶)) ≤ 3.1|s|e^{8ℓ_k²}a_k^{−σ}.
- The rest is as before (factor 2 from |G(w*)|, 1.0001, 1 + 10⁻¹⁰): constant 6.21e·2Λ/0.198 ≤ 171Λ.
- **|D̂_{≥a_k}| ≤ 171Λe^{8ℓ_k² − θL_k} ≤ 171Λe^{−ℓ_k²} ≤ 171Λe^{−4Λ²}.**

### o_R (04f), small θ

The terms are o_R ≤ H(u)u^{−θ} for u ≥ x₁/4, and o_R = 0 below.
- Put f(u) = θ log u − 8ℓ_u² − 3 log log 3u. Then f ≥ ℓ_u² − 4ℓ_u − 1 ≥ 3Λ², using θ log u ≥ 9ℓ_u² − 1.
- f grows by ≥ θ log 2/2 per dyadic step, since (16ℓ + 4)/L ≤ θ/2.
- With 1/θ ≤ log x₁: **Σ_{u≥x₁/4} log²(3u)H(u)u^{−θ} ≤ 4 log x₁·e^{−f(u₁)} ≤ e^{−Λ²}**.
- This term is added to Σ log(2u)o_u ≤ e^{−83}. The R-parts of Σ(log 3v)²o_v and of sup log v·o_v are ≤ e^{−Λ²} by the same bound.

### 04k (checker defect 2)
- log H(v) ≤ max(8(log L)², 2 log c + 2 log 2) ≤ max(8(log L)², 15Λ + 1.4).
- If L ≤ 113Λ + 18: 8(log L)² ≤ Λ − 1, and log c ≤ max(4(log L)², 0.03√L) (Step 6). So log H ≤ Λ − 1 and 2.1H/X₀ < 1 ≤ h.
- Otherwise: log h(v/X₀) ≥ max(14Λ + 2.2, 8(log L)²) ≥ log(2.1H(v)/X₀).
- Numerically (W3), the margin is ≥ 1.125Λ at every L ≥ 2Λ − 1. This matches the checker's k04.py.

### Goodheights (ii)

η := 3·10⁻⁵, from D_max ≤ x^{3·10⁻⁵}, and K(N) := 2(2N+2)^η + 5. Then (θ + η)/2 − ¼ ≤ −3.5·10⁻⁵ ≤ −2.5·10⁻⁵. This is the
only use of θ ≤ θ₁ in §3.

## Checked and unchanged (θ-reads that are upper bounds or θ-free)

These were read and need no change:
- **Positivity and target**: Lemma G1 (θ + 2 ≤ Γ_k); Rankin C_{X₀} (finite for every θ > 0); Lemma adapted; Remark stopped.
- **§3 zeta bounds**: ZB/ZBlow (κΓ₁ ≥ e^{0.49X₀²}, θ ≤ ½); the R̂ bullets (Re w ≥ 0.49); eq:Rhatbound and LP-c (Re w ≥ 0.4);
  goodheights R′ and ρ̄_Abs parts; Theorem zeros.
- **Prop g1(B) and LP**: Step 3 (F_θ ≤ F_{1/2} ≤ 1.33, 1/(1 − θ) ≤ 2, R_j″ factor); Step 4 (separation, Average, r = 2^{θ−1} ≤ 2^{−1/2});
  04e 214–217 (y^{θ−1}log y ≤ X₀^{−0.49}).
- **Other sections**: the probability budget; Table 1; App. A. No θ appears in them.

## Certificates (certificates/capl-cert, certificates/depcheck)

- **capl_model.py**:
  - `logh_of(l, lam)` implements the window, and `lemmaP_ok` uses u₀ = log h/log 2y.
  - `CAPL_THETA_B`, if set, switches back to log h = θ_bL, for comparison only.
- **caplw_check_independent.py**:
  - It has its own window implementation, and Step 5 is now the paper's new criterion.
  - Its random sample (s ≤ 60) covers only the raised range of Step 5.
- **window_check.py** (new). For Λ ∈ {1e8, 1e9, 1e10, 1e12, 1e16, 1e20, 1e30, 1e50, 1e70, 1e100} it checks:
  - (W1) (12.2) with the precise y, ratio ≥ 1.0001, u₀ ≥ 100 and u₀ ≥ 2Λ, from the onset of Abs to ℓ = 1e70. The grids are fine
    at the onset, at L = 400Λ², at ℓ_std and at the two crossovers.
  - (W2) log h ≤ L/8, h ≥ 2L¹¹, and log 2y ≤ log h/100.
  - (W3) the 04k inequality for L ∈ [2Λ − 1, 1e300].
  - (W4) slope ∈ [0, 1/8], monotonicity, and continuity.
  - (W5) the analytic Step 5 inequalities.
  - (W6) 20 scalar constants quoted in the text.

  First runs found two text constants that were wrong, and both are now fixed in the paper: 0.26889 → 0.2689 (since
  4.02·3.01/45 = 0.268893) and ℓ_std ≥ 1.37·10⁴ → 1.36·10⁴.
- **theta_ramp.py**: marked LEGACY; it defaults to θ_b = 1/20 and its output is unchanged.
- **depcheck.py**: edge lem:T1 → thm:caplw(b)(c) added. Acyclic; 78 nodes, 198 edges, 28 strictly earlier.

Outputs (`/usr/bin/python3 -I -B`, from the repository root):

```
window_check.py (12.7 s):
Lam=1e+08: (W1-2) 51547 pts, fails 0, min (12.2) ratio 1.1043 at l=6.1692e+11, min u0/Lam 2.2221 at l=13608; (W3) 224223 pts, fails 0, min margin 1.125e+08 at L=2e+08; (W4) fails 0, max b 0.1250, rel. jump 4.0e-14; (W5) fails 0, min raised 1.2704, min std 1.1043, min u0/Lam 2.2148
Lam=1e+09 ... 1e+20: identical minima (1.1043, 2.2222), 0 fails; min raised 1.4227 .. 3.0973
Lam=1e+30: min ratio 1.1049; 1e+50: 1.1081; 1e+70: 1.1106; 1e+100: 1.1132 (min u0/Lam 2.2222, 0 fails, every Lam)
(W6) 20 lines OK
TOTAL FAILURES: 0

caplw_check_independent.py:
window: log h = L/8 (L <= 400 Lam^2), max(50 Lam^2, 27 Lam l^2, 120 l^4/log l) beyond
s_H = 5.974538031693934
Step1 violations: 0  Step2 violations: 0 (min lhs/rhs 1.6938)  Dickman violations: 0 (min ratio 1.1897)  Step5 violations: 0 (min lhs/rhs 1.2705)  u0 >= 2Lam violations: 0 (min u0/Lam 2.2148)

analytic_capl.py: s_H = 5.9745; G decreasing on every sample line; 4842/5072/5302/5763/6684/7605 points, 0 failures (unchanged)
cert_capl.py:     cells 20790 on [18.421, 60]: failures 0; cells 398801 on [60, 2e4]: failures 0 (unchanged)
raise_max.py:     max (log H - log H_std)/L = 1.292e-08 ... analytic bound 1e-6: OK (unchanged)
theta_ramp.py:    (legacy, theta_b = 1/20) min lhs/rhs 1.3624; min u0/Lam 2.3732 (unchanged)
needs.py:         diagnostic; P-ceiling now 8.46 Lam beyond the ramp (was theta_b-dependent)
depcheck.py:      same-time subgraph acyclic: True | nodes 78 | edges 198 | strictly-earlier edges 28
```

rankin_R.py is not affected by the window and was not rerun.

## Build

`cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/wt-s1-build main.tex`:
- 0 undefined references.
- 14 overfull boxes, the same 14 (same lines) as the baseline build of 37e7339.
- Comments added are whole-line only (checked on the diff).

## Open points

1. **One independent AI check only** (passed on every item); no human review.
2. ~~Step 5 rests on two inherited raised-range bounds~~ Closed: the independent check re-derived log 2y ≤ 3.01γΛ and
   log C_d + 4ℓ ≤ 1.01γΛ by hand.
3. **Lean**: ported (branch lean-s1). See *Lean* below.
4. **Statement form.** Theorem A(i) now carries D_max(x) + h(x)Λ⁻⁸ explicitly. For θ < 1/8, h is not ≤ x^θ near
   L = 400Λ², so the clean form N = x + O(x^θ log*x) holds only with a constant depending on θ (and X₀); that constant is not
   computed.
5. **Lemma ZA(b)** keeps its o(1). It is unused, as before.
6. **CORRECTIONS-vs-v3.md** entry #115 records S1 (strengthening, not an error). README notes that Lean's `Theorem21` is the
   pre-S1 form.
7. **S2** (per-zero θ_k and the switch-off, giving a [1,0]-system) is not attempted here.

## Lean (branch lean-s1, 2026-10-31)

`lake build` is green. `#print axioms` of `BModel.corollary_2_2_complete`, `BModel.theoremA_full` and
`BModel.theoremA_ii_complete` gives [propext, Classical.choice, Quot.sound]. Statements:

- `Theorem21 := ∃ XHux, ∀ θ ∈ Ioc 0 (1/2 − 1/10000), ∀ X₀ even, e^{10⁸} ≤ X₀ → XHux ≤ X₀ → …`. The threshold is
  max(x₁, XH, e^{10⁸+1}) from (84), so it does not depend on θ.
- (i) is |N(x) − x| ≤ C x^θ + 3 x^θ log* x + x^{η(θ)}, with C depending on θ and ω (see point 4). In Lean the lag
  D_max = `LagSplit.lagMax` and the window h = `Absorbed.winH X₀` are `SubPow` (x^{o(1)}) and are absorbed into C.
- `theoremA_ii_complete` is stated in the same uniform form.

Where the Lean differs from the S1 text, or the text left something unspecified:
- **Switch-on.** The seed is S = max(X₀, 1000/θ) and x_k = switchOn S k. The condition used is
  16ℓ² + 4ℓ + 2Λ + 10 ≤ θ log y for log y ≥ log x₁ − 3 (`Construction.switchOn_cond'`), not the text's 9(log log)².
- **Smoothing exponent.** θ′ = max(θ + 0.01, 0.26) (`LocalPNT.thetaPrime`). The smoothing step needs θ′ ≥ θ + 0.01.
- **T1 bound.** The absorbed target error |#A − ∫ρ̄_A| ≤ 2h(x) comes from ε·h(x) + (1/8)∫ρ h/v
  (`absorbed_target_error_cap`), not from the text's argument.
- **Lemma ZA.** Lemma ZA keeps h ≤ a^{1/8} (Y = |t|^{8/7}) in place of Y/h(Y) = |t|. The decomposition is proved on Re s > 1/8.
- **Constants.** D_max is written with B(X₀) + 3H(X₀) + 5 (`lagMax`).
- **Inversion.** `solveU` (u + h(u) = n) needs u ≥ 1 and n ≥ 2.
- **Window count (step (iii)).** The last term is 2(y/X₀)^{1/8} in place of 2(y/X₀)^{θ/2}. The window length
  2.04H(y)/X₀ + ½ is ≤ h(0.99 y/X₀): below log u = 400Λ² by e^{(L−0.02)/20}, beyond by log H(y) ≤ 8(log log y)² + 15Λ + 2
  ≤ 27Λ(log log u)² (`Queue6.win_len_h`).
- **o_R.** The R′ modulus is the explicit max(s, x₁)^{−θ}/10¹³ (`oscMod`). Summed over dyadic scales it is ≤ 10⁻⁸⁰ by the
  switch-on condition (`sum_oscModU_le`). This replaces the old (u/2)^{−1/20} term in o_j and B(u).
- **Lag exponent.** Inside §5/§6 the θ-free lag exponent λ(10⁻⁴) = 1/20000 replaces λ(θ).
