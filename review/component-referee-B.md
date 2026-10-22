# Referee report B on `beurling-greedy-v2.md` (independent second referee)

Date: 2026-10-20. Scope: v2 draft plus cited proofs `gap-G2R.md`, `gap-localPNT.md`, `gap-G3.md`,
and the Lean files `RH/Attempts/{Beurling,BeurlingGreedy,GapG2R}.lean` (read, not built).
Sections 1-3 were written before reading `beurling-greedy-referee.md` or `revision-plan.md`.

Tags: FATAL / SERIOUS / GAP / MINOR, each with a confidence (high / medium / low).

## 1. Summary verdict

**Theorem A does not follow, even granting every item the draft lists as open, sketched or
pending (R1′-base, CL, SM, the gap-localpnt cross-check, the LP constants).** The dependency
table understates what is missing. The main reason (issue F1 below) is structural, not
bookkeeping.

- The drift R1′ at scale x comes from bounding (Ke)(x) = Σ_n c_n ν(x/n)/n in **sup norm**
  (rows G2-R, BR, G1′). That needs sup_{u≤x/2}|ν(u)| ≪ 1/(log x·Σ|c_n|/n).
- The jitter width H(u) = exp(8(log log u)²) **increases** with u. So the noise at the smallest
  jittered scales, u ≈ 2X₀–3X₀, has the fixed size ≍ H(X₀)^{−1/2}. It does not shrink as x
  grows, while the required tolerance does.
- Every threshold in §3.5 and §0.4 ("log H ≥ 5.77ℓ² + 12ℓ + 13", "ℓ ≥ 6.3") silently puts
  H(x) in place of min_{u≤x/2} H(u) = H(X₀).
- With the draft's own amplification (1 + log x)^{2K+1}, the stated G2-R inequality fails
  from log x ≈ 5·10⁹–4·10¹¹ on (for c = 1/100 … 1/500). That is **below X_*** and far below
  x₁, so the sup-norm route never reaches the range where R1′ is claimed for x ≥ X_*, and
  never reaches the designed zeros.
- Even if M-op held (|c_n| ≤ 1), the same argument fails from log log x ≈ 500–700 on. The
  zeros need log log x ≥ log log x₁ ≥ 2 log X₀ ≈ 10⁹.
- No repair is available inside v2. [§8 corrects the next clause: for scalar coefficients a
  scale-weighted bound suffices; the open step is the operator-valued compensator.] A repair needs **signed cancellation** in the
  propagation of small-scale noise (an "absorption" lemma; compare gap-localPNT §6.7, which
  meets the same obstruction for base-range anomalies and finds an unresolved range and a
  "tower"). It is not a matter of constants.

Beyond F1, there are three further independent errors in rows tagged [P]:
- **F2.** The proof of Lemma B′ in operator form is invalid: identity (ii) of gap-G2R §8.0″
  replaces the identity by the average A. My numerics suggest the conclusion may still hold
  in the void-filter region.
- **S1.** NV §3.4 step 2 relies on "X₀ ≫ H", which is false at every scale ≥ x₁.
- **S2.** The full-block step of Thm 4.2′ fails once log x ≳ 0.0015·X₀, because M_sm grows like
  L⁵/X₀. Every zero scale has log x ≥ X₀².

The zero design of §2 (Lemmas 2.1–2.3, Thm 2.4), the TC excess identity, Lemma M (scalar sharp
filter), LP's structure, and the Lindley bookkeeping look correct up to minor issues. The
conditional implication "(L-a) at all scales ⇒ zeros with Re ρ_k → 1" is, in my reading,
sound. The weak link is the derivation of (L-a), i.e. of the queue bound.

Confidence in the verdict: **high** for F1 (it is a monotonicity oversight, checked
numerically in `/tmp/rhscratch/referee-b/supnoise*.py`), high for S1 and S2, and
medium-high for F2 as a gap in the proof. F2 is not a counterexample to the conclusion.

## 2. Fatal and serious errors

### F1. FATAL (confidence high): the sup-norm noise response ignores that H(u) increases with u

**Location.** v2 §3.4–§3.5 (rows NV, G2-R), §3.6 (BR), §3.7/gap-localPNT (6.1) (G1′, via the
term log x·(1+log x)^{2K+1}ν_*), §0.4 rows H and "noise response". Source: gap-G2R §8.1–8.2.

**Claim.**
(3.5): |(Ke)(x)| ≤ (1 + log x)^{2K+1}·sup_{u≤x/2}|ν(u)| ≤ c′/(4 log x), "once
log H ≥ 5.77ℓ² + 12ℓ + 13", ℓ = log log x. Here sup_{u≤x/2}|ν(u)| is bounded by
√(4M₁λ/H)(1+o(1)) + O((M₁λ+B)/H), and H is read as H(x).

**Why it fails.**
1. The construction jitters slot j by H(s_j) (§1.2 item 3), with H(u) = exp(8(log log u)²)
   increasing. ν(u) is an H(u)-window average of a martingale with ≍ H(u) increments, so
   |ν(u)| ≍ H(u)^{−1/2} typically, not merely as an upper bound. On [2X₀, 3X₀) the jittered
   composites 2q already give Mart ≠ 0.
2. Hence sup_{u≤x/2}|ν(u)| ≥ (typical |ν| at u ≈ 2X₀–3X₀) ≍ H(X₀)^{−1/2}·√(λ-ish). This is a
   quantity **fixed by X₀**.
3. (Ke)(x) does involve those scales. c_n(x) ≠ 0 for n up to x/X₀ (K^{jit} only imposes
   x/n ≥ X₀). **[Corrected in §8.]** I first claimed that the scalar weight
   Σ_{n∈[N,2N]}|μχ_x|/n at N ≍ x/X₀ is ≍ 1. That is wrong. χ_x(n) = 1 is Tenenbaum's t-dense
   condition with t = x/n, so this weight is ≍ log X₀/log x (Saias). The draft's *stated* bound
   still fails as computed below, because it uses (1+log x)^{2K+1} at every scale.
4. So the sup-norm bound at x is at least ≍ H(X₀)^{−1/2}, while the target c′/(4 log x) → 0.
   The required inequality (1+log x)^{2K+1}·√(4M₁λ/H(X₀)) ≤ c′/(4 log x) fails once
   2.885ℓ² ≳ ½·8(log log X₀)², i.e. ℓ ≳ 1.18·log log X₀.

**Numeric check** (`/tmp/rhscratch/referee-b/supnoise.py`, `supnoise2.py`). These use the draft's
own K = ⌈log₂log₂x⌉ − 1, M₁, λ = 3L and c′ = 0.15. The left column is the first scale where the
inequality fails.

| log X₀ | log H(X₀) | fails from (B′, as in v2) | fails from (if M-op, Σ\|c_n\|/n ≤ 1+log x) | zeros need |
|---|---|---|---|---|
| 4915 | 578 | log x ≈ 1.1·10⁴ | log log x ≈ 95 | log log x ≥ 9.8·10³ |
| 2.6·10⁸ (c = 1/100) | 3004 | log x ≈ 5.2·10⁹ | log log x ≈ 500 | log log x ≥ 5.2·10⁸ |
| 1.2·10⁹ (c = 1/200) | 3496 | log x ≈ 2.4·10¹⁰ | log log x ≈ 582 | log log x ≥ 2.4·10⁹ |
| 9.1·10⁹ (c = 1/500) | 4207 | log x ≈ 3.5·10¹¹ | log log x ≈ 701 | log log x ≥ 1.8·10¹⁰ |

Compare log X_* ≈ 10²⁴–10²⁹ (§0.4). The stated G2-R bound already fails **inside the base
range**. It fails on all of [X_*, ∞), where the table claims R1′ [P | PENDING]. It fails at
every designed zero scale.

**The same defect in two other rows.**
- *BR (§3.6, gap-G2R §10 step 1).* The resolvent (1+K_op)^{−1}, of norm ≥ Σ|μ(n)|/n ≍ log x,
  acts on Δρ^{sh} at **all** scales v ∈ [X₀, x]. Near-threshold cofactors with latest prime
  p₀ ≈ X₀ exist at every v, so |Δρ^{sh}(v)| contains a part of size ≈ √H(X₀)/X₀ that does not
  decay in v. (This is a rough estimate: the near-threshold weight ∫H(p₀)/(p₀²log p₀)dp₀
  times the H(X₀)-window prime discrepancy.)
  - The claimed bound C(log⁴x/√H(x) + √(λ/H(x)))/log x is smaller than this once
    4(log log x)² > log X₀.
  - Even granting the bound per scale, the product with (1+log x)^{2K+1} exceeds 1/log x once
    2.885ℓ² ≳ log X₀. So BR fails for log log x ≳ (log X₀/2.9)^{1/2} ≈ 1.9·10⁴, still ≪ the
    zero scales.
- *G1′ (gap-localPNT (6.1)).* η₁ contains log x·(1+log x)^{2K+1}ν_*, with ν_* := sup_{u≤x/2}|ν|.
  The same arithmetic applies.

**What a repair would need.** [Superseded by §8. A scale-weighted sup-norm bound with Lemma M
plus Saias support density (referee A §6) needs no signed cancellation *for scalar
coefficients*. What remains open is the operator-valued step.] Original text: one needs **cancellation**
in Σ_n c_n(x)ν(x/n)/n over n-intervals of relative length ≈ H(v)/v. Two candidate inputs:
- (a) a martingale/L² argument with predictable coefficients. This is exactly the route v2
  abandons ("no predictability of the c_n is used"; Addendum B "moot"). It becomes live again.
- (b) Möbius-type cancellation Σ_{n∈I}μ_P(n)χ_x(n) over short intervals. LP gives this, if at
  all, only at relative length ≥ e^{−c√log x}. Lemma B′'s weights reach H(v)^{−1/2} ≪ 1/log x
  only when log log v ≳ 0.85ℓ. So the noise at scales c√log x ≲ log v ≲ (log x)^{0.85} is
  covered by neither argument, at every large x. With M-op the two ranges would overlap
  heuristically, but M-op is [OPEN].

gap-localPNT §6.7 meets the same obstruction for base-range anomalies. It records an
"unresolved range (X_*, X_**)" and a possible "tower". v2 does not carry this over, and it
does not notice that the *ordinary* noise of size H(X₀)^{−1/2} has the same problem.

**Consequence.** Rows G2-R, BR and G1′, and hence R1′ and G3 (Thm 4.2′) and (L-a), are not
[P | listed items] at any scale with log x ≳ 10¹⁰. Theorem A's implication chain breaks
before the first designed zero.

### F2. SERIOUS (confidence high that the proof is invalid; medium that the conclusion is true): Lemma B′ in operator form

**Location.** v2 §3.3 "Lemma B′ [P]… covers operator-valued weights"; table row LB′. Source:
gap-G2R §8.0″, items (i)–(iii). Used by G2-R (3.2), BR step 1, and gap-localPNT (6.1).

**Claim.** From (i) c_n = −Σ_{d|n,d<n} κ_{n,d}∘c_d, the source derives (ii)
b_d := Σ_{e|d} c_e = Σ_e (A − κ_{d,e})∘c_e, with ‖A − κ‖ ≤ 1 and A − κ ≠ 0 only on bad pairs.
The scalar layer descent then gives ‖c_n‖ ≤ τ_{2K+1}(n).

**Why the proof fails.**
- From (i), Σ_{e|d}c_e = c_d + Σ_{e<d}c_e = Σ_{e<d}(**I** − κ_{d,e})∘c_e.
- (ii) holds only if Σ_{e<d}(I − A)∘c_e = 0. That is false unless A = I.
- On good pairs κ = A, so I − κ = I − A, with ‖I − A‖_{∞→∞} = 2 for a box average. Then b_d is
  **not** supported on bad divisors, and the layer descent never starts.
- The scalar proof works only because the scalar weight on good pairs is exactly 1.
- The Lean statement `abs_cG_le_G` is scalar (ℤ-valued, `good : ℕ → ℕ → Bool`). It does not
  cover this step, contrary to the table's "[P] (Lean, scalar abstract form …; operator form on
  paper)".

**Numerics** (`/tmp/rhscratch/referee-b/optv.py`, `optv2.py`). Model: the void-filter region
n < √x with H constant. There the coefficient kernels obey
G_n = −Σ_{v|n,v≥2} box₁ * D_{1/v}G_{n/v}, and I computed TV(G_n) exactly by FFT.
- Squarefree n: TV = 1.0002 (n = 6, 30, 210), 1.006 (2310), 1.024 (30030), 1.039 (510510),
  1.054 (9699690), 1.066 (223092870).
- Non-squarefree n: TV ≤ 0.25 (for example 0.0016 at n = 2¹⁰).
- So in this region ‖c_n‖ ≈ |μ(n)|·(1 + slowly growing). The conclusion is plausible there,
  even though the stated proof is wrong. Single-frequency tests give Σ_{n≤10⁵}|Ĝ_n(ξ)|/n ≤ Σ|μ|/n.
- The filtered (threshold-straddling) region, where ‖A − κ‖ matters, is untested.

**Classification.** LB′ (operator form) should be [OPEN] or [S], not [P]. It is a different,
weaker statement than M-op, and it is not implied by the scalar Lean lemma. Note that F1 makes
this moot for G2-R as currently structured. It still matters for BR, and for any L² or
martingale repair.

### S1. SERIOUS (confidence high): NV §3.4 step 2 uses "X₀ ≫ H", which is false at all scales ≥ x₁

**Location.** v2 §3.4 item 2; gap-G2R §8.1 ("All latest primes are then jittered (q ≥ X₀ ≫ H)").

**Claim.** The cofactor window W/q has length H/q ≤ H/X₀ ≪ L^{−6}, so two E_cl windows cover it
and X_q ≤ 2M₁.

**Why it fails.**
- H(u) ≥ X₀ as soon as log log u ≥ (log X₀/8)^{1/2} (≈ 1.1·10⁴ for log X₀ = 10⁹).
- At u = x₁, log log u ≥ 2 log X₀, so H(x₁) ≥ X₀^{32 log X₀} ≫ X₀. For a latest prime
  q ∈ [X₀, H(u)L⁶) the window W/q has length ≥ L^{−6}, and E_cl gives only
  X_q ≤ M₁(H/q·L⁶/4 + 1).
- Inserting this crude increment bound into Freedman gives a contribution √(M₁L⁷/X₀) to ν. That
  is not small once L ≳ X₀^{1/8}.

**Repair (plausible, not in v2).** Split off q < H(u)L⁶ as in Lemma SM and bound the
compensator of these (H L⁶)-smooth composites by Rankin. This needs an SM-type lemma at
smoothness level ≈ H(u)L⁶ rather than L¹¹, so the [S] status of SM propagates to NV. NV's
dependency row should list it.

### S2. SERIOUS (confidence high): Thm 4.2′ full-block step fails once log x ≳ 0.0015·X₀

**Location.** v2 §4.3 proof step 5; gap-G3 §4 and §5 ("Effect on §4").

**Claim.** "Full blocks (ℓ_jit = L₀) have excess ≤ 0, because
c′L⁴ ≥ √(12M₁L⁶) + 4M₁L + L³", where L³ stands in for "(rest)".

**Why it fails.**
- (rest) contains M_sm = 100(2 + L⁵/X₀). That term exceeds L³ once L > √X₀/10, and it exceeds
  the whole drift c′L⁴ once L > c′X₀/100 = 0.0015·X₀.
- Every designed zero has L = log x_k ≥ X₀². So at all zero scales the full-block excess bound
  is positive (≈ 100L⁵/X₀ − 0.15L⁴ ≥ 99L⁴·X₀ − …). Concatenating blocks then gives linear
  growth, and B(x) is not established. The "κ_D = 5" claim of §0.4 inherits this.

**Source of the problem.** D = 2 + L₀/X₀ in Lemma SM counts *every* integer in a window of length
L₀/r as a possible deterministic X₀-smooth cofactor. At log x ≫ X₀, 𝒟 is astronomically sparse.

**Repair (plausible).** Bound #(𝒟 ∩ window) by Tijdeman-type gaps between S-units, or by a
counting argument. This reintroduces exactly the Tijdeman input that v2 §1.3 says is "deleted",
although only at scales log x ≫ X₀.

## 3. Gaps beyond the known open items

Known items (R1′-base, CL and SM shape counting, LP constants, PENDING under TC) are not
repeated here. My classification checks of those items are in §6.

**G1. GAP (classification; confidence high): R1′ for x ≥ X_* is conditional on R1′-base, not
only on PENDING.**
- Table row R1′ says "[P | G1′, G2-R, BR] for y ≥ X_*", and §8 U1 says a failure of R1′-base
  makes Theorem A "lose its base case".
- But G2-R at x reads ν at **all** scales u ≤ x/2, including [2X₀, X_*]. If R1′-base fails,
  the queue there is ≍ x^{θ/4} and ν ≍ 1/log v on draining stretches (gap-localPNT §6.6). That
  breaks G2-R at every larger x.
- gap-localPNT §6.7 finds that absorption is provable only beyond X_** = exp(C_r log²X_*). It
  records an unresolved range (X_*, X_**) and a possible "tower".
- v2 mentions neither X_** nor the tower. Repair (R-d) of §5.3 ("drift-free base range …
  not excluded a priori") is exactly the case §6.7 analyses and finds open. F1 is the same
  phenomenon for ordinary noise.

**G2. GAP (confidence medium-low): exactness of the margin identity e = −Ke − ν.**
- The compensator of jittered composites in W_x is Σ_m (1/m)·avg_{W_x/m}(Σ_q 1_{J_q}1_{s_q>τ_m}/H(s_q)).
  Its averaging window W_x/m has length H(x)/m. The decided-prime density inside it is
  smoothed by the q-jitter, of width H(x/m).
- Writing it as (Kρ̃)(x), with ρ̃ itself an H(·)-window average of decided primes, needs
  A_{x}∘K = K∘A at the level of the rough decided-prime measure. These kernels differ (box(H(x)/m) * box(H(x/m))
  versus box(H(x/m)) * box(H(x/m))). The commutator acts on a rough measure, so it is not small.
  It can be put into ν, but it is then not a martingale and not ΔQ. Its size is comparable to
  the local prime discrepancy, ≈ (B + √(Hλ))/H.
- v2 §3.2 and gap-G2R §8.0 assert "exactly" without fixing the definitions precisely enough
  to check.

**G3. GAP (confidence medium): Thm 4.2′ is stated "on G_{<x}" for windows up to 2x, but its
input R1′ at u ∈ [x, 2x] needs (H_y) up to u(1−2δ) > x** (through LP⁺ in G1′). As literally
stated, this is the induction conclusion. The stopping-time formulation of §0.3 (first failure
time τ) avoids the circularity, but then Thm 4.2′, the union bounds and Freedman must be
restated for windows ending before τ. The stopping step for Freedman needs the
"P(S ≥ a, V ≤ v)" form. Bookkeeping, but it is not written. §0.3's sentence "the one place
where an item at y uses the current scale is G3" also misses G1′: (6.1) uses Freedman for
Mart(J) on the current-scale window J, with past randomness only.

**G4. GAP (confidence high, minor in effect): probability budget.**
- (a) Thm 4.2′'s union bound "≤ x² windows × 2e^{−λ}" with λ = 3L gives 2x^{−1}, not ≤ 3x^{−2}.
  Restricting to windows of ≤ L₀ slots gives ≈ 4L⁵x^{−2}, still above 3x^{−2} but summable. Or
  take λ = 4L, which changes B(x) and the c′ arithmetic slightly.
- (b) NV takes the sup over a continuum of u. A net and a Lipschitz step are needed, and
  Freedman two-sided costs 2e^{−λ}.
- (c) The NV and (6.1) failure events are not in G_{<y} and not in the 3x^{−2} budget.
- Σ_m still converges, so this is fixable.

**G5. GAP (confidence high): the "multiplicity lemma not used" claim (§0.3) is false.**
- R(δ) (gap-localPNT §6.2 step (ii)) uses N(I′) ≤ 3|I′| + K_loc from gap-G2R §8.3.
- BR uses K_loc ≍ B in ω_{ρ^{sh}}.
- (6.1) uses M_loc = 2B + 2λ + 9 in Freedman.
- All of these are at scales < x, so this is not circular. But the table should list §8.3 (at
  smaller scales) as an input of R(δ), BR and G1′. §8.3 itself needs the lag-count w.h.p.
  event, with its own union bound.

**G6. GAP (confidence medium): Lemma B and B′ for generalized integers.**
- The Lean lemmas `abs_c_le_G_all` and `abs_cG_le_G` are over ℕ with natural-number thresholds
  `Y * e < d * d`. The realised system has real values and exponent-vector divisibility.
- The transfer ("holds verbatim") is plausible: each divisor lattice is a product of chains,
  and the thresholds are monotone in values. But it is not formalised.
- `abs_cG_le_G` is proved only for n in a layer. An "all n" corollary like `abs_c_le_G_all`
  is not stated for cG.
- G_k ≤ τ_{2k+1} is not formalised (gap-G2R §6 says so).
- So the table's "[P] (Lean …)" for LB and LB′ overstates the formal coverage.

**G7. GAP (scope; confidence high): §7.3 omits the closest prior result.**
- F. Broucke, arXiv 2507.13780 (2025), Thm 1.6: for every eventually C¹, decreasing,
  strictly convex f with 1/u = o(f(u)), regularly or slowly varying, there is a Beurling
  system with N = Ax + O_ε(x^{1/2+ε}), infinitely many zeros on σ = 1 − f(log|t|), and none to
  the right. I checked the statement at source (pp. 4–5).
- The greedy zeros have the shape f(u) ≍ log u/u. Broucke already obtains this for N-error
  x^{1/2+ε}. So the entire content of Theorem A is the step from 1/2+ε to θ < 1/2. §7 should
  say so, and should cite it next to DMV and Zhang. The Lean docstring in `Beurling.lean`
  already cites it; v2 does not.
- Broucke's thesis App. A (checked at source, pp. 191–192) asks the stronger question
  (optimality of Landau's PNT for θ < 1/2, "even for systems in the extended sense, the matter
  is not clear"). I found no source that poses Q itself, or attributes it to Beurling. v2 §7
  does not claim such an attribution, which is correct. A refutation of Q would be a
  partial answer to App. A bullet 4, off by the log log factor (as v2 §7.2 says).

**G8. GAP (confidence medium): Lemma CL, independently of the shape count.** E_cl is
queue-independent in the sense claimed. CL uses only (F1), (F2) (sure facts) and (F3)
(harmonic sums and N(y) ≤ 2y on G_{<z}). I confirm the §0.3 claim on that point. Two
points need writing, though:
- (i) The tower-property step sums conditional probabilities Σ_r P(·|F_{r−}) over candidate
  slots whose existence (P_j = 1) is F_{j−}-measurable. It must be shown that the other
  members' constraints are F_{r−}-measurable *for every candidate r simultaneously*, since
  c_{i₀}'s admissibility depends on r's decision time.
- (ii) Peeling a member whose latest prime is unjittered (q < X₀) never happens by definition
  of N_jit. But cofactor chains pass through rigid elements (P-pass down to 𝒟). The claim "distinct
  elements of one component cannot pass all the way down to deterministic integers" uses
  |d − d′| ≤ εd < 1 with ε = δ/z. That needs εd < 1, i.e. d < z/δ, which holds since d ≤ 2z/X₀.
  Fine, but it should be stated.

## 4. Minor issues

- **M1 (§2, base factor; confidence high).** Integration by parts gives jump terms
  d^{−θ_b}·|F(d − d^{θ_b}) − F(d)| ≤ 2d^{1−σ−θ_b}/|t|. So the bound is 4E_{X₀}(σ + θ_b − **1**)/|t|,
  not 4E_{X₀}(σ + θ_b)/|t|.
  - This is finite only for σ > 1 − θ_b. "For σ ≥ ¾" is false when θ_b ≤ ¼ (θ = ¼: needs σ > 7/8).
  - Near σ = 1, E_{X₀}(θ_b/2) ≤ exp(O(X₀^{1−θ_b/2})) ≤ e^{X₀}, so Z = E_{X₀} + O(e^{−X₀}) still holds
    on the discs actually used.
  - Lemma 2.3(ii) averages over σ ∈ [¾, 5/4]. There the ρ_det integral is small for a different
    reason (𝒟 is astronomically sparse above Γ), and that should be said.
- **M2 (§2, Lemma 2.2).** |G(w*)| ≥ |s|α_k ReΨ_min/(2Z_max) drops the factor 1/|w*|. This is
  harmless since |w*| ≤ 1.
- **M3 (§0.4).** "X₀ ≥ max(e^{4915}, X_LP)" is the θ = ¼ figure. The lag row needs
  log X₀ ≥ 3.7·10⁶ at θ = 0.499, as the text below the table says. The table row should carry
  the θ-dependence. Irrelevant in practice, since X_LP binds.
- **M4 (§7.2, BDR).** BDR Thm 1.3 (checked at source) assumes RH and gives [½, β]-systems for
  0 ≤ β < ½ and [α, β]-systems for ½ < α < ⅔, 2α/(α+2) ≤ β < ½. v2's "(α < 1)" should read
  "α < ⅔". The other v2 statements I checked are accurate:
  - Zhang (two systems, N = kx + O(x^{1/2}e^{c(log x)^{2/3}}), zeros on σ = 1 − 1/log t);
  - BDR's quotes ("uncertainty of size at least x^{1/2−ε}", "extremely difficult to show which
    behavior the primes must admit");
  - the Broucke–Debruyne MVT (Acta Arith. 207 (2023) 365–391, Thm 2.1:
    ∫|S|² ≪ (T + 1/η)Σχ(n_k, ηN)|a_k|², which gives v2's form with η = 1/N).
- **M5 (row C1).** The Lean lemmas prove the abstract recursion for an arbitrary A : ℕ → ℕ.
  The identification of V_j with "composites < s_{j+1} + decided primes + 1" (including jump
  slots under TC, the base below X₀, and the slot indexing offset) is on paper. Fine, but the
  tag should say so.
- **M6 (§1.3 versus S2).** "No Tijdeman-type … input enters the excess" is true of the excess
  identity, but SM's deterministic-cofactor count D needs some sparsity of 𝒟 at large scales
  (S2).
- **M7 (gap-G2R §10 step 3).** The near-threshold weight is ≈ ∫_{X₀}H(p₀)dp₀/(p₀²log p₀) ≈
  H(X₀)/(X₀ log X₀), dominated by the *smallest* jittered primes, not "≈ 2/log x". Harmless
  in size, but it shows again that small scales dominate (F1).
- **M8 (§2 Remark, §7.2).** "The log log loss is forced by the positivity constraint (1.1)" is
  true of this design: amplitude ≍ 1 would violate (1.1). Under (A) the loss is 3·log log
  instead of 1·log log. The wording should say "in this design".
- **M9 (Theorem A (i)).** "for all x ≥ 1" uses the O(x^{θ/2}) of T1 with an unstated constant.
  State it or write "x ≥ x₀".
- **M10 (§0.2 row LP⁺).** "relative width δ ≥ e^{−c√log x}·polylog" is the hypothesis of LP⁺,
  and G1′ uses δ = γ_*^{−2}log^{−4}x. Fine, but the polylog exponent should be fixed (the proof
  needs δ ≫ K log³x·e^{−c√log x}).

## 5. The first referee's issues: fixed or papered over

Written after reading `beurling-greedy-referee.md` (main report and Addenda A, B) and
`revision-plan.md` (§A–§L).

| ref-1 item | v2 status | my assessment |
|---|---|---|
| 1. Cross-scale circularity (global PNT) | LP: local Landau on N♯, with positivity transferred from the finite Euler product P_y | **Genuinely fixed as a circularity.** I read LP Steps 1–6 and found no error. Constants are uncomputed, as stated. But the replacement architecture brings in a **non-uniformity** in its place: noise fixed at small scales is propagated by a resolvent whose norm grows (F1). The induction is non-circular but does not close. |
| 2. G2 false (discrete cofactors) | ρ_ref := (1+K_op)^{−1}T′; G1′ by resolution (gap-localPNT §6.4) | **Fixed in design.** The reference is the right object, and §6.4's resolution idea is sound for the smooth source. The proof of G1′ still passes through (6.1)'s ν_* term and through BR, and both carry F1. Under TC it holds only beyond (6.3) (acknowledged). |
| 3. H-pair insufficient | CL + E_cl (local, constant-free, queue-independent) | **Fixed in approach, [S] in execution.** I confirm queue-independence (G8). The multiplicity lemma (§8.3) is correctly dropped from G3 (gap-G3 §2.2 is right that it would be circular there). It is still used at smaller scales in R(δ), BR and (6.1) (G5). |
| 4. Tijdeman false on base range | TC (rigid set in the target) | **Partly fixed, partly moved.** The excess identity is exact (I checked it). The base-range difficulty moves into R1′-base, which is honestly flagged. But S2 shows that Lemma SM's deterministic-cofactor count needs sparsity of 𝒟 at large scales, so a Tijdeman-type input returns there, contrary to §1.3. |
| 5. G3-sm not minor | Lemma SM [S] | **Not fixed.** Beyond the acknowledged [S], SM's bound M_sm = 100(2 + L⁵/X₀) breaks the block argument at all zero scales (S2). |
| 6a–d. Literature | §7 rewritten | **Fixed**, except two omissions: Broucke 2507.13780 Thm 1.6 is not cited (G7), and BDR's α-range is "α < ⅔", not "α < 1" (M4). |
| 7. log* | T1 | Fixed. |
| 8. (L-a) constants, numerics regime | x^η form; proxy captions | Fixed. |
| 9. Lemma 2.3 radius | ⅛ | Fixed. |
| 10. D̂ convergence | "σ > η under (L-a)" | Fixed. |
| 11. §5.4 sign, f_II | superseded by the margin identity | The sign is fixed. "Exactly" in e = −Ke − ν is not verified (G2, medium-low confidence). |
| 12. G2-R | Lemma B [P, Lean], Lemma B′, sup-norm route | **Papered over.** (i) The sup-norm route fails at large scales (F1). (ii) Lemma B′'s operator form has an invalid proof (F2). |
| 13. Numerics | rewritten | Fixed. Captions are honest. |
| A-a … A-c5 | all incorporated | Fixed. The switch-on shift φ ≡ 0 on [x_k, x_k + H] correctly restores predictability of γ_k. |
| B1. Predictability for n > √x | "moot: the sup-norm route needs no predictability" | **Not moot.** Because of F1, a working proof will need cancellation across scales, either probabilistic (needing B1) or arithmetic. B1 is live again. |
| B2. Increment bound | §8.3 → E_cl's M₁ | Fixed for q ≥ H(u)L⁶ only. NV still needs the small-q part (S1). |
| B3. C-κ needs local H-pair | C-κ not used | Moot (correct). |
| B4, B5, B-K | done | Fixed. |

**The first referee's own suggestion seeded F1.** Addendum B item 1 proposes: "bound that part in
sup-norm, Σ_{n>√Y}|c_n|/n·sup|ν| ≤ (1 + log Y)^m·√(λ/H). This is fine for quasi-polylog H."
- The sup includes ν at scales x/n ≈ X₀, where H = H(X₀) is fixed. The suggestion therefore
  fails for log x ≳ (log X₀)^{1.18} (F1).
- revision-plan §C then generalised it to the whole resolvent, and v2 §3.5 inherits it.
- Neither referee nor authors checked the H-monotonicity.

**Open items that the revision plan records and v2 drops.**
- *revision-plan §L (amended):* "under G, R1′ is [P] only for x ≥ X_**, and (X_*, X_**) is a
  second OPEN window (the echo tower)". Also: "R1′ [P] for log x ≥ C_b(…)², … **under soft
  feedback S(ε)**".
  - v2 uses the **hard** greedy (§1.2, P_j = max(0, 1 − Q_{j−1} − A_j)).
  - So by its own sources, v2's table row R1′ "[P | G1′, G2-R, BR] for y ≥ X_*" is not
    supported for the construction it defines.
  - v2's "Bottom line" lists one open statement, R1′-base. The sources list two, even before F1.
- *revision-plan §J:* "M-op is a cosmetic open item", "Lemma B′ holds for them [P]". By F2
  the operator-form B′ is not proved, so "cosmetic" is wrong.
- *gap-G2R §8.0″* labels M-op "[GAP, cosmetic]". Together with F1, the operator-weight
  question is central, not cosmetic. Even M-op would not rescue the sup-norm route at the zero
  scales (F1 table, last column).

## 6. What blocks Theorem A (prioritised)

**Check of the known open items' classification** (requested):
- **R1′-base [OPEN].** Correctly classified. The [2X₀, 3X₀) mechanism (nested windows of
  rational primes at length x^{θ/2}) is convincing as an obstruction to *this proof*. But its
  failure is **not local to the base case** (G1). Under the hard greedy, the sources' own
  "second OPEN window" (X_*, X_**) belongs in §0 and §8. The soft-feedback repair would
  change C1, C3, NV and G3, as the lead says. It does **not** address F1: the ordinary noise
  at scales near X₀ is unaffected by the placement rule.
- **CL, SM [S].** Correctly classified. E_cl is queue-independent as claimed (G8). SM has an
  additional error, S2, beyond the [S].
- **LP constants.** Correctly "not needed for existence".
- **PENDING (LP⁺/R(δ) under TC beyond (6.3)).** I read gap-localPNT §6.5 and found nothing
  wrong in the threshold part. The source part is plausible beyond (6.3). This is downstream of
  F1 anyway.

**Blocking list, most severe first:**

1. **F1 (FATAL).** The sup-norm noise response (G2-R), the bridge (BR) and the ν_* term of G1′
   do not survive H(u) being increasing. Noise of fixed size ≍ H(X₀)^{−1/2} at the smallest
   jittered scales is amplified by Σ|c_n|/n ≥ c·log x, against a tolerance ≍ 1/log x. The
   stated inequalities fail from log x ≈ 10¹⁰ (with B′), or from log log x ≈ 600 (even with
   M-op), long before x₁.
   - Needed: a genuinely new cross-scale cancellation lemma. Candidates are an L²/martingale
     route with predictable coefficients (ref-1 B1 revived), or short-interval Möbius
     cancellation for μ_Pχ_x at relative length H(v)/v, combined with an O(1)-per-dyadic-block
     bound on ‖c_n‖ (M-op-type) so that the two ranges overlap.
2. **R1′-base, and the (X_*, X_**) echo window under the hard greedy (OPEN).** Alternatively, a
   switch to soft feedback, which then needs C1, C3, NV and G3 redone. v2 lists only the first.
3. **F2 (SERIOUS).** Lemma B′ in operator form is unproved: step (ii) uses A in place of I. It
   is needed by BR and by any repair of F1. My numerics (TV(G_n) ≈ |μ(n)|·(1 + o(1)) in the
   void-filter region) suggest a true statement, possibly even of M-op strength there. The
   threshold-straddling region is untested.
4. **S2 (SERIOUS, likely fixable).** Thm 4.2′'s block step fails for log x ≳ 0.0015·X₀, which
   includes all zero scales, because M_sm ≍ 100L⁵/X₀ > c′L⁴. Fix by bounding #(𝒟 ∩ short window)
   at large scales (Tijdeman, effective).
5. **S1 (SERIOUS, likely fixable).** NV for latest primes q ∈ [X₀, H(u)L⁶) at scales with
   H(u) ≥ X₀ (all u ≥ x₁). Needs an SM-type small-q lemma at smoothness level H(u)L⁶.
6. **CL and SM shape counting [S]**, with the two writing points in G8.
7. **Bookkeeping gaps.** G2 (exactness of the margin identity), G3 (stopping-time form of
   Thm 4.2′), G4 (union-bound arithmetic, probability budget), G5 (§8.3 inputs at smaller
   scales), G6 (scope of the Lean coverage).
8. **PENDING cross-check and LP constants.** Not blocking for existence.

**What is sound.**
- The conditional implication "(L-a) at all scales ⇒ ζ_P has zeros ρ_k with Re ρ_k → 1"
  (§2, Lemmas 2.1–2.3, Thm 2.4) holds up, modulo M1 and M2.
- The TC excess identity holds.
- Lemma M for sharp filters holds (both involutions checked).
- The scalar Lemmas B and B′ hold, and their Lean statements match the paper statements.
- The Lindley bookkeeping (Lean `count_eq`, `exists_sum_eq_Q`, `Q_le_of_window`) holds.
- LP's architecture holds: N♯ extension, positivity transferred from P_y, no residue
  at 0.
- `def Q` and `quasiRH_of_Q` in `Beurling.lean` match §0.1. Uniqueness of the continuation on
  {Re s > ½} \ {1} makes ¬Q follow from zeros of the continuation with Re → 1.
- The weak link is the derivation of (L-a): the queue bound at all scales.

**Scratch files** (all under `/tmp/rhscratch/referee-b/`):
- `supnoise.py`, `supnoise2.py`: F1 thresholds.
- `opres.py`: single-frequency resolvent model.
- `optv.py`, `optv2.py`: TV of the operator resolvent kernels, F2.
- `dl/bd.txt`: Broucke–Debruyne text, used for the MVT check.

## 7. Addendum: the updated draft (1021 lines; §0.2, §1.2, §5, §8 revised)

I re-read §0–§1.3, §3.4–§3.8, §5 and §7–§8 of the current file. §3.4–§3.5, §3.6 and §4.3 are
unchanged. So **F1, F2, S1 and S2 stand as written**. U8 ("referee re-check of the sup-norm route
and the bridge") is answered by F1 and F2.

**What the revision fixes.**
- G1 (classification): R1′-echo on (X_*, X_**) is now listed (U1″). G1′ and R1′-hi are now
  rule-tagged, with "x ≥ X_** under G".
- The "uses (scale)" column of R1′-hi now says "over **all** smaller scales, base range
  included". That is exactly the hook F1 needs.

**What it does not fix.**

**A1. F1 is rule-independent: S(ε) does not rescue R1′-hi (FATAL; confidence high).**
- §1.2 and §5.3(a) claim that under S(ε) "sup|ν| = O(ε/log x + √(λ/H)) at every scale, so NV
  and G2-R hold at every scale". The √(λ/H) term is the ordinary martingale noise. Its H is
  H(u) at scale u, which equals H(X₀) near the bottom of the jittered range. The placement rule
  does not change it.
- The F1 arithmetic is therefore unchanged. The table rows G1′ and R1′-hi ("[P] for x ≥ X_*
  under S(ε)") fail from log x ≈ 5·10⁹–4·10¹¹ on, under **either** rule. That is still inside
  [2X₀, X_*]. The "Bottom line" sentence "Only … R1′ are scale- and rule-limited" therefore
  understates the problem: R1′-hi is unproved at every scale under both rules.

**A2. The soft-rule deficit echo hits the same wall, and the claim "no resolution argument is
needed" is false (SERIOUS; confidence high).**
- Under S(ε), while Q > 0 the deficit is e ≈ −ε(v)ρ_ref(v). This is a *bias* on stretches of
  length ≍ v^{θ/2}, not mean-zero noise, and it is fixed once scale v has been processed.
- The draft's bound for its echo at x is |B(x)| ≤ (1 + log x)^{2K(x)+1}·ε(v)/log v.
- Case 1: x in "ε ≤ c′(1 + log x)^{−2K−1}/8" means the current scale v. Then
  ε(2X₀) ≈ exp(−2.885(log log X₀)²), and the echo bound exceeds c′/(8 log x) as soon as
  log log x exceeds log log X₀ by o(1). That fails far below X_*.
- Case 2: ε is a fixed constant calibrated to X_**, ε₀ := c′(1 + log X_**)^{−2K(X_**)−1}/8 ≈
  exp(−(4.3–6.5)·10⁴) (log log X_** ≈ 122–150). That is legitimate, since X_** is a function of X₀.
  Then the sup-norm bound covers (X_*, X_**) but fails just beyond X_**.
- Beyond X_** one needs gap-localPNT §6.7's *resolved-range* absorption (LP resolution of a bias
  pattern of relative length X_*^{θ/2−1}). That is [P] there, but it is not "nothing new".
- Either way, "no echo and no tower, and no resolution argument is needed" is incorrect.
  - The correct statement is: sup-norm with ε₀ on (X_*, X_**), plus §6.7 resolution on
    [X_**, ∞).
  - The S(ε) queue on the base range must then be computed with ε₀, not ε(v). That queue is
    ≍ λ log x/(cε₀) ≤ e^{6.5·10⁴}·polylog, which is harmless against x^η ≥ X₀^η.
- This repairs the *deficit* echo only. The *noise* echo (A1) needs the same kind of argument
  for mean-zero noise at every scale v with c√log x ≲ log v ≲ (log x)^{0.85}. There it has
  no resolved range: v runs up to x.

**A3. S(ε) changes the drift that G3 uses.** While Q > 0 the soft rule's drift is −ε·margin
per slot, not −c′/L.
- Thm 4.2′ (blocks L₀ = L⁵, q_min = L¹¹, E_cl windows 4L^{−6}) is built on the −c′/L drift.
- Under S(ε) the Freedman block length must be ≳ λ·M₁/ε² ≈ exp(5.8ℓ²)·polylog, so
  q_min ≳ L₀L⁶ and the CL/E_cl window lengths and SM's regimes all move.
- The last point matters for S1: smoothness levels ≍ exp(5.8ℓ²) are comparable to H.
- §5.3(a) lists "κ, the threshold" as pending. It should also list L₀, q_min, M₁ and the SM
  regimes. S2's M_sm-versus-drift comparison becomes 100(2 + L₀/X₀) versus εL₀/L, which needs
  L₀ ≪ X₀·ε/L, a real constraint.

**A4. Unchanged items that still need edits.**
- §0.3 still says the local multiplicity lemma "is not used in v2" (G5).
- §7.2 still has "α < 1" for BDR (M4). §7.3 still omits Broucke 2507.13780 Thm 1.6 (G7).
- §2's base-factor exponent (M1) and Thm 4.2′'s union-bound arithmetic (G4) are unchanged.
- Theorem A's bracket [R1′-int, R1′-echo, CL, SM] should add F1 (an OPEN cross-scale
  cancellation lemma), the operator form of LB′ (F2), the NV small-q lemma (S1), and the M_sm
  fix (S2).

**Revised one-line verdict.** Even under S(ε), and even granting R1′-int, CL and SM, Theorem A does
not follow. The sup-norm propagation of ordinary small-scale noise (F1) blocks R1′-hi at every
scale above log x ≈ 10¹⁰, and nothing in the revised §0.2, §1.2 or §5 addresses it.

## 8. Cross-check with referee A (`beurling-greedy-v2-referee-A.md`)

(My §7 is the addendum on the updated draft, so this cross-check is §8.)

| A's item | verdict | one-line reason |
|---|---|---|
| §1 sup-norm G2-R diverges at log x ≳ (log X₀)^{1.18} | **agree** | Same as my F1, same threshold. |
| §1 "χ_x(n) = 1 on a positive proportion of n ≈ x/X₀; no absolute-value bound can repair" | **disagree** (I made the same error) | χ_x(n) = 1 is t-dense with t = x/n, density ≍ log t/log n. A's own §3d/§6 corrects it. |
| §3a induction constants diverge, not a cycle | agree | Matches my F1 and G3. |
| §3b(1) NV step 2 false for q < H(u)L⁶ | agree | Same as my S1. |
| §3b(2) bridge has the same scale defect | agree | Same as my F1 (BR paragraph). |
| §3b(3) near-threshold weight super-polynomially small | agree | My M7 overcounted: it ignored P⁺(m) < p ≈ √(x/m), which forces m to be smooth. |
| §3c B′-op identity false (M − A on every pair) | agree | Same as my F2; same n = pq example. |
| §3d Lemma M correct; Saias density of supp χ_x | agree | My involution check matches. I did not rerun `chi_density.py`. |
| §3e LP correct; C(X₀)-dependence kills LP under B-lin and Huxley | agree / not checked | LP: agree. The B-lin constant C_{X₀}: not checked. |
| §3f ρ_det ≤ 1 + u^{−θ_b}; "x generic" unavailable | agree | I missed both. A window (u, u+u^{θ_b}] can hold ⌊u^{θ_b}⌋+1 integers. |
| §3g CL/E_cl queue-independent | agree | Same as my G8. |
| §3h Z-estimate exponent σ + θ_b − 1 | agree | Same as my M1. |
| §4.1 thesis Thm 3.1.1 states only the PNT, not the zero-free region | not checked | |
| §4.2 "everything else [P] or [C]" false | agree | |
| §4.4 Diamond's remark (Watkins page) bears on novelty | not checked | Relevant. Add Broucke 2507.13780 Thm 1.6 (my G7), which A does not mention. |
| §5 S(ε) needs general-m telescoping; Σε(u) ≪ c′ suffices under §6 weights | agree (in principle) | Under the weighting, a deficit ε(u) at scale u costs ≈ ε(u)/log x. This would dissolve my A2, *if* §6 is established. |
| §5 B-lin, randomised base, ranking | not checked | |
| §7 addendum, items 1–4 | agree | Item 1 is my A1. Item 2 (Mart(J) small-q increments) is the analogue of S1. Item 3: PR/(PR1) bookkeeping not independently checked. |

A does not raise my S2 (M_sm ≍ 100L⁵/X₀ exceeds the drift c′L⁴ at all zero scales), G4
(union-bound arithmetic), M4 (BDR α < ⅔) or G7. I still hold these.

**A's repair (§6): assessment.**

*(i) The reconciliation.*
- Yes, the scale-weighted sum is the right reconciliation with my "Σ|c_n|/n ≥ c log x".
- The total Σ|μχ_x|/n ≍ log x is true, but it is spread over dyadic scales u = x/n with weight
  W_x(u) ≍ log u/log x. That is Saias's bound with t = u, N = x/u.
- The small-scale noise is therefore damped by exactly the factor needed:
  log x·|e(x)| ≲ Σ_{u dyadic} log u·|ν(u)| ≲ Σ_L L^{O(1)}/√H(L) =: C_{X₀} → 0.
- For **scalar sharp** coefficients no signed (Möbius or martingale) cancellation is needed;
  positivity plus support sparsity is enough. I retract the "cancellation is necessary" part
  of F1 (corrections inserted in §1 and F1). The failure of the *draft's* stated bound stands.

*(ii) Does the route avoid cross-scale cancellation? Only if step 2 is valid for the operator
that actually appears.* A's risk (b) is the crux, and A's §6 is in tension with A's own §3c.
- **K_sh with the H-average** (v2 §3.6's K_sharp, which keeps Δ near-threshold). Lemma M then
  does **not** apply: the coefficients are kernels (A's §3c).
  - New numerics (`optv3.py`, void-filter model) give TV(C_n) at non-squarefree n with a small
    square factor that does **not** decay with the large prime: 0.146 at n = 4p (p up to 10⁵),
    0.117 at 9p, 0.081 at 25p, 0.091 at 8p.
  - Large squares p², p²q have TV ≈ 10⁻³. So these kernels carry O(1) mass off supp(μ) and
    give W_x^{op}(u) ≳ 0.02 per dyadic block wherever they survive.
  - If that persists for n > √x (untested), log x·Σ_u W^{op}|ν(u)| ≳ 0.02·log x·Σ_u|ν(u)| → ∞,
    and the divergence returns.
  - So this branch needs "M-op with t-dense support", i.e. TV(C_n) ≲ 1_{dense}(n) + tiny, which
    my data already contradict at non-squarefree n in the void region. It also needs an
    argument that those n do not reach small scales.
- **Pointwise K_sh.** Lemma M applies, but Δ = K_op − K_sh then contains (A − I) on **every**
  cofactor, not only near-threshold ones.
  - The dense cofactors (w > √(v/H)) are harmless: positive weights 1/w sampled densely give
    Riemann sums of (A − I)f ≈ 0, using only equidistribution of 𝒩 from (L-a). No signs are
    needed.
  - The sparse cofactors (w ≤ √(v/H), total weight ≈ ½ log v) act on e_sh at large scales
    t ≥ √(vH). So the perturbation in Δ converges only with a **regularity lemma for the
    response**: |(A − I)e_sh(t)| ≪ 1/log²t. That needs ν's own (A − I)-part ≍ H(t)^{−1/2}·polylog
    at those t (fine), together with R(δ)-type smoothness of the resolvent response at scale
    H(t). This is plausible but is an additional lemma, not in A's sketch.
- The edge terms (risk (c)) and the exactness of the margin identity (my G2) bear on the same
  split.

**Net.** A's route is the most promising repair. It converts my F1 from "needs cross-scale
cancellation" to "needs three lemmas":
1. a Saias-type upper bound for t-dense elements of the realised semigroup;
2. the pointwise-K_sh split, with the dense-cofactor Riemann-sum step and the
   sparse-cofactor regularity lemma above;
3. per-scale noise events with the S1 small-q truncation.

It avoids Möbius or martingale cancellation, but only along the pointwise branch. The
averaged branch, as written in A's §6 step 2, is contradicted by the non-squarefree TV data.

## 9. Targeted review: addendum §A2.3–§A2.4 (Saias-weighted G2-R; long-window Freedman)

Source: `beurling-greedy-v2-addendum.md` §A2.1–§A2.4. Scratch: `/tmp/rhscratch/referee-b/chiw.py`.

**Verdict.**
- A2.3's weighted bound is **correct** for ℕ-cofactors with *pointwise* sharp coefficients
  acting on ν as a function. Its constants are absolute, given Saias's upper bound.
- A2.4 is **correct up to a predictability wording fix**.
- The open list (i)–(iii) is **incomplete**:
  - add (iv): NV must be frozen per scale, otherwise the divergence returns as a
    √(log x) factor;
  - add (v): the weighting must also replace the crude sup in BR and (6.1);
  - sharpen (ii) into two concrete branches, one of which fails my numerics.

### 9.1 Claim 1: χ_x(n) = 1 ⟺ n is (x/n)-dense

- **Squarefree n: correct.** With p₁ < ⋯ < p_r, the Lemma M condition p_j·∏_{q≥p_j}q < x reads
  p_j·n/(p₁⋯p_{j−1}) < x, i.e. p_j < u·p₁⋯p_{j−1} with u = x/n. That is Tenenbaum's prime-factor
  criterion for u-dense n (consecutive divisor ratios ≤ u).
  - The criterion is combinatorial on the divisor list, so it holds verbatim for real-valued
    generalized primes.
  - Strict versus ≤ differs only at non-generic x.
  - For n ∈ (x/2u, x/u] we have u ≤ x/n < 2u, so "χ_x(n) = 1 ⟹ 2u-dense" is right.
- **Non-squarefree n under the pointwise sharp operator:** c_n = 0 exactly (Lemma M's d ↔ d△{s}
  pairing). So the support is {squarefree, u-dense}, and the Saias count of *all* u-dense n is a
  valid upper bound.
- **Order weights (Remark M′, decision order).** Jitter can swap the order only of primes within
  H/2 of each other, and t(p) = p(1 + O(H/p)). So χ^t_x(n) = 1 ⟹ n is 4u-dense, which is harmless
  for upper bounds. This should be stated, since the compensator's filter is in decision order.
- **Not covered: the averaged operator.** For the H-averaged sharp operator the coefficients are
  kernels with off-support mass. My §8 numerics give TV ≈ 0.146 at n = 4p, 0.117 at 9p and 0.081
  at 25p, not decaying in p. Claim 1 says nothing about these (see §9.5(ii)).
- **Numerics.** My independent recount (`chiw.py`) reproduces A2.3(b)'s table exactly:
  - W = 0.1084 (10⁷, 20), 0.2143 (10⁸, 200), 0.2767 (10⁹, 2000), 0.0953 (10⁸, 20);
  - shares 0.257, 0.509, 0.657, 0.226;
  - W/(log 2u/log(x/u)) = 0.39–0.47, stable, as Saias predicts.
  - So gap-G3 §9.8's ρ(v − 1) tail weight is indeed false.

### 9.2 Claim 2: the weighted bound

**Derivation: correct.**
- Group n by u = x/n dyadic. For u ≤ √(x/2), Saias's range X = x/u ≥ y = 2u holds, and
  W(u;x) ≤ (2u/x)·D(x/u, 2u) ≤ 2c₄ log(2u)/log(x/u) ≤ 4c₄ log(2u)/log x.
- For u > √(x/2), c_n = μ(n) (the filter is void), and W ≤ log 2 + O(u/x) per block, over ≤ log₂x
  blocks.
- This gives the displayed inequality with C = 4c₄ + 2. Saias's c₄ is absolute: Weingartner's
  uniform form D(X,t) ≤ c₄X log t/log(Xt), checked via his statement of Saias Thm 1, not at
  source.
- **The √x split hides nothing.** The second term is C log²x·sup_{u≥√x}|ν|, which is small since
  H(√x) is huge.

**Two things it does hide.**
- **(a) Per-scale freezing of NV.** "sup_{[u,2u]}|ν| ≤ √(4M₁λ(u)/H(u)) + …" requires NV to be
  proved *at scale u*, with λ(u) = 3 log u, M₁(u), E_cl at L(u), and B(u), and then frozen.
  - v2 §3.4 proves NV at the current scale x, with λ = 3L(x), M₁(L(x)) and a union over all windows
    ≤ x. Inserted here, that gives log x·|Ke| ≲ √(M₁(x)λ(x))·C′_{X₀} ≍ (L/√log L)·C′_{X₀} → ∞.
  - So the per-scale version is **essential**, not cosmetic.
  - It needs: per-scale failure probability ≤ u^{−2} (fine, summable over dyadic u); the events
    added to G_{<y}; and E_cl stated per scale.
- **(b) ν is a measure (A2.1), tested on windows.**
  - Under pointwise sharp coefficients, (𝒦_sh-resolvent ν)(W) tests ν on W/n, of length
    H(x)/n ≪ H(x/n) for large n.
  - NV controls ν only on windows of length ≳ H(u). On a window of length ≪ 1, ν is O(1) per
    element, not small.
  - So the pointwise branch must keep at least the last jitter smoothing B, which makes the
    coefficient maps operator-valued again. This belongs in (ii) and must be said.

### 9.3 Claim 3: polylog H = (log u)^C

**The G2-R arithmetic is right.** With ℓ_k := log 2^k ≍ k, the per-block term is
log(2u)·[√(4M₁λ/H) + (B + 4M₁)/H] ≍ k·k·k^{−C/2} + k·(k³ + 100k⁵/X₀)·k^{−C}. The sum over k
converges and is (log X₀)^{−large} once C > 6, and C > 7 while the M_sm term ∝ L⁵/X₀ is present.
The √x term is L³·L^{−C/2}, which needs C > 6. So C = 8 is safe.

**It does not remove S1.**
- NV's increment bound needs H(u)/q ≪ L^{−6} for latest primes q ≥ X₀, i.e. L^{C+6} ≪ X₀.
- With H = L^C, this fails once log u ≳ X₀^{1/(C+6)}, which is still ≪ log x₁ = X₀².
- So the small-q truncation (iii) is needed at the zero scales for polylog H too.

Polylog H also helps the lag ((L-a) becomes polylog), and B′'s quasi-polylog requirement
disappears. But that holds only where the Saias weighting has *replaced* B′, i.e. in G2-R, BR and
(6.1) (see (v) below).

### 9.4 Claim 4: A2.4, long-window Freedman

**Correct, with one wording fix.**
- **The per-prime increment is fine.** For each U_q the window J/q(U) has length |J|/q(U), so
  X_q ≤ 2|J|/q + 2B + H + 7 pointwise. Hence |X_q − E[X_q|F]| ≤ b_q with b_q computed from
  s_q − H/2, which is predictable.
  - My first worry, that a predictable sup over the jitter range adds a term xH/q², is unfounded.
    Each position's window has the same length.
- **The fix.** "q ∈ [Q, 2Q)" must mean the **decision slot** s_q ∈ [Q, 2Q). The value q depends
  on U_q, so selecting by value is not predictable. With s_q, each Mart_Q is a martingale and
  Freedman applies as written.
- The bound V_Q ≤ 2b_Q·Comp(J) uses the full compensator. That is crude but valid. The dyadic sum
  is dominated by Q₀: ≈ 4|J|√(λ/Q₀)/(1 − 2^{−1/2}) ≈ 14|J|L^{−5/2}. The (B+H) terms need
  |J| ≳ L⁷(L⁵ + H), which L^{10}H covers.
- **Small q < Q₀.** These composites are (Q₀ + H)-smooth, so a global Rankin count
  Ψ_𝒩(2x, Q₀ + H) ≤ x·exp(−(1+o(1))u log u) suffices; no short-interval smooth bound is needed.
  - With H = exp(8ℓ²): u = L/(8ℓ²), and x·e^{−L/(9ℓ)} ≪ δx/L² since δ ≥ e^{−c√L}.
  - With polylog H: u ≍ L/log L, and ρ ≈ x^{−1/max(C,6)}. Also fine.
  - The Chebyshev input is the same as SM's.
- The probability bookkeeping (8L/x per dyadic x, or λ = 4L) is correctly flagged.

### 9.5 Claim 5: is the open list (i)–(iii) complete?

No. My additions and sharpenings:

**(i) Beurling–Saias.**
- Needed for the realised semigroup, in the decision-order (4u-dense) form of §9.1.
- A Buchstab recursion with LP's local Chebyshev bounds is plausible, since only the *upper* bound
  is needed.

**(ii) Operator weights. Must be split into two concrete branches.** As written, A2.3(ii) says Δ
"is supported on near-threshold cofactors". That is true only for the *averaged* K_sh, for which
Lemma M does not apply.
- **(ii-a) Averaged K_sh.** One needs "M-op with dense support": Σ_{n∈(x/2u,x/u]}TV(C_n)/n ≪ log u/log x
  for u ≤ √x.
  - My TV data (§8) show off-support mass ≈ 0.15 at n = 4p in the void region.
  - So this needs a proof that such mass does not reach n > √x, or that it carries Saias-sized
    weight. It is currently unsupported.
- **(ii-b) Pointwise K_sh.** Lemma M applies, but then:
  - Δ = 𝒦 − 𝒦_pt contains (B − I) on **every** cofactor.
  - Dense cofactors are handled by Riemann sums, using only equidistribution of 𝒩.
  - The sparse cofactors w ≤ √(v/H) carry weight ≈ ½ log v. They need a **regularity lemma**
    |(B − I)e(t)| ≪ 1/log²t at large t.
  - And by §9.2(b), at least one B must be kept so that ν is tested on H(u)-windows.

**(iii) NV small-q truncation.** Needed for both choices of H (§9.3).

**(iv) [missing] Per-scale NV**, with λ(u), M₁(u), E_cl(u) and B(u) frozen at scale u, and
included in G_{<y} and in the probability budget (§9.2(a)). Without it the weighted bound diverges
like √(log x).

**(v) [missing] The same weighting in BR (step 1) and in (6.1)'s ν_* term.**
- A2.2 lists these rows as depending on B′-op, but A2.3's status covers only G2-R.
- For (6.1), use K_r e = −e − ν (referee A §6.7) rather than a resolvent bound.
- For BR, the near-threshold weight is super-polynomially small (referee A §3b(3); my M7 was an
  overcount), so the weighted bound absorbs it easily. But it must be written.

**(vi) [outside G2-R, still blocking Theorem A]:**
- S2, the M_sm-versus-drift block step at zero scales. Not affected by A2.3.
- CL and SM [S].
- B-lin's μ bookkeeping (A2.2 last bullet) must be rerun with the weighted bound.

**Net.** A2.3 turns the F1 divergence into a **proved scalar inequality** plus (i)–(v). Of those:
- (iv) and (v) are bookkeeping;
- (i) is standard in shape;
- (ii) is the real content: one of the two branches above must be proved.
"Reduced to three explicit statements" understates this by (iv), (v) and the branch choice in (ii).

## 10. Targeted review: gap-G3 §13 (fix for S1 and S2 by absorption; Lemma R)

Source: `gap-G3.md` §13.1–§13.5 (supersedes §12.2), with addendum A11, A11.2 and A12.2 for the §2
side.

**Verdict.**
- Lemma R and the absorption idea are **sound**.
- S2 is **closed** (κ = 3), given CL.
- S1 is closed for large q and for rigid cofactors (given (SW)). It is **not closed as written**
  for small q with jittered cofactors: the increment bound there is applied to the wrong count.
  An easy repair using the same ingredients is given below.
- Two consistency items are new: the (H_y) normalisation for LP, and the removal of 𝒜 from K.
- §13 also leans on CL/DR and B-lin, not only on (SW).

### 10.1 Lemma R: correct, with two minor repairs

- **The main computation is right.** σ = 1 − b gives X₀^{1−σ} = L. Chebyshev gives
  Σ_{p<X₀}p^{b−1} ≈ L/(b log X₀) = L/log L. So the exponent is 1 − b + (1+o(1))/log L.
  - That matches the true size Ψ ≈ x·ρ(u), whose exponent is ≈ 1 − b + log log X₀/log X₀.
  - The examples are conservative. 0.983 at b = 0.04 assumes log X₀ ≥ 1087; with log X₀ ≥ 10⁸ the
    exponent is 0.96. The 0.008 example uses log X₀ ≈ 1100.
- **Repair (a): Rankin needs Σ −log(1 − p^{−σ}), not Σ p^{−σ}.**
  - At σ = 0.01 the small primes contribute about log(100/log p) each: 2^{−0.01} gives a factor 145.
  - So for b ≥ 1 the correct bound is Σ ≤ 1.3π(X₀) + e^{101} ≤ 0.001L once log X₀ ≥ 2600.
  - x^{0.011} stands.
- **Repair (b): "for b ≤ 1" is not uniform as b → 1⁻.** σ = 1 − b → 0 and the Rankin product blows
  up. Use σ = max(1 − b, 0.01). Then nothing changes in the stated ranges.

### 10.2 Absorption (§13.2): size, causality, T1, and what else it touches

- **Size and margin: correct.**
  - #(𝒜 ∩ [x,2x]) ≤ π_P(Q)·L·Ψ(2x, X₀) ≤ x^{1−b+o(1)}HL^{11}.
  - Since the window [u, u + u^{0.99}] lies inside [u, 2u], ρ_𝒜 ≤ x^{−0.005+o(1)}.
  - This is sure, not only on the good event: there is ≤ 1 prime per slot.
- **Causality: correct.**
  - Membership of n ∈ [u, 2u] needs only the landed values of jittered q < Q(2u) ≈ H(u)L⁶ ≪ u.
  - q is the only jittered prime, so it is automatically the latest-decided.
  - So T on [u, 2u], including ρ_𝒜 over the look-ahead window u^{0.99}, is known long before slot u.
- **(T1): correct for Q.**
  - E_𝒜 ≤ one window count ≤ x^{1−b+o(1)}. That is ≤ x^θ once L ≥ X₀^{1−θ+o(1)}, and ≤ C_{X₀}x^θ with
    C_{X₀} = exp(O(X₀^{1−θ})) on the bounded range.
  - A11.3's ω-by-ω argument makes the random adapted T harmless for Q.
- **New (GAP, confidence high): (H_y) at θ′ = ¾, C = 1 fails, so LP's normalisation must change.**
  - On L ∈ [X₀^{0.04}, X₀^{1/4+o(1)}], |E_𝒜| reaches x^{0.95…0.985}. This is not a crude bound:
    a moving average with window x^{0.99} genuinely errs by ≈ ½(local count) at the top end.
  - So §0.3's |N(u) − u| ≤ u^{3/4} is false there, and LP (used above X_LP, which is ≪ exp(X₀^{0.04}))
    sees it.
  - Fix: run LP with θ′ = 0.996 and C = O(1). The constants stay absolute, but c shrinks with
    r = (1−θ′)/2, so log X_LP grows by a large absolute factor. Then re-derive X₀ ≥ X_LP.
  - Do not use C_{X₀}: that is the circularity referee A §3e warned about.
- **New (GAP, confidence medium): 𝒜 must leave the compensator.**
  - 𝒜-elements now consume their own jump slots, so the arrivals that Lindley and the margin
    see are the non-𝒜 composites. ρ_ref must then be (1 + K′)^{−1}(1 − ρ_det − ρ_𝒜 + R′), with K′
    excluding pairs (w X₀-smooth, latest prime < Q).
  - K′'s exclusion is a lower bound on w for smooth blocks, not of Lemma M's form F(B_i)Π_i < x.
    So Lemma M is not immediate for K′.
  - Cleanest route: keep K, and carry [K_𝒜ρ̃ − ρ_𝒜] as a source perturbation.
    - Both terms are ≤ v^{−0.004+o(1)} at scales v ≥ exp(L_𝒜), by Lemma R.
    - With Saias weights the response is ≪ (1/log x)·Σ_{log v≥L_𝒜}log v·v^{−0.004}, which is
      negligible.
  - This must be written out in G2 and in the (SW) bookkeeping.
- **Jittered-cofactor small-q elements as ordinary arrivals: fine in principle.** They have ≥ 2
  jittered primes, all decided before q, so they are (Q + H)-smooth and rare.
  - Their per-block count, ≤ 100(1 + M₁), rests on CL's long-window moments, hence on CL [S]
    and Lemma DR.
  - See §10.4 for how they enter NV.
- **§2 side (A11, A11.2, A12.2): no conflict with §13.2's thresholds.**
  - A11's (log n)^{11} version and A11.2's extended version (with arbitrary cofactors, abscissa 1)
    are both superseded.
  - A12.2's check under §13.2 is right: Σ_{n∈𝒜}n^{−σ} ≤ exp(−0.016X₀^{0.04}) on σ ≥ 1 − 1/log X₀;
    the Plancherel mean square ≤ exp(X₀^{1/2})/Γ; and γ_k is selected from Z_∞.
  - A11's table row "(T1): adds O(x^{θ/2})" is stale. With the x^{0.99} window it is the C_{X₀}
    statement above.
  - The (H_y) point above is the one §2-adjacent item that A12 does not cover.

### 10.3 S2 by ranges (§13.3): closed, κ = 3 (given CL)

- **The switch point should be L_𝒜.** The ranges [·, 7.5·10⁻⁴X₀] and [X₀^{0.04}, ·] overlap.
- **Below the switch.** For L < X₀^{1/11}, SM is vacuous. On [X₀^{1/11}, X₀^{0.04}],
  L⁵/X₀ ≤ X₀^{−0.8}:
  - the per-block rigid part is ≤ 100(2 + L⁵/X₀) ≤ 201;
  - the distinct-top-prime count is an adapted-Bernoulli Freedman bound with mean ≲ L⁵x^{−0.059}.
  I accept this.
- **Above the switch.** Rigid-cofactor small-q elements are absorbed and cancel exactly. The
  remainder is 100(1 + M₁) + 0.7L³/log²L + O(L) ≤ L³ for L ≥ 1100, so the full-block inequality
  c′L⁴ ≥ √(12M₁L⁶) + 4M₁L + L³ holds at every scale.
- The 7.5·10⁻⁴X₀ range is needed only to show overlap. Using it above X₀^{1/2}/10 would make the
  remainder exceed L³, so state that absorption is used from L_𝒜 on.
- **So S2 is closed, and B ≈ 25L³/log L with κ = 3.** The jittered-cofactor term inherits CL [S]
  and DR.

### 10.4 S1 split at HL⁶ (§13.4)

- **q ≥ HL⁶: correct.** The window W_H/q has length ≤ L^{−6}, so E_cl gives X_q ≤ 2M₁. (E_cl is per
  scale, §9.2(a).)
- **q < HL⁶, rigid cofactors: correct given (SW).**
  - For L(u) ≥ L_𝒜 these are in 𝒜, since H(n) ≈ H(u) gives Q(n) ≥ HL⁶.
  - Below L_𝒜, unit spacing gives X_q ≤ 1 + H/X₀. With V ≤ b·Comp ≤ (1 + H/X₀)H, the contribution
    to ν is ≈ √(6L/X₀) + 2L/X₀; the stated √(3L/X₀) is off by √2, which is harmless.
  - The Saias-weighted sum over L < X₀^{0.04} is ≲ X₀^{0.1}/√X₀ = X₀^{−0.4}. ✓
  - The parenthetical "below L ≈ 1.2·10⁵, H < X₀" uses log X₀ ≈ 1100. With log X₀ ≥ 10⁸ the
    empty range is L < e^{1.1·10⁴}, which is fine and conservative.
- **q < HL⁶, jittered cofactors: the stated argument is invalid (GAP, confidence high), but it is
  repairable.**
  - **What it does.** It equates X_q (composites in W_H whose *latest-decided* prime is q) with
    N_jit(W_H/q) (all jittered elements in the cofactor window). It then uses §8.3's two-sided
    discrepancy to get |X_q − E X_q| ≤ 4B + 4λ + 14.
  - **Why that fails.** Admissible cofactors m must have every prime decided before q < HL⁶, so
    they are (HL⁶ + H)-smooth. Most elements of W_H/q, at scale u/q ≫ HL⁶, are not admissible.
    §8.3 controls the fluctuation of N, not of this sparse sub-population, so the increment bound
    does not transfer. V ≤ π(HL⁶)b² is also not justified.
  - **Repair, with the same inputs.**
    - The increment is b_q ≤ max_U N(W_H/q(U)) ≤ H/q + 2B + 2λ + 8. That uses §8.3's one-sided
      local count at scale u/q < u, so it is **non-circular**.
    - The compensator is Comp_small ≤ H·Ψ_𝒩-density(HL⁶ + H) ≤ H·e^{−L/(9ℓ)}, by Rankin with
      the realised Chebyshev bound, a predictable sum.
    - Freedman with V ≤ max b_q·Comp_small then gives a ν-contribution
      ≲ √(L e^{−L/(9ℓ)}(1/X₀ + B/H)). This is summable with log u weights.
    - With the stated (crude) bound V ≤ (H/X₀ + 3B)·H, the per-scale term would be ≈ √(6L/X₀) at
      **every** scale. The (SW) sum would then diverge like L_max^{2.5}/√X₀. So the Rankin
      compensator is essential, not optional.
  - **Non-circularity (your question): yes.** §8.3 at scale u/q uses the queue bound and the
    lag-landing event at scale u/q < u, both in G_{<u}. The lag-landing w.h.p. event (union over
    windows) must be in the probability budget.

### 10.5 What §13 uses besides (SW)

1. **CL (shape count [S]) and Lemma DR**, a Diophantine input still owed by fix-smooth. They are
   needed for E_cl (S1 large q) and for the jittered-cofactor part in S2. "S1/S2 need no
   Diophantine input" is true only of the rigid parts that §13 changes.
2. **§8.3 multiplicity lemma at smaller scales**, with its lag-landing event (§10.4).
3. **Per-scale NV** (my §9.2(a)) and the operator-weight branch (ii) of (SW) itself (§9.5).
   (SW) is only a scalar inequality until (ii) is proved.
4. **The B-lin target and its pending items** (A10 items 42–45: normalisation N1, the
   "exact up to O(κ/log x)" identity N2, LP with shrunken discs N3). §13.2's "rational counterpart in
   B-lin's 1 − ρ_det" assumes them.
5. **LP with a changed normalisation** θ′ ≥ 0.995 (§10.2). This is new.
6. **The 𝒜-compensator perturbation** in G2 and (SW) (§10.2). This is new.
7. **Rankin for the realised system at smoothness HL⁶ + H**, already used in A2.4. It needs
   Chebyshev from LP at scales ≤ 2HL⁶, which is in hand.

**Net.** §13 does what it claims for the *rigid* small-q elements: S2 is closed with κ = 3, and
the rigid part of S1 is closed given (SW), with no Tijdeman input. The jittered-cofactor part of S1
needs the repair above. Items 5 and 6 should be added to the edit list.

## 11. Review of gap-G3 §14 (canonical absorption = §12.4's extended class) and Lemma P

Source: `gap-G3.md` §12.4–§12.5 and §14. This supersedes my §10 wherever §10 concerned §13.2's 𝒜.
Lemma R (§10.1) and the range logic (§10.3) still stand.

**Verdict.**
- The canonical version is **sound**. Lemma P is correct, with one wrong threshold that does not
  matter in its application.
- With it, S2 is closed for every L, and S1 reduces to the original NV step 2 (E_cl) wherever small
  jittered primes exist.
- Two items still need writing:
  - the 𝒜-compensator perturbation, which needs Saias weights;
  - the source-smoothness claim, which is overstated but not needed.

### 11.1 Correction to my §10: gap-g3's objection to §13.2 is right

- I accepted §13.3's "jittered-cofactor part ≤ 100(1 + M₁) via CL long-window moments". That is
  **wrong above L ≈ X₀^{0.4}**.
- Elements r·r′·d with two small jittered primes and rigid d form, for fixed (r, r′), the rigid
  pattern rr′·{d}: runs of length up to L⁵/(rr′) per block, for the price of one jitter.
- CL's step "|d − d′| ≤ εd < 1 forces d = d′" needs the window to be shorter than rr′, which fails
  once L⁵ > X₀².
- So §13.2's single-jittered-prime 𝒜 does not close S2 at the zero scales. **My §10.3 verdict
  "S2 closed" applied only below X₀^{0.4}.** gap-g3 caught this; I did not.

### 11.2 Lemma P (§12.4, (12.1)): correct

- **(i) Smoothness.** 𝒜 ≠ ∅ only where y(n) > X₀, since jittered r ≥ X₀. So rigid primes
  (< X₀ < y) and earlier-decided jittered primes (< r + H) are all < 2y. ✓
- **(ii)–(iii) Divisor trick.** Stop at the first partial product d > h. Then d ∈ (h, 2yh] is a
  realised 2y-smooth element, and |I_d| = h/d < 1. Counting all pairs (d, m), not only canonical
  ones, only overcounts. ✓
- **(iv) Window counts.** N(I_d) ≤ L⁸ via §8.3 at height u/d < u plus E_cl.
  - E_cl alone already gives N(J) ≤ (L⁶/2 + 1)M₁ for |J| < 1, so §8.3 is not even needed here.
  - This is non-circular: only heights < u are used. ✓
- **(v) Rankin.** The form exp(−u log u + (2+o(1))u/log u + O(log log y)) is right, with the
  Chebyshev input from LP at scales ≤ 2y ≪ u.
  - **But "≤ exp(−0.9u_* log u_*) for u_* ≥ e³" is false.** At u_* = e³, 0.1u log u = 6 while
    2u/log u = 13.4. It needs log u_* ≥ 4.6 or so (u_* ≳ 100), plus room for 2 log log 2y.
  - **In the application u₀ ≈ 535 at L = 10⁷**, so the conclusion stands. Fix the stated
    threshold.
- **(vi) Arithmetic (12.2).** I reproduce 3021 ≥ 2370 at L = 10⁷ (θ = ¼). Larger θ only helps,
  since u₀ ∝ θ_b. ✓

### 11.3 The canonical class: what it fixes, and what still needs writing

- **S2.** For L ≥ L_*, every composite with latest prime < y (> L¹¹ there) is absorbed, at any
  depth, so C_sm ≡ 0.
  - Below L_* = 10⁷ there are **no** jittered primes < L¹¹, since L¹¹ ≤ 10⁷⁷ ≪ X₀ for log X₀ ≥ 10⁸.
    So S2's small-q term is vacuous, not merely bounded.
  - **Closed for all L, B ≈ 25L³/log L, κ = 3.** This still inherits CL [S] and DR through E_cl.
- **S1.** For L ≥ L_*, every non-absorbed arrival in W_H at height u has q ≥ y(u) = H(u)L⁶. So
  |W_H/q| ≤ L^{−6} and E_cl gives X_q ≤ 2M₁: the original step, now valid.
  - Below L_*, HL⁶ ≤ e^{2.2·10³} ≪ X₀, so there are no jittered q < HL⁶, and §13.4's split is
    vacuous. My §10.4 objection (jittered small q) is therefore **moot** for the canonical version,
    given log X₀ ≥ 10⁸.
  - It would bite only if X₀ were as small as e^{1100}, where HL⁶ > X₀ already at L ≈ 1.2·10⁵ < L_*.
    So §14's table row "below L_*: §8.3 for jittered small q" should either be deleted (vacuous) or
    replaced by my §10.4 repair.
- **(T1) and (H_y).** |E_𝒜| ≤ hL^{−4} ≤ x^{θ/2} pointwise. So **(H_y) at θ′ = ¾, C = 1 survives**:
  my §10.2 concern was specific to §13.2's x^{0.99} window and is resolved by the u^{θ/2} window.
  - Lemma R's role is reduced to N1's drift, as §14 says.
- **§2.** #𝒜 = x^{1−o(1)}, so there is no sure bound for σ < 1. A11.2's height-dependent bounds
  must be used, and I re-checked them:
  - on the δ_k-discs, δ_k v ≤ v/(10 log v) needs 90(log log x_k)² ≤ log x_k ✓;
  - the a > Y tail is ≲ Y^{δ_k − 1/(9 log log Y)} ✓;
  - the Plancherel mean square is x_k^{θ−½−o(1)} ✓;
  - γ_k is selected from Z_∞ ✓.
  - The A12.2 sure bound is correctly demoted to a record.
- **Still to write (a): the 𝒜-compensator.** Absorbed elements must leave the compensator. The
  exclusion "latest prime < y" is x_i/w_i ≥ y(x_i) on each step. That depends on consecutive
  partial products, so it is not Lemma M's F(B_i)Π_i < x form, and Lemma M is not immediate for K′.
  - Route: keep K, and carry [K_𝒜ρ̃ − ρ_𝒜] as source. Both are ≤ L(v)^{−4} by Lemma P and Rankin.
  - **This needs Saias weights.** The crude bound (1 + log x)·2L_*^{−4} fails once log x ≳ 10²⁷.
  - The weighted sum (1/log x)Σ_{L(v)≥L_*}L(v)·L(v)^{−4} ≈ 10^{−14}/log x is negligible.
  - So "(SW): S1 adds none" is right for S1, but the 𝒜-source term adds a (harmless) (SW) use.
    Record it.
- **Still to write (b): source smoothness.** "ρ_𝒜 changes by ≤ 2(H/h)L^{−4} per H-window" needs a
  count bound on H-windows. The divisor trick at window H gives u₀ = log H/log 2y < 1, so Rankin
  gives nothing.
  - Only "≤ 2L^{−4} per H-window" (from the h-window bound) is proved.
  - That is enough: every downstream use (margin, LP⁺, R(δ), the bridge's ω) needs the source
    variation ≪ 1/log x, not smoothness per se. Restate it.

### 11.4 What the canonical version uses (complete list, as I read it)

- E_cl (CL [S] + Lemma DR), at heights < u.
- §8.3 at heights < u (optional in Lemma P), with its lag-landing event.
- Beurling–Rankin with LP's Chebyshev bound at scales ≤ 2y.
- (SW) for G2-R's main term, plus the small 𝒜-source term of 11.3(a).
- A11.2's §2 bounds.
- B-lin's N1 (Lemma R) for the drift.
- log X₀ ≥ 10⁸, which makes everything below L_* vacuous.

Nothing else. In particular no Tijdeman or Evertse input is needed, and no short-interval
smooth-number result beyond what the divisor trick proves.

### 11.5 gap-G3 §14.1 (my §10 items applied to the canonical 𝒜) and §11.5 (rank-deficient CL)

| §14.1 item | verdict | reason |
|---|---|---|
| 1. Lemma R (Σ −log(1−p^{−σ}); σ = max(1−b, 0.01)); N1 drift only | **agree** | Fixed as I asked. |
| 2. (H_y) moot since \|E_𝒜\| ≤ x^{θ/2}L^{−4} | **agree** | Same as my §11.3. θ′ = ¾, C = 1 stands. |
| 3. σ_𝒜 := K_𝒜ρ̃ − ρ_𝒜 as source; Lemma M on full K only | **agree, tag [P \| CL]** | See note (a). |
| 4. S1 jittered small q below L_*: one-sided b_q, crude Comp, "no (SW) needed" | **agree with the bound, disagree with the reasoning** | See note (b). |
| 5. S2: absorption from L_*; below it D ≤ 2, remainder ≤ L³ | **agree** | For log X₀ ≥ 10⁸ the range below L_* is vacuous anyway (§11.3). |
| 6. "No Diophantine input" scoped to the rigid parts | **agree** | |

**(a) σ_𝒜.**
- The identity ρ̃ + Kρ̃ = (1 − ρ_det + R′) + σ_𝒜 − ν follows from primes(W) = ∫(1 − ρ_det − ρ_𝒜 + R′) − (non-𝒜
  arrivals) + ΔQ, with K = K_{¬𝒜} + K_𝒜. ✓
- K_𝒜ρ̃(x) ≤ ‖ρ̃‖_∞·Σ_{w∈𝒢_{2y}, w≥x/y}1/w ≤ 2 log(2y)·exp(−0.9u log u) with u ≈ L/log 2y, which is ≈ 4·10³ at
  L_*. So |σ_𝒜| ≤ 2L^{−4} holds with vast room.
- The Saias-weighted sum is ≈ 1.4L_*^{−2}, under the stated 3L_*^{−2}. ✓ The v > √x blocks add
  ≲ (log x)^{−2}, which is also fine.
- **One caveat.** The weights are for the *scalar* sharp resolvent. σ_𝒜 is smooth at scale ≳ H, being a
  compensator density plus a u^{θ/2} moving average. So passing to the operator-valued 𝒦 costs only O(H·|σ_𝒜′|),
  by the bridge's smooth-input argument. Say so. Tag [P | CL] (through Lemma P), not bare [P].

**(b) S1, jittered small q, below L_* (your question on the Rankin step).**
- **The bound is right.** b_q ≤ 2H/q + 2B + 2λ + 8 is one-sided and uses §8.3 at height u/q, on its landing event.
  The crude Comp ≤ H + 2 then gives a per-scale term √(5λ/X₀ + 5Bλ/H) + O(λ/X₀ + Bλ/H). ✓
- **Why Rankin is now inessential.** In §13.2's setting the jittered-small-q case occurred at *every* large scale.
  The crude per-scale term ≈ √(λ/X₀) summed with log v weights over all scales diverged, so Rankin was essential.
  Under canonical absorption the case exists only for L < L_*, a **bounded set of scales**, so
  Σ_{L<L_*}L·√(15L/X₀) ≲ L_*^{2.5}X₀^{−1/2} ≈ e^{−510} (X₀ = e^{1100}). It is inessential because the range is
  finite, not because H/q or B are small.
- **The stated reasoning is the F1 fallacy.** "(1+L)·e^{−540} with L < 10⁷ is negligible, so no (SW) summation is
  needed" multiplies by the *small* scale's log.
  - A fixed small-scale term is propagated to *every* evaluation scale x with resolvent weight Σ|c_n|/n ≍ log x
    (crude), and (1 + log x)·e^{−540} → ∞.
  - Only the Saias weighting turns it into (1/log x)·Σ_{L<L_*}L·e^{−540}.
  - So these terms *are* summed in (SW), harmlessly: ≲ 10^{14}e^{−540}.
  - The correct wording: "S1 adds no new *kind* of (SW) term. Its small-scale terms enter (SW) like the main term
    and contribute ≤ e^{−500}."
- **For log X₀ ≥ 10⁸ the whole case is vacuous.** H(u)L⁶ ≤ e^{2.2·10³} ≪ X₀ for L < L_*.
- The §8.3 landing-event budget (≤ x^{−1} per dyadic height) is correctly added.

**(c) gap-g3 §11.5: CL's uniform moment form is false (new, important for the [S] status of CL).**
- The grid example checks out: k = m² elements R_a q_b, with the R's and q's each pairwise within relative ε. Its
  cost is ≈ (Aδ)^{2m−1}(4A/z)^{m−1}, which exceeds (C₁Aδ)^{m²} once (m−1)·log(1/(Aδ)) > log z.
- So v2 §4.1's "E[binom(N_jit(J),k); G] ≤ (C₁Aδ)^k for all k ≥ 1" is **false as stated**, not merely sketched.
- What survives: the rank-full moment bound, plus gap-g3's (DR-res) requirement for E_cl. Grids are harmless for
  E_cl: ≲ z^{−(m−2)}·polylog per height, and they occur only at z ≥ X₀².
- U3 should read: "CL [P for rank-full configurations]; rank-deficient part [OPEN] as (DR-res)". My G8 did not catch
  this.

**Answers to the lead's four questions.**
1. **Lemma P:** correct in the Beurling setting. The divisor trick needs only realised partial products. N(I_d) ≤ L⁸
   holds (E_cl alone suffices). The (12.2) check reproduces at L_* (3021 ≥ 2370). The stated Rankin threshold u_* ≥ e³
   is wrong (it needs ≈ e^{4.6}), which is harmless at u₀ ≈ 535.
2. **My §10 gaps:**
   - (H_y): holds without renormalisation.
   - The 𝒜-compensator perturbation: still needed; it is now written (§14.1(3)), modulo caveat (a).
   - S1 jittered cofactors: gone above L_*, and correctly bounded below L_* (vacuous for log X₀ ≥ 10⁸), modulo the
     wording in (b).
3. **§13.2 insufficient (r·r′·d runs): agree** (§11.1).
4. **"S1 adds no (SW) dependence":** true in kind, false as argued. Its terms must go through the Saias weighting
   like every fixed small-scale term, which they do harmlessly.

**11.6 Note (after the lead's query).** §11.3's "still to write (a)" predates §14.1. gap-g3 §14.1 item 3 has since
written σ_𝒜. I checked it in §11.5(a): the identity, |σ_𝒜| ≤ 2L⁻⁴ and the Saias sum ≈ 1.4L_*⁻² ≤ 3L_*⁻² are all
**correct**. The only caveats are the scalar-to-operator step on smooth inputs (cost O(H|σ_𝒜′|)) and the tag
[P | CL]. With log X₀ ≥ 10⁸ adopted as canonical, the below-L_* rows are vacuous, and my §10.4 repair is a remark
for smaller X₀ only.

## 12. Targeted review: `fix-Bprime.md` (operator weights via the Kantorovich–Rubinstein norm)

**Verdict.**
- Theorem 1, Corollaries 2–4, Proposition 5, Lemma 6 and (R_H) are **correct** as statements about the kernels
  C_n paired with **functions**.
- The numerics reproduce.
- The BR repair is correct in substance, but (Lip) is false for the canonical target. An oscillation bound
  replaces it, with the same conclusion given (S).
- **The G2-R and (6.1) consumers (§4.9, first item) do not follow as written.** ν is a *measure* controlled only
  on windows of length ≳ H(u) (my point 2b). The bound TV(C_n)·sup|ν| is then unavailable, because the bottom
  jitter box cannot both smooth ν and supply the KR→TV gain.
- **Fix:** give the jitter a Lipschitz density, e.g. triangular U = (U₁ + U₂)/2. Then the KR framework pairs with
  ν exactly as needed (§12.4).

### 12.1 Theorem 1 and Corollaries 2–4: correct

- **Proof of Theorem 1, line by line.**
  - (K1)–(K5) are right. In particular (K2) gives F_{D_wν}(t) = F_ν(wt), so ‖D_wν‖_KR = ‖ν‖_KR/w, and (K3) uses the
    density (F(t+H/2) − F(t−H/2))/H.
  - (4.1)–(4.3) follow from D_{n/d}δ_{x/d} = δ_{x/n} and c_n = −Σκc_d.
  - The induction in step 4 uses the renewal H_ord(m) = Σ_{g|m, g<m}H_ord(g) (m ≥ 2). The e = n term is |c_n|H_n/4. ✓
  - Step 5's (2/H_n)-gain uses the **bottom** box_{H_n} of each chain kernel. See §12.4 for why this matters.
  - The bound holds for any scalar κ ∈ [−1, 1]. Lemma M enters only through |c_e| ≤ 1 and the support.
- **Spot checks.**
  - n = 4: bound ¼, true ¼ (my FFT: 0.2499). ✓
  - n = 6: bound 1.417 ≥ 1.0002. n = 30: bound 2.02 ≥ 1.0002. n = 4p: bound ½(1 + 3/(2p)) ≥ 0.146. ✓
- **Corollary 2.**
  - (e/n)/n = 1/(em²) and H_e/H_{em} ≤ m^ε by (R_H). The block identity Σ_{x/e∈[um,2um)}|c_e|/e = W^sh_x(um) is exact.
- **Corollary 3.** The constants check: A₀(0) = 1/(2−ζ(2)) − 1 = 1.8163 and A₁(0) = −ζ′(2)/(2−ζ(2))² = 7.436. At
  ε = 0.03, 1 + A₀/2 = 2.034 and A₁/2 = 4.70. The (W) constant is independent of x given (S). ✓
- **Corollary 4.** Correct.
  - It is a strict improvement on v2 (3.2). As an ∞-norm bound it still grows like log x, so by F1 it is usable
    only on sources that decay with scale. Examples are σ_𝒜, the near-threshold sources, and BR's terms.
- **(R_H).** log H(vw) − log H(v) ≤ s(16 log L + 5.2) with s = log w/L gives ε ≤ (16 log log X₀ + 5.2)/log X₀
  = 0.0287 at log X₀ = 4915. ✓

### 12.2 Proposition 5 (true, fuzzy operator) and Lemma 6: correct, with one bookkeeping requirement

- **Prop. 5.** Each step checks:
  - agreement off N_n, since 2H_n ≥ R_n;
  - Duhamel, with TV(S_n) ≤ Σ_{d∈N_n}TV(C_d) by (K5);
  - transfers as translates of nominal kernels from start y = x/n′, with landing points y/(d_i/n′) = x/d_i and the
    same widths and filters;
  - the fixed point M ≤ C_N/(1 − C_N E_η).
  - There is no circularity: M is one finite number at fixed x.
  - It needs (S) **at every start y ≤ x**, a uniform Beurling–Saias. That is item (i) of my §9.5.
- **Lemma 6.**
  - Near-threshold w = pm with p t-largest forces P⁺(m) ≤ p + H. So the m-sums are over smooth m, and
    Σ_{P⁺(m)≤4P}log(8mP²)/m ≲ log²P by the LP-Mertens product (gap-localPNT §3.1).
  - E_η ≲ (H(X₀) + K_loc(X₀))log X₀/X₀. ✓
  - θ_* in §4.8 uses only Σ_{m∈(v/4P², v/P²]}1/m ≤ log 4, so it needs no smoothness. ✓
  - **Requirement:** K_loc(P) must be the **per-scale** local-count constant (λ(P) = 3 log P, B(P)), frozen at
    scale P, like NV in my §9.2(a). With §8.3's current-scale λ = 3 log x, E_η ∝ log x and C_N E_η ≤ ½ fails at
    log x ≳ X₀/log X₀.
- **§4.5.**
  - (Q1)–(Q3) for random widths hold, with ∏(1 + θ_u) ≤ exp(2.1H(X₀)/X₀).
  - The exact compensator box(H(x)/m) * jitter is covered with ½ → 1.
  - The X₀-cutoff is terminal.
  - All fine.
- **Numerics, reproduced** (`/tmp/rhscratch/fix-bprime/opfilt2.py`):
  - nominal mode: 0 KR violations at (10⁵, 50, 4, hdiv 48), and in a fresh run (3·10⁵, 30, 6·log², hdiv 12);
  - fuzzy mode (10⁵, 50, 4): W^op/W^sh = 1.04–1.09 per block, Σ TV/n = 5.46 against Σ|c|/n = 5.26.
  - The fuzzy per-n "violations" in the raw output (worst ratio 50 at n = 14941 for 10⁶) are expected. They are
    near-threshold n where c_n = 0 but the fuzzy kernel has mass. Theorem 1 claims only the nominal case, and
    Prop. 5 handles these dyadically. The note's "0 violations" refers to nominal runs, which is correct.

### 12.3 BR (§4.9) and (Lip): (Lip) is false for the canonical target, but BR survives

- **(Lip) fails.** Lip_{[u,3u]}(T′_cont) ≤ C u^{−θ_b}polylog is assumed, but T′_cont = 1 − ρ_det − ρ_𝒜 + R′:
  - Under B-lin, ρ_det(u) = #(𝒟 ∩ [u, u+κu])/(κu) is a box-window moving average of a counting measure. It is a
    **step function**, with jumps 1/(κu) whenever a rigid integer enters or leaves the window.
  - ρ_𝒜(u) = #(𝒜 ∩ [u, u+h])/h has jumps 1/h.
  - So the Lipschitz constant is infinite. "Smoothed at width u^{θ_b}" bounds the oscillation, not the derivative.
- **Replacement (sufficient).** In the KR part, bound
  |∫(T′ − T′(x/n))dD_n| ≤ osc_{[x/n±R_n]}(T′)·TV(D_n), with TV(D_n) ≤ TV(C_n) + |c_n|. The oscillation over a
  window of length 2R ≈ 2H(u) at scale u is the sum of:
  - (2H(u) + 2)/(κu) from ρ_det (unit spacing);
  - 2L(u)^{−4} from ρ_𝒜 (Lemma P: the 𝒜-count in a window of length 2R ≤ h is ≤ hL^{−4});
  - O(γ_kH|R′|/u) from R′.
- With Prop. 5's weights, log x·|KR part| ≲ C_N·Σ_u log(2u)·osc_u ≲ C_N(L_*^{−2} + H(X₀)X₀^{−5/12+o(1)}). This is
  uniform in x. ✓
- **So BR holds as [P | Thm 1, Prop. 5, (S), Lemma 6′, oscillation bound]**, with (Lip) replaced by the
  oscillation bound. The Lipschitz-free route needs (S) through W^op. Fix-Bprime's KR-only version
  (Lip·‖D_n‖_KR, no (S) in the KR part) would need **triangular** moving-average windows in ρ_det and ρ_𝒜. With
  those, Lip ≲ (local count)/window², which is a one-line design change.
- The near-threshold part of BR (Cor. 4 at start y, Lemma 6′) is correct as written. Its source is a function.

### 12.4 My point 2b: pairing the kernels with the measure ν. The G2-R/(6.1) consumers are not covered

**[Superseded by §13.3.]** fix-Bprime §7's function-level identity (7.1) makes ν a window-average function, so the
box jitter suffices. This subsection applies only to the measure-level formulation of A2.1.


- **What §2 and §4.9 assume.** (2.1) bounds Σ_n(1/n)∫g dC_n by Σ_n(1/n)TV(C_n)·ψ*(x/n), with ψ* = sup|g|
  *pointwise*. For G2-R, g = ν.
- **But ν is a measure** (A2.1: ν = μ_dec + 𝒦μ_dec − T′dx, with atoms of mass 1 at decided-prime slots). NV
  controls only window averages ν̄_H(t) = ν(W_t)/H(t) with |W_t| ≳ H. So ψ* is not defined, and TV(C_n)·sup|ν̄| is
  not a valid bound for ∫ν dC_n.
- **Why it really fails with uniform (box) jitter.** Every chain kernel ends with the bottom jitter box:
  C_n = box_{H_n} * C″_n, where C″_n = c_nδ_{x/n} + D″_n and D″_n has no bottom box. Then
  - ∫ν dC_n = c_nν̄(x/n) + ∫ν̄ dD″_n. The bottom box is **spent on ν**, and is no longer available for Theorem 1's
    (K3) gain TV(box * D) ≤ (2/H)‖D‖_KR.
  - ν̄ = box_H * ν is a step function with jumps 1/H at every atom ± H/2. So KR pairing (which needs Lip ν̄) gives
    nothing.
  - Using the local mass |ν|(I) ≤ 3|I| + K and NV on all window lengths, a chain term at width ℓ = H_e e/n costs
    ≈ min(2ε, (3ℓ + 1)/H). That decays only like √(e/n) or worse, and Σ_m H_ord(m)m^{−3/2} diverges, since the
    abscissa is 1.729 > 1.5.
  - Example, n = pq: C″ = −δ + box_a + box_b, so the dual norm of C_{pq} with respect to "sup|ν̄| ≤ ε" is ≈ 3ε
    (realised by a dip of ν̄ at x/n of width ≳ √H), while TV(C_{pq})·ε ≈ ε.
  - So as written the bound is a function-level statement, and the measure-level G2-R is not proved.
- **The fix: a Lipschitz jitter density.** Take the jitter law with density T_H := box_{H/2} * box_{H/2}
  (U = (U₁ + U₂)/2 with independent uniforms). Then:
  - (T_H * ν)′(t) = [ν̄_{H/2}(t + H/4) − ν̄_{H/2}(t − H/4)]/(H/2), so **Lip(T_H * ν) ≤ 4ε_{H/2}/H**, where ε_{H/2} is
    NV on windows of length H/2 (same Freedman, √2 worse).
  - ∫ν dC_n = c_n(T*ν)(x/n) + ∫(T*ν)dD″_n ≤ ε_{H/2}[|c_n| + (4/H_n)‖D″_n‖_KR].
  - ‖D″_n‖_KR obeys the recursion of §4.2 with ‖T − δ‖_KR = H/6, so ‖D″_n‖_KR ≤ (1/6)Σ|c_e|H_e H_ord(n/e)(e/n).
  - Hence |∫ν dC_n| ≤ ε_{H/2}[|c_n| + (2/3)Σ_{e|n,1<e<n}|c_e|(H_e/H_n)H_ord(n/e)(e/n)]. **This is Theorem 1's bound
    with ½ → ⅔**, and it holds for the measure ν.
  - Prop. 5 carries over. The transfers end with the bottom triangle. The un-transferred near-threshold source
    S_n (a cut triangle) costs O(1)·TV(S_n), absorbed by E_η ≪ 1.
  - **Costs elsewhere:** CL's (F2) density 1/H → 2/H, so constants double; the landing lag is still symmetric;
    nothing else uses the jitter shape.
  - (Alternatively, an averaging-over-n argument might rescue box jitter, since for most n no atom lies within
    o(1) of x/n ± H/2. It is not written, and it is more delicate.)
- **Status.** G2-R/(6.1) operator part: [P | Prop. 5, (S), NV at window H/2] **with triangular jitter**. [OPEN] as
  written with uniform jitter. This is the "keep one jitter smoothing" item of my §9.2(b), now made precise: the
  kept smoothing must be Lipschitz.

### 12.5 Summary table

| claim | verdict |
|---|---|
| 1. Thm 1 (KR, nominal), attained at n = 4; M-op false pointwise | **correct** |
| 2. (W) for nominal kernels, C_S(2.04 log 2u + 4.7)/log x, x-uniform | **correct** given (S) |
| 3. True operator: (W) with 2C_N via fixed point plus Lemma 6 | **correct**, given (S) at all starts and **per-scale K_loc** |
| 4. ‖(1+K_op)^{−1}‖_∞ ≤ 2.1(log x + B₁) | **correct** (for functions); usable only on decaying sources (F1) |
| 5. BR uniform in x via KR | **(Lip) false** for box-window moving averages. **BR still holds** via the oscillation bound and (S), or with triangular moving-average windows |
| 6. ν a measure, controlled at scale ≥ H(u) | **not handled.** With box jitter the bound fails as a proof; **fix: triangular jitter**, giving the bound with ½ → ⅔ and NV at H/2 |
| 7. Numerics | **reproduced**: 0 nominal violations, including a fresh run; fuzzy ratios 1.04–1.09 |

**Net.** fix-Bprime's kernel theory is right and is the correct replacement for B′-op. To close the operator branch
(ii) of (SW) for G2-R, adopt Lipschitz (triangular) jitter, and state NV per scale at window H/2. For BR, replace
(Lip) by the oscillation bound. Then the remaining inputs are (S) for the realised semigroup and per-scale NV with
the S1 truncation, which the canonical absorption has already disposed of above L_*.

## 13. Targeted review: `fix-Bprime.md` §7 (exact identity ρ̃ + BK_ptρ̃ = F; push-through)

**Verdict.**
- §7 is **correct**, and it **does satisfy my point 2b with the uniform (box) jitter**. My §12.4 triangular-jitter
  fix is **not needed** under §7's formulation. It was needed only for the measure-level formulation (A2.1),
  which §7 supersedes.
- The push-through identity and Lemma S are right, and the numerics reproduce. The flag against gap-localpnt is
  right.
- One genuine gap remains:
  - (7.1) controls the compensator margin only on **H-windows**, but Thm 4.2′'s Freedman blocks have L⁵ ≪ H slots.
  - So R1′ needs the *pointwise* margin T′ − K_ptρ̃, i.e. smallness of (1 − B)K_ptρ̃. That is the same term
    fix-bprime flags for gap-localpnt.
  - It follows from (7.3) at lower scales plus R(δ), but it is not written (§13.4).

### 13.1 (7.1): correct, and it is the exact form of my G2

- ρ̃ := Jσ (the landing density: a box of width H(s_q) per decided prime) is a **function**. The compensator of W_y
  equals Σ_w Σ_{q eligible}|J_q ∩ W_y/w|/H(s_q). Using ∫_{W_y/w}g = (1/w)∫_{W_y}g(·/w), this is
  H(y)·(BK_ptρ̃)(y) + H(y)·NT(y).
  - NT replaces the slot filter s_q > τ_w by the landing filter y/w > τ_w, so it is supported on near-threshold w. ✓
- Bookkeeping in W_y then gives ρ̃ + BK_ptρ̃ = T̃′ − ν − NT **at every y**, up to |ρ̃ − σ(W_y)/H| ≤ 2/H, which is
  included in θ/H.
  - Here ν(y) := (Mart(W_y) − ΔQ(W_y))/H(y) is the window-average **function**.
  - This is the "B outside K" structure that my G2 diagnosed (A_xK ≠ KA). §7 makes it exact.
- *Cosmetic.* In §7.4 the last term should read (1 − B)BT′ + (1 − B)θ/H, not (1 − B)(T′ + θ/H). Both are
  O(osc_H T′ + 2/H).

### 13.2 (7.2)–(7.3): correct

- Expanding (1+BK)[(1−B) + B𝓡(1 − K + KB)] with (1+BK)B𝓡 = B gives exactly 1. Volterra in scale gives the two-sided
  inverse. ✓
- ρ̃ = (1 − B)F + B𝓡F − B𝓡G, with G = K_pt(1 − B)F. ✓
- **𝓡 = (1 + K_ptB)^{−1}.** Each step averages at the landing scale, then pulls up pointwise.
  - So its chain kernels are exactly §1.1's, with box_{H_n} at **every landing level including the bottom**.
  - Theorem 1 applies (nominal), and Prop. 5 applies (the true filter, evaluated at fuzzy positions within R). ✓
- By contrast (1 + BK_pt)^{−1} has its boxes at the *output* scales and none at the bottom. Its kernels are of C″
  type, with TV ~ the number of chains. That is why the push-through is essential, not cosmetic.

### 13.3 The key question (2b with box jitter): only H(u)-window averages of ν are used

- **𝓡F and B𝓡F.** (𝓡F)(x) = Σ_n(1/n)∫F dC_n^x, with C_n^x a measure (box_{H_n} at the bottom) and F a bounded
  **function**: F ∋ −ν(·), the window-average function.
  - |∫ν dC_n| ≤ TV(C_n)·sup_{|t−x/n|≤R_n}|ν(t)| is legitimate.
  - The bottom box is used by Theorem 1's (K3) on the kernel's D-part. It is **not** needed to make ν bounded,
    because ν(t) is already the H(t)-window average.
  - That is the whole difference from my §12.4, where ν was the measure of A2.1 and the bottom box was
    double-booked.
- **B𝓡G.**
  - (1 − B)F needs only |(1 − B)ν| ≤ 2 sup|ν| (window averages again) and osc_{H}(T′) (deterministic).
  - K_pt is pointwise on the bounded function (1 − B)F. Then 𝓡 again uses TV·sup.
- **What is required of ν.** sup_t|ν(t)| over *all* real t at each scale, i.e. H(t)-window averages at every
  position, not just on a net.
  - Since ν(t ± 1) − ν(t) ≤ (2 + #elements in two unit edges)/H ≤ (2 + 2M₁L⁶)/H on E_cl, a 1-net plus E_cl
    suffices. No Lipschitz test functions and no sub-H windows are needed. NV per scale, as already required
    (§9.2(a)), suffices.
- **Conclusion.** None of 𝓡F, B𝓡F, B𝓡G tests ν against Lipschitz functions. Only box windows of length H(u) at
  scale u (NV) are used. The box jitter is fine, and I withdraw §12.4's "triangular jitter needed". §12.4 remains
  correct for the measure-level formulation, which should no longer be used.

### 13.4 Assembly (§7.4) and the remaining gap: R1′ on windows shorter than H

- **The H-window margin is correct.** T̃′ − BK_ptρ̃ = ρ̃ + ν + NT
  = B𝓡T′ + B𝓡F_r − B𝓡G + Bν + B·NT + (1 − B)(…).
  - B𝓡T′ ≥ (0.33 − o(1))/log x via BR (in its oscillation form, my §12.3) and G1′.
  - The other terms are Saias-weighted sums over scales with no x-dependence. ✓
- **The gap.** R1′ is needed for slot windows of ≤ L₀ = L⁵ slots (Thm 4.2′ step 4 and the full blocks), and
  L⁵ ≪ H = exp(8ℓ²).
  - On such W the compensator is ∫_W K_ptρ̃ (pointwise density), so the margin is
    ∫_W(T′ − BK_ptρ̃) − ∫_W(1 − B)K_ptρ̃.
  - §7 controls only the first. The trivial bound on the second is O(1/log x): w = 2, 3 give
    Σ_w(1/w)·osc_{H/w}ρ̃ ≈ Σ_w 2/(w² log x) ≈ 1.3/log x, against c′/log x = 0.15/log x. That is not enough.
- **Repair (available, not written).** Apply (7.3) at the cofactor scales z = x/w:
  - ρ̃(z) = (1 − B)F(z) + [B𝓡(F − G)](z).
  - The bracket is an H(z)-average of 𝓡T′ + small, and its oscillation over H(x)/w is controlled by R(δ)
    (threshold jumps of ρ^sh at δ = H/u) plus the smallness of 𝓡F_r and 𝓡G.
  - The first term gives K_pt(1 − B)F, which is **exactly a G-type term**, bounded by Lemma S.
  - Hence (1 − B)K_ptρ̃ = O(Lemma-S sum + R(δ)-jumps) = o(1/log x), and R1′ holds on all windows.
  - **Alternative:** take Freedman blocks ≥ H·L. The drift then only needs H-windows, but the queue becomes
    ~ H·sup|(1 − B)K_ptρ̃| ≈ √(Hλ)·polylog. That is acceptable for (L-a) in x^η form and in NV (B/H ≈ H^{−1/2}), but
    it is no longer polylog. I prefer the first route.
- **Lemma P's strength.** In F_r^+, the term H·osc(T′) contains ρ_𝒜's oscillation. With Lemma P's bare 2L^{−4},
  the (log 3v)^{2+e}-weighted sum is Σ_{L≥L_*}L^{e−2}·L^{−2} ≈ L_*^{−0.28}/0.28 ≈ 0.04, times 6C_N C_S′. That is
  not obviously ≪ 0.33. Use Lemma P's actual margin: (12.2) has 3019 versus 2370 at L_*, i.e. a factor
  ≤ e^{−600}, growing with L. Then the term is negligible. State this.

### 13.5 Lemma S, the convergence threshold, the gap-localpnt flag, and numerics

- **Lemma S: correct.**
  - (i) ω ≤ 1.2 per dyadic block.
  - (ii) For y ≥ 4v², τ_w < 2v forces P⁺(w) ≤ 3v. Rankin with σ = 1 − 1/log 3v gives
    ∏(1 − p^{−σ})^{−1} ≤ C(log 3v)^e, so ω ≤ C(log 3v)^e e^{−log(y/2v)/log 3v}.
  - The dyadic swap gives Σ_y log(2y)ω_y(v) ≤ 3.5(log 3v)² + C(log 3v)^{2+e}. ✓
- **The threshold H ≥ (log v)^{8.5+2e+δ}** comes from (log v)^{2+e}·√(M₁λ/H) summed over dyadic v. ✓ That means
  ≥ (log v)^{14} for polylog H. H = exp(8ℓ²) is far beyond this.
- **gap-localpnt flag: agree.** (7.1) gives (1 + K_pt)ρ̃ = F + (1 − B)K_ptρ̃. The extra term involves the response,
  and its a priori bound is ≈ 1.3/log x (13.4), comparable to the margin. So e = −Σμχν(x/n)/n is not justified.
  (7.3) is the correct replacement. It is the same term as in my 13.4 gap, where it is needed *pointwise* for R1′.
- **Numerics reproduced** (`omega.py`, Y = 3·10⁶):
  - ω_y(v) decays Dickman-like in U = log(y/v)/log v − 1: e.g. 0.001, 0.010, 0.041, 0.115 at v = 2³…2⁶ for
    y = 3·10⁶, and ≈ 0.5–0.7 for v ≥ √y.
  - The truncated sums Σ_y log(2y)ω_y(v) are 22.2, 48.7, 75.3, 86.3 at v = 8, 32, 128, 512, i.e. 2.9, 2.8, 2.45,
    1.8 × (log 2v)². The last ratio is truncation-limited. ✓

**Net.** With §7, branch (ii-b) closes **with the box jitter**. Two items remain to be written:
1. the short-window (pointwise) margin of 13.4, via (7.3) at cofactor scales plus R(δ);
2. Lemma P's actual margin in the ρ_𝒜 oscillation.

Also replace (Lip) by its oscillation form throughout, as §7.4 already does. Then the operator-weight part of (SW)
reduces to (S) for the realised semigroup, per-scale NV, Lemma 6 and Lemma S.

## 14. Targeted review: `fix-Bprime.md` §9 (Prop. 9: pointwise margin; ρ_𝒜 oscillation)

**Verdict.**
- Prop. 9 is **correct** and closes my §13.4 gap (R1′ on windows shorter than H). It does so by a cleaner route
  than mine, with no R(δ) and no operator kernels.
- §9.4's local-count bound for the ρ_𝒜 oscillation is correct and disposes of my §13.4 Lemma-P point.
- There is no circularity.
- Two bookkeeping points, below, do not affect the conclusion.

### 14.1 Step 1 (bookkeeping on any window) and Step 2 (the key step): legitimate

- **Step 1.** On any slot window I:
  - primes(I) = slots(I) − arrivals(I) + ΔQ(I);
  - arrivals = Comp + Mart, with Comp(I) = Σ_w∫_{I/w}JΠσ = ∫_I(K_ptρ̃ + NT_pt), via ∫_{I/w}g = (1/w)∫_I g(·/w).
  - So σ(I) = ∫_I m + E(I), with |E| ≤ 3 + |Mart(I)| + |ΔQ(I)|. ✓ The identity is (7.1) without the B-average,
    and it holds for every length.
- **Step 2 (the lead's question: is it legitimate given that ρ̃ is a smoothed landing density and m a margin
  density?). Yes.**
  - ρ̃ = Jσ equals σ(W_z)/H(z) up to ≤ 2/H, because a box of width H(s_q) at each decided slot, evaluated at z,
    counts the slots in W_z. The H(s_q) versus H(z) edge effect is in the "3".
  - So ρ̃'s increment over a sub-H shift s is (σ(I₊) − σ(I₋))/H for the two strips at the window ends, and these
    are exactly H(z) apart.
  - Step 1 turns each strip count into ∫m + E. The difference is ∫_0^s[m(t + H) − m(t)]dr ≤ s·V(z), plus 2ε_s.
  - The landing density is never differentiated as a smooth object; only decided-prime counts on strips are used.
    And the H-shift in V is the right object, because the two strips are separated by the window length itself.
- **The extended per-scale event (λ′ = λ + log H)** is the same Freedman over ≤ 2uH windows, with increments ≤ 2M₁
  on E_cl(u). ✓
  - Strips with non-grid endpoints: σ and Mart change by ≤ (elements in a unit edge) ≤ 2M₁L⁶ on E_cl, which is
    absorbed into the "3"-type term after /H.

### 14.2 Step 3 (recursion): closes, and is non-circular

- **Compression.** A shift h ≤ 1.01H(y) at scale y becomes h/w at scale y/w. That is a fraction
  (h/w)/H(y/w) ≤ 1.01w^{ε−1} of the local window, by (R_H). Step 2 is linear in s/H, so the lower scale contributes
  1.01κ_w w^{ε−2}·V(y/w).
  - Σ_w 1.01w^{ε−2} ≈ ζ(2−ε) − 1 ≈ 0.69 < 1, so this is a genuine contraction.
  - Chain weights are ≤ 1.01^{Ω(M)}H_ord(M)M^{ε−2} ≤ H_ord(M)M^{ε′−2}, with 1.01^{Ω} ≤ M^{0.0144}. This is summable
    since 2 − ε′ = 1.955 > ρ = 1.7286.
  - Step 5's split at √y: A₀(0.045) = 2.218 (I get 2.215), giving 2(1 + A₀) = 6.44. The tail is
    ≤ 5.32y^{−0.0525}E_S/log X₀. ✓
- **Non-circularity (the lead's question).** Write the recursion pointwise, as v(t) := sup_{|h|≤1.01H(t)}|m(t+h) − m(t)|.
  - v(t) depends on v at points ≤ t/2 + 2H < t, on noise events at scales ≤ t/2, and on the deterministic T′.
  - The base case is t < 2X₀, where m = T′. So it is a well-founded induction on scale. ✓
- **Bookkeeping (a).** V(y) is defined as a sup over [y/2, 2y]. The recursion from t ∈ [y/2, 2y] calls points in
  [y/(2w) − 2H, 2y/w + 2H], which is slightly outside [y/(2w), 2y/w]. Use the pointwise form above, or
  V*(y) := sup_{[y/4,4y]}. This is cosmetic, since the solution E_S/log y is monotone.
- **Bookkeeping (b).** Step 4 uses "log y·2η(y) ≤ 2θ_*". As θ_* is bounded in §4.8 (Σ_m 1/m ≤ log 4, no smoothness),
  η(y) is uniformly ≈ H(X₀)/X₀, and log y·η(y) would grow with y.
  - The inequality is true only because near-threshold cofactors w = pm have P⁺(m) ≤ p + H. Then
    Σ_{m∈(y/4P², y/P²], P⁺(m)≤4P}1/m ≈ ρ(log(y/P²)/log 4P) is Dickman-small for y ≫ P^{O(1)}, and
    log y·η(y) ≤ C·Σ_P(H(P) + K_loc)log P/P, which is the Lemma 6 sum.
  - Cite Lemma 6's smooth-m argument here, not §4.8's θ_*.
  - Moreover the filter switches under a shift h only for τ_w ∈ (y/w, (y+h)/w], a set of width h/w, much narrower
    than the near-threshold width 2H(p). So 2η is an overestimate. Fine.

### 14.3 Step 4 (S(y) ≤ E_S/log y) and §9.3 numbers

- The noise term ε_{H(y)/w}(y/w)/H(y/w) ≤ ν̂(y/w)(w^{(ε−1)/2} + 1) uses √(4M₁λ′(s+2))/H with s ≤ Hw^{ε−1}. ✓
- The Lemma S weights apply: ω ≤ 1.2 with log y ≤ 2 log 2v′ for v′ ≥ √y/2, and log y·ω_y(v′) ≤ C′(log 3v′)^{1+e}
  below that. That is (log)^{1+e}, one power less than §7.4's B𝓡G sum, since here there is no outer Saias weight. ✓
- **Canonical numbers.** I checked the leading term: at v = X₀ with log X₀ = 10⁸, H(X₀) = e^{2714}, so
  √(4M₁λ′/H) ≈ e^{18.3−1357}, and log(2v)·(…) ≈ e^{−1320}. That is consistent with e^{−1306.7} for the dyadic sum.
  (log 3v)^{1+e}·ν̂ ≈ e^{68.5−1339}, consistent with e^{−1256.6}.
- So E_S ≤ e^{−1250}, and 6.5E_S is negligible. **m ≥ (0.33 − o(1))/log y pointwise, and R1′ holds on every slot
  window with K_d = O(1)**, independent of L₀ and of M₁ ≤ H^{1/2}. ✓

### 14.4 §9.4 (ρ_𝒜 oscillation): correct

- (a) A shift by t changes #(𝒜 ∩ [u, u+h]) by at most the counts in two strips of length t, and 𝒜 ⊂ 𝒩 gives
  N(strip) ≤ 3t + K_loc (per-scale §8.3). So osc_t ρ_𝒜 ≤ 2(3t + K_loc)/u^{θ/2} ≤ e^{−1.25·10⁶+3000} at L ≥ 10⁷. ✓
  This needs neither Lemma P nor (12.2)'s margin.
- (b) Lemma P with Δ(L) = LHS − RHS of (12.2) ≥ 649 at L_* is also right. It is the alternative I suggested.

### 14.5 Net

- Branch (ii-b) is now complete modulo:
  - (S) (Beurling–Saias at all starts);
  - per-scale NV and the extended short-window Freedman event (λ′ = λ + log H, included in G_{<y} and in the
    budget);
  - per-scale B(u) and K_loc;
  - Lemma 6 (with the smooth-m point of 14.2(b)) and Lemma S.
- The operator-weight branch of (SW), BR (in its oscillation form) and R1′ on all windows are closed under these
  inputs.
- My §13.4 "alternative" (blocks ≥ HL) and my R(δ)-based repair are not needed.

## 15. Targeted review: gap-G3 §11.7–11.10 (Deficit/Capacity reductions) and §16 (M₁ tolerance, CapL-w, the lever)

**Verdict.**
- The reductions of §11.7–11.9 are **correct**: extras, summable failure, the Covering Lemma, and the peeling formula.
  One caveat on "≤ 1 integer per exponent vector" is in 15.2.
- DL's withdrawal is right.
- §16.1's tolerance (M₁ ≤ H^{1/2}) is **correct**. Two intermediate thresholds are mis-stated, but are harmless at
  H^{1/2}.
- CapL-w (§16.2) is the right target, essentially the weakest one.
- **§16.5's lever is NOT admissible as decoupled.** The decoupled absorption threshold still scales with M₁ through
  L₀. Once that threshold exceeds X₀ (L ≈ 6·10¹⁴), Lemma P fails. That is most of the middle range on a log scale.

### 15.1 §16.1 tolerance, checked against Prop. 9 and fix-Bprime §7–9

- **Block step.** With L₀ ≥ 48M₁L³/c′², √(12M₁LL₀) ≤ c′L₀/(2L). The other half of the drift, ≥ 160M₁L², beats
  4M₁L + 0.55M₁L²/log L.
  - B = max_ℓ(−c′ℓ/L + √(12M₁Lℓ)) + … = 20M₁L² + O(M₁L), so ≈ 21M₁L². ✓ The maximiser 3M₁L³/c′² is ≤ L₀. κ = C + 2
    for M₁ = L^C. ✓
- **E_cl.** δ₁ = 2L^{−6} is unchanged since q ≥ q_min = L₀L⁶. The absorption threshold y ≥ q_min ✓, and
  |W_H/q| ≤ 1/(L₀L⁶) on H-windows. ✓
- **(SW): mis-stated, harmless.**
  - "M₁ ≤ H/L⁸" is enough only for a log u-weighted sum. The binding sums are now fix-Bprime §7.4's
    Σ_v(log 3v)^{2+e}ν̂(v) (the B𝓡G term) and Prop. 9's Σ(log 3v)^{1+e}ν̂.
  - With ν̂ ≥ √(4M₁λ/H), these need M₁ ≤ H·L^{−(2(3+e)+1)−δ} ≈ H/L^{13.5}.
  - H^{1/2} satisfies this with vast room. Correct the stated threshold.
- **G2R crude form** (10⁶M₁L⁷ ≤ H): obsolete since the Saias weighting, and implied anyway.
- **Lemma P threshold: mis-stated, harmless.** Redo (12.2) with log 2y ≈ log H + log M₁ + 9 log L and
  log C_d ≈ log M₁ + 7 log L, at θ = ¼:
  - for M₁ ≤ H it needs L ≳ 5·10⁷ (at 2·10⁷: LHS 3145 < RHS ≈ 7100);
  - for M₁ = H^{1/2} it needs L ≳ 2.5·10⁷.
  - Both lie inside L ≥ log X₀ ≥ 10⁸, and 𝒜 ≠ ∅ only from L ≈ e^{2.9·10³}. ✓
- **K_loc ∝ B ∝ M₁ downstream.**
  - The only uses that would mind are K_loc/√H terms. R(δ) at δ = H/u had one, but it is no longer used (fix-Bprime
    replaced it).
  - §9.4(a) (2K_loc/u^{θ/2}), Lemma 6 (K_loc(X₀)/X₀) and Prop. 9 (B/H inside ν̂ ≈ H^{−1/2}L²) all survive
    M₁ = H^{1/2}. ✓
- **Prop. 9 and §7.3** are insensitive to L₀ and M₁ ≤ H^{1/2} (fix-Bprime §9.3). ✓
- **Net:** "any M₁(z) ≤ H(z)^{1/2} works" is **correct**. The two thresholds above should be corrected.

### 15.2 §11.7–11.10: the reductions

- **Step 1 ("extras are free").** The reduction N(J) ≥ k ⇒ ∃ rank-full B with Cap(B) ≥ k − r is definitional, hence
  ✓. Since e_x = Σα_ie_i, the jittered part of x is Π_i(n_i/d_i)^{α_i}, so d_x lies in an interval of length
  ≤ 2(‖α‖₁+1)δ.
  - **[Retracted in §16.3.]** I first raised a caveat that "≤ 1 integer" needs ‖α‖₁ small. That is wrong. Given the
    exponent vector e, the jittered part Q_e ≥ X₀ is fixed, so d ∈ J/Q_e, an interval of length δ/Q_e < 1. Distinct
    elements of J therefore have distinct exponent vectors, whatever α is.
- **Step 2 (summable failure).** Correct. Per height ≤ L_z^{−4} gives ≤ L^{−3} per dyadic x, and Σ_m(log 2^mX₀)^{−3} is
  ≪ ½, compatible with §0.3's first-failure budget.
- **Covering Lemma.** Correct; I checked both cases.
  - I₋ ≠ ∅: nonnegativity gives supp(e_y) ∪ ∪_{I₋}supp(e_i) ⊂ ∪_{I₊}supp(e_i).
  - I₋ = ∅: supp(e_y) = ∪_{I₊}supp(e_i) for a positive combination, with |I₊| ≥ 2.
  - Each cover vector has mass ≤ log 2z.
  - The proportional case is correctly carved out.
- **Exact peeling formula (§11.9).** Correct as a sketch.
  - The q-volume of the payers' pinned region is ε^r Πq̂/|det E_P| with |det| ≥ 1.
  - Πq̂ = exp(1ᵀE_P^{−1}(log z₀1 − t − E_Nx_N)) = z₀^{σ₀}Πd_i^{−γ_i}Πq_ℓ^{−β_ℓ}.
  - My recomputations:
    - grid basis: γ = (0, 1, 1), σ₀ = 2, β_{q₁} = 1 ✓;
    - hypercube: γ = (2−t, 1, …, 1), σ₀ = 2, β = 1 on the t − 1 free q_{j,0} ✓;
    - simplex: γ₁ = (1 − (D′−1)(s−1))/D′, σ₀ = s/D′ ✓.
  - "Tails open free directions" (γ_i ≤ 0) is a genuine observation. The amendment (apply CapL to basis plus extras'
    relations) is right.
- **DL withdrawal: agree.**
  - The pinning budget (r tails + 1 window + #free prime sums) bounds the number of available decay factors
    independently of Cap.
  - The hypercube t = 5 has budget 6 + 1 + 4 = 11 < 26 extras.
  - §11.10's "M₁ = r₀ + 1 is wrong" is also right: rank-2 tail extras are abundant at large z.
  - The 24δτ/X₀² tail-extra weight: not checked (fix-smooth's numerics).
- **Note: CL's §11.1 display is still false as stated** (§11.5 grids, my §11.5(c)). The canonical form is "rank-full
  [P] + rank-deficient via CapL".

### 15.3 §16.2 CapL-w: the right target, with two corrections

- **Logic.** With M₁ := r₀ + H^{1/2}, N(J) > M₁ forces either rank ≥ r₀ (rank-full CL) or a rank-r basis with
  Cap ≥ H^{1/2}. So CapL-w is exactly E_cl's requirement. ✓
- **The deterministic cap bound.** Cap ≤ (2D+1)^{r−1} is not justified: the window constraint involves log d_y, so it
  is not a linear slice of the exponent lattice.
  - What holds: project the rank-r lattice injectively onto r coordinates with |coord| ≤ D. That gives ≤ (2D+1)^r
    vectors, times the per-vector multiplicity of 15.2.
  - So r₁ = 4 log²L/log(3D) up to O(1), **if** ‖α‖₁δ ≪ 1 for the vectors involved. Otherwise the low-rank exclusion
    needs a separate argument. That is a small gap: either bound ‖α‖₁ for exponent vectors of degree ≤ D, or count
    elements directly.
- **Weakest form.** The tolerance is set by M₁ ≤ H_std·L^{−15} (SW/NV), not by H^{1/2}. Lemma P alone would allow
  log M₁ ≲ 0.19√(L log L) (15.5). So the threshold could be H/L^{15}, which roughly doubles r₁. H^{1/2} is within a
  factor 2 of optimal in r₁. ✓

### 15.4 §16.3–16.4: diagnosis and family checks

- **Middle range: confirmed numerically.** r₁ log X₀ ≥ L, i.e. 4 log²L·log X₀/log(3D) ≥ L (log X₀ = 10⁸):
  - L = 10¹⁰: 3.7·10¹⁰ ≥ 10¹⁰ ✓;
  - L = 10¹¹: 3.2·10¹⁰ < 10¹¹ ✗.
  - Lemma R's saving b − 1/log L > 0 needs log L > √(log X₀) = 10⁴, and a usable saving needs ≈ 1.5–2·10⁴.
  - So counting with cheap gains fails on L ∈ [≈5·10¹⁰, ≈e^{1.5·10⁴}]. ✓
- **Family checks: correct.**
  - Hypercube: per height ≲ 2δ^t z^{2−t}(log L)^{t−1}. Note that γ₀ = 2 − t < 0 means nontrivial tails on v₀ would be
    summed with a positive power. The check used trivial tails, and it should state that tails need the extras'
    relations (§11.9 amendment).
  - Simplex: z^{1−s(1−1/D′)}.
  - Equal-tail and powers-of-2 families.
- **The dichotomy** ((i) a z-type pin; (ii) ≥ H^{1/4} independent smoothness costs) is a conjecture. Its deterministic
  half (exact structure ⇒ pin) is the real content. (ii)'s independence is unproved; the powers-of-2 example shows
  correlations exist and are exactly the structured case.

### 15.5 §16.5 the raised-H lever: not admissible as decoupled (SERIOUS for the lever; confidence high)

- **What the decoupling misses.** The point of raising H is to raise the CapL-w threshold, i.e. M₁ = r₀ + H_raised^{1/2}.
  - By §16.1 that forces L₀ = 48M₁L³/c′² ∝ H_raised^{1/2}, and q_min = L₀L⁶. These are forced by the block step and by
    E_cl's coverage |W/q| ≤ L^{−6}.
  - So the "standard" threshold y_std = H_std·L₀·L⁶ is ≈ x^{c/2}·polylog, not standard.
  - Lemma P at such y has u₀ = θ_bL/log y ≈ 1/(4c), fixed, against log 2y + log C_d ≈ cL, which grows. Its (12.2)
    analogue is 0.9u₀ log u₀ ≥ cL.
  - **But Lemma P matters only where 𝒜 ≠ ∅, i.e. y > X₀.** Under the lever log y ≈ cL/2, which first exceeds
    log X₀ = 10⁸ at L ≈ 6·10¹⁴. Below that, 𝒜 = ∅, S2's small-q term is vacuous, and nothing fails.
  - From L ≈ 6·10¹⁴ on, (12.2) fails badly: at L = 10¹⁵, LHS ≈ 8.9·10⁶ against RHS ≈ cL = 3.4·10⁸. It keeps failing up
    to the switch-off at log L ≈ 1.5·10⁴.
  - Lowering y below q_min returns S2's rigid-run problem: q ∈ [y, q_min) with |W/q| > L^{−6} gives increments
    ∝ M₁L₀/y, so Freedman needs y ≫ M₁λL/c′.
- **No raise of H helps beyond ≈ 5·10¹⁴.** There are two regimes.
  - While H_raised^{1/2} ≲ X₀/polylog, y stays below X₀, so 𝒜 = ∅ and no Lemma P is needed. But then
    r₁ log X₀ ≤ log²X₀/log(3D), so counting works only for L ≲ 10¹⁶/log(3D) ≈ 5·10¹⁴.
  - Beyond that, 𝒜 ≠ ∅, and Lemma P tolerates only log H ≲ 0.38√(L log L). (From 0.9(L/(12 log H))log(…) ≥ 2 log H
    with M₁ = H^{1/2}.) Counting would need log H ≥ 2L log(3D)/log X₀, which is impossible for L ≳ 3·10¹³.
  - So the lever can extend the counting-sufficient range from ≈ 5·10¹⁰ to ≈ 5·10¹⁴ at most, by keeping 𝒜 empty. The
    structural lemma (§16.3/16.4) is needed on [≈5·10¹⁴, e^{1.5·10⁴}] **regardless of H**.
  - (gap-g3's own verdict already says the lever does not remove the structural lemma. This sharpens it: the lever
    does not even remove the counting gap.)
- **(R_H) across the switch.**
  - On the x^c plateau, H(vw)/H(v) = w^{c(vw)}v^{c(vw)−c(v)} ≤ w^{c+2/log X₀}. ✓ (c(vw) − c(v) ≤ (2/log X₀)·log w/log 2v.)
  - **Switch-on:** (R_H) is a bound on the log-slope, d log H/d log v ≤ ε. At L = 10¹¹, log H must rise from
    8 log²L ≈ 5.1·10³ to cL ≈ 1.6·10⁴. A "smooth bump" works only if its ramp has slope ≤ ε, i.e. length
    ΔL ≥ 1.1·10⁴/ε (≈ 3.7·10⁵ for ε = 0.03; ε < 0.27 is all that summability, 2 − ε > 1.7286, needs). Trivial to
    arrange, but it must be stated: an abrupt switch-on violates (R_H) by a factor e^{10⁴}.
  - **Switch-off:** a decrease of H is harmless for (R_H), which only bounds growth. The other uses (H(v)/v
    decreasing; H(x)/m ≤ H(x/m)) also survive a decrease. ✓
- **Other constraints.**
  - The lag needs c_max < η. For θ near ½ that forces log X₀ ≥ 2 log(3D_max)/η, a θ-dependent X₀, which is fine.
  - The NV middle q via my §10.4 repair (Rankin at x^c-smoothness, ρ(1/c) tiny) is correct.
  - The rigid part √(λ/X₀) per scale: its (SW) sum with the binding weights (log)^{4.72} is ≲ e^{9·10⁴}/√X₀, still
    negligible.

**Net for the G3 side.**
- §16.1 holds: any M₁ ≤ H^{1/2} is tolerated, with κ = C + 2.
- E_cl reduces to **CapL-w**, which is open. It needs the structural dichotomy on all of L ∈ [≈5·10¹⁰, e^{1.5·10⁴}],
  and the lever (with 𝒜 kept empty) cannot shrink this below [≈5·10¹⁴, …].
- Small gaps to close in passing:
  - the per-vector multiplicity (‖α‖₁) in Step 1 and the (2D+1)^r cap bound;
  - the thresholds in 15.1.

## 16. Targeted review: the Thin-Cover Lemma (gap-G3 §16.7–16.8)

**Verdict.**
- **TCL is correct.** I checked Steps 1–5 line by line and found no gap. The bound 3r(8D+4) holds and is tight up to
  the constant: a star of segments gives Cap = (r−1)(D−1).
- TCL counts **exponent vectors, which equal elements** in J (16.3), so my §15 multiplicity caveat is moot. I have
  retracted it there.
- The **Σα = 1 input** is not automatic. It needs a two-branch reduction (16.4), which is available but should be
  written.
- Brute force (`/tmp/rhscratch/referee-b/tcl.py`, 3 seeds): **278 configurations with κ = r−1, 0 violations** of rule
  G, |I(y)| ≤ 3, #supports ≤ 3r or Cap ≤ 3r(8D+4). The maximum Cap/(r(D+1)) found was 0.48.

### 16.1 Steps 1–3: correct

- **Step 1 (rule G).** S ⊂ aff(B) gives Σα = 1, so no extra is proportional (|I₊| = 1 would force y = e_i). The
  Covering Lemma's covers have sizes r − |I₋| and 1 + r − |I₊|. So κ = r − 1 forces |I₋| ≤ 1, and, when I₋ = ∅,
  |I₊| = 2. P(S) = P(B), since every extra's support lies in ∪_{I₊}supp(e_i). ✓
- **T1/T2.**
  - T1 is a point strictly inside a segment [e_i, e_j], with supp = supp_i ∪ supp_j.
  - T2 has I₋ = {l}.
  - Two T1 extras on disjoint segments give the cover {y₁, y₂} ∪ (B ∖ {i,j,k,l}) of size r − 2. So T1 segments pairwise
    meet (a star or a triangle). ✓
- **Step 2 (|I(y)| ≤ 3).** For i ∈ I₊(y), B* = B − e_i + y is a basis, and e_i = (e_y − Σ_{j≠i}α_je_j)/α_i. Relative to
  B*, the negative set of e_i is I₊(y)∖{i} and its positive set is {y} ∪ I₋(y). Rule G for (B*, e_i) gives
  |I₊(y)| ≤ 2. The only patterns are (|I₊|, |I₋|) ∈ {(2,0), (2,1), (1,1)}, and (1,1) is consistent: the exchange
  gives I₋ = ∅, |I₊| = 2. ✓
- **Step 3 (exchange).** With I(y) ∩ I(y′) = {h} and B′ = B − e_h + y, substituting for e_h gives coefficients:
  - −α′_hα_j/α_h ≠ 0 on I(y)∖h, since α′_j = 0 there;
  - α′_j ≠ 0 on I(y′)∖h, since α_j = 0 there;
  - α′_h/α_h ≠ 0 on y.
  So nothing cancels, |I_{B′}(y′)| = |I| + |I′| − 1 ≤ 3, and |I| = |I′| = 2. ✓
  - The P4 exclusion is also valid. After e₂ ↔ y₁₂, y₂₃'s set becomes {1, 3, y₁₂}, which meets y₃₄'s unchanged {3, 4} in
    exactly {3}. ✓

### 16.2 Steps 4–5 and the bound: correct

- **Components.**
  - Pair-only components are connected graphs with no 3-edge path: stars or triangles. (A triangle plus a pendant edge
    has such a path.)
  - A triple meets every other support in 0 or 2 points (Step 3). So a pair touching a triple lies inside it, and a pair
    meeting it in one point is excluded. That also excludes stars hanging off triples.
  - Triples in one component pairwise meet in exactly 2 points. If T₁ ∩ T₃ were a single point via a chain, Step 3 is
    violated.
  - Families of 3-sets with pairwise intersections of size exactly 2 are a 2-kernel sunflower or lie inside a 4-set
    (standard).
  - In the book, the only addable pair is the kernel {i,j}: {i, l_t} meets {i, j, l_s} in one point.
  - Counts: star v−1, triangle 3, book t+1 on t+2 vertices, 4-set ≤ 6+4 = 10 ≤ 12. All are ≤ 3v_c. Components are
    vertex-disjoint, so #supports ≤ 3r. ✓
- **Points per support.**
  - A line in the degree-≤D box holds ≤ D+1 lattice points.
  - In a plane, S is in weakly convex position. A point strictly inside a triangle of S, with the triangle extended to a
    basis (affinely independent ⇒ linearly independent, since 0 ∉ aff), has I₋ = ∅ and |I₊| = 3, violating rule G.
  - An injective projection to two coordinates lands in ℤ² ∩ [0,D]². Four chains, each monotone in both coordinates,
    give ≤ 4(2D+1) points. ✓
- **Hypotheses actually used.** Only S ⊂ aff(B) (0 ∉ aff), integrality, nonnegativity and degree ≤ D. **w > 0 is never
  used**, which matters for 16.4.
- **Use.** Contrapositive: Cap > 24r(D+1) ⇒ κ ≤ r − 2. Since a non-proportional extra exists, κ ≤ r − 1 always. Then
  the Cover Bound gives z^{|C|−r+1} ≤ z^{−1}. With r < r₀ and D ≤ L, 24r(D+1) ≪ L² ≪ H^{1/2}. ✓

### 16.3 Vectors versus elements (the lead's question)

- TCL counts distinct exponent vectors; Cap(B) counts elements of 𝒩 ∩ J.
- They coincide. For a fixed vector e the jittered part Q_e = Πq^{e_q} ≥ X₀ is a realised number, so an element
  Q_e·d ∈ J forces d ∈ J/Q_e, an interval of length δ/Q_e < 1.
- So at most one element per vector, for **any** tail size. My §15 "≤ 1 + 2(‖α‖₁+1)δ" was a confusion (the α-interval is
  only a consequence of the basis relation) and is retracted.
- §15's other point, that (2D+1)^{r−1} should be (2D+1)^r, stands but is minor. TCL does not use it.

### 16.4 The Σα = 1 input: needs a two-branch reduction (GAP, small; confidence medium-high)

**[Superseded by §16.6: TCL′ and fix-smooth's Theorem 11.3 are hyperplane-free, so branch B is not needed for the
deterministic step.]**

- **The exactness is not automatic.** Small tails give wᵀe_y = 1 − log d_y/log z₀ + O(ε), so only Σα ≈ 1. Precisely,
  (1 − Σα)·log z₀ = log d_y − Σα_i log d_i + O((1+‖α‖₁)ε).
  - Σα ∈ (1/det E)ℤ, so Σα = 1 is forced only if (1+‖α‖₁)log T·|det| < log z₀. With r up to r₀ and D up to L, |det| can
    be large, up to (√r D)^r.
- **Branch A: all extras have Σα = 1.** Then S ⊂ aff(B), and aff(B′) = aff(B) for every basis B′ ⊂ S. TCL applies,
  needing only S ⊂ aff(B) (w > 0 is not needed; see 16.2). ✓
- **Branch B: some extra has Σα ≠ 1.** Then log z₀ is pinned by the tails, a (D2) window pin.
  - The pinned set has width ≲ (1+‖α‖₁)|det|ε per tail tuple, in place of the ≍ z/δ windows.
  - Using |det|, ‖α‖₁ ≤ (√r D)^{r+1} ≤ L^{1.5r+O(1)} (Hadamard; D ≤ L), the pinned per-height count is
    ≲ δ^{r−1}·L^{1.5r+O(1)}·T^{r}·polylog·(rank-full factors).
  - The L-exponent is −6(r−1) + 2r + 1.5r + r·log_L T. This is ≤ −4 iff r(2.5 − log_L T) ≥ 10. That holds for every
    r ≥ r₁ ≈ 4 log²L/log(3D) (≫ 10), which Cap ≥ H^{1/2} forces deterministically, provided T ≤ L^{2.4}. **It does not
    hold for small r**: at r = 2 with |det| ≍ L² the bound is O(1). But small r is excluded by r ≥ r₁.
  - This is a short computation in the style of §16.6's Cover Bound, not yet written. §16.6's own T^r against
    δ^{r−1} = (2L^{−6})^{r−1} needs only T ≤ L^{5}. So "small tails" should be fixed as **T ≤ L²**.
- **With branches A and B, small-tail CapL-w is closed [P | Cover Bound, TCL, branch B computation].**

### 16.5 Net

- TCL is a correct, clean lemma. Together with the Cover Bound it closes the small-tail case of CapL-w at every scale,
  once branch B is written (using r ≥ r₁) and "small tails" is fixed as T ≤ L².
- What remains for CapL-w: mixed and large tails (§16.6 (b)–(c)), i.e. fix-smooth's pins plus the lever question. By my
  §15.5, the lever cannot help beyond L ≈ 5·10¹⁴, so the large-tail "many weak gains" lemma is needed on
  [≈5·10¹⁴, e^{5000}] (or [5·10¹⁴, e^{1.5·10⁴}], depending on which estimate of fix-smooth's threshold holds).

### 16.6 Addendum: fix-smooth's proof (fix-smooth.md §11–12) and gap-g3's TCL′ (gap-G3 §16.9)

**fix-smooth's route is correct, stronger, and needs no hyperplane.**
- **Lemma 11.1.** Each element of a minimum cover has a private prime, else it could be dropped. So the C × {p_c} minor
  is diagonal, and C is independent, which means a basis B ⊃ C exists. ✓
- **Lemma 11.2 (κ ≥ r − j ⇒ |I₋| ≤ j, |I₊| ≤ j+1).** From e_y + Σ_{I₋}|α|e_l = Σ_{I₊}αe_i with nonnegative vectors,
  supp(y) ∪ ∪_{I₋}supp(e_l) = ∪_{I₊}supp(e_i). Then:
  - B∖I₋ covers, so |I₋| ≤ j;
  - {y} ∪ {e_l : l ∈ I₋} ∪ (B∖(I₊∪I₋)) covers with size r + 1 − |I₊|, so |I₊| ≤ j + 1. ✓
  - No hyperplane, no Σα, no exchange.
- **Theorem 11.3.** Every extra lies in span{e_I} with |I| ≤ 2j+1. An s-dimensional linear span projects injectively
  onto s coordinates in [0,D]^s, so it holds ≤ (D+1)^s points. Summing over I gives
  Σ_{s≤2j+1}binom(r,s)(D+1)^s ≤ e(r(D+1))^{2j+1}. ✓
  - For Cap ≥ H^{1/2} = e^{4log²L} and r(D+1) ≤ L², this forces κ ≤ r − 1 − j* with j* ≥ log L − 2.
  - So the Cover Bound gains **z^{−j*}**, not just z^{−1}.
- **Theorem 11.4 (TCL, 12r(D+1)² on the hyperplane).**
  - T2 extras sharing a negative index l have pairwise-intersecting I₊-pairs. Otherwise
    {y, y′, e_l} ∪ (B∖{l,i,j,i′,j′}) is an (r−2)-cover, which I checked.
  - The linking lemma bounds the number of distinct negative indices: C(t,2) ≤ 2t, so t ≤ 5. ✓
  - It is weaker in D than gap-g3's 3r(8D+4), but independent of it, and it closes T2 directly.
- **Numerics.** fix-smooth's 1500 configurations (2888 extras) and my 278 configurations: no violations in either.

**gap-g3's TCL′ (§16.9): correct.**
- Without the hyperplane, Step 1 also allows proportional extras (|I| = 1).
- Steps 2–3 are about supports and signs only. Step 2 gives |I₊| ≤ 2; Step 3 gives |I| + |I′| − 1 ≤ 3, and with
  |I| = 1 there is no constraint.
- So Step 4's pair/triple classification is unchanged. Size-1 supports never meet a pair or triple in a forbidden way,
  and they add ≤ r supports.
- Step 5 becomes crude: span(e_I) ∩ [0,D]^m holds ≤ (D+1)^{|I|} points.
- Cap ≤ r(D+1) + 3r(D+1)³ ≤ 4r(D+1)³ for κ ≥ r − 1, for any tails. ✓
- This is Theorem 11.3 at j = 1, up to constants.

**Consequences for my §16.4 and §15.**
- **The Σα = 1 input is no longer needed** for the deterministic step: TCL′ and Theorem 11.3 are hyperplane-free. My
  branch-B computation is moot.
- My only remaining use for "small tails" is the Cover Bound's tail sums (T^r against δ^{r−1}, so T ≤ L⁵ suffices).
- **The ‖α‖₁ / per-vector multiplicity point:** I agree with fix-smooth §12.3, and it matches my §16.3. A fixed
  jittered part M_f ≥ X₀ makes two J-elements with the same vector differ by ≥ X₀ > δ, so the count is ≤ 1 per vector.
  Neither TCL proof involves α growth: gap-g3's exchanges are support/sign bookkeeping, and fix-smooth uses only covers.
  Retracted in §15.

**What is still open for CapL-w (deterministic side closed).**
- **(a) Union over structure types** (fix-smooth §11.1, flagged). The gain z^{−j*} = e^{−L(log L−2)} absorbs type counts
  up to e^{L(log L−3)}. Naive typing of free-prime incidence patterns costs ≈ e^{rD log r}, which is ≤ e^{L²/(4 log X₀)},
  and that exceeds the gain once L ≳ 4 log X₀·log L ≈ 10¹⁰.
  - So either compress the incidence types (a trie, as in rank-full CL) or do the free-prime sum untyped inside the §11.9
    formula. GAP, bookkeeping, not structural. It **must** be written, because it bites exactly in the middle range.
- **(b) Large/mixed tails.** fix-smooth §12.4 shows the Cover Bound with smoothness densities needs r − |C| ≳ 2.8·10⁶ at
  L = 5·10¹⁴, while Theorem 11.3 gives only ≈ 33. So large tails need the exact γ-weights (harmonic versus pinned tails
  outside C). This remains the open core of CapL-w, consistent with my §15.5: it is not removable by raising H.

## 17. Cross-check with verify-cl (`verify-CL.md`)

- **Their point 1 (multiplicity): agree.** Already retracted in §15 and §16.3. A fixed exponent vector fixes Q ≥ X₀, so at
  most one tail lies in J/Q.
- **Their point 2: agree, and slightly sharper than mine.** Coordinates are nonnegative and ≤ D, so the injective pivot
  projection lands in [0,D]^r. That gives Cap ≤ (D+1)^r, not (2D+1)^r. Hence r₁ = 4 log²L/log(D+1).
- **Their points 3–4: agree** (Covering Lemma; peeling identity).
- **Their point 5: accept, and it widens my status table.**
  - §11.4(a)'s "every combination has ℓ¹ ≤ k" is false; their counterexample pays a width 5ε > 4ε. Their Theorem R (an
    exact Jacobian volume bound) replaces it, at ≈ θAδ per element.
  - But both Theorem R and §11.3's tree argument (lines 781–783, "deterministic sum over realised elements") integrate the
    pivots **with the free data held at realised values**. That is legitimate only if every free prime is decided before
    every pivot.
  - In general a free prime f decided after a pivot q is not F_{q−}-measurable: its existence and position depend on q's
    landing through the greedy. So the "sure (F3) sum over realised cofactors" cannot simply be pulled outside the
    pivot integrals. I accepted §11.3's step in my G8 without noticing this, and verify-cl is right.
  - Their partial repair is plausible: latest-first greedy pivots make e_f lie in the span of later pivots, so the
    integrand factorises as q_f^{−β_f}·G₀, and they add a sure Mertens-type bound (F4). Not yet done.
  - **Consequence beyond CL.** §11.9's peeling formula, the Cover Bound (§16.6), and therefore the probabilistic half
    of small-tail CapL-w (TCL is deterministic and unaffected) all use the same "integrate the pivots, then sum the
    realised free data" step. So **R.6 is a shared open step for rank-full CL, the Cover Bound and CapL-w**. It is not
    specific to §11.3.
- **Updated status line for the G3 side.**
  - E_cl ⟸ [Theorem R (rank-full) + Cover Bound + TCL/TCL′ (small tails) + large-tail core], **all modulo R.6**.
  - The large-tail core is still open.
  - The union over structure types (§16.6 (a)) is still to be written.

## 18. Targeted review: gap-G3 §16.10 (type union for small tails; mixed → large)

*Revision (same day).* Two points of my first version (quoted in gap-G3 §16.14) are withdrawn. (1) "Theorem R holds only
to L ≈ X₀^{1+o(1)}": verify-CL §R.8 already has Theorem R′, with e^{2k/X₀}(1+k/X₀)^{1.02k} at all L, so delete that sentence
from §16.14. (2) "Multiset Mertens" as the large-L fix: it misses the B′∖C rows, which 18.3 fixes.

**Verdict.**
- (i) is **correct**.
- (ii) as written is correct only for L ≲ e^{5·10⁷}, i.e. log L ≲ ½ log X₀.
  - "Canonical regime, L ≤ e^{100}" mis-scopes it. L is unbounded, and the zero scales have L ≥ X₀².
- (ii) can be repaired at every L by two pointwise sums over the distinct realised primes, the device verify-cl uses in
  R.8 (18.3). **With 18.3 written in, the type-union GAP of §16.6 is closed**, modulo R.6 and the Cover Bound.
- (iii) is **correct**, with one implicit step (18.4).

### 18.1 (i) Extras drop out: correct
- Cap(B) ≥ H^{1/2} gives κ(S) ≤ r − 1 − j*, with j* ≥ log L − 2 at every L (Thm 11.3, using r(D+1) ≤ L²).
- A minimum cover C is independent (L. 11.1), so it extends to a basis B′ ⊃ C in S, and κ(B′) ≤ |C|. No extra needs typing. ✓

### 18.2 (ii) as written: correct accounting, limited range
- As a union bound the accounting is right. A B′∖C row's z⁻¹ is its excess weight Πq^{−a} = 1/M, where M is the row's
  jittered part. So the row weighs (#types)·T/z.
- Two counts grow with L while X₀ stays fixed (D ≈ L/log X₀, κ < r₀ ≈ L/(3 log L)):
  - **B′∖C rows.** (e(κ+1))^D = z^ν with ν ≈ log(eκ)/log X₀, so ν ≤ ½ needs log L ≲ ½ log X₀. At L ≥ X₀², ν ≈ 2, and each
    row *loses* a factor ≈ z.
  - **C-row excess.** The cost κD/X₀ per unit exceeds 1 once L ≳ (X₀ log X₀ log L)^{1/2}.
- The weakness is in the bound itself, not in the arithmetic.
  - If P(C) really were κD primes in [X₀, 2X₀] with κ > X₀, there would be ≈ (eκ)^D > z monomials of degree D.
  - What rules this out is that P(C) consists of **distinct** realised primes, and only ≈ X₀/log X₀ of them lie in
    [X₀, 2X₀]. (ii) never uses this.

### 18.3 Repair at every L (pointwise in the realised primes, as in R.8)
**Input [sure].** The π ≤ κD primes of P(C) are distinct, so the j-th smallest is ≥ τ_j := max(X₀, X₀ + 0.99(j−1) − 2H)
(R.8). Hence
  Σ_{p∈P(C)} p^{−1/2} ≤ Σ_{j≤π} τ_j^{−1/2} ≤ 2.1√π,      Σ_{p∈P(C)} p^{−1} ≤ o(1) + 1.02 log(1 + π/X₀).

**(a) B′∖C rows.** At the realised pivots, a row's type sum is Σ 1/M over P(C)-monomials M ∈ [z/2T, 2z]. Rankin at
exponent ½ gives
  #{M ≤ 2z} ≤ (2z)^{1/2}·Π_{p∈P(C)}(1 − p^{−1/2})^{−1} ≤ (2z)^{1/2}·e^{2.11√π}.
- For L ≥ log X₀ ≥ 10⁸ we have √π ≤ 2·10⁻⁵L, so each row weighs ≤ 3T·z^{−0.499}.
- Taking the better of this bound and (ii)'s: per row ≤ T·z^{−max(1−ν, 0.499)}, at every L.

**(b) C-row excess.** Sum the excess patterns exactly:
  Π_{p∈P(C)}(1 − 1/p)^{−κ} ≤ (1 + π/X₀)^{1.04κ}·e^{o(κ)} ≤ L^{2.1κ}.
- This is e^{O(r log L)}, which δ^{r−2} = (2L^{−6})^{r−2} absorbs, as in §16.11.

**Result.** Per height ≲ e^{O(r log L)}·δ^{r−2}·z^{2−0.499(r−κ)}, with r − κ ≥ log L − 1. [§19.2: z² should be z,
since §16.10(ii) counts the window union twice. This only helps.]
- This is ≪ L^{−4} for log L ≥ 10 + O(c_T). Smaller L is covered by (ii) as written, since ν ≤ 10⁻⁵ there.
- Both bounds hold pointwise for every distinct-prime configuration. So they can be applied inside the pivot integral,
  before integrating, exactly as R.8 does for Πτ_j^{−(s_j−1)}. They add no hypothesis.
- Shared free primes still carry R.6/LBS's sharing caveat. The C-row free sums (λ = log D) must be realised sums via (F4),
  as §16.12 already notes.
- Multiset Mertens alone fails for (a): Σ_{all M} 1/M ≈ 1 has no gain. The gain is the window M ≳ z/T, which needs a
  Rankin exponent below 1.

### 18.4 (iii) Mixed → large: correct
- C's tails enter only harmonically. A completing row weighs (#types)·T/z if its tail is small, and (#types)·2ρ(u)/X₀ if
  it is large.
- **Implicit step (to be stated).** If rank(C ∪ S_small) ≥ κ + s, use the sub-basis B″ = C ∪ (s small-tail rows). It is
  rank-full with κ(B″) ≤ κ.
  - **Drop** the large-tail rows. Carrying them is wrong, because (eκ)^D·2ρ/X₀ can exceed 1.
- **Threshold.** With ν ≤ 10⁻⁵, s ≥ 3 + O(c_T) suffices. At large L, with 18.3's z^{−0.499}, the condition is
  s ≥ 5 + O(c_T), not 4.
- Otherwise all but O(1) of the ≥ 1 + j* completing rows have large tails. That is the large-tail problem with O(1) extra
  rows. ✓

### 18.5 Is everything modulo R.6 only?
- (i) is deterministic [P].
- (ii) and (iii), with 18.3, hold modulo:
  - R.6, which is (F4) [available] plus LBS [open];
  - the Cover Bound, a §11.9 sketch whose only open step I found is R.6 (§17).
  Everything else is [P]: Thm 11.3, Lemma 11.1, (F4), and the τ_j spacing.
- **So the answer is yes: modulo R.6 only, once 18.3 is written in.** Without 18.3, the claim is modulo R.6 *and*
  restricted to L ≲ e^{5·10⁷}.
- CapL-w as a whole stays open on the large-tail core (§16.12's table). (iii) correctly reduces mixed tails to it.
- **Bookkeeping for gap-G3:**
  - §16.13 still quotes Theorem R with e^{2k²/X₀} and says the original r₀ suffices. Per R.8 it should be Theorem R′, and
    r₀ = ⌈L/(3 log L)⌉ + 3 is needed once log L ≳ 51 log X₀.
  - With that r₀, §16.10(ii)'s "r log L ≤ L/4" becomes L/3. That is harmless.
  - §16.14's (iii) threshold should be κ + 5 + O(c_T) at large L.
  - I have not checked §16.14's large-L Ψ remark.

## 19. Targeted review: gap-G3 §16.11 (weak gains with a mild lever), plus §16.12/§16.16 and fix-smooth §13–15

**Verdict.**
- §16.11's claim "CapL-w closed at every scale" is **wrong as stated**, and gap-g3 has retracted it in §16.12. The cause is
  my §15.5 objection: once the raised M₁ pushes the absorption threshold y above X₀, Lemma P (12.2) fails.
- The **weak-gain lemma itself is correct** (modulo R.6 and the Cover Bound), with fix-smooth's correction: the condition
  is (1+j)g ≥ L + 4 log L + O(1), not 2L (19.2).
- **Residual window**, recomputed independently: no admissible M₁ supplies enough rows on
  - **log L ∈ [31.42, 41.95]** with tolerance A (M₁ ≤ H^{1/2});
  - **log L ∈ [31.83, 41.28]** with tolerance B (M₁ ≤ H/L^{14});
  - that is, **L ∈ [4.4·10¹³, 1.7·10¹⁸]**.

  This matches gap-G3 §16.16 to two decimals, and beurling-lit's rough [32, 41].
- **No capped lever threads the window** (19.3).
- ρ(D−1) per row is **not** the z-type gain fix-smooth §13.2 asks for. It is a strong weak gain. What replaces the z-type
  gain is the *number* of rows, which needs a capacity threshold c ≈ X₀^{5.6} (19.5).

### 19.1 The per-row gain (team-lead Q2): correct
- **Structure of a row.** A B′∖C row is M·d: M is a monomial in the P(C) labels (P(B′) = P(C)), and d is the
  non-jittered part. All primes ≥ X₀ are jittered, so d is an **X₀-smooth rational integer**.
  - In §11.9's formula the tails are free summation variables with counting weight (fix-smooth §14.1). This agrees with
    my reading of the Cover Bound: C rows keep 1/d_y, and rows outside C carry no tail weight.
- **The bound.** w_row ≤ z^{−1}Σ_k(π^k/k!)Ψ(2z/X₀^k, X₀) ≤ 3πρ(D−1)/X₀.
  - The k = 1 term dominates: the ratio πD log D/X₀ is ≪ 1 for every L ≤ X₀^{1/4}.
- **verify-cl's "(F1) counts slots" warning does not touch this.** That warning is about free *jittered* primes
  integrated at density 1. A row has none: its jittered primes are labels of C, and its tail count is an honest count of
  integers, so Ψ is the classical function. ✓
  - The warning does apply to the C rows' λ = log D sums. Those must be realised (F4) sums, as §16.12 says (part of R.6).
- **Ψ input: [P] without Hildebrand.**
  - Hildebrand's asymptotic holds here, since u = D−1 ≤ exp((log X₀)^{3/5−ε}) for log L ≲ 6·10⁴. But it is not needed.
  - Rankin's explicit bound Ψ(t,X₀)/t ≤ e^{−0.9u log u} (as in Lemma P (v)) raises the peak need from 5.59 to 5.90·log X₀
    and moves the window edges by ≤ 0.11 (19.3).
- **Caveat (R.6).** The row weight 1/M at fixed pivots is what the pivot-integration lemma must deliver. Free primes of C
  that are shared between rows carry LBS's caveat.

### 19.2 Arithmetic (team-lead Q3)
- **The double count: fix-smooth §14.2 is right.**
  - Per window the bound is δ^rz^{|C|−r}·Σ. Per height it is (z/δ)× that, i.e. δ^{r−1}z^{|C|−r+1}·Σ.
  - Check: at |C| = r this is exactly Theorem R's (z/δ)(θAδ)^r.
  - §16.10(ii)'s display "δ^{r−2}z²[…]" multiplies by z/δ a second time. So the condition is (1+j)g ≥ L + 4 log L + O(1).
- **Knock-on for my §18 (in my favour).** 18.3's z^{2−0.499(r−κ)} should read z^{1−0.499(r−κ)}. 18.4's large-L threshold
  s ≥ 5 becomes s ≥ 3, and the small-L one becomes s ≥ 2 + O(c_T).
- **Rerun.** Script /tmp/rhscratch/referee-b/lemP_window.py. Setup: log X₀ = 10⁸; worst r = r₀ = ⌈L/(3 log L)⌉+3 (R.8);
  ρ ≤ 1/Γ(u+1); j from Thm 11.3.
  - Standard capacity H_std^{1/2} closes log L ≤ 22.23 and log L ≥ 10002.
  - Under tolerance B (c ≈ H_std/L^{14}) it closes log L ≤ 22.86 and log L ≥ 7074.
  - The needed log c peaks at **5.59·log X₀ at log L = 38.06** (with r₀ = L/(4 log L): 5.56 at 38.08, gap-g3's and
    fix-smooth's figure). So the peak need is M₁ ≈ X₀^{5.6}, H ≈ X₀^{11.2} (A).
- **Above √(2 log X₀) ≈ 14142,** standard parameters close with margin, and no lever is needed.
  - Rankin keeps g ≥ 0.9D log D up to u ≈ √X₀.
  - Beyond that, Rankin at σ = ½ gives per-row gains of order z^{1/2} (cf. §16.14's remark).

### 19.3 Lemma P on the raised range (Q1, and the team-lead's M₁ question): the exact window
**Model** (gap-G3 §16.1 and my §15.1):
- M₁ = r₀ + c, L₀ = max(L⁵, 48M₁L³), log 2y = log 2 + log H + log L₀ + 6 log L, C_d = M₁L⁶/2;
- (12.2): 0.9u₀ log u₀ ≥ log 2y + log C_d + 4 log L, with u₀ = θ_bL/log 2y. It is vacuous when y ≤ X₀ (𝒜 = ∅).

Tolerance A, θ_b = ⅛, c in units of log X₀:

| log L | need | 𝒜-empty ceiling | (12.2) ceiling | status |
|---|---|---|---|---|
| 31.00 | 0.22 | 0.333 | — | closes (𝒜 = ∅) |
| 31.42 | 0.335 | 0.333 | none above it | **lower edge** |
| 34.00 | 2.83 | 0.333 | none above it | fails |
| 38.06 | 5.59 | 0.333 | 0.73 | fails; worst (LHS 3.3·10⁷ vs RHS 2.2·10⁹) |
| 40.00 | 5.51 | 0.333 | 1.98 | fails |
| 41.95 | 5.38 | 0.333 | 5.38 | **upper edge** |
| 43.00 | 5.32 | — | 9.2 | closes |

- **Window.** [31.42, 41.95] (A) and [31.83, 41.28] (B). With Rankin's 0.9: [31.42, 42.06] and [31.83, 41.40].
- **Shape of the failure.**
  - The lower edge is where the need crosses the 𝒜-empty ceiling: log c = log X₀/3 (A) or log X₀/2 (B).
  - On [31.4, ≈37], (12.2) fails for **every** y > X₀, not only the needed one. At log L = 34, a y just above X₀ gives
    u₀ ≈ 7·10⁵ and LHS ≈ 9·10⁶ against RHS ≈ 1.3·10⁸.
  - On [≈37, 41.95], (12.2) admits some 𝒜 ≠ ∅, but its ceiling stays below the need.
  - **So no lever value threads the window anywhere.** The answer to "a lever capped lower" is no.
- **§16.11's literal lever** (x^{400/log X₀} capped at X₀^{23}, M₁ = H^{1/2}) violates (12.2) on [30.45, 43.43].
- **Sharper Lemma P only trims the top of the window.**
  - (a) θ → ½ (θ_b = ¼) moves the upper edge to 41.27.
  - (b) [S] Stop the divisor trick at V = h/(2yC_dL⁴) rather than at h, and use the long-window count
    N(I) ≤ (6 + M₁L⁶/2)|I| + C_d (splitting into H-windows).
    - This removes the y-loss and leaves the E_cl cluster factor M₁L⁶. The RHS becomes log M₁ + 10 log L + O(1).
    - Upper edge: 40.66 at θ_b = ⅛, 39.98 at θ_b = ¼.
  - **The lower edge does not move under either.** Any Lemma P that keeps the M₁L⁶ cluster factor fails just above X₀.
- **Conjectured sharper Thm 11.3** (fix-smooth §15.1; I used Cap ≤ r²(D+1)^{j+1}): the peak need drops to 1.05·log X₀,
  and the window becomes [33.41, 38.75] (A) or [34.04, 38.06] (B). gap-g3's [32.1, 40.6] differs only via the poly(r) factor.

### 19.4 beurling-lit's figures, and a correction to my §15.5
- lit's "𝒜 ≠ ∅ from log L ≈ 32" and "[32, 41]" are confirmed: 31.42 and 41.95.
- lit's Lemma P tolerance "log H ≲ 0.38√(L log L) ≈ 4·10⁸ at log L = 38" comes from **my §15.5 formula, which overstates**.
  - Redoing it: log 2y ≈ 1.5 log H and log C_d ≈ 0.5 log H give log H ≲ 0.19√(L log u₀), with log u₀ ≈ 15, not log L.
    That is ≈ 1.4·10⁸ (1.46·log X₀) at log L = 38, matching the table's 0.73 in log c. §15.5's conclusions are unchanged.
- lit's "needed log H ≈ 22.3·log X₀" is §16.11's 2L version. With L it is 11.2·log X₀ (A).

### 19.5 Reconciliation with fix-smooth §13
- **ρ(D−1) per row is a weak gain.** g ≈ log X₀ + D log D ≈ 6.4·10⁹ at log L = 38, about 64 units of 1/X₀, against
  L ≈ 3.4·10¹⁶.
- §16.11 works by **multiplicity**. It needs 1 + j ≈ L/g ≈ 5·10⁶ rows outside a minimum cover, and Thm 11.3 supplies that
  many only when log c ≳ (2j+1)·log(r(D+1)) ≈ 5.6·log X₀.
- **fix-smooth §13.2** ("≳ L/log X₀ units of 1/X₀, or one z-type gain") is right as a statement about standard c, but its
  range should read log L ∈ [22.3, 10⁴]. Each ρ-strengthened unit is worth ≈ D log D/log X₀ ordinary ones.
- After c is raised wherever that is admissible, both notes agree: **a z-type gain is needed exactly on the 19.3 window**.
  The candidates there are a z-type tail gain, the Swap or Loose-Cube Lemmas, or a sharper Thm 11.3. fix-smooth §14.2
  already says this. The subfamily claims of §16.16 (trees closed to 34.7, cubes to 36.3) are not rechecked here.

### 19.6 Dependencies (Q4), and the other inputs that depend on y
- **Weak-gain lemma:**
  - the Cover Bound (§11.9 sketch; its open step is R.6);
  - Thm 11.3 [P] and §16.10(i) [P];
  - the Rankin bound on Ψ [P];
  - Theorem R′ for the rank-full part (modulo R.6).
- **Raised parts:**
  - [22.23, 31.42] uses 𝒜 = ∅. There y ≤ X₀, hence q_min ≤ X₀, so no jittered prime lies below q_min and there are no
    rigid runs. ✓
  - [41.95, 10⁴] uses (12.2) with 𝒜 ≠ ∅, which holds by the table. ✓
- **Ramp (R_H).** log H rises to ≤ 11.2·log X₀ with slope d log H/dL ≲ 10⁻⁶ ≪ ε. It glues to H_std near log L = 10⁴
  (need 4.0·log X₀, so log H = 8·10⁸ = 8 log²L). Decreases are harmless. The lag uses log H/L ≤ 2·10⁻⁶. ✓
- **σ_𝒜's compensator bound** uses u = L/log 2y with the full L, so it is far easier than (12.2): at log L ≥ 41.95,
  u ≥ 10⁸. ✓
- **Not rechecked at log y up to 17·log X₀:** fix-Bprime Lemma S / Prop. 9 (Dickman decay in log v/log y) and NV for
  q ∈ [y_std, y). gap-g3 should confirm both on [41.95, 10⁴].
- **Status of CapL-w:** closed for log L ∉ [31.42, 41.95] (tolerance A), modulo R.6 and the Cover Bound, given the minimal
  raise of c. **Open on L ∈ [4.4·10¹³, 1.7·10¹⁸].**

### 19.7 fix-smooth §16 (high-degree completion rows): correct. The 19.3 window is moot for CapL-w
- **(a) Span claim ✓.** Re-derived from Participation⁺ with φ(u) = c + uQ + u(u+1)/2:
  #(S∩V) ≥ φ(r) + r, and #(S∩W) < φ(r−1) + r − 1 for every proper W. So every W misses more than Q + r elements.
  Elements of degree ≤ D* number at most binom(m+D*, D*) ≤ Q (elements ↔ exponent vectors, §12.3), with
  m = |P(S∩V)| ≤ |C|·D ≤ rD. So ≥ r+1 elements of degree > D* lie outside every W, and these span V.
  D* must be computed from the deterministic bound m ≤ rD, so that the union runs over a fixed type class; fix-smooth
  does this.
- **(b) ✓.** The z⁻¹ per row is structural (Π_payers ≤ Π_C(2z/d_y)/Π_free; fix-smooth §14.1) and ignores row degrees.
  The bad event implies that some B′ = C ∪ R exists with R ⊂ {deg > D*}, by Steinitz from the spanning set. So the
  union may run over that restricted type class, and restricting only lowers the sum.
- **(c) ✓.** M_y ≥ X₀^{deg} gives d_y ≤ 2z/X₀^{D*+1}, and the trivial count of tails suffices (no Ψ needed). Then
  w_row ≤ Σ_{k>D*} binom(π+k−1, k)·2X₀^{−k} ≤ 3(eπ/(D*+1))^{D*+1}X₀^{−(D*+1)}, since eπ/k ≪ X₀.
- **(d) ✓.** My rerun is `/tmp/rhscratch/referee-b/degree_rows_check.py`. It uses r₀ = ⌈L/(3 log L)⌉+3, entropy bounds for
  every binomial, and π, m ≤ rD.
  - **Needed log c:** 0.098·log X₀ at log L = 41.9 (fix-smooth: 0.137). Robust version (×10 requirement, Q = c^{1/4}): 0.43.
  - **Range with 𝒜 = ∅:** the need stays below the 𝒜-empty ceiling log X₀/3 for every log L ≤ 44.2.
  - **The §15.5 chain:** M₁ ≈ c ≤ X₀^{0.1} and H = M₁², so y ≈ 48·H·M₁·L⁹ ≤ X₀^{0.3} < X₀. Hence 𝒜 = ∅, Lemma P is
    vacuous, and q_min ≤ y < X₀ (no rigid runs).
  - The grid scan finds **no inadmissible point** for this method on [20, 44.2], nominal or robust.
- **Combined coverage.**

  | log L | method |
  |---|---|
  | ≤ 22.2 | standard parameters |
  | [22.2, 44.2] | high-degree rows, 𝒜 = ∅ |
  | [41.95, 10⁴] | ρ-weighted rows with raised c; Lemma P holds (19.3) |
  | ≥ 10⁴ | standard parameters |

  The high-degree method alone degrades beyond log L ≈ 45 (need 7·log X₀ at 50), but the ranges overlap.
- **So CapL-w holds at every scale**, modulo R.6, the Cover Bound (§11.9 sketch) and Theorem R′'s constants. The Lemma P
  window of 19.3 matters only for the ρ-route.

### 19.8 Tolerance B (M₁ ≤ H/L^{14}) is valid: nothing downstream needs H^{1/2}
I checked every M₁-dependent step against M₁ = H/L^{14}, with λ′ ≈ 4L.
- **NV / (SW).** ν̂ = √(4M₁λ′/H) + (3 + B + 2M₁λ′)/H ≈ 4L^{−6.5} + 21L^{−12}.
  - **The binding sum** is fix-Bprime §7.4's Σ_v(log 3v)^{2+e}ν̂(v) ≈ Σ L^{−1.78}, which is ≈ 10⁻⁶ from L ≥ 10⁸. Prop. 9's
    E_S sums are smaller still.
  - So E_S ≈ 10⁻⁵ instead of e^{−600}, which is still ≪ 0.33. **The margin is now polynomial, not exponential.** The exact
    (SW) requirement is M₁ ≲ H/L^{12.5}, so B has slack L^{1.5}.
- **Per-scale NV** (Σ log u·ν̄): Σ L^{−5.5} ✓.
- **Lemma M form of G2R** (10⁶M₁L⁷ ≤ H): ✓, since L⁷ ≥ 10⁶.
- **Lemma P.** C_d ≈ M₁L⁶. At standard H, log 2y ≈ 16 log²L, so 𝒜 = ∅ until log L ≈ 2500, and then u₀ log u₀ ≫ log 2y ✓.
- **Participation⁺.** It needs only M₁ ≥ r₀ + φ(r₀); any tolerance works.
- **Block length and B.** L₀ = 48H/L^{11} < H, so Thm 4.2′ still works on sub-H windows. B ≈ 21H/L^{12} keeps (L-a) ✓.
- **K_loc terms.** K_loc ∝ B. Lemma 6's K_loc(X₀)/X₀ and §9.4(a)'s 2K_loc/u^{θ/2} ✓.
- **Where H^{1/2} came from.** It was only the R(δ) term (K_loc/√H), which is no longer used (§15.1). **Tolerance B is
  valid.**

## 20. Targeted review: verify-CL §R.12 / §R.12′ / §R.12″ (Staged Volume Lemma, SVL)

**Verdict: SVL is correct, and it closes LBS.** Three bookkeeping repairs are needed: B1 and B2 (needed only at L ≳ X₀) and B3 (for the
§R.12″ Cover-Bound use), all in 20.4. None of them changes the method. I re-derived every algebraic claim as a proof, not a numeric check
(20.1–20.2). verify-cl's stress tests (§R.12′, k ≤ 12, entries ≤ 6, T ≤ 9) agree with those proofs. They cannot test the analytic
steps, which are chains of pointwise inequalities, and I checked those by hand.

**The mechanism in one line.** FAC's exact weight for a late f ∈ F_t is q_f^{−β_f}. Write the integrand after stage t as
W_t·Π_{P_t}q^{1−s^{(t)}}. The q_f-dependence then splits into q_f^{−sᵀv} (inside W_t) and q_f^{+(s−1)ᵀv} (inside the pivot
factor), where e_{f,C≤t} = E_{C≤t,P≤t}v. SVL bounds the pivot factor pointwise by Π τ_j^{1−s_j}, which is valid because s_j ≥ 1
and q_j ≥ τ_j, **before** the F_t sum. Then f is harmonic: sᵀv = Σ_{y∈C≤t} e_{f,y} ≥ 1. β < 1 is absorbed rather than avoided,
and the result is the Volume Lemma's own pointwise bound, applied stage by stage. I sanity-checked the size on §R.12's example:
exact Σ_a (ab d₁/z)·(1/a) ≈ 1/X₀, against SVL's (1/X₀)Σ_a 1/a. These agree up to a log, so the bound is not too good to be true.

### 20.1 Item 1: stage identity (i), including §R.12″. Correct
- **Row stages exist.** Take the rows of E_{·,P≤t} as a matroid. C_{<t} is independent there, because E_{C<t,P<t} is invertible
  and E_{C<t,P≤t} therefore has full row rank. Extend C_{<t} to a basis. So nested C≤t exist for *any* grouping of pivots. Using
  singleton stages avoids typing the run structure; otherwise the type carries a harmless factor 2^{k−1}.
- **The nested Jacobian is the Schur complement.**
  - At fixed n_{C<t}, the earlier rows' P_t-content enters through q_{P<t} = q_{P<t}(n_{C<t}, c^{(≤t−1)}).
  - So ∂log n_{C_t}/∂log q_{P_t} = E_{C_t,P_t} − E_{C_t,P<t}E_{C<t,P<t}^{−1}E_{C<t,P_t} = S_t.
  - **Only D_t is needed** (team-lead's (c)). det S_t = D_t/D_{t−1}, and the stage factors are type constants, so they commute
    with every SUP-SUM and sup over ω. Their product telescopes to 1/|D_T| = 1/|det E_P| ≤ 1. No individual |det S_t| ≥ 1 is used.
- **Interleaving is fine.**
  - Within a run, pivots are integrated one at a time, with (θ/H)∫dq_p under progressive G (§R.9′).
  - The pending integrand is ∫ over dummy n_{C<t} of a function of (q_{P_t}, earlier). That is deterministic given those
    variables, so it is F_{p−}-measurable.
  - Tonelli then allows the joint change q_{P_t} → n_{C_t}.
- **§R.12″ (non-cover rows keep 1/n_y).** The identity Π_{P≤t}q/Π_{C≤t}n = W_t^{cov}·Π_{non-cov}n_y^{−1}·Πq^{1−s^{cov}} is
  just partial expansion, so it holds. It needs s_j^{cov} ≥ 1 at the stage where j is integrated. Lemma SC (lead L1) supplies
  that; I did not check Lemma SC.

### 20.2 Item 2: late primes (ii). Correct
- **Nonzero column.** e_f = E_{·,P≤t}v with v ≠ 0, and E_{C≤t,P≤t} is invertible, so e_{f,C≤t} = E_{C≤t,P≤t}v ≠ 0. It is
  nonnegative, hence ≥ 1 somewhere.
- **The rest of the column is forced.** e_{f,y} = E_{y,P≤t}E_{C≤t,P≤t}^{−1}e_{f,C≤t}. So in log n_y (y ∉ C≤t), expressed through
  n_{C≤t}, the coefficient of log q_f is e_{f,y} − E_{y,P≤t}v = 0. This is FAC exactly, with no ε-fuzz.
- **Injectivity.** The semigroup is free over distinct realised primes. Given (c_{y,F_t})_{y∈C≤t}, unique factorisation recovers
  each f and e_{f,C≤t}, and hence its whole column.
- So Σ_{F_t data}Π_{C≤t}1/c_{y,F_t} ≤ Π_{y∈C≤t}Σ_{c_y}1/c_y. All sharing patterns, including coincidences across C≤t rows, sit
  inside the product of sums.
- **Rows outside C≤t that contain f.** Their exponents are forced (no pattern count), their indicators are f-free, and they later
  drop f via (iii) with a bonus X₀^{−e}. ✓

### 20.3 Item 3: projected feasibility (iii). Correct (monotone, correctly ordered)
- **Define the projection over reals.** Proj_t(rem) := 1{∃ real values of the eliminated variables, i.e. pivots ≥ τ_j in slot
  order and free primes ≥ X₀ in their block ranges, completing a feasible point}. This is a deterministic function of the
  remaining variables, so it is F_{p−}-measurable at every later pivot.
  - A realised-completion version would be random and unusable. The real-valued version dominates it.
- **Why the indicator must be kept.** After a SUP-SUM the bound Π_y Eu is no longer supported anywhere. So the support has to be
  carried explicitly: Σ_F(·)1(feas) ≤ 1(Proj)·Σ_F(·). This is an upper bound, and it composes with later projections because
  feasible ⊂ Proj_t ⊂ Proj_{t−1}. ✓
- **The lower bound on n_y (y ∈ C_t).** n_y is a remaining variable and f-free by 20.2. At any point of Proj, a feasible completion
  satisfies n_y = c_y^{noF}·Π_{P_t}q^{E}·[Π_{P<t}q^{E}·Π_{F<t}f^{e}]. Hence
  n_y ≥ c_y^{noF}·Π_{P_t}q^{E}·Π_{P<t}τ^{E}·X₀^{|e_{F<t}|}. So 1/n_y is bounded on the support. ✓
- **Ordering.** The P_t factor's exponent is 1 − s_j^{(t)}. It collects the Jacobian's +1, the C_{<t} rows' q_{P_t}-powers (still
  live in W_{t−1}, since only F-parts were summed) and the C_t rows' powers via the bound above. So it is ≤ 0. ✓

### 20.4 Item 4: one chain per element, the pattern factor, and H-fuzz. Correct after B1–B3
- **One chain per element ✓.** Row y collects F-pieces only from blocks t ≥ t(y), and those blocks are disjoint and consecutive in
  decision order. Earlier pieces are dropped, but they are paid by a C≤t row (20.2). Early primes and tail come at the end.
- **B1 (pattern factor; needed for L ≳ X₀).**
  - §R.12 weights the later rows' units in column j (y ∈ C_{>t_j}) by X₀^{−E}. Summed over patterns, that gives
    Π_j(1−1/X₀)^{−k} ≈ e^{k²/X₀}, which is exactly the factor §R.8a removed.
  - With k = L/(3 log L), E_cl's exponent L − (5/3)L + L²/(18X₀ log²L) turns positive at **L ≳ 12X₀ log²L**, which is the zero
    scales.
  - **Fix:** on Proj every integrated pivot satisfies q_j ≥ τ_j (slot spacing; R.10(2)), so use τ_j^{−E}. That gives
    Π_jτ_j^{−(s_j−1)} → (1+k/X₀)^{1.02k}e^{2k/X₀}, as in R.8a. One line.
- **B2 (H-fuzz; needed for L ≳ X₀^{1−3·10⁻⁵}).**
  - §R.12′(b) charges e^{1.01(2H+3)/X₀} per boundary and e^{3TH/X₀} per row. With H = H(z) this exceeds 1 once log L > 3536.
  - With the boundary-local H(x_b)/x_b ≤ H(X₀)/X₀ (since H(v)/v decreases), the per-row cost is
    exp(2.02Σ_bH(x_b)/x_b) ≤ (1+T/X₀)^{2.04H(X₀)} when the T pivots are packed at τ_j.
  - That is ≈ 1 only while T ≪ X₀/H(X₀) = e^{10⁸−2716}. At the zero scales (T ≈ L/(3 log L) ≫ X₀) a prime near X₀ lies in the
    value-range of up to ~2H(X₀) blocks, and the cost is (1+T/X₀)^{2e^{2716}} per row, which is fatal.
  - **Fix: index chains by slot.** Put Eu_s(s) := Π_{realised p, slot ≤ s}(1−1/p)^{−1}.
    - Blocks are slot-disjoint, so each piece equals Eu_s(s_{p_t}−)/Eu_s(s_{p_{t+1}}) exactly, and the chain telescopes with no
      fuzz.
    - The carried factor 1/Eu_s(s_p) is *exactly* F_{p−}-measurable, which removes (S3)'s "≤ H+3 primes" proviso too.
    - Only the chain ends are fuzzy: Eu_s(top)/Eu_s(X₀) ≤ Eu(top+H)/Eu(X₀−H). (F4) is then applied once per row, at cost
      e^{O(H(X₀)/X₀)}, at every L.
- **B3 (§R.12″ non-cover rows).**
  - A non-cover row's free pieces across several blocks, plus its tail, must share **one** cap: #{(c_t)_t : Πc_t ≤ Y} ≤ Y·Π_tEu_s.
    Equivalently, use 1(Πc ≤ Y) ≤ Y/Πc_t, which is sequential-safe and harmonic in each block.
  - Separate per-block caps Y_{y,t} would give Π_tY_{y,t}, up to Y^T.
  - The sure count is #{c ≤ Y} ≤ Y·Σ1/c. This avoids (F3′)'s Y + H ≤ s proviso.

### 20.5 Item 5: worked examples and stress tests
- **§R.12 example** (R a b d₁, R a c d₂, R e d₃). Pivots are {R,e} | a | {b} | c, with C₁ = {n₁,n₃} and C₂ = {n₂}; S₂ = −1 and
  D₂ = −1. My recomputation gives θ³δ³·τ_R^{−2}X₀^{−1}·(Σ_a 1/a)·Σ1/(c d₁d₂d₃).
  - The displayed "Σ1/(a²c d₁d₂d₃)" omits the pattern factor. It also has a² where SVL gives a·X₀, because n₂'s a is dropped
    after F₁ is summed.
  - Both are harmless, but the display should be corrected.
- **§R.12′(d1), (d2)**: re-derived. Both are correct, including (d2)'s |det S₂| = 2 with D₂ = −2.
- **Stress tests.** The algebra SVL relies on is proved in 20.1–20.2 (matroid extension, nonzero column, exact FAC
  cancellation), so random tests can only confirm it, and §R.12′ did. The content beyond algebra is the pointwise chain of
  20.3–20.4, which no finite test exercises.
  - I found no configuration with late shared primes that escapes it. A late prime shared with non-C≤t rows is paid once,
    harmonically, in C≤t; it is forced elsewhere and dropped there with a bonus.

### 20.6 Consequences
- With B1–B3, Theorem R (general rank-full) is **[P] modulo PIL's inputs, (F1)–(F4) and progressive G**, at every L. LBS is
  closed, and EXT is not needed. That matters, since fix-budget showed EXT with c = O(1) is false.
- **R.6 for the Cover Bound** reduces to SVL plus §R.12″ with B3, plus Lemma SC (referee A).
- **What remains open:** only the inputs, i.e. (F4) on G and the per-scale events. No structural dependency of the CL chain is
  left open, on my reading.

### 20.7 gap-G3 §16.23 (raised y on log L ∈ [41.95, 10⁴]; my §19.6 "not rechecked" item). Correct
(Requested as "§20.6", but §20.6 above is already the SVL consequences.)
- **Inclusion ✓.** H ≥ H_std and M₁ ≥ M₁,std give L₀ ≥ L₀,std, hence y ≥ y_std and 𝒜_std ⊂ 𝒜_raised.
  - Primes are never absorbed, since y(q) ≪ q. Membership is n-local and decided at the latest prime, so causality holds.
- **NV / Thm 4.2′ ✓.**
  - Arrivals have latest prime q ≥ y(n) = H(n)L₀L⁶, so H(n)/q ≤ L^{−6}/L₀. The increments X_q ≤ 2M₁ follow with the *same*
    raised H and L₀.
  - Jittered q ∈ [X₀, y) are absorbed, so §16.5's one-sided repair is not needed.
- **Lemma S ✓.** I checked fix-Bprime §7.3: y there is the start point of ω_y(v), and the bound uses only Mertens for 𝒫.
  Its threshold H(v) ≥ (log v)^{8.5+2e+δ} only gets easier.
- **Prop. 9 ✓.**
  - The only 𝒜-input is §9.4(a). That gives (6.2H + 2K_loc)/u^{θ/2} ≤ e^{1.2·10⁹}/e^{2·10¹⁷} ≤ e^{−10¹⁷}, using H ≤ X₀^{11.2},
    K_loc ∝ B ≤ 21X₀^{5.6}L², L ≥ e^{41.95} and θ = ¼.
  - ν̂ ≈ 2√λ′H^{−1/4} under tolerance A, and T′_det's oscillation over 2.04H(v) is still negligible.
- **Lemma P (12.2), σ_𝒜, queue size ✓.** These are as in my §19.3 table (C_d included) and §19.6. B ≪ x^θ trivially.
- **One small point.** Lemma P(i) takes y := y(2u) as the bound for y(n), n ∈ [u, u+h]. That is a mild monotonicity use, and it
  fails on the *decreasing* part of the ramp near log L = 10⁴.
  - Fix: use y := sup_{[u,2u]}y(·).
  - This is harmless: the ramp slope d log H/dL ≲ 10⁻⁶ moves log y by ≪ 1 over [u, 2u]. So §16.23's "no step uses monotonicity
    of y" should read "only Lemma P(i), harmlessly".
- **Not checked:** A11.2's Ê_𝒜 at y = X₀^{O(1)} (beurling-lit).
- **Remark.** By my §19.7 the high-degree route already covers up to log L ≈ 44.2 with 𝒜 = ∅. So the raised y is needed only on
  [≈44, 10⁴]. Taking it on [41.95, 10⁴] is also fine.

### 20.8 Note on verify-CL §R.13
- **B1–B3 and the display fix are transcribed correctly.** ✓
- **The exchange issue does not touch SVL.** That issue is about Referee A §17.1 and gap-g3's 𝒩_τ[Φ], where the sup is taken outside
  ∫dP_{>t}. SVL keeps PIL's order: F_t's SUP-SUM sits *inside* the later-performed integrals over P_{>t}, and its bound
  (Eu_s ratio × 1(Proj)) is a function of those earlier variables. No exchange is used.
- **The allocation caution (no double credit of X₀^{−deg_P}).** I re-checked the per-row weights I accepted:
  - §19.1: z^{−1}Σ_k(π^k/k!)Ψ(2z/X₀^k, X₀);
  - §19.7: Σ_k binom(π+k−1, k)·2X₀^{−k}.

  Both sum the row's monomial patterns against its count cap, with no separate excess credit. ✓
- **Confirmation (after Referee A §17.4).** §R.13's Proj_t (the projection of real completions, deterministic and F_{p−}-measurable) and its B2 slot-indexed chains (Eu_s, fuzz only at the chain ends) are **[P] as written**. Two notational readings are needed: the n_y inequality is meant with t = t′−1, and τ_j uses slot labels; the carried factor should be 1/Eu_s(s_p−), over jittered primes. Nothing is missing.

## 21. Targeted review: Lemma BS (H⁗) certification (gap-localPNT §6.9.3′(H⁗))

**Verdict.** The canonical case (τ ≥ 10⁸) is **[P] plus [P-CA in arb], once two cover seams are closed**. I closed them and
reran the cover: 0 failures (21.2).
- Items 1, 3, 4 and 5 are correct. Item 2 is correct after the seam fix. The remaining edits are cosmetic.
- **Reproduction.** I ran the arb run from the durable copy, with paths patched, from /tmp/rhscratch/referee-b/bscert/:
  - Z2: 301,504 cells, 0 failures, min ℓS = 2.491·10⁶, identical to the report;
  - aux: 9,609 and 13,823 cells, with margins 0.189 and 1.724.

### 21.1 Item 1: S ≤ Σ is proved (derivation checked line by line); the 300 checkpoints are only corroboration
- **The target.** The induction needs J_true := ∫_{w≤U(m)}πe^D − 1, where π has mass 1 for u ≥ 2 by (R1).
  - Take any majorant D̄ of D on [u−1, Ū], extended positively beyond Ū. Then J_true ≤ ∫π(e^{D̄} − 1).
  - Likewise E₁–E₃ may drop the indicator.
  - So the code's full-range integrals are legitimate upper bounds.
- **Part I ✓.** The bound D ≤ β_I − α(u−w) follows from:
  - h convex, so h(w) ≤ h(u) − h′(u−1)(u−w);
  - alphaA ≤ (B/ℓ)h′(u−1), since h′(u−1) = u³[(3u−4)log(1+u) + u(u−1)/(1+u)]/(u−1)²;
  - φ convex, with the same chord argument;
  - 1/√m ≤ k_u/√ℓ;
  - the shift bound, which holds because (1−x)^{1/4} ≥ 1 − x/3 on [0, ½];
  - c_w ≤ c_u and −κ/(wℓ) ≤ −κ_min/(uℓ).

  Then π(I) = 1 − 1/(ur(u)) and E(u−w)₊ = 1 − 1/r(u) hold exactly (R1), and e^{−αt} ≤ 1 − (1−e^{−α})t for α ≥ 0.
- **Part II ✓.**
  - Slopes are taken at the right end of each piece (convexity), with Ū ≥ U(m).
  - The π density is ≤ e^{−r(u−1)s}/u (R3).
  - It is applied only to e^{β+γs} − 1 ≥ 0, since β_II ≥ 0.
- **E₁, E₂, E₃ ✓.**
  - E₁ = 2K′u²r(u−1)e^{D(u−1)}/ℓ exactly, because ρ(u−2)/ρ(u−1) = (u−1)r(u−1).
  - E₂'s Part I mass is ∫ρ(w−1)/ρ(u−1)dw = u−1 (R1).
  - Every term of η is increasing in w, with m ≥ ℓ/2.
- **T ✓.** The bound follows from (G), (R3) and Φ(ℓ) ≥ C₀e^{−κ/ℓ}.
  - The expression maximised by E_T is decreasing in y = log(ℓ/τ), since √(2y+4) ≤ 7.1 < r₀ℓ^{1/4}.
  - So the maximum is at y = log 30, or else at U_y = u. In the second case a(ℓ,u) = y + 2 gives exactly −2 − 1.5r₀.
- **r enclosures ✓.** r_low comes from the (R3) recursion. Its step g(r) = r/(1−e^{−r}) is increasing, and r is increasing, so
  it is a lower bound. r_up uses (R4), valid for x ≥ 1 and any δ.
- **Uniform in τ ≥ 10⁸ ✓.**
- **Independent check** (`s_vs_sigma.py`).
  - My own Dickman table uses a stable trapezoid scheme for vρ(v) = ∫_{v−1}^vρ and matches ρ(10) and ρ(20).
  - At 19 points with ℓ ∈ {3·10⁹, 8.3·10¹⁰, 10¹⁴, 10¹⁷} and u ∈ [2, 205], S ≤ Σ_true everywhere, with S/Σ_true ∈ [0.55, 0.97].
  - At the minimum cell (ℓ ≈ 8.3·10¹⁰, u ≈ 200): ℓΣ_true = 4.8·10⁶ against ℓS = 4.2·10⁶.
- **Nit.** S_cell checks r₀ > γ_max but not r₀ > γ₁, and γ₁ > γ_max when u > Ū − 60. On the domain γ₁ ≤ 0.25 < 1 ≤ r₀, so this
  cannot fail, but add `assert lo_(r0) > hi_(gam1)`.

### 21.2 Item 2: the cell cover is correct after closing two seams (done)
- **Enclosures hold on whole cells.**
  - Every quantity depending on ℓ or u is an arb ball over the cell.
  - In v-mode, u = u₀(ℓ) + v, which removes the u − u₀ dependency correctly.
  - r is enclosed by r_low(ua) and r_up(ub); Ū by Ubar_up(lb).
  - The only floats left outside lookups are `us = Ub + 0.5` (sub-ulp, and it only touches T ≤ 10⁻¹¹) and `arb(12.8)`, which
    is ≥ 12.8 as a float.
- **ivarb.py's primitives are valid enclosures** (tested directly). The lo/hi conversions are outward. ipos and isq are
  conservative: isq([−3,−1]) returns [0, 9], loose but valid. Arb radii carry about 10⁻⁹ relative widening, which is one reason
  arb runs about 4% below binary64. The floats B = 11, KMIN = 4·10⁸, K′ = 2.2 and 12.8 are all ≥ the true constants.
- **No gaps inside a band.** The ℓ-bands are contiguous and exact at both ends (checked exactly). The u-edges and bisection
  midpoints are shared floats.
- **But two seams per band were not covered** (`seams.py`, exact arb check):
  - **u/v seam.** The v-cells start at va = fl(split − fl(lb^{1/4})). That leaves u ∈ (split, u₀(ℓ)+va) uncovered for ℓ near lb,
    in 399 of 403 bands, with width ≤ 4.3·10⁻¹².
  - **Top seam.** The last v-cell ends at fl(va + n·step), which falls short of Ū(lb) − lb^{1/4} by up to 1.9·10⁻¹⁰ in 402 of 403
    bands. That leaves u near U(ℓ; 10⁸) uncovered.
  - **Fix.** Use va := ↓(split − ↑lb^{1/4}) and top := ↑(Ubar_up(lb) − ↓la^{1/4}); cells may overhang the domain harmlessly. With
    `cert_run_arb_patched.py`: 302,013 cells, **0 failures**, min ℓS = 2.491·10⁶.
- **Doc corrections.**
  - "binary64 agrees with arb to ≈ 2·10⁻⁵" is wrong. On the minimum cell they give 2.600 versus 2.491·10⁶, and they differ by up
    to 10% on random cells; balls are wider on wide cells by the 2r₁r₂ terms. This is harmless, because arb is the
    conservative run.
  - The durable copy hard-codes sys.path to /tmp/rhscratch/gap-localpnt. Under -I the script's own directory is not on sys.path,
    so it will not run once /tmp is wiped. Insert `os.path.dirname(__file__)` instead.

### 21.3 Item 3: Z1 and Φ-dominance are correct
- **Z1** (u < 2, ℓ ≥ 30τ). I checked every step and recomputed the constants:

  | constant | value | check |
  |---|---|---|
  | c₂⁻ | 0.610034 | closed form = quadrature |
  | J₂ | 200.516 | Gamma moments 393 and 1029 |
  | 1 − κ/(2w₁ℓ) | 0.92874 | ✓ |
  | 4·0.92874·c₂⁻ − 2.0012 | 0.26504 | ✓ |

  - **Nit.** h(2) = 56.145, not 56.1. With it, B's part is 2677.6, so the constant is 2711, not 2700. This is harmless, since
    0.265τ ≥ 2.6·10⁷.
  - **Exact-ρ check** (`z1_check.py`). At τ = 10⁸ and ℓ ∈ {30τ, 300τ, 10¹⁷}, min_{u<2} ℓΣ_true is 6.4·10⁷, 5.1·10⁷ and 3.1·10⁸.
    The claimed bound is 2.65·10⁷.
- **Φ-dominance** (ℓ ≥ 10¹⁸, 2 ≤ u < 27).
  - E_π[1/w] ≥ π(I)/u ≥ (1 − 1/(2r(2)))/u = 0.693/u, so ℓΦ_ben ≥ 9.54·10⁶. ✓
  - j_A ≤ (1.5 + 392/u)Λ(u). Part I uses h_A ≤ Λ(1+u)/u; Part II uses h′ ≤ 8(1+w)²log(2+w) and r₀ ≥ 1. So B·j_A ≤ 4.67·10⁵. ✓
  - 2K′u²r_up(26) ≤ 1.96·10⁴. That is close to the stated 2·10⁴, but holds. ✓

### 21.4 Item 4: scope ℓ₁ = 30τ is correct, and no consumer is restricted by it
- **ℓ₁ is internal to the proof.** The base region [τ, 30τ] is (F).
  - Φ_∞ ≥ C₀·max_{[τ,30τ]}(ℓ/τ)e^{κ/ℓ} = C₀e^{4+1500/τ}. The maximum is at an endpoint by convexity, and 30e^{0.133} = 34.3 < e⁴.
  - Lemma V applies because U ≤ 4.21ℓ^{1/4} there, so L ≥ ℓ^{3/4}/4.3 ≥ 2·10⁵.
- **So W_t(Y) ≤ C_BS·log t/log Y for every Y ≥ t**, with C_BS ≤ 38.3.
- **Consumers** use only t ≥ X₀, so τ ≥ 10⁸, and any Y ≥ t: (S) with t = max(2v, X₀), and (SW)/A2.3(c), where ν vanishes below
  X₀. ✓

### 21.5 Item 5: (H″) for u ≥ 27 and Lemma V are correct
- **(H″).** `aux_cert_arb.py` certifies the exact consequence of
  E_πh_A ≤ (1+u)³log(2+u)/u − 3u²log(1+u)(1−1/r(u)) + 144Λ/(ur₀²).
  - I re-derived it: h′(u−1) ≥ 3u²log(1+u) for u ≥ 3/2, and the Part II moment is ≤ 8·3.67Λ/(ur₀²) for r₀ ≥ 4.3. Also
    e₁ = u²r(u−1) and e₂ ≤ u+1, and the r enclosures point the right way.
  - **Doc nit.** The text's (1+3/u)(1+1/(u log u)) is not an upper bound for (1+u)³log(2+u)/(u³log(1+u)): at u = 27 it gives
    1.1236 < 1.1271. The script uses the exact term, so only the display is wrong.
  - Beyond 4·10⁵, r_low ≥ 15.57 gives a bracket ≥ 1.80. ✓
- **Lemma V for L ≥ 100.**
  - α is the minimum of a_V′ on [u−1, u] at fixed L, and E_ν[u−s] ≥ max(½, 1 − 1/r(u−1)). ✓
  - L(1−e^{−α}) is increasing in L, so L = max(100, u) is the worst case. ✓
  - θ ≥ 0.92 needs r(u) ≤ 0.08L. At L = u = 100 this holds only with the optimised-δ (R4): r_up(100) = 7.66, while the
    true r(100) = 6.48. The cruder bound log u + log log u + 2 = 8.13 would not suffice; worth one line in the text.
  - The 15e^{−0.4L} term is generous. Beyond 10⁶ the argument is analytic. ✓

**Net.** Lemma BS in the canonical regime is [P] plus [P-CA in arb], once the two-line seam patch is adopted in
`cert_run_arb.py`. Nothing else is outstanding from my side. Scripts: /tmp/rhscratch/referee-b/bscert/
(`seams.py`, `cert_run_arb_patched.py`, `s_vs_sigma.py`, `z1_check.py`).
- **Confirmation (after gap-localpnt applied §21).** The durable `cert_run_arb.py` now has seam-safe edges.
  - Checked exactly in arb at 53 and 200 bits: for every one of the 403 bands, u₀(lb) + va ≤ split and top ≥ Ū(lb) − lb^{1/4}.
    These are the worst cases over ℓ ∈ [la, lb]. Edges are contiguous, and the u-cells run from 2 to split.
  - The r₀ > γ₁ guard is in, and the scripts import from their own directory.
  - I reran the durable copy: 302,013 cells, 0 failures, min ℓS = 2.491·10⁶.
  - **§21's verdict is now unconditional: Lemma BS (canonical) is [P] plus [P-CA in arb].**

## 22. Targeted review: v3 part-G (notes/v3/part-G.md)

### 22.1 Lemma 4.15(e) (joint Rankin) and its use in Theorem 4.17's tail (T2): correct
**The statement and proof of (e) check out.**
- **Rankin.** w_y = z^{−1}·#{(M,d) : Md ≤ 2z}, with M a monomial in the π labels and d X₀-smooth. Using 1(Md ≤ 2z) ≤ (2z/Md)^{1−η}
  gives w_y ≤ 2z^{−η}·Π_{P(C)}(1−p^{η−1})^{−1}·Π_{p<X₀}(1−p^{η−1})^{−1}.
  - Summing over all monomials, including M = 1, only over-counts.
  - The bound is uniform over realised label sets, so it is a pointwise bound in the pivot variables. This is the same use as
    in my §18.3/§20, and it is legitimate inside SVL.
- **The rigid factor ≤ exp(log Λ + 2 + 1.3X₀^η/(ηΛ)).**
  - The first-order part is Σ1/p ≤ log Λ + 0.27 (Rosser–Schoenfeld), plus Σ(p^η−1)/p ≤ 1.26X₀^η/(ηΛ)(1 + O(1/ηΛ)) by partial
    summation, including the boundary term π(X₀)f(X₀).
  - The second-order Euler terms are 0.62 at η = ¼ (computed).
  - So "+2" covers both.
- **The label factor ≤ (X₀+π)^η/(0.99η).** This holds given the stated "i-th smallest label ≥ X₀/2 + 0.99(i−1)".
- **Caveat on that lower bound.** It needs the jitter H(q) of a label at value q to be ≤ X₀/2.
  - It holds whenever L ≤ X₀^{50}, since H(q) ≤ q^{0.01} for log q ≥ 3·10⁵.
  - For astronomically larger L the safe form is q_i ≥ ⅔(X₀ + 0.99(i−1)), from H(q) ≤ q/3. That multiplies the last term by
    (3/2)^{1−η} ≤ 1.36, which is immaterial for (T2).
  - Please state it that way.

**(T2), ℓ ≥ 0.3Λ.**
- With η = ¼ the bound reads log(1/w_y) ≥ L/4 − 5.2X₀^{1/4}/Λ − 4.04(X₀+L²)^{1/4} − log Λ − 3, using π ≤ r₀D ≤ L².
- Since L ≥ X₀^{0.3}, L/4 exceeds the X₀^{1/4} and L^{1/2} terms by a factor ≥ e^{0.05Λ}, so log(1/w_y) ≥ 0.24L. ✓
- Also j ≥ ℓ − 2 ≥ 4 (log c = 4ℓ² − log 4 and log(r(D+1)) ≤ 2ℓ), so 5 rows give (4.10). ✓
- There is no upper limit in L: every error term is o(L). Lemma 4.14(ii)'s per-row costs (C-row excess ≤ L^{2.1} via slot
  spacing, λ_D ≤ log D + 1, tail sum ≤ 2L) are also uniform in L.
- **So CapL-w closes at every scale through and beyond the zero scales L ≥ X₀².**

**(T1), 2·10⁴ ≤ ℓ ≤ 0.3Λ.**
- Lemma 4.15(d)'s hypotheses hold: π X₀^{−1}(eD)^{0.9} ≤ e^{−0.13Λ+1}, D ≤ X₀^{1/2} and D − 1 ≥ 10⁴. The label-ratio condition fails
  only past ℓ ≈ Λ/2.9, as gap-g3 says, so (e) is needed exactly where it is used.
- The bound (1+j)g/L ≥ 0.9(ℓ−1)(ℓ−log Λ)(1−Λ/L)/Λ ✓. At ℓ = 2·10⁴ it is 3.597. ✓
- **Heads-up for the Λ-uniform version.** This "≥ 3.5" holds only for Λ = 10⁸: at Λ = 3·10⁸ it is 1.20, and at 10⁹ it is 0.36.
  (T1) holds once ℓ ≥ ≈ 1.1√Λ. So in the Λ-uniform version the certificate must run up to ≈ 1.1√Λ, or the analytic tail must
  start there. Its other thresholds (log Λ = 18.43, 4ℓ² ≥ 5.95Λ at ℓ = 1.22√Λ) also scale with Λ.

### 22.2 Theorem 4.17, Λ-uniform analytic version (Steps 0–6): correct. My T1 concern is met
- **(1) Route H ≥ 1.63L ✓.** The ingredients:
  - k = D*+1 ≥ log c/(2(A+1)), and 1+j ≥ (log c/(2A))(1 − (A+1)/log c), with a ≤ A;
  - log((π+k)/k) ≤ log 2m ≤ A in Lemma 4.15(b), whose hypothesis holds since π ≤ Λ³e^{14} ≪ X₀;
  - (A+1)/log c ≤ (2ℓ+1)/(3.9ℓ²) ≤ 0.029.

  Then log c ≥ 1.3GΛ gives (log c)²(Λ−A−1)/(4A(A+1)) ≥ 1.69L, times 0.969. ✓
  - The "D* ≥ D−1 impossible" branch is not even needed. If no element has degree > D*, the degree count gives ≤ Q < c
    elements, a contradiction. Otherwise Lemma 4.15(b) applies with k = D*+1.
  - The ramp: G(10⁸,·) has log-slope ½ + A_s(1/A + 1/(A+1))/2 + … ≤ 0.53, since A ≥ 64 at s ≥ s_H. So γ_* stays below the
    linear ramp. ✓
- **(2) G is decreasing in Λ ✓.** ∂_ΛA = (3−2/ℓ)/Λ, and the sign condition reduces to 6/A < 1. Also A ≥ log(2Λ/log Λ) ≥ 16 on the
  whole path Λ′ ∈ [Λ_s, Λ], because L′ ≥ Λ′ there. Λ ≥ Λ_s holds exactly because z ≥ X₀, and γ_* is non-decreasing in s. ✓
- **(3) Dickman rows ✓, uniformly in Λ.** f(s, x = log Λ) = 3.375(x+s)/(3x+2s−2.9).
  - ∂_s f ∝ x − 2.9 > 0 and ∂_x f ∝ −(s+2.9) < 0. So inf f = lim_{Λ→∞} = 1.125 > 1.12, and at Λ = 10⁸, s = s_H+1, f = 1.29.
  - a ≤ 3x + 2s − 2.9 holds with room, since a ≤ A − log 2 = 3x + 2s − log ℓ and log ℓ ≥ 3.78.
  - Using the standard term instead only enlarges j.
- **(4) Lemma P ✓.**
  - log 2y ≤ 3.01γΛ and log C_d + 4ℓ ≤ 1.01γΛ. With u₀ ≥ θ_bΛe^s/(3.01γ), (12.2) reduces to e^s·log(θ_bΛe^s/(3.01γ)) ≥ 13.44γ²/θ_b,
    which is 107.5γ². This is increasing in Λ, s and θ_b.
  - At Λ = 10⁸ the values are 393e^t(19.2+t) (log evaluated at the worst γ = 7.5) against ≤ 6053. ✓
  - s ≤ s_H gives y ≤ X₀ uniformly, since 9ℓ + 7.3 ≤ 3·10⁻⁵Λ. With H_std dominant the constant is 7.33, not 6.6; harmless.
- **(5) Tails ✓.** T2 is as in §22.1; please apply that subsection's label-bound restatement to Lemma 4.15(e), which is still
  unchanged in the text.
  - T1 now starts at ℓ_std ≈ 1.37√Λ, where its value is 0.9·1.875·(1 − O(log Λ/√Λ)) ≥ 1.68 for every Λ ≥ 10⁸.
- **My T1 heads-up is met.** The middle range s ∈ [s_H + 1, 0.3Λ − 2 log Λ] is covered for every Λ by Step 3, with ratio
  ≥ 1.125. Step 3 needs only log c ≥ 7.5Λ, whichever term of c dominates. T1 is therefore redundant, and also correct. Step 2
  covers every s ≤ s_H + 1, including s near −log Λ. So the cover of s ∈ [−log Λ, ∞) is complete.
- **fix-smooth's corner issue is moot.** D enters only through D ≤ 2L/Λ (in m and a, the worst direction for route H) and
  D ≥ L/Λ (in g, the worst direction for Dickman). There are no cells.
- **(c) ✓.**
  - On the ramp, d log H/dL ≤ 14.4/(393Λ) ≈ 3.7·10⁻¹⁰.
  - In the γ_*-dominant region it is ≤ 1.73A²/(Λℓ²). That is ≤ 4·10⁻⁸ with A ≤ 1.5ℓ there; A ≤ 2ℓ alone gives 7·10⁻⁸. Either is
    ample.
  - (log H − log H_std)/L ≤ 10⁻⁶ on the raised range. The tolerance M₁ ≤ H^{1/2} ≤ H/L^{14} holds.
- **Nit.** Step 0's "a ≤ A − log 2" is off by log(1+1/D) when D ≈ 1. Only Step 3 uses the −log 2, and there D ≥ 10¹¹.
- **Independent numeric check** (`/tmp/rhscratch/referee-b/capl/thm417_check.py`; 2·10⁵ random points, Λ ∈ [10⁸, 10³⁰],
  s ∈ [−log Λ, 60]):
  - s_H = 5.97454 ✓;
  - Step 1 monotonicity, route H with exact j and D* (min ratio 1.69), Dickman rows (sampled min 1.19) and the Step 5 condition:
    0 violations.
  - This is evidence only. The proof stands on Steps 0–6, which I checked line by line.

## 23. Targeted review: fix-Bprime §11–§12 (the X₀ jump; Lemma XB, Lemma SI)

**Verdict.** §12 closes the X₀-jump gap of §11(b) for Λ = 10⁸. Two statement fixes are needed: SI's constant and its t-range
(23.1), and the λ in 12.1's tail (23.3). Neither changes the margins. Λ-uniformity is pending §12′ (23.5).

### 23.1 Item 1: Lemma SI (huge N) is correct, with one statement fix
- **The profile is genuinely proved.** "W_t(M; z) ≤ (τ/log M)Φ_∞ρ(u−1)e^{A+a}" is exactly Lemma BS's induction claim Ψ(ℓ,u) ≤ G(ℓ,u)
  (gap-localPNT §6.9.3′(E)), divided by max(1, ℓ/τ) = ℓ/τ.
  - That claim is proved for every ℓ ≥ τ and 0 ≤ u ≤ U(ℓ; τ), with Φ(ℓ) ≤ Φ_∞ ≤ 38.3, uniformly in τ ≥ 10⁸ (my §21).
  - Here log M ≥ (J−τ)/2 ≥ 9·10³², so only the analytic part of that proof is used: (H′), (H″), Z1 and Φ-dominance, not the cell
    certificate.
  - Also Y = M ≥ t, and ρ(u−1) := 1 for u ≤ 2, as in the profile's convention.
- **Decomposition ✓.** n = mp with p = P⁺(n) ≤ tm gives m ≥ √(N/t), and in a block P⁺(m) < 2N/M.
  - (B) is Rankin with β = 1/log z. Then Σ_{p≤z}p^{β−1} ≤ log log z + O(1), since p^β ≤ e, so v ≤ e^{14}(log z)e^{−ℓ/log z}.
    Also J/Λ₁ ≥ 1.33·10⁸ beats log(1/η) ≤ 1.01·10⁸.
  - (A) uses LP⁺ as an input, giving Σ_{p∈I/m}1/p ≤ 1.1η/log(N/m).
  - The Riemann-sum change of variables dj/(jσ) = du/(Ju) is right. ∫_{u_min}^∞ρ(u−1)du/u = log(1/u_min) + 1 by (R1).
  - Region 2 drops density, at cost ≤ e^{−(J/2)^{1/4}}.
- **The fix.** The lower limit is u_min = (J−τ)/(J+τ). So the factor written "(1 + 10⁻⁵)" is really 1 + log((J+τ)/(J−τ)), which is
  1.2 at τ = J/10. The constant 61.1 therefore holds only for τ/J ≲ 5·10⁻⁶.
  - In general SI gives ≤ 61.1(1 + 2.1τ/J)·ητ/J.
  - SI's hypothesis t ≤ (height)^{1/10} is also violated in the huge-N (β₁) step for wm ∈ (N^{0.09}, N^{1/10}]: there
    t_{wm} = 4.01wmX₀ > (N/(wm))^{1/10}.
  - Both are harmless. Cut that m-sum at wm ≤ N^{1/100} instead of N^{1/10}. The cut tail has weight ≤ 13.1(N^{1/100}/W₁)^{−0.2},
    which is negligible, and below the cut τ_{wm}/J ≤ 0.01 + o(1). So the effective constant stays ≈ 61·(1 + O(Λ/J)).
  - The huge-N total and the margin e^{−59} stand.

### 23.2 Item 2: the medium range is correct
- The counting input Σ_{e∈J}1/e ≤ 27|J|/z + 6z^{−3/4} ✓, from N(J) ≤ 13.5|J| + K(z), K ≤ 3z^{θ/2}.
- The (α), (β₁), (β₂) and (γ) bookkeeping is ✓. The arb constants reproduce: A(1.8) = 7.4911, A(1.77) = 13.082, ζ(1.97) − 1 = 0.67398,
  A₀ = 2.0673.
- Margin: (log y/Λ)(200δ + 400X₀^{−0.001}) ≤ 4.1·10²⁵·400e^{−10⁵} ≤ e^{−9.9·10⁴} ✓.

### 23.3 Item 3: small N is correct
- **Single level ✓.** 10Nδ < ½ for N ≤ X₀^{0.01}, so only n₀ = round(N) occurs. If no integer is within the band, 𝔅 = 0.
- **B(n) reproduced independently** (`/tmp/rhscratch/referee-b/xb/bcheck.py`, exact H(m), n ≤ 2·10⁵):
  - max B = B(6) = 5/12 exactly;
  - sup B over n ≥ 10², 10³, 10⁴, 10⁵ is 0.08806, 0.02283, 0.00761, 0.00212, matching §12.1.
  - The "(½ + 2 + 2)/6" in the text is a typo for (½ + ½(2+2))/6.
- **Analytic tail.** It is right with A(1.8) = 7.4911 and B(n) ≤ 0.1374 at n ≥ 10⁶. One fix: "H_e/H_d ≤ (d/e)^{3·10⁻⁶} ≤ λ = 1.0001" holds
  only for d/e ≤ e^{33}. For n₀ up to X₀^{0.01} the factor is ≤ n^{3·10⁻⁶} ≤ e^{3}.
  - So write the tail as 2.152·n^{3·10⁻⁶}·n^{−0.2} ≤ 2.152n^{−0.197}. That is still ≤ 0.14 for n ≥ 10⁶. Harmless.
- **Absorption.** 0.88 − 0.421 − e^{−1200} ≥ 0.45 > 0.33 ✓, given Prop 3.16(A)'s ρ^sh log x ≥ 0.88 (not re-derived here) and
  j₀ ≤ 1.0001/Λ (Huxley, so X₀ ≥ X_Hux is assumed).

### 23.4 Item 4: the structural claim is correct
- **The push-through identity:** the j₀-part of ρ̃ = (1+BK_pt)^{−1}F, with F ∋ j₀B1_{≥X₀} from T̃′ = BT′ + θ/H, is
  j₀(1+BK_pt)^{−1}B1_{≥X₀} = j₀B(1+K_ptB)^{−1}1_{≥X₀} = j₀B𝓡1_{≥X₀}. ✓
- **Why the pieces fail.** (3.5)'s G = K_pt(1−B)F turns the single dipole (1−B)j₀1_{≥X₀} at X₀ into a comb of dipoles at wX₀ with
  weights 1/w. Its response is ≈ j₀δΣ_{w≤N}1/w ≈ j₀δ log N, which is not uniform in N. In the net chain form it cancels.
- **Lemma XB's level formula.** Box smearing at the top step plus propagated D_d through straddling steps gives the split 𝔹₀/𝔹₁/𝔹₂, which
  is consistent with the chain calculus I reviewed in §12–§14. I did not re-derive the τ-source part (Prop 3.8's Duhamel sum).

### 23.5 Λ-uniformity: pending §12′. What it must state
- **(i) SI's η-range.** The application uses η ≈ δ = H(X₀)/X₀ = e^{8(log Λ)² − Λ}. So the hypothesis η ≥ e^{−1.01·10⁸} must become
  η ≥ e^{−1.01Λ}, and (B) then needs J/Λ₁ ≳ Λ.
- **(ii) Λ₁(Λ).** This comes from LP⁺ with c_zf ∝ 1/Λ: c_zf ≈ 0.088/Λ, and L₁ ≈ Λ. So fc_zfΛ₁/L₁ ≥ Λ + O(log Λ₁) gives
  Λ₁ ≈ 13Λ³, which is 1.3·10²⁵ at 10⁸ ✓. Hence J₁ ≈ 1.33ΛΛ₁ ≈ 17Λ⁴.
  - The scaling c_zf(Λ) must be quoted from gap-localPNT §7′.6 for all Λ. "c_zf ≥ 10⁻²⁰ suffices" is a Λ = 10⁸ statement.
- **(iii) The medium range must reach log N ≤ 2J₁(Λ) ≈ 34Λ⁴.** Its (γ) step needs log y ≤ N^{1/8}/C, which holds since
  N ≥ X₀^{0.01}. The margin (log y/Λ)·400X₀^{−0.001} is fine for every Λ.
- **(iv) Small N and absorption** are uniform, given n^{3·10⁻⁶} and j₀ ≤ 1.0001/Λ for X₀ ≥ X_Hux.
- I will check §12′'s cover of all N, for every Λ, against (i)–(iv) when it lands.

### 23.6 §12′ (Λ-uniform) checked against 23.5: complete, with one statement left to fix
- **(i) ✓.** SI(Λ) now has η ∈ [e^{−2Λ}, ½]. The application's η values (1.04δ, δ_w ≥ δe^{−100}, 3.1δ) are all ≥ e^{−Λ−100}.
- **(ii) ✓.**
  - LP⁺: L₁ ≤ 2Λ + 2 log Λ_p + 5 and RHS ≤ 3Λ + 3 log Λ_p + 6. So Λ_p ≥ (2.01Λ)(3.01Λ)Λ/(0.9c_*) = 76Λ³ suffices, and
    Λ₁ = 100Λ³ ✓.
  - (B): J ≥ Λ₁(2Λ + 8 log Λ + 40) ≈ 200Λ⁴, so J₁ = 300Λ⁴ ✓.
  - Region 2: (J/2)^{1/4} ≥ 3.5Λ beats e^{2Λ}·J ✓.
  - Region 1: A ≤ 88ℓ^{−1/4}(¼log ℓ + 1) = 5.7·10⁻⁶ at ℓ = 100Λ⁴ ✓.
  - The c_zf ≥ Λ^{−A} robustness is right: Λ₁ gains a factor Λ^{A−1}, and the middle range's e^{−0.001Λ} still wins.
- **(iii) ✓.** The middle range is e^{0.01Λ} ≤ N ≤ e^{600Λ⁴} = e^{2J₁}.
  - (γ) needs log y ≤ N^{1/8}/C, and log y ≤ 601Λ⁴ ≪ e^{0.00125Λ}.
  - The total is 1.01·601Λ³(200δ + 400e^{−0.001Λ}) ≤ e^{−0.0009Λ}, since 0.0001Λ ≥ 67 ✓.
  - The three ranges are contiguous for every Λ ✓.
- **(iv) ✓.**
  - Single level: 10N^{1.03}δ < ½ for N ≤ e^{0.01Λ}.
  - The λ fix is done well: m^{ε_*} is folded into the Rankin exponent, giving A(1.8 − 3·10⁻⁶) = 7.4915. On the heights
    [X₀, X₀^{1.01}] H is standard, so ε_* ≤ 3·10⁻⁶ ✓.
  - 1.0101·5/12 = 0.4209 ✓.
- **Still to fix: SI's constant versus its t-range** (my 23.1).
  - Region 1's factor is 1 + log((J+τ)/(J−τ)). 61.1 leaves only 0.5% slack over 1.1Φ_∞/log 2 = 60.79, so SI as stated needs τ/J ≤ 0.0025,
    i.e. t ≤ N^{1/400}.
  - The application now has t ≤ 4.01N^{1/20}X₀, i.e. τ/J up to 0.05, a factor ≤ 1.11.
  - Either state SI as 61.1(1 + 2.1τ/J)ητ/J, or cut the (β₁) m-sum at wm ≤ N^{1/400}. The tail weight is then
    ≤ 13.1(N^{1/400}/W₁)^{−0.2} = e^{−J/2000 + 25}, which is negligible. The weighted correction in (β₁) is O(A₂/J), so the totals
    32/131/110 and the e^{−59} margin stand either way.
- **Flag 1, the τ-dependence of BS's ℓ ≥ 10¹⁸ step: confirmed safe.**
  - (H′)'s ε(ℓ) uses the largest junction, U(ℓ; 10³) ≥ U(ℓ; τ).
  - c(u) ≥ K′u²log(1+u) for u ≥ 27 is τ-free. Φ_ben is increasing in κ_Φ = 4τ + 1500. Z1's 0.265τ − 2712 is increasing in τ.
  - The κ-pieces of the remainders (E₃'s κ/m², ρ₁ ≤ 6Φ_ben E_π|D′|) are bounded relative to Φ_ben, and −9·10¹⁷/ℓ and 60·1[u ≥ u₀−2]
    are τ-free.
  - For ℓ < 30τ the base region (F) applies instead.
  - Nit: "ℓΦ_ben ≥ 0.57κ_Φ" holds near u = 2 (c₂·0.933 = 0.58). For general u it is 0.933·0.69κ_Φ/u. Only the monotonicity in τ is
    used, and that holds.
- **Flag 2, §12′.4 "paid once": correct.**
  - 𝓡f = f − K_ptB𝓡f, so m_j = j₀𝓡1_{≥X₀} exactly. Lemma XB is pointwise in y, so m_j needs no B-variation step.
  - m_c's recursion runs on T′_c, which is continuous at X₀ (T′_c(X₀+) = 0), so the X₀-cut flips cost nothing.
  - Hence m·log t ≥ 0.88 − 0.421 − o(1) = 0.459 in range (A).
  - The additive route pays v_X₀ (the H-variation of m_j, 0.258 at N = 2) on top of 𝔅, so 0.459 is the right figure. Prop 3.18 in
    part-F should be routed this way.
- **Conditional on:**
  - part-F's X₀^{1.01} ≤ X_sw(Λ) ≤ exp(X₀^{5/24}/7) and Prop 3.16(A) for all X₀ ≥ max(e^{10⁸}, X_Hux);
  - c_zf ≥ Λ^{−A} (gap-localpnt).
  
  With those, the X₀-jump closure is [P] for every Λ ≥ 10⁸, the small range [P-CA], once the SI statement fix above is made.
- **Closure (after fix-bprime's patch).** The current fix-Bprime §12′ already carries fix (a): SI ≤ 61.1(1 + 2.1τ/J)ητ/J, with
  u_min = (J−τ)/(J+τ). I checked: log((1+x)/(1−x)) ≤ 2.1x for x ≤ 0.1. The (β₁) cut is at wm ≤ N^{1/100} (factor ≤ 1.022, tail
  e^{22.6−0.002J}), and the Φ_ben nit is fixed. I had read a pre-patch copy. **The open item of 23.6 is closed.**
  - The X₀-jump closure is [P] for every Λ ≥ 10⁸, with small N [P-CA].
  - It remains conditional on part-F's X_sw(Λ) window and Prop 3.16(A), and on gap-localpnt's confirmation that c_zf ≥ 0.088/Λ
    (its "merit" and "a" are Λ-independent).
