# R13: check of correction #69, the explicit o(1)/≪ terms in §4

The checker was margin-var-check, a fresh AI agent that is independent of gap-localpnt. It checked a snapshot of the live
tree taken at 10:33 PDT on 2026-10-23. It was not allowed to write files, so the lead saved its message here.

In that snapshot, #70 was already partly applied. #69 was checked as it reads there; #70 was checked only where it overlaps
(§5), and gets its own full check separately.

## Verdict: CORRECT

0 BLOCKING, 0 FIXABLE, 3 COSMETIC.

The main finding of #69 is confirmed. The old o(1) convention was too small, and the new convention, o(1) ≤ Λ⁻³, covers the
itemised list in Step 5.

## 1. The main finding and Step 5 of Prop g1(B) (04f:289–306)

### The old convention fails

- The old convention was exp(−10⁻³X₀^{0.005}/Λ) + 10⁵Λ²/X₀², which is about e^{−2·10⁸} at Λ = 10⁸.
- The σ_A term alone is e^{−80.2} at Λ = 10⁸, e^{−89.4} at Λ = 10⁹ and e^{−117} at Λ = 10¹².
- The ν̄ and threshold terms also exceed the old bound.

### The assumptions of Step 5 all hold

- log x ≥ e^{Λ/100}: this is the definition of X_sw.
- 1/δ ≤ x^{0.02}: from Step 3.
- δ ≤ log⁻⁴x: since γ_* ≥ 1.
- log(1/δ) ≤ 0.6√log x: since 1/δ ≤ Γ²log⁴x + X₀^{1/2}, log(1/δ) ≤ max(c_LP√log x/2 + 4 log log x, Λ/2) + log 2.
- H(x) ≤ x^{0.01}.
- **One more fact is used.** The item 160 log^{−1.5}x needs log H = 8(log log x)². Step 3 states this (04f:229–230). It holds
  because range (B) lies off the raised range: ℓ ≥ Λ/100 gives 4ℓ² − log 4 > 7.5Λ. With only H ≤ x^{0.01}, that item would be
  about 2.2/log x.

### Each item, re-derived (as a contribution to ρ^sh·log x)

**Step 1.**
- Partial boxes and the local count: (27H + 2K_loc + 6 + 2√x)·log x/(δx) ≈ 2x^{−0.48}log x ≤ x^{−0.4}, with K_loc ≤ H.
- Theorem lp(ii): ≤ e^{−0.4c_LP√log x}, since c_LP√log x ≥ 0.0176e^{Λ/200}/Λ.
- The variation of π₀ over J: ≤ 2.02δ/log x ≤ 3δ/log x.

**Step 2.**
- ν̄ ≤ 128L_u^{−6} + 2.3s₂, which gives ≤ 129 log⁻⁵x.
- NT: 54η·log x ≤ 55e^{−0.99Λ}.
- The boundary term: ≤ x^{−0.9}.

**Step 3.**
- The threshold: the worst case is δ = log⁻⁴x, which gives ≲ 220 log⁻²x(8(log log x)² + 4 log log x + 2). That is far below
  160 log^{−1.5}x.
- The jump at X₀: ≤ log⁻³x.
- ρ_det: ≤ X₀^{−0.08}, with a logarithmic margin of −3.3·10⁵ in arb.
- The resolvable R_j: ≤ log⁻²x.
- σ_A: with C_S = 77, the dyadic sum over L_v > 391Λ² is **1.4533·10⁻³Λ⁻⁴** (arb), within 1.5·10⁻³. The cut is right, since
  e^{5.97} = 391.5.

**Step 4.**
- The average: ≤ e^{−c_LP√log x/6}, plus a second part far below 40 log^{−1.5}x.
- Pointwise: C′ = 29055Λ² ≤ (171Λ)², which gives 19445Λ²X₀⁻² ≤ 2·10⁴Λ²X₀⁻².

**The total.** o(1) ≤ 1.4533·10⁻³Λ⁻⁴ + e^{−0.01Λ} ≤ 1.6·10⁻³Λ⁻⁴ ≤ Λ⁻³.

## 2. The o(1) sites

Every listed site is this term, or this term plus the conversion from log y to log x (≤ X₀^{−0.9}), with one exception:
04-noise:10. It drops ε_N + E_BR ≤ 10⁻¹³, which is larger than Λ⁻³ (C3).

The constants 0.969, 0.959 and 0.819 follow.

## 3. The explicit replacements: all correct

- **04k:430:** ≤ 3.0002H(p) ≤ 3.01H(p).
- **04k:515–519:** 2.597 ≤ 2.7.
- **04a:151:** X₀^{−0.39}.
- **04e:210:** X₀^{−0.09}κ, and the coefficient 1 on y^{θ−1}log y holds, since the actual factor is 0.82.
- **04e:525–528:** the final ≤ 2.01Λ holds, but the intermediate "≤ 2Λ + 640" does not (C1).
- **04f:197–200 and 04f:266.**

## 4. X_LP = exp(10⁵Λ²log²Λ)

- **Step 9's height conditions hold.** log log X_LP = 54.18 ≤ 3 log Λ = 55.26 at Λ = 10⁸, and (1000 + 4 log Λ)² ≈ 1.15·10⁶.
- **K′.** c_LP√log X_LP = 5.566 log Λ, and #69's K′ is consistent with #70's replacement.
- **The remark at 04f:310–313** holds.
- **Other files.** eq:XLP in 06 and the bound at 04x:411 are both consistent.

## 5. log K = O(Λ)

- **Safe as used, with a vast margin.** Any absolute implied constant up to about e^{Λ/200}/(10⁴Λ²) would do.
- **Now explicit.** #70 replaces it with log K ≤ 98 + 5.9 log Λ. That correction gets its own full check separately.

## 6. Comments, row 69 and the build

- **Comments.** All 14 "Logged correction 69" comments are whole-line. Each affected passage reads in full in pdftotext.
- **Row 69** matches the diff, apart from the claim covered by C3.
- **Build.** The snapshot builds with exit 0 and no undefined references. The overfull boxes at 04e:393 (103pt) and 04e:423
  belong to #70. They were fixed in the live tree after the snapshot, and the current build is at the baseline of 15.

## Cosmetic items

**C1. 04e:528.**
- **Defect.** "The left side is ≤ 2Λ + 640" is false. With log Λ_p = log 76 + 3 log Λ, the left side is
  2Λ + 2 log Λ_p + log(2Λ + 20 log Λ_p + 1) + 503.1 ≤ 2Λ + 7 log Λ + 513. That is 2Λ + 641.4 at Λ = 10⁸, and it grows slowly
  with Λ.
- **Fix:** "≤ 2Λ + 7 log Λ + 513 ≤ 2.01Λ".

**C2. The exponent of κ.**
- **Defect.** κ = X₀^{−5/12+0.02} = X₀^{−0.396667}, which is larger than X₀^{−0.3967}.
  - "κ = X₀^{−0.3967}" (04a:151, 04e:210) states a rounding as an equality.
  - "κ ≤ X₀^{−0.3967}" (04f:174) is false as an inequality.
  - 01-setup:76 and 06:203 are pre-existing approximations.
- **Impact:** none, because every use has a margin of at least X₀^{0.006}.
- **Fix:** write κ = X₀^{−0.39666…} ≤ X₀^{−0.3966}.

**C3. 04-noise:10.**
- **Defect.** It drops ε_N + E_BR ≤ 10⁻¹³.
- **Fix:** write "0.97 − o(1) − ε_N − E_BR − j_{X₀}(x)".

**A note on Step 5.** Its list of assumptions could also state log H(x) = 8(log log x)² in range (B). Step 3 already states
this, so it is not a defect.

## 7. Check of #70 (the explicit log K in Theorem lp)

This is a separate snapshot of the live tree, taken at 10:37 PDT, after the polish to #70.

**Verdict: CORRECT.** 0 BLOCKING, 0 FIXABLE, 1 COSMETIC (C4).

### The kernel
- h₀ = β^{*19}(x+2), with β = 19·1_{[0,1/19]}. It is ≥ 0, has ∫h₀ = 1 and support [−2,−1], and its transform is
  ĥ₀ = e^{−2w}β̂^{19}.
- |β̂| ≤ e^{(Re w)₊/19}·min(1, 38/|w|), and min(1, 38/|w|) ≤ 76/(1+|w|). So |ĥ₀| ≤ 76^{19}e^{2|Re w|}(1+|w|)^{−19}, with
  log C_m = 82.2839.
- 20,000 random values of w give a maximum ratio to the bound of 2.3·10⁻⁶.
- h₀ is C^{17}, and the decay follows from the product formula, so nothing needs C^∞.

### The contour pieces
- **The shifted line:** ≤ π⁻¹eC_m·G·log(3T₁/a)·v^{−a}.
- **The segments and the tail:** ≤ e^{−√log v} with the explicit C_m, by a margin of e^{−1.05·10¹³} in arb.
- **The smoothing error:** 6/T + 3v^{θ′−1}.

### The constants of (i)
Checked in arb at log v = log X_LP, 10× and 10⁶× that, for Λ ∈ {10⁸, 10⁹, 10¹²}. All hold:
- √log v ≥ 316Λ log Λ, L_T ≤ 2.01√log v, G ≤ 808√log v, and a ≥ 0.445c_zf/√log v ≥ 2.2c_LP/√log v;
- log(3T₁/a) ≤ 2.02√log v;
- 0.37593/c² = 1213.62Λ² ≤ 1214Λ²;
- log(eC_m/π) + log(1633·1214) = 96.639 ≤ 96.7.

Step 8's height condition T₁ ≤ T_v holds, with a ratio of 1.054 at X_LP for Λ = 10⁸, growing with v and Λ.

### Part (ii)
c_LP√log X_LP = 5.5656 log Λ, and 6 log Λ + 5.5 = 116 ≤ Λ^{0.3}. Hence K′ ≤ e^{98}Λ^{5.9} and log K ≤ 98 + 5.9 log Λ.

### The consumer (Prop g1(B), Step 1)
The claim holds with a vast margin.

**C4 (COSMETIC).** The stated sufficient condition, that c_LP√log x exceeds log K + 2Λ + 5 log log x, was too weak as written.
Both error terms need c_LP√log x/2 > log(2K) + 5 log log x, and the displayed chain gives that only while
log log x ≤ about 0.6Λ.
- **Fixed by the lead.** The text now displays both error terms and uses c_LP√log x ≥ 2(log K + Λ + 10 log√log x) + 10, which
  holds via (0.0176/Λ)√log x ≥ 4Λ + 20 log√log x + 10 for √log x ≥ X₀^{0.005}. The error is then ≤ π₀(x)e^{−Λ}.

### Other checks
- Nothing else used the C^∞ property of h₀.
- 01-setup:70, eq:XLP in §6 and 04x:411 are consistent.
- The mismatch bound at 04f:159–162 agrees with R7's count.
- All nine #70 comments are whole-line. One, at 01-setup:71, sits mid-sentence, but pdftotext shows nothing is swallowed.
- Row 70 matches.
- The build has 15 overfull boxes, the baseline.

### Limitations
Step 7's finite-height width, Step 8's G(L) and the smoothing-error bound were taken as given; they predate #69 and #70.

## 8. Confirmation of the lead's fix of C4 (in c8011c2)

**Verdict: CORRECT.**
- **Γ.** Γ := e^{c_LP√log x/4}, so Γ² = e^{c_LP√log x/2} exactly. Since γ_* ≤ Γ, 1/δ ≤ Γ²log⁴x + X₀^{1/2}.
- **The comparison.** (0.0176/Λ)s ≥ 4Λ + 20 log s + 10 for s ≥ e^{Λ/200}. Together with log K ≤ Λ, this gives
  c√log x ≥ 2(log K + Λ + 10 log√log x) + 10.
- **The two error terms.** They are ≤ 2e^{−5}e^{−Λ} and ≤ 2e^{−10}e^{−1.5Λ}, a total of about 0.014·e^{−Λ} in units of π₀(x).
  So the error is ≤ π₀(x)e^{−Λ}.
- **A nit with no effect.** The displayed bound uses π₀(x) = (1 − 1/x)/log x where the exact factor is 1/log x, so it is low by
  the factor 1 − 1/x. The 0.014 slack absorbs this.
- **Step 5.** Its item e^{−0.4c_LP√log x} still holds.
