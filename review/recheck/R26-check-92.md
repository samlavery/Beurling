# R26: independent check of correction #92 (Theorem lp, Landau discs)

**Setup.** A fresh agent did the check; it had not written the repair. It worked on a snapshot of the working tree after the
#92 repair. Its scripts are in `review/recheck/r26/` (python-flint arb balls).

**Verdict: #92 CONFIRMED.** Nothing was blocking or fixable. There were 4 optional cosmetic items and 2 bookkeeping items, and
all have been applied.

## 1. Step 7 extended to |t| ≤ T_y + 1
Each quantity in the explicit-width argument is monotone in |t|:
- L_t, X and Y increase with |t|.
- η = 0.33769/(ΛY) and δ_t decrease with |t|.

The only height condition is Y(t) ≤ Q_y/50.343. Since Y increases, this condition defines an interval of t, and that interval
contains T_y + 1.

The remaining checks:
- **Size of T_y.** T_y ≥ e^{10^{10}}, since log T_y ≥ 10⁴Λ/51 − 500 ≥ 1.96·10¹⁰.
- **Shift from T_y to T_y + 1.** log(T_y+4) − log T_y ≤ 4/T_y.
- **Slack.** 1/50.35 − 1/51 = 2.5313·10⁻⁴. The new Y bound holds for every Q_y from 10⁴Λ to 10⁹Λ.
- **No other limit at T_y.** No other input stops at T_y: (LP-b), (LP-c), the D̂♯ bound, Step 3 and analyticity all hold at
  every height.

## 2. Step 8
- **Disc radius.** R₁ = (κ_L + 0.95)δ_t ≤ 8.7·10⁻¹², far inside the Landau radius 6.8/Λ.
- **Variation of δ_zf.** Its relative change over a disc is ≤ 5.8·10⁻¹⁵.
- **Leftmost point.** It lies inside even the weaker eq:lp-zf (ratio 0.984).
- **Borel–Carathéodory constant.** 187.6.
- **Points below 1/16.** Points with |Im s| < 1/16 are covered by Step 6.

## 3. Consumer margins
Both margins were confirmed, and both increase with their parameters.

| Step | Ratio | Where computed | How it grows |
|---|---|---|---|
| 9 | log T_v / log T₁ = 1.0540388 | threshold, Λ = 10⁸ | 1.072 at Λ = 10^{8.5}, 1.478 at 10¹⁰⁰; also increases in v |
| 10 | 1.25032·10⁶ | Λ_p = 76Λ³, η = e^{−2Λ} | increases in Λ_p and Λ; η = e^{−2Λ} is the worst case |

## 4. Step 9 wording
- At the threshold, log log v = 11.513 + 2 log Λ + 2 log log Λ ≤ 3 log Λ, with margin 1.0808 at Λ = 10⁸. This was checked
  for Λ up to 10¹⁰⁰⁰.
- The condition log v ≥ 1.1·10⁴Λ²(log log v)² is equivalent to ℓ/(log ℓ)² ≥ 1.1·10⁴Λ², with ℓ = log v. The left side
  increases for ℓ > e².

## 5. Sweep (no region extends past its proved range)
- **04e:**
  - Step 6 disc;
  - Step 7 Landau discs (heights up to 4(T_y+1); all inputs are global in t);
  - Step 8 discs and contour (both parts);
  - Step 9 shift, horizontal segments (inside the Step 8 disc at T₁) and the line Re s = η_y;
  - Step 10 rectangle (A)–(C).
- **03:**
  - Lemma designedzero (Cauchy discs inside Lemma ZB's range);
  - Theorem zeros (Rouché circle);
  - Lemma goodheights (i), (ii).

## 6. Rendering
- 142 pages, 15 overfull boxes, 0 undefined references.
- Every edit renders, including "The function h := …".
- No mid-line `%`.

## Findings (applied)
1. **Step 8** (wording predates #92). The bound |log((s−1)/s)| ≤ log 17.01 + π ≤ 6 holds on the discs, where
   |Im s| ≥ 1/16 − 10⁻⁹. The old text stated it only for |t| ≥ 1/16.
2. **Step 8.** The discs use eq:lp-width and eq:lp-zf. Points with |Im s| < 1/16 lie in the disc of Step 6.
3. **Step 7.** Added the reason for T_y ≥ e^{10^{10}}.
4. **Step 9.** "increasing for log v ≥ e²".
5. **Bookkeeping.** Ledger date.
6. **Bookkeeping.** Report list in the AI statement.
