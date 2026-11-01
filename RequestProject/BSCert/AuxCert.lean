module

public import RequestProject.BSCert.AuxKCovers

/-!
# The one-variable checks of `aux_cert_arb.py`, verified

The three covers are checked by the kernel (`decide +kernel`) in the fixed-point arithmetic
`BSCert.FX` (`AuxKCovers`: adaptive cells with explicit break points, 572 cells in total instead
of the script's ~25000 cells of ratio `1.001`/`1.0005`), and combined with the soundness of the
cell tests to give the real-valued statements.
-/

@[expose] public section

namespace BSCert

/-- The `r_low` table used by the one-variable checks (`r_low(n)` for `2 ≤ n < 400002`). -/
def auxTable : Array ℚ := rlowTable 400000

/-- **Check (1) of `aux_cert_arb.py`** (positivity of `c₀`, proof of Theorem 5.6):
for `27 ≤ u ≤ 4·10⁵`,
`5 log(1+u) [3(1-1/r(u)) - (1+u)³ log(2+u)/(u³ log(1+u)) - 144(1+u)² log(2+u)/(u³ r(u-1)² log(1+u))]
 - 2 r(u-1) - (u+1)/u² > log(1+u)`. -/
theorem cA_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 27 ≤ u)
    (h2 : u ≤ 400000) : 0 < cAMargin r u :=
  cAK_range hr u (by rw [toR_mulZ]; exact_mod_cast h1) (by rw [toR_mulZ]; exact_mod_cast h2)

/-- **Check (2) of `aux_cert_arb.py`** (the one-step inequality (28) of Lemma 5.3, without
`X(u)`, at `L_z = max(100, u)`): positive for `1 ≤ u ≤ 10⁶`. -/
theorem lemV_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 1 ≤ u)
    (h2 : u ≤ 1000000) : 0 < lemVLHS r u :=
  lemVK_range hr u (by rw [toR_mulZ]; exact_mod_cast h1) (by rw [toR_mulZ]; exact_mod_cast h2)

/-- **Check (3) of `aux_cert_arb.py`** (the one-step inequality (28) on `[1, 2]` at `L_z = 100`,
with `X(u)` and the allowance `2 K_M r(u)(e^{0.141} - 1)`): positive for `1 ≤ u ≤ 2`. -/
theorem lemVExt_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 1 ≤ u)
    (h2 : u ≤ 2) : 0 < lemVExtLHS r u :=
  lemVExtK_range hr u (by rw [toR_mulZ]; exact_mod_cast h1) (by rw [toR_mulZ]; exact_mod_cast h2)

end BSCert
