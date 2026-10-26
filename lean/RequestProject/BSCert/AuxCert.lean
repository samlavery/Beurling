module

public import RequestProject.BSCert.AuxDefs
meta import RequestProject.BSCert.AuxDefs

/-!
# The one-variable checks of `aux_cert_arb.py`, verified

The three covers are run by `native_decide` (cells of ratio `1.001`, `1.001` and `1.0005`, as
in the script; every cell passes at its first evaluation), and combined with the soundness of
the cell tests to give the real-valued statements.
-/

@[expose] public section

namespace BSCert

/-- The `r_low` table used by the one-variable checks (`r_low(n)` for `2 ≤ n < 400002`). -/
def auxTable : Array ℚ := rlowTable 400000

theorem cA_cover_ok :
    cover (cACell auxTable) 0 (gstep (1001 / 1000)) 20000 27 400000 = true := by
  native_decide

theorem lemV_cover_ok :
    cover (lemVCell auxTable) 0 (gstep (1001 / 1000)) 20000 1 1000000 = true := by
  native_decide

theorem lemVExt_cover_ok :
    cover (lemVExtCell auxTable) 0 (gstep (10005 / 10000)) 20000 1 2 = true := by
  native_decide

/-- **Check (1) of `aux_cert_arb.py`** (positivity of `c₀`, proof of Theorem 5.6):
for `27 ≤ u ≤ 4·10⁵`,
`5 log(1+u) [3(1-1/r(u)) - (1+u)³ log(2+u)/(u³ log(1+u)) - 144(1+u)² log(2+u)/(u³ r(u-1)² log(1+u))]
 - 2 r(u-1) - (u+1)/u² > log(1+u)`. -/
theorem cA_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 27 ≤ u)
    (h2 : u ≤ 400000) : 0 < cAMargin r u :=
  cover_sound (fun u => 0 < cAMargin r u) _
    (cACell_sound hr (rlowTable_ok hr 400000)) 0 _ 20000 27 400000 cA_cover_ok u
    (by norm_num; exact h1) (by norm_num; exact h2)

/-- **Check (2) of `aux_cert_arb.py`** (the one-step inequality (28) of Lemma 5.3, without
`X(u)`, at `L_z = max(100, u)`): positive for `1 ≤ u ≤ 10⁶`. -/
theorem lemV_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 1 ≤ u)
    (h2 : u ≤ 1000000) : 0 < lemVLHS r u :=
  cover_sound (fun u => 0 < lemVLHS r u) _
    (lemVCell_sound hr (rlowTable_ok hr 400000)) 0 _ 20000 1 1000000 lemV_cover_ok u
    (by norm_num; exact h1) (by norm_num; exact h2)

/-- **Check (3) of `aux_cert_arb.py`** (the one-step inequality (28) on `[1, 2]` at `L_z = 100`,
with `X(u)` and the allowance `2 K_M r(u)(e^{0.141} - 1)`): positive for `1 ≤ u ≤ 2`. -/
theorem lemVExt_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (u : ℝ) (h1 : 1 ≤ u)
    (h2 : u ≤ 2) : 0 < lemVExtLHS r u :=
  cover_sound (fun u => 0 < lemVExtLHS r u) _
    (lemVExtCell_sound hr (rlowTable_ok hr 400000)) 0 _ 20000 1 2 lemVExt_cover_ok u
    (by norm_num; exact h1) (by norm_num; exact h2)

end BSCert
