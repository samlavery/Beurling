module

public import RequestProject.Beurling.Noise.MarginVarRec
public import RequestProject.Beurling.Noise.MarginVarCert
public import RequestProject.Beurling.Noise.MarginVarStep4
public import RequestProject.Beurling.Noise.MarginVarStep6

/-!
# Proposition 5.38, Steps 1–6: summary

* Step 3 (the induction) : `Margin.Var.le_of_super`;
* Step 4 : `Margin.Var.logt_omega_le` (from Lemma 5.21) and `Margin.Var.step4`;
* Step 5 : `Margin.Var.step5_split`, `step5_hv`, and `step5_hv_cert` below, which uses the
  certified `A₀(0.045) ≤ 2.218` (`BSCert.Consts.ordA_1955_le`, for `ℕ`): if the head of the
  chain sum is at most `1 + A₀(0.045)` (the trivial chain plus the ordered-factorisation sum,
  which for `𝒩` agrees with `ℕ` on `M < X₀⁻` — the transfer is the hypothesis `hhead`) and the
  tail is at most `0.06 E_S/log t`, then `v(t) log t ≤ 6.5 E_S + V_{X₀}(t)`;
* Step 6 : `Margin.Var.Bavg_le_add_var`, `Bm_ge`, `prop_5_38_a_of`, `prop_5_38_c_low`,
  `prop_5_38_c_high`.
-/

@[expose] public section

open Finset

namespace Margin.Var

/-- **Step 5** with the certified constant `A₀(0.045) = ordA 1.955 ≤ 2.218`. -/
theorem step5_hv_cert {t ES τ vX VX : ℝ} {v : ℝ} (P : Finset ℝ) (a : ℝ → ℝ)
    (ht : 1 < t) (hES : 0 ≤ ES) (ha : ∀ M ∈ P, 0 ≤ a M) (hP1 : ∀ M ∈ P, 1 ≤ M)
    (hv : v ≤ ∑ M ∈ P, a M * ES / Real.log (t / M) + vX)
    (hhead : ∑ M ∈ P.filter (fun M => M ≤ √t), a M ≤ 1 + BSCert.Consts.ordA 1.955)
    (htail : ∑ M ∈ P.filter (fun M => ¬ M ≤ √t), a M * ES / Real.log (t / M) ≤
      τ * ES / Real.log t)
    (hτ : τ ≤ 0.06) (hVX : vX * Real.log t ≤ VX) :
    v * Real.log t ≤ 6.5 * ES + VX :=
  step5_hv P a ht hES ha hP1 hv hhead htail BSCert.Consts.ordA_1955_le hτ hVX

end Margin.Var

end
