module

public import RequestProject.Beurling.Noise.MarginChain2

/-!
# Step 5 of Proposition 5.38 with the head bound valid over `𝒩`

`KR.Chain.hv_of_chain'` : `hv_of_chain` with the head bound `1 + 2.2181` (the certified
`A₀(0.045) ≤ 2.218` plus the tail of `𝒩` above `X₀⁻`, `Margin.Rec.hhead_loc`) in place of the
exact `1 + A₀(0.045)` of `ℕ`, which has no slack over `𝒩`; the constant `6.5` is unchanged
(`2(1 + 2.2181) + 0.06 = 6.4962`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.Chain

/-- **Step 5** (`hv_of_chain`) with the head bound `1 + 2.2181` valid over `𝒩`; the constant
`6.5` is unchanged. -/
theorem hv_of_chain' {t ES j v : ℝ} (S1 S2 : Finset ℕ) (A V : ℕ → ℝ) (ht : 1 < t)
    (hES : 0 ≤ ES) (hA : ∀ M ∈ S1, 0 ≤ A M) (hV0 : ∀ M ∈ S1, 0 < V M)
    (hv : v ≤ ∑ M ∈ S1, A M * (ES / Real.log (t / V M)) + j * ∑ M ∈ S2, A M)
    (hhead : ∑ M ∈ S1.filter (fun M => V M ≤ √t), A M ≤ 1 + 2.2181)
    (htail : ∑ M ∈ S1.filter (fun M => ¬ V M ≤ √t), A M * (ES / Real.log (t / V M)) ≤
      0.06 * ES / Real.log t) :
    v * Real.log t ≤ 6.5 * ES + Real.log t * (j * ∑ M ∈ S2, A M) := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have hhd : ∀ M ∈ S1.filter (fun M => V M ≤ √t),
      A M * (ES / Real.log (t / V M)) ≤ A M * (2 * ES / Real.log t) := by
    intro M hM
    obtain ⟨hM1, hM2⟩ := Finset.mem_filter.mp hM
    have hV := hV0 M hM1
    have hl : Real.log t / 2 ≤ Real.log (t / V M) := by
      rw [Real.log_div (by linarith) hV.ne']
      have := Real.log_le_log hV hM2
      have hsq : Real.log √t = Real.log t / 2 := Real.log_sqrt (by linarith)
      linarith
    apply mul_le_mul_of_nonneg_left _ (hA M hM1)
    rw [div_le_div_iff₀ (by linarith) hlt]
    nlinarith
  have hsplit := (Finset.sum_filter_add_sum_filter_not S1 (fun M => V M ≤ √t)
    (fun M => A M * (ES / Real.log (t / V M)))).symm
  have hH : ∑ M ∈ S1.filter (fun M => V M ≤ √t), A M * (ES / Real.log (t / V M)) ≤
      (1 + 2.2181) * (2 * ES / Real.log t) := by
    refine (Finset.sum_le_sum hhd).trans ?_
    rw [← Finset.sum_mul]
    have : 0 ≤ 2 * ES / Real.log t := by positivity
    exact mul_le_mul_of_nonneg_right hhead this
  have hsum : ∑ M ∈ S1, A M * (ES / Real.log (t / V M)) ≤ 6.5 * ES / Real.log t := by
    rw [hsplit]
    have e1 : (1 + 2.2181) * (2 * ES / Real.log t) + 0.06 * ES / Real.log t =
        6.4962 * ES / Real.log t := by ring
    have e2 : 6.4962 * ES / Real.log t ≤ 6.5 * ES / Real.log t :=
      div_le_div_of_nonneg_right (by nlinarith) hlt.le
    linarith
  have := mul_le_mul_of_nonneg_right hv hlt.le
  have e3 : (∑ M ∈ S1, A M * (ES / Real.log (t / V M))) * Real.log t ≤ 6.5 * ES := by
    have := mul_le_mul_of_nonneg_right hsum hlt.le
    rwa [div_mul_cancel₀ _ hlt.ne'] at this
  nlinarith

end KR.Chain

end
