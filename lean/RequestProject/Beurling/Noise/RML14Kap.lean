module

public import RequestProject.Beurling.Noise.RML13Kap

/-!
# Step 4 with and without the filter `κ_w(t)`

The paper's Step 4 (04g, Step 3) sums the Step 2 errors only over the cofactors that pass the
filter, `κ_w(t) = 1`. Since `0 ≤ κ ≤ 1` and the errors are non-negative, the unfiltered bound
implies the filtered one (`hS4_kap_of`), so every earlier `hS4` in the unfiltered form feeds the
filtered field.
-/

@[expose] public section

open Finset

namespace KR.RML14

/-- `∑_{w ∈ F} κ_w (e_w/w) ≤ ∑_{w ∈ F} e_w/w` for non-negative `e`. -/
lemma sum_kap_le (P : BeurlingSystem) (tw : ℕ → ℝ) (t : ℝ) (F : Finset ℕ) (e : ℕ → ℝ)
    (he0 : ∀ w ∈ F, 0 ≤ e w) :
    ∑ w ∈ F, Margin.Rec.kap P tw t w * (e w / KR.Vl P w) ≤ ∑ w ∈ F, e w / KR.Vl P w := by
  refine Finset.sum_le_sum fun w hw => ?_
  have hk := Margin.Rec.kap_mem P tw t w
  have hV := KR.Sharp.Vl_pos P w
  have h0 : 0 ≤ e w / KR.Vl P w := div_nonneg (he0 w hw) hV.le
  calc Margin.Rec.kap P tw t w * (e w / KR.Vl P w) ≤ 1 * (e w / KR.Vl P w) :=
        mul_le_mul_of_nonneg_right hk.2 h0
    _ = e w / KR.Vl P w := one_mul _

/-- **The filtered Step 4 from the unfiltered one**: if `e ≥ 0` and
`o + 2η + ∑_{w ∈ F} e_w/w ≤ R`, then `o + 2η + ∑_{w ∈ F} κ_w e_w/w ≤ R`. -/
theorem hS4_kap_of {P : BeurlingSystem} {tw : ℕ → ℝ} {F : ℝ → Finset ℕ} {e : ℝ → ℕ → ℝ}
    {o η R : ℝ → ℝ} {T0 b : ℝ}
    (he0 : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ F t, 0 ≤ e t w)
    (h : ∀ t, T0 ≤ t → t ≤ b → o t + 2 * η t + ∑ w ∈ F t, e t w / KR.Vl P w ≤ R t) :
    ∀ t, T0 ≤ t → t ≤ b →
      o t + 2 * η t + ∑ w ∈ F t, Margin.Rec.kap P tw t w * (e t w / KR.Vl P w) ≤ R t := by
  intro t ht htb
  have := sum_kap_le P tw t (F t) (e t) (he0 t ht htb)
  linarith [h t ht htb]

end KR.RML14

end
