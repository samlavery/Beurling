module

public import RequestProject.Beurling.Noise.RML12M

/-!
# Step 4 in the paper's filtered form, for the Model's `RestMarginH.h4`

`hS4_12_kap` is `RML12M.hS4_12` with the filter `κ_w(t)` (04g Step 3): from the filtered `h4`
(`log t (o_V + 2η_V + ∑_w κ_w e_w/w) ≤ E_S`) it gives the filtered `hS4` field.
-/

@[expose] public section

open Finset Real BModel Construction

namespace BModel.RML14

variable {X₀ : ℕ} {θ : ℝ}

/-- **Step 4, filtered** (the `hS4` field of `RestMargin`/`RealMarginLoc` in κ-form). -/
theorem hS4_12_kap (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {Mf : ℝ → ℝ} (ES jP b : ℝ)
    (h4 : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t +
        ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
            (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w)) ≤ ES) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t + ∑ w ∈ Margin.Rec.Fset
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
            (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w) ≤
        (RML7.canonP X₀ epsH ES jP).ES / Real.log t := by
  intro t ht htb
  have h1 := RML10.T0_gt_one hX ES jP
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  rw [show (RML7.canonP X₀ epsH ES jP).ES = ES from rfl, le_div_iff₀ hl, mul_comm]
  exact h4 t ht htb

end BModel.RML14

end
