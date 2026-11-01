module

public import RequestProject.BSCert.FX.Core

/-!
# Gluing ranges with fixed-point endpoints
-/

@[expose] public section

namespace BSCert.FX

/-- Glue two ranges with fixed-point endpoints. -/
lemma glueF {P : ℝ → Prop} {a b c : ℤ} (h1 : ∀ x : ℝ, toR a ≤ x → x ≤ toR b → P x)
    (h2 : ∀ x : ℝ, toR b ≤ x → x ≤ toR c → P x) : ∀ x : ℝ, toR a ≤ x → x ≤ toR c → P x := by
  intro x hx1 hx2
  rcases le_total x (toR b) with h | h
  · exact h1 x hx1 h
  · exact h2 x h hx2

end BSCert.FX
