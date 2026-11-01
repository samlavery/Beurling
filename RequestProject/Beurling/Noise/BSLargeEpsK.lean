module

public import RequestProject.Beurling.Noise.BSLargeDefs
public import RequestProject.BSCert.FX.Expr
public import RequestProject.BSCert.FX.Cover
public import RequestProject.BSCert.FX.Glue

/-!
# Lemma 5.7, `ε(ℓ) ≤ 0.03` on `[10¹⁸, 10³⁰]`: the fixed-point cell test

`epsBar` and its expression `epsEx` (moved here from `BSLargeEpsCert`), and the cell test
`epsCellF` in the fixed-point arithmetic `BSCert.FX` (kernel-evaluable), with soundness. The
cover is in `BSLargeEpsCert`.
-/

@[expose] public section

open Real BSCert.FX

namespace BSaias.Large

/-- `ε̄(ℓ)` at `τ = 10⁸`, written with `ℓ^{-1/8} = 1/√(ℓ^{1/4})`. -/
noncomputable def epsBar (ℓ : ℝ) : ℝ :=
  20000 * BSCert.Z2.Ubar ℓ * BSCert.Z2.Ubar ℓ * Real.log (2 + BSCert.Z2.Ubar ℓ) / ℓ
    + 30 * BSCert.Z2.UbMu0 ℓ / √ℓ + 1 / √(u0 ℓ)

open BSCert in
/-- The expression `0.03 - ε̄(ℓ)`, environment `[ℓ]`. -/
def epsEx : Ex :=
  .lett (.sqrt (.var 0)) <|                                   -- var 1 = √ℓ
  .lett (.sqrt (.var 1)) <|                                   -- var 2 = u₀
  .lett (.sqrt (2 * .log (.var 0 / 100000000) + 4)) <|        -- var 3 = σ
  .lett (.var 2 * .var 3) <|                                  -- var 4 = Ū - u₀
  .lett (.var 2 + .var 4) <|                                  -- var 5 = Ū
  (3 / 100 : Ex) - (20000 * .var 5 * .var 5 * .log (2 + .var 5) / .var 0
    + 30 * .var 4 / .var 1 + 1 / .sqrt (.var 2))

lemma epsEx_eval (ℓ : ℝ) : BSCert.Ex.eval epsEx [ℓ] = 3 / 100 - epsBar ℓ := by
  simp [epsEx, BSCert.Ex.eval, epsBar, BSCert.Z2.Ubar, BSCert.Z2.UbMu0, BSCert.Z2.u0, u0]

/-- The fixed-point cell test. -/
def epsCellF (a b : ℤ) : Bool := BSCert.Ex.fcheckPos epsEx [⟨a, b⟩]

lemma epsCellF_sound (a b : ℤ) (h : epsCellF a b = true) (ℓ : ℝ) (h1 : toR a ≤ ℓ)
    (h2 : ℓ ≤ toR b) : 0 < 3 / 100 - epsBar ℓ := by
  rw [← epsEx_eval]
  exact BSCert.Ex.fcheckPos_sound (List.Forall₂.cons ⟨h1, h2⟩ List.Forall₂.nil) h

end BSaias.Large

end
