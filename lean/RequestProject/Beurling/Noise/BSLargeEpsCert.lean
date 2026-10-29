module

public import RequestProject.Beurling.Noise.BSLargeDefs
public import RequestProject.BSCert.Cover
meta import RequestProject.BSCert.Cover

/-!
# Lemma 5.7: `ε(ℓ) ≤ 0.03` on `[10¹⁸, 10³⁰]` (interval cover)

At the worst case `τ = 10⁸`, `ε̄(ℓ) = 2·10⁴ Ū² log(2+Ū)/ℓ + 30 (Ū - u₀)/√ℓ + ℓ^{-1/8}` with
`Ū = BSCert.Z2.Ubar ℓ`. We check `0.03 - ε̄(ℓ) > 0` on `[10¹⁸, 10³⁰]` by the certified interval
arithmetic of `BSCert` (`Ex`, `cover`), with cells of ratio `1.001`.
-/

@[expose] public section

open Real

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

/-- The cell test. -/
def epsCell (a b : ℚ) : Bool := BSCert.Ex.checkPos epsEx [⟨a, b⟩]

lemma epsCell_sound (a b : ℚ) (h : epsCell a b = true) (ℓ : ℝ) (h1 : (a : ℝ) ≤ ℓ)
    (h2 : ℓ ≤ (b : ℝ)) : 0 < 3 / 100 - epsBar ℓ := by
  rw [← epsEx_eval]
  exact BSCert.Ex.checkPos_sound (List.Forall₂.cons ⟨h1, h2⟩ List.Forall₂.nil) h

theorem eps_cover_ok :
    BSCert.cover epsCell 0 (BSCert.gstep (1001 / 1000)) 40000 (10 ^ 18) (10 ^ 30) = true := by
  native_decide

/-- `ε̄(ℓ) < 0.03` on `[10¹⁸, 10³⁰]`. -/
theorem epsBar_lt_cert {ℓ : ℝ} (h1 : 1000000000000000000 ≤ ℓ)
    (h2 : ℓ ≤ 1000000000000000000000000000000) : epsBar ℓ < 3 / 100 := by
  have := BSCert.cover_sound (fun ℓ => 0 < 3 / 100 - epsBar ℓ) epsCell epsCell_sound 0 _ 40000
    _ _ eps_cover_ok ℓ (by norm_num; exact h1) (by norm_num; exact h2)
  simp only at this
  linarith

end BSaias.Large

end
