module

public import RequestProject.Beurling.Noise.BSLargeDefs

/-!
# Lemma 5.7: the remainders `ρ₁, …, ρ₄` and the assembled remainder bound

For `u ≥ 2` (04c-saias.tex, proof of Lemma 5.7, "Decomposition", lines 366-376), with
`D' = D_A + D_a = Q(m, w) - Q(ℓ, u)` (`Dp`) and `D_Φ = -κ_Φ/(wℓ)`:

* `rho1 = ρ₁ = E_π[(1 - e^{D_Φ}) |D'|]`;
* `rho2 = ρ₂ = ½ E_π[D'² e^{D'₊} 1[w ≤ Ū]]`, `Ū = U(ℓ)`;
* `rho3 = ρ₃ = E₁ - E₁^lin`, `ℓ E₁^lin = 2K' e₁`;
* `rho4 = ρ₄ = E₂ - E₂^lin`, `ℓ E₂^lin = K' e₂`;
* `Rsum = ℓ(ρ₁ + ρ₂ + ρ₃ + ρ₄ + E₃ + T)`;
* `lamL = λ = Ū² log(2 + Ū)/ℓ`, `alphaL = α' = a'(ℓ, Ū)`.

`Lemma57Rem` is the remainder bound obtained in the paper by adding (a)–(f) (lines 434-498).
-/

@[expose] public section

open Real MeasureTheory

namespace BSaias.Large

/-- `D' = Q(m, w) - Q(ℓ, u)`. -/
noncomputable def Dp (ℓ u w : ℝ) : ℝ := Qf (mOf ℓ w) w - Qf ℓ u

/-- `ρ₁ = E_π[(1 - e^{-κ_Φ/(wℓ)}) |D'|]`. -/
noncomputable def rho1 (τ ℓ u : ℝ) : ℝ :=
  Epi u (fun w => (1 - Real.exp (-(kappa τ / (w * ℓ)))) * |Dp ℓ u w|)

/-- `ρ₂ = ½ E_π[D'² e^{D'₊} 1[w ≤ Ū]]`. -/
noncomputable def rho2 (τ ℓ u : ℝ) : ℝ :=
  1 / 2 * ((∫ w in Set.Ioc (u - 1) (Uf τ ℓ),
    Dp ℓ u w ^ 2 * Real.exp (max (Dp ℓ u w) 0) * Dickman.rho (w - 1) / w) /
      Dickman.rho (u - 1))

/-- `ρ₃ = E₁ - E₁^lin`. -/
noncomputable def rho3 (τ ℓ u : ℝ) : ℝ := E1term τ ℓ u (paperCut τ ℓ) - 2 * Kp * e1 u / ℓ

/-- `ρ₄ = E₂ - E₂^lin`. -/
noncomputable def rho4 (τ ℓ u : ℝ) : ℝ := E2term τ ℓ u (paperCut τ ℓ) - Kp * e2 u / ℓ

/-- `ℓ(ρ₁ + ρ₂ + ρ₃ + ρ₄ + E₃ + T)`. -/
noncomputable def Rsum (τ ℓ u : ℝ) : ℝ :=
  ℓ * (rho1 τ ℓ u + rho2 τ ℓ u + rho3 τ ℓ u + rho4 τ ℓ u +
    E3term τ ℓ u (paperCut τ ℓ) + Tterm τ ℓ u)

/-- `λ = Ū² log(2 + Ū)/ℓ`. -/
noncomputable def lamL (τ ℓ : ℝ) : ℝ := Uf τ ℓ ^ 2 * Real.log (2 + Uf τ ℓ) / ℓ

/-- `α' = a'(ℓ, Ū)`. -/
noncomputable def alphaL (τ ℓ : ℝ) : ℝ := aprime ℓ (Uf τ ℓ)

/-- **Lemma 5.7, the remainders (a)–(f) added** (04c-saias.tex, lines 434-498, "Assembly"):
for `u ≥ 27`,
`ℓ(ρ₁ + ⋯ + T) ≤ ε₁ c + ε₂ ℓ(s_a)₊ + 2.2·1[u ≥ u₀ - 2] + 1/ℓ`,
`ε₁ = 4300λ + 8.8α'`, `ε₂ = 4.7α' + 0.035 ℓ^{-1/8}`; for `2 ≤ u < 27`,
`ℓ(ρ₁ + ⋯ + T) ≤ ε₁ c + 2.5·10¹⁵/ℓ` with `ε₁ = 14400λ + 8.1α'`.

For `u < 27` the paper writes `ε₁ = 14400λ + α'`; but remainder (a) as stated there,
`ℓρ₁ ≤ (13540λ + 7.6α') ℓΦ_ben`, with `c ≥ 0.944 ℓΦ_ben` only gives `14400λ + 8.1α'`
(the sharper coefficient needs `a' = 0` inside the proof of (a)). Either constant satisfies
`ε₁ ≤ 0.72 ε`, which is all that the conclusion of Lemma 5.7 uses. -/
def Lemma57Rem : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (27 ≤ u → Rsum τ ℓ u ≤ (4300 * lamL τ ℓ + 8.8 * alphaL τ ℓ) * cfun τ ℓ u +
        (4.7 * alphaL τ ℓ + 0.035 * ℓ ^ (-(1 / 8 : ℝ))) * (ℓ * max (sA ℓ u) 0) +
        2.2 * (if u0 ℓ - 2 ≤ u then 1 else 0) + 1 / ℓ) ∧
    (u < 27 → Rsum τ ℓ u ≤ (14400 * lamL τ ℓ + 8.1 * alphaL τ ℓ) * cfun τ ℓ u +
        2500000000000000 / ℓ)

end BSaias.Large

end
