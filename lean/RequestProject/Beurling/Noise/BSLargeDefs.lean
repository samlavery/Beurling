module

public import RequestProject.Beurling.Noise.BSDefs
public import RequestProject.Beurling.Noise.BSZ2Hfun

/-!
# Theorem 5.6, Step 7(ii) (large `ℓ`): the objects of Lemma 5.7

For `u ≥ 2` (so `w_lo = u - 1` and `μ₀ = 0`), `π(dw) = ρ(w-1) dw/(w ρ(u-1))` on `[u-1, ∞)` is a
probability measure (by (R1)). We write `E_π φ = ∫_{(u-1,∞)} φ(w) ρ(w-1)/w dw / ρ(u-1)` (`Epi`).

* `Lam u = Λ(u) = (1+u)² log(2+u)`, `hA u w = h_A(u,w) = h(w) - (1+u)³ log(2+u)`;
* `PhiBen τ ℓ u = Φ_ben = E_π[1 - e^{-κ_Φ/(wℓ)}]`, `jA u = j_A = E_π h_A`,
  `e1 u = (1+w_lo)² ρ(w_lo-1)/(w_lo ρ(u-1))`, `e2 u = ∫ (1+w) ρ(w-1) dw/(w ρ(u-1))`;
* `cfun τ ℓ u = c(u) = ℓ Φ_ben - B j_A - 2K' e₁ - K' e₂` (the first-order profile; `μ₀ = 0`),
  `c0fun u = c₀(u) = c(u) - ℓ Φ_ben`;
* `aprime ℓ u = a'(ℓ,u) = (u - u₀)₊/√ℓ`, `sA ℓ u = s_a = -E_π D_a`, `D_a = a(m,w) - a(ℓ,u)`;
* `epsL τ ℓ = ε(ℓ) = 2·10⁴ U² log(2+U)/ℓ + 30 a'(ℓ,U) + ℓ^{-1/8}`, `U = U(ℓ)`.

The three parts of **Lemma 5.7 (remainder, in ratio form)** are the named statements
`Lemma57Ineq`, `Lemma57Eps` and `Lemma57Slack`.

Our `Σ` (BSDefs) uses the componentwise majorant `etaF` of `η_f`, so it is at most the paper's
`Σ`; `Lemma57Ineq` for our `Σ` is therefore (slightly) stronger than the paper's statement. The
paper's proof of remainder (e) bounds `|∂_m A|`, `|∂_m a|`, `∂_w A`, `∂_w a` separately, so it
applies verbatim.
-/

@[expose] public section

open Real MeasureTheory

namespace BSaias.Large

/-- `E_π φ = ∫_{(u-1,∞)} φ(w) ρ(w-1)/w dw / ρ(u-1)`. -/
noncomputable def Epi (u : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ w in Set.Ioi (u - 1), φ w * Dickman.rho (w - 1) / w) / Dickman.rho (u - 1)

/-- `Λ(u) = (1+u)² log(2+u)`. -/
noncomputable def Lam (u : ℝ) : ℝ := (1 + u) ^ 2 * Real.log (2 + u)

/-- `h_A(u, w) = h(w) - (1+u)³ log(2+u)`. -/
noncomputable def hA (u w : ℝ) : ℝ := hfun w - (1 + u) ^ 3 * Real.log (2 + u)

/-- `Φ_ben = E_π[1 - e^{-κ_Φ/(wℓ)}]`. -/
noncomputable def PhiBen (τ ℓ u : ℝ) : ℝ := Epi u (fun w => 1 - Real.exp (-(kappa τ / (w * ℓ))))

/-- `j_A = E_π h_A`. -/
noncomputable def jA (u : ℝ) : ℝ := Epi u (hA u)

/-- `e₁ = (1 + w_lo)² ρ(w_lo - 1)/(w_lo ρ(u-1))` with `w_lo = u - 1`. -/
noncomputable def e1 (u : ℝ) : ℝ :=
  (1 + (u - 1)) ^ 2 * Dickman.rho (u - 1 - 1) / ((u - 1) * Dickman.rho (u - 1))

/-- `e₂ = ∫_{u-1}^∞ (1+w) ρ(w-1) dw/(w ρ(u-1))`. -/
noncomputable def e2 (u : ℝ) : ℝ := Epi u (fun w => 1 + w)

/-- `c₀(u) = -B j_A - 2K' e₁ - K' e₂`. -/
noncomputable def c0fun (u : ℝ) : ℝ := -(11 * jA u) - 2 * Kp * e1 u - Kp * e2 u

/-- The first-order profile `c(u) = ℓ(Φ_ben - μ₀) - B j_A - 2K' e₁ - K' e₂` (`μ₀ = 0`, `u ≥ 2`). -/
noncomputable def cfun (τ ℓ u : ℝ) : ℝ := ℓ * PhiBen τ ℓ u + c0fun u

/-- `a'(ℓ, u) = ∂_u a = (u - u₀)₊/√ℓ`. -/
noncomputable def aprime (ℓ u : ℝ) : ℝ := max (u - u0 ℓ) 0 / √ℓ

/-- The slack of `a`: `s_a = -E_π D_a`, `D_a = a(m, w) - a(ℓ, u)`. -/
noncomputable def sA (ℓ u : ℝ) : ℝ := -Epi u (fun w => aQ (mOf ℓ w) w - aQ ℓ u)

/-- `ε(ℓ) = 2·10⁴ U² log(2+U)/ℓ + 30 a'(ℓ, U) + ℓ^{-1/8}`, `U = U(ℓ)`. -/
noncomputable def epsL (τ ℓ : ℝ) : ℝ :=
  20000 * Uf τ ℓ ^ 2 * Real.log (2 + Uf τ ℓ) / ℓ + 30 * aprime ℓ (Uf τ ℓ) + ℓ ^ (-(1 / 8 : ℝ))

/-- The range of Lemma 5.7: `τ ≥ 10⁸`, `ℓ ≥ max(10¹⁸, 30τ)` (strictly above `30τ`, as in
the induction step), `2 ≤ u ≤ U(ℓ)`. -/
def LargeRange (τ ℓ u : ℝ) : Prop :=
  100000000 ≤ τ ∧ 30 * τ < ℓ ∧ 1000000000000000000 ≤ ℓ ∧ 2 ≤ u ∧ u ≤ Uf τ ℓ

/-- **Lemma 5.7, main inequality** (04c-saias.tex, lines 326-331):
`ℓΣ ≥ (1 - ε(ℓ))(c(u) + ℓ s_a) - 60·1[u ≥ u₀ - 2] - 9·10¹⁷/ℓ`. -/
def Lemma57Ineq : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (1 - epsL τ ℓ) * (cfun τ ℓ u + ℓ * sA ℓ u)
        - 60 * (if u0 ℓ - 2 ≤ u then 1 else 0) - 900000000000000000 / ℓ ≤ ℓ * Sigma τ ℓ u

/-- **Lemma 5.7, size of `ε`** (line 335): `ε(ℓ) ≤ 0.03`. -/
def Lemma57Eps : Prop :=
  ∀ τ ℓ : ℝ, 100000000 ≤ τ → 30 * τ < ℓ → 1000000000000000000 ≤ ℓ → epsL τ ℓ ≤ 0.03

/-- **Lemma 5.7, the slack `s_a`** (lines 336-337): `s_a ≥ 0.67 a'(ℓ,u) - 0.54/√ℓ` for
`u ≥ u₀ - 2`, and `-0.01 ≤ ℓ s_a ≤ 0` for `u < u₀ - 2`. -/
def Lemma57Slack : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (u0 ℓ - 2 ≤ u → 0.67 * aprime ℓ u - 0.54 / √ℓ ≤ sA ℓ u) ∧
    (u < u0 ℓ - 2 → -0.01 ≤ ℓ * sA ℓ u ∧ ℓ * sA ℓ u ≤ 0)

end BSaias.Large

end
