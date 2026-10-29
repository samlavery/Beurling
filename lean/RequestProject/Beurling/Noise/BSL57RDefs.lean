module

public import RequestProject.Beurling.Noise.BSL57Defs

/-!
# Lemma 5.7: the six remainder bounds (a)–(f), as stated in the paper

Each `Rem*` is exactly one remainder bound of the proof of Lemma 5.7 (04c-saias.tex), in the
ℓ-scaled form in which the paper states it. Notation: `X = K' u² log(1+u)`, `λ = lamL`,
`α' = alphaL`, `ℓΦ_ben = ℓ * PhiBen`, `ℓ(s_a)₊ = ℓ * max s_a 0`, `Ū = U(ℓ)`.

* `RemA` — (a), lines 436-439: `ℓρ₁ ≤ (13540λ + 7.6α') ℓΦ_ben`, and `(540λ + 7.6α') ℓΦ_ben`
  if `u ≥ 27`;
* `RemB` — (b), lines 440-450: `ℓρ₂` ≤ A-part + a-part, i.e. for `u ≥ 27`, `u ≥ u₀ - 2`:
  `4000λX + 4.7α' ℓ(s_a)₊ + 2.54α'√ℓ + 2.1`; for `27 ≤ u < u₀ - 2`: `4000λX + λX`; for
  `u < 27`: `2.3·10¹⁵/ℓ + e^{-u₀/3}`;
* `RemC` — (c), lines 452-455: `ρ₃ ≤ 0` (the paper: `ρ₃ ≤ E₁^lin·1.0001 D'(u-1)₊ = 0`) for
  `u < u₀ + 0.74`, and `ℓρ₃ ≤ 0.72α'X` otherwise;
* `RemD` — (d), lines 456-460: `ℓρ₄ ≤ (0.21λ + 0.004α')X` for `u ≥ 27`, `≤ 2·10⁹/ℓ` for
  `u < 27`;
* `RemE` — (e), lines 461-477: `ℓE₃ ≤ λℓΦ_ben` + A-part + a-part: for `u ≥ 27`, `u ≥ u₀ - 2`:
  `260λX + 0.2α'X`; for `27 ≤ u < u₀ - 2`: `260λX + 10⁻³(λ + α')X`; for `u < 27`:
  `2·10¹¹/ℓ + e^{-u₀/3}`;
* `RemF` — (f), lines 478-485: `T ≤ 0.035 ℓ^{-1/8} s_a` if `Ū - u ≤ (Ū - u₀)/2`, and
  `ℓT ≤ 1/ℓ` otherwise.

`Lemma57RemC` is the assembled bound (lines 488-498) with the λ-coefficient for `u ≥ 27`
corrected from the paper's `4300` to `4900`: adding (a)–(f) as stated gives
`(540 + 1 + 4000 + 1 + 0.21 + 260 + 0.001)λ = 4802.2λ` (the A-part of (b) alone is `4000λ`), so
the paper's `ε₁ = 4300λ + 8.8α'` does not follow from its own remainder bounds. The conclusion
of Lemma 5.7 only uses `ε₁ ≤ 0.72 ε = 14400λ + …`, which `4900λ` satisfies.
-/

@[expose] public section

open Real

namespace BSaias.Large

/-- `X = K' u² log(1+u)`. -/
noncomputable def Xu (u : ℝ) : ℝ := Kp * u ^ 2 * Real.log (1 + u)

/-- **(a)**, lines 436-439. -/
def RemA : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    ℓ * rho1 τ ℓ u ≤ (13540 * lamL τ ℓ + 7.6 * alphaL τ ℓ) * (ℓ * PhiBen τ ℓ u) ∧
    (27 ≤ u → ℓ * rho1 τ ℓ u ≤ (540 * lamL τ ℓ + 7.6 * alphaL τ ℓ) * (ℓ * PhiBen τ ℓ u))

/-- **(b)**, lines 440-450. -/
def RemB : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (27 ≤ u → u0 ℓ - 2 ≤ u → ℓ * rho2 τ ℓ u ≤ 4000 * lamL τ ℓ * Xu u +
      4.7 * alphaL τ ℓ * (ℓ * max (sA ℓ u) 0) + 2.54 * alphaL τ ℓ * √ℓ + 2.1) ∧
    (27 ≤ u → u < u0 ℓ - 2 → ℓ * rho2 τ ℓ u ≤ 4000 * lamL τ ℓ * Xu u + lamL τ ℓ * Xu u) ∧
    (u < 27 → ℓ * rho2 τ ℓ u ≤ 2300000000000000 / ℓ + Real.exp (-(u0 ℓ / 3)))

/-- **(c)**, lines 452-455. -/
def RemC : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (u < u0 ℓ + 0.74 → rho3 τ ℓ u ≤ 0) ∧
    (u0 ℓ + 0.74 ≤ u → ℓ * rho3 τ ℓ u ≤ 0.72 * alphaL τ ℓ * Xu u)

/-- **(d)**, lines 456-460. -/
def RemD : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (27 ≤ u → ℓ * rho4 τ ℓ u ≤ (0.21 * lamL τ ℓ + 0.004 * alphaL τ ℓ) * Xu u) ∧
    (u < 27 → ℓ * rho4 τ ℓ u ≤ 2000000000 / ℓ)

/-- **(e)**, lines 461-477. -/
def RemE : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (27 ≤ u → u0 ℓ - 2 ≤ u → ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 260 * lamL τ ℓ * Xu u + 0.2 * alphaL τ ℓ * Xu u) ∧
    (27 ≤ u → u < u0 ℓ - 2 → ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 260 * lamL τ ℓ * Xu u +
        0.001 * (lamL τ ℓ + alphaL τ ℓ) * Xu u) ∧
    (u < 27 → ℓ * E3term τ ℓ u (paperCut τ ℓ) ≤
      lamL τ ℓ * (ℓ * PhiBen τ ℓ u) + 200000000000 / ℓ + Real.exp (-(u0 ℓ / 3)))

/-- **(f)**, lines 478-485. -/
def RemF : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (Uf τ ℓ - u ≤ (Uf τ ℓ - u0 ℓ) / 2 → Tterm τ ℓ u ≤ 0.035 * ℓ ^ (-(1 / 8 : ℝ)) * sA ℓ u) ∧
    (¬ (Uf τ ℓ - u ≤ (Uf τ ℓ - u0 ℓ) / 2) → ℓ * Tterm τ ℓ u ≤ 1 / ℓ)

/-- The assembled remainder bound (lines 488-498) with the corrected coefficient `4900λ`
for `u ≥ 27` (see the module docstring). -/
def Lemma57RemC : Prop :=
  ∀ τ ℓ u : ℝ, LargeRange τ ℓ u →
    (27 ≤ u → Rsum τ ℓ u ≤ (4900 * lamL τ ℓ + 8.8 * alphaL τ ℓ) * cfun τ ℓ u +
        (4.7 * alphaL τ ℓ + 0.035 * ℓ ^ (-(1 / 8 : ℝ))) * (ℓ * max (sA ℓ u) 0) +
        2.2 * (if u0 ℓ - 2 ≤ u then 1 else 0) + 1 / ℓ) ∧
    (u < 27 → Rsum τ ℓ u ≤ (14400 * lamL τ ℓ + 8.1 * alphaL τ ℓ) * cfun τ ℓ u +
        2500000000000000 / ℓ)

end BSaias.Large

end
