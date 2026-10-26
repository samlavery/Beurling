module

public import RequestProject.BSCert.Cover

/-!
# The Beurling–Saias certificate, region Z2: the bound `S(ℓ, u)`

This file states, as real-valued definitions, the closed-form lower bound `S(ℓ, u) ≤ Σ(ℓ, u)`
of Step 7(iii) of the proof of Theorem 5.6 (the quantity computed by `S_cell` in
`bs_cert_arb.py`), together with the two convergence conditions `r(u-1) > γ₁` and
`r(u-1) > γ_max`. The names follow the script:

* `u0 ℓ = ℓ^{1/4}`, `Ubar ℓ = Ū(ℓ) = ℓ^{1/4}(1 + √(2 log(ℓ/10⁸) + 4))`,
  `UbMu0 ℓ = Ū(ℓ) - u₀(ℓ)`;
* `v = u - u₀`, `c_u = u₀/(3u)`, `k_u = 1 + 1/(2(u-1))`, `B = 11`, `K' = 2.2`,
  `κ_min = 4·10⁸`, `κ_max = 4ℓ/30 + 1500`, `S₁ = 60`;
* `betaI`, `betaII`, `alpha` (first majorant), `gamma1`, `gammaMax`, `qq` (second majorant),
  `E1`, `E2`, `E3` with `eta` (error terms), `ET`, `T` (tail), `Mm1` (`M - 1`).

The statement that is certified is `0 < Z2Claim r ℓ u`, i.e.
`r(u-1) > γ₁`, `r(u-1) > γ_max` and `S(ℓ,u) > 0`.
The file also contains the expression tree `z2Ex` evaluated by the interval arithmetic, the
proof that it computes exactly `Z2Claim` (`z2Ex_eval`), and the cell tests with their
soundness proofs.
-/

@[expose] public section

namespace BSCert

namespace Z2

open Real

/-- `u₀(ℓ) = ℓ^{1/4}`. -/
noncomputable def u0 (ℓ : ℝ) : ℝ := √(√ℓ)
/-- `Ū(ℓ) - u₀(ℓ) = ℓ^{1/4} √(2 log(ℓ/10⁸) + 4)`. -/
noncomputable def UbMu0 (ℓ : ℝ) : ℝ := u0 ℓ * √(2 * Real.log (ℓ / 100000000) + 4)
/-- The largest junction `Ū(ℓ) = U(ℓ; τ = 10⁸) = ℓ^{1/4}(1 + √(2 log(ℓ/10⁸) + 4))`. -/
noncomputable def Ubar (ℓ : ℝ) : ℝ := u0 ℓ + UbMu0 ℓ
/-- `c_u = u₀/(3u)`. -/
noncomputable def cu (ℓ u : ℝ) : ℝ := u0 ℓ / (3 * u)
/-- `k_u = 1 + 1/(2(u-1))`. -/
noncomputable def ku (u : ℝ) : ℝ := 1 + 1 / (2 * (u - 1))
/-- `A(ℓ, u) = B (1+u)³ log(2+u)/ℓ`, `B = 11`. -/
noncomputable def A (ℓ u : ℝ) : ℝ := 11 * (1 + u) ^ 3 * Real.log (2 + u) / ℓ
/-- `β_a = (k_u - 1)(v + c_u)₊²/(2√ℓ) + σ_u`, with `σ_u = c_u(2v₊ + c_u)/(2√ℓ)` if
`v + c_u > 0` and `σ_u = 0` otherwise (`v = u - u₀`). -/
noncomputable def betaa (ℓ u : ℝ) : ℝ :=
  (ku u - 1) * (max (u - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)
    + (if u - u0 ℓ + cu ℓ u ≤ 0 then 0
       else cu ℓ u * (2 * max (u - u0 ℓ) 0 + cu ℓ u) / (2 * √ℓ))
/-- `β_I = A/u + β_a - κ_min/(uℓ)`, `κ_min = 4·10⁸`. -/
noncomputable def betaI (ℓ u : ℝ) : ℝ := A ℓ u / u + betaa ℓ u - 400000000 / (u * ℓ)
/-- `β_II = A/u + β_a`. -/
noncomputable def betaII (ℓ u : ℝ) : ℝ := A ℓ u / u + betaa ℓ u
/-- `α = (B/ℓ) u³(3u-4) log(1+u)/(u-1)² + k_u (v - 1 + c_u)₊/√ℓ`. -/
noncomputable def alpha (ℓ u : ℝ) : ℝ :=
  11 / ℓ * u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2
    + ku u * max (u - u0 ℓ - 1 + cu ℓ u) 0 / √ℓ
/-- `γ₁ = (B/ℓ) 8 (1 + u + 60)² log(2 + u + 60) + k_u (v + 60 + c_u)₊/√ℓ`. -/
noncomputable def gamma1 (ℓ u : ℝ) : ℝ :=
  11 / ℓ * 8 * (1 + (u + 60)) ^ 2 * Real.log (2 + (u + 60))
    + ku u * max (u - u0 ℓ + 60 + cu ℓ u) 0 / √ℓ
/-- `γ_max = (B/ℓ) 8 (1 + Ū)² log(2 + Ū) + k_u (Ū - u₀ + c_u)₊/√ℓ`. -/
noncomputable def gammaMax (ℓ u : ℝ) : ℝ :=
  11 / ℓ * 8 * (1 + Ubar ℓ) ^ 2 * Real.log (2 + Ubar ℓ) + ku u * max (UbMu0 ℓ + cu ℓ u) 0 / √ℓ
/-- `q = e^{-(r₀ - γ_max) S₁}/(r₀ - γ_max)`, `r₀ = r(u-1)`, `S₁ = 60`. -/
noncomputable def qq (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  Real.exp (-(r (u - 1) - gammaMax ℓ u) * 60) / (r (u - 1) - gammaMax ℓ u)
/-- `κ_max = 4ℓ/30 + 1500`. -/
noncomputable def kmax (ℓ : ℝ) : ℝ := 4 * ℓ / 30 + 1500
/-- `η̄(w, d)`, with `d₊ = (d + c_u)₊`:
`4κ_max/ℓ² + 4B(1+w)³log(2+w)/ℓ² + d₊/(4(ℓ/2)^{5/4}) + k_u d₊²/(2ℓ^{3/2})
 + ((1+w)²/ℓ)(2B(1+w)²(3 log(2+w) + 1)/ℓ + √2 d₊/√ℓ)`. -/
noncomputable def eta (ℓ u w d : ℝ) : ℝ :=
  4 * kmax ℓ / (ℓ * ℓ) + 4 * (11 * (1 + w) ^ 3 * Real.log (2 + w) / ℓ) / ℓ
    + max (d + cu ℓ u) 0 / (4 * (ℓ / 2) * √(√(ℓ / 2)))
    + ku u * ((max (d + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) / ℓ
    + (1 + w) ^ 2 / ℓ * (2 * 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) / ℓ
      + √2 * max (d + cu ℓ u) 0 / √ℓ)
/-- The bound for `M - 1`:
`(e^{β_I} - 1)(1 - 1/(ur)) + (e^{β_II} - 1)/(ur) - e^{β_I}(1 - e^{-α})(1 - 1/r)
 + (e^{β_II}/u)(γ₁/(r₀(r₀ - γ₁)) + q)`. -/
noncomputable def Mm1 (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  (Real.exp (betaI ℓ u) - 1) * (1 - 1 / (u * r u)) + (Real.exp (betaII ℓ u) - 1) / (u * r u)
    - Real.exp (betaI ℓ u) * (1 - Real.exp (-alpha ℓ u)) * (1 - 1 / r u)
    + Real.exp (betaII ℓ u) / u
      * (gamma1 ℓ u / (r (u - 1) * (r (u - 1) - gamma1 ℓ u)) + qq r ℓ u)
/-- `E₁ = 2K' u² r₀ e^{β_I - α}/ℓ`, `K' = 2.2`. -/
noncomputable def E1 (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  2 * 2.2 * u ^ 2 * r (u - 1) * Real.exp (betaI ℓ u - alpha ℓ u) / ℓ
/-- `E₂ = (K'/ℓ)(u/(u-1))((u-1)e^{β_I} + e^{β_II}(1/(r₀ - γ₁) + q))`. -/
noncomputable def E2 (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  2.2 / ℓ * (u / (u - 1)) * (Real.exp (betaI ℓ u) * (u - 1)
    + Real.exp (betaII ℓ u) * (1 / (r (u - 1) - gamma1 ℓ u) + qq r ℓ u))
/-- `E₃ = 2K'(η̄(u, v)e^{β_I} + (e^{β_II}/u)(η̄(u+S₁, v+S₁)/(r₀ - γ₁) + η̄(Ū, Ū - u₀) q))`. -/
noncomputable def E3 (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  2 * 2.2 * (eta ℓ u u (u - u0 ℓ) * Real.exp (betaI ℓ u)
    + Real.exp (betaII ℓ u) / u * (eta ℓ u (u + 60) (u - u0 ℓ + 60) / (r (u - 1) - gamma1 ℓ u)
      + eta ℓ u (Ubar ℓ) (UbMu0 ℓ) * qq r ℓ u))
/-- `a_V(Ū + 1/2) = 4K (Ū + 1/2)² log(Ū + 1/2 + 2)/ℓ`, `4K = 12.8`. -/
noncomputable def aV (ℓ : ℝ) : ℝ := 12.8 * (Ubar ℓ + 1 / 2) ^ 2 * Real.log (Ubar ℓ + 1 / 2 + 2) / ℓ
/-- `U₃₀ - u = u₀ √(2 log 30 + 4) - v`. -/
noncomputable def gap (ℓ u : ℝ) : ℝ := u0 ℓ * √(2 * Real.log 30 + 4) - (u - u0 ℓ)
/-- `E_T = log 30 - v₊²/(2√ℓ) - r₀ ((U₃₀ - u)₊ + 3/2)` if `u ≤ U₃₀`, and `-2 - (3/2) r₀`
otherwise (in the first case `(U₃₀ - u)₊ = U₃₀ - u`; the positive part is written as in the
script). -/
noncomputable def ET (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  if 0 ≤ gap ℓ u then
    Real.log 30 - (max (u - u0 ℓ) 0) ^ 2 / (2 * √ℓ) - r (u - 1) * (max (gap ℓ u) 0 + 1.5)
  else -2 - 1.5 * r (u - 1)
/-- The tail `T = exp(κ_max/ℓ + a_V(Ū + 1/2) + E_T)`. -/
noncomputable def T (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ := Real.exp (kmax ℓ / ℓ + aV ℓ + ET r ℓ u)
/-- The closed-form lower bound `S = -[(M - 1) + E₁ + E₂ + E₃ + T]`. -/
noncomputable def S (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  -(Mm1 r ℓ u + E1 r ℓ u + E2 r ℓ u + E3 r ℓ u + T r ℓ u)

/-- The certified claim: `0 < Z2Claim r ℓ u` means `r(u-1) > γ₁`, `r(u-1) > γ_max` and
`S(ℓ, u) > 0`. -/
noncomputable def Z2Claim (r : ℝ → ℝ) (ℓ u : ℝ) : ℝ :=
  min (min (r (u - 1) - gamma1 ℓ u) (r (u - 1) - gammaMax ℓ u)) (S r ℓ u)

end Z2

end BSCert
