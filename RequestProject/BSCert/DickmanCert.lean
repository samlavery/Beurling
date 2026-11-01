module

public import RequestProject.BSCert.DickmanRatio
public import RequestProject.BSCert.Z2Cert
public import RequestProject.BSCert.AuxCert

/-!
# The Beurling–Saias certificates for the true Dickman ratio

The certificates of Appendix B.1 (`z2_certificate`, `cA_certificate`, `lemV_certificate`,
`lemVExt_certificate`) were stated for any function `r` satisfying the hypothesis
`DickmanRatioFacts r`. Dickman's function is now constructed (`Dickman.rho`, `DickmanFn.lean`)
and the facts (R2)–(R4) and the formula on `[1, 2]` are proved for its ratio
`Dickman.ratio v = ρ(v-1)/(v ρ(v))` (`DickmanRatio.lean`). So the hypothesis is discharged:

* `dickmanRatioFacts` : `DickmanRatioFacts Dickman.ratio`;
* `z2_certificate_dickman`, `cA_certificate_dickman`, `lemV_certificate_dickman`,
  `lemVExt_certificate_dickman` : the certificates for the true Dickman ratio, with no
  hypothesis.
-/

@[expose] public section

namespace BSCert

/-- **The Dickman-ratio facts hold for the true Dickman ratio** `r(v) = ρ(v-1)/(v ρ(v))`
(= `-ρ'(v)/ρ(v)` for `v > 1`): (R2) monotonicity on `[1, ∞)`, the formula `1/(x(1 - log x))` on
`[1, 2]`, (R3) and (R4). -/
theorem dickmanRatioFacts : DickmanRatioFacts Dickman.ratio where
  mono := Dickman.ratio_monotoneOn
  exact_one_two := fun _ h1 h2 => Dickman.ratio_one_two h1 h2
  recursion := fun _ hv => Dickman.ratio_recursion (by linarith)
  upper := fun _ _ hx hδ0 hδ1 => Dickman.ratio_upper (by linarith) hδ0 hδ1

/-- **Region Z2 of the Beurling–Saias certificate** for the true Dickman ratio: for
`ℓ ∈ [3·10⁹, 10¹⁸]` and `u ∈ [2, Ū(ℓ)]`, `r(u-1) > γ₁(ℓ,u)`, `r(u-1) > γ_max(ℓ,u)` and
`S(ℓ, u) > 0`. -/
theorem z2_certificate_dickman (ℓ u : ℝ)
    (hℓ1 : 3000000000 ≤ ℓ) (hℓ2 : ℓ ≤ 1000000000000000000) (hu1 : 2 ≤ u) (hu2 : u ≤ Z2.Ubar ℓ) :
    Z2.gamma1 ℓ u < Dickman.ratio (u - 1) ∧ Z2.gammaMax ℓ u < Dickman.ratio (u - 1) ∧
      0 < Z2.S Dickman.ratio ℓ u :=
  Z2.z2_certificate dickmanRatioFacts ℓ u hℓ1 hℓ2 hu1 hu2

/-- Check (1) of `aux_cert_arb.py` for the true Dickman ratio. -/
theorem cA_certificate_dickman (u : ℝ) (h1 : 27 ≤ u) (h2 : u ≤ 400000) :
    0 < cAMargin Dickman.ratio u :=
  cA_certificate dickmanRatioFacts u h1 h2

/-- Check (2) of `aux_cert_arb.py` for the true Dickman ratio. -/
theorem lemV_certificate_dickman (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 1000000) :
    0 < lemVLHS Dickman.ratio u :=
  lemV_certificate dickmanRatioFacts u h1 h2

/-- Check (3) of `aux_cert_arb.py` for the true Dickman ratio. -/
theorem lemVExt_certificate_dickman (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 2) :
    0 < lemVExtLHS Dickman.ratio u :=
  lemVExt_certificate dickmanRatioFacts u h1 h2

end BSCert
