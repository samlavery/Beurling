module

public import RequestProject.Beurling.Noise.BSZ2Errors

/-!
# Region Z2 of the proof of Theorem 5.6: `S(ℓ, u) ≤ Σ(ℓ, u)`, hence `Σ > 0`

Step 7(iii) of the proof of Theorem 5.6 (Beurling–Saias): on region Z2,
`30τ < ℓ ≤ 10¹⁸`, `2 ≤ u ≤ U(ℓ)`, `τ ≥ 10⁸`, the closed-form quantity `S(ℓ, u)` evaluated by the
certificate (`BSCert.Z2.S`, as in `bs_cert_arb.py`) is a lower bound for `Σ(ℓ, u)` of (bs-Sigma)
(`BSaias.Sigma`, with the paper's cut-off `1[w ≤ U(m)]`), provided the two convergence
conditions `r(u-1) > γ₁`, `r(u-1) > γ_max` hold:

* `S_le_Sigma_Z2` : `S(ℓ, u) ≤ Σ(ℓ, u)`; this is the analytic reduction of Step 7(iii)
  (`M_le`, `E1_le`, `E2_le`, `E3_le` and the tail bound `Tterm_le` of Step 6);
* `regionZ2` : `0 < Σ(ℓ, u)` on region Z2, from the certificate `BSCert.z2_certificate_dickman`
  (which also supplies the two convergence conditions).
-/

@[expose] public section

namespace BSaias

/-- **Step 7(iii) of the proof of Theorem 5.6**: on region Z2, the certified closed form `S`
is a lower bound for `Σ`. -/
theorem S_le_Sigma_Z2 {τ ℓ u : ℝ} (hτ : 100000000 ≤ τ) (hℓ1 : 30 * τ < ℓ)
    (_hℓ2 : ℓ ≤ 1000000000000000000) (hu1 : 2 ≤ u) (hu2 : u ≤ Uf τ ℓ)
    (hγ1 : BSCert.Z2.gamma1 ℓ u < Dickman.ratio (u - 1))
    (hγm : BSCert.Z2.gammaMax ℓ u < Dickman.ratio (u - 1)) :
    BSCert.Z2.S Dickman.ratio ℓ u ≤ Sigma τ ℓ u := by
  have h : Z2Hyp τ ℓ u := ⟨hτ, hℓ1, hu1, hu2, hγ1, hγm⟩
  have hM := h.M_le
  have h1 := h.E1_le
  have h2 := h.E2_le
  have h3 := h.E3_le
  have hT := Tterm_le hτ hℓ1 hu1 hu2
  unfold Sigma SigmaGen BSCert.Z2.S
  linarith

/-- **Region Z2 of Theorem 5.6** (Step 7(iii)): `Σ(ℓ, u) > 0` for `τ ≥ 10⁸`, `30τ < ℓ ≤ 10¹⁸`,
`2 ≤ u ≤ U(ℓ)`. Uses the interval certificate `BSCert.z2_certificate_dickman`. -/
theorem regionZ2 {τ ℓ u : ℝ} (hτ : 100000000 ≤ τ) (hℓ1 : 30 * τ < ℓ)
    (hℓ2 : ℓ ≤ 1000000000000000000) (hu1 : 2 ≤ u) (hu2 : u ≤ Uf τ ℓ) :
    0 < Sigma τ ℓ u := by
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨hγ1, hγm, hS⟩ := BSCert.z2_certificate_dickman ℓ u (by linarith) hℓ2 hu1
    (hu2.trans (Uf_le_Ubar hτ hℓ0))
  exact lt_of_lt_of_le hS (S_le_Sigma_Z2 hτ hℓ1 hℓ2 hu1 hu2 hγ1 hγm)

end BSaias

end
