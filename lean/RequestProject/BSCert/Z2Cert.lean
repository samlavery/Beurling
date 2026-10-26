module

public import RequestProject.BSCert.Z2Chunks.C00
public import RequestProject.BSCert.Z2Chunks.C01
public import RequestProject.BSCert.Z2Chunks.C02
public import RequestProject.BSCert.Z2Chunks.C03
public import RequestProject.BSCert.Z2Chunks.C04
public import RequestProject.BSCert.Z2Chunks.C05
public import RequestProject.BSCert.Z2Chunks.C06
public import RequestProject.BSCert.Z2Chunks.C07
public import RequestProject.BSCert.Z2Chunks.C08
public import RequestProject.BSCert.Z2Chunks.C09
public import RequestProject.BSCert.Z2Chunks.C10
public import RequestProject.BSCert.Z2Chunks.C11
public import RequestProject.BSCert.Z2Chunks.C12
public import RequestProject.BSCert.Z2Chunks.C13
public import RequestProject.BSCert.Z2Chunks.C14
public import RequestProject.BSCert.Z2Chunks.C15
public import RequestProject.BSCert.Z2Chunks.C16
public import RequestProject.BSCert.Z2Chunks.C17
public import RequestProject.BSCert.Z2Chunks.C18
public import RequestProject.BSCert.Z2Chunks.C19
public import RequestProject.BSCert.Z2Chunks.C20
public import RequestProject.BSCert.Z2Chunks.C21
public import RequestProject.BSCert.Z2Chunks.C22
public import RequestProject.BSCert.Z2Chunks.C23
public import RequestProject.BSCert.Z2Chunks.C24
public import RequestProject.BSCert.Z2Chunks.C25
public import RequestProject.BSCert.Z2Chunks.C26
public import RequestProject.BSCert.Z2Chunks.C27
public import RequestProject.BSCert.Z2Chunks.C28
public import RequestProject.BSCert.Z2Chunks.C29
public import RequestProject.BSCert.Z2Chunks.C30
public import RequestProject.BSCert.Z2Chunks.C31

/-!
# The Beurling–Saias certificate, region Z2 (`cert_run_arb.py`), verified

Gluing the 32 verified pieces gives the statement certified by `cert_run_arb_patched.py`:
on the whole region `3·10⁹ ≤ ℓ ≤ 10¹⁸`, `2 ≤ u ≤ Ū(ℓ)`, the convergence conditions
`r(u-1) > γ₁`, `r(u-1) > γ_max` hold and the closed-form bound `S(ℓ, u)` is positive.
-/

@[expose] public section

namespace BSCert.Z2

/-- **The Beurling–Saias certificate, region Z2** (Appendix B.1; Step 7(iii) of the proof of
Theorem 5.6). For every `ℓ ∈ [3·10⁹, 10¹⁸]` and every `u ∈ [2, Ū(ℓ)]`, where
`Ū(ℓ) = ℓ^{1/4}(1 + √(2 log(ℓ/10⁸) + 4))`:
`r(u-1) > γ₁(ℓ,u)`, `r(u-1) > γ_max(ℓ,u)` and `S(ℓ, u) > 0`.
Here `r` is any function satisfying the Dickman-ratio facts (R2)–(R4) (`DickmanRatioFacts`). -/
theorem z2_certificate {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (ℓ u : ℝ)
    (hℓ1 : 3000000000 ≤ ℓ) (hℓ2 : ℓ ≤ 1000000000000000000) (hu1 : 2 ≤ u) (hu2 : u ≤ Ubar ℓ) :
    gamma1 ℓ u < r (u - 1) ∧ gammaMax ℓ u < r (u - 1) ∧ 0 < S r ℓ u := by
  have h00 := z2_range_sound hr chunk00
  have h01 := glue h00 (z2_range_sound hr chunk01)
  have h02 := glue h01 (z2_range_sound hr chunk02)
  have h03 := glue h02 (z2_range_sound hr chunk03)
  have h04 := glue h03 (z2_range_sound hr chunk04)
  have h05 := glue h04 (z2_range_sound hr chunk05)
  have h06 := glue h05 (z2_range_sound hr chunk06)
  have h07 := glue h06 (z2_range_sound hr chunk07)
  have h08 := glue h07 (z2_range_sound hr chunk08)
  have h09 := glue h08 (z2_range_sound hr chunk09)
  have h10 := glue h09 (z2_range_sound hr chunk10)
  have h11 := glue h10 (z2_range_sound hr chunk11)
  have h12 := glue h11 (z2_range_sound hr chunk12)
  have h13 := glue h12 (z2_range_sound hr chunk13)
  have h14 := glue h13 (z2_range_sound hr chunk14)
  have h15 := glue h14 (z2_range_sound hr chunk15)
  have h16 := glue h15 (z2_range_sound hr chunk16)
  have h17 := glue h16 (z2_range_sound hr chunk17)
  have h18 := glue h17 (z2_range_sound hr chunk18)
  have h19 := glue h18 (z2_range_sound hr chunk19)
  have h20 := glue h19 (z2_range_sound hr chunk20)
  have h21 := glue h20 (z2_range_sound hr chunk21)
  have h22 := glue h21 (z2_range_sound hr chunk22)
  have h23 := glue h22 (z2_range_sound hr chunk23)
  have h24 := glue h23 (z2_range_sound hr chunk24)
  have h25 := glue h24 (z2_range_sound hr chunk25)
  have h26 := glue h25 (z2_range_sound hr chunk26)
  have h27 := glue h26 (z2_range_sound hr chunk27)
  have h28 := glue h27 (z2_range_sound hr chunk28)
  have h29 := glue h28 (z2_range_sound hr chunk29)
  have h30 := glue h29 (z2_range_sound hr chunk30)
  have h31 := glue h30 (z2_range_sound hr chunk31)
  have key := h31 ℓ (by norm_num; exact hℓ1) (by norm_num; exact hℓ2) u hu1 hu2
  simp only [Z2Claim, lt_min_iff, sub_pos] at key
  exact ⟨key.1.1, key.1.2, key.2⟩

end BSCert.Z2
