module

public import RequestProject.BSCert.Z2KChunks.K00
public import RequestProject.BSCert.Z2KChunks.K01
public import RequestProject.BSCert.Z2KChunks.K02
public import RequestProject.BSCert.Z2KChunks.K03
public import RequestProject.BSCert.Z2KChunks.K04
public import RequestProject.BSCert.Z2KChunks.K05
public import RequestProject.BSCert.Z2KChunks.K06
public import RequestProject.BSCert.Z2KChunks.K07
public import RequestProject.BSCert.Z2KChunks.K08
public import RequestProject.BSCert.Z2KChunks.K09
public import RequestProject.BSCert.Z2KChunks.K10
public import RequestProject.BSCert.Z2KChunks.K11
public import RequestProject.BSCert.Z2KChunks.K12
public import RequestProject.BSCert.Z2KChunks.K13
public import RequestProject.BSCert.Z2KChunks.K14
public import RequestProject.BSCert.Z2KChunks.K15
public import RequestProject.BSCert.Z2KChunks.K16
public import RequestProject.BSCert.Z2KChunks.K17
public import RequestProject.BSCert.Z2KChunks.K18
public import RequestProject.BSCert.Z2KChunks.K19
public import RequestProject.BSCert.Z2KChunks.K20
public import RequestProject.BSCert.Z2KChunks.K21
public import RequestProject.BSCert.Z2KChunks.K22
public import RequestProject.BSCert.Z2KChunks.K23
public import RequestProject.BSCert.Z2KChunks.K24
public import RequestProject.BSCert.Z2KChunks.K25
public import RequestProject.BSCert.Z2KChunks.K26
public import RequestProject.BSCert.Z2KChunks.K27
public import RequestProject.BSCert.Z2KChunks.K28
public import RequestProject.BSCert.Z2KChunks.K29
public import RequestProject.BSCert.Z2KChunks.K30
public import RequestProject.BSCert.Z2KChunks.K31

/-!
# The Beurling–Saias certificate, region Z2 (`cert_run_arb.py`), verified

Gluing the 32 pieces gives the statement certified by `cert_run_arb_patched.py`. The pieces are
checked by the kernel (`Z2KChunks/K*.lean`, fixed-point interval arithmetic `BSCert.FX`,
adaptive covers; no `native_decide`):
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
  have h00 := K00.chunk00K hr
  have h01 := glue h00 (K01.chunk01K hr)
  have h02 := glue h01 (K02.chunk02K hr)
  have h03 := glue h02 (K03.chunk03K hr)
  have h04 := glue h03 (K04.chunk04K hr)
  have h05 := glue h04 (K05.chunk05K hr)
  have h06 := glue h05 (K06.chunk06K hr)
  have h07 := glue h06 (K07.chunk07K hr)
  have h08 := glue h07 (K08.chunk08K hr)
  have h09 := glue h08 (K09.chunk09K hr)
  have h10 := glue h09 (K10.chunk10K hr)
  have h11 := glue h10 (K11.chunk11K hr)
  have h12 := glue h11 (K12.chunk12K hr)
  have h13 := glue h12 (K13.chunk13K hr)
  have h14 := glue h13 (K14.chunk14K hr)
  have h15 := glue h14 (K15.chunk15K hr)
  have h16 := glue h15 (K16.chunk16K hr)
  have h17 := glue h16 (K17.chunk17K hr)
  have h18 := glue h17 (K18.chunk18K hr)
  have h19 := glue h18 (K19.chunk19K hr)
  have h20 := glue h19 (K20.chunk20K hr)
  have h21 := glue h20 (K21.chunk21K hr)
  have h22 := glue h21 (K22.chunk22K hr)
  have h23 := glue h22 (K23.chunk23K hr)
  have h24 := glue h23 (K24.chunk24K hr)
  have h25 := glue h24 (K25.chunk25K hr)
  have h26 := glue h25 (K26.chunk26K hr)
  have h27 := glue h26 (K27.chunk27K hr)
  have h28 := glue h27 (K28.chunk28K hr)
  have h29 := glue h28 (K29.chunk29K hr)
  have h30 := glue h29 (K30.chunk30K hr)
  have h31 := glue h30 (K31.chunk31K hr)
  have key := h31 ℓ hℓ1 hℓ2 u hu1 hu2
  simp only [Z2Claim, lt_min_iff, sub_pos] at key
  exact ⟨key.1.1, key.1.2, key.2⟩

end BSCert.Z2
