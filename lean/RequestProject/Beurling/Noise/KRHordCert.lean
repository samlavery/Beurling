module

public import RequestProject.BSCert.Consts.ZetaCert
meta import RequestProject.BSCert.Consts.ZetaCert

/-!
# Sharper certificates for `A₀(0.03)` and `A₁(0.03)` (correction #103)

`consts.py` lines k2, k3 now certify `A₀(0.03) = A(1.97) ≤ 2.06734` and
`A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.409`; the same interval evaluation as
`BSCert.Consts.ordA_197_le`, `ordA1_197_le` (3000 terms and the integral tail) gives these.
-/

@[expose] public section

namespace BSCert.Consts

lemma check_k2_103 : optLe (ordAHiQ (197 / 100) 3000) (206734 / 100000) = true := by
  native_decide

lemma check_k3_103 : optLe (ordA1HiQ (197 / 100) 3000) (9409 / 1000) = true := by
  native_decide

/-- **k2** (correction #103): `A₀(0.03) = A(1.97) ≤ 2.06734`. -/
theorem ordA_197_le_103 : ordA 1.97 ≤ 2.06734 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_k2_103
  have h := (ordA_le (by norm_num) (by norm_num) ha).2
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **k3** (correction #103): `A₁(0.03) ≤ 9.409`. -/
theorem ordA1_197_le_103 : ordA1 1.97 ≤ 9.409 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_k3_103
  have h := ordA1_le (by norm_num) (inv_log_two_le (by norm_num)) (by norm_num) ha
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

end BSCert.Consts

end
