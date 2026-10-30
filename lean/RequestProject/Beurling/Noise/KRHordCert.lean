module

public import RequestProject.BSCert.Consts.ZetaCert

/-!
# Sharper certificates for `A₀(0.03)` and `A₁(0.03)` (correction #103)

`consts.py` lines k2, k3 now certify `A₀(0.03) = A(1.97) ≤ 2.06734` and
`A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.409`; the same kernel-checked evaluation as
`BSCert.Consts.ordA_197_le`, `ordA1_197_le` (3000 terms and the integral tail) gives these.
-/

@[expose] public section

namespace BSCert.Consts

/-- **k2** (correction #103): `A₀(0.03) = A(1.97) ≤ 2.06734`. -/
theorem ordA_197_le_103 : ordA 1.97 ≤ 2.06734 := by
  exact (ordA_le_check zH197 (by decide +kernel : _ ∧ _ ≤ (206734 / 100000 : ℚ))).2.trans
    (by norm_num)

/-- **k3** (correction #103): `A₁(0.03) ≤ 9.409`. -/
theorem ordA1_197_le_103 : ordA1 1.97 ≤ 9.409 := by
  exact (ordA1_le_check (by norm_num) zH197 zD197
    (by decide +kernel : _ ∧ _ ≤ (9409 / 1000 : ℚ))).trans (by norm_num)

end BSCert.Consts

end
