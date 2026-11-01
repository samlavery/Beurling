module

public import RequestProject.BSCert.Consts.ZetaCert

/-!
# A sharper certificate for `A₁(0.03)`

`consts.py` (line k3) certifies `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.42`
(`BSCert.Consts.ordA1_197_le`). Corollary 5.17(b) needs `½ λ₀ A₁(0.03) ≤ 4.71` with
`λ₀ = exp(2.1 H(X₀)/X₀) > 1`, which `9.42` does not quite give; the paper's numerical value is
`9.409`. The same interval evaluation (3000 terms and the integral tail bound) gives `≤ 9.41`.
-/

@[expose] public section

namespace BSCert.Consts

/-- `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.41`. -/
theorem ordA1_197_le_sharp : ordA1 1.97 ≤ 9.41 := by
  exact (ordA1_le_check (by norm_num) zH197 zD197
    (by decide +kernel : _ ∧ _ ≤ (941 / 100 : ℚ))).trans (by norm_num)

/-- The numerical conditions of Corollary 5.17(b) for `ℕ`: if `1 ≤ λ₀ ≤ 1.001` then
`1 + ½λ₀A₀(0.03) ≤ 2.04` and `½λ₀A₁(0.03) ≤ 4.71`. -/
theorem cor517_numerics {lam0 : ℝ} (h0 : 0 ≤ lam0) (h1 : lam0 ≤ 1.001) :
    1 + 1 / 2 * lam0 * ordA 1.97 ≤ 2.04 ∧ 1 / 2 * lam0 * ordA1 1.97 ≤ 4.71 := by
  have hA := ordA_197_le
  have hA1 := ordA1_197_le_sharp
  constructor <;> nlinarith

end BSCert.Consts

end
