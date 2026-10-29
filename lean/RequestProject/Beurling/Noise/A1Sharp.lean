module

public import RequestProject.BSCert.Consts.ZetaCert
meta import RequestProject.BSCert.Consts.ZetaCert

/-!
# A sharper certificate for `A₁(0.03)`

`consts.py` (line k3) certifies `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.42`
(`BSCert.Consts.ordA1_197_le`). Corollary 5.17(b) needs `½ λ₀ A₁(0.03) ≤ 4.71` with
`λ₀ = exp(2.1 H(X₀)/X₀) > 1`, which `9.42` does not quite give; the paper's numerical value is
`9.409`. The same interval evaluation (3000 terms and the integral tail bound) gives `≤ 9.41`.
-/

@[expose] public section

namespace BSCert.Consts

lemma check_k3_sharp : optLe (ordA1HiQ (197 / 100) 3000) (941 / 100) = true := by native_decide

/-- `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.41`. -/
theorem ordA1_197_le_sharp : ordA1 1.97 ≤ 9.41 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_k3_sharp
  have h := ordA1_le (by norm_num) (inv_log_two_le (by norm_num)) (by norm_num) ha
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- The numerical conditions of Corollary 5.17(b) for `ℕ`: if `1 ≤ λ₀ ≤ 1.001` then
`1 + ½λ₀A₀(0.03) ≤ 2.04` and `½λ₀A₁(0.03) ≤ 4.71`. -/
theorem cor517_numerics {lam0 : ℝ} (h0 : 0 ≤ lam0) (h1 : lam0 ≤ 1.001) :
    1 + 1 / 2 * lam0 * ordA 1.97 ≤ 2.04 ∧ 1 / 2 * lam0 * ordA1 1.97 ≤ 4.71 := by
  have hA := ordA_197_le
  have hA1 := ordA1_197_le_sharp
  constructor <;> nlinarith

end BSCert.Consts

end
