module

public import RequestProject.BSCert.Consts.ZetaCert
meta import RequestProject.BSCert.Consts.ZetaCert

/-!
# Proposition 5.38, Step 5: the constant `A₀(0.045) ≤ 2.218` for `ℕ`

`A₀(ε') = ∑_{M ≥ 2} H_ord(M) M^{ε'-2} = 1/(2 - ζ(2 - ε')) - 1` (`BSCert.Consts.ordA`,
`ordA_eq_tsum`). Step 5 uses `A₀(0.045) = 2.218`, i.e. `ordA 1.955 ≤ 2.218`, certified here by
the interval evaluation of `consts.py` (3000 terms and the integral tail bound).
-/

@[expose] public section

namespace BSCert.Consts

lemma check_A0_0045 : optLe (ordAHiQ (1955 / 1000) 3000) (2218 / 1000) = true := by
  native_decide

/-- `A₀(0.045) = 1/(2 - ζ(1.955)) - 1 ≤ 2.218`. -/
theorem ordA_1955_le : ordA 1.955 ≤ 2.218 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_A0_0045
  have h := (ordA_le (by norm_num) (by norm_num) ha).2
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

end BSCert.Consts

end
