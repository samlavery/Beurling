module

public import RequestProject.BSCert.Consts.ZetaCert

/-!
# Proposition 5.38, Step 5: the constant `A₀(0.045) ≤ 2.218` for `ℕ`

`A₀(ε') = ∑_{M ≥ 2} H_ord(M) M^{ε'-2} = 1/(2 - ζ(2 - ε')) - 1` (`BSCert.Consts.ordA`,
`ordA_eq_tsum`). Step 5 uses `A₀(0.045) = 2.218`, i.e. `ordA 1.955 ≤ 2.218`, certified here by
the kernel-checked evaluation of `consts.py` (3000 terms and the integral tail bound).
-/

@[expose] public section

namespace BSCert.Consts

/-- `A₀(0.045) = 1/(2 - ζ(1.955)) - 1 ≤ 2.218`. -/
theorem ordA_1955_le : ordA 1.955 ≤ 2.218 := by
  exact (ordA_le_check zH1955 (by decide +kernel : _ ∧ _ ≤ (2218 / 1000 : ℚ))).2.trans
    (by norm_num)

end BSCert.Consts

end
