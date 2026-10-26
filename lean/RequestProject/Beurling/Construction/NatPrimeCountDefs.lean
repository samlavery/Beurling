module

public import RequestProject.BSCert.Finite.LogTab

/-!
# Computable checks for `NatPrimeCount` (`π(N) ≤ 2N/log N`)
-/

@[expose] public section

open Finset BSCert.FiniteN

namespace NatPrimeCount

/-- The direct check `π(N) · logHi(N) ≤ 2N · 2^KS`. -/
def piOk (N : ℕ) : Bool := decide (((N + 1).primesBelow.card : ℤ) * logHiN N ≤ 2 * N * 2 ^ KS)

/-- Upper bound for `∑_{n=3}^N 2^KS / log n`. -/
def sumRecip (N : ℕ) : ℚ := ∑ n ∈ Icc 3 N, ((2 : ℚ) ^ KS / logLoN n)

end NatPrimeCount

end
