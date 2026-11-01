module

public import RequestProject.BSCert.Finite.Small
meta import RequestProject.BSCert.Finite.Small

/-!
# `finite_checks.py`, lines 4 and 5

Still checked by `native_decide`; not used by `BModel.corollary_2_2_complete` (nothing imports
this file).
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction

lemma f12_checks : sumLoop (fun _ => 0) f12Hi f12Ok (10 ^ 6) 1 0 0 = true := by native_decide

lemma thr_checks : ∀ p ∈ (range 400).filter Nat.Prime, thrCheck p = true := by native_decide

/-- **`finite_checks.py`, line 4** (`F_{1/2}`, Section 5.8): for `1 ≤ y ≤ 10⁶`,
`y^{-1/2} ∑_{n ≤ y} μ²(n) n^{-1/2} ≤ 1.32964`. -/
theorem F12_le {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 10 ^ 6) : F12 y ≤ 1.32964 :=
  f12_of_check f12_checks hy1 hy2

/-- **`finite_checks.py`, line 5** (Lemma 5.23, threshold mass): for every prime `p < 400`,
`∏_{q < p prime} (1 - 1/q)⁻¹ - 1.8 log p ≤ 0.25`. -/
theorem threshold_mass_small {p : ℕ} (hp : p.Prime) (hp4 : p < 400) :
    ∏ q ∈ (range p).filter Nat.Prime, (1 - 1 / (q : ℝ))⁻¹ - 1.8 * Real.log p ≤ 0.25 :=
  thr_of_check thr_checks hp hp4

end BSCert.FiniteN
