module

public import RequestProject.BSCert.Finite.CM
public import RequestProject.BSCert.Finite.KArith

/-!
# `finite_checks.py`, line 1 (Lemma 5.1(i) for `ℕ`), checked by the kernel

`ψ(N) - ψ(N/2) ≤ 0.6803 N` for `1 ≤ N ≤ 1499`: the window sums `∑_{N/2 < k ≤ N} Λ(k)` are
bounded by running sums of the fixed-point upper bounds `K.vmHiK` (trial division and the
certified `FX.logHi`), checked by `decide +kernel`. (Lines 2 and 6 are in `CMWeak` and, with
the paper's sharp constants, in `CMCertSharp`.)
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction Chebyshev

/-- The check of line 1 at `N` (fixed point): `10⁴ D ≤ 6803 N`. -/
def cm1OkK (N : ℕ) (D : ℤ) : Bool := decide (10000 * D ≤ 6803 * (N : ℤ) * FX.ZI)

lemma cm1_checksK : K.winLoopK K.vmHiK cm1OkK 1498 1 0 = true := by decide +kernel

lemma toR_sum {s : Finset ℕ} (v : ℕ → ℤ) : FX.toR (∑ i ∈ s, v i) = ∑ i ∈ s, FX.toR (v i) := by
  unfold FX.toR; push_cast; rw [Finset.sum_div]

/-- `∑_{N/2 < k ≤ N} Λ(k) ≤ 0.6803 N` for `1 ≤ N ≤ 1499`. -/
theorem cm1K {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 1499) : ∑ k ∈ Ioc (N / 2) N, Λ k ≤ 0.6803 * N := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | hN
  · simp; norm_num
  have h0 : ∑ i ∈ Ioc (1 / 2) 1, K.vmHiK i = 0 := by
    simp [K.vmHiK]
  have hc := K.winLoopK_spec K.vmHiK cm1OkK 1498 1 (by rw [h0]; exact cm1_checksK) N hN (by omega)
  simp only [cm1OkK, decide_eq_true_eq] at hc
  have hc' : FX.toR (10000 * ∑ i ∈ Ioc (N / 2) N, K.vmHiK i) ≤
      FX.toR (6803 * (N : ℤ) * FX.ZI) := FX.toR_le_toR.mpr hc
  have e1 : FX.toR (10000 * ∑ i ∈ Ioc (N / 2) N, K.vmHiK i) =
      10000 * ∑ i ∈ Ioc (N / 2) N, FX.toR (K.vmHiK i) := by
    rw [← toR_sum]; unfold FX.toR; push_cast; ring
  have e2 : FX.toR (6803 * (N : ℤ) * FX.ZI) = 6803 * N := by
    unfold FX.toR; push_cast; field_simp [FX.ZR_pos.ne']
  rw [e1, e2] at hc'
  have hs : ∑ k ∈ Ioc (N / 2) N, Λ k ≤ ∑ i ∈ Ioc (N / 2) N, FX.toR (K.vmHiK i) :=
    sum_le_sum fun k _ => K.vmHiK_spec k
  linarith

/-- **`finite_checks.py`, line 1** (Lemma 5.1(i) for `ℕ`, small `x`): for `1 ≤ x < 1500`,
`ψ(x) - ψ(x/2) ≤ 0.6803 x` (the maximum `0.68024 x` is attained at `x = 5`). -/
theorem psi_sub_psi_half_le_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x < 1500) :
    ψ x - ψ (x / 2) ≤ 0.6803 * x := by
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN2 : N ≤ 1499 := by
    have : N < 1500 := Nat.floor_lt (by linarith) |>.mpr (by exact_mod_cast hx2)
    omega
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hψx : ψ x = ψ (N : ℝ) := by rw [psi_eq_psi_coe_floor]
  have hψ2 : ψ ((N / 2 : ℕ) : ℝ) ≤ ψ (x / 2) := by
    apply psi_mono
    have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self N 2
    linarith
  have hsplit : ψ (N : ℝ) - ψ ((N / 2 : ℕ) : ℝ) = ∑ k ∈ Ioc (N / 2) N, Λ k := by
    rw [psi_natCast, psi_natCast, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (N / 2))
      (Nat.div_le_self N 2)]
    ring
  have := cm1K hN1 hN2
  nlinarith

end BSCert.FiniteN
