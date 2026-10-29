module

public import RequestProject.Beurling.Queue6.Defs6

/-!
# The cluster bound `M₁(z)` is at most the smooth majorant `M̄₁` (§6.1)

`M₁(z) = r₀ + φ(r₀) + 1` with the integer `r₀ = ⌈L/(3ℓ)⌉ + 3` is at most
`M̄₁(z) = r̄₀ + φ(r̄₀) + 1`, `r̄₀ = L/(3ℓ) + 4`, and `M̄₁` is non-decreasing from `X₀/2` on
(Theorem 6.23(c)). Hence the cluster events `E_cl(z)` at the heights `z ≤ 4u/(log u)^{11} ≤ u/2`
give `ClusterUpTo` with the threshold `M_q(u) = M̄₁(max(X₀, u/2))`, and with `M̄₁(v)`.
-/

@[expose] public section

open Set Real Construction BModel CaplLink QueueMono BSCert.Capl

namespace Queue6

variable {X₀ : ℕ}

/-- `M̄₁` is non-decreasing on `[X₀/2, ∞)`. -/
lemma capM1_mono_half (hX : 10 ^ 8 ≤ Real.log X₀) {z w : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z)
    (hzw : z ≤ w) : capM1 X₀ z ≤ capM1 X₀ w := by
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hz0 : 0 < z := by linarith
  have hlz : Real.log X₀ - 1 ≤ Real.log z := by
    have := Real.log_le_log (by positivity) hz
    rw [Real.log_div hX0.ne' (by norm_num)] at this
    linarith [Real.log_two_lt_d9]
  have hlz0 : 0 < Real.log z := by linarith
  have hS : capS X₀ z ≤ capS X₀ w := by
    unfold capS
    have := Real.log_le_log hlz0 (Real.log_le_log hz0 hzw)
    linarith
  have hl : 1 ≤ 2 * Real.log (Real.log X₀) + capS X₀ z := by
    rw [ell_eq, Real.le_log_iff_exp_le hlz0]
    have := Real.exp_one_lt_d9; linarith
  exact Mbar1_mono sHroot_le_six gstar_sHroot_le (Real.log_nonneg (by linarith)) hl hS

/-- **`M₁(z) ≤ M̄₁(z)`** for `z ≥ X₀/2`. -/
lemma M1cl_le_capM1 (hX : 10 ^ 8 ≤ Real.log X₀) {z : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z) :
    M1cl X₀ z ≤ capM1 X₀ z := by
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hz0 : 0 < z := by linarith
  have hlz : Real.log X₀ - 1 ≤ Real.log z := by
    have := Real.log_le_log (by positivity) hz
    rw [Real.log_div hX0.ne' (by norm_num)] at this
    linarith [Real.log_two_lt_d9]
  have hlz0 : 0 < Real.log z := by linarith
  have hll : 1 ≤ Real.log (Real.log z) := by
    rw [Real.le_log_iff_exp_le hlz0]
    have := Real.exp_one_lt_d9; linarith
  have hell := ell_eq (X₀ : ℝ) z
  unfold M1cl capM1 Mbar1 cAt logcAt Covers.phi
  simp only
  set c := Real.exp (logc sHroot (Real.log X₀) (capS X₀ z))
  set r := rbar0 (Real.log X₀) (capS X₀ z)
  have hr : r = Real.log z / (3 * Real.log (Real.log z)) + 4 := by
    simp only [r, rbar0]; rw [hell, Real.exp_log hlz0]
  have hr0 : ((r0At z : ℕ) : ℝ) ≤ r := by
    unfold r0At; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.log z / (3 * Real.log (Real.log z)) by positivity)
    rw [hr]; linarith
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hq : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hn0 : (0 : ℝ) ≤ (r0At z : ℕ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hr0 hq]

/-- **The cluster threshold is at most `M̄₁` higher up**: `M₁(z) ≤ M̄₁(w)` for `X₀/2 ≤ z ≤ w`. -/
lemma M1cl_le (hX : 10 ^ 8 ≤ Real.log X₀) {z w : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z) (hzw : z ≤ w) :
    M1cl X₀ z ≤ capM1 X₀ w :=
  (M1cl_le_capM1 hX hz).trans (capM1_mono_half hX hz hzw)

/-- `zH n ≥ X₀/2`, and the `zH n` are exactly the dyadic heights. -/
lemma zH_ge (n : ℕ) : (X₀ : ℝ) / 2 ≤ zH X₀ n := by
  unfold zH
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  nlinarith

/-- **The cluster events give `ClusterUpTo`** with any threshold `≥ M₁(z)` for `z ≤ Z`. -/
theorem clusterUpTo_of_ecl {θ : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) {ω : JitterΩ} {Z w : ℝ}
    (hw : Z ≤ w) (hcl : ∀ n, zH X₀ n ≤ Z → ω ∈ EclE θ X₀ n) :
    ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀ Z (capM1 X₀ w) := by
  rintro z ⟨n, rfl⟩ hzZ k h1 h2
  have h := hcl n (by unfold zH; exact hzZ) k (by unfold zH; exact h1) (by unfold zH; exact h2)
  unfold zH at h
  refine h.trans (M1cl_le hX ?_ (hzZ.trans hw))
  have := zH_ge (X₀ := X₀) n; unfold zH at this; exact this

end Queue6

end
