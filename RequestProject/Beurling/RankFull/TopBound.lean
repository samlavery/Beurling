module

public import Mathlib

/-!
# Lemma A.6 (S3)(d): the numeric part of the sure top bound

Lemma A.6 (S3)(d) ends with
`A_top = e^γ log(2z + H(2z)) exp(2.21/Λ + 5H(X₀)/X₀) ≤ 1.8 (log z + 4) e^{2.2/Λ} = A_R e^{2.2/Λ}`,
using `log(2z + H(2z)) ≤ log z + 0.7` and `5H(X₀)/X₀ ≤ e^{-10⁶}`. The only non-trivial constant
is `e^γ < 1.8`.

* `RankFull.eulerMascheroni_lt` : `γ < 0.5815`, from `γ < H₁₂₈ - log 128` (Mathlib's
  `eulerMascheroniConstant_lt_eulerMascheroniSeq'`), with `H₁₂₈` computed exactly;
* `RankFull.exp_eulerMascheroni_lt` : `e^γ < 1.79`;
* `RankFull.log_top_le` : `log(2z + H(2z)) ≤ log z + 0.7` when `H(2z) ≤ 10⁻⁴ · 2z`;
* `RankFull.A_top_le` : **the numeric part of (S3)(d)**, `A_top ≤ A_R e^{2.2/Λ}`;
* `RankFull.A_top_le_Ch` : `A_top ≤ Ch = e^γ log(2z + H(2z)) exp(2.21/Λ + 10⁻⁹)` (Proposition 6.19)
  when `5H(X₀)/X₀ ≤ 10⁻⁹`.

No `native_decide`: `H₁₂₈` is evaluated by `norm_num`.
-/

@[expose] public section

open Real

namespace RankFull

lemma harmonic_128_le : (harmonic 128 : ℝ) ≤ 5.4335 := by
  have h : harmonic 128 ≤ (54335 : ℚ) / 10000 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have : ((harmonic 128 : ℚ) : ℝ) ≤ (((54335 : ℚ) / 10000 : ℚ) : ℝ) := by exact_mod_cast h
  norm_num at this ⊢

/-- `γ < 0.5815`. -/
theorem eulerMascheroni_lt : eulerMascheroniConstant < 0.5815 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  unfold eulerMascheroniSeq' at h
  simp only [show (128 : ℕ) ≠ 0 by norm_num, if_false] at h
  have hlog : Real.log ((128 : ℕ) : ℝ) = 7 * Real.log 2 := by
    rw [show ((128 : ℕ) : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  rw [hlog] at h
  have := Real.log_two_gt_d9
  have := harmonic_128_le
  linarith

/-- `e^γ < 1.79`. -/
theorem exp_eulerMascheroni_lt : Real.exp eulerMascheroniConstant < 1.79 := by
  refine lt_of_lt_of_le (Real.exp_lt_exp.mpr eulerMascheroni_lt) ?_
  have hb := Real.exp_bound (x := (0.5815 : ℝ)) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
  have := (abs_le.mp hb).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

/-- `log(2z + H(2z)) ≤ log z + 0.7` when `H(2z) ≤ 10⁻⁴ · 2z` and `z > 0`. -/
theorem log_top_le {z h : ℝ} (hz : 0 < z) (h0 : 0 ≤ h) (hh : h ≤ 0.0001 * (2 * z)) :
    Real.log (2 * z + h) ≤ Real.log z + 0.7 := by
  have h1 : 2 * z + h ≤ z * 2.0002 := by linarith
  have h2 : Real.log (2 * z + h) ≤ Real.log (z * 2.0002) :=
    Real.log_le_log (by linarith) h1
  rw [Real.log_mul hz.ne' (by norm_num)] at h2
  have h3 : Real.log 2.0002 ≤ 0.7 := by
    rw [show (2.0002 : ℝ) = 2 * 1.0001 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_lt_d9
    have := Real.log_le_sub_one_of_pos (x := (1.0001 : ℝ)) (by norm_num)
    linarith
  linarith

/-- **Lemma A.6 (S3)(d), numeric part**: with `Λ ≥ 10⁸`, `log z ≥ 0`,
`0 ≤ ℓ_top ≤ log z + 0.7` (`ℓ_top = log(2z + H(2z))`) and `η ≤ 10⁻⁸` (`η = 5H(X₀)/X₀`),
`A_top = e^γ ℓ_top exp(2.21/Λ + η) ≤ 1.8 (log z + 4) e^{2.2/Λ}`. -/
theorem A_top_le {Λ Lz ℓtop η : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hLz : 0 ≤ Lz) (hℓ0 : 0 ≤ ℓtop)
    (hℓ : ℓtop ≤ Lz + 0.7) (hη : η ≤ 1e-8) :
    Real.exp eulerMascheroniConstant * ℓtop * Real.exp (2.21 / Λ + η) ≤
      1.8 * (Lz + 4) * Real.exp (2.2 / Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hsplit : Real.exp (2.21 / Λ + η) = Real.exp (2.2 / Λ) * Real.exp (0.01 / Λ + η) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsmall : 0.01 / Λ + η ≤ 0.001 := by
    have : 0.01 / Λ ≤ 0.01 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
    norm_num at this ⊢; linarith
  have hexp : Real.exp (0.01 / Λ + η) ≤ 1.0011 := by
    have h1 := Real.exp_le_exp.mpr hsmall
    have hb := Real.exp_bound (x := (0.001 : ℝ)) (by norm_num [abs_of_pos]) (n := 2) (by norm_num)
    have := (abs_le.mp hb).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hg := exp_eulerMascheroni_lt
  have hE := Real.exp_pos (2.2 / Λ)
  rw [hsplit]
  have hg0 := Real.exp_pos eulerMascheroniConstant
  have hx0 := Real.exp_pos (0.01 / Λ + η)
  have key : Real.exp eulerMascheroniConstant * ℓtop * Real.exp (0.01 / Λ + η) ≤
      1.8 * (Lz + 4) := by
    calc Real.exp eulerMascheroniConstant * ℓtop * Real.exp (0.01 / Λ + η)
        ≤ 1.79 * (Lz + 0.7) * 1.0011 := by gcongr
      _ ≤ 1.8 * (Lz + 4) := by nlinarith
  calc Real.exp eulerMascheroniConstant * ℓtop * (Real.exp (2.2 / Λ) * Real.exp (0.01 / Λ + η))
      = Real.exp eulerMascheroniConstant * ℓtop * Real.exp (0.01 / Λ + η) *
          Real.exp (2.2 / Λ) := by ring
    _ ≤ 1.8 * (Lz + 4) * Real.exp (2.2 / Λ) := mul_le_mul_of_nonneg_right key hE.le

/-- `A_top ≤ Ch` (Proposition 6.19): `e^γ ℓ_top exp(2.21/Λ + η) ≤ e^γ ℓ_top exp(2.21/Λ + 10⁻⁹)`
for `η ≤ 10⁻⁹`, `ℓ_top ≥ 0`. -/
theorem A_top_le_Ch {Λ ℓtop η : ℝ} (hℓ0 : 0 ≤ ℓtop) (hη : η ≤ 1e-9) :
    Real.exp eulerMascheroniConstant * ℓtop * Real.exp (2.21 / Λ + η) ≤
      Real.exp eulerMascheroniConstant * ℓtop * Real.exp (2.21 / Λ + 1e-9) := by
  gcongr

end RankFull
