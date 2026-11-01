module

public import RequestProject.Beurling.Noise.TauNearProofMain

/-!
# Lemma 5.20: the numerical consequences

For the standard width at `P₀ = X₀⁻/2`, `H(P₀) ≤ e^{8(log log P₀)²}` (on `[X₀⁻/2, X₀)` the width
is `H_std`, §5.1), with `ℓ₀ = log P₀ ≥ 10⁷`:

* `Phi_small` : `Φ_a(P₀) ≤ 2·10⁻¹⁴` for `a ≤ 3`;
* `energy_small` : `λ₀ C_N E_η ≤ ½` (`λ₀ ≤ 2`, `C_N ≤ 158`), the hypothesis of
  Propositions 5.18, 5.26 and Lemma 5.27;
* `etaBlk_small` : `2.04 ∑_v s_v ≤ 0.02` (Proposition 5.18, the `∞`-norm bound);
* `thetaStar_small` : `2.04 λ₀ θ_* ≤ 0.02` for `θ_* = 207800 Φ₂(P₀)`;
* `thetaE_small` : `E_θ ≤ 10⁻⁷`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `10⁷ (ℓ + 2)³ e^{8(log ℓ)² - ℓ} ≤ e^{-ℓ/2}` for `ℓ ≥ 10⁷`. -/
theorem num_core {ℓ : ℝ} (hℓ : 10000000 ≤ ℓ) :
    10000000 * (ℓ + 2) ^ 3 * Real.exp (8 * Real.log ℓ ^ 2 - ℓ) ≤ Real.exp (-(ℓ / 2)) := by
  have hℓ0 : 0 < ℓ := by linarith
  set L := Real.log ℓ
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hℓL : ℓ = Real.exp L := (Real.exp_log hℓ0).symm
  -- `(ℓ+2)³ ≤ 2ℓ³ = 2e^{3L}`, `2·10⁷ ≤ e^{17}`
  have h1 : (ℓ + 2) ^ 3 ≤ 2 * ℓ ^ 3 := by nlinarith [sq_nonneg ℓ]
  have h17 : (20000000 : ℝ) ≤ Real.exp 17 := by
    have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := (Real.exp_one_gt_d9).le
    have : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (20000000 : ℝ) ≤ 2.7182818283 ^ 17 := by norm_num
      _ ≤ Real.exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) he 17
  have key : 17 + 3 * L + 8 * L ^ 2 ≤ ℓ / 2 := by
    rcases le_or_gt L 20 with h | h
    · nlinarith
    · have h8 := pow_eight_le_exp hL0
      rw [← hℓL] at h8
      have hL6 : (20 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
      nlinarith [sq_nonneg L, pow_pos (show (0 : ℝ) < L by linarith) 2]
  have hexp : Real.exp (17 + 3 * L + 8 * L ^ 2 - ℓ) =
      Real.exp 17 * ℓ ^ 3 * Real.exp (8 * L ^ 2 - ℓ) := by
    rw [show 17 + 3 * L + 8 * L ^ 2 - ℓ = 17 + (L + L + L) + (8 * L ^ 2 - ℓ) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, ← hℓL]
    ring
  have hE := Real.exp_pos (8 * L ^ 2 - ℓ)
  calc 10000000 * (ℓ + 2) ^ 3 * Real.exp (8 * L ^ 2 - ℓ)
      ≤ 10000000 * (2 * ℓ ^ 3) * Real.exp (8 * L ^ 2 - ℓ) := by gcongr
    _ ≤ Real.exp 17 * ℓ ^ 3 * Real.exp (8 * L ^ 2 - ℓ) := by
        have : 0 ≤ ℓ ^ 3 * Real.exp (8 * L ^ 2 - ℓ) := by positivity
        nlinarith
    _ = Real.exp (17 + 3 * L + 8 * L ^ 2 - ℓ) := hexp.symm
    _ ≤ Real.exp (-(ℓ / 2)) := Real.exp_le_exp.mpr (by linarith)

/-- **`Φ_a(X₀⁻/2) ≤ 2·10⁻¹⁴`** for `a ≤ 3`, for the standard width at `X₀⁻/2`. -/
theorem Phi_small (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)) {a : ℕ}
    (ha : a ≤ 3) : Phi H a (X0m / 2) ≤ 2 / 10 ^ 14 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hl := log_Pk_ge hX h.hXm 0
  rw [Pk_zero] at hl
  set ℓ := Real.log (X0m / 2)
  have hP0 : X0m / 2 = Real.exp ℓ := (Real.exp_log (by positivity)).symm
  have hb : 1 ≤ ℓ + 2 := by linarith
  have hpow : (ℓ + 2) ^ a ≤ (ℓ + 2) ^ 3 := pow_le_pow_right₀ hb ha
  have hc := num_core hl
  have hsmall : Real.exp (-(ℓ / 2)) ≤ 2 / 10 ^ 7 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (ℓ / 2)
    nlinarith
  have hHq : H (X0m / 2) / (X0m / 2) ≤ Real.exp (8 * Real.log ℓ ^ 2 - ℓ) := by
    rw [Real.exp_sub, ← hP0]
    exact div_le_div_of_nonneg_right hH (by positivity)
  unfold Phi
  have hH0 := hP.reg.pos (X0m / 2)
  have hE := Real.exp_pos (8 * Real.log ℓ ^ 2 - ℓ)
  calc H (X0m / 2) * (ℓ + 2) ^ a / (X0m / 2) = (H (X0m / 2) / (X0m / 2)) * (ℓ + 2) ^ a := by
        ring
    _ ≤ Real.exp (8 * Real.log ℓ ^ 2 - ℓ) * (ℓ + 2) ^ 3 :=
        mul_le_mul hHq hpow (by positivity) hE.le
    _ ≤ 2 / 10 ^ 14 := by nlinarith

/-- **`λ₀ C_N E_η ≤ ½`** (the hypothesis `hE` of Propositions 5.18, 5.26 and Lemma 5.27). -/
theorem energy_small (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)) {Sc : Finset ℝ}
    (hS : Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) {lam0 CN : ℝ} (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hCN0 : 0 ≤ CN) (hCN : CN ≤ 158) :
    lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) *
        blk P H X0m K (fun k => 1 / (Real.log (Pk X0m k) - 0.18)) v ≤ 1 / 2 := by
  have h1 := (etaBound_energy h hS hSc hZ hK).2.1
  have h2 := Phi_small h hH (a := 1) (by norm_num)
  have hlc : lam0 * CN ≤ 316 := by nlinarith
  have hE : ∑ v ∈ Sc, Real.log (2 * v) *
      blk P H X0m K (fun k => 1 / (Real.log (Pk X0m k) - 0.18)) v ≤ 1 / 1000000 := by
    linarith
  rcases le_or_gt 0 (∑ v ∈ Sc, Real.log (2 * v) *
      blk P H X0m K (fun k => 1 / (Real.log (Pk X0m k) - 0.18)) v) with h0 | h0
  · nlinarith [mul_nonneg hlam0 hCN0]
  · nlinarith [mul_nonneg hlam0 hCN0]

/-- **`2.04 ∑_v s_v ≤ 0.02`** for the `η`-blocks (Proposition 5.18, `∞`-norm bound). -/
theorem etaBlk_small (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)) {Sc : Finset ℝ}
    (hS : Sep Sc) (hSc : ∀ v ∈ Sc, 0 < v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) :
    2.04 * ∑ v ∈ Sc, blk P H X0m K (fun _ => 1) v ≤ 0.02 := by
  have h1 := (etaBlk_sum h hS hSc hZ hK).2
  have h2 := Phi_small h hH (a := 1) (by norm_num)
  nlinarith

/-- **`2.04 λ₀ θ_* ≤ 0.02`** for `θ_* = 207800 Φ₂(X₀⁻/2)` and `0 ≤ λ₀ ≤ 2`. -/
theorem thetaStar_small (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)) {lam0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
    0 ≤ 207800 * Phi H 2 (X0m / 2) ∧ 2.04 * lam0 * (207800 * Phi H 2 (X0m / 2)) ≤ 0.02 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have h0 := Phi_nonneg hP 2 (le_refl _) (by
    have := Pk_ge_one hX h.hXm 0; rwa [Pk_zero] at this)
  have h2 := Phi_small h hH (a := 2) (by norm_num)
  refine ⟨by positivity, ?_⟩
  nlinarith

/-- **`E_θ ≤ 10⁻⁷`** for the `θ`-blocks. -/
theorem thetaE_small (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)) {Sc : Finset ℝ}
    (hS : Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) :
    ∑ v ∈ Sc, Real.log (2 * v) * blk P H X0m K (fun k => Real.log (Pk X0m k) + 2) v ≤
      1 / 10000000 := by
  have h1 := (thetaBlk_sum h hS hSc hZ hK).2
  have h2 := Phi_small h hH (a := 3) (by norm_num)
  nlinarith

end KR.TNP

end
