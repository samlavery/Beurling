module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Theorem 5.6: the constant `C_BS = Φ_∞`, the base-region inequality, and the case `u = 0`

* `PhiInf_le`: `C_BS = Φ_∞ ≤ 38.3` for `τ ≥ 10⁸` (Theorem 5.6);
* `PhiInf_antitoneOn`: `Φ_∞` is non-increasing in `τ` on `[10⁸, ∞)` (Lemma 5.8);
* `base_phi`: `(ℓ/τ) C₀ ≤ Φ(ℓ)` for `τ ≤ ℓ ≤ 30τ` (Step 4: `ℓ e^{κ_Φ/ℓ}` is convex);
* `Phi_le_PhiInf`, `Gf_zero_le`: `G(ℓ, 0) ≤ Φ_∞` (Step 3, since `B log 2 ≤ κ_Φ`).
-/

@[expose] public section

open Real

namespace BSaias

lemma exp_small_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  linarith [le_abs_self (Real.exp x - 1 - x)]

/-- `C_BS = Φ_∞ ≤ 38.3` for `τ ≥ 10⁸`. -/
theorem PhiInf_le {τ : ℝ} (hτ : 100000000 ≤ τ) : PhiInf τ ≤ 38.3 := by
  have hτ0 : 0 < τ := by linarith
  have h1 : kappa τ / τ = 4 + 1500 / τ := by unfold kappa; field_simp
  have h2 : kappa τ / (30 * τ) = 2 / 15 + 50 / τ := by unfold kappa; field_simp; ring
  have hs1 : 1500 / τ ≤ 0.000015 := by rw [div_le_iff₀ hτ0]; linarith
  have hs2 : 50 / τ ≤ 0.0000005 := by rw [div_le_iff₀ hτ0]; linarith
  have hp1 : 0 ≤ 1500 / τ := by positivity
  have hp2 : 0 ≤ 50 / τ := by positivity
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he1' : 0 < Real.exp 1 := Real.exp_pos 1
  have he4 : Real.exp 4 < 54.6 := by
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := pow_lt_pow_left₀ he1 he1'.le (by norm_num : (4 : ℕ) ≠ 0)
    linarith [show (2.7182818286 : ℝ) ^ 4 < 54.6 by norm_num]
  have hA : Real.exp (kappa τ / τ) ≤ 54.6 * 1.0000151 := by
    rw [h1, Real.exp_add]
    have := exp_small_le hp1 (by linarith)
    have hb : Real.exp (1500 / τ) ≤ 1.0000151 := by nlinarith
    exact mul_le_mul he4.le hb (Real.exp_pos _).le (by norm_num)
  have hB : 30 * Real.exp (kappa τ / (30 * τ)) ≤ 30 * 1.2 := by
    rw [h2]
    have := exp_small_le (x := 2 / 15 + 50 / τ) (by positivity) (by linarith)
    have : Real.exp (2 / 15 + 50 / τ) ≤ 1.2 := by nlinarith
    linarith
  unfold PhiInf C0
  have : max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ))) ≤ 54.6 * 1.0000151 :=
    max_le hA (by linarith)
  nlinarith

/-- `Φ_∞` is non-increasing in `τ` on `[10⁸, ∞)`. -/
theorem PhiInf_antitoneOn : AntitoneOn PhiInf (Set.Ici 100000000) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : ∀ τ, 0 < τ → kappa τ / τ = 4 + 1500 / τ := fun τ h => by unfold kappa; field_simp
  have h2 : ∀ τ, 0 < τ → kappa τ / (30 * τ) = 2 / 15 + 50 / τ := fun τ h => by
    unfold kappa; field_simp; ring
  unfold PhiInf
  rw [h1 a ha0, h1 b hb0, h2 a ha0, h2 b hb0]
  have e1 : 1500 / b ≤ 1500 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hab
  have e2 : 50 / b ≤ 50 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hab
  unfold C0
  gcongr

/-- **Step 4**: `(ℓ/τ) C₀ ≤ Φ(ℓ)` for `τ ≤ ℓ ≤ 30τ`. -/
theorem base_phi {τ ℓ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ ℓ) (h2 : ℓ ≤ 30 * τ) :
    ℓ / τ * C0 ≤ Phi τ ℓ := by
  have hℓ : 0 < ℓ := by linarith
  set κ := kappa τ
  -- perspective convexity: ℓ e^{κ/ℓ} ≤ λ τ e^{κ/τ} + (1-λ) 30τ e^{κ/(30τ)}
  set lam := (30 * τ - ℓ) / (29 * τ) with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have hl1 : lam ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hℓeq : ℓ = lam * τ + (1 - lam) * (30 * τ) := by rw [hlam]; field_simp; ring
  set μ := lam * τ / ℓ
  have hμ0 : 0 ≤ μ := div_nonneg (mul_nonneg hl0 hτ.le) hℓ.le
  have hμ1 : 1 - μ = (1 - lam) * (30 * τ) / ℓ := by
    simp only [μ]; field_simp; linarith
  have hμ1' : 0 ≤ 1 - μ := by rw [hμ1]; exact div_nonneg (by nlinarith) hℓ.le
  have hconv := convexOn_exp.2 (Set.mem_univ (κ / τ)) (Set.mem_univ (κ / (30 * τ))) hμ0 hμ1'
    (by ring)
  simp only [smul_eq_mul] at hconv
  have hx : μ * (κ / τ) + (1 - μ) * (κ / (30 * τ)) = κ / ℓ := by
    rw [hμ1]; simp only [μ]; field_simp; ring
  rw [hx] at hconv
  have hmax : ℓ / τ * Real.exp (κ / ℓ) ≤
      max (Real.exp (κ / τ)) (30 * Real.exp (κ / (30 * τ))) := by
    have : ℓ / τ * Real.exp (κ / ℓ) ≤
        lam * Real.exp (κ / τ) + (1 - lam) * (30 * Real.exp (κ / (30 * τ))) := by
      have h := mul_le_mul_of_nonneg_left hconv (div_nonneg hℓ.le hτ.le)
      calc ℓ / τ * Real.exp (κ / ℓ) ≤ ℓ / τ * (μ * Real.exp (κ / τ) +
            (1 - μ) * Real.exp (κ / (30 * τ))) := h
        _ = lam * Real.exp (κ / τ) + (1 - lam) * (30 * Real.exp (κ / (30 * τ))) := by
          rw [hμ1]; simp only [μ]; field_simp
    refine this.trans ?_
    have hA := le_max_left (Real.exp (κ / τ)) (30 * Real.exp (κ / (30 * τ)))
    have hB := le_max_right (Real.exp (κ / τ)) (30 * Real.exp (κ / (30 * τ)))
    nlinarith
  unfold Phi PhiInf
  have he := Real.exp_pos (κ / ℓ)
  have hC0 : (0 : ℝ) < C0 := by unfold C0; norm_num
  have : ℓ / τ * C0 = C0 * (ℓ / τ * Real.exp (κ / ℓ)) * Real.exp (-(κ / ℓ)) := by
    rw [mul_assoc, mul_assoc, ← Real.exp_add]; simp; ring
  rw [this]
  gcongr

lemma PhiInf_pos (τ : ℝ) : 0 < PhiInf τ := by
  unfold PhiInf C0
  have := Real.exp_pos (kappa τ / τ)
  have : 0 < max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ))) :=
    lt_max_of_lt_left this
  positivity

lemma Phi_pos (τ ℓ : ℝ) : 0 < Phi τ ℓ := by
  unfold Phi; have := PhiInf_pos τ; positivity

/-- `Φ(ℓ) ≤ Φ_∞` for `ℓ > 0`, `τ ≥ 0`. -/
lemma Phi_le_PhiInf {τ ℓ : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) : Phi τ ℓ ≤ PhiInf τ := by
  unfold Phi
  have hk : 0 ≤ kappa τ / ℓ := div_nonneg (by unfold kappa; linarith) hℓ.le
  have : Real.exp (-(kappa τ / ℓ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have := PhiInf_pos τ
  nlinarith

/-- **Step 3**: `G(ℓ, 0) ≤ Φ_∞` (because `B log 2 ≤ κ_Φ`). -/
theorem Gf_zero_le {τ ℓ : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) : Gf τ ℓ 0 ≤ PhiInf τ := by
  unfold Gf Phi Qf aQ BSCert.Z2.A
  have hu0 : 0 ≤ u0 ℓ := by unfold u0 BSCert.Z2.u0; positivity
  rw [Dickman.rho_of_le_one (by norm_num), max_eq_right (by linarith)]
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hk : 11 * (1 + 0) ^ 3 * Real.log (2 + 0) / ℓ + 0 ^ 2 / (2 * √ℓ) - kappa τ / ℓ ≤ 0 := by
    simp only [add_zero, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div]
    rw [← sub_div]
    apply div_nonpos_of_nonpos_of_nonneg _ hℓ.le
    unfold kappa; nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have := PhiInf_pos τ
  calc PhiInf τ * Real.exp (-(kappa τ / ℓ)) * 1 *
        Real.exp (11 * (1 + 0) ^ 3 * Real.log (2 + 0) / ℓ + 0 ^ 2 / (2 * √ℓ))
      = PhiInf τ * Real.exp (11 * (1 + 0) ^ 3 * Real.log (2 + 0) / ℓ + 0 ^ 2 / (2 * √ℓ)
          - kappa τ / ℓ) := by
        rw [sub_eq_add_neg, Real.exp_add]; simp; ring_nf; rw [mul_assoc, ← Real.exp_add]
    _ ≤ PhiInf τ * 1 := by
        gcongr; exact Real.exp_le_one_iff.mpr hk
    _ = PhiInf τ := mul_one _

end BSaias

end
