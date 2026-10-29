module

public import RequestProject.Beurling.LocalPNT.Extension

/-!
# (LP-a) from the lag bound (13) below the certified horizon, and (LP-c)

* `lpa_of_lag`: if the lag bound (13) `|N - T| ≤ u^η`, `η = lagExponent θ`, and the absorbed
  part of the target error (Lemma 3.4) `|#A(u) - ∫_{X₀}^u ρ̄_A| ≤ 2u^{θ/2}` hold at the heights
  `X₀ ≤ u ≤ ž`, and `N = ⌊·⌋` below `X₀⁻` with `X₀ - X₀⁻ ≤ X₀^{1/4}`, then (LP-a) holds for every
  `y ≤ ž`, with `D₀(u) = u^{θ'}`. On `Good(<z)` the construction provides these at heights
  `≤ ž = z - 12 log z - 3` (Remark `horizon`); on the good event `G` at all heights
  (`Construction.lag_of_slotData`). The absorbed count and density are kept as parameters
  (`cntA`, `rhoA`), so the statement does not depend on how `A` is modelled.
* `lpc`: (LP-c), `|R̂(s)| ≤ |s|` (indeed `≤ |s| e^{-0.39 X₀²}`, eq. Rhatbound) on
  `σ ≥ 1 - 8/log X₀`.
-/

@[expose] public section

open Set Real Oscillation Construction DesignedZero

namespace LocalPNT

/-- `T - T₀ = #A - ∫ ρ̄_A` above `X₀`, and `T = T₀ = ⌊·⌋` below. -/
lemma target_sub_T0 {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} (cntA rhoA : ℝ → ℝ) (u : ℝ) :
    Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u - T0 θ X₀ α γ xp u =
      if u < X₀ then 0 else cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v := by
  unfold T0 Target.target
  split_ifs <;> simp; ring

/-- `u^a + 2 u^b ≤ u^{θ'}` when `a, b ≤ 1/4`, `θ' ≥ 0.26` and `u ≥ X₀ / 2`. -/
lemma two_pow_le_thetaPrime {θ : ℝ} {X₀ : ℕ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) {u a b : ℝ} (hu : (X₀ : ℝ) / 2 ≤ u) (ha : a ≤ 1 / 4)
    (hb : b ≤ 1 / 4) :
    u ^ a + 2 * u ^ b + 6 * (X₀ : ℝ) ^ (1 / 4 : ℝ) + 2 ≤ u ^ thetaPrime θ X₀ := by
  have hX0 := logX_pos_aux hX
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hu1 : 1 ≤ u := by
    have := rpow_ge_of_half hX hu (show (0 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at this; nlinarith [hX]
  have htp := (thetaPrime_bounds hθ hX).1
  have h1 : u ^ a ≤ u ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 ha
  have h2 : u ^ b ≤ u ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hb
  have h3 : (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ (2 * u) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hX0.le (by linarith) (by norm_num)
  have h4 : (2 * u) ^ (1 / 4 : ℝ) ≤ 2 * u ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hu0.le]
    have : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h5 : 20 ≤ u ^ (0.01 : ℝ) := by
    have := rpow_ge_of_half hX hu (show (0 : ℝ) ≤ 0.01 by norm_num); nlinarith
  have h6 : u ^ (0.26 : ℝ) = u ^ (1 / 4 : ℝ) * u ^ (0.01 : ℝ) := by
    rw [← Real.rpow_add hu0]; norm_num
  have h7 : u ^ (0.26 : ℝ) ≤ u ^ thetaPrime θ X₀ :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by linarith [hθ.1])
  have h8 : 1 ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
  have h9 : 20 * u ^ (1 / 4 : ℝ) ≤ u ^ (1 / 4 : ℝ) * u ^ (0.01 : ℝ) := by nlinarith
  linarith

/-- **(LP-a) from the lag bound (13) below the horizon** (Theorem 5.24, (LP-a); Remark
`horizon`(ii)). -/
theorem lpa_of_lag {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm zc : ℝ}
    (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (cntA rhoA : ℝ → ℝ) (hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ Xm) (hXmX : Xm ≤ X₀)
    (hfl : ∀ u, u < Xm → P.N u = ⌊u⌋₊)
    (hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |P.N u - Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u| ≤ u ^ lagExponent θ)
    (hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → |cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v| ≤ 2 * u ^ (θ / 2))
    (hz : (X₀ : ℝ) ≤ zc) :
    (∀ u, u < Xm → P.N u = T0 θ X₀ α γ xp u) ∧
    ∀ u, Xm ≤ u → u ≤ zc → |P.N u - T0 θ X₀ α γ xp u| ≤ u ^ thetaPrime θ X₀ := by
  have hX0 := logX_pos_aux hX
  have hX1 := one_le_X_aux hX
  have hlagE : lagExponent θ ≤ 1 / 8 := by
    unfold lagExponent; have := min_le_right θ (1 / 2 - θ); linarith [hθ.1]
  have hlag0 : 0 ≤ lagExponent θ := by
    unfold lagExponent; apply div_nonneg _ (by norm_num)
    exact le_min (by linarith [hθ.1]) (by linarith [hθ.2])
  have hX4 : (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ (X₀ : ℝ) / 2 := by
    have : (X₀ : ℝ) ^ (1 / 4 : ℝ) * (X₀ : ℝ) ^ (3 / 4 : ℝ) = X₀ := by
      rw [← Real.rpow_add hX0]; norm_num
    have h2 : (2 : ℝ) ≤ (X₀ : ℝ) ^ (3 / 4 : ℝ) := by
      have := rpow_ge_of_half hX (v := (X₀ : ℝ)) (by linarith) (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      nlinarith
    have h0 : 0 ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) := by positivity
    nlinarith
  have hXmh : (X₀ : ℝ) / 2 ≤ Xm := by linarith
  have hT0low : ∀ u : ℝ, u < X₀ → T0 θ X₀ α γ xp u = ⌊u⌋₊ := fun u hu => LPHyp.T0_low hu
  refine ⟨fun u hu => by rw [hfl u hu, hT0low u (lt_of_lt_of_le hu hXmX)], ?_⟩
  intro u h1 h2
  have hub := two_pow_le_thetaPrime hθ hX (u := u) (a := lagExponent θ) (b := θ / 2)
    (by linarith) (by linarith) (by linarith [hθ.2])
  have hu0 : 0 < u := by linarith
  have hpa : 0 ≤ u ^ lagExponent θ := by positivity
  have hpb : 0 ≤ u ^ (θ / 2) := by positivity
  rcases lt_or_ge u X₀ with hlow | hhigh
  · -- `N(u) - ⌊u⌋` on `[X₀⁻, X₀)`: squeeze with `N(Xm - 1/2) = ⌊Xm - 1/2⌋` and `N(X₀)`
    rw [hT0low u hlow]
    have hw := hfl (Xm - 1 / 2) (by linarith)
    have hmono := BeurlingSystem.N_mono P
    have hA1 : P.N (Xm - 1 / 2) ≤ P.N u := hmono (by linarith)
    have hA2 : P.N u ≤ P.N X₀ := hmono hlow.le
    have hNX := hlag X₀ le_rfl hz
    have hTX : Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) X₀ = X₀ + cntA X₀ := by
      simp only [Target.target, lt_irrefl, if_false, sub_self, intervalIntegral.integral_same]
      ring
    have hAX := hA X₀ le_rfl hz
    simp only [intervalIntegral.integral_same, sub_zero] at hAX
    rw [hTX] at hNX
    have hpX : (X₀ : ℝ) ^ lagExponent θ ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hpX2 : (X₀ : ℝ) ^ (θ / 2) ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [hθ.2])
    have hfl1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
    have hfl2 : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
    have hw1 : Xm - 1 / 2 - 1 < (⌊Xm - 1 / 2⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (Xm - 1 / 2); linarith
    have e1 := abs_le.mp hNX
    have e2 := abs_le.mp hAX
    have hXq : 1 ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
    have hup : P.N u - ⌊u⌋₊ ≤ 4 * (X₀ : ℝ) ^ (1 / 4 : ℝ) + 1 := by
      have : P.N X₀ ≤ X₀ + cntA X₀ + (X₀ : ℝ) ^ lagExponent θ := by linarith [e1.2]
      have : cntA X₀ ≤ 2 * (X₀ : ℝ) ^ (θ / 2) := e2.2
      linarith
    have hlo : -(4 * (X₀ : ℝ) ^ (1 / 4 : ℝ) + 1) ≤ P.N u - ⌊u⌋₊ := by
      rw [hw] at hA1
      linarith
    rw [abs_le]; constructor <;> linarith
  · have hd := target_sub_T0 (θ := θ) (X₀ := X₀) (α := α) (γ := γ) (xp := xp) cntA rhoA u
    rw [if_neg (not_lt.mpr hhigh)] at hd
    have e1 := hlag u hhigh h2
    have e2 := hA u hhigh h2
    have : P.N u - T0 θ X₀ α γ xp u =
        (P.N u - Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u) +
          (cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v) := by linarith
    rw [this]
    calc _ ≤ |P.N u - Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u| +
          |cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v| := abs_add_le _ _
      _ ≤ u ^ lagExponent θ + 2 * u ^ (θ / 2) := add_le_add e1 e2
      _ ≤ u ^ thetaPrime θ X₀ := by
          have : 0 ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) := by positivity
          linarith

/-- **The hypotheses of Theorem 5.24 at every `y ∈ [X₀, ž]`** from the design, Lemma 3.3 for
`T₀`, and the lag bound (13) with the absorbed target error below the horizon `ž`. -/
theorem lpHyp_of_lag {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm zc y : ℝ}
    (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀) (hev : Even X₀)
    (hα : ∀ k, |α k| ≤ 2) (h0 : Real.exp ((X₀ : ℝ) ^ 2) ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) (hmono : MonotoneOn (T0 θ X₀ α γ xp) (Ici (X₀ : ℝ)))
    (cntA rhoA : ℝ → ℝ) (hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ Xm) (hXmX : Xm ≤ X₀)
    (hfl : ∀ u, u < Xm → P.N u = ⌊u⌋₊)
    (hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |P.N u - Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u| ≤ u ^ lagExponent θ)
    (hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → |cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v| ≤ 2 * u ^ (θ / 2))
    (hy : (X₀ : ℝ) ≤ y) (hyz : y ≤ zc) :
    LPHyp P θ X₀ α γ xp Xm y (fun u => u ^ thetaPrime θ X₀) := by
  obtain ⟨hlo, hhi⟩ := lpa_of_lag hθ hX cntA rhoA hXm hXmX hfl hlag hA (hy.trans hyz)
  have hX0 := logX_pos_aux hX
  have hX4 : (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ (X₀ : ℝ) / 2 := by
    have e : (X₀ : ℝ) ^ (1 / 4 : ℝ) * (X₀ : ℝ) ^ (3 / 4 : ℝ) = X₀ := by
      rw [← Real.rpow_add hX0]; norm_num
    have h2 : (2 : ℝ) ≤ (X₀ : ℝ) ^ (3 / 4 : ℝ) := by
      have := rpow_ge_of_half hX (v := (X₀ : ℝ)) (by linarith) (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      nlinarith
    have h0 : 0 ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) := by positivity
    nlinarith
  exact
    { theta_mem := hθ, logX := hX, even := hev, alpha_le := hα, xp_zero := h0, xp_succ := hsp
      T0_mono := hmono, Xm_ge := by linarith, Xm_le := hXmX, y_ge := hy
      lpa_low := hlo
      lpa_high := fun u h1 h2 => ⟨hhi u h1 (h2.trans hyz), le_rfl⟩ }

/-- **(LP-c)** with eq. (Rhatbound): `|R̂(s)| ≤ |s| e^{-0.39 X₀²} ≤ |s|` on `σ ≥ 1 - 8/log X₀`. -/
theorem lpc {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} (hθ : θ ≤ 1 / 2) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hα : ∀ k, |α k| ≤ 2) (h0 : Real.exp ((X₀ : ℝ) ^ 2) ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) {s : ℂ} (hs : 1 - 8 / Real.log X₀ ≤ s.re) :
    ‖oscHatSum θ α γ xp s‖ ≤ ‖s‖ * Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) ∧
      ‖oscHatSum θ α γ xp s‖ ≤ ‖s‖ := by
  have hX1 := one_le_X_aux hX
  have h400 : (400 : ℝ) ≤ (X₀ : ℝ) ^ 2 := by
    have : (20 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀)
      rw [Real.exp_log (logX_pos_aux hX)] at this; linarith
    nlinarith
  have hσ : θ + 2 / 5 ≤ s.re := by
    have : 8 / Real.log X₀ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hX
    linarith
  obtain ⟨hsum, hle⟩ := norm_tsum_oscHat_le (θ := θ) (γ := γ) hα h400 h0 hsp hσ
  have h1 : ‖oscHatSum θ α γ xp s‖ ≤ ‖s‖ * Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) :=
    (norm_tsum_le_tsum_norm hsum).trans hle
  refine ⟨h1, h1.trans ?_⟩
  have : Real.exp (-(39 / 100) * (X₀ : ℝ) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith [norm_nonneg s]

end LocalPNT

end
