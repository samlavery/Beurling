module

public import RequestProject.Beurling.Noise.LemSPoint
public import RequestProject.Beurling.Noise.LemSRho

/-!
# Lemma 5.21(ii): the numerical forms

For `log 3v ≥ 10⁸`:

* `HBS.lemS_ii_le30` : `ω_y(v) ≤ 2C₀ ρ(u_y) e^{0.02}` for `u_y ≤ 30`;
* `HBS.lemS_ii_gt30` : `ω_y(v) ≤ 2C₀ e^{-0.7 u_y log u_y}` for `30 < u_y ≤ log 3v`;
* `LemSRankin` : the statement of the bound `ω_y(v) ≤ 5 (log 3v)^{1.65} e^{-u_y/2}` for
  `u_y > log 3v` (Rankin's bound; proved in `LemSRankin.lean`);
* `HBS.omega_le_mid`, `HBS.omega_le_far` : the two bounds used in (iii),
  `ω_y(v) ≤ 0.71 e^{-0.99(u_y - 1)}` for `1 ≤ u_y ≤ log 3v`, and, for `ℓ = log(y/2v) > (log 3v)²`,
  `ω_y(v) ≤ 2 e^{-√ℓ/2}` (Lemma 5.3 with `z = e^{√ℓ}`, as the cofactors are `3v`-smooth).
-/

@[expose] public section

open Finset Real

namespace LemS

/-- `log(L + 2) ≤ 10⁻⁶ L` for `L ≥ 10⁸`. -/
lemma log_add_two_le {L : ℝ} (hL : 100000000 ≤ L) : Real.log (L + 2) ≤ L / 1000000 := by
  rw [Real.log_le_iff_le_exp (by linarith)]
  have h := Real.pow_div_factorial_le_exp (x := L / 1000000) (by positivity) 6
  refine le_trans ?_ h
  have h1 : (100 : ℝ) ≤ L / 1000000 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h5 : (100 : ℝ) ^ 5 ≤ (L / 1000000) ^ 5 := pow_le_pow_left₀ (by norm_num) h1 5
  rw [show (6 : ℕ).factorial = 720 by rfl]
  push_cast
  have e : (L / 1000000) ^ 6 = (L / 1000000) ^ 5 * (L / 1000000) := by ring
  rw [e, le_div_iff₀ (by norm_num)]
  nlinarith

end LemS

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma aV_uY_small {y v : ℝ} (hL : 100000000 ≤ Real.log (3 * v)) (hu1 : 1 ≤ uY y v)
    (hu2 : uY y v ≤ Real.log (3 * v)) :
    BSaias.aV (Real.log (y / (2 * v))) (uY y v) ≤ 0.000013 * uY y v := by
  have hL0 : 0 < Real.log (3 * v) := by linarith
  refine (aV_uY_le hL0 hu1).trans ?_
  have hl := LemS.log_add_two_le hL
  have hl2 : Real.log (uY y v + 2) ≤ Real.log (Real.log (3 * v) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [div_le_iff₀ hL0]
  have hu0 : 0 ≤ uY y v := by linarith
  have := mul_le_mul_of_nonneg_left (hl2.trans hl) (show 0 ≤ 13 * uY y v by positivity)
  have e : 13 * uY y v * (Real.log (3 * v) / 1000000) =
      0.000013 * uY y v * Real.log (3 * v) := by ring
  linarith

/-- **Lemma 5.21(ii)** for `u_y ≤ 30`: `ω_y(v) ≤ 2C₀ ρ(u_y) e^{0.02}`. -/
theorem lemS_ii_le30 (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {y : ℝ}
    (hy : 0 < y) (hu : uY y v ≤ 30) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤ 2 * BSaias.C0 * Dickman.rho (uY y v) * Real.exp 0.02 := by
  have hC : BSaias.C0 = 0.70 := rfl
  have he : 1 ≤ Real.exp 0.02 := Real.one_le_exp (by norm_num)
  rcases lt_or_ge (uY y v) 1 with h1 | h1
  · rw [Dickman.rho_of_le_one h1.le, hC]
    refine (lemS_i h t hv hZ).trans ?_
    nlinarith
  · have hD := lemS_ii_dickman h hd hv (by linarith) hy h1 (by linarith) hZ
    have ha := aV_uY_small hL h1 (by linarith)
    have hρ := (Dickman.rho_pos (uY y v)).le
    refine hD.trans ?_
    have hexp : Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v)) ≤ Real.exp 0.02 :=
      Real.exp_le_exp.mpr (by linarith)
    rw [hC]
    have := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 0.70 * Dickman.rho (uY y v) by positivity)
    have h2 : 0 ≤ 0.70 * Dickman.rho (uY y v) * Real.exp 0.02 := by positivity
    nlinarith

/-- **Lemma 5.21(ii)** for `30 < u_y ≤ log 3v`: `ω_y(v) ≤ 2C₀ e^{-0.7 u_y log u_y}`. -/
theorem lemS_ii_gt30 (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {y : ℝ}
    (hy : 0 < y) (hu1 : 30 < uY y v) (hu2 : uY y v ≤ Real.log (3 * v)) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤ 2 * BSaias.C0 * Real.exp (-(0.7 * uY y v * Real.log (uY y v))) := by
  have hD := lemS_ii_dickman h hd hv (by linarith) hy (by linarith) hu2 hZ
  have ha := aV_uY_small hL (by linarith) hu2
  have hb := LemS.rho_exp_le_big hu1 ha
  have hC : (0 : ℝ) ≤ BSaias.C0 := by unfold BSaias.C0; norm_num
  calc P.omegaW t y v ≤ BSaias.C0 * Dickman.rho (uY y v) *
        Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v)) := hD
    _ = BSaias.C0 * (Dickman.rho (uY y v) *
        Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v))) := by ring
    _ ≤ BSaias.C0 * (2 * Real.exp (-(0.7 * uY y v * Real.log (uY y v)))) :=
        mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

/-- The bound of (ii) used in (iii) for `1 ≤ u_y ≤ log 3v`: `ω_y(v) ≤ 0.71 e^{-0.99(u_y - 1)}`. -/
theorem omega_le_mid (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {y : ℝ}
    (hy : 0 < y) (hu1 : 1 ≤ uY y v) (hu2 : uY y v ≤ Real.log (3 * v)) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤ 0.71 * Real.exp (-(0.99 * (uY y v - 1))) := by
  have hD := lemS_ii_dickman h hd hv (by linarith) hy hu1 hu2 hZ
  have ha := aV_uY_small hL hu1 hu2
  have hρ := LemS.rho_le_exp_one_sub hu1
  have hC : BSaias.C0 = 0.70 := rfl
  refine hD.trans ?_
  rw [hC]
  have h1 : Dickman.rho (uY y v) * Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v)) ≤
      Real.exp (1 - uY y v) * Real.exp (0.000013 * uY y v) :=
    mul_le_mul hρ (Real.exp_le_exp.mpr ha) (Real.exp_pos _).le (Real.exp_pos _).le
  have h2 : Real.exp (1 - uY y v) * Real.exp (0.000013 * uY y v) ≤
      Real.exp 0.000013 * Real.exp (-(0.99 * (uY y v - 1))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; nlinarith
  have h3 : Real.exp (0.000013 : ℝ) ≤ 1.0001 := by
    have := Real.exp_bound' (x := (0.000013 : ℝ)) (by norm_num) (by norm_num) (n := 2)
      (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hE := (Real.exp_pos (-(0.99 * (uY y v - 1)))).le
  calc 0.70 * Dickman.rho (uY y v) * Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v))
      = 0.70 * (Dickman.rho (uY y v) *
          Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v))) := by ring
    _ ≤ 0.70 * (Real.exp 0.000013 * Real.exp (-(0.99 * (uY y v - 1)))) := by
        nlinarith
    _ ≤ 0.70 * (1.0001 * Real.exp (-(0.99 * (uY y v - 1)))) := by nlinarith
    _ ≤ 0.71 * Real.exp (-(0.99 * (uY y v - 1))) := by nlinarith

/-- The bound used in (iii) for `ℓ = log(y/2v) > (log 3v)²`: `ω_y(v) ≤ 2 e^{-√ℓ/2}`. The
cofactors are `3v`-smooth, hence `e^{√ℓ}`-smooth, and Lemma 5.3 applies with `z = e^{√ℓ}`,
`u = √ℓ`. -/
theorem omega_le_far (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {y : ℝ}
    (hy : 0 < y) (hℓ : Real.log (3 * v) ^ 2 < Real.log (y / (2 * v))) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤ 2 * Real.exp (-(√(Real.log (y / (2 * v))) / 2)) := by
  set ℓ := Real.log (y / (2 * v)) with hℓdef
  set s := √ℓ with hs
  have hL0 : 0 < Real.log (3 * v) := by linarith
  have hℓ0 : 0 < ℓ := lt_of_le_of_lt (by positivity) hℓ
  have hsL : Real.log (3 * v) ≤ s := by
    rw [hs, Real.le_sqrt hL0.le hℓ0.le]; linarith
  have hs0 : 0 < s := by linarith
  have hss : s * s = ℓ := Real.mul_self_sqrt hℓ0.le
  have hz : Real.log (Real.exp s) = s := Real.log_exp s
  have h3v : 3 * v ≤ Real.exp s := by
    rw [← Real.exp_log (show 0 < 3 * v by positivity)]; exact Real.exp_le_exp.mpr hsL
  have hY : Real.exp (s * Real.log (Real.exp s)) = y / (2 * v) := by
    rw [hz, hss, hℓdef, Real.exp_log (by positivity)]
  have h53 := h.lemma53 (Real.exp s) s (by rw [hz]; linarith) (by linarith) (by rw [hz]) (by
    rw [hY, two_mul_div_two_mul hv]; exact hZ)
  rw [hY, hz] at h53
  have hω := (omegaW_le_vSmooth hd y hv).trans ((vSmooth_mono h3v).trans h53)
  refine hω.trans ?_
  have haV : BSaias.aV (s * s) s = 12.8 * Real.log (s + 2) := by
    unfold BSaias.aV; field_simp; ring
  rw [haV]
  have hρ := LemS.rho_le_exp_one_sub (u := s) (by linarith)
  have hlog := LemS.log_add_two_le (L := s) (by linarith)
  have hC : BSaias.C0 = 0.70 := rfl
  rw [hC]
  have h1 : 0.70 * Dickman.rho s * Real.exp (12.8 * Real.log (s + 2)) ≤
      0.70 * (Real.exp (1 - s) * Real.exp (12.8 * Real.log (s + 2))) := by
    have := mul_le_mul_of_nonneg_right hρ (Real.exp_pos (12.8 * Real.log (s + 2))).le
    nlinarith
  refine h1.trans ?_
  rw [← Real.exp_add]
  have h2 : Real.exp (1 - s + 12.8 * Real.log (s + 2)) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have := (Real.exp_pos (-(s / 2))).le
  nlinarith

end HBS

/-- **Lemma 5.21(ii), last bound** (Rankin's bound with exponent `1 - 1/(2 log 3v)` and
Lemma 5.1, 04k-kernels.tex lines 540-541): for `u_y > log 3v` (and `y/v ≤ Z`),
`ω_y(v) ≤ 5 (log 3v)^{1.65} e^{-u_y/2}`. Proved in `LemSRankin.lean` (`HBS.lemS_rankin`). -/
def LemSRankin (P : BeurlingSystem) (Z : ℝ) (t : ℕ → ℝ) (v : ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → y / v ≤ Z → Real.log (3 * v) < HBS.uY y v →
    P.omegaW t y v ≤ 5 * Real.log (3 * v) ^ (1.65 : ℝ) * Real.exp (-(HBS.uY y v / 2))

end BeurlingSystem

end
