module

public import RequestProject.Beurling.LocalPNT.Growth
public import RequestProject.Beurling.LocalPNT.LogDerivJ
public import RequestProject.Beurling.LocalPNT.Landau
public import RequestProject.Beurling.LocalPNT.ZFNumeric

/-!
# Step 7 of the proof of Theorem 5.24: the zero-free region

With `Λ = log X₀`, `L_t = log(|t| + 3)`, `X(t) = L_t + 442 + 2 log Λ`, `Y(t) = X + log X + 0.7` and
`η_t = 0.33769/(Λ Y(t))`: if `|t| ≥ 1/16` and `η_t ≥ 16 log log y/log y`, then `ζ^♯(σ + it) ≠ 0`
for `1 - η_t/3.79 ≤ σ ≤ 2` (`zeroFree_width`; the paper's eq. lp-width, `δ_t = η_t/κ_L`,
`κ_L = 3.79`). Landau's discs have radius `r = 6.8/Λ`.

The growth constant: `log M_k ≤ L_t + log Λ + log(1/η) + 439` (the paper has `440.86`; we use
`log C₈ < 439.4`, `γ < 2/3` and `|ζ^♯(1 + η + ikt)| ≥ 0.98η`).
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp

namespace LocalPNT

/-- `L_t = log(|t| + 3)`. -/
noncomputable def Lt (t : ℝ) : ℝ := Real.log (|t| + 3)

/-- `Y(t) = X + log X + 0.7`, `X = L_t + 442 + 2 log Λ`. -/
noncomputable def Yt (Λ t : ℝ) : ℝ :=
  Lt t + 442 + 2 * Real.log Λ + Real.log (Lt t + 442 + 2 * Real.log Λ) + 0.7

/-- `η_t = 0.33769/(Λ Y(t))`. -/
noncomputable def etat (Λ t : ℝ) : ℝ := 0.33769 / (Λ * Yt Λ t)

lemma Lt_nonneg (t : ℝ) : 0 ≤ Lt t := Real.log_nonneg (by linarith [abs_nonneg t])

lemma Yt_ge {Λ : ℝ} (hΛ : 1 ≤ Λ) (t : ℝ) : 442 ≤ Yt Λ t := by
  unfold Yt
  have := Lt_nonneg t
  have := Real.log_nonneg hΛ
  have : 0 ≤ Real.log (Lt t + 442 + 2 * Real.log Λ) := Real.log_nonneg (by linarith)
  linarith

lemma etat_pos {Λ : ℝ} (hΛ : 1 ≤ Λ) (t : ℝ) : 0 < etat Λ t := by
  unfold etat; have := Yt_ge hΛ t; positivity

lemma etat_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (t : ℝ) : etat Λ t ≤ 1 / 10 ^ 10 := by
  unfold etat
  have hY := Yt_ge (Λ := Λ) (by linarith) t
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `κ ≤ e^{-0.39 Λ}`. -/
lemma kap_le_exp {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    kap X₀ ≤ Real.exp (-(0.39 * Real.log X₀)) := by
  rw [kap_eq (kap_facts hX).1]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `C₈ e^γ Λ κ ≤ 10^{-6}`. -/
lemma C8_kap_small {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    C8 * Real.exp Real.eulerMascheroniConstant * Real.log X₀ * kap X₀ ≤ 1 / 10 ^ 6 := by
  set Λ := Real.log X₀
  have hC := log_C8_lt
  have hC0 : 0 < C8 := by unfold C8; positivity
  have hC8 : C8 ≤ Real.exp 439.4 := by
    have := (Real.log_lt_iff_lt_exp hC0).mp hC; unfold C8 at *; linarith
  have hγ : Real.exp Real.eulerMascheroniConstant ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by linarith [Real.eulerMascheroniConstant_lt_two_thirds])
  have hΛ0 : 0 < Λ := by linarith
  have hΛ : Λ ≤ Real.exp (0.01 * Λ) := by
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.01 * Λ by positivity) 3
    norm_num [Finset.sum_range_succ] at this
    nlinarith
  have hκ := kap_le_exp hX
  have hκ0 := (kap_facts hX).2.2.1
  have hγ0 := Real.exp_pos Real.eulerMascheroniConstant
  calc C8 * Real.exp Real.eulerMascheroniConstant * Λ * kap X₀
      ≤ Real.exp 439.4 * Real.exp 1 * Real.exp (0.01 * Λ) * Real.exp (-(0.39 * Λ)) := by
        gcongr
    _ = Real.exp (440.4 - 0.38 * Λ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-14) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 10 ^ 6 := by
        have e : Real.exp (-14) = Real.exp (-1) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc Real.exp (-1) ^ 14 ≤ 0.368 ^ 14 :=
              pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_neg_one_lt_d9]) 14
          _ ≤ 1 / 10 ^ 6 := by norm_num

/-- The growth majorant on Landau's disc at height `kt`. -/
noncomputable def Bk (X₀ : ℕ) (k : ℕ) (t : ℝ) : ℝ :=
  18.1 + C8 * (1 + kap X₀ * (k * |t| + 1.02)) * Real.exp Real.eulerMascheroniConstant *
      Real.log X₀ + (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * (k * |t| + 1.02)

lemma log_six_four_le : Real.log 6.4 ≤ 1.857 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.857 by norm_num) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

/-- **`log B_k ≤ L_t + log Λ + 438.975`** for `k ≤ 4`. -/
lemma log_Bk_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {k : ℕ} (hk : k ≤ 4) (t : ℝ) :
    Real.log (Bk X₀ k t) ≤ Lt t + Real.log (Real.log X₀) + 438.975 := by
  set Λ := Real.log X₀
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨hX0, -, hκ0, hκs, -⟩ := kap_facts hX
  have hC0 : 0 < C8 := by unfold C8; positivity
  set Bb := C8 * Real.exp Real.eulerMascheroniConstant * Λ
  set A := 4 * |t| + 19.2 with hAdef
  have hA : 19.2 ≤ A := by have := abs_nonneg t; linarith [hAdef]
  have hsmall := C8_kap_small hX
  have hXp : (X₀ : ℝ) ^ (-(0.48 : ℝ)) ≤ 1 / 10 ^ 7 := by
    have := rpow_ge_of_half hX (v := (X₀ : ℝ)) (by linarith) (show (0 : ℝ) ≤ 0.48 by norm_num)
    have hX48 : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) ^ (0.48 : ℝ) := by nlinarith
    rw [Real.rpow_neg hX0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hX48
  have hXp0 : 0 ≤ (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by positivity
  have hkt : (k : ℝ) * |t| ≤ 4 * |t| := mul_le_mul_of_nonneg_right (by exact_mod_cast hk)
    (abs_nonneg t)
  have hkt0 : 0 ≤ (k : ℝ) * |t| := by positivity
  -- `B_k ≤ (1 + ε)(A + B)`
  have hBb : Real.exp 10 ≤ Bb := by
    have h1 : 1 ≤ C8 := by
      unfold C8
      have := Real.add_one_le_exp (8 : ℝ)
      have : 0 < Real.exp (Ein 8) := Real.exp_pos _
      nlinarith
    have h2 : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
      Real.one_le_exp (by linarith [Real.one_half_lt_eulerMascheroniConstant])
    have h3 : Real.exp 10 ≤ Λ := by
      have : Real.exp 10 ≤ 10 ^ 8 := by
        have e : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc Real.exp 1 ^ 10 ≤ 2.7182818286 ^ 10 :=
              pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 10
          _ ≤ 10 ^ 8 := by norm_num
      linarith
    have : 1 * 1 * Λ ≤ C8 * Real.exp Real.eulerMascheroniConstant * Λ :=
      mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 zero_le_one (by linarith)) hΛ0.le
    simp only [Bb]; linarith
  have hBk : Bk X₀ k t ≤ (1 + 1 / 10 ^ 5) * (A + Bb) := by
    unfold Bk
    have e1 : C8 * (1 + kap X₀ * (k * |t| + 1.02)) * Real.exp Real.eulerMascheroniConstant * Λ =
        Bb + (Bb * kap X₀) * (k * |t| + 1.02) := by simp only [Bb]; ring
    rw [e1]
    have h1 : (Bb * kap X₀) * (k * |t| + 1.02) ≤ 1 / 10 ^ 6 * A :=
      mul_le_mul hsmall (show (k : ℝ) * |t| + 1.02 ≤ A by linarith [hAdef]) (by positivity)
        (by norm_num)
    have h2 : (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * (k * |t| + 1.02) ≤
        (1 + 5 / 10 ^ 7) * (k * |t| + 1.02) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hBb0 : 0 ≤ Bb := le_trans (Real.exp_pos _).le hBb
    have h3 : (1 + 5 / 10 ^ 7) * (k * |t| + 1.02) + 18.1 ≤ (1 + 5 / 10 ^ 7) * A := by
      simp only [A]; nlinarith
    nlinarith
  have hpos : 0 < Bk X₀ k t := by
    unfold Bk; have := hκ0; positivity
  calc Real.log (Bk X₀ k t) ≤ Real.log ((1 + 1 / 10 ^ 5) * (A + Bb)) :=
        Real.log_le_log hpos hBk
    _ = Real.log (1 + 1 / 10 ^ 5) + Real.log (A + Bb) :=
        Real.log_mul (by norm_num) (by linarith)
    _ ≤ 1 / 10 ^ 5 + (Real.log A + Real.log Bb - 2.95) := by
        have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 10 ^ 5 by norm_num)
        have h2 := log_add_le hA hBb
        linarith
    _ ≤ Lt t + Real.log Λ + 438.975 := by
        have hlA : Real.log A ≤ Real.log 6.4 + Lt t := by
          unfold Lt
          rw [← Real.log_mul (by norm_num) (by have := abs_nonneg t; linarith)]
          exact Real.log_le_log (by linarith) (by have := abs_nonneg t; linarith [hAdef])
        have hlB : Real.log Bb ≤ 439.4 + 2 / 3 + Real.log Λ := by
          simp only [Bb]
          rw [Real.log_mul (by positivity) hΛ0.ne', Real.log_mul hC0.ne' (Real.exp_pos _).ne',
            Real.log_exp]
          have := log_C8_lt
          have := Real.eulerMascheroniConstant_lt_two_thirds
          unfold C8 at *
          linarith
        have := log_six_four_le
        linarith

/-- `log T_y = log y/(51 Λ log log y) - 500` (eq. lp-zf). -/
noncomputable def logTy (Λ L : ℝ) : ℝ := L / (51 * Λ * Real.log L) - 500

/-- **The height constraint** (Step 7): under (eq. lp-yrange) `log y ≥ 10⁴ Λ² log log y`, every
`|t|` with `log(|t| + 3) ≤ log T_y + 1` has `η_t ≥ 16 log log y/log y`. -/
theorem etat_ge_of_height {Λ L t : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL0 : 10 ^ 8 ≤ L)
    (hL : 10 ^ 4 * Λ ^ 2 * Real.log L ≤ L) (ht : Lt t ≤ logTy Λ L + 1) :
    16 * Real.log L / L ≤ etat Λ t := by
  have hΛ0 : 0 < Λ := by linarith
  have hℓ : 0 < Real.log L := Real.log_pos (by linarith)
  set ℓ := Real.log L
  set Qy := L / (Λ * ℓ)
  have hQy : 10 ^ 4 * Λ ≤ Qy := by
    simp only [Qy]; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hQ0 : 0 < Qy := by nlinarith
  have hlogΛ : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hLt : Lt t ≤ Qy / 51 - 499 := by
    have : logTy Λ L = Qy / 51 - 500 := by
      simp only [logTy, Qy, ℓ]; field_simp
    linarith
  set X := Lt t + 442 + 2 * Real.log Λ
  have hX1 : 1 ≤ X := by have := Lt_nonneg t; linarith
  have hXQ : X ≤ Qy := by nlinarith
  have hlogX : Real.log X ≤ Real.log Qy := Real.log_le_log (by linarith) hXQ
  have hlogQ : Real.log Qy ≤ Qy / 1000 := by
    have h1 := Real.log_le_rpow_div (x := Qy) hQ0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : Qy ^ (1 / 2 : ℝ) * Qy ^ (1 / 2 : ℝ) = Qy := by
      rw [← Real.rpow_add hQ0]; norm_num
    have h3 : (10 : ℝ) ^ 6 ≤ Qy := by nlinarith
    have h4 : (10 : ℝ) ^ 3 ≤ Qy ^ (1 / 2 : ℝ) := by
      have : ((10 : ℝ) ^ 6) ^ (1 / 2 : ℝ) ≤ Qy ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h3 (by norm_num)
      rwa [show ((10 : ℝ) ^ 6) ^ (1 / 2 : ℝ) = 10 ^ 3 by
        rw [show ((10 : ℝ) ^ 6) = (10 ^ 3) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num] at this
    have h5 : 0 ≤ Qy ^ (1 / 2 : ℝ) := by positivity
    rw [div_div_eq_mul_div] at h1
    nlinarith
  have hY : Yt Λ t ≤ 0.33769 / 16 * Qy := by
    unfold Yt
    change X + Real.log X + 0.7 ≤ 0.33769 / 16 * Qy
    nlinarith
  unfold etat
  have hYpos : 0 < Yt Λ t := lt_of_lt_of_le (by norm_num) (Yt_ge (by linarith) t)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  have : Λ * Yt Λ t ≤ 0.33769 / 16 * (L / ℓ) := by
    have e : Qy = (L / ℓ) / Λ := by simp only [Qy]; field_simp
    rw [e] at hY
    have := mul_le_mul_of_nonneg_left hY hΛ0.le
    calc Λ * Yt Λ t ≤ Λ * (0.33769 / 16 * (L / ℓ / Λ)) := this
      _ = 0.33769 / 16 * (L / ℓ) := by field_simp
  have e2 : 0.33769 / 16 * (L / ℓ) * (16 * ℓ) = 0.33769 * L := by field_simp
  nlinarith

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `ζ^♯ ≠ 0` on `1 + 8 log log y/log y ≤ σ ≤ 2`. -/
theorem zetaSharp_ne_zero_right {s : ℂ}
    (hs1 : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ s.re) (hs2 : s.re ≤ 2) :
    zetaSharp P θ X₀ α γ xp y s ≠ 0 := by
  have hL := h.logy_ge
  have hg := h.norm_g_le hs1 hs2
  have hs0 : 0 < s.re := by
    have : 0 ≤ 8 * Real.log (Real.log y) / Real.log y :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) (by linarith)
    linarith
  rw [h.zetaSharp_eq_mul hs0]
  refine mul_ne_zero (zetaF_ne_zero P _ hs0) ?_
  intro e
  have : gJ P θ X₀ α γ xp y s = -1 := by linear_combination e
  rw [this, norm_neg, norm_one, one_mul] at hg
  have : ((10 : ℝ) ^ 8) ^ 4 ≤ Real.log y ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  norm_num at this; linarith

/-- `|ζ^♯(1 + η + it)| ≥ 0.98 η` for `16 log log y/log y ≤ η ≤ 10^{-4}`. -/
theorem norm_zetaSharp_ge {s : ℂ}
    (hs1 : 1 + 16 * Real.log (Real.log y) / Real.log y ≤ s.re) (hs2 : s.re ≤ 1 + 1 / 10 ^ 4) :
    0.98 * (s.re - 1) ≤ ‖zetaSharp P θ X₀ α γ xp y s‖ := by
  set L := Real.log y
  have hL := h.logy_ge
  have hLL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have h8 : 1 + 8 * Real.log L / L ≤ s.re := by
    have : 8 * Real.log L / L ≤ 16 * Real.log L / L := by
      apply div_le_div_of_nonneg_right _ (by linarith); linarith
    linarith
  have hσ : 1 < s.re := by
    have : 0 < 16 * Real.log L / L := div_pos (mul_pos (by norm_num)
      (Real.log_pos (by linarith))) (by linarith)
    linarith
  have hs0 : 0 < s.re := by linarith
  set η := s.re - 1
  have hη0 : 0 < η := by simp only [η]; linarith
  have hg := h.norm_g_le h8 (by linarith)
  have hL4 : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg' : ‖gJ P θ X₀ α γ xp y s‖ ≤ 1 / 10 ^ 32 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [norm_nonneg (gJ P θ X₀ α γ xp y s)]
  have hZ := h.zetaFR_le hσ (by linarith)
  have hinv := norm_inv_zetaF_le P (P.primesLe y) hs0
  have hE := h.rpow_mul_log_pow_le h8
  have hκ := (kap_facts h.logX).2.2.2.1
  have hκ0 := (kap_facts h.logX).2.2.1
  -- `ζ_J(σ) ≤ (1 + 2κ)/η + 71`
  have hEL : y ^ (1 - s.re) * (Real.exp 11 * Real.log y ^ (2 : ℝ)) ≤ 1 := by
    have he11 : Real.exp 11 ≤ 60000 := by
      have e : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
        _ ≤ 60000 := by norm_num
    rw [Real.rpow_two]
    have hyp : 0 ≤ y ^ (1 - s.re) := Real.rpow_nonneg (lt_of_lt_of_le h.X0_pos h.y_ge).le _
    have : y ^ (1 - s.re) * L ^ 2 * L ^ 6 ≤ 1 := by
      have : y ^ (1 - s.re) * L ^ 8 = y ^ (1 - s.re) * L ^ 2 * L ^ 6 := by ring
      linarith
    have hL6 : (10 : ℝ) ^ 48 ≤ L ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hL 6; norm_num at this ⊢; linarith
    have h2 : y ^ (1 - s.re) * L ^ 2 ≤ 1 / 10 ^ 48 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith [mul_nonneg hyp (sq_nonneg L)]
    calc y ^ (1 - s.re) * (Real.exp 11 * L ^ 2) = Real.exp 11 * (y ^ (1 - s.re) * L ^ 2) := by
          ring
      _ ≤ 60000 * (1 / 10 ^ 48) := mul_le_mul he11 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hZ' : zetaFR P (P.primesLe y) s.re ≤ (1 + 2 * kap X₀) / η + 71 := by linarith
  have hZpos := zetaFR_pos P (P.primesLe y) hs0
  have hzJ : 1 / ((1 + 2 * kap X₀) / η + 71) ≤ ‖zetaF P (P.primesLe y) s‖ := by
    have hne := zetaF_ne_zero P (P.primesLe y) hs0
    have h1 : ‖(zetaF P (P.primesLe y) s)⁻¹‖ ≤ (1 + 2 * kap X₀) / η + 71 := hinv.trans hZ'
    rw [norm_inv] at h1
    have hn : 0 < ‖zetaF P (P.primesLe y) s‖ := norm_pos_iff.mpr hne
    rw [div_le_iff₀ (by positivity)]
    calc 1 = ‖zetaF P (P.primesLe y) s‖ * ‖zetaF P (P.primesLe y) s‖⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hn.le
  have h1g : 1 - 1 / 10 ^ 32 ≤ ‖1 + gJ P θ X₀ α γ xp y s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-gJ P θ X₀ α γ xp y s)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  rw [h.zetaSharp_eq_mul hs0, norm_mul]
  have hηs : η ≤ 1 / 10 ^ 4 := by simp only [η]; linarith
  have key : 0.98 * η ≤ 1 / ((1 + 2 * kap X₀) / η + 71) * (1 - 1 / 10 ^ 32) := by
    rw [div_add' _ _ _ hη0.ne', one_div_div, le_div_iff₀ (by positivity)] at *
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc 0.98 * η ≤ 1 / ((1 + 2 * kap X₀) / η + 71) * (1 - 1 / 10 ^ 32) := key
    _ ≤ _ := mul_le_mul hzJ h1g (by norm_num) (norm_nonneg _)

/-- Landau's lemma at `z = 1 + η + ikt` (Step 7): with `r = 6.8/Λ` and
`Q = L_t + log Λ + log(1/η) + 439`, `-Re ζ^♯'/ζ^♯(z) ≤ (2/r) Q`, minus the zero term for a zero
`ρ` in the disc. -/
theorem landau_at {η t : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (ht : 1 / 16 ≤ |t|)
    (hη1 : 16 * Real.log (Real.log y) / Real.log y ≤ η) (hη2 : η ≤ 1 / 10 ^ 10) :
    (-(deriv (zetaSharp P θ X₀ α γ xp y) (((1 + η : ℝ) : ℂ) + k * t * I) /
        zetaSharp P θ X₀ α γ xp y (((1 + η : ℝ) : ℂ) + k * t * I))).re ≤
      2 / (6.8 / Real.log X₀) * (Lt t + Real.log (Real.log X₀) + Real.log (1 / η) + 439) ∧
    ∀ ρ ∈ closedBall (((1 + η : ℝ) : ℂ) + k * t * I) (6.8 / Real.log X₀),
      zetaSharp P θ X₀ α γ xp y ρ = 0 →
      (-(deriv (zetaSharp P θ X₀ α γ xp y) (((1 + η : ℝ) : ℂ) + k * t * I) /
        zetaSharp P θ X₀ α γ xp y (((1 + η : ℝ) : ℂ) + k * t * I))).re ≤
      2 / (6.8 / Real.log X₀) * (Lt t + Real.log (Real.log X₀) + Real.log (1 / η) + 439) -
        ((((1 + η : ℝ) : ℂ) + k * t * I) - ρ).re *
          (1 / ‖(((1 + η : ℝ) : ℂ) + k * t * I) - ρ‖ ^ 2 - 1 / (6.8 / Real.log X₀) ^ 2) := by
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log y
  set f := zetaSharp P θ X₀ α γ xp y
  set z : ℂ := ((1 + η : ℝ) : ℂ) + k * t * I with hzdef
  have hX := h.logX
  have hΛ0 : 0 < Λ := by linarith
  have hL := h.logy_ge
  have hLL : 0 < Real.log L := Real.log_pos (by linarith)
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hzre : z.re = 1 + η := by simp [hzdef]
  have hzim : z.im = k * t := by simp [hzdef]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk' : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
  have hkt : 1 / 16 ≤ |(k : ℝ) * t| := by
    rw [abs_mul, Nat.abs_cast]; nlinarith [abs_nonneg t]
  set r := 6.8 / Λ
  set R := 6.9 / Λ
  have hr0 : 0 < r := by positivity
  have hrR : r < R := by simp only [r, R]; exact div_lt_div_of_pos_right (by norm_num) hΛ0
  have hRs : R ≤ 6.9 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
  -- points of the ball
  have hball : ∀ w ∈ ball z R, 1 + η - R < w.re ∧ w.re < 1 + η + R ∧
      |(k : ℝ) * t| - R < |w.im| := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - z)
    have h2 := Complex.abs_im_le_norm (w - z)
    simp only [Complex.sub_re, Complex.sub_im, hzre, hzim] at h1 h2
    have h3 := abs_sub_abs_le_abs_sub (k * t) w.im
    refine ⟨?_, ?_, ?_⟩
    · linarith [(abs_lt.mp (lt_of_le_of_lt h1 hw)).1]
    · linarith [(abs_lt.mp (lt_of_le_of_lt h1 hw)).2]
    · rw [abs_sub_comm] at h2; linarith
  have hdiff : DifferentiableOn ℂ f (ball z R) := by
    intro w hw
    obtain ⟨h1, -, h3⟩ := hball w hw
    have hw1 : w ≠ 1 := by
      intro e; rw [e] at h3; simp at h3
      rw [abs_mul, Nat.abs_cast] at hkt; linarith [hkt, hRs]
    refine (h.differentiableAt_zetaSharp ?_ hw1).differentiableWithinAt
    linarith [h.theta_mem.2]
  -- the lower bound at the centre
  have hlow := h.norm_zetaSharp_ge (s := z) (by rw [hzre]; linarith) (by rw [hzre]; linarith)
  rw [hzre] at hlow
  simp only [add_sub_cancel_left] at hlow
  have hfz : 0 < ‖f z‖ := lt_of_lt_of_le (by positivity) hlow
  have hfz0 : f z ≠ 0 := norm_pos_iff.mp hfz
  -- the bound on the disc
  have hBk : ∀ w ∈ closedBall z r, ‖f w‖ ≤ Bk X₀ k t := by
    intro w hw
    have hwb : w ∈ ball z R := Metric.closedBall_subset_ball hrR hw
    obtain ⟨h1, h2, h3⟩ := hball w hwb
    have hw1 : w ≠ 1 := by
      intro e; rw [e] at h3; simp at h3
      rw [abs_mul, Nat.abs_cast] at hkt; linarith [hkt, hRs]
    have hwn : ‖w‖ ≤ k * |t| + 1.02 := by
      have : ‖w‖ ≤ ‖z‖ + r := by
        have := norm_le_norm_add_norm_sub' w z
        rw [mem_closedBall, dist_eq_norm] at hw; linarith
      have hz : ‖z‖ ≤ 1 + η + k * |t| := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [hzre, hzim, abs_mul, Nat.abs_cast, abs_of_pos (by linarith : (0 : ℝ) < 1 + η)]
          at this
        exact this
      have : r ≤ 6.8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      linarith
    have hgr := h.norm_zetaSharp_sub_le (s := w) (by
      have : 8 / Λ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      have : R ≤ 8 / Λ := div_le_div_of_nonneg_right (by norm_num) hΛ0.le
      linarith) hw1
    have hpole : ‖w / (w - 1)‖ ≤ 17.1 := by
      have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
      have e : w / (w - 1) = 1 + 1 / (w - 1) := by field_simp; ring
      rw [e]
      have him : 1 / 16.1 ≤ ‖w - 1‖ := by
        have := Complex.abs_im_le_norm (w - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
        linarith
      calc ‖1 + 1 / (w - 1)‖ ≤ 1 + ‖1 / (w - 1)‖ := by
            have := norm_add_le (1 : ℂ) (1 / (w - 1)); simpa using this
        _ = 1 + 1 / ‖w - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 1 + 16.1 := by
            have : 1 / ‖w - 1‖ ≤ 1 / (1 / 16.1) :=
              one_div_le_one_div_of_le (by norm_num) him
            norm_num at this ⊢; linarith
        _ = 17.1 := by norm_num
    have hκ0 := (kap_facts hX).2.2.1
    have hC0 : 0 < C8 := by unfold C8; positivity
    have hγ0 := Real.exp_pos Real.eulerMascheroniConstant
    have hXp : 0 ≤ (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by positivity
    have hmono1 : C8 * (1 + kap X₀ * ‖w‖) * Real.exp Real.eulerMascheroniConstant * Λ ≤
        C8 * (1 + kap X₀ * (k * |t| + 1.02)) * Real.exp Real.eulerMascheroniConstant * Λ := by
      gcongr
    have hmono2 : (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * ‖w‖ ≤
        (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * (k * |t| + 1.02) := by gcongr
    have htri : ‖f w‖ ≤ ‖w / (w - 1)‖ + ‖f w - w / (w - 1)‖ := by
      have := norm_add_le (w / (w - 1)) (f w - w / (w - 1)); simpa using this
    unfold Bk; linarith
  set M := Bk X₀ k t / ‖f z‖
  have hM : ∀ w ∈ closedBall z r, ‖f w‖ ≤ M * ‖f z‖ := by
    intro w hw; simp only [M]; rw [div_mul_cancel₀ _ hfz.ne']; exact hBk w hw
  have hBkpos : 0 < Bk X₀ k t := lt_of_lt_of_le hfz (hBk z (mem_closedBall_self hr0.le))
  have hlogM : Real.log M ≤ Lt t + Real.log Λ + Real.log (1 / η) + 439 := by
    simp only [M]
    rw [Real.log_div hBkpos.ne' hfz.ne']
    have h1 := log_Bk_le hX hk4 t
    have h2 : Real.log (0.98 * η) ≤ Real.log ‖f z‖ := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (by norm_num) hη0.ne'] at h2
    have h3 : -0.021 ≤ Real.log 0.98 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h4 : Real.exp (-0.021) ≤ 1 / (1 + 0.021) := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (0.021 : ℝ)])
      have : (1 : ℝ) / (1 + 0.021) ≤ 0.98 := by norm_num
      linarith
    have h5 : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
    linarith
  -- zeros in the disc have real part ≤ 1 + η
  have hzero : ∀ w ∈ closedBall z r, f w = 0 → w.re ≤ z.re := by
    intro w hw hf0
    by_contra hc; push_neg at hc
    have hwb : w ∈ ball z R := Metric.closedBall_subset_ball hrR hw
    obtain ⟨-, h2, -⟩ := hball w hwb
    rw [hzre] at hc
    have h8 : 8 * Real.log L / L ≤ η := by
      have : 8 * Real.log L / L ≤ 16 * Real.log L / L :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
    exact h.zetaSharp_ne_zero_right (s := w) (by linarith) (by linarith) hf0
  have h2r : 0 ≤ 2 / r := by positivity
  constructor
  · have := landau_lemma hr0 hrR hdiff hfz0 hM hzero
    rw [Complex.neg_re]
    calc _ ≤ 2 / r * Real.log M := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM h2r
  · intro ρ hρ hρ0
    have := landau_lemma_zero hr0 hrR hdiff hfz0 hM hzero hρ hρ0
    rw [Complex.neg_re]
    calc _ ≤ 2 / r * Real.log M - (z - ρ).re * (1 / ‖z - ρ‖ ^ 2 - 1 / r ^ 2) := this
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hlogM h2r]

/-- The pole term (eq. lp-pole): `-Re ζ^♯'/ζ^♯(1+η) ≤ 1/η + 0.43 + 3y^{-η} + 4/(η log⁴ y)`. -/
theorem pole_point {η : ℝ} (hη1 : 16 * Real.log (Real.log y) / Real.log y ≤ η) (hη2 : η ≤ 1 / 2) :
    (-(deriv (zetaSharp P θ X₀ α γ xp y) ((1 + η : ℝ) : ℂ) /
        zetaSharp P θ X₀ α γ xp y ((1 + η : ℝ) : ℂ))).re ≤
      1 / η + 0.43 + 3 * y ^ (-η) + 4 / (η * Real.log y ^ 4) := by
  set s : ℂ := ((1 + η : ℝ) : ℂ)
  have hL := h.logy_ge
  have hLL : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hsre : s.re = 1 + η := by simp [s]
  have hs : 1 < s.re := by rw [hsre]; linarith
  obtain ⟨hne, hlog⟩ := h.norm_logDeriv_g_le (s := s) (by rw [hsre]; linarith)
    (by rw [hsre]; linarith)
  rw [hsre, show 1 + η - 1 = η by ring] at hlog
  have hld := h.logDeriv_zetaSharp hs hne
  rw [logDeriv_apply] at hld
  rw [hld, neg_add, Complex.add_re]
  -- the `ζ_J` part
  have hJ : (-logDeriv (zetaF P (P.primesLe y)) s).re =
      ∑ j ∈ P.primesLe y, Real.log (P.p j) * (P.p j ^ (-(1 + η)) / (1 - P.p j ^ (-(1 + η)))) := by
    rw [logDeriv_apply, logDeriv_zetaF P _ (by linarith), neg_neg, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hp := P.p_pos j
    have e : ((P.p j : ℝ) : ℂ) ^ (-s) = ((P.p j ^ (-(1 + η)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp.le]; simp [s]
    rw [e]
    have : (Real.log (P.p j) : ℂ) * ((P.p j ^ (-(1 + η)) : ℝ) : ℂ) /
        (1 - ((P.p j ^ (-(1 + η)) : ℝ) : ℂ)) =
        ((Real.log (P.p j) * (P.p j ^ (-(1 + η)) / (1 - P.p j ^ (-(1 + η)))) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [hJ]
  have hpole := h.pole_le hη0
  have hg : (-logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s).re ≤ 4 / (η * Real.log y ^ 4) := by
    have h1 := Complex.re_le_norm (-logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s)
    rw [norm_neg] at h1
    have hpos : 0 < η * Real.log y ^ 4 := by positivity
    rw [le_div_iff₀ hpos]
    calc _ ≤ ‖logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s‖ * (η * Real.log y ^ 4) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ ≤ 4 := hlog
  linarith

/-- The 3-4 sum for `ζ^♯`: `∑_k a_k Re(-ζ^♯'/ζ^♯)(1 + η + ikt) ≥ -512/(η log⁴ y)`. -/
theorem threeFour_sharp {η : ℝ} (hη1 : 16 * Real.log (Real.log y) / Real.log y ≤ η)
    (hη2 : η ≤ 1 / 2) (t : ℝ) :
    -(512 / (η * Real.log y ^ 4)) ≤ ∑ k ∈ Finset.range 5, aw k *
      (-(deriv (zetaSharp P θ X₀ α γ xp y) (((1 + η : ℝ) : ℂ) + k * t * I) /
        zetaSharp P θ X₀ α γ xp y (((1 + η : ℝ) : ℂ) + k * t * I))).re := by
  have hL := h.logy_ge
  have hLL : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hpos : 0 < η * Real.log y ^ 4 := by positivity
  have h34 := threeFour P (P.primesLe y) (σ := 1 + η) (by linarith) t
  have hk : ∀ k : ℕ, (-(deriv (zetaF P (P.primesLe y)) (((1 + η : ℝ) : ℂ) + k * t * I) /
        zetaF P (P.primesLe y) (((1 + η : ℝ) : ℂ) + k * t * I))).re -
        4 / (η * Real.log y ^ 4) ≤
      (-(deriv (zetaSharp P θ X₀ α γ xp y) (((1 + η : ℝ) : ℂ) + k * t * I) /
        zetaSharp P θ X₀ α γ xp y (((1 + η : ℝ) : ℂ) + k * t * I))).re := by
    intro k
    set z : ℂ := ((1 + η : ℝ) : ℂ) + k * t * I
    have hzre : z.re = 1 + η := by simp [z]
    obtain ⟨hne, hlog⟩ := h.norm_logDeriv_g_le (s := z) (by rw [hzre]; linarith)
      (by rw [hzre]; linarith)
    rw [hzre, show 1 + η - 1 = η by ring] at hlog
    have hld := h.logDeriv_zetaSharp (s := z) (by rw [hzre]; linarith) hne
    rw [logDeriv_apply, logDeriv_apply] at hld
    rw [hld, neg_add, Complex.add_re]
    have h1 := Complex.abs_re_le_norm (logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) z)
    have h2 : ‖logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) z‖ ≤ 4 / (η * Real.log y ^ 4) := by
      rw [le_div_iff₀ hpos]; exact hlog
    rw [Complex.neg_re (logDeriv _ z)]
    have := (abs_le.mp (h1.trans h2)).2
    linarith
  calc -(512 / (η * Real.log y ^ 4)) ≤ ∑ k ∈ Finset.range 5, aw k *
        (-(deriv (zetaF P (P.primesLe y)) (((1 + η : ℝ) : ℂ) + k * t * I) /
          zetaF P (P.primesLe y) (((1 + η : ℝ) : ℂ) + k * t * I))).re -
        ∑ k ∈ Finset.range 5, aw k * (4 / (η * Real.log y ^ 4)) := by
        rw [← Finset.sum_mul, aw_sum]
        have : 512 / (η * Real.log y ^ 4) = 128 * (4 / (η * Real.log y ^ 4)) := by ring
        rw [this]; push_cast at h34 ⊢; linarith
    _ = ∑ k ∈ Finset.range 5, aw k *
        ((-(deriv (zetaF P (P.primesLe y)) (((1 + η : ℝ) : ℂ) + k * t * I) /
          zetaF P (P.primesLe y) (((1 + η : ℝ) : ℂ) + k * t * I))).re -
          4 / (η * Real.log y ^ 4)) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (aw_nonneg k)

/-- **The zero-free region, explicit width** (Step 7, eq. lp-width): for `|t| ≥ 1/16` with
`η_t = 0.33769/(Λ Y(t)) ≥ 16 log log y/log y`, `ζ^♯(σ + it) ≠ 0` for `1 - η_t/3.79 ≤ σ ≤ 2`. -/
theorem zeroFree_width {t : ℝ} (ht : 1 / 16 ≤ |t|)
    (hη : 16 * Real.log (Real.log y) / Real.log y ≤ etat (Real.log X₀) t) {σ : ℝ}
    (hσ1 : 1 - etat (Real.log X₀) t / 3.79 ≤ σ) (hσ2 : σ ≤ 2) :
    zetaSharp P θ X₀ α γ xp y ((σ : ℂ) + t * I) ≠ 0 := by
  intro hz
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log y
  set η := etat Λ t with hηdef
  have hX := h.logX
  have hΛ0 : 0 < Λ := by linarith
  have hL := h.logy_ge
  have hLL : 0 < Real.log L := Real.log_pos (by linarith)
  have hη0 : 0 < η := etat_pos (by linarith) t
  have hηs : η ≤ 1 / 10 ^ 10 := etat_le hX t
  have hηΛ : η * Λ ≤ 0.33769 / 442 := by
    simp only [η, etat]
    have hY := Yt_ge (Λ := Λ) (by linarith) t
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the zero is to the left of `1 + 8 log log y/log y`
  by_cases hσr : 1 + 8 * Real.log L / L ≤ σ
  · exact h.zetaSharp_ne_zero_right (s := (σ : ℂ) + t * I) (by simpa using hσr)
      (by simpa using hσ2) hz
  push_neg at hσr
  have h8 : 8 * Real.log L / L ≤ η / 2 := by
    have : 8 * Real.log L / L = (16 * Real.log L / L) / 2 := by ring
    linarith
  set d := 1 + η - σ with hd
  have hd0 : 0 < d := by linarith
  have hd1 : d ≤ η * (1 + 1 / 3.79) := by
    have : η * (1 + 1 / 3.79) = η + η / 3.79 := by ring
    linarith
  set r := 6.8 / Λ
  have hr0 : 0 < r := by positivity
  have hdr : d ≤ r := by
    have : d * Λ ≤ 6.8 := by nlinarith
    rw [le_div_iff₀ hΛ0]; linarith
  set Q := Lt t + Real.log Λ + Real.log (1 / η) + 439
  -- the five centres
  set z : ℕ → ℂ := fun k => ((1 + η : ℝ) : ℂ) + k * t * I
  set F : ℕ → ℝ := fun k => (-(deriv (zetaSharp P θ X₀ α γ xp y) (z k) /
    zetaSharp P θ X₀ α γ xp y (z k))).re
  have h34 := h.threeFour_sharp (η := η) hη (by linarith) t
  have hF0 : F 0 ≤ 1 / η + 0.43 + 3 * y ^ (-η) + 4 / (η * L ^ 4) := by
    have := h.pole_point (η := η) hη (by linarith)
    have hz0 : z 0 = ((1 + η : ℝ) : ℂ) := by simp [z]
    simp only [F, hz0]; exact this
  have hFk : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → F k ≤ 2 / r * Q := fun k hk1 hk4 =>
    (h.landau_at hk1 hk4 ht hη hηs).1
  have hF1 : F 1 ≤ 2 / r * Q - 1 / d + d / r ^ 2 := by
    have hρ : (σ : ℂ) + t * I ∈ closedBall (z 1) r := by
      rw [mem_closedBall, dist_eq_norm]
      have : z 1 - ((σ : ℂ) + t * I) = (d : ℂ) := by
        simp only [z, hd]; push_cast; ring
      rw [norm_sub_rev, this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]; exact hdr
    have := (h.landau_at (k := 1) le_rfl (by norm_num) ht hη hηs).2 _ hρ hz
    change F 1 ≤ 2 / r * Q - (z 1 - ((σ : ℂ) + t * I)).re *
      (1 / ‖z 1 - ((σ : ℂ) + t * I)‖ ^ 2 - 1 / r ^ 2) at this
    have e : z 1 - ((σ : ℂ) + t * I) = (d : ℂ) := by
      simp only [z, hd]; push_cast; ring
    rw [e, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0] at this
    have e2 : d * (1 / d ^ 2 - 1 / r ^ 2) = 1 / d - d / r ^ 2 := by field_simp
    linarith
  have hsum : ∑ k ∈ Finset.range 5, aw k * F k =
      35 * F 0 + 56 * F 1 + 28 * F 2 + 8 * F 3 + 1 * F 4 := by
    simp [Finset.sum_range_succ, aw]
  have h34' : -(512 / (η * L ^ 4)) ≤ ∑ k ∈ Finset.range 5, aw k * F k := h34
  rw [hsum] at h34'
  have hF2 := hFk 2 (by norm_num) (by norm_num)
  have hF3 := hFk 3 (by norm_num) (by norm_num)
  have hF4 := hFk 4 (by norm_num) (by norm_num)
  set ε := 1 / (η * L ^ 4)
  have hεdef : 4 / (η * L ^ 4) = 4 * ε := by simp only [ε]; ring
  have hεdef' : 512 / (η * L ^ 4) = 512 * ε := by simp only [ε]; ring
  rw [hεdef] at hF0
  rw [hεdef'] at h34'
  have hineq : -512 * ε ≤ 35 * (1 / η + 0.43 + 3 * y ^ (-η) + 4 * ε) +
      56 * (2 / (6.8 / Λ) * Q - 1 / d + d / (6.8 / Λ) ^ 2) + 37 * (2 / (6.8 / Λ) * Q) := by
    change -512 * ε ≤ 35 * (1 / η + 0.43 + 3 * y ^ (-η) + 4 * ε) +
      56 * (2 / r * Q - 1 / d + d / r ^ 2) + 37 * (2 / r * Q)
    linarith
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have he1 : y ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (le_trans h.one_le_X0 h.y_ge) (by linarith)
  have hεη : ε * η ≤ 1 / 10 ^ 30 := by
    simp only [ε]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ((10 : ℝ) ^ 8) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    nlinarith
  exact zf_contra (Λ := Λ) (Lt := Lt t) hX (Lt_nonneg t) rfl le_rfl hd0 hd1
    (Real.rpow_nonneg hy0.le _) he1 (by positivity) hεη hineq

end LPHyp

end LocalPNT

end
