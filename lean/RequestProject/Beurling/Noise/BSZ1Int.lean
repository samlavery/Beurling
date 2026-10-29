module

public import RequestProject.Beurling.Noise.BSZ1Point

/-!
# Region Z1 of Theorem 5.6: the integrals

* `exp_neg_le_quad`: `e^{-y} ≤ 1 - y + y²/2` for `y ≥ 0`;
* `integral_Fz1_le`: `∫_{w_lo}^{U(ℓ)} F ≤ 480000` for `F(w) = ρ(w-1)(1+w)⁶e^{(1+w)/2}/w`
  (on `[w_lo, 3]` by `ρ ≤ 1`, on `[3, U]` by (R3) from `2`, `ρ(w-1) ≤ ρ(2) e^{-r(2)(w-3)}`,
  and `(1+w)⁶ ≤ 6! 2⁶ e^{(1+w)/2}`);
* `integral_mass_le`: `∫_{w_lo}^{U} ρ(w-1)/w ≤ log(1/w_lo) + 1` (`(R1)`, exact up to `ρ(U)`);
* `benefit_ge`: the `Φ`-benefit `∫_1^3 ρ(w-1)(1 - e^{-k/w})/w ≥ 0.5639 k` for
  `0 ≤ k ≤ 0.13334` (the paper's `Φ_ben ≥ 0.92873 (κ_Φ/ℓ) c₂⁻`, `c₂⁻ ≥ 0.61003`; we use
  five pieces of `[1, 3]` and `ρ` antitone instead of the closed form of `c₂⁻`).
-/

@[expose] public section

open Real MeasureTheory intervalIntegral Set

namespace BSaias

namespace Z1

/-! ## Elementary bounds -/

lemma exp_neg_le_quad {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hf : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous f).continuousOn
    · intro x _; exact (by fun_prop : Differentiable ℝ f).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hd : HasDerivAt f (-1 + x + Real.exp (-x)) x := by
        have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
          (hasDerivAt_neg x).exp
        have h2 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + x) x := by
          have := ((hasDerivAt_id x).pow 2).div_const 2
          have h3 := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add this
          convert h3 using 1; simp
        convert h2.sub h1 using 1; ring
      rw [hd.deriv]
      have := Real.add_one_le_exp (-x)
      linarith
  have := hf (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
  simp only [f] at this
  simp at this
  linarith

lemma exp_one_lt' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

lemma exp_two_le : Real.exp 2 ≤ 7.39 := by
  have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := exp_one_lt'
  have h0 := (Real.exp_pos 1).le
  nlinarith

lemma exp_four_le : Real.exp 4 ≤ 54.6 := by
  have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := exp_one_lt'
  have h0 := (Real.exp_pos 1).le
  have : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ h0 this.le 4
  norm_num at this ⊢; linarith

lemma log_le_of_exp_ge {x c : ℝ} (hx : 0 < x) (h : x ≤ Real.exp c) : Real.log x ≤ c := by
  rw [← Real.log_exp c]; exact Real.log_le_log hx h

lemma rho_125 : 0.775 ≤ Dickman.rho 1.25 := by
  rw [Dickman.rho_one_two (by norm_num) (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.225 by norm_num)
  have := log_le_of_exp_ge (c := 0.225) (show (0 : ℝ) < 1.25 by norm_num)
    (by norm_num at this ⊢; linarith)
  linarith

lemma rho_15 : 0.585 ≤ Dickman.rho 1.5 := by
  rw [Dickman.rho_one_two (by norm_num) (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.415 by norm_num)
  have := log_le_of_exp_ge (c := 0.415) (show (0 : ℝ) < 1.5 by norm_num)
    (by norm_num at this ⊢; linarith)
  linarith

lemma rho_175 : 0.418 ≤ Dickman.rho 1.75 := by
  rw [Dickman.rho_one_two (by norm_num) (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.582 by norm_num)
  have := log_le_of_exp_ge (c := 0.582) (show (0 : ℝ) < 1.75 by norm_num)
    (by norm_num at this ⊢; linarith)
  linarith

lemma rho_2 : 0.3068 ≤ Dickman.rho 2 ∧ Dickman.rho 2 ≤ 0.307 := by
  rw [Dickman.rho_one_two (by norm_num) (by norm_num)]
  have := log_two_bounds
  constructor <;> linarith

lemma ratio_2 : 1.629 ≤ Dickman.ratio 2 := by
  rw [Dickman.ratio_one_two (by norm_num) (by norm_num)]
  have := log_two_bounds
  rw [le_div_iff₀ (by nlinarith)]; nlinarith

/-! ## Continuity -/

lemma continuousOn_rho_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : Continuous f) :
    ContinuousOn (fun w => Dickman.rho (w - 1) * f w / w) (uIcc a b) := by
  rw [uIcc_of_le hab]
  apply ContinuousOn.div _ continuousOn_id
  · intro w hw; simp only [id]; linarith [hw.1]
  exact ((Dickman.continuous_rho.comp (continuous_sub_right 1)).mul hf).continuousOn

lemma intervalIntegrable_Fz1 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable Fz1 volume a b := by
  have := continuousOn_rho_div ha hab (fun w => (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)))
    (by fun_prop)
  refine (this.congr ?_).intervalIntegrable
  intro w _; unfold Fz1; ring

/-! ## `∫ F` -/

lemma integral_exp_decay {C lam U : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    ∫ w in (3 : ℝ)..U, C * Real.exp (-(lam * (w - 3))) ≤ C / lam := by
  have hF : ∀ w ∈ uIcc (3 : ℝ) U, HasDerivAt (fun w => -(C / lam) * Real.exp (-(lam * (w - 3))))
      (C * Real.exp (-(lam * (w - 3)))) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => -(lam * (w - 3))) (-(lam * 1)) w :=
      (((hasDerivAt_id w).sub_const 3).const_mul lam).neg
    convert (h1.exp).const_mul (-(C / lam)) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have : 0 ≤ C / lam * Real.exp (-(lam * (U - 3))) := by positivity
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- On `[3, U]`: `F(w) ≤ 409300 · e^{-0.629(w-3)}` (in the form used below). -/
lemma Fz1_le_tail {w : ℝ} (hw : 3 ≤ w) :
    Fz1 w ≤ 0.307 * 46080 * 54.6 / 3 * Real.exp (-(0.629 * (w - 3))) := by
  unfold Fz1
  have hw0 : 0 < w := by linarith
  -- (R3) from `2`
  have hρ : Dickman.rho (w - 1) ≤ Dickman.rho 2 * Real.exp (-(Dickman.ratio 2 * (w - 1 - 2))) :=
    Dickman.rho_le_exp (by norm_num) (by linarith)
  have hr2 := ratio_2
  have hρ2 := rho_2.2
  have hρ' : Dickman.rho (w - 1) ≤ 0.307 * Real.exp (-(1.629 * (w - 3))) := by
    refine hρ.trans ?_
    apply mul_le_mul hρ2 _ (Real.exp_pos _).le (by norm_num)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ w - 3 := by linarith
    nlinarith
  -- `(1+w)⁶ ≤ 46080 e^{(1+w)/2}`
  have hp : (1 + w) ^ 6 ≤ 46080 * Real.exp (0.5 * (1 + w)) := by
    have := Real.pow_div_factorial_le_exp _ (show 0 ≤ 0.5 * (1 + w) by linarith) 6
    rw [show (Nat.factorial 6 : ℝ) = 720 by norm_num [Nat.factorial]] at this
    rw [div_le_iff₀ (by norm_num)] at this
    nlinarith
  have he4 := exp_four_le
  have hρ0 := (Dickman.rho_pos (w - 1)).le
  have key : Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)) ≤
      0.307 * 46080 * 54.6 * Real.exp (-(0.629 * (w - 3))) := by
    have e1 : Real.exp (-(1.629 * (w - 3))) * Real.exp (0.5 * (1 + w)) *
        Real.exp (0.5 * (1 + w)) = Real.exp 4 * Real.exp (-(0.629 * (w - 3))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    calc Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w))
        ≤ (0.307 * Real.exp (-(1.629 * (w - 3)))) * (46080 * Real.exp (0.5 * (1 + w))) *
          Real.exp (0.5 * (1 + w)) := by
          gcongr
      _ = 0.307 * 46080 * (Real.exp (-(1.629 * (w - 3))) * Real.exp (0.5 * (1 + w)) *
          Real.exp (0.5 * (1 + w))) := by ring
      _ = 0.307 * 46080 * (Real.exp 4 * Real.exp (-(0.629 * (w - 3)))) := by rw [e1]
      _ ≤ 0.307 * 46080 * (54.6 * Real.exp (-(0.629 * (w - 3)))) := by
          gcongr
      _ = _ := by ring
  rw [div_le_iff₀ hw0]
  have h3 : 0 ≤ Real.exp (-(0.629 * (w - 3))) := (Real.exp_pos _).le
  nlinarith

/-- On `[a, 3]` with `a ≥ 0.9`: `F(w) ≤ 4⁶ e² / 0.9`. -/
lemma Fz1_le_head {w : ℝ} (hw1 : 0.9 ≤ w) (hw3 : w ≤ 3) :
    Fz1 w ≤ 4096 * 7.39 / 0.9 := by
  unfold Fz1
  have hw0 : 0 < w := by linarith
  have hρ := Dickman.rho_le_one (w - 1)
  have hρ0 := (Dickman.rho_pos (w - 1)).le
  have hp : (1 + w) ^ 6 ≤ 4096 := by
    have := pow_le_pow_left₀ (show 0 ≤ 1 + w by linarith) (show 1 + w ≤ 4 by linarith) 6
    norm_num at this; linarith
  have he : Real.exp (0.5 * (1 + w)) ≤ 7.39 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_two_le
  have hnum : Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)) ≤ 4096 * 7.39 := by
    have h1 : Dickman.rho (w - 1) * (1 + w) ^ 6 ≤ 1 * 4096 :=
      mul_le_mul hρ hp (by positivity) (by norm_num)
    have := mul_le_mul h1 he (Real.exp_pos _).le (by norm_num)
    linarith
  calc Dickman.rho (w - 1) * (1 + w) ^ 6 * Real.exp (0.5 * (1 + w)) / w
      ≤ 4096 * 7.39 / w := div_le_div_of_nonneg_right hnum hw0.le
    _ ≤ 4096 * 7.39 / 0.9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw1

/-- `∫_a^U F ≤ 480000` for `0.9 ≤ a ≤ 3 ≤ U`. -/
lemma integral_Fz1_le {a U : ℝ} (ha : 0.9 ≤ a) (ha3 : a ≤ 3) (hU : 3 ≤ U) :
    ∫ w in a..U, Fz1 w ≤ 480000 := by
  have ha0 : 0 < a := by linarith
  rw [← integral_add_adjacent_intervals (b := 3) (intervalIntegrable_Fz1 ha0 ha3)
    (intervalIntegrable_Fz1 (by norm_num) hU)]
  have h1 : ∫ w in a..3, Fz1 w ≤ ∫ w in a..3, (4096 * 7.39 / 0.9 : ℝ) :=
    integral_mono_on ha3 (intervalIntegrable_Fz1 ha0 ha3) intervalIntegral.intervalIntegrable_const
      (fun w hw => Fz1_le_head (ha.trans hw.1) hw.2)
  have h2 : ∫ w in (3 : ℝ)..U, Fz1 w ≤
      ∫ w in (3 : ℝ)..U, 0.307 * 46080 * 54.6 / 3 * Real.exp (-(0.629 * (w - 3))) :=
    integral_mono_on hU (intervalIntegrable_Fz1 (by norm_num) hU)
      (by apply Continuous.intervalIntegrable; fun_prop) (fun w hw => Fz1_le_tail hw.1)
  have h3 := integral_exp_decay (C := 0.307 * 46080 * 54.6 / 3) (lam := 0.629) (U := U)
    (by norm_num)
    (by norm_num)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have : (3 - a) * (4096 * 7.39 / 0.9) ≤ 2.1 * (4096 * 7.39 / 0.9) :=
    mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  linarith

/-! ## The mass of `π` -/

/-- `∫_a^U ρ(w-1)/w ≤ log(1/a) + 1` for `0 < a ≤ 1 ≤ U`. -/
lemma integral_mass_le {a U : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hU : 1 ≤ U) :
    ∫ w in a..U, Dickman.rho (w - 1) / w ≤ Real.log (1 / a) + 1 := by
  have hi1 : IntervalIntegrable (fun w => Dickman.rho (w - 1) / w) volume a 1 := by
    have := continuousOn_rho_div ha ha1 (fun _ => (1 : ℝ)) continuous_const
    simpa using this.intervalIntegrable
  rw [← integral_add_adjacent_intervals hi1 (Dickman.intervalIntegrable_shift_div le_rfl hU),
    Dickman.integral_shift_div le_rfl hU]
  have h1 : ∫ w in a..1, Dickman.rho (w - 1) / w = ∫ w in a..1, w⁻¹ := by
    apply integral_congr
    intro w hw
    rw [uIcc_of_le ha1] at hw
    simp only
    rw [Dickman.rho_of_le_one (by linarith [hw.2]), one_div]
  rw [h1, integral_inv_of_pos ha one_pos, Dickman.rho_of_le_one le_rfl]
  have := (Dickman.rho_pos U).le
  simp only [one_div, Real.log_inv] at *
  linarith

/-! ## The `Φ`-benefit -/

/-- One piece `[a, b] ⊂ [1, ∞)` of the benefit, with `c ≤ ρ(b - 1)`. -/
lemma benefit_piece {a b c k : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (_hc : 0 ≤ c)
    (hcρ : c ≤ Dickman.rho (b - 1)) (hk : 0 ≤ k) (hk2 : k ≤ 2) :
    c * (k * (1 / a - 1 / b) - k ^ 2 / 4 * (1 / a ^ 2 - 1 / b ^ 2)) ≤
      ∫ w in a..b, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w := by
  have ha0 : 0 < a := by linarith
  have hF : ∀ w ∈ uIcc a b, HasDerivAt (fun w => c * (-(k / w) + k ^ 2 / (4 * w ^ 2)))
      (c * (k / w ^ 2 - k ^ 2 / (2 * w ^ 3))) w := by
    intro w hw
    rw [uIcc_of_le hab] at hw
    have hw0 : w ≠ 0 := by linarith [hw.1]
    have h1 : HasDerivAt (fun w : ℝ => -(k * w⁻¹)) (-(k * -(w ^ 2)⁻¹)) w :=
      ((hasDerivAt_inv hw0).const_mul k).neg
    have h3 : HasDerivAt (fun w : ℝ => 4 * w ^ 2) (4 * (2 * w)) w := by
      have := (hasDerivAt_pow 2 w).const_mul 4
      simpa using this
    have h2 : HasDerivAt (fun w : ℝ => k ^ 2 * (4 * w ^ 2)⁻¹)
        (k ^ 2 * (-(4 * (2 * w)) / (4 * w ^ 2) ^ 2)) w :=
      (h3.inv (by positivity)).const_mul (k ^ 2)
    convert (h1.add h2).const_mul c using 1
    field_simp; ring
  have hcont : ContinuousOn (fun w => c * (k / w ^ 2 - k ^ 2 / (2 * w ^ 3))) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro w hw; have : 0 < w := (by linarith [hw.1]); exact pow_ne_zero _ this.ne'
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.mul (continuousOn_pow 3))
      intro w hw; have : 0 < w := (by linarith [hw.1]); simp only [Pi.mul_apply]; positivity
  have hval := integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable)
  have hmono : ∫ w in a..b, c * (k / w ^ 2 - k ^ 2 / (2 * w ^ 3)) ≤
      ∫ w in a..b, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w := by
    apply integral_mono_on hab hcont.intervalIntegrable
    · have := continuousOn_rho_div ha0 hab (fun w => 1 - Real.exp (-(k / w)))
      · refine (ContinuousOn.intervalIntegrable ?_)
        rw [uIcc_of_le hab]
        apply ContinuousOn.div _ continuousOn_id
        · intro w hw; simp only [id]; linarith [hw.1]
        apply ContinuousOn.mul
        · exact (Dickman.continuous_rho.comp (continuous_sub_right 1)).continuousOn
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.rexp
          apply ContinuousOn.neg
          apply ContinuousOn.div continuousOn_const continuousOn_id
          intro w hw; simp only [id]; linarith [hw.1]
    · intro w hw
      have hw0 : 0 < w := by linarith [hw.1]
      have hy : 0 ≤ k / w := div_nonneg hk hw0.le
      have hy2 : k / w ≤ 2 := by
        rw [div_le_iff₀ hw0]; nlinarith [hw.1]
      have hq := exp_neg_le_quad hy
      have hρ : c ≤ Dickman.rho (w - 1) := hcρ.trans (Dickman.rho_antitone (by linarith [hw.2]))
      have hpos : 0 ≤ k / w - (k / w) ^ 2 / 2 := by nlinarith
      have e : c * (k / w ^ 2 - k ^ 2 / (2 * w ^ 3)) = c * (k / w - (k / w) ^ 2 / 2) / w := by
        field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hw0.le
      exact mul_le_mul hρ (by linarith) hpos (Dickman.rho_pos _).le
  rw [hval] at hmono
  have hb0 : 0 < b := by linarith
  have e : c * (-(k / b) + k ^ 2 / (4 * b ^ 2)) - c * (-(k / a) + k ^ 2 / (4 * a ^ 2)) =
      c * (k * (1 / a - 1 / b) - k ^ 2 / 4 * (1 / a ^ 2 - 1 / b ^ 2)) := by
    field_simp; ring
  linarith

lemma benefit_integrable (k : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w => Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w)
      volume a b := by
  refine (ContinuousOn.intervalIntegrable ?_)
  rw [uIcc_of_le hab]
  apply ContinuousOn.div _ continuousOn_id
  · intro w hw; simp only [id]; linarith [hw.1]
  apply ContinuousOn.mul
  · exact (Dickman.continuous_rho.comp (continuous_sub_right 1)).continuousOn
  · apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.rexp
    apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro w hw; simp only [id]; linarith [hw.1]

/-- **The `Φ`-benefit**: `∫_1^3 ρ(w-1)(1 - e^{-k/w})/w ≥ 0.5639 k` for `0 ≤ k ≤ 0.13334`. -/
lemma benefit_ge {k : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 0.13334) :
    0.5639 * k ≤ ∫ w in (1 : ℝ)..3, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w := by
  have I := fun a b (ha : (0 : ℝ) < a) (hab : a ≤ b) => benefit_integrable k ha hab
  rw [← integral_add_adjacent_intervals (b := 2.75) (I 1 2.75 (by norm_num) (by norm_num))
      (I 2.75 3 (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals (b := 2.5) (I 1 2.5 (by norm_num) (by norm_num))
      (I 2.5 2.75 (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals (b := 2.25) (I 1 2.25 (by norm_num) (by norm_num))
      (I 2.25 2.5 (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals (b := 2) (I 1 2 (by norm_num) (by norm_num))
      (I 2 2.25 (by norm_num) (by norm_num))]
  have hk2 : k ≤ 2 := by linarith
  have p1 := benefit_piece (a := 1) (b := 2) (c := 1) (k := k) le_rfl (by norm_num)
    (by norm_num) (by norm_num [Dickman.rho_of_le_one]) hk hk2
  have p2 := benefit_piece (a := 2) (b := 2.25) (c := 0.775) (k := k) (by norm_num)
    (by norm_num) (by norm_num) (by convert rho_125 using 2; norm_num) hk hk2
  have p3 := benefit_piece (a := 2.25) (b := 2.5) (c := 0.585) (k := k) (by norm_num)
    (by norm_num) (by norm_num) (by convert rho_15 using 2; norm_num) hk hk2
  have p4 := benefit_piece (a := 2.5) (b := 2.75) (c := 0.418) (k := k) (by norm_num)
    (by norm_num) (by norm_num) (by convert rho_175 using 2; norm_num) hk hk2
  have p5 := benefit_piece (a := 2.75) (b := 3) (c := 0.3068) (k := k) (by norm_num)
    (by norm_num) (by norm_num) (by convert rho_2.1 using 2; norm_num) hk hk2
  norm_num at p1 p2 p3 p4 p5
  nlinarith

end Z1

end BSaias

end
