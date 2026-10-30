module

public import RequestProject.Beurling.OscMellin

/-!
# Auxiliary estimates for Lemma 4.6 (the designed zero)

* `norm_one_sub_exp_neg_ge` : `|1 - e^{-ξ}| ≥ 3/5` on `|ξ| = 1` (step 5 of the proof of Lemma 4.6;
  the paper uses the sharp value `1 - e^{-1}`);
* `norm_log_sub_log_le` : the principal logarithm is `2`-Lipschitz on `|z - 1| < 1/2`;
* `exists_fixedPoint_closedBall` : the contraction principle on a closed disc (step 3);
* `norm_phiTransform_sub_le` : `Φ` is `1`-Lipschitz on `Re w ≥ 0` (the bound `|Φ'| ≤ 1`);
* `one_sixth_le_norm_phiTransform` : `|Φ(w)| ≥ 1/6` for `0 ≤ Re w ≤ 1`, `|Im w| ≤ 1`
  (from `Re Φ ≥ e^{-1} cos 1`);
* `large_L` : for `Λ ≥ 10` and `log L ≥ 2Λ`, `10⁴ Λ³ log L ≤ L`.
-/

@[expose] public section

open Complex Metric Set SmoothStep

namespace DesignedZero

/-- `|1 - e^{-ξ}| ≥ 3/5` on the unit circle `|ξ| = 1`. -/
lemma norm_one_sub_exp_neg_ge {ξ : ℂ} (hξ : ‖ξ‖ = 1) : (3 / 5 : ℝ) ≤ ‖1 - Complex.exp (-ξ)‖ := by
  have hb := Complex.exp_bound (x := -ξ) (by rw [norm_neg, hξ]) (n := 4) (by norm_num)
  simp only [norm_neg, hξ, one_pow, one_mul, Finset.sum_range_succ, Finset.sum_range_zero] at hb
  norm_num [Nat.factorial] at hb
  set p : ℂ := ξ * (6 - 3 * ξ + ξ ^ 2) / 6 with hp
  have hsplit : 1 - Complex.exp (-ξ) =
      p - (Complex.exp (-ξ) - (1 + -ξ + ξ ^ 2 / 2 + -ξ ^ 3 / 6)) := by
    rw [hp]; ring
  have hq : (395 / 100 : ℝ) ≤ ‖6 - 3 * ξ + ξ ^ 2‖ := by
    have h1 : ξ.re ^ 2 + ξ.im ^ 2 = 1 := by
      have := Complex.sq_norm ξ
      rw [hξ, Complex.normSq_apply] at this; nlinarith
    have h2 : (395 / 100 : ℝ) ^ 2 ≤ ‖6 - 3 * ξ + ξ ^ 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [pow_two]
      nlinarith [sq_nonneg (ξ.re - 7/8)]
    exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |>.2
  have hpn : (395 / 600 : ℝ) ≤ ‖p‖ := by
    rw [hp, norm_div, norm_mul, hξ]; simp; linarith
  rw [hsplit]
  have : ‖p‖ - ‖Complex.exp (-ξ) - (1 + -ξ + ξ ^ 2 / 2 + -ξ ^ 3 / 6)‖ ≤
      ‖p - (Complex.exp (-ξ) - (1 + -ξ + ξ ^ 2 / 2 + -ξ ^ 3 / 6))‖ := norm_sub_norm_le _ _
  have hb' : ‖Complex.exp (-ξ) - (1 + -ξ + ξ ^ 2 / 2 + -ξ ^ 3 / 6)‖ ≤ 5/96 := by
    convert! hb using 3; ring
  linarith

/-- The principal logarithm is `2`-Lipschitz on the disc `|z - 1| < 1/2`. -/
lemma norm_log_sub_log_le {a b : ℂ} (ha : ‖a - 1‖ < 1 / 2) (hb : ‖b - 1‖ < 1 / 2) :
    ‖Complex.log a - Complex.log b‖ ≤ 2 * ‖a - b‖ := by
  have hmem : ∀ z ∈ ball (1 : ℂ) (1 / 2), z ∈ slitPlane ∧ (1/2 : ℝ) ≤ ‖z‖ := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre : |z.re - 1| < 1/2 := by
      have := Complex.abs_re_le_norm (z - 1); simp at this; linarith
    have hn : (1/2 : ℝ) ≤ ‖z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - z)
      rw [norm_sub_rev] at hz; simp at this; linarith
    refine ⟨Or.inl ?_, hn⟩
    have := (abs_lt.mp hre).1; linarith
  exact (convex_ball (1 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
    (f := Complex.log) (C := 2)
    (fun z hz => Complex.differentiableAt_log (hmem z hz).1)
    (fun z hz => by
      rw [(Complex.hasDerivAt_log (hmem z hz).1).deriv, norm_inv]
      have := (hmem z hz).2
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith)
    (x := b) (y := a) (by rw [mem_ball, dist_eq_norm]; exact hb)
    (by rw [mem_ball, dist_eq_norm]; exact ha)

/-- **Contraction principle on a closed disc.** -/
lemma exists_fixedPoint_closedBall {F : ℂ → ℂ} {c : ℂ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q)
    (hq : q < 1) (hmaps : ∀ w ∈ closedBall c r, F w ∈ closedBall c r)
    (hlip : ∀ w₁ ∈ closedBall c r, ∀ w₂ ∈ closedBall c r, ‖F w₁ - F w₂‖ ≤ q * ‖w₁ - w₂‖) :
    ∃ w ∈ closedBall c r, F w = w := by
  have hsf : MapsTo F (closedBall c r) (closedBall c r) := hmaps
  have hc : ContractingWith ⟨q, hq0⟩ (hsf.restrict F _ _) := by
    refine ⟨by exact_mod_cast hq, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [MapsTo.restrict, Subtype.dist_eq, dist_eq_norm, NNReal.coe_mk]
    exact hlip _ x.2 _ y.2
  obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' isClosed_closedBall.isComplete hsf
    (mem_closedBall_self hr) (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

/-- `exp` is `1`-Lipschitz on the closed left half-plane. -/
lemma norm_cexp_sub_cexp_le {a b : ℂ} (ha : a.re ≤ 0) (hb : b.re ≤ 0) :
    ‖Complex.exp a - Complex.exp b‖ ≤ ‖a - b‖ := by
  have hconv : Convex ℝ {z : ℂ | z.re ≤ 0} := convex_halfSpace_re_le 0
  have := hconv.norm_image_sub_le_of_norm_deriv_le (f := Complex.exp) (C := 1)
    (fun z _ => Complex.differentiableAt_exp)
    (fun z hz => by rw [Complex.deriv_exp, Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hz)
    hb ha
  simpa using this

/-- `Φ` is `1`-Lipschitz on `Re w ≥ 0` (the bound `|Φ'| ≤ 1` of step 3). -/
lemma norm_phiTransform_sub_le {w₁ w₂ : ℂ} (h₁ : 0 ≤ w₁.re) (h₂ : 0 ≤ w₂.re) :
    ‖phiTransform w₁ - phiTransform w₂‖ ≤ ‖w₁ - w₂‖ := by
  unfold phiTransform
  rw [← intervalIntegral.integral_sub ((continuous_phiIntegrand _).intervalIntegrable _ _)
    ((continuous_phiIntegrand _).intervalIntegrable _ _)]
  have hb : ∫ v in (0:ℝ)..1, ‖w₁ - w₂‖ * deriv Real.smoothTransition v = ‖w₁ - w₂‖ := by
    rw [intervalIntegral.integral_const_mul, integral_deriv_smoothTransition, mul_one]
  rw [← hb]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_
    ((continuous_const.mul continuous_deriv_smoothTransition).intervalIntegrable _ _)
  refine Filter.Eventually.of_forall fun v hv => ?_
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (deriv_smoothTransition_nonneg v)]
  apply mul_le_mul_of_nonneg_right _ (deriv_smoothTransition_nonneg v)
  have hv0 : 0 ≤ v := hv.1.le
  have hv1 : v ≤ 1 := hv.2
  refine (norm_cexp_sub_cexp_le (by simp; nlinarith) (by simp; nlinarith)).trans ?_
  rw [show -w₁ * (v:ℂ) - -w₂ * v = -((w₁ - w₂) * v) by ring, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
  exact mul_le_of_le_one_right (norm_nonneg _) hv1

/-- `|Φ(w)| ≥ 1/6` on `0 ≤ Re w ≤ 1`, `|Im w| ≤ 1`, from `Re Φ ≥ e^{-1} cos 1 ≥ 1/6`. -/
lemma one_sixth_le_norm_phiTransform {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1)
    (him : |w.im| ≤ 1) : (1 / 6 : ℝ) ≤ ‖phiTransform w‖ := by
  have h := re_phiTransform_ge h0 h1 him
  have hc : (1/2 : ℝ) ≤ Real.cos 1 := by
    have := Real.one_sub_sq_div_two_le_cos (x := 1); norm_num at this; linarith
  have he : (1/3 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have := Complex.re_le_norm (phiTransform w)
  nlinarith

/-- For `Λ ≥ 10` and `log L ≥ 2Λ` (i.e. `log log x ≥ 2 log X₀`): `10⁴ Λ³ log L ≤ L`. -/
lemma large_L {Λ L : ℝ} (hΛ : 10 ≤ Λ) (hL : 0 < L) (hLL : 2 * Λ ≤ Real.log L) :
    10 ^ 4 * Λ ^ 3 * Real.log L ≤ L := by
  set y := Real.log L with hy
  have hLe : L = Real.exp y := (Real.exp_log hL).symm
  have hy20 : 20 ≤ y := by linarith
  have hΛy : Λ ≤ y / 2 := by linarith
  have h1 : 10 ^ 4 * Λ ^ 3 * y ≤ 1250 * y ^ 4 := by
    have : Λ ^ 3 ≤ (y/2) ^ 3 := pow_le_pow_left₀ (by linarith) hΛy 3
    nlinarith
  set t := y - 20
  have ht : 0 ≤ t := by linarith
  have h2 : (1 + t / 20) ^ 4 ≤ Real.exp t := by
    have h := Real.add_one_le_exp (t / 20)
    have : (1 + t/20) ^ 4 ≤ Real.exp (t/20) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    rw [← Real.exp_nat_mul] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    push_cast; linarith
  have h3 : (2 * 10 ^ 8 : ℝ) ≤ Real.exp 20 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have : (2.7 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) he 20
    rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
  have h4 : 1250 * y ^ 4 = 2 * 10 ^ 8 * (1 + t / 20) ^ 4 := by
    simp only [t]; ring
  have h5 : Real.exp y = Real.exp 20 * Real.exp t := by
    rw [← Real.exp_add]; congr 1; simp [t]
  rw [hLe, h5]
  calc 10 ^ 4 * Λ ^ 3 * y ≤ 2 * 10 ^ 8 * (1 + t / 20) ^ 4 := by linarith
    _ ≤ Real.exp 20 * Real.exp t := by
      apply mul_le_mul h3 h2 (by positivity) (by positivity)

/-- A product of three numbers within `ε ≤ 1` of `1` is within `7ε` of `1`. -/
lemma norm_mul3_sub_one_le {a b c : ℂ} {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ ≤ ε)
    (hb : ‖b - 1‖ ≤ ε) (hc : ‖c - 1‖ ≤ ε) : ‖a * b * c - 1‖ ≤ 7 * ε := by
  have hb2 : ‖b‖ ≤ 2 := by
    have := norm_sub_norm_le b 1; simp at this; linarith
  have hc2 : ‖c‖ ≤ 2 := by
    have := norm_sub_norm_le c 1; simp at this; linarith
  have e : a * b * c - 1 = (a - 1) * b * c + (b - 1) * c + (c - 1) := by ring
  rw [e]
  have h0 : 0 ≤ ε := le_trans (norm_nonneg _) ha
  calc ‖(a - 1) * b * c + (b - 1) * c + (c - 1)‖
      ≤ ‖a - 1‖ * ‖b‖ * ‖c‖ + ‖b - 1‖ * ‖c‖ + ‖c - 1‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ ε * 2 * 2 + ε * 2 + ε := by
        gcongr
    _ = 7 * ε := by ring

end DesignedZero

end
