module

public import RequestProject.Beurling.BaseFactor

/-!
# The base factor `Z_B` made concrete (Lemma 4.2, first statement)

The paper defines, for `σ > 1`,
`Z_B(s) = ∑_{n<X₀} n^{-s} + ∑_{d∈D, d≥X₀} d^{-s} + ∫_{X₀}^∞ x^{-s}(1 - ρ_det(x)) dx`.
Its proof of Lemma 4.2 rewrites this as (15), up to the boundary terms:
`Z_B = Z_∞ - W(s) S_{≥X₀}(s) + X₀^{1-s}/(s-1) + (boundary terms)` with
`W(s) = ((1+κ)^s - 1)/(sκ)` and `S_{≥X₀}(s) = ∑_{d∈D, d≥X₀} d^{-s} = Z_∞(s) - ∑_{n<X₀} n^{-s}`.

Here the right-hand side is taken as the definition `ZBcont` of the continuation of `Z_B`
(the identity with the paper's integral for `σ > 1` is proved in `ZBIdentity`). We prove:

* `differentiableAt_ZBcont` : `ZBcont` is holomorphic on `σ > 0`, `s ≠ 1`;
* `norm_ZBcont_sub_Zinf_le` : the first statement of Lemma 4.2, `|Z_B - Z_∞| ≤ e^{-X₀²/4}` on
  `1/2 ≤ σ ≤ 2` once `κ|t| ≥ e^{X₀²/3}` (in the paper `κ|t| ≥ κΓ₁/2 ≥ e^{0.49 X₀²}/2`).
-/

@[expose] public section

open Complex Metric Set Finset

namespace BaseFactor

/-- The head `∑_{1 ≤ n < X₀} n^{-s}`. -/
noncomputable def headSum (X₀ : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 X₀, ((n : ℝ) : ℂ) ^ (-s)

/-- `W(s) = ((1+κ)^s - 1)/(sκ)` of (15). -/
noncomputable def Wfac (κ : ℝ) (s : ℂ) : ℂ :=
  (((1 + κ : ℝ) : ℂ) ^ s - 1) / (s * κ)

/-- The rigid `d` with truncated ramps: `X₀ ≤ d < (1+κ)X₀`, `d` `X₀`-smooth. -/
noncomputable def boundarySet (X₀ : ℕ) (κ : ℝ) : Finset ℕ :=
  open Classical in
  (Nat.smoothNumbersUpTo ⌊(1 + κ) * X₀⌋₊ X₀).filter
    fun d => X₀ ≤ d ∧ (d : ℝ) < (1 + κ) * X₀

/-- The boundary terms of the proof of Lemma 4.2:
`∑_{d∈D, X₀ ≤ d < (1+κ)X₀} ((d/(1+κ))^{-s} - X₀^{-s})/(sκ)`. -/
noncomputable def boundary (X₀ : ℕ) (κ : ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ boundarySet X₀ κ,
    ((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ)

/-- The continuation of the base factor, by (15) with its boundary terms:
`Z_B(s) = Z_∞(s) + X₀^{1-s}/(s-1) - W(s)(Z_∞(s) - ∑_{n<X₀} n^{-s}) + (boundary terms)`. -/
noncomputable def ZBcont (X₀ : ℕ) (κ : ℝ) (s : ℂ) : ℂ :=
  Zinf X₀ s + ((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1) - Wfac κ s * (Zinf X₀ s - headSum X₀ s) +
    boundary X₀ κ s

/-- `Z_B` is holomorphic on `σ > 0`, `s ≠ 1`. -/
theorem differentiableAt_ZBcont (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (ZBcont X₀ κ) s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ
  have hsκ : s * (κ : ℂ) ≠ 0 := mul_ne_zero hs0 (by exact_mod_cast hκ.ne')
  have hcpow : ∀ c : ℝ, 0 < c → ∀ f : ℂ → ℂ, DifferentiableAt ℂ f s →
      DifferentiableAt ℂ (fun z => ((c : ℝ) : ℂ) ^ f z) s := fun c hc f hf =>
    hf.const_cpow (Or.inl (by exact_mod_cast hc.ne'))
  have hZ := differentiableAt_Zinf X₀ hσ
  have hW : DifferentiableAt ℂ (Wfac κ) s := by
    unfold Wfac
    refine DifferentiableAt.div ?_ (differentiableAt_id.mul_const _) hsκ
    exact (hcpow _ (by linarith) _ differentiableAt_id).sub_const _
  have hH : DifferentiableAt ℂ (headSum X₀) s := by
    unfold headSum
    refine DifferentiableAt.fun_sum fun n hn => ?_
    have : (n : ℝ) ≠ 0 := by
      have := (Finset.mem_Ico.mp hn).1; positivity
    exact differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast this))
  have hB : DifferentiableAt ℂ (boundary X₀ κ) s := by
    unfold boundary
    refine DifferentiableAt.fun_sum fun d hd => ?_
    refine DifferentiableAt.div ?_ (differentiableAt_id.mul_const _) hsκ
    refine DifferentiableAt.sub ?_ ?_
    · exact differentiableAt_id.neg.const_cpow (Or.inr (by simpa using hs0))
    · exact differentiableAt_id.neg.const_cpow (Or.inr (by simpa using hs0))
  have hP : DifferentiableAt ℂ (fun z : ℂ => ((X₀ : ℝ) : ℂ) ^ (1 - z) / (z - 1)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow
      (Or.inr (by intro h; apply hs1; simp only [Pi.sub_apply, id] at h; linear_combination -h)) |>.div
      (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hs1)
  unfold ZBcont
  exact ((hZ.add hP).sub (hW.mul (hZ.sub hH))).add hB

/-- `Z_∞(σ) ≤ 4^{X₀}` for `σ ≥ 1/2`. -/
lemma ZinfR_le_four_pow (X₀ : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) : ZinfR X₀ σ ≤ 4 ^ X₀ := by
  have hfac : ∀ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ 4 := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp2 := two_le_cast hpp
    have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
      have hs : 4 / 3 ≤ Real.sqrt p := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    have h3 : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith [rpow_neg_lt_one hpp (by linarith : (0:ℝ) < σ)]
    rw [inv_le_comm₀ h3 (by norm_num)]; linarith
  calc ZinfR X₀ σ ≤ ∏ _p ∈ X₀.primesBelow, (4 : ℝ) :=
        Finset.prod_le_prod (fun p hp => (factor_pos (Nat.mem_primesBelow.mp hp).2
          (by linarith)).le) hfac
    _ = 4 ^ X₀.primesBelow.card := by rw [Finset.prod_const]
    _ ≤ 4 ^ X₀ := by
        apply pow_le_pow_right₀ (by norm_num)
        calc X₀.primesBelow.card ≤ (Finset.range X₀).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = X₀ := Finset.card_range _

lemma norm_sκ_ge {κ : ℝ} (hκ : 0 < κ) (s : ℂ) : κ * |s.im| ≤ ‖s * (κ : ℂ)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, mul_comm]
  exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) hκ.le

lemma norm_Wfac_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {s : ℂ} (hσ2 : s.re ≤ 2)
    (ht : s.im ≠ 0) : ‖Wfac κ s‖ ≤ 5 / (κ * |s.im|) := by
  have hpos : 0 < κ * |s.im| := mul_pos hκ (abs_pos.mpr ht)
  unfold Wfac
  rw [norm_div]
  apply div_le_div₀ (by norm_num) _ hpos (norm_sκ_ge hκ s)
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), norm_one]
  have : (1 + κ) ^ s.re ≤ (1 + κ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
  have h2 : (1 + κ) ^ (2 : ℝ) ≤ 4 := by
    rw [Real.rpow_two]; nlinarith
  linarith

lemma norm_pole_le {X₀ : ℕ} (hX : 1 ≤ X₀) {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (ht : s.im ≠ 0) :
    ‖((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ X₀ / |s.im| := by
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  apply div_le_div₀ (by positivity) _ (abs_pos.mpr ht)
  · have := Complex.abs_im_le_norm (s - 1)
    simpa using this
  · calc (X₀ : ℝ) ^ (1 - s).re ≤ (X₀ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX' (by simp; linarith)
      _ = X₀ := Real.rpow_one _

lemma norm_headSum_le (X₀ : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) : ‖headSum X₀ s‖ ≤ X₀ := by
  unfold headSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.Ico 1 X₀, ‖((n : ℝ) : ℂ) ^ (-s)‖ ≤ ∑ _n ∈ Finset.Ico 1 X₀, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp; linarith)
    _ ≤ X₀ := by simp

lemma card_boundarySet_le (X₀ : ℕ) {κ : ℝ} (hκ1 : κ ≤ 1) :
    ((boundarySet X₀ κ).card : ℝ) ≤ 2 * X₀ + 1 := by
  have hsub : boundarySet X₀ κ ⊆ Finset.range (2 * X₀ + 1) := by
    intro d hd
    simp only [boundarySet, Finset.mem_filter] at hd
    have h2 : (d : ℝ) < 2 * X₀ := by
      have : (0 : ℝ) ≤ X₀ := by positivity
      nlinarith [hd.2.2]
    have : d < 2 * X₀ := by exact_mod_cast h2
    simp only [Finset.mem_range]; omega
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact_mod_cast this

lemma norm_boundary_le {X₀ : ℕ} (hX : 1 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {s : ℂ}
    (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : s.im ≠ 0) :
    ‖boundary X₀ κ s‖ ≤ 5 * (2 * X₀ + 1) / (κ * |s.im|) := by
  have hpos : 0 < κ * |s.im| := mul_pos hκ (abs_pos.mpr ht)
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  unfold boundary
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ boundarySet X₀ κ, ‖((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) -
      ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ)‖ ≤ 5 / (κ * |s.im|) := by
    intro d hd
    simp only [boundarySet, Finset.mem_filter] at hd
    have hd0 : (X₀ : ℝ) ≤ d := by exact_mod_cast hd.2.1
    have hq : (X₀ : ℝ) / (1 + κ) ≤ d / (1 + κ) := div_le_div_of_nonneg_right hd0 (by linarith)
    have hq0 : 0 < (X₀ : ℝ) / (1 + κ) := by positivity
    rw [norm_div]
    apply div_le_div₀ (by norm_num) _ hpos (norm_sκ_ge hκ s)
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    have h1 : ((d : ℝ) / (1 + κ)) ^ (-s.re) ≤ ((X₀ : ℝ) / (1 + κ)) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos hq0 hq (by linarith)
    have h2 : ((X₀ : ℝ) / (1 + κ)) ^ (-s.re) ≤ (1 / 2) ^ (-s.re) := by
      apply Real.rpow_le_rpow_of_nonpos (by norm_num) _ (by linarith)
      rw [le_div_iff₀ (by linarith)]; linarith
    have h3 : ((1 / 2 : ℝ)) ^ (-s.re) ≤ 4 := by
      rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
        one_div, inv_inv]
      calc (2 : ℝ) ^ s.re ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
        _ = 4 := by norm_num
    have h4 : (X₀ : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hX' (by linarith)
    linarith
  calc ∑ d ∈ boundarySet X₀ κ, ‖((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) -
        ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ)‖ ≤ ∑ _d ∈ boundarySet X₀ κ, 5 / (κ * |s.im|) :=
        Finset.sum_le_sum hterm
    _ = (boundarySet X₀ κ).card * (5 / (κ * |s.im|)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * X₀ + 1) * (5 / (κ * |s.im|)) :=
        mul_le_mul_of_nonneg_right (card_boundarySet_le X₀ hκ1) (by positivity)
    _ = 5 * (2 * X₀ + 1) / (κ * |s.im|) := by ring

/-- The crude bound before the choice of height. -/
lemma norm_ZBcont_sub_Zinf_le_aux {X₀ : ℕ} (hX : 2 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : s.im ≠ 0) :
    ‖ZBcont X₀ κ s - Zinf X₀ s‖ ≤ 30 * 4 ^ X₀ / (κ * |s.im|) := by
  have hpos : 0 < κ * |s.im| := mul_pos hκ (abs_pos.mpr ht)
  have hX1 : 1 ≤ X₀ := by omega
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX1
  have hP := norm_pole_le hX1 hσ1 ht
  have hW := norm_Wfac_le hκ hκ1 hσ2 ht
  have hH := norm_headSum_le X₀ (s := s) (by linarith)
  have hZ : ‖Zinf X₀ s‖ ≤ 4 ^ X₀ :=
    (norm_Zinf_le X₀ (by linarith)).trans (ZinfR_le_four_pow X₀ hσ1)
  have hB := norm_boundary_le hX1 hκ hκ1 hσ1 hσ2 ht
  have h4 : (X₀ : ℝ) ≤ 4 ^ X₀ := by
    have := Nat.lt_pow_self (n := X₀) (show 1 < 4 by norm_num)
    exact_mod_cast this.le
  have hP' : ‖((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ X₀ / (κ * |s.im|) := by
    refine hP.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) hpos
    calc κ * |s.im| ≤ 1 * |s.im| := mul_le_mul_of_nonneg_right hκ1 (abs_nonneg _)
      _ = |s.im| := one_mul _
  have hWZ : ‖Wfac κ s * (Zinf X₀ s - headSum X₀ s)‖ ≤ 5 / (κ * |s.im|) * (4 ^ X₀ + X₀) := by
    rw [norm_mul]
    exact mul_le_mul hW ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _) (by positivity)
  have e : ZBcont X₀ κ s - Zinf X₀ s = ((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      Wfac κ s * (Zinf X₀ s - headSum X₀ s) + boundary X₀ κ s := by
    unfold ZBcont; ring
  rw [e]
  have h1 := norm_add_le (((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
      Wfac κ s * (Zinf X₀ s - headSum X₀ s)) (boundary X₀ κ s)
  have h2 := norm_sub_le (((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1))
      (Wfac κ s * (Zinf X₀ s - headSum X₀ s))
  have hsum : X₀ / (κ * |s.im|) + 5 / (κ * |s.im|) * (4 ^ X₀ + X₀) +
      5 * (2 * X₀ + 1) / (κ * |s.im|) ≤ 30 * 4 ^ X₀ / (κ * |s.im|) := by
    rw [div_mul_eq_mul_div, ← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hpos.le
    have : (1 : ℝ) ≤ 4 ^ X₀ := one_le_pow₀ (by norm_num)
    nlinarith
  linarith

/-- **Lemma 4.2, first statement**: for `1/2 ≤ σ ≤ 2` and `κ|t| ≥ e^{X₀²/3}`,
`|Z_B(s) - Z_∞(s)| ≤ e^{-X₀²/4}`. -/
theorem norm_ZBcont_sub_Zinf_le {X₀ : ℕ} (hX : 24 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 2)
    (ht : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * |s.im|) :
    ‖ZBcont X₀ κ s - Zinf X₀ s‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4)) := by
  have hX' : (24 : ℝ) ≤ X₀ := by exact_mod_cast hX
  have hpos : 0 < κ * |s.im| := lt_of_lt_of_le (Real.exp_pos _) ht
  have ht0 : s.im ≠ 0 := by
    intro h; rw [h, abs_zero, mul_zero] at hpos; exact lt_irrefl _ hpos
  have haux := norm_ZBcont_sub_Zinf_le_aux (X₀ := X₀) (by omega) hκ hκ1 hσ1 hσ2 ht0
  have he1 := Real.exp_one_gt_d9
  -- `4 ≤ e^{3/2}` and `30 ≤ e^4`
  have h4 : (4 : ℝ) ≤ Real.exp (3 / 2) := by
    have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    nlinarith [Real.exp_pos 1]
  have h30 : (30 : ℝ) ≤ Real.exp 4 := by
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h2 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    norm_num at h2 ⊢; linarith
  have hpow : (4 : ℝ) ^ X₀ ≤ Real.exp (3 / 2 * X₀) := by
    rw [show (3 / 2 * (X₀ : ℝ)) = X₀ * (3 / 2) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h4 _
  have hnum : 30 * (4 : ℝ) ^ X₀ ≤ Real.exp ((X₀ : ℝ) ^ 2 / 12) := by
    calc 30 * (4 : ℝ) ^ X₀ ≤ Real.exp 4 * Real.exp (3 / 2 * X₀) :=
          mul_le_mul h30 hpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 + 3 / 2 * X₀) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc ‖ZBcont X₀ κ s - Zinf X₀ s‖ ≤ 30 * 4 ^ X₀ / (κ * |s.im|) := haux
    _ ≤ Real.exp ((X₀ : ℝ) ^ 2 / 12) / Real.exp ((X₀ : ℝ) ^ 2 / 3) :=
        div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _) ht
    _ = Real.exp (-((X₀ : ℝ) ^ 2 / 4)) := by rw [← Real.exp_sub]; ring_nf

end BaseFactor

end
