module

public import RequestProject.Beurling.LocalPNT.Inversion

/-!
# §5.7: partial summation, Theorem 5.24 (ii) from (i)

The last bullet of Step 9 of the proof of Theorem 5.24 (paper, `04e-lp.tex`). Write
`Φ(u) = ∫_{[1,u]} d(Π - Π₀)/t = piRecip P u - pi0Recip u`.

* `piCount_sub_pi0_eq`: partial summation `Π(v) - Π₀(v) = v Φ(v) - ∫_1^v Φ` for `v ≥ 1`
  (`piCount_eq` for the discrete part, `pi0_eq`, by parts, for the continuous one).
* `integral_exp_neg_sqrt_log_le`: `0.99 ∫_X^v e^{-c √(log u)} du ≤ [u e^{-c √(log u)}]_X^v`.
* `lp_ii_of_i8`: from `|Φ| ≤ e^{97} Λ² e^{-c_LP √(log u)}` on `[X_LP, y]` and
  `|Φ| ≤ 2 log log X_LP + 8` on `[1, X_LP]`, the bounds (i) and (ii) of Theorem 5.24 with
  `K = e^{98} Λ^{5.9}` on `[X_LP, y]`; `lp_ii_of_i` is the same with `+ 5.5`.
* `abs_piRecip_sub_pi0Recip_le_of8`, `lp_ii_of_i8'`: the input on `[1, X_LP]` from
  `∫_{[1,u]} dΠ/t ≤ log log X_LP + 7` and `∫_{[1,u]} dΠ₀/t ≤ log log X_LP + 1`
  (`pi0Recip_le_log_log`); `abs_piRecip_sub_pi0Recip_le_of`, `lp_ii_of_i'` with `+ 4.5`/`+ 5.5`.
-/

@[expose] public section

open Set Real MeasureTheory

namespace LocalPNT

/-! ## Partial summation for `Π` -/

section Partial

variable (P : BeurlingSystem)

theorem piRecip_nonneg (v : ℝ) : 0 ≤ piRecip P v :=
  Finset.sum_nonneg fun jk _ => by
    have := (zero_lt_one.trans (P.one_lt jk.1))
    positivity

theorem monotone_piRecip : Monotone (piRecip P) := by
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun jk => ?_) fun jk _ _ => ?_
  · simp only [BeurlingSystem.mem_pps]
    exact fun h => h.trans hab
  · have := (zero_lt_one.trans (P.one_lt jk.1))
    positivity

theorem intervalIntegrable_piRecip (a b : ℝ) : IntervalIntegrable (piRecip P) volume a b :=
  (monotone_piRecip P).intervalIntegrable

/-- For `u ≤ v`, `∫_{[1,u]} dΠ/u` as a sum of step functions over the prime powers `≤ v`. -/
theorem piRecip_eq_sum_indicator {u v : ℝ} (huv : u ≤ v) :
    piRecip P u = ∑ jk ∈ P.pps v, (Ici (P.p jk.1 ^ (jk.2 + 1))).indicator
      (fun _ => 1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) u := by
  have : P.pps u = (P.pps v).filter (fun jk => P.p jk.1 ^ (jk.2 + 1) ≤ u) := by
    ext jk
    simp only [BeurlingSystem.mem_pps, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans huv, h⟩, fun h => h.2⟩
  rw [piRecip, this, Finset.sum_filter]
  rfl

theorem integral_indicator_Ici_const {a q v c : ℝ} (ha : a < q) (hq : q ≤ v) :
    ∫ u in a..v, (Ici q).indicator (fun _ => c) u = c * (v - q) := by
  rw [intervalIntegral.integral_of_le (ha.le.trans hq), integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    show Ici q ∩ Ioc a v = Icc q v by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ha.trans_le h.1, h.2⟩⟩,
    setIntegral_const, Real.volume_real_Icc_of_le hq, smul_eq_mul, mul_comm]

theorem integral_piRecip {v : ℝ} (hv : 1 ≤ v) :
    ∫ u in (1 : ℝ)..v, piRecip P u = ∑ jk ∈ P.pps v,
      1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1)) * (v - P.p jk.1 ^ (jk.2 + 1)) := by
  rw [intervalIntegral.integral_congr (g := fun u => ∑ jk ∈ P.pps v,
      (Ici (P.p jk.1 ^ (jk.2 + 1))).indicator
        (fun _ => 1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) u)
      fun u hu => piRecip_eq_sum_indicator P (by rw [uIcc_of_le hv] at hu; exact hu.2)]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun jk hjk => integral_indicator_Ici_const ?_
      (by simpa using hjk)
    exact one_lt_pow₀ (P.one_lt jk.1) (Nat.succ_ne_zero _)
  · intro jk _
    refine Monotone.intervalIntegrable fun x y hxy => ?_
    have := (zero_lt_one.trans (P.one_lt jk.1))
    simp only [indicator_apply, mem_Ici]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hxy) h2
    · positivity
    · exact le_rfl

/-- **Discrete partial summation**: `Π(v) = v ∫_{[1,v]} dΠ/u - ∫_1^v (∫_{[1,u]} dΠ/t) du`. -/
theorem piCount_eq {v : ℝ} (hv : 1 ≤ v) :
    piCount P v = v * piRecip P v - ∫ u in (1 : ℝ)..v, piRecip P u := by
  rw [integral_piRecip P hv, piRecip, Finset.mul_sum, ← Finset.sum_sub_distrib, piCount]
  refine Finset.sum_congr rfl fun jk _ => ?_
  have := (zero_lt_one.trans (P.one_lt jk.1))
  field_simp
  ring

end Partial

/-! ## Partial summation for `Π₀` -/

theorem pi0Dens_div_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ pi0Dens u / u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [pi0Dens]
  · exact div_nonneg (pi0Dens_nonneg hu) (by linarith)

theorem pi0Dens_div_le {u : ℝ} (hu : 1 ≤ u) : pi0Dens u / u ≤ 1 / u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [pi0Dens]
  · exact div_le_div_of_nonneg_right (pi0Dens_le_one hu) (by linarith)

theorem measurable_pi0Dens : Measurable pi0Dens := by
  unfold pi0Dens; fun_prop

theorem integrableOn_pi0Dens_div (v : ℝ) : IntegrableOn (fun u => pi0Dens u / u) (Icc 1 v) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    (measurable_pi0Dens.div measurable_id).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine ae_of_all _ fun u hu => ?_
  rw [Real.norm_of_nonneg (pi0Dens_div_nonneg hu.1)]
  exact (pi0Dens_div_le hu.1).trans (by rw [div_le_one (by linarith [hu.1])]; exact hu.1)

theorem continuousOn_pi0Recip {v : ℝ} (hv : 1 ≤ v) : ContinuousOn pi0Recip (Icc 1 v) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 1) (b := v)
    (by rw [uIcc_of_le hv]; exact integrableOn_pi0Dens_div v)
  rwa [uIcc_of_le hv] at this

theorem hasDerivAt_pi0Recip {x : ℝ} (hx : 1 < x) : HasDerivAt pi0Recip (pi0Dens x / x) x := by
  have hc : ContinuousOn (fun u => pi0Dens u / u) (Ioi 1) :=
    continuousOn_pi0Dens.div continuousOn_id fun u (hu : 1 < u) => by positivity
  exact intervalIntegral.integral_hasDerivAt_right
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hx.le).mpr (integrableOn_pi0Dens_div x))
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))

theorem intervalIntegrable_pi0Recip {v : ℝ} (hv : 1 ≤ v) :
    IntervalIntegrable pi0Recip volume 1 v :=
  (continuousOn_pi0Recip hv).intervalIntegrable_of_Icc hv

/-- **Continuous partial summation**: `Π₀(v) = v ∫_{[1,v]} dΠ₀/u - ∫_1^v (∫_{[1,u]} dΠ₀/t) du`. -/
theorem pi0_eq {v : ℝ} (hv : 1 ≤ v) : pi0 v = v * pi0Recip v - ∫ u in (1 : ℝ)..v, pi0Recip u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := 1) (b := v)
    (u := id) (u' := fun _ => 1) (v := pi0Recip) (v' := fun u => pi0Dens u / u)
    continuousOn_id (by rw [uIcc_of_le hv]; exact continuousOn_pi0Recip hv)
    (fun x _ => hasDerivAt_id x)
    (fun x hx => hasDerivAt_pi0Recip (by rw [min_eq_left hv] at hx; exact hx.1))
    intervalIntegrable_const
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hv).mpr (integrableOn_pi0Dens_div v))
  simp only [id, one_mul, show pi0Recip 1 = 0 from intervalIntegral.integral_same,
    mul_zero, sub_zero] at h
  rw [← h, pi0]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hv] at hu
  have : u ≠ 0 := by linarith [hu.1]
  field_simp

/-- **Partial summation** for `Π - Π₀`, with `Φ(u) = ∫_{[1,u]} d(Π - Π₀)/t`:
`Π(v) - Π₀(v) = v Φ(v) - ∫_1^v Φ`. -/
theorem piCount_sub_pi0_eq (P : BeurlingSystem) {v : ℝ} (hv : 1 ≤ v) :
    piCount P v - pi0 v = v * (piRecip P v - pi0Recip v) -
      ∫ u in (1 : ℝ)..v, (piRecip P u - pi0Recip u) := by
  rw [piCount_eq P hv, pi0_eq hv, intervalIntegral.integral_sub (intervalIntegrable_piRecip P 1 v)
    (intervalIntegrable_pi0Recip hv)]
  ring


/-! ## Theorem 5.24 (ii) from (i) -/

theorem hasDerivAt_mul_exp_neg_sqrt_log (c : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun u => u * Real.exp (-(c * Real.sqrt (Real.log u))))
      (Real.exp (-(c * Real.sqrt (Real.log u))) * (1 - c / (2 * Real.sqrt (Real.log u)))) u := by
  have hu0 : u ≠ 0 := by positivity
  have hl : 0 < Real.log u := Real.log_pos hu
  have hs : 0 < Real.sqrt (Real.log u) := Real.sqrt_pos.mpr hl
  have h := (hasDerivAt_id u).mul
    ((((Real.hasDerivAt_log hu0).sqrt hl.ne').const_mul c).neg.exp)
  convert! h using 1
  simp only [id, Pi.neg_apply]
  field_simp
  ring

theorem continuousOn_exp_neg_sqrt_log (c : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u => Real.exp (-(c * Real.sqrt (Real.log u)))) (Icc a b) :=
  ((((Real.continuousOn_log.mono fun u (hu : u ∈ Icc a b) =>
    (ha.trans_le hu.1).ne').sqrt).const_smul c).neg).rexp

/-- `∫_X^v e^{-c √(log u)} du ≤ (v e^{-c √(log v)} - X e^{-c √(log X)})/0.99` for `c ≤ 1/50`
and `e ≤ X ≤ v`: the derivative of `u e^{-c √(log u)}` is `≥ 0.99 e^{-c √(log u)}`. -/
theorem integral_exp_neg_sqrt_log_le {c X v : ℝ} (hc : c ≤ 1 / 50)
    (hX : Real.exp 1 ≤ X) (hXv : X ≤ v) :
    0.99 * ∫ u in X..v, Real.exp (-(c * Real.sqrt (Real.log u))) ≤
      v * Real.exp (-(c * Real.sqrt (Real.log v))) -
        X * Real.exp (-(c * Real.sqrt (Real.log X))) := by
  have hX1 : 1 < X := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX0 : 0 < X := one_pos.trans hX1
  have hd : ∀ u ∈ Icc X v, HasDerivAt (fun u => u * Real.exp (-(c * Real.sqrt (Real.log u))))
      (Real.exp (-(c * Real.sqrt (Real.log u))) * (1 - c / (2 * Real.sqrt (Real.log u)))) u :=
    fun u hu => hasDerivAt_mul_exp_neg_sqrt_log c (hX1.trans_le hu.1)
  have hcont : ContinuousOn (fun u => Real.exp (-(c * Real.sqrt (Real.log u))) *
      (1 - c / (2 * Real.sqrt (Real.log u)))) (Icc X v) := by
    refine (continuousOn_exp_neg_sqrt_log c hX0).mul (continuousOn_const.sub
      (continuousOn_const.div (continuousOn_const.mul ((Real.continuousOn_log.mono
        fun u (hu : u ∈ Icc X v) => (hX0.trans_le hu.1).ne').sqrt)) fun u hu => ?_))
    have := Real.log_pos (hX1.trans_le hu.1)
    positivity
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le hXv])
    (hcont.intervalIntegrable_of_Icc hXv)
  beta_reduce at hF
  rw [← hF, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hXv
    (((continuousOn_exp_neg_sqrt_log c hX0).const_smul (0.99 : ℝ)).intervalIntegrable_of_Icc hXv)
    (hcont.intervalIntegrable_of_Icc hXv) fun u hu => ?_
  have hlu : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le (hX0.trans_le hu.1)]; exact hX.trans hu.1
  have hs : 1 ≤ Real.sqrt (Real.log u) := Real.one_le_sqrt.mpr hlu
  have : c / (2 * Real.sqrt (Real.log u)) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have := Real.exp_pos (-(c * Real.sqrt (Real.log u)))
  nlinarith


theorem one_le_log_of_ge {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : 1 ≤ Real.log Λ := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_XLP {Λ : ℝ} : Real.log (XLP Λ) = 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 := by
  rw [XLP, Real.log_exp]

theorem one_le_log_XLP {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : 1 ≤ Real.log (XLP Λ) := by
  have h := one_le_log_of_ge hΛ
  rw [log_XLP]
  have : 1 ≤ Λ ^ 2 := by nlinarith
  have : 1 ≤ Real.log Λ ^ 2 := by nlinarith
  nlinarith

theorem exp_one_le_XLP {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : Real.exp 1 ≤ XLP Λ := by
  rw [XLP, Real.exp_le_exp, ← log_XLP]; exact one_le_log_XLP hΛ

/-- `e^{c √(log X)} ≤ Λ^{5.6}`: `c √(log X) = 0.0176 √(10⁵) log Λ ≤ 5.6 log Λ`. -/
theorem exp_cLP_sqrt_log_XLP_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    Real.exp (cLP Λ * Real.sqrt (Real.log (XLP Λ))) ≤ Λ ^ (5.6 : ℝ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hl := one_le_log_of_ge hΛ
  have hs : Real.sqrt (Real.log (XLP Λ)) = Real.sqrt (10 ^ 5) * (Λ * Real.log Λ) := by
    rw [log_XLP, show (10 : ℝ) ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 = 10 ^ 5 * (Λ * Real.log Λ) ^ 2 by
      ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have h317 : Real.sqrt (10 ^ 5) ≤ 317 := by
    rw [show (317 : ℝ) = Real.sqrt (317 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [Real.rpow_def_of_pos hΛ0, Real.exp_le_exp, hs, cLP, cZF]
  have : 0.088 / Λ / 5 * (Real.sqrt (10 ^ 5) * (Λ * Real.log Λ)) =
      0.0176 * Real.sqrt (10 ^ 5) * Real.log Λ := by field_simp; ring
  rw [this]
  have := mul_le_mul_of_nonneg_right h317 (by linarith : (0 : ℝ) ≤ Real.log Λ)
  norm_num at this ⊢
  nlinarith

/-- `2 log log X + 8 ≤ 3·10⁵ Λ^{0.3}` (very crude). -/
theorem two_log_log_XLP_add_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    2 * Real.log (Real.log (XLP Λ)) + 8 ≤ 3 * 10 ^ 5 * Λ ^ (0.3 : ℝ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hl := one_le_log_of_ge hΛ
  have hll : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
  have h1 : Real.log (Real.log (XLP Λ)) ≤ Real.log (10 ^ 5) + 4 * Real.log Λ := by
    rw [show Real.log (10 ^ 5) + 4 * Real.log Λ = Real.log (10 ^ 5 * Λ ^ 4) by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num]
    refine Real.log_le_log (by linarith [one_le_log_XLP hΛ]) ?_
    rw [log_XLP]
    have : Real.log Λ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by linarith) hll 2
    nlinarith [sq_nonneg Λ]
  have h2 : Real.log (10 ^ 5) ≤ 10 ^ 5 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have h3 : Real.log Λ ≤ Λ ^ (0.3 : ℝ) / 0.3 := Real.log_le_rpow_div hΛ0.le (by norm_num)
  have h4 : 1 ≤ Λ ^ (0.3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  generalize Λ ^ (0.3 : ℝ) = t at h3 h4 ⊢
  norm_num at h3 ⊢
  linarith

theorem K0_le_KLP {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : Real.exp 97 * Λ ^ 2 ≤ KLP Λ := by
  have h : Λ ^ 2 ≤ Λ ^ (5.9 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  exact mul_le_mul (Real.exp_le_exp.mpr (by norm_num)) h (by positivity) (by positivity)

/-- `(1 + 1/0.99) e^{97} Λ² + e^{c √(log X)} (2 log log X + 8) ≤ K = e^{98} Λ^{5.9}`. -/
theorem const_le_KLP {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    (1 + 1 / 0.99) * (Real.exp 97 * Λ ^ 2) + Real.exp (cLP Λ * Real.sqrt (Real.log (XLP Λ))) *
      (2 * Real.log (Real.log (XLP Λ)) + 8) ≤ KLP Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 := exp_cLP_sqrt_log_XLP_le hΛ
  have h2 := two_log_log_XLP_add_le hΛ
  have hB : 0 ≤ 2 * Real.log (Real.log (XLP Λ)) + 8 := by
    have := Real.log_nonneg (one_le_log_XLP hΛ); linarith
  have h3 : Real.exp (cLP Λ * Real.sqrt (Real.log (XLP Λ))) *
      (2 * Real.log (Real.log (XLP Λ)) + 8) ≤ 3 * 10 ^ 5 * Λ ^ (5.9 : ℝ) := by
    calc _ ≤ Λ ^ (5.6 : ℝ) * (3 * 10 ^ 5 * Λ ^ (0.3 : ℝ)) :=
          mul_le_mul h1 h2 hB (by positivity)
      _ = 3 * 10 ^ 5 * Λ ^ (5.9 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add hΛ0]; norm_num
  have h4 : Λ ^ 2 ≤ Λ ^ (5.9 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have he : (2 : ℝ) ^ 97 ≤ Real.exp 97 := by
    rw [show (97 : ℝ) = (97 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  have h98 : Real.exp 98 = Real.exp 1 * Real.exp 97 := by rw [← Real.exp_add]; norm_num
  have he1 := Real.exp_one_gt_d9
  have h5 : 0 < Λ ^ (5.9 : ℝ) := by positivity
  have key : 3 * 10 ^ 5 * Λ ^ (5.9 : ℝ) ≤
      (Real.exp 1 - (1 + 1 / 0.99)) * Real.exp 97 * Λ ^ (5.9 : ℝ) := by
    refine mul_le_mul_of_nonneg_right ?_ h5.le
    nlinarith
  rw [KLP, h98]
  have : (1 + 1 / 0.99) * (Real.exp 97 * Λ ^ 2) ≤ (1 + 1 / 0.99) * (Real.exp 97 * Λ ^ (5.9 : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) (by norm_num)
  linarith


/-- **Theorem 5.24 (ii) from (i).** With `K₀ = e^{97} Λ²`, `c = c_LP`, `X = X_LP`, the bound
`|Φ(u)| ≤ K₀ e^{-c √(log u)}` on `[X, y]` and `|Φ(u)| ≤ 2 log log X + 8` on `[1, X]` for
`Φ(u) = ∫_{[1,u]} d(Π - Π₀)/t` give, on `[X, y]`, `|Φ(v)| ≤ K e^{-c √(log v)}` and
`|Π(v) - Π₀(v)| ≤ K v e^{-c √(log v)}`, `K = e^{98} Λ^{5.9}`. -/
theorem lp_ii_of_i8 (P : BeurlingSystem) {Λ y : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hi : ∀ v, XLP Λ ≤ v → v ≤ y → |piRecip P v - pi0Recip v| ≤
      Real.exp 97 * Λ ^ 2 * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))))
    (hlow : ∀ u, 1 ≤ u → u ≤ XLP Λ → |piRecip P u - pi0Recip u| ≤
      2 * Real.log (Real.log (XLP Λ)) + 8) :
    ∀ v, XLP Λ ≤ v → v ≤ y →
      |piRecip P v - pi0Recip v| ≤ KLP Λ * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) ∧
      |piCount P v - pi0 v| ≤ KLP Λ * v * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) := by
  intro v hXv hvy
  have hX := exp_one_le_XLP hΛ
  have hX1 : 1 ≤ XLP Λ := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hv1 : 1 ≤ v := hX1.trans hXv
  have hc : cLP Λ ≤ 1 / 50 := by
    rw [cLP, cZF, div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hK := K0_le_KLP hΛ
  have hΦv := hi v hXv hvy
  refine ⟨hΦv.trans (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le), ?_⟩
  have hB : 0 ≤ 2 * Real.log (Real.log (XLP Λ)) + 8 := by
    have := Real.log_nonneg (one_le_log_XLP hΛ); linarith
  have h8 := mul_le_mul_of_nonneg_right (const_le_KLP hΛ)
    (by positivity : (0 : ℝ) ≤ v * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))))
  set X := XLP Λ
  set c := cLP Λ
  set K₀ := Real.exp 97 * Λ ^ 2
  set B := 2 * Real.log (Real.log X) + 8
  set E := Real.exp (c * Real.sqrt (Real.log X))
  set Gv := Real.exp (-(c * Real.sqrt (Real.log v)))
  set GX := Real.exp (-(c * Real.sqrt (Real.log X)))
  have hint : ∀ a b, 1 ≤ a → a ≤ b → b ≤ v →
      IntervalIntegrable (fun u => piRecip P u - pi0Recip u) volume a b := fun a b ha hab hb =>
    (intervalIntegrable_piRecip P a b).sub ((intervalIntegrable_pi0Recip hv1).mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hv1]; exact Icc_subset_Icc ha hb))
  rw [piCount_sub_pi0_eq P hv1, ← intervalIntegral.integral_add_adjacent_intervals
    (hint 1 X le_rfl hX1 hXv) (hint X v hX1 hXv le_rfl)]
  have hI1 : |∫ u in (1 : ℝ)..X, (piRecip P u - pi0Recip u)| ≤ B * X := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := X) (C := B)
      (f := fun u => piRecip P u - pi0Recip u) fun u hu => by
        rw [uIoc_of_le hX1] at hu; exact hlow u hu.1.le hu.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ X - 1)] at this
    nlinarith
  have hI2 : |∫ u in X..v, (piRecip P u - pi0Recip u)| ≤
      K₀ * ∫ u in X..v, Real.exp (-(c * Real.sqrt (Real.log u))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hXv
      (ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hi t ht.1.le (ht.2.trans hvy))
      (((continuousOn_const (c := K₀)).mul
        (continuousOn_exp_neg_sqrt_log c (by linarith))).intervalIntegrable_of_Icc hXv)
  have h3 := integral_exp_neg_sqrt_log_le hc hX hXv
  have h4 : 0 ≤ ∫ u in X..v, Real.exp (-(c * Real.sqrt (Real.log u))) :=
    intervalIntegral.integral_nonneg hXv fun u _ => (Real.exp_pos _).le
  have hGX : 0 < GX := Real.exp_pos _
  have hFX : X * GX ≤ v * Gv := by linarith
  have hXE : X = X * GX * E := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hK0 : 0 ≤ K₀ := by positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have h5 : |v * (piRecip P v - pi0Recip v)| ≤ K₀ * (v * Gv) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ v)]
    nlinarith
  have h6 : B * X ≤ E * B * (v * Gv) := by
    rw [hXE]; nlinarith [mul_le_mul_of_nonneg_left hFX (mul_nonneg hE hB)]
  have h7 : K₀ * ∫ u in X..v, Real.exp (-(c * Real.sqrt (Real.log u))) ≤
      1 / 0.99 * K₀ * (v * Gv) := by
    have : 0.99 * (K₀ * ∫ u in X..v, Real.exp (-(c * Real.sqrt (Real.log u)))) ≤
        K₀ * (v * Gv) := by
      nlinarith [mul_le_mul_of_nonneg_left h3 hK0, mul_pos (by linarith : (0 : ℝ) < X) hGX]
    norm_num at this ⊢
    linarith
  calc _ ≤ |v * (piRecip P v - pi0Recip v)| + |∫ u in (1 : ℝ)..X, (piRecip P u - pi0Recip u)|
        + |∫ u in X..v, (piRecip P u - pi0Recip u)| := by
        refine (abs_sub _ _).trans ?_
        rw [add_assoc]
        exact add_le_add le_rfl (abs_add_le _ _)
    _ ≤ KLP Λ * v * Gv := by
        rw [mul_assoc]
        norm_num at h7 h8
        linarith

/-- `lp_ii_of_i8` with the stronger input `|Φ| ≤ 2 log log X + 5.5` on `[1, X]`. -/
theorem lp_ii_of_i (P : BeurlingSystem) {Λ y : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hi : ∀ v, XLP Λ ≤ v → v ≤ y → |piRecip P v - pi0Recip v| ≤
      Real.exp 97 * Λ ^ 2 * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))))
    (hlow : ∀ u, 1 ≤ u → u ≤ XLP Λ → |piRecip P u - pi0Recip u| ≤
      2 * Real.log (Real.log (XLP Λ)) + 5.5) :
    ∀ v, XLP Λ ≤ v → v ≤ y →
      |piRecip P v - pi0Recip v| ≤ KLP Λ * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) ∧
      |piCount P v - pi0 v| ≤ KLP Λ * v * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) :=
  lp_ii_of_i8 P hΛ hi fun u hu huX => (hlow u hu huX).trans (by norm_num)

/-! ## The input on `[1, X]` -/

theorem pi0Recip_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ pi0Recip u :=
  intervalIntegral.integral_nonneg hu fun _ ht => pi0Dens_div_nonneg ht.1

/-- `∫_{[1,u]} dΠ₀/t ≤ log log X + 1` for `1 ≤ u ≤ X`, `X ≥ e`: `π₀(t)/t ≤ 1/t` on `[1, e]` and
`π₀(t)/t ≤ 1/(t log t)` on `[e, X]`. -/
theorem pi0Recip_le_log_log {X u : ℝ} (hX : Real.exp 1 ≤ X) (hu : 1 ≤ u) (huX : u ≤ X) :
    pi0Recip u ≤ Real.log (Real.log X) + 1 := by
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX1 : 1 ≤ X := he1.trans hX
  have hI : ∀ a b, 1 ≤ a → a ≤ b → b ≤ X →
      IntervalIntegrable (fun t => pi0Dens t / t) volume a b := fun a b ha hab hb =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((integrableOn_pi0Dens_div b).mono_set (Icc_subset_Icc ha le_rfl))
  have h1 : pi0Recip u ≤ pi0Recip X :=
    intervalIntegral.integral_mono_interval le_rfl hu huX
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht =>
        pi0Dens_div_nonneg ht.1.le)) (hI 1 X le_rfl hX1 le_rfl)
  have h2 : ∫ t in (1 : ℝ)..Real.exp 1, pi0Dens t / t ≤ 1 := by
    calc _ ≤ ∫ t in (1 : ℝ)..Real.exp 1, 1 / t :=
          intervalIntegral.integral_mono_on he1 (hI 1 _ le_rfl he1 hX)
            ((continuousOn_const.div continuousOn_id fun t (ht : t ∈ Icc 1 (Real.exp 1)) =>
              (one_pos.trans_le ht.1).ne').intervalIntegrable_of_Icc he1)
            fun t ht => pi0Dens_div_le ht.1
      _ = 1 := by rw [integral_one_div_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp]
  have h3 : ∫ t in Real.exp 1..X, pi0Dens t / t ≤ Real.log (Real.log X) := by
    have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpos : ∀ t ∈ Icc (Real.exp 1) X, 1 < t := fun t ht => he.trans_le ht.1
    have hc : ContinuousOn (fun t => t⁻¹ / Real.log t) (Icc (Real.exp 1) X) :=
      (continuousOn_inv₀.mono fun t ht => (one_pos.trans (hpos t ht)).ne').div
        (Real.continuousOn_log.mono fun t ht => (one_pos.trans (hpos t ht)).ne')
        fun t ht => (Real.log_pos (hpos t ht)).ne'
    calc _ ≤ ∫ t in Real.exp 1..X, t⁻¹ / Real.log t :=
          intervalIntegral.integral_mono_on hX (hI _ X he1 hX le_rfl)
            (hc.intervalIntegrable_of_Icc hX) fun t ht => by
              have := hpos t ht
              exact (div_le_div_of_nonneg_right (pi0Dens_le_inv_log this) (by linarith)).trans_eq
                (by rw [div_right_comm, one_div])
      _ = Real.log (Real.log X) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (Real.log t))
            (fun t ht => by
              rw [uIcc_of_le hX] at ht
              have := hpos t ht
              exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos this).ne')
            (hc.intervalIntegrable_of_Icc hX)]
          simp
  have := intervalIntegral.integral_add_adjacent_intervals (hI 1 _ le_rfl he1 hX)
    (hI _ X he1 hX le_rfl)
  unfold pi0Recip at h1 ⊢
  linarith

/-- The input `|Φ| ≤ 2 log log X + 5.5` on `[1, X]` from `0 ≤ ∫_{[1,u]} dΠ/t ≤ log log X + 4.5`
and `0 ≤ ∫_{[1,u]} dΠ₀/t ≤ log log X + 1`. -/
theorem abs_piRecip_sub_pi0Recip_le_of (P : BeurlingSystem) {X : ℝ} (hX : Real.exp 1 ≤ X)
    (hP : ∀ u, 1 ≤ u → u ≤ X → piRecip P u ≤ Real.log (Real.log X) + 4.5) :
    ∀ u, 1 ≤ u → u ≤ X → |piRecip P u - pi0Recip u| ≤ 2 * Real.log (Real.log X) + 5.5 := by
  intro u hu huX
  have hL : 0 ≤ Real.log (Real.log X) :=
    Real.log_nonneg ((Real.le_log_iff_exp_le (by linarith [Real.add_one_le_exp (1 : ℝ)])).mpr hX)
  have h1 := hP u hu huX
  have h2 := pi0Recip_le_log_log hX hu huX
  have h3 := pi0Recip_nonneg hu
  have h4 := piRecip_nonneg P u
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- `lp_ii_of_i` with the input on `[1, X]` in the form `∫_{[1,u]} dΠ/t ≤ log log X + 4.5`. -/
theorem lp_ii_of_i' (P : BeurlingSystem) {Λ y : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hi : ∀ v, XLP Λ ≤ v → v ≤ y → |piRecip P v - pi0Recip v| ≤
      Real.exp 97 * Λ ^ 2 * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))))
    (hP : ∀ u, 1 ≤ u → u ≤ XLP Λ → piRecip P u ≤ Real.log (Real.log (XLP Λ)) + 4.5) :
    ∀ v, XLP Λ ≤ v → v ≤ y →
      |piRecip P v - pi0Recip v| ≤ KLP Λ * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) ∧
      |piCount P v - pi0 v| ≤ KLP Λ * v * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) :=
  lp_ii_of_i P hΛ hi (abs_piRecip_sub_pi0Recip_le_of P (exp_one_le_XLP hΛ) hP)

/-- The input `|Φ| ≤ 2 log log X + 8` on `[1, X]` from `0 ≤ ∫_{[1,u]} dΠ/t ≤ log log X + 7`
and `0 ≤ ∫_{[1,u]} dΠ₀/t ≤ log log X + 1`. -/
theorem abs_piRecip_sub_pi0Recip_le_of8 (P : BeurlingSystem) {X : ℝ} (hX : Real.exp 1 ≤ X)
    (hP : ∀ u, 1 ≤ u → u ≤ X → piRecip P u ≤ Real.log (Real.log X) + 7) :
    ∀ u, 1 ≤ u → u ≤ X → |piRecip P u - pi0Recip u| ≤ 2 * Real.log (Real.log X) + 8 := by
  intro u hu huX
  have hL : 0 ≤ Real.log (Real.log X) :=
    Real.log_nonneg ((Real.le_log_iff_exp_le (by linarith [Real.add_one_le_exp (1 : ℝ)])).mpr hX)
  have h1 := hP u hu huX
  have h2 := pi0Recip_le_log_log hX hu huX
  have h3 := pi0Recip_nonneg hu
  have h4 := piRecip_nonneg P u
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- `lp_ii_of_i8` with the input on `[1, X]` in the form `∫_{[1,u]} dΠ/t ≤ log log X + 7`. -/
theorem lp_ii_of_i8' (P : BeurlingSystem) {Λ y : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hi : ∀ v, XLP Λ ≤ v → v ≤ y → |piRecip P v - pi0Recip v| ≤
      Real.exp 97 * Λ ^ 2 * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))))
    (hP : ∀ u, 1 ≤ u → u ≤ XLP Λ → piRecip P u ≤ Real.log (Real.log (XLP Λ)) + 7) :
    ∀ v, XLP Λ ≤ v → v ≤ y →
      |piRecip P v - pi0Recip v| ≤ KLP Λ * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) ∧
      |piCount P v - pi0 v| ≤ KLP Λ * v * Real.exp (-(cLP Λ * Real.sqrt (Real.log v))) :=
  lp_ii_of_i8 P hΛ hi (abs_piRecip_sub_pi0Recip_le_of8 P (exp_one_le_XLP hΛ) hP)

end LocalPNT

end
