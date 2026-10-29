module

public import RequestProject.Beurling.LocalPNT.Step2Recip
public import RequestProject.Beurling.LocalPNT.TailT
public import RequestProject.Beurling.LocalPNT.Inversion
public import RequestProject.Beurling.Model.Slope

/-!
# Step 9 of the proof of Theorem 5.24: the smoothing error

For a smoothed step `H` (`0 ≤ H ≤ 1`, `H(z) = 1` for `z ≥ 2/T`, `H(z) = 0` for `z < 1/T`), put

  `R(v) = ∑_{p^k ≤ v} H(log(v/p^k))/(k p^k) - ∫_1^∞ H(log(v/u)) π₀(u)/u du`.

Then `|Φ(v) - R(v)| ≤ 10/T + 14 v^{θ' - 1}` with `Φ(v) = ∫_{[1,v]} d(Π - Π₀)/u`
(`smoothing_error`): the difference lives on `(v e^{-2/T}, v]`, where `dΠ ≤ dN` and
`N(v) - N(v') ≤ 2(v - v') + 7 v^{θ'}` by (LP-a) (the rigid count grows by at most `v - v' + 1`).
-/

@[expose] public section

open Set Real MeasureTheory Construction Oscillation

namespace LocalPNT

/-- `#{p^k ∈ (v', v]} ≤ N(v) - N(v')`. -/
lemma card_pps_between_le (P : BeurlingSystem) {v' v : ℝ} (hv : v' ≤ v) :
    (((P.pps v).filter (fun jk => v' < P.p jk.1 ^ (jk.2 + 1))).card : ℝ) ≤ P.N v - P.N v' := by
  classical
  rw [BeurlingSystem.N_eq_card, BeurlingSystem.N_eq_card]
  have hsub : P.elems v' ⊆ P.elems v := P.elems_mono hv
  rw [← Nat.cast_sub (Finset.card_le_card hsub), ← Finset.card_sdiff_of_subset hsub]
  norm_cast
  refine Finset.card_le_card_of_injOn (fun jk => Finsupp.single jk.1 (jk.2 + 1)) ?_ ?_
  · intro jk hjk
    rw [Finset.coe_filter, Set.mem_setOf_eq, BeurlingSystem.mem_pps] at hjk
    rw [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, Finset.mem_coe,
      BeurlingSystem.mem_elems, BeurlingSystem.mem_elems, P.val_single]
    exact ⟨hjk.1, not_le.mpr hjk.2⟩
  · intro a _ b _ hab
    simp only at hab
    rcases Finsupp.single_eq_single_iff _ _ _ _ |>.mp hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1 (by omega)
    · omega

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `N(v) - N(v') ≤ 2(v - v') + 1000 v^{θ'}` for `X₀ ≤ v' ≤ v ≤ y`. -/
theorem N_sub_le {v' v : ℝ} (hv' : (X₀ : ℝ) ≤ v') (hv : v' ≤ v) (hvy : v ≤ y) :
    P.N v - P.N v' ≤ 2 * (v - v') + 1000 * v ^ thetaPrime θ X₀ := by
  have hX := h.logX
  have hv'0 : 0 < v' := lt_of_lt_of_le h.X0_pos hv'
  have hv1 : 1 ≤ v' := le_trans h.one_le_X0 hv'
  have hXm : Xm ≤ v' := le_trans h.Xm_le hv'
  have hl1 := h.lag_le (u := v) (by linarith) hvy
  have hl2 := h.lag_le (u := v') hXm (by linarith)
  rw [h.T0_high (by linarith)] at hl1
  rw [h.T0_high hv'] at hl2
  -- the rigid error grows by at most the number of integers
  have hrig : Target.rigidErr X₀ (kap X₀) v - Target.rigidErr X₀ (kap X₀) v' ≤ v - v' + 1 := by
    unfold Target.rigidErr
    have h1 := smoothCount_sub_le X₀ (by linarith) hv
    have hκ := kappa_pos_aux hX
    have h2 : 0 ≤ ∫ u in v'..v, Target.rhoDet X₀ (kap X₀) u :=
      intervalIntegral.integral_nonneg hv fun u hu => by
        unfold Target.rhoDet
        have : 0 < u := lt_of_lt_of_le hv'0 hu.1
        positivity
    have hsplit : (∫ u in (X₀ : ℝ)..v, Target.rhoDet X₀ (kap X₀) u) =
        (∫ u in (X₀ : ℝ)..v', Target.rhoDet X₀ (kap X₀) u) +
          ∫ u in v'..v, Target.rhoDet X₀ (kap X₀) u := by
      have hX1n : 1 ≤ X₀ := by exact_mod_cast h.one_le_X0
      have hii : ∀ a b : ℝ, (X₀ : ℝ) ≤ a → a ≤ b →
          IntervalIntegrable (Target.rhoDet X₀ (kap X₀)) MeasureTheory.volume a b := by
        intro a b ha hab
        exact (BModel.intervalIntegrable_rhoDet X₀ hκ hX1n ha).symm.trans
          (BModel.intervalIntegrable_rhoDet X₀ hκ hX1n (ha.trans hab))
      exact (intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl hv')
        (hii _ _ hv' hv)).symm
    rw [hsplit]
    linarith
  have hR1 := abs_osc_le h.spacing h.alpha_le (le_trans hv1 hv) (θ := θ) (γ := γ)
  have hR2 := abs_osc_le h.spacing h.alpha_le hv1 (θ := θ) (γ := γ)
  have htp := (thetaPrime_bounds h.theta_mem hX).1
  have hθ := h.theta_mem
  have hvv : 1 ≤ v := by linarith
  have hpow : ∀ x : ℝ, 1 ≤ x → x ^ θ * (logStar x : ℝ) ≤ 201 * x ^ thetaPrime θ X₀ := by
    intro x hx
    have hls := logStar_le_rpow hx (show (0 : ℝ) < 0.005 by norm_num)
    calc x ^ θ * (logStar x : ℝ) ≤ x ^ θ * ((1 / 0.005 + 1) * x ^ (0.005 : ℝ)) := by gcongr
      _ = 201 * x ^ (θ + 0.005) := by rw [Real.rpow_add (by linarith)]; ring
      _ ≤ 201 * x ^ thetaPrime θ X₀ := by
          have := Real.rpow_le_rpow_of_exponent_le hx (show θ + 0.005 ≤ thetaPrime θ X₀ by
            linarith)
          linarith
  have hv'p : v' ^ thetaPrime θ X₀ ≤ v ^ thetaPrime θ X₀ :=
    Real.rpow_le_rpow hv'0.le hv (by linarith [hθ.1])
  have hp1 := hpow v hvv
  have hp2 := hpow v' hv1
  have a1 := abs_le.mp hl1
  have a2 := abs_le.mp hl2
  have a3 := abs_le.mp hR1
  have a4 := abs_le.mp hR2
  have hpos : 0 ≤ v ^ thetaPrime θ X₀ := by positivity
  have hone : 1 ≤ v ^ thetaPrime θ X₀ := Real.one_le_rpow hvv (by linarith [hθ.1])
  nlinarith

/-- **The smoothing error** (Step 9). -/
theorem smoothing_error {v T : ℝ} (hv : 2 * (X₀ : ℝ) ≤ v) (hvy : v ≤ y) (hT : 4 ≤ T)
    {H : ℝ → ℝ} (hHc : Continuous H) (hH01 : ∀ z, 0 ≤ H z ∧ H z ≤ 1)
    (hH1 : ∀ z, 2 / T ≤ z → H z = 1) (hH0 : ∀ z, z < 1 / T → H z = 0) :
    IntegrableOn (fun u => H (Real.log (v / u)) * (pi0Dens u / u)) (Ioi 1) ∧
    |(piRecip P v - pi0Recip v) - ((∑ jk ∈ P.pps v,
        H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) -
      ∫ u in Ioi 1, H (Real.log (v / u)) * (pi0Dens u / u))| ≤
      10 / T + 2000 * v ^ (thetaPrime θ X₀ - 1) := by
  classical
  have hX0 := h.X0_pos
  have hv0 : 0 < v := by linarith
  have hT0 : 0 < T := by linarith
  set v' := v * Real.exp (-(2 / T)) with hv'def
  have he : 0.6 ≤ Real.exp (-(2 / T)) := by
    have h1 : -(1 / 2 : ℝ) ≤ -(2 / T) := by
      rw [neg_le_neg_iff, div_le_iff₀ hT0]; linarith
    have h2 : 0.6 ≤ Real.exp (-(1 / 2)) := by
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have hb : Real.exp (1 / 2) ≤ 1.65 := by
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
      have hm : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (-(1 / 2) : ℝ)]
    exact h2.trans (Real.exp_le_exp.mpr h1)
  have he1 : Real.exp (-(2 / T)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 < 2 / T := by positivity
    linarith)
  have hv'v : v' ≤ v := by simp only [v']; nlinarith
  have hv'0 : 0 < v' := by simp only [v']; positivity
  have hv'X : (X₀ : ℝ) ≤ v' := by simp only [v']; nlinarith
  have hvv' : v - v' ≤ 2 * v / T := by
    simp only [v']
    have := Real.add_one_le_exp (-(2 / T))
    have : v * (1 - Real.exp (-(2 / T))) ≤ v * (2 / T) :=
      mul_le_mul_of_nonneg_left (by linarith) hv0.le
    have e : 2 * v / T = v * (2 / T) := by ring
    linarith
  have hlogvv' : Real.log (v / v') = 2 / T := by
    simp only [v']
    rw [div_mul_eq_div_div, div_self hv0.ne', one_div, Real.log_inv, Real.log_exp, neg_neg]
  -- the discrete part
  set w : ℕ × ℕ → ℝ := fun jk => 1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))
  have hD : (∑ jk ∈ P.pps v, w jk) -
      ∑ jk ∈ P.pps v, H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) /
        (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1)) ∈
      Set.Icc 0 ((2 * (v - v') + 1000 * v ^ thetaPrime θ X₀) / v') := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ jk ∈ P.pps v, w jk - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) /
        (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1)) =
        (1 - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))) * w jk := by
      intro jk _; simp only [w]; ring
    rw [Finset.sum_congr rfl hterm]
    have hw0 : ∀ jk, 0 ≤ w jk := fun jk => by simp only [w]; have := P.pp_pos jk; positivity
    constructor
    · exact Finset.sum_nonneg fun jk _ => mul_nonneg
        (by linarith [(hH01 (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))).2]) (hw0 jk)
    · rw [← Finset.sum_filter_add_sum_filter_not (P.pps v)
        (fun jk => v' < P.p jk.1 ^ (jk.2 + 1))]
      have hzero : ∑ jk ∈ (P.pps v).filter (fun jk => ¬ v' < P.p jk.1 ^ (jk.2 + 1)),
          (1 - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))) * w jk = 0 := by
        refine Finset.sum_eq_zero fun jk hjk => ?_
        rw [Finset.mem_filter, not_lt] at hjk
        have hp := P.pp_pos jk
        rw [hH1, sub_self, zero_mul]
        rw [← hlogvv']
        exact Real.log_le_log (div_pos hv0 hv'0) (div_le_div_of_nonneg_left hv0.le hp hjk.2)
      rw [hzero, add_zero]
      have hcard := card_pps_between_le P hv'v
      have hN := h.N_sub_le hv'X hv'v hvy
      calc _ ≤ ∑ jk ∈ (P.pps v).filter (fun jk => v' < P.p jk.1 ^ (jk.2 + 1)), 1 / v' := by
            refine Finset.sum_le_sum fun jk hjk => ?_
            rw [Finset.mem_filter] at hjk
            have hp := P.pp_pos jk
            have h1 : 1 - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) ≤ 1 := by
              linarith [(hH01 (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))).1]
            have h2 : w jk ≤ 1 / v' := by
              simp only [w]
              apply one_div_le_one_div_of_le hv'0
              have : (1 : ℝ) ≤ (jk.2 : ℝ) + 1 := by have := (jk.2).cast_nonneg (α := ℝ); linarith
              nlinarith
            have h0 : 0 ≤ 1 - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) := by
              linarith [(hH01 (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))).2]
            calc (1 - H (Real.log (v / P.p jk.1 ^ (jk.2 + 1)))) * w jk ≤ 1 * (1 / v') :=
                  mul_le_mul h1 h2 (hw0 jk) zero_le_one
              _ = 1 / v' := one_mul _
        _ = ((P.pps v).filter (fun jk => v' < P.p jk.1 ^ (jk.2 + 1))).card / v' := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ (2 * (v - v') + 1000 * v ^ thetaPrime θ X₀) / v' := by
            apply div_le_div_of_nonneg_right _ hv'0.le; linarith
  -- the continuous part
  set g : ℝ → ℝ := fun u => pi0Dens u / u
  have hg : ∀ u, 1 < u → 0 ≤ g u ∧ g u ≤ 1 / u := by
    intro u hu
    have h0 := pi0Dens_nonneg hu
    have h1 := pi0Dens_le_one hu
    exact ⟨div_nonneg h0 (by linarith), div_le_div_of_nonneg_right h1 (by linarith)⟩
  have hgm : Measurable g := by
    simp only [g, pi0Dens]
    exact ((measurable_const.sub (measurable_const.div measurable_id)).div
      Real.measurable_log).div measurable_id
  have hHm : Measurable (fun u : ℝ => H (Real.log (v / u)) * g u) :=
    (hHc.measurable.comp (Real.measurable_log.comp (measurable_const.div measurable_id))).mul hgm
  have hbdd : ∀ u ∈ Ioc (1 : ℝ) v, ‖H (Real.log (v / u)) * g u‖ ≤ 1 := by
    intro u hu
    obtain ⟨g0, g1⟩ := hg u hu.1
    have h1u : 1 / u ≤ 1 := by rw [div_le_one (by linarith [hu.1])]; exact hu.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hH01 _).1 g0)]
    calc H (Real.log (v / u)) * g u ≤ 1 * 1 :=
          mul_le_mul (hH01 _).2 (g1.trans h1u) g0 zero_le_one
      _ = 1 := by ring
  have hintIoc : IntegrableOn (fun u => H (Real.log (v / u)) * g u) (Ioc 1 v) :=
    Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne hHm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono hbdd)
  have hzero : ∀ u, v < u → H (Real.log (v / u)) * g u = 0 := by
    intro u hu
    rw [hH0, zero_mul]
    have : Real.log (v / u) < 0 := Real.log_neg (div_pos hv0 (by linarith))
      ((div_lt_one (by linarith)).mpr hu)
    have : 0 < 1 / T := by positivity
    linarith
  have hint : IntegrableOn (fun u => H (Real.log (v / u)) * g u) (Ioi 1) := by
    refine hintIoc.of_forall_diff_eq_zero measurableSet_Ioi fun u hu => ?_
    have : v < u := by
      by_contra hc; push_neg at hc; exact hu.2 ⟨hu.1, hc⟩
    exact hzero u this
  refine ⟨hint, ?_⟩
  have hIoi : ∫ u in Ioi 1, H (Real.log (v / u)) * g u =
      ∫ u in Ioc 1 v, H (Real.log (v / u)) * g u := by
    have hv1 : (1 : ℝ) ≤ v := by linarith [h.one_le_X0]
    rw [← Ioc_union_Ioi_eq_Ioi hv1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hintIoc (hint.mono_set (Ioi_subset_Ioi hv1))]
    have : ∫ u in Ioi v, H (Real.log (v / u)) * g u = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hzero u hu)]; simp
    rw [this, add_zero]
  have hgint : IntegrableOn g (Ioc 1 v) :=
    Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne hgm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun u hu => by
        obtain ⟨g0, g1⟩ := hg u hu.1
        rw [Real.norm_eq_abs, abs_of_nonneg g0]
        exact g1.trans (by rw [div_le_one (by linarith [hu.1])]; exact hu.1.le))
  have hpi0 : pi0Recip v = ∫ u in Ioc 1 v, g u := by
    unfold pi0Recip
    rw [intervalIntegral.integral_of_le (by linarith [h.one_le_X0])]
  have hC : pi0Recip v - ∫ u in Ioi 1, H (Real.log (v / u)) * g u ∈ Set.Icc 0 (2 / T) := by
    rw [hpi0, hIoi, ← integral_sub hgint hintIoc]
    have hpt : ∀ u ∈ Ioc (1 : ℝ) v, 0 ≤ g u - H (Real.log (v / u)) * g u ∧
        g u - H (Real.log (v / u)) * g u ≤ (Ioc v' v).indicator (fun u => 1 / u) u := by
      intro u hu
      obtain ⟨g0, g1⟩ := hg u hu.1
      have e : g u - H (Real.log (v / u)) * g u = (1 - H (Real.log (v / u))) * g u := by ring
      rw [e]
      refine ⟨mul_nonneg (by linarith [(hH01 (Real.log (v / u))).2]) g0, ?_⟩
      by_cases hu' : u ∈ Ioc v' v
      · rw [Set.indicator_of_mem hu']
        calc (1 - H (Real.log (v / u))) * g u ≤ 1 * (1 / u) :=
              mul_le_mul (by linarith [(hH01 (Real.log (v / u))).1]) g1 g0 zero_le_one
          _ = 1 / u := one_mul _
      · rw [Set.indicator_of_notMem hu']
        have huv' : u ≤ v' := by
          by_contra hc; push_neg at hc; exact hu' ⟨hc, hu.2⟩
        have hu0 : 0 < u := by linarith [hu.1]
        rw [hH1, sub_self, zero_mul]
        rw [← hlogvv']
        exact Real.log_le_log (div_pos hv0 hv'0) (div_le_div_of_nonneg_left hv0.le hu0 huv')
    constructor
    · exact setIntegral_nonneg measurableSet_Ioc fun u hu => (hpt u hu).1
    · have h2X : (2 : ℝ) ≤ X₀ := by
        have := Real.add_one_le_exp (Real.log X₀)
        rw [Real.exp_log h.X0_pos] at this; linarith [h.logX]
      have h1v' : 1 < v' := by linarith
      have hcont : IntegrableOn (fun u : ℝ => 1 / u) (Ioc v' v) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
        intro u hu
        exact (continuousAt_const.div continuousAt_id
          (ne_of_gt (lt_of_lt_of_le hv'0 hu.1))).continuousWithinAt
      have hind : IntegrableOn ((Ioc v' v).indicator (fun u : ℝ => 1 / u)) (Ioc 1 v) :=
        ((integrable_indicator_iff measurableSet_Ioc).mpr hcont).integrableOn
      have hle := setIntegral_mono_on (f := fun u => g u - H (Real.log (v / u)) * g u)
        (hgint.sub hintIoc) hind measurableSet_Ioc (fun u hu => (hpt u hu).2)
      have hval : ∫ u in Ioc 1 v, (Ioc v' v).indicator (fun u : ℝ => 1 / u) u = 2 / T := by
        rw [setIntegral_indicator measurableSet_Ioc]
        have : Ioc (1 : ℝ) v ∩ Ioc v' v = Ioc v' v := by
          ext u; simp only [mem_inter_iff, mem_Ioc]
          constructor
          · exact fun h => h.2
          · intro hu; exact ⟨⟨by linarith [hu.1], hu.2⟩, hu⟩
        rw [this, ← intervalIntegral.integral_of_le hv'v]
        simp only [one_div]
        rw [integral_inv (by
          rw [Set.uIcc_of_le hv'v]; intro h0; linarith [h0.1]), hlogvv']
      linarith
  -- combine
  obtain ⟨hD0, hD1⟩ := hD
  obtain ⟨hC0, hC1⟩ := hC
  have hbound : (2 * (v - v') + 1000 * v ^ thetaPrime θ X₀) / v' ≤
      8 / T + 2000 * v ^ (thetaPrime θ X₀ - 1) := by
    have hv'b : 0.6 * v ≤ v' := by simp only [v']; nlinarith
    rw [div_le_iff₀ hv'0]
    have hrp : v ^ (thetaPrime θ X₀ - 1) * v = v ^ thetaPrime θ X₀ := by
      rw [Real.rpow_sub_one hv0.ne']; field_simp
    have hp0 : 0 ≤ v ^ (thetaPrime θ X₀ - 1) := by positivity
    have h8 : 0 ≤ 8 / T := by positivity
    have : 8 / T * v' + 2000 * v ^ (thetaPrime θ X₀ - 1) * v' ≥
        8 / T * (0.6 * v) + 2000 * v ^ (thetaPrime θ X₀ - 1) * (0.6 * v) := by
      apply add_le_add <;> apply mul_le_mul_of_nonneg_left hv'b <;> positivity
    have e1 : 8 / T * (0.6 * v) = 2.4 * (2 * v / T) := by ring
    nlinarith
  have e : (piRecip P v - pi0Recip v) - ((∑ jk ∈ P.pps v,
        H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) -
      ∫ u in Ioi 1, H (Real.log (v / u)) * (pi0Dens u / u)) =
      ((∑ jk ∈ P.pps v, w jk) - ∑ jk ∈ P.pps v, H (Real.log (v / P.p jk.1 ^ (jk.2 + 1))) /
        (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))) -
      (pi0Recip v - ∫ u in Ioi 1, H (Real.log (v / u)) * g u) := by
    simp only [w, g, piRecip]; ring
  have hp0 : 0 ≤ v ^ (thetaPrime θ X₀ - 1) := by positivity
  have h8 : 0 ≤ 8 / T := by positivity
  have e10 : 10 / T = 8 / T + 2 / T := by ring
  rw [e, abs_le]
  constructor <;> linarith

end LPHyp

end LocalPNT

end
