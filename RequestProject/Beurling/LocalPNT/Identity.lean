module

public import RequestProject.Beurling.LocalPNT.Hpart
public import RequestProject.Beurling.LocalPNT.Perron

/-!
# Steps 9–10 of the proof of Theorem 5.24: the Mellin inversion identity for `Gright`

For `f` continuous, vanishing on `(x₀, ∞)` with `x₀ < log y`, and `F(s) = ∫ f(x) e^{sx} dx`
(holomorphic on `σ > c₀ ≥ c₁` and `O(e^{σ x₀}(1 + σ)/(1 + t²))` on `σ ≥ c`),
`(1/2π) ∫ F(c + it) Gright(c + it) dt = ∑_{p_j^k ≤ y} f(log p_j^k)/k - ∫_1^∞ f(log u) π₀(u) du`
(`identity_Gright`). With `Gright = Ly + Hp + log((s-1)/s)`:

* `Ly` gives the prime powers `≤ y` by Laplace inversion (`integral_mul_cpow_eq`);
* `Hp` gives `0`, by shifting the line of integration to `+∞` (`e^{x₀} < y`);
* `log((s-1)/s) = -∫_1^∞ u^{-s} π₀(u) du` gives `-∫ f(log u) π₀(u) du` by Fubini.
-/

@[expose] public section

open Set Real Complex Filter Topology MeasureTheory

namespace LocalPNT

/-- **Laplace inversion in Mellin form**: if `F(c + it) = ∫ f(x) e^{(c+it)x} dx` is integrable on
the line and `f(x) e^{cx}` is integrable, then `∫ F(c + it) u^{-(c+it)} dt = 2π f(log u)`. -/
theorem integral_mul_cpow_eq {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, F (c + t * I) = ∫ x : ℝ, (f x : ℂ) * cexp ((c + t * I) * x))
    (hfint : Integrable (fun x : ℝ => f x * Real.exp (c * x)))
    (hFi : Integrable (fun t : ℝ => F (c + t * I))) {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, F (c + t * I) * (u : ℂ) ^ (-((c : ℂ) + t * I)) = 2 * π * f (Real.log u) := by
  have hrefl : ∀ t : ℝ, ∫ ξ : ℝ, (f (-ξ) : ℂ) * cexp (-((c : ℂ) + t * I) * ξ) =
      F (c + t * I) := fun t => by
    rw [hF, ← integral_neg_eq_self (fun y : ℝ => (f y : ℂ) * cexp (((c : ℂ) + t * I) * y))]
    congr 1
    ext ξ
    push_cast
    ring_nf
  have hint : Integrable (fun ξ : ℝ => (f (-ξ) : ℂ) * (Real.exp (-c * ξ) : ℂ)) := by
    refine hfint.comp_neg.ofReal.congr (Eventually.of_forall fun ξ => ?_)
    simp only [neg_mul, mul_neg]
    exact ofReal_mul _ _
  have key := laplace_inversion (f := fun ξ : ℝ => (f (-ξ) : ℂ)) (c := c) (by fun_prop) hint
    (by simpa only [hrefl] using hFi) (-Real.log u)
  simp only [neg_neg, hrefl] at key
  have e : ∫ t : ℝ, F (c + t * I) * (u : ℂ) ^ (-((c : ℂ) + t * I)) =
      ∫ t : ℝ, F (c + t * I) * cexp (((c : ℂ) + t * I) * ((-Real.log u : ℝ) : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [cpow_def_of_ne_zero (by exact_mod_cast hu.ne'), ← ofReal_log hu.le]
    push_cast
    ring_nf
  rw [e, key, ← mul_assoc, mul_one_div_cancel
    (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)), one_mul]

lemma exists_le_of_tendsto_zero {B : ℝ → ℝ} (hB : Continuous B) (h0 : Tendsto B atTop (𝓝 0))
    (c : ℝ) : ∃ C, ∀ σ ≥ c, B σ ≤ C := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := R)).bddAbove_image hB.continuousOn
  refine ⟨max C 1, fun σ hσ => ?_⟩
  rcases le_total σ R with hσR | hσR
  · exact (hC ⟨σ, ⟨hσ, hσR⟩, rfl⟩).trans (le_max_left _ _)
  · exact (hR σ hσR).le.trans (le_max_right _ _)

lemma re_div_sub_one_pos {s : ℂ} (hs : 1 < s.re) : 0 < (s / (s - 1)).re := by
  have hN : 0 < normSq (s - 1) := normSq_pos.mpr fun h0 => by
    have := congrArg re h0
    simp at this
    linarith
  rw [div_re]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  exact add_pos_of_pos_of_nonneg (div_pos (by nlinarith) hN)
    (div_nonneg (mul_self_nonneg _) hN.le)

/-- `log((s-1)/s) = -∫_1^∞ u^{-s} π₀(u) du` for `Re s > 1`. -/
lemma log_sub_one_div_eq {s : ℂ} (hs : 1 < s.re) :
    Complex.log ((s - 1) / s) = -∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s) * (pi0Dens u : ℂ) := by
  have harg : arg (s / (s - 1)) ≠ π := fun ha =>
    (re_div_sub_one_pos hs).not_gt (arg_eq_pi_iff.mp ha).1
  rw [integral_cpow_pi0Dens hs, ← inv_div, Complex.log_inv _ harg]

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- Reindexing `∑_{p_j ≤ y} ∑_{1 ≤ n < M, p_j^n ≤ y}` as a sum over `pps y`. -/
lemma sum_Mcut_eq_sum_pps (g : ℝ → ℝ) :
    ∑ j ∈ P.primesLe y, ∑ n ∈ Finset.range (Mcut y),
      (if 1 ≤ n ∧ P.p j ^ n ≤ y then g (Real.log (P.p j ^ n)) / n else 0) =
      ∑ jk ∈ P.pps y, g (Real.log (P.p jk.1 ^ (jk.2 + 1))) / ((jk.2 : ℝ) + 1) := by
  classical
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  rw [← Finset.sum_product' (f := fun (j n : ℕ) =>
      if 1 ≤ n ∧ P.p j ^ n ≤ y then g (Real.log (P.p j ^ n)) / n else 0),
    ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun jn => (jn.1, jn.2 - 1)) (fun jk => (jk.1, jk.2 + 1))
    ?_ ?_ ?_ ?_ ?_
  · intro jn hjn
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjn
    simp only [P.mem_pps]
    rw [Nat.sub_add_cancel hjn.2.1]
    exact hjn.2.2
  · intro jk hjk
    simp only [P.mem_pps] at hjk
    have hp1 := P.one_lt jk.1
    have hpj : P.p jk.1 ≤ y := (le_self_pow₀ hp1.le (Nat.succ_ne_zero _)).trans hjk
    have hp2 := h.p_ge_two' hpj
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      P.mem_primesLe]
    refine ⟨⟨hpj, ?_⟩, by omega, hjk⟩
    by_contra hc
    push_neg at hc
    have : (2 : ℝ) ^ Mcut y ≤ P.p jk.1 ^ (jk.2 + 1) :=
      (pow_le_pow_right₀ (by norm_num) hc).trans (pow_le_pow_left₀ (by norm_num) hp2 _)
    linarith [two_pow_Mcut_gt hy1]
  · intro jn hjn
    simp only [Finset.mem_filter] at hjn
    ext
    · rfl
    · exact Nat.sub_add_cancel hjn.2.1
  · intro jk _
    simp
  · intro jn hjn
    simp only [Finset.mem_filter] at hjn
    obtain ⟨k, hk⟩ : ∃ k, jn.2 = k + 1 := ⟨jn.2 - 1, by omega⟩
    simp only [hk, Nat.add_sub_cancel]
    push_cast
    rfl

/-- **The inversion identity of Steps 9–10**: for `f` continuous, vanishing beyond `x₀ < log y`,
with transform `F(s) = ∫ f(x) e^{sx} dx`,
`(1/2π) ∫ F(c + it) Gright(c + it) dt = ∑_{p_j^k ≤ y} f(log p_j^k)/k - ∫_1^∞ f(log u) π₀(u) du`. -/
theorem identity_Gright {f : ℝ → ℝ} (hf : Continuous f) {x₀ : ℝ} (hx₀ : x₀ < Real.log y)
    (hfsupp : ∀ x, x₀ < x → f x = 0) {c c₀ : ℝ} (hc₀ : c1 y ≤ c₀) (hc : c₀ < c) (hc2 : c ≤ 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hF : ∀ s : ℂ, c ≤ s.re → F s = ∫ x : ℝ, (f x : ℂ) * cexp (s * x))
    (hfint : ∀ σ : ℝ, c ≤ σ → Integrable (fun x : ℝ => f x * Real.exp (σ * x)))
    {K : ℝ} (hFb : ∀ σ : ℝ, c ≤ σ → ∀ t : ℝ,
      ‖F (σ + t * I)‖ ≤ K * Real.exp (σ * x₀) * (1 + σ) / (1 + t ^ 2)) :
    Integrable (fun t : ℝ => F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)) ∧
    (1 / (2 * Real.pi)) * ∫ t : ℝ, F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I) =
      ((∑ jk ∈ P.pps y, f (Real.log (P.p jk.1 ^ (jk.2 + 1))) / ((jk.2 : ℝ) + 1) -
        ∫ u in Ioi (1 : ℝ), f (Real.log u) * pi0Dens u : ℝ) : ℂ) := by
  classical
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hc1 : 1 < c := by linarith [h.c1_gt]
  have hre : ∀ σ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun σ t => by simp
  have hFc : ∀ σ, c₀ < σ → Continuous fun t : ℝ => F (σ + t * I) := fun σ hσ =>
    hFd.continuousOn.comp_continuous (by fun_prop) fun t => by simpa using hσ
  have hFi : Integrable (fun t : ℝ => F (c + t * I)) :=
    integrable_vertical_of_bound (hFc c hc) (hFb c le_rfl)
  have hinv : ∀ u : ℝ, 0 < u →
      ∫ t : ℝ, F (c + t * I) * (u : ℂ) ^ (-((c : ℂ) + t * I)) = 2 * π * f (Real.log u) :=
    fun u hu => integral_mul_cpow_eq hf (fun t => hF _ (hre c t).ge) (hfint c le_rfl) hFi hu
  have hcpow : ∀ u : ℝ, 0 < u →
      Integrable (fun t : ℝ => F (c + t * I) * (u : ℂ) ^ (-((c : ℂ) + t * I))) := by
    intro u hu
    refine (hFi.norm.mul_const (u ^ (-c))).mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact ((hFc c hc).mul ((by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I)).const_cpow
        (Or.inl (by exact_mod_cast hu.ne')))).aestronglyMeasurable
    · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu]
      simp
  /- The part `Ly`. -/
  have hLy_eq : ∀ t : ℝ, F (c + t * I) * Ly P y (c + t * I) =
      ∑ j ∈ P.primesLe y, ∑ n ∈ Finset.range (Mcut y), if 1 ≤ n ∧ P.p j ^ n ≤ y then
        F (c + t * I) * ((P.p j ^ n : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) / n else 0 := by
    intro t
    unfold Ly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [mul_div_assoc]
  have hterm : ∀ j n : ℕ, Integrable (fun t : ℝ => if 1 ≤ n ∧ P.p j ^ n ≤ y then
      F (c + t * I) * ((P.p j ^ n : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) / n else 0) := by
    intro j n
    split_ifs
    · exact (hcpow _ (pow_pos (P.p_pos j) n)).div_const _
    · exact integrable_zero _ _ _
  have hLyi : Integrable (fun t : ℝ => F (c + t * I) * Ly P y (c + t * I)) := by
    simp only [hLy_eq]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun n _ => hterm j n
  have hLyI : (1 / (2 * π)) * ∫ t : ℝ, F (c + t * I) * Ly P y (c + t * I) =
      ((∑ jk ∈ P.pps y, f (Real.log (P.p jk.1 ^ (jk.2 + 1))) / ((jk.2 : ℝ) + 1) : ℝ) : ℂ) := by
    rw [← h.sum_Mcut_eq_sum_pps f]
    simp only [hLy_eq]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun n _ => hterm j n,
      Finset.mul_sum, ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun n _ => hterm j n, Finset.mul_sum, ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [integral_div, hinv _ (pow_pos (P.p_pos j) n)]
      push_cast
      field_simp
    · simp
  /- The part `Hp` vanishes. -/
  set L := Real.log y with hL
  set δ := L - x₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set q₀ := 2 * ((P.primesLe y).card : ℝ) + 1.5 * (L * (L + Real.exp 11 * L ^ 2)) with hq₀
  set q₁ := 1.5 * L ^ 2 with hq₁
  set B : ℝ → ℝ := fun σ => K * (y * Real.exp (-(δ * σ))) * ((1 + σ) * (q₀ + q₁ * σ)) with hB
  have hBd : ∀ σ ≥ c, ∀ t : ℝ,
      ‖F (σ + t * I) * Hp P θ X₀ α γ xp y (σ + t * I)‖ ≤ B σ / (1 + t ^ 2) := by
    intro σ hσ t
    have hH := h.norm_Hp_le (s := σ + t * I) (by rw [hre]; linarith)
    have hFσ := hFb σ hσ t
    rw [hre] at hH
    have e : Real.exp (σ * x₀) * Real.exp (L * (1 - σ)) = y * Real.exp (-(δ * σ)) := by
      calc _ = Real.exp L * Real.exp (-(δ * σ)) := by
            rw [← Real.exp_add, ← Real.exp_add, hδ]
            ring_nf
        _ = _ := by rw [hL, Real.exp_log hy0]
    rw [norm_mul]
    calc _ ≤ K * Real.exp (σ * x₀) * (1 + σ) / (1 + t ^ 2) * (y ^ (1 - σ) *
          (2 * (P.primesLe y).card + 1.5 * (L * (L + Real.exp 11 * L ^ 2) + L ^ 2 * σ))) :=
          mul_le_mul hFσ hH (norm_nonneg _) ((norm_nonneg _).trans hFσ)
      _ = _ := by
          rw [Real.rpow_def_of_pos hy0, ← hL, hB]
          simp only
          rw [← e]
          ring
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hB0 : Tendsto B atTop (𝓝 0) := by
    have hT : ∀ k : ℕ, Tendsto (fun σ : ℝ => σ ^ k * Real.exp (-(δ * σ))) atTop (𝓝 0) :=
      fun k => (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k δ hδ0).congr fun σ => by
        rw [Real.rpow_natCast, neg_mul]
    have := (((hT 0).const_mul q₀).add (((hT 1).const_mul (q₀ + q₁)).add
      ((hT 2).const_mul q₁))).const_mul (K * y)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun σ => ?_
    rw [hB]
    ring
  obtain ⟨C, hC⟩ := exists_le_of_tendsto_zero hBc hB0 c
  have hHpd : DifferentiableOn ℂ (fun s => F s * Hp P θ X₀ α γ xp y s) {s : ℂ | c₀ < s.re} :=
    fun s hs => ((hFd s hs).mul (h.differentiableAt_Hp
      (lt_of_le_of_lt hc₀ hs)).differentiableWithinAt)
  have hHp0 : ∫ t : ℝ, F (c + t * I) * Hp P θ X₀ α γ xp y (c + t * I) = 0 :=
    integral_vertical_eq_zero (F := fun s => F s * Hp P θ X₀ α γ xp y s) hc hHpd hBd hC hB0
  have hHpi : Integrable (fun t : ℝ => F (c + t * I) * Hp P θ X₀ α γ xp y (c + t * I)) :=
    integrable_vertical_of_bound (F := fun s => F s * Hp P θ X₀ α γ xp y s)
      (hHpd.continuousOn.comp_continuous (by fun_prop) fun t => by simpa using hc)
      (hBd c le_rfl)
  /- The part `log((s-1)/s)`, by Fubini. -/
  set Φ : ℝ → ℝ → ℂ := fun t u =>
    F (c + t * I) * ((u : ℂ) ^ (-((c : ℂ) + t * I)) * (pi0Dens u : ℂ)) with hΦ
  have hΦi : Integrable (Function.uncurry Φ) (volume.prod (volume.restrict (Ioi 1))) := by
    have hb : Integrable (fun p : ℝ × ℝ => ‖F (c + p.1 * I)‖ * (p.2 ^ (-c) * pi0Dens p.2))
        (volume.prod (volume.restrict (Ioi 1))) :=
      hFi.norm.mul_prod (integrableOn_rpow_mul_pi0Dens hc1)
    refine hb.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      have hm1 : Measurable fun p : ℝ × ℝ => F (c + p.1 * I) :=
        (hFc c hc).measurable.comp measurable_fst
      have hm2 : Measurable fun p : ℝ × ℝ => (p.2 : ℂ) ^ (-((c : ℂ) + p.1 * I)) :=
        (continuous_ofReal.measurable.comp measurable_snd).pow
          ((by fun_prop : Continuous fun p : ℝ × ℝ => -((c : ℂ) + p.1 * I)).measurable)
      have hm3 : Measurable fun p : ℝ × ℝ => (pi0Dens p.2 : ℂ) := by
        unfold pi0Dens
        fun_prop
      exact hm1.mul (hm2.mul hm3)
    · have hμ : (volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ))) =
          (volume.prod volume).restrict (univ ×ˢ Ioi 1) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hμ]
      refine (ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)).mpr
        (Eventually.of_forall fun p hp => ?_)
      have hp1 : 1 < p.2 := hp.2
      simp only [Function.uncurry, hΦ, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pi0Dens_nonneg hp1)]
      simp
  have hlogI : ∫ t : ℝ, F (c + t * I) * Complex.log ((c + t * I - 1) / (c + t * I)) =
      -(2 * π * ((∫ u in Ioi (1 : ℝ), f (Real.log u) * pi0Dens u : ℝ) : ℂ)) := by
    calc _ = ∫ t : ℝ, -∫ u in Ioi (1 : ℝ), Φ t u := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [hΦ]
          rw [log_sub_one_div_eq (by rw [hre]; exact hc1), integral_const_mul, mul_neg]
      _ = -∫ u in Ioi (1 : ℝ), ∫ t : ℝ, Φ t u := by
          rw [integral_neg, integral_integral_swap hΦi]
      _ = _ := by
          congr 1
          rw [← integral_complex_ofReal, ← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
          have hu : (1 : ℝ) < u := hu
          simp only [hΦ]
          simp_rw [← mul_assoc]
          rw [integral_mul_const, hinv u (by linarith)]
          push_cast
          ring
  have hlogi : Integrable (fun t : ℝ =>
      F (c + t * I) * Complex.log ((c + t * I - 1) / (c + t * I))) := by
    refine hΦi.integral_prod_left.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Function.uncurry_apply_pair, hΦ]
    rw [log_sub_one_div_eq (by rw [hre]; exact hc1), integral_const_mul, mul_neg]
  /- Assembling. -/
  have hsplit : (fun t : ℝ => F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)) =
      fun t : ℝ => F (c + t * I) * Ly P y (c + t * I) +
        F (c + t * I) * Hp P θ X₀ α γ xp y (c + t * I) +
        F (c + t * I) * Complex.log ((c + t * I - 1) / (c + t * I)) := by
    ext t
    rw [Gright_eq]
    ring
  have hAB : Integrable (fun t : ℝ => F (c + t * I) * Ly P y (c + t * I) +
      F (c + t * I) * Hp P θ X₀ α γ xp y (c + t * I)) := hLyi.add hHpi
  refine ⟨hsplit ▸ hAB.add hlogi, ?_⟩
  rw [hsplit, integral_add hAB hlogi, integral_add hLyi hHpi, hHp0, hlogI,
    add_zero, mul_add, hLyI]
  push_cast
  field_simp
  ring

end LPHyp

end LocalPNT

end
