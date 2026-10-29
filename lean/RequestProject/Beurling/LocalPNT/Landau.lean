module

public import Mathlib

/-! # Landau's lemma -/

@[expose] public section

open Complex ComplexConjugate Metric Set Filter Topology

namespace LocalPNT

theorem exists_zero_factorization {f : ℂ → ℂ} {z₀ : ℂ} {s R : ℝ} (hs : 0 ≤ s) (hsR : s < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hf0 : f z₀ ≠ 0) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ) (g : ℂ → ℂ), (∀ u ∈ S, u ∈ closedBall z₀ s ∧ f u = 0) ∧
      AnalyticOnNhd ℂ g (closedBall z₀ s) ∧ (∀ z ∈ closedBall z₀ s, g z ≠ 0) ∧
      ∀ z ∈ ball z₀ s, f z = (∏ u ∈ S, (z - u) ^ n u) * g z := by
  set U := closedBall z₀ s
  have hUR : U ⊆ ball z₀ R := closedBall_subset_ball hsR
  have hA : AnalyticOnNhd ℂ f U := (hf.analyticOnNhd isOpen_ball).mono hUR
  have hmer : MeromorphicOn f U := hA.meromorphicOn
  have hz₀U : z₀ ∈ U := mem_closedBall_self hs
  have h0 : meromorphicOrderAt f z₀ = 0 := by
    rw [(hA z₀ hz₀U).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hf0)]
    rfl
  have htop : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := fun u =>
    hmer.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall z₀ s).isPreconnected
      hz₀U u.2 (by simp [h0])
  have hfin := (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall z₀ s)
  obtain ⟨g, hgA, hg0, hfg⟩ := hmer.extract_zeros_poles htop hfin
  have hD0 := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA
  set D := MeromorphicOn.divisor f U
  refine ⟨hfin.toFinset, fun u => (D u).toNat, g, ?_, hgA, fun z hz => hg0 ⟨z, hz⟩, ?_⟩
  · intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have huU : u ∈ U := D.supportWithinDomain hu
    refine ⟨huU, ?_⟩
    by_contra hfu
    apply hu
    rw [MeromorphicOn.divisor_apply hmer huU, (hA u huU).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hfu)]
    rfl
  · intro z hz
    have hφ : ∀ w, (∏ᶠ u, (fun x => x - u) ^ D u) w =
        ∏ u ∈ hfin.toFinset, (w - u) ^ (D u).toNat := by
      intro w
      have hsub : Function.mulSupport (fun u => (fun x : ℂ => x - u) ^ D u) ⊆ hfin.toFinset := by
        intro u hu
        rw [Finite.coe_toFinset]
        by_contra h
        exact hu (by simp [Function.notMem_support.mp h])
      rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_apply]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [Pi.pow_apply, ← zpow_natCast, Int.toNat_of_nonneg (hD0 u)]
    have hzU : z ∈ U := ball_subset_closedBall hz
    have hev : (fun w => (∏ u ∈ hfin.toFinset, (w - u) ^ (D u).toNat) * g w) =ᶠ[𝓝[≠] z] f := by
      have h1 := (mem_codiscreteWithin.mp hfg) z hzU
      rw [disjoint_principal_right] at h1
      filter_upwards [h1, nhdsWithin_le_nhds
        (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)] with w h1 h2
      by_contra h
      refine h1 ⟨h2, fun h' => h ?_⟩
      simp only [mem_setOf_eq, Pi.smul_apply', smul_eq_mul, hφ] at h'
      exact h'.symm
    have hc : ContinuousAt (fun w => (∏ u ∈ hfin.toFinset, (w - u) ^ (D u).toNat) * g w) z :=
      (by fun_prop : Continuous fun w : ℂ => ∏ u ∈ hfin.toFinset, (w - u) ^ (D u).toNat)
        |>.continuousAt.mul (hgA z hzU).continuousAt
    exact tendsto_nhds_unique ((hA z hzU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)

lemma mem_of_factorization {f g : ℂ → ℂ} {z₀ z : ℂ} {s : ℝ} {S : Finset ℂ} {n : ℂ → ℕ}
    (hfg : ∀ z ∈ ball z₀ s, f z = (∏ u ∈ S, (z - u) ^ n u) * g z)
    (hg0 : ∀ z ∈ closedBall z₀ s, g z ≠ 0) (hz : z ∈ ball z₀ s) (hz0 : f z = 0) :
    z ∈ S ∧ n z ≠ 0 := by
  rw [hfg z hz] at hz0
  obtain ⟨u, hu, hu0⟩ := Finset.prod_eq_zero_iff.mp
    ((mul_eq_zero.mp hz0).resolve_right (hg0 z (ball_subset_closedBall hz)))
  obtain ⟨h1, h2⟩ := pow_eq_zero_iff'.mp hu0
  rw [sub_eq_zero] at h1
  exact h1 ▸ ⟨hu, h2⟩

theorem norm_logDeriv_le_of_ne_zero {F : ℂ → ℂ} {z₀ : ℂ} {s s₁ M : ℝ} (hs : 0 < s)
    (hss₁ : s < s₁) (hF : DifferentiableOn ℂ F (ball z₀ s₁))
    (hF0 : ∀ z ∈ closedBall z₀ s, F z ≠ 0) (hM : ∀ z ∈ sphere z₀ s, ‖F z‖ ≤ M * ‖F z₀‖) :
    ‖logDeriv F z₀‖ ≤ 2 / s * Real.log M := by
  have hz₀ : z₀ ∈ closedBall z₀ s := mem_closedBall_self hs.le
  have hFz₀ : 0 < ‖F z₀‖ := norm_pos_iff.mpr (hF0 z₀ hz₀)
  -- maximum modulus: the bound holds on the closed disc
  have hM' : ∀ z ∈ closedBall z₀ s, ‖F z‖ ≤ M * ‖F z₀‖ := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((hF.mono ?_).diffContOnCl) ?_ (by rwa [closure_ball z₀ hs.ne'])
    · rw [closure_ball z₀ hs.ne']; exact closedBall_subset_ball hss₁
    · rwa [frontier_ball z₀ hs.ne']
  have hM1 : 1 ≤ M := by
    have := hM' z₀ hz₀
    nlinarith
  -- a slightly larger zero-free disc
  obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall z₀ s).exists_thickening_subset_open
    (hF.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton)
    (fun z hz => ⟨closedBall_subset_ball hss₁ hz, hF0 z hz⟩)
  rw [thickening_closedBall hδ hs.le] at hδs
  set s₂ := δ + s
  have hFs₂ : DifferentiableOn ℂ F (ball z₀ s₂) := hF.mono fun z hz => (hδs hz).1
  have hFs₂0 : ∀ z ∈ ball z₀ s₂, F z ≠ 0 := fun z hz => (hδs hz).2
  -- a holomorphic logarithm of `F`
  obtain ⟨h₀, hh₀⟩ : IsExactOn (logDeriv F) (ball z₀ s₂) := by
    apply DifferentiableOn.isExactOn_ball
    intro z hz
    have hd := (hFs₂.differentiableAt (isOpen_ball.mem_nhds hz))
    refine (DifferentiableAt.div ?_ hd (hFs₂0 z hz)).differentiableWithinAt
    exact ((hFs₂.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz))
  have hexp : EqOn (logDeriv F) (logDeriv fun z => exp (h₀ z)) (ball z₀ s₂) := by
    intro z hz
    rw [logDeriv_apply (fun z => exp (h₀ z)), ((hh₀ z hz).cexp).deriv]
    field_simp [exp_ne_zero]
  obtain ⟨c, -, hc⟩ := (logDeriv_eqOn_iff hFs₂
    (fun z hz => (hh₀ z hz).differentiableAt.cexp.differentiableWithinAt) isOpen_ball
    (convex_ball z₀ s₂).isPreconnected (fun z _ => exp_ne_zero _) hFs₂0).mp hexp
  have hs₂ : s < s₂ := by simp only [s₂]; linarith
  have hre : ∀ z ∈ closedBall z₀ s, (h₀ z - h₀ z₀).re ≤ Real.log M := by
    intro z hz
    have hzb : z ∈ ball z₀ s₂ := closedBall_subset_ball hs₂ hz
    have hz₀b : z₀ ∈ ball z₀ s₂ := closedBall_subset_ball hs₂ hz₀
    have h1 := hM' z hz
    rw [hc hzb] at h1
    rw [hc hz₀b] at h1 hFz₀
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_exp] at h1 hFz₀
    rw [Real.le_log_iff_exp_le (by linarith), sub_re, Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]
    have hc0 : 0 < ‖c‖ := pos_of_mul_pos_left hFz₀ (Real.exp_pos _).le
    nlinarith [mul_le_mul_iff_of_pos_left hc0 (b := Real.exp (h₀ z).re)
      (c := M * Real.exp (h₀ z₀).re)]
  -- Borel–Carathéodory for `H w = h₀ (z₀ + w) - h₀ z₀`
  set H : ℂ → ℂ := fun w => h₀ (z₀ + w) - h₀ z₀
  have hHd : ∀ w ∈ ball (0 : ℂ) s₂, HasDerivAt H (logDeriv F (z₀ + w)) w := by
    intro w hw
    have : z₀ + w ∈ ball z₀ s₂ := by simpa [mem_ball, dist_eq_norm] using hw
    exact ((hh₀ _ this).comp_const_add z₀ w).sub_const _
  have key : ∀ ε, 0 < ε → ‖logDeriv F z₀‖ ≤ 2 / s * Real.log M + ε := by
    intro ε hε
    set A := Real.log M + ε * s / 2
    have hA : 0 < A := by have := Real.log_nonneg hM1; positivity
    have hBC : ∀ w ∈ ball (0 : ℂ) s, ‖H w‖ ≤ 2 * A * ‖w‖ / (s - ‖w‖) := by
      intro w hw
      refine Complex.borelCaratheodory_zero hA
        (fun v hv => (hHd v (ball_subset_ball hs₂.le hv)).differentiableAt.differentiableWithinAt)
        (fun v hv => ?_) hs hw (by simp [H])
      have : z₀ + v ∈ closedBall z₀ s := by
        simpa [mem_closedBall, dist_eq_norm] using (mem_ball_zero_iff.mp hv).le
      have := hre _ this
      simp only [mem_setOf_eq, H, A]
      nlinarith
    have hd0 := hHd 0 (mem_ball_self (hs.trans hs₂))
    rw [add_zero] at hd0
    have h1 := (hasDerivAt_iff_tendsto_slope.mp hd0).norm
    have h2 : Tendsto (fun w : ℂ => 2 * A / (s - ‖w‖)) (𝓝[≠] 0) (𝓝 (2 * A / s)) := by
      have : ContinuousAt (fun w : ℂ => 2 * A / (s - ‖w‖)) 0 :=
        continuousAt_const.div (continuousAt_const.sub continuous_norm.continuousAt)
          (by simp [hs.ne'])
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    have h3 := le_of_tendsto_of_tendsto h1 h2 ?_
    · calc ‖logDeriv F z₀‖ ≤ 2 * A / s := h3
        _ = _ := by simp only [A]; field_simp
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hs)] with w hw0 hws
      have hw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hws' : ‖w‖ < s := mem_ball_zero_iff.mp hws
      rw [slope_def_field, show H 0 = 0 by simp [H], sub_zero, sub_zero, norm_div,
        div_le_div_iff₀ hw (by linarith)]
      have := hBC w hws
      rw [le_div_iff₀ (by linarith)] at this
      linarith
  exact le_of_forall_pos_le_add key

/-- The contribution `Re(z₀ - u) (1/|z₀ - u|² - 1/s²)` of a zero `u` to `-Re f'/f(z₀)`. -/
noncomputable def zeroTerm (z₀ u : ℂ) (s : ℝ) : ℝ :=
  (z₀ - u).re * (1 / ‖z₀ - u‖ ^ 2 - 1 / s ^ 2)

lemma zeroTerm_nonneg {z₀ u : ℂ} {s : ℝ} (hu : u.re ≤ z₀.re) (hu0 : u ≠ z₀)
    (hus : u ∈ ball z₀ s) : 0 ≤ zeroTerm z₀ u s := by
  have h0 : 0 < ‖z₀ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu0.symm)
  have h1 : ‖z₀ - u‖ < s := by rwa [mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at hus
  refine mul_nonneg (by simpa using hu) (sub_nonneg.mpr ?_)
  gcongr

lemma re_logDeriv_blaschke (z₀ u : ℂ) {s : ℝ} (hs : s ≠ 0) (hu : u ≠ z₀) :
    (1 / (z₀ - u) + conj (u - z₀) / ((s ^ 2 : ℝ) : ℂ)).re = zeroTerm z₀ u s := by
  have h0 : ‖z₀ - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu.symm)
  rw [add_re, div_ofReal_re, one_div, inv_re, normSq_eq_norm_sq, conj_re, zeroTerm,
    ← neg_sub z₀ u, neg_re]
  field_simp
  ring

lemma logDeriv_prod_pow_mul {S : Finset ℂ} {n : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {g : ℂ → ℂ} {x : ℂ}
    (hφ : ∀ u ∈ S, φ u x ≠ 0) (hφd : ∀ u ∈ S, DifferentiableAt ℂ (φ u) x) (hg : g x ≠ 0)
    (hgd : DifferentiableAt ℂ g x) :
    logDeriv (fun z => (∏ u ∈ S, φ u z ^ n u) * g z) x =
      ∑ u ∈ S, n u * logDeriv (φ u) x + logDeriv g x := by
  rw [logDeriv_mul (f := fun z => ∏ u ∈ S, φ u z ^ n u) x
    (Finset.prod_ne_zero_iff.mpr fun u hu => pow_ne_zero _ (hφ u hu)) hg
    (DifferentiableAt.fun_finset_prod fun u hu => (hφd u hu).pow _) hgd,
    logDeriv_prod (f := fun u z => φ u z ^ n u) (fun u hu => pow_ne_zero _ (hφ u hu))
      (fun u hu => (hφd u hu).pow _)]
  congr 1
  exact Finset.sum_congr rfl fun u hu => logDeriv_fun_pow (hφd u hu) _

lemma logDeriv_blaschke_denom (z₀ a : ℂ) {s : ℝ} (hs : s ≠ 0) :
    logDeriv (fun z => ((s : ℂ) ^ 2 - (z - z₀) * a) / s) z₀ = -a / ((s ^ 2 : ℝ) : ℂ) := by
  have hd : HasDerivAt (fun z => ((s : ℂ) ^ 2 - (z - z₀) * a) / s) (-(1 * a) / s) z₀ :=
    ((((hasDerivAt_id z₀).sub_const z₀).mul_const a).const_sub _).div_const _
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  rw [logDeriv_apply, hd.deriv]
  push_cast
  field_simp
  ring

/-- Landau's lemma for a radius `s` whose circle carries no zeros: all zeros of `f` in the closed
disc of radius `s₁ > s` lie in the open disc of radius `s`, and each of them contributes. -/
theorem landau_core {f : ℂ → ℂ} {z₀ : ℂ} {s s₁ R M : ℝ} (hs : 0 < s) (hss₁ : s < s₁)
    (hs₁R : s₁ < R) (hM0 : 0 ≤ M) (hf : DifferentiableOn ℂ f (ball z₀ R)) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ sphere z₀ s, ‖f z‖ ≤ M * ‖f z₀‖)
    (hzero : ∀ z ∈ closedBall z₀ s₁, f z = 0 → z.re ≤ z₀.re ∧ z ∈ ball z₀ s) :
    -(logDeriv f z₀).re ≤ 2 / s * Real.log M ∧
      ∀ ρ ∈ ball z₀ s, f ρ = 0 →
        -(logDeriv f z₀).re ≤ 2 / s * Real.log M - zeroTerm z₀ ρ s := by
  obtain ⟨S, n, g, hS, hgA, hg0, hfg⟩ :=
    exists_zero_factorization (hs.le.trans hss₁.le) hs₁R hf hf0
  have hSz : ∀ u ∈ S, u.re ≤ z₀.re ∧ u ∈ ball z₀ s ∧ u ≠ z₀ := fun u hu =>
    ⟨(hzero u (hS u hu).1 (hS u hu).2).1, (hzero u (hS u hu).1 (hS u hu).2).2,
      fun h => hf0 (h ▸ (hS u hu).2)⟩
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  set q : ℂ → ℂ → ℂ := fun u z => ((s : ℂ) ^ 2 - (z - z₀) * conj (u - z₀)) / s with hq
  set F : ℂ → ℂ := fun z => (∏ u ∈ S, q u z ^ n u) * g z with hF
  have hz₀s : z₀ ∈ ball z₀ s₁ := mem_ball_self (hs.trans hss₁)
  have hgd : DifferentiableOn ℂ g (ball z₀ s₁) :=
    hgA.differentiableOn.mono ball_subset_closedBall
  have hqz₀ : ∀ u, q u z₀ = s := fun u => by simp only [hq]; field_simp; ring
  -- `F` has no zeros on the closed disc of radius `s`
  have hF0 : ∀ z ∈ closedBall z₀ s, F z ≠ 0 := by
    intro z hz
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun u hu => pow_ne_zero _ ?_)
      (hg0 z (closedBall_subset_closedBall hss₁.le hz))
    simp only [hq, ne_eq, div_eq_zero_iff, hs', or_false, sub_eq_zero]
    intro h
    have h1 := congrArg norm h
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_conj] at h1
    have h2 : ‖z - z₀‖ ≤ s := by rwa [mem_closedBall, dist_eq_norm] at hz
    have h3 : ‖u - z₀‖ < s := by have := (hSz u hu).2.1; rwa [mem_ball, dist_eq_norm] at this
    nlinarith [norm_nonneg (z - z₀), norm_nonneg (u - z₀)]
  -- on the circle `|F| = |f|`
  have hFf : ∀ z ∈ sphere z₀ s, ‖F z‖ = ‖f z‖ := by
    intro z hz
    have hz' : ‖z - z₀‖ = s := by rwa [mem_sphere, dist_eq_norm] at hz
    rw [hfg z (sphere_subset_ball hss₁ hz), norm_mul, norm_mul, norm_prod, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [norm_pow, norm_pow]
    congr 1
    have hss : (s : ℂ) ^ 2 = (z - z₀) * conj (z - z₀) := by
      rw [mul_conj, normSq_eq_norm_sq, hz']; push_cast; rfl
    simp only [hq]
    rw [hss, ← mul_sub, ← map_sub, norm_div, norm_mul, norm_conj, hz', norm_real,
      Real.norm_eq_abs, abs_of_pos hs, sub_sub_sub_cancel_right]
    field_simp
  have hfF : ‖f z₀‖ ≤ ‖F z₀‖ := by
    rw [hfg z₀ hz₀s, norm_mul, norm_mul, norm_prod, norm_prod]
    gcongr with u hu
    rw [norm_pow, norm_pow, hqz₀, norm_real, Real.norm_eq_abs, abs_of_pos hs]
    gcongr
    have := (hSz u hu).2.1
    rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at this
    exact this.le
  have hFd : DifferentiableOn ℂ F (ball z₀ s₁) := by
    refine DifferentiableOn.mul ?_ hgd
    simp only [hq]
    fun_prop
  have hFbound := norm_logDeriv_le_of_ne_zero hs hss₁ hFd hF0 fun z hz => by
    rw [hFf z hz]; exact (hM z hz).trans (mul_le_mul_of_nonneg_left hfF hM0)
  have hz₀c : z₀ ∈ closedBall z₀ s₁ := mem_closedBall_self (hs.trans hss₁).le
  have hlin : ∀ u ∈ S, logDeriv (fun z => z - u) z₀ = 1 / (z₀ - u) := fun u _ => by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have hfP : logDeriv f z₀ = logDeriv (fun z => (∏ u ∈ S, (z - u) ^ n u) * g z) z₀ := by
    have hev : f =ᶠ[𝓝 z₀] fun z => (∏ u ∈ S, (z - u) ^ n u) * g z :=
      eventually_of_mem (isOpen_ball.mem_nhds hz₀s) hfg
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hsum : logDeriv f z₀ =
      logDeriv F z₀ + ∑ u ∈ S, n u * (1 / (z₀ - u) + conj (u - z₀) / ((s ^ 2 : ℝ) : ℂ)) := by
    have h1 := logDeriv_prod_pow_mul (S := S) (n := n) (φ := fun u z => z - u)
      (fun u hu => sub_ne_zero.mpr (hSz u hu).2.2.symm) (fun u _ => by fun_prop)
      (hg0 z₀ hz₀c) (hgA z₀ hz₀c).differentiableAt
    have h2 := logDeriv_prod_pow_mul (S := S) (n := n) (φ := q)
      (fun u _ => by rw [hqz₀]; exact hs') (fun u _ => by simp only [hq]; fun_prop)
      (hg0 z₀ hz₀c) (hgA z₀ hz₀c).differentiableAt
    rw [Finset.sum_congr rfl fun u hu => by rw [hlin u hu]] at h1
    rw [Finset.sum_congr rfl fun u _ => by
      rw [show q u = fun z => ((s : ℂ) ^ 2 - (z - z₀) * conj (u - z₀)) / s from rfl,
        logDeriv_blaschke_denom z₀ _ hs.ne']] at h2
    rw [hfP, h1, hF, h2]
    simp only [mul_add, Finset.sum_add_distrib, neg_div, mul_neg, Finset.sum_neg_distrib]
    ring
  have hre : (logDeriv f z₀).re = (logDeriv F z₀).re + ∑ u ∈ S, n u * zeroTerm z₀ u s := by
    rw [hsum, add_re, re_sum]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← ofReal_natCast, re_ofReal_mul, re_logDeriv_blaschke z₀ u hs.ne' (hSz u hu).2.2]
  have hnn : ∀ u ∈ S, 0 ≤ (n u : ℝ) * zeroTerm z₀ u s := fun u hu =>
    mul_nonneg (Nat.cast_nonneg _) (zeroTerm_nonneg (hSz u hu).1 (hSz u hu).2.2 (hSz u hu).2.1)
  have hFre : -(logDeriv F z₀).re ≤ 2 / s * Real.log M :=
    (neg_le_abs _).trans ((abs_re_le_norm _).trans hFbound)
  refine ⟨by linarith [Finset.sum_nonneg hnn], fun ρ hρ hρ0 => ?_⟩
  have hρS := mem_of_factorization hfg hg0 (ball_subset_ball hss₁.le hρ) hρ0
  have h1 : (n ρ : ℝ) * zeroTerm z₀ ρ s ≤ ∑ u ∈ S, n u * zeroTerm z₀ u s :=
    Finset.single_le_sum hnn hρS.1
  have h2 : zeroTerm z₀ ρ s ≤ n ρ * zeroTerm z₀ ρ s :=
    le_mul_of_one_le_left (zeroTerm_nonneg (hSz ρ hρS.1).1 (hSz ρ hρS.1).2.2 (hSz ρ hρS.1).2.1)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρS.2)
  linarith

theorem landau_eventually {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖)
    (hzero : ∀ z ∈ closedBall z₀ r, f z = 0 → z.re ≤ z₀.re) :
    ∀ᶠ s in 𝓝[<] r, -(logDeriv f z₀).re ≤ 2 / s * Real.log M ∧
      ∀ ρ ∈ ball z₀ s, f ρ = 0 →
        -(logDeriv f z₀).re ≤ 2 / s * Real.log M - zeroTerm z₀ ρ s := by
  have hM0 : 0 ≤ M := by
    have h1 := hM z₀ (mem_closedBall_self hr.le)
    have h2 : 0 < ‖f z₀‖ := norm_pos_iff.mpr hf0
    nlinarith
  obtain ⟨S, n, g, -, -, hg0, hfg⟩ := exists_zero_factorization hr.le hrR hf hf0
  have hS : ∀ᶠ s in 𝓝[<] r, ∀ u ∈ S.filter (fun u => ‖u - z₀‖ < r), ‖u - z₀‖ < s :=
    (eventually_all_finset _).2 fun u hu =>
      mem_of_superset (Ioo_mem_nhdsLT (Finset.mem_filter.mp hu).2) fun _ h => h.1
  filter_upwards [Ioo_mem_nhdsLT hr, hS] with s ⟨hs0, hsr⟩ hsS
  refine landau_core hs0 (s₁ := (s + r) / 2) (by linarith) (by linarith) hM0 hf hf0
    (fun z hz => hM z (sphere_subset_closedBall.trans (closedBall_subset_closedBall hsr.le) hz))
    fun z hz hz0 => ?_
  have hzr : ‖z - z₀‖ < r := by
    rw [mem_closedBall, dist_eq_norm] at hz; linarith
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  refine ⟨hzero z (ball_subset_closedBall hzb) hz0, ?_⟩
  rw [mem_ball, dist_eq_norm]
  exact hsS z (Finset.mem_filter.mpr ⟨(mem_of_factorization hfg hg0 hzb hz0).1, hzr⟩)

theorem landau_lemma {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖)
    (hzero : ∀ z ∈ closedBall z₀ r, f z = 0 → z.re ≤ z₀.re) :
    -(deriv f z₀ / f z₀).re ≤ 2 / r * Real.log M := by
  have ht : Tendsto (fun s : ℝ => 2 / s * Real.log M) (𝓝[<] r) (𝓝 (2 / r * Real.log M)) :=
    ((continuousAt_const.div continuousAt_id hr.ne').mul continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto ht
    ((landau_eventually hr hrR hf hf0 hM hzero).mono fun _ h => h.1)

theorem landau_lemma_zero {f : ℂ → ℂ} {z₀ ρ : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖)
    (hzero : ∀ z ∈ closedBall z₀ r, f z = 0 → z.re ≤ z₀.re)
    (hρ : ρ ∈ closedBall z₀ r) (hρ0 : f ρ = 0) :
    -(deriv f z₀ / f z₀).re ≤
      2 / r * Real.log M - (z₀ - ρ).re * (1 / ‖z₀ - ρ‖ ^ 2 - 1 / r ^ 2) := by
  have hρr : ‖z₀ - ρ‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm'] at hρ
  rcases hρr.eq_or_lt with h | h
  · rw [h, sub_self, mul_zero, sub_zero]
    exact landau_lemma hr hrR hf hf0 hM hzero
  have ht : Tendsto (fun s : ℝ => 2 / s * Real.log M - zeroTerm z₀ ρ s) (𝓝[<] r)
      (𝓝 (2 / r * Real.log M - zeroTerm z₀ ρ r)) := by
    refine ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds
    unfold zeroTerm
    have : r ^ 2 ≠ 0 := by positivity
    fun_prop (disch := first | assumption | exact hr.ne')
  refine ge_of_tendsto ht ?_
  filter_upwards [landau_eventually hr hrR hf hf0 hM hzero, Ioo_mem_nhdsLT h] with s hs hs'
  exact hs.2 ρ (by rw [mem_ball, dist_eq_norm']; exact hs'.1) hρ0

end LocalPNT

end
