module

public import RequestProject.Beurling.Zeros

/-!
# Further properties of `ζ_P` and of the designed zeros

* `BeurlingSystem.zetaCont_residue`: if `N_P(x) = A x + O(x^β)` with `β < 1`, then
  `(s - 1) ζ_P(s) → A` as `s → 1` (simple pole with residue `A`).
* `BeurlingSystem.norm_zetaCont_le`: the continuation grows at most linearly in vertical
  half-planes: `|ζ_P(s)| ≤ (|A| + |C|/(σ₀ - β)) |s|` for `Re s ≥ σ₀ > β`, `|s - 1| ≥ 1`.
* `BeurlingSystem.zeta_ne_zero`: `ζ_P(s) ≠ 0` for `Re s > 1`.
* `TheoremAConclusion.tendsto_abs_im`: the zeros `ρ_k` of Theorem 2.1(ii) satisfy
  `|Im ρ_k| → ∞` (they cannot accumulate at a finite point, since `ζ_P` is not identically
  zero and has a pole at `s = 1`).
* `exists_system_zeros_escaping`: assuming Theorem 2.1, a system with `N_P(x) = x + O(x^β)`
  (every `β > 1/4`) whose zeta function has zeros with `Re ρ_k → 1`, `|Im ρ_k| → ∞`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Metric BeurlingSystem Remark12

namespace BeurlingSystem

/-- `N_P(x) = A x + O(x^β)` with `β < 1` gives the partial-summation hypotheses for `N_P`. -/
lemma hyp_of_N_bound (P : BeurlingSystem) {A C β : ℝ} (hβ : β < 1)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) :
    AbelMellin.Hyp P.val (fun _ => (1 : ℝ)) 1 := by
    refine ⟨P.one_le_val, fun _ => zero_le_one, P.summable_N_ite, A + |C|, fun x hx => ?_⟩
    rw [← P.N_eq_cnt, Real.rpow_one]
    have h1 := (abs_le.mp (hN x hx)).2
    have h2 : x ^ β ≤ x := by
      calc x ^ β ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hβ.le
        _ = x := Real.rpow_one x
    have h3 : C * x ^ β ≤ |C| * x :=
      calc C * x ^ β ≤ |C| * x ^ β :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C| * x := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    nlinarith

/-- The tail Mellin integral of `N_P - A x` is holomorphic on `Re s > β`. -/
lemma tailMellin_N_differentiableOn (P : BeurlingSystem) {A C β : ℝ} (hβ : β < 1)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) :
    DifferentiableOn ℂ (tailMellin (fun x => P.N x - A * x)) {s : ℂ | β < s.re} := by
  have hNH := P.hyp_of_N_bound hβ hN
  have hNmono : Monotone P.N := fun x y h => by
    rw [P.N_eq_cnt, P.N_eq_cnt]; exact AbelMellin.cnt_mono hNH h
  have hNli : LocallyIntegrable (fun x => P.N x - A * x) :=
    hNmono.locallyIntegrable.sub (continuous_const.mul continuous_id).locallyIntegrable
  exact tailMellin_differentiableOn hNli hN

/-- **The pole of `ζ_P` at `s = 1`**: if `N_P(x) = A x + O(x^β)` with `β < 1`, then
`(s - 1) ζ_P(s) → A` as `s → 1`, `s ≠ 1`, for the continuation `zetaCont P A`. -/
theorem zetaCont_residue (P : BeurlingSystem) {A C β : ℝ} (hβ : β < 1)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) :
    Tendsto (fun s => (s - 1) * P.zetaCont A s) (𝓝[≠] 1) (𝓝 (A : ℂ)) := by
  set T := tailMellin (fun x => P.N x - A * x)
  have hT : ContinuousAt T 1 :=
    ((P.tailMellin_N_differentiableOn hβ hN).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show β < (1 : ℂ).re by simpa using hβ))).continuousAt
  have hg : ContinuousAt (fun s : ℂ => (A : ℂ) * s + (s - 1) * s * T s) 1 := by
    fun_prop
  have h1 : Tendsto (fun s : ℂ => (A : ℂ) * s + (s - 1) * s * T s) (𝓝[≠] 1) (𝓝 (A : ℂ)) := by
    have := hg.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp only [zetaCont, T]
  field_simp

/-- **Linear growth of the continuation**: if `N_P(x) = A x + O(x^β)` and `σ₀ > β`, then
`|ζ_P(s)| ≤ (|A| + |C|/(σ₀ - β)) |s|` for `Re s ≥ σ₀` and `|s - 1| ≥ 1`. -/
theorem norm_zetaCont_le (P : BeurlingSystem) {A C β σ₀ : ℝ} (hβσ : β < σ₀)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) {s : ℂ} (hs : σ₀ ≤ s.re)
    (hs1 : 1 ≤ ‖s - 1‖) :
    ‖P.zetaCont A s‖ ≤ (|A| + |C| / (σ₀ - β)) * ‖s‖ := by
  have hT : ‖tailMellin (fun x => P.N x - A * x) s‖ ≤ |C| / (σ₀ - β) := by
    have hint : IntegrableOn (fun x : ℝ => |C| * x ^ (β - σ₀ - 1)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    have hval : ∫ x in Ioi (1:ℝ), |C| * x ^ (β - σ₀ - 1) = |C| / (σ₀ - β) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
      have : β - σ₀ - 1 + 1 = -(σ₀ - β) := by ring
      rw [this]
      field_simp
    rw [← hval]
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
      Real.norm_eq_abs]
    have h1 : |P.N x - A * x| ≤ |C| * x ^ β :=
      (hN x hx1.le).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (by linarith) _))
    have h2 : x ^ ((-s - 1).re) ≤ x ^ (-σ₀ - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1.le
      simp; linarith
    calc |P.N x - A * x| * x ^ ((-s - 1).re) ≤ (|C| * x ^ β) * x ^ (-σ₀ - 1) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ = |C| * x ^ (β - σ₀ - 1) := by
          rw [mul_assoc, ← Real.rpow_add (by linarith)]; congr 2; ring
  have hs0 : 0 < ‖s - 1‖ := by linarith
  have hA : ‖(A : ℂ) * s / (s - 1)‖ ≤ |A| * ‖s‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hs0]
    nlinarith [mul_nonneg (abs_nonneg A) (norm_nonneg s)]
  unfold zetaCont
  calc ‖(A : ℂ) * s / (s - 1) + s * tailMellin (fun x => P.N x - A * x) s‖
      ≤ ‖(A : ℂ) * s / (s - 1)‖ + ‖s‖ * ‖tailMellin (fun x => P.N x - A * x) s‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ |A| * ‖s‖ + ‖s‖ * (|C| / (σ₀ - β)) := by gcongr
    _ = (|A| + |C| / (σ₀ - β)) * ‖s‖ := by ring

/-- `ψ_P(x) ≤ log x · N_P(x)`: each prime power `p_j^{k+1} ≤ x` is an element `≤ x`, and
`log p_j ≤ log x`. -/
lemma psi_le_log_mul_N (P : BeurlingSystem) {x : ℝ} (hx : 1 ≤ x) :
    P.psi x ≤ Real.log x * P.N x := by
  rw [P.psi_eq_cnt, P.N_eq_cnt, AbelMellin.cnt, AbelMellin.cnt, ← tsum_mul_left]
  set f : ℕ × ℕ → (ℕ →₀ ℕ) := fun jk => Finsupp.single jk.1 (jk.2 + 1)
  have hf : Function.Injective f := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    simp only [f] at h
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · omega
  set g : (ℕ →₀ ℕ) → ℝ := fun e => Real.log x * if P.val e ≤ x then (1 : ℝ) else 0
  have hg0 : ∀ e, 0 ≤ g e := fun e => mul_nonneg (Real.log_nonneg hx) (by split_ifs <;> norm_num)
  have hgs : Summable g := (P.summable_N_ite x).mul_left _
  refine le_trans ?_ (_root_.tsum_comp_le_tsum_of_inj hgs hg0 hf)
  refine (P.summable_psi_ite x).tsum_le_tsum (fun jk => ?_) (hgs.comp_injective hf)
  simp only [g, f, Function.comp, P.val_single]
  split_ifs with h
  · rw [mul_one]
    calc Real.log (P.p jk.1) = Real.log (P.p jk.1 ^ 1) := by rw [pow_one]
      _ ≤ Real.log (P.p jk.1 ^ (jk.2 + 1)) :=
          Real.log_le_log (by have := P.p_pos jk.1; positivity)
            (pow_le_pow_right₀ (P.one_lt _).le (by omega))
      _ ≤ Real.log x := Real.log_le_log (pow_pos (P.p_pos _) _) h
  · simp

/-- **`ζ_P` has no zeros in `Re s > 1`** (for systems with `N_P(x) = A x + O(x^β)`, `β < 1`). -/
theorem zeta_ne_zero (P : BeurlingSystem) {A C β : ℝ} (hβ : β < 1)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) {s : ℂ} (hs : 1 < s.re) :
    P.zeta s ≠ 0 := by
  have hNH := P.hyp_of_N_bound hβ hN
  obtain ⟨K, hK⟩ := hNH.bound
  set c : ℝ := min ((1 + s.re) / 2) (3 / 2)
  have hc1 : 1 < c := lt_min (by linarith) (by norm_num)
  have hcs : c < s.re := (min_le_left _ _).trans_lt (by linarith)
  have hc2 : c < 2 := (min_le_right _ _).trans_lt (by norm_num)
  set δ : ℝ := c - 1
  have hδ : 0 < δ := by simp only [δ]; linarith
  -- `ψ_P(x) = O(x^c)`
  have hψb : ∀ x ≥ (1 : ℝ), |P.psi x| ≤ (|K| / δ) * x ^ c := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hpsi0 : 0 ≤ P.psi x := by
      rw [P.psi_eq_cnt]
      exact tsum_nonneg fun jk => by
        split_ifs <;> simp [Real.log_nonneg (P.one_lt jk.1).le]
    have hN0 : 0 ≤ P.N x := by unfold N; positivity
    have hNK : P.N x ≤ |K| * x := by
      have := hK x hx; rw [← P.N_eq_cnt, Real.rpow_one] at this
      nlinarith [le_abs_self K]
    have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [abs_of_nonneg hpsi0]
    calc P.psi x ≤ Real.log x * P.N x := P.psi_le_log_mul_N hx
      _ ≤ (x ^ δ / δ) * (|K| * x) := mul_le_mul hlog hNK hN0 (by positivity)
      _ = (|K| / δ) * x ^ c := by
          rw [show c = δ + 1 by simp only [δ]; ring, Real.rpow_add hx0, Real.rpow_one]
          ring
  have hψH : AbelMellin.Hyp (fun jk : ℕ × ℕ => P.p jk.1 ^ (jk.2 + 1))
      (fun jk => Real.log (P.p jk.1)) c := by
    refine ⟨fun jk => P.one_le_pow' _ _, fun jk => Real.log_nonneg (P.one_lt _).le,
      P.summable_psi_ite, |K| / δ, fun x hx => ?_⟩
    rw [← P.psi_eq_cnt]
    exact (le_abs_self _).trans (hψb x hx)
  have hψmono : Monotone P.psi := fun x y h => by
    rw [P.psi_eq_cnt, P.psi_eq_cnt]; exact AbelMellin.cnt_mono hψH h
  set U : Set ℂ := {z : ℂ | c < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  -- `Λ_P(z) = z ∫_1^∞ ψ_P(x) x^{-z-1} dx` on `U`, hence holomorphic there
  have hlam : ∀ z ∈ U, P.lam z = z * tailMellin P.psi z := by
    intro z hz
    have h := AbelMellin.hasSum_cpow hψH (s := z) (by simp only [U, mem_setOf_eq] at hz; linarith) hz
    have hcnt : AbelMellin.cnt (fun jk : ℕ × ℕ => P.p jk.1 ^ (jk.2 + 1))
        (fun jk => Real.log (P.p jk.1)) = P.psi := funext fun x => (P.psi_eq_cnt x).symm
    rw [hcnt] at h
    exact h.tsum_eq
  have hlamD : DifferentiableOn ℂ P.lam U := by
    have hT := tailMellin_differentiableOn hψmono.locallyIntegrable hψb
    exact (differentiableOn_id.mul hT).congr hlam
  have hzD : DifferentiableOn ℂ P.zeta U := fun z hz =>
    (P.hasDerivAt_zeta hNH (show 1 < z.re by simp only [U, mem_setOf_eq] at hz; linarith)
      ).differentiableAt.differentiableWithinAt
  have hode : ∀ z ∈ U, deriv P.zeta z = -(P.zeta z * P.lam z) := by
    intro z hz
    have hz' : c < z.re := hz
    have hz1 : 1 < z.re := by linarith
    have hZ : Summable fun e : ℕ →₀ ℕ => P.val e ^ (-z.re) := by
      simpa using AbelMellin.summable_rpow hNH (σ := z.re) (by linarith) hz1
    have hL := AbelMellin.summable_rpow hψH (σ := z.re) (by linarith) hz'
    rw [(P.hasDerivAt_zeta hNH hz1).deriv, P.logZeta_eq_lam_mul_zeta hZ hL]
    ring
  have hsU : s ∈ U := hcs
  have two_mem : (2 : ℂ) ∈ U := by simp only [U, mem_setOf_eq]; norm_num; exact hc2
  refine ne_zero_of_deriv_eq hU hzD hlamD hode hsU fun hall => ?_
  have h0 := (hzD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt c).isPreconnected hsU hall two_mem
  exact zeta_two_ne_zero P hNH h0

end BeurlingSystem

namespace TheoremAConclusion

variable {θ : ℝ} {P : BeurlingSystem}

/-- **The designed zeros escape vertically**: in Theorem 2.1(ii), `Re ρ_k → 1` and
`|Im ρ_k| → ∞`. -/
theorem tendsto_abs_im (h : TheoremAConclusion θ P) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, P.IsZetaContinuation a F ∧ ∃ ρ : ℕ → ℂ,
      (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
      Tendsto (fun k => (ρ k).re) atTop (𝓝 1) ∧
      Tendsto (fun k => |(ρ k).im|) atTop atTop := by
  obtain ⟨a, ha, F, hF, ρ, xk, C, hx, hz, hb, -⟩ := h.2
  have hre := tendsto_one_of_log_asymptotic (fun k => (ρ k).re) xk C hx hb
  set β' : ℝ := (θ + 1) / 2
  have hβ' : β' < 1 := by simp only [β']; linarith
  obtain ⟨CN, hCN⟩ := N_bound_of_part_i hθ h.1 (β := β') (by simp only [β']; linarith)
  have hcont := P.zetaCont_isZetaContinuation hβ' hCN
  have hNH := P.hyp_of_N_bound hβ' hCN
  -- `Re ρ_k < 1` eventually
  have hlt : ∀ᶠ k in atTop, (ρ k).re < 1 := by
    have hy : Tendsto (fun k => Real.log (xk k)) atTop atTop := Real.tendsto_log_atTop.comp hx
    have hyy : Tendsto (fun k => Real.log (Real.log (xk k))) atTop atTop :=
      Real.tendsto_log_atTop.comp hy
    filter_upwards [hy.eventually_gt_atTop 0, hyy.eventually_gt_atTop C] with k h1 h2
    have := (abs_le.mp (hb k)).1
    by_contra hk
    push_neg at hk
    nlinarith
  refine ⟨a, ha, F, hF, ρ, hz, hre, ?_⟩
  rw [Filter.tendsto_atTop]
  intro M
  by_contra hM
  rw [Filter.not_eventually] at hM
  have hfreq : ∃ᶠ k in atTop, ρ k ∈ closedBall (0 : ℂ) (|M| + 2) ∧ (ρ k).re < 1 := by
    have hev : ∀ᶠ k in atTop, |(ρ k).re| < 2 ∧ (ρ k).re < 1 := by
      filter_upwards [hre.eventually (Ioo_mem_nhds (show (0:ℝ) < 1 by norm_num)
        (show (1:ℝ) < 2 by norm_num)), hlt] with k hk hk'
      exact ⟨abs_lt.mpr ⟨by linarith [hk.1], hk.2⟩, hk'⟩
    refine (hM.and_eventually hev).mono fun k hk => ⟨?_, hk.2.2⟩
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im (ρ k)
    have : |(ρ k).im| ≤ |M| := (le_of_lt (not_le.mp hk.1)).trans (le_abs_self M)
    linarith [hk.2.1]
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨z₀, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall
    (fun n => (hφP n).1)
  set σ := φ ∘ ψ
  have hσ : Tendsto σ atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hlim' : Tendsto (fun n => ρ (σ n)) atTop (𝓝 z₀) := hlim
  have hre0 : z₀.re = 1 :=
    tendsto_nhds_unique ((Complex.continuous_re.tendsto z₀).comp hlim') (hre.comp hσ)
  have hne : ∀ n, ρ (σ n) ≠ z₀ := fun n e => by
    have := (hφP (ψ n)).2
    rw [show ρ (φ (ψ n)) = ρ (σ n) from rfl, e, hre0] at this
    exact lt_irrefl _ this
  have hlimW : Tendsto (fun n => ρ (σ n)) atTop (𝓝[≠] z₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim', Eventually.of_forall hne⟩
  have hF0 : ∀ n, F (ρ (σ n)) = 0 := fun n => (hz _).2
  have two_mem : (2:ℂ) ∈ puncturedHalfPlane a := ⟨by simp; linarith, by norm_num⟩
  by_cases hz1 : z₀ = 1
  · subst hz1
    have hres := (P.zetaCont_residue hβ' hCN).comp hlimW
    have hmem : ∀ᶠ n in atTop, ρ (σ n) ∈ puncturedHalfPlane (max a β') := by
      have hb1 : max a β' < 1 := max_lt ha hβ'
      filter_upwards [(hre.comp hσ).eventually (lt_mem_nhds hb1)] with n hn
      exact ⟨hn, (hz _).1.2⟩
    have h0 : Tendsto (fun n => (ρ (σ n) - 1) * P.zetaCont 1 (ρ (σ n))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hmem] with n hn
      rw [← (hF.eqOn hcont) hn, hF0 n, mul_zero]
    have := tendsto_nhds_unique hres h0
    simp at this
  · have hz₀ : z₀ ∈ puncturedHalfPlane a := ⟨show a < z₀.re by rw [hre0]; exact ha, hz1⟩
    have hU := isOpen_puncturedHalfPlane a
    have hFa : AnalyticAt ℂ F z₀ := hF.1.analyticAt (hU.mem_nhds hz₀)
    rcases hFa.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · have := (hF.1.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (isPreconnected_puncturedHalfPlane a) hz₀ h0 two_mem
      simp only [Pi.zero_apply] at this
      rw [hF.2 2 (by norm_num)] at this
      exact zeta_two_ne_zero P hNH this
    · obtain ⟨n, hn⟩ := (hlimW.eventually h0).exists
      exact hn (hF0 n)

end TheoremAConclusion

/-- Assuming Theorem 2.1: there is a discrete Beurling system with `N_P(x) = x + O(x^β)` for every
`β > 1/4` whose zeta function has zeros `ρ_k` with `Re ρ_k → 1` and `|Im ρ_k| → ∞`. -/
theorem exists_system_zeros_escaping (h : Theorem21) :
    ∃ P : BeurlingSystem,
      (∀ β > (1 / 4 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ β) ∧
      ∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, P.IsZetaContinuation a F ∧ ∃ ρ : ℕ → ℂ,
        (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
        Tendsto (fun k => (ρ k).re) atTop (𝓝 1) ∧
        Tendsto (fun k => |(ρ k).im|) atTop atTop := by
  have hθ : (1 / 4 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000) := by
    constructor <;> norm_num
  obtain ⟨P, hP⟩ := exists_realisation h hθ
  refine ⟨P, fun β hβ => ?_, hP.tendsto_abs_im (by norm_num) (by norm_num)⟩
  obtain ⟨C, hC⟩ := hP.N_bound (by norm_num) hβ
  exact ⟨C, fun x hx => by simpa using hC x hx⟩

end
