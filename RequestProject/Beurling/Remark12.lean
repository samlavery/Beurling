module

public import RequestProject.Beurling.LogDeriv
public import RequestProject.Beurling.Main

/-!
# Remark 1.2, direction (b) ⇒ (a)

If `N_P(x) = A x + O(x^β)` with `A > 0`, `β < 1/2`, and `ψ_P(x) = x + O(x^{1-ε'})`, `ε' > 0`,
then `ζ_P` has a zero-free half-plane `Re s > 1 - ε`.

Proof (as in the paper). Partial summation gives, for `Re s > 1`,

  `ζ_P(s) = A s/(s-1) + s ∫_1^∞ (N_P(x) - A x) x^{-s-1} dx`,
  `-ζ_P'(s)/ζ_P(s) = s/(s-1) + s ∫_1^∞ (ψ_P(x) - x) x^{-s-1} dx`.

The right-hand sides `F`, `G` are holomorphic on `Re s > max(β, 1-ε')`, `s ≠ 1`, and
`F' = -F G` there (identity theorem). A zero of `F` of order `n ≥ 1` at `s₀` would make
`F'/F ~ n/(s - s₀)` have a pole, contradicting `F' = -F G`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set BeurlingSystem

namespace Remark12

/-- The tail Mellin integral `∫_1^∞ E(x) x^{-s-1} dx`. -/
noncomputable def tailMellin (E : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi 1, (E x : ℂ) * (x : ℂ) ^ (-s - 1)

variable {E : ℝ → ℝ} {C γ : ℝ}

lemma tailMellin_integrable (hE : LocallyIntegrable E)
    (hb : ∀ x ≥ (1 : ℝ), |E x| ≤ C * x ^ γ) {s : ℂ} (hs : γ < s.re) :
    IntegrableOn (fun x : ℝ => (E x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hint : IntegrableOn (fun x : ℝ => C * x ^ (γ - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
  refine Integrable.mono' hint ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hE.aestronglyMeasurable).restrict
    · exact (by fun_prop : Measurable fun x : ℝ => (x : ℂ) ^ (-s - 1)).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
      Real.norm_eq_abs]
    have hx0 : 0 ≤ x ^ ((-s - 1).re) := Real.rpow_nonneg (by linarith) _
    calc |E x| * x ^ ((-s - 1).re) ≤ C * x ^ γ * x ^ ((-s - 1).re) :=
          mul_le_mul_of_nonneg_right (hb x hx1.le) hx0
      _ = C * x ^ (γ - s.re - 1) := by
          rw [mul_assoc, ← Real.rpow_add (by linarith)]; congr 2; simp; ring

lemma tailMellin_differentiableOn (hE : LocallyIntegrable E)
    (hb : ∀ x ≥ (1 : ℝ), |E x| ≤ C * x ^ γ) :
    DifferentiableOn ℂ (tailMellin E) {s : ℂ | γ < s.re} := by
  set f : ℝ → ℂ := (Ioi 1).indicator fun x => (E x : ℂ)
  have hm : ∀ s, tailMellin E s = mellin f (-s) := by
    intro s
    unfold mellin tailMellin
    have : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • f t) =
        (Ioi 1).indicator fun t => (E t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      ext t
      simp only [f, Set.indicator, smul_eq_mul]
      split_ifs <;> simp [mul_comm]
    rw [this, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0:ℝ) ∩ Ioi 1 = Ioi 1 by ext x; simp]
  have hEc : LocallyIntegrable (fun x => (E x : ℂ)) := by
    intro x
    obtain ⟨U, hU, h⟩ := hE x
    exact ⟨U, hU, h.ofReal⟩
  intro s hs
  simp only [mem_setOf_eq] at hs
  apply DifferentiableAt.differentiableWithinAt
  have hfun : tailMellin E = fun s => mellin f (-s) := funext hm
  rw [hfun]
  refine DifferentiableAt.comp (g := mellin f) s ?_ differentiableAt_id.neg
  refine mellin_differentiableAt_of_isBigO_rpow (a := -γ) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
  · exact (hEc.indicator measurableSet_Ioi).locallyIntegrableOn _
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    simp only [f, Set.indicator, mem_Ioi, hx, if_true, Complex.norm_real, Real.norm_eq_abs,
      neg_neg]
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hb x hx.le
  · simp; linarith
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
    simp [f, not_lt.mpr hx.2.le]
  · simp

/-- Splitting off the main term: `∫_1^∞ W x^{-s-1} = ∫_1^∞ (W - A x) x^{-s-1} + A/(s-1)`. -/
lemma integral_split (W : ℝ → ℝ) (A : ℝ) (hE : LocallyIntegrable fun x => W x - A * x)
    (hb : ∀ x ≥ (1 : ℝ), |W x - A * x| ≤ C * x ^ γ) {s : ℂ} (hs : γ < s.re) (hs1 : 1 < s.re) :
    ∫ x in Ioi 1, (W x : ℂ) * (x : ℂ) ^ (-s - 1) =
      tailMellin (fun x => W x - A * x) s + A / (s - 1) := by
  have h1 := tailMellin_integrable hE hb hs
  have h2 : IntegrableOn (fun x : ℝ => (A : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos).const_mul _
  have hpt : ∀ x ∈ Ioi (1:ℝ), (W x : ℂ) * (x : ℂ) ^ (-s - 1) =
      ((W x - A * x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) + (A : ℂ) * (x : ℂ) ^ (-s) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simp at hx; linarith)
    have : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      have := Complex.cpow_add (-s - 1) 1 hx0
      rw [Complex.cpow_one] at this
      rw [← this]; ring_nf
    rw [this]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1 h2, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  unfold tailMellin
  have hs' : -s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs'' : s - 1 ≠ 0 := fun h => hs' (by linear_combination -h)
  simp only [Complex.ofReal_one, Complex.one_cpow]
  field_simp
  ring

/-- A function satisfying `F' = -F G` with `G` holomorphic on an open set `U` cannot vanish at a
point `s₀ ∈ U` near which it is not identically zero: at a zero of order `n ≥ 1`,
`F'/F ~ n/(s - s₀)` would have a pole. -/
lemma ne_zero_of_deriv_eq {U : Set ℂ} (hU : IsOpen U) {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U)
    (hode : ∀ z ∈ U, deriv F z = -(F z * G z)) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hnz : ¬ ∀ᶠ z in 𝓝 s₀, F z = 0) : F s₀ ≠ 0 := by
  have hFa : AnalyticAt ℂ F s₀ := hF.analyticAt (hU.mem_nhds hs₀)
  cases hn : analyticOrderAt F s₀ with
  | top => exact absurd (analyticOrderAt_eq_top.mp hn) hnz
  | coe n =>
    obtain ⟨g, hg, hg0, hFg⟩ := (hFa.analyticOrderAt_eq_natCast).mp hn
    cases n with
    | zero =>
      have := hFg.self_of_nhds
      simp only [sub_self, pow_zero, one_smul] at this
      rw [this]; exact hg0
    | succ m =>
      exfalso
      have hFg' : F =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ (m + 1) • g z := hFg
      have hd := hFg'.deriv
      have hGc : ContinuousAt G s₀ := (hG.differentiableAt (hU.mem_nhds hs₀)).continuousAt
      set φ : ℂ → ℂ := fun z => (m + 1) * g z + (z - s₀) * (deriv g z + g z * G z)
      have hφc : ContinuousAt φ s₀ := by
        have h1 := hg.continuousAt
        have h2 := hg.deriv.continuousAt
        fun_prop
      have hφ0 : ∀ᶠ z in 𝓝[≠] s₀, φ z = 0 := by
        have hev : ∀ᶠ z in 𝓝 s₀, (z - s₀) ^ m * φ z = 0 := by
          filter_upwards [hd, hFg, hg.eventually_analyticAt, hU.mem_nhds hs₀] with
            z hdz hFz hgz hzU
          have hder : deriv (fun z => (z - s₀) ^ (m + 1) • g z) z =
              (m + 1 : ℂ) * (z - s₀) ^ m * g z + (z - s₀) ^ (m + 1) * deriv g z := by
            have h1 : HasDerivAt (fun z => (z - s₀) ^ (m + 1))
                ((m + 1 : ℕ) * (z - s₀) ^ m) z := by
              simpa using ((hasDerivAt_id z).sub_const s₀).fun_pow (m + 1)
            have := h1.mul hgz.differentiableAt.hasDerivAt
            simp only [smul_eq_mul]
            exact this.deriv.trans (by push_cast; ring)
          have := hode z hzU
          rw [hdz, hder, hFz, smul_eq_mul] at this
          simp only [φ]
          linear_combination this
        rw [eventually_nhdsWithin_iff]
        filter_upwards [hev] with z hz hne
        exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hne))
      have h1 : Tendsto φ (𝓝[≠] s₀) (𝓝 (φ s₀)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto φ (𝓝[≠] s₀) (𝓝 0) :=
        tendsto_const_nhds.congr' (hφ0.mono fun z hz => hz.symm)
      have := tendsto_nhds_unique h1 h2
      simp only [φ, sub_self, zero_mul, add_zero] at this
      exact hg0 ((mul_eq_zero.mp this).resolve_left (by norm_cast))

/-- `ζ_P(2) ≠ 0` (its real part is at least `1`, the contribution of the element `1`). -/
lemma zeta_two_ne_zero (P : BeurlingSystem) (h : AbelMellin.Hyp P.val (fun _ => (1 : ℝ)) 1) :
    P.zeta 2 ≠ 0 := by
  have hs : Summable fun e : ℕ →₀ ℕ => P.val e ^ (-2 : ℝ) := by
    simpa using AbelMellin.summable_rpow h (σ := 2) (by norm_num) (by norm_num)
  have he : P.zeta 2 = ((∑' e : ℕ →₀ ℕ, P.val e ^ (-2 : ℝ) : ℝ) : ℂ) := by
    unfold zeta
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun e => ?_
    rw [Complex.ofReal_cpow (P.val_pos e).le]
    push_cast; ring_nf
  have h1 : (1 : ℝ) ≤ ∑' e : ℕ →₀ ℕ, P.val e ^ (-2 : ℝ) := by
    have := hs.le_tsum 0 (fun j _ => Real.rpow_nonneg (P.val_pos j).le _)
    have h0 : P.val 0 = 1 := by simp [val]
    rwa [h0, Real.one_rpow] at this
  rw [he]
  exact_mod_cast (show (∑' e : ℕ →₀ ℕ, P.val e ^ (-2 : ℝ)) ≠ 0 by linarith)

end Remark12

open Remark12

/-- **Remark 1.2, direction (b) ⇒ (a)**, proved: if `N_P(x) = A x + O(x^β)` with `A > 0`,
`β < 1/2`, and `ψ_P(x) = x + O(x^{1-ε'})` with `ε' > 0`, then `ζ_P` has a zero-free half-plane
`Re s > 1 - ε` (with `ε = min(ε', 1 - β)`). -/
theorem remark12_ba : Remark12_ba := by
  intro P A β hA hβ hNb ε' hε' hψb
  obtain ⟨C, hN⟩ := hNb
  obtain ⟨Cψ, hψ⟩ := hψb
  -- `x^γ ≤ x` for `γ ≤ 1`, `x ≥ 1`
  have hpow : ∀ {γ : ℝ}, γ ≤ 1 → ∀ (K : ℝ) {x : ℝ}, 1 ≤ x → K * x ^ γ ≤ |K| * x := by
    intro γ hγ K x hx
    have h2 : x ^ γ ≤ x := by
      calc x ^ γ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hγ
        _ = x := Real.rpow_one x
    calc K * x ^ γ ≤ |K| * x ^ γ :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by linarith) _)
      _ ≤ |K| * x := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
  -- the partial-summation hypotheses for `N_P` and `ψ_P` (both are `O(x)`)
  have hNH : AbelMellin.Hyp P.val (fun _ => (1 : ℝ)) 1 := by
    refine ⟨P.one_le_val, fun _ => zero_le_one, P.summable_N_ite, A + |C|, fun x hx => ?_⟩
    rw [← P.N_eq_cnt, Real.rpow_one]
    have h1 := (abs_le.mp (hN x hx)).2
    have h3 := hpow (show β ≤ 1 by linarith) C hx
    nlinarith
  have hψH : AbelMellin.Hyp (fun jk : ℕ × ℕ => P.p jk.1 ^ (jk.2 + 1))
      (fun jk => Real.log (P.p jk.1)) 1 := by
    refine ⟨fun jk => P.one_le_pow' _ _, fun jk => Real.log_nonneg (P.one_lt _).le,
      P.summable_psi_ite, 1 + |Cψ|, fun x hx => ?_⟩
    rw [← P.psi_eq_cnt, Real.rpow_one]
    have h1 := (abs_le.mp (hψ x hx)).2
    have h3 := hpow (show 1 - ε' ≤ 1 by linarith) Cψ hx
    nlinarith
  have hNmono : Monotone P.N := fun x y h => by
    rw [P.N_eq_cnt, P.N_eq_cnt]; exact AbelMellin.cnt_mono hNH h
  have hψmono : Monotone P.psi := fun x y h => by
    rw [P.psi_eq_cnt, P.psi_eq_cnt]; exact AbelMellin.cnt_mono hψH h
  have hNli : LocallyIntegrable (fun x => P.N x - A * x) :=
    hNmono.locallyIntegrable.sub (continuous_const.mul continuous_id).locallyIntegrable
  have hψli : LocallyIntegrable (fun x => P.psi x - 1 * x) :=
    hψmono.locallyIntegrable.sub (continuous_const.mul continuous_id).locallyIntegrable
  have hψ' : ∀ x ≥ (1:ℝ), |P.psi x - 1 * x| ≤ Cψ * x ^ (1 - ε') := fun x hx => by
    rw [one_mul]; exact hψ x hx
  -- the continuations of `ζ_P` and of `-ζ_P'/ζ_P`
  set FF : ℂ → ℂ := fun s => A * s / (s - 1) + s * tailMellin (fun x => P.N x - A * x) s
  set GG : ℂ → ℂ := fun s => 1 * s / (s - 1) + s * tailMellin (fun x => P.psi x - 1 * x) s
  have hsub : ∀ s : ℂ, 1 < s.re → s - 1 ≠ 0 := fun s hs h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hFz : ∀ s : ℂ, 1 < s.re → FF s = P.zeta s := by
    intro s hs
    have h := AbelMellin.hasSum_cpow hNH (s := s) (by linarith) hs
    have hcnt : AbelMellin.cnt P.val (fun _ => (1:ℝ)) = P.N :=
      funext fun x => (P.N_eq_cnt x).symm
    rw [hcnt, integral_split P.N A hNli hN (by linarith) hs] at h
    have : P.zeta s = s * (tailMellin (fun x => P.N x - A * x) s + A / (s - 1)) := by
      rw [← h.tsum_eq]; unfold zeta; simp
    rw [this]
    have := hsub s hs
    simp only [FF]
    field_simp
    ring
  have hGl : ∀ s : ℂ, 1 < s.re → GG s = P.lam s := by
    intro s hs
    have h := AbelMellin.hasSum_cpow hψH (s := s) (by linarith) hs
    have hcnt : AbelMellin.cnt (fun jk : ℕ × ℕ => P.p jk.1 ^ (jk.2 + 1))
        (fun jk => Real.log (P.p jk.1)) = P.psi := funext fun x => (P.psi_eq_cnt x).symm
    rw [hcnt, integral_split P.psi 1 hψli hψ' (by linarith) hs] at h
    have : P.lam s = s * (tailMellin (fun x => P.psi x - 1 * x) s + (1:ℝ) / (s - 1)) := by
      rw [← h.tsum_eq]; rfl
    rw [this]
    have := hsub s hs
    simp only [GG]
    push_cast
    field_simp
    ring
  -- the punctured half-plane `V`
  set b : ℝ := 1 - min ε' (1 - β)
  have hbβ : β ≤ b := by simp only [b]; linarith [min_le_right ε' (1 - β)]
  have hbε : 1 - ε' ≤ b := by simp only [b]; linarith [min_le_left ε' (1 - β)]
  have hb1 : b < 1 := by simp only [b]; linarith [lt_min hε' (show 0 < 1 - β by linarith)]
  set V := puncturedHalfPlane b
  have hV : IsOpen V := isOpen_puncturedHalfPlane b
  have hVc : IsPreconnected V := isPreconnected_puncturedHalfPlane b
  have two_mem : (2:ℂ) ∈ V := ⟨by simp; linarith, by norm_num⟩
  have hFdiff : DifferentiableOn ℂ FF V := by
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
    have hT := (tailMellin_differentiableOn hNli hN).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show β < s.re from lt_of_le_of_lt hbβ hs.1))
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (A : ℂ) * s / (s - 1)) s :=
      ((differentiableAt_const _).mul differentiableAt_id).div
        (differentiableAt_id.sub_const 1) hs1
    have h2 : DifferentiableAt ℂ
        (fun s : ℂ => s * tailMellin (fun x => P.N x - A * x) s) s :=
      differentiableAt_id.mul hT
    exact h1.add h2
  have hGdiff : DifferentiableOn ℂ GG V := by
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
    have hT := (tailMellin_differentiableOn hψli hψ').differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 - ε' < s.re from lt_of_le_of_lt hbε hs.1))
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 * s / (s - 1)) s :=
      ((differentiableAt_const _).mul differentiableAt_id).div
        (differentiableAt_id.sub_const 1) hs1
    have h2 : DifferentiableAt ℂ
        (fun s : ℂ => s * tailMellin (fun x => P.psi x - 1 * x) s) s :=
      differentiableAt_id.mul hT
    exact h1.add h2
  -- `F' = -F G` on `V` (identity theorem from `Re s > 1`)
  have hode : ∀ z ∈ V, deriv FF z = -(FF z * GG z) := by
    set H : ℂ → ℂ := fun z => deriv FF z + FF z * GG z
    have hH : AnalyticOnNhd ℂ H V :=
      ((hFdiff.deriv hV).add (hFdiff.mul hGdiff)).analyticOnNhd hV
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : H =ᶠ[𝓝 2] 0 := by
      filter_upwards [hopen.mem_nhds (show (1:ℝ) < (2:ℂ).re by norm_num)] with z hz
      have hz' : 1 < z.re := hz
      have hzF : FF =ᶠ[𝓝 z] P.zeta := by
        filter_upwards [hopen.mem_nhds hz] with w hw; exact hFz w hw
      have hZ : Summable fun e : ℕ →₀ ℕ => P.val e ^ (-z.re) := by
        simpa using AbelMellin.summable_rpow hNH (σ := z.re) (by linarith) hz'
      have hL := AbelMellin.summable_rpow hψH (σ := z.re) (by linarith) hz'
      simp only [H, Pi.zero_apply]
      rw [hzF.deriv_eq, (P.hasDerivAt_zeta hNH hz').deriv, hFz z hz', hGl z hz',
        P.logZeta_eq_lam_mul_zeta hZ hL]
      ring
    have := hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVc two_mem hev
    intro z hz
    have h := this hz
    simp only [H, Pi.zero_apply] at h
    linear_combination h
  refine ⟨min ε' (1 - β), lt_min hε' (by linarith), FF, ⟨hFdiff, hFz⟩, fun s hs => ?_⟩
  refine ne_zero_of_deriv_eq hV hFdiff hGdiff hode hs fun hall => ?_
  have h0 := (hFdiff.analyticOnNhd hV).eqOn_zero_of_preconnected_of_eventuallyEq_zero hVc hs hall
  have h2 := h0 two_mem
  simp only [Pi.zero_apply] at h2
  rw [hFz 2 (by norm_num)] at h2
  exact zeta_two_ne_zero P hNH h2

/-- **Corollary 2.2, second form**, now assuming only Theorem 2.1 (Remark 1.2 (b) ⇒ (a) is
proved above): there is a discrete `[1, β]`-system with `β ≤ 1/4 < 1/2`. -/
theorem corollary_2_2_one_beta_system' (h : Theorem21) :
    ∃ P : BeurlingSystem,
      (∀ β > (1 / 4 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ β) ∧
      ∀ ε' > (0 : ℝ), ¬ ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.psi x - x| ≤ C * x ^ (1 - ε') :=
  corollary_2_2_one_beta_system h remark12_ba

end
