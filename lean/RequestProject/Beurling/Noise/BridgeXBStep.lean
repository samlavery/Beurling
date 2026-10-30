module

public import RequestProject.Beurling.Noise.BridgeXBLevel

/-!
# Lemma 5.27, Step 2: the bounds of the step contributions

With `w = n/d`, `R_d = 1.02 H(x/d)`, `H_n = H(x/n)`:

* `near_bound` : on an `X₀`-near step with a non-terminal parent,
  `|Δ_{d→n}| ≤ ½ TV(D_d) + TV(Ẽ_d)` (the half-TV bound against `φ G ∈ [0,1]`, and
  `|(φ - κ) G| ≤ 1`);
* `far_bound` : on a step that is not `X₀`-near, `Δ_{d→n} = 0` unless
  `|x/n - X₀| ≤ (1 + θ) H_n/2 + R_d/w` (`G` is constant on the support), and then
  `|Δ_{d→n}| ≤ λ₀ ‖D_d‖_KR/(w H_n)` (`G` is `λ₀/H_n`-Lipschitz there, Kantorovich–Rubinstein).

Here `θ` is the Lipschitz constant of `H` on `[X₀⁻/2, ∞)` (`PaperWidth`), and `λ₀ ≥ 1 + 3θ`;
the paper's factor `1 + ϑ_{X₀}` (resp. `1 + 2ϑ_{X₀} ≤ λ₀`) uses the local derivative of `H`,
which is at most `θ`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal NNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- **The bound on `X₀`-near steps**. -/
theorem near_bound {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (X0 : ℝ)
    {d n : ℕ} (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1)
    (hX : X0Near P.labelVal x H X0m d n) :
    |xbStep P H tw X0m x X0 d n| ≤
      1 / 2 * TVD P H tw X0m x d + TVE P H tw X0m x d := by
  have hH := hP.reg
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d
      · simp at hdn; omega
      · exact absurd rfl hd1
    · exact h
  have hφ := trueFilter_ok tw X0m
  obtain ⟨hgi, hgm⟩ := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hH d
  obtain ⟨hti, -⟩ := integrable_gKT (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m) hH d
  rw [xbStep_near hH X0 hdn hn0 hd1 hX]
  set w := Vl P (n / d)
  set Ψ : ℝ → ℝ := fun v => phiT tw X0m d n (v / w) * Gs H X0 (v / w)
  have hΨm : Measurable Ψ := by
    have hGm : Measurable fun v => Gs H X0 (v / w) := by
      have : (fun v => Gs H X0 (v / w)) = fun v => ramp ((v / w - X0) / H (v / w) + 1 / 2) := by
        funext v; exact Gs_eq_ramp hH X0 _
      rw [this]
      exact continuous_ramp.measurable.comp (((measurable_id.div_const _).sub_const _).div
        (hH.lip.continuous.measurable.comp (measurable_id.div_const _)) |>.add_const _)
    exact ((hφ d n).1.comp (measurable_id.div_const _)).mul hGm
  have hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1 := fun v => by
    have h1 := (hφ d n).2 (v / w)
    have h2 := Gs_mem hH X0 (v / w)
    exact ⟨mul_nonneg h1.1 h2.1, by nlinarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hmass := nom_mass (tw := tw) (x := x) hP hval2 hd2
  have h1 := abs_sub_half_le hgi hΨm hΨ (posn P.labelVal x d)
  rw [hmass] at h1
  set E := Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d
  have hEi : Integrable E := hti.sub hgi
  have h2 : |∫ v, E v * ((phiT tw X0m d n (v / w) - kapN tw X0m P.labelVal x d n) *
      Gs H X0 (v / w))| ≤ TVE P H tw X0m x d := by
    unfold TVE
    rw [← integral_norm_eq_lintegral_enorm hEi.1]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun v => abs_nonneg _) hEi.norm
      (Filter.Eventually.of_forall fun v => ?_))
    simp only [abs_mul, Real.norm_eq_abs]
    have hk := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x d n
    have hp := (hφ d n).2 (v / w)
    have hg := Gs_mem hH X0 (v / w)
    have a1 : |phiT tw X0m d n (v / w) - kapN tw X0m P.labelVal x d n| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have a2 : |Gs H X0 (v / w)| ≤ 1 := by rw [abs_of_nonneg hg.1]; exact hg.2
    calc |E v| * (|phiT tw X0m d n (v / w) - kapN tw X0m P.labelVal x d n| *
          |Gs H X0 (v / w)|) ≤ |E v| * (1 * 1) := by gcongr
      _ = |E v| := by ring
  have hTVD : 1 / 2 * ((∫⁻ v, ‖gNom P H tw X0m x d v‖ₑ).toReal + |cN P tw X0m x d|) =
      1 / 2 * TVD P H tw X0m x d := rfl
  calc |-((∫ v, gNom P H tw X0m x d v * Ψ v) - cN P tw X0m x d * Ψ (posn P.labelVal x d)) -
        ∫ v, E v * ((phiT tw X0m d n (v / w) - kapN tw X0m P.labelVal x d n) *
          Gs H X0 (v / w))|
      ≤ |(∫ v, gNom P H tw X0m x d v * Ψ v) - cN P tw X0m x d * Ψ (posn P.labelVal x d)| +
        |∫ v, E v * ((phiT tw X0m d n (v / w) - kapN tw X0m P.labelVal x d n) *
          Gs H X0 (v / w))| := by
        rw [abs_sub_comm]
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, add_comm]
    _ ≤ _ := by rw [← hTVD]; exact add_le_add h1 h2

/-- The numerical inequality behind the Lipschitz constant `λ₀/H_n`. -/
lemma lip_numeric {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 100) :
    (1 + θ * 1.532 / (1 - 0.516 * θ)) / (1 - 0.516 * θ) ≤ 1 + 3 * θ := by
  set q := 1 - 0.516 * θ with hq
  have hpos : 0 < q := by linarith
  rw [div_le_iff₀ hpos]
  have key : (1 + θ * 1.532 / q) * q = q + θ * 1.532 := by field_simp
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  rw [key]
  rw [hq]
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

set_option maxHeartbeats 3000000 in
/-- **The bound off `X₀`-near steps**: `Δ_{d→n} = 0` unless
`|x/n - X₀| ≤ (1 + θ) H_n/2 + R_d/w`, and then `|Δ_{d→n}| ≤ λ₀ ‖D_d‖_KR/(w H_n)`. -/
theorem far_bound {ε θ lam0 X0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (hlam : 1 + 3 * θ ≤ lam0) {d n : ℕ} (hd : d ∈ n.properDivisors)
    (hd1 : d ≠ 1) (hpos : X0m / 2 ≤ posn P.labelVal x n)
    (hX : ¬ X0Near P.labelVal x H X0m d n) :
    |xbStep P H tw X0m x X0 d n| ≤
      if |posn P.labelVal x n - X0| ≤ (1 + θ) * H (posn P.labelVal x n) / 2 +
          1.02 * H (posn P.labelVal x d) / Vl P (n / d)
      then lam0 * KRD P H tw X0m x d / (Vl P (n / d) * H (posn P.labelVal x n)) else 0 := by
  have hH := hP.reg
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d
      · simp at hdn; omega
      · exact absurd rfl hd1
    · exact h
  have hθ0 := hP.theta_nonneg
  have hθ1 := hP.theta_le
  have hXm := hP.X0m_pos
  have hHX := hH.pos X0
  have hXX : X0m ≤ X0 := by linarith
  set w := Vl P (n / d) with hwdef
  set a := posn P.labelVal x d with hadef
  set pn := posn P.labelVal x n with hpndef
  set Hn := H pn
  set R := 1.02 * H a
  have hw : 2 ≤ w := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < w := by linarith
  have ha : a = pn * w := posn_mul hval hdn hn0
  have hHn := hH.pos pn
  have hHa := hH.pos a
  have hR0 : 0 < R := by positivity
  have hsmall := hP.small pn hpos
  have hRw : R / w ≤ 0.5106 * Hn := by
    have := hP.step_le hpos hw
    rw [← ha] at this
    calc R / w = 1.02 * (H a / w) := by ring
      _ ≤ 1.02 * (0.5005 * Hn) := by gcongr
      _ ≤ 0.5106 * Hn := by nlinarith
  have hRw0 : 0 < R / w := div_pos hR0 hw0
  -- the formula
  obtain ⟨hgi, hgm⟩ := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hH d
  set g := gNom P H tw X0m x d
  set Φ : ℝ → ℝ := fun v => Gs H X0 (v / w)
  have hGm : Measurable Φ := by
    have : Φ = fun v => ramp ((v / w - X0) / H (v / w) + 1 / 2) := by
      funext v; exact Gs_eq_ramp hH X0 _
    rw [this]
    exact continuous_ramp.measurable.comp (((measurable_id.div_const _).sub_const _).div
      (hH.lip.continuous.measurable.comp (measurable_id.div_const _)) |>.add_const _)
  have hΦb : ∀ᵐ v ∂volume, ‖Φ v‖ ≤ 1 := Filter.Eventually.of_forall fun v => by
    have := Gs_mem hH X0 (v / w)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hgΦ : Integrable (fun v => g v * Φ v) := by
    simpa [mul_comm] using hgi.bdd_mul (c := 1) hGm.aestronglyMeasurable hΦb
  have hmass := nom_mass (tw := tw) (x := x) hP hval2 hd2
  have hΦa : Φ a = Gs H X0 pn := by simp only [Φ]; rw [ha]; field_simp
  have hform : xbStep P H tw X0m x X0 d n =
      -(kapN tw X0m P.labelVal x d n * ∫ v, g v * (Φ v - Φ a)) := by
    rw [xbStep_far hH X0 hd1 hX]
    congr 2
    rw [show (fun v => g v * (Φ v - Φ a)) = fun v => g v * Φ v - g v * Φ a by
      funext v; ring, integral_sub hgΦ (hgi.mul_const _), integral_mul_const, hmass, hΦa]
  -- truncation
  set g' : ℝ → ℝ := (Icc (a - R) (a + R)).indicator g
  have hgg : g =ᵐ[volume] g' := by
    filter_upwards [nom_ae_zero (tw := tw) (x := x) hP hval2 hd2] with v hv0
    have hv : R < |v - a| → g v = 0 := hv0
    simp only [g']
    by_cases hm : v ∈ Icc (a - R) (a + R)
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
      apply hv
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hm
      rcases hm with hm | hm
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hg'i : Integrable g' := hgi.indicator measurableSet_Icc
  have hg'm : Measurable g' := hgm.indicator measurableSet_Icc
  have hsupp : ∀ v, R < |v - a| → g' v = 0 := by
    intro v hv
    simp only [g']
    rw [Set.indicator_of_notMem]
    rw [Set.mem_Icc]; intro h
    have : |v - a| ≤ R := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    linarith
  have hint_eq : ∫ v, g v * (Φ v - Φ a) = ∫ v, g' v * (Φ v - Φ a) :=
    integral_congr_ae (hgg.mono fun v hv => by simp only; rw [hv])
  have hk := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x d n
  rw [hform, abs_neg, abs_mul, abs_of_nonneg hk.1, hint_eq]
  split_ifs with hB
  · -- the Kantorovich–Rubinstein bound
    have hpnX : 0.9078 * X0 ≤ pn := by
      have h1 : |pn - X0| ≤ 1.0156 * Hn := by
        refine hB.trans ?_
        have : (1 + θ) * Hn / 2 ≤ 0.505 * Hn := by nlinarith
        change (1 + θ) * Hn / 2 + R / w ≤ 1.0156 * Hn
        linarith
      have := (abs_le.mp h1).1
      nlinarith
    set S := Icc (pn - 1.01 * (R / w)) (pn + 1.01 * (R / w))
    have hSge : ∀ c ∈ S, X0m / 2 ≤ c := by
      intro c hc
      have := hc.1
      nlinarith
    set hm := Hn * (1 - 0.516 * θ)
    have hhm : 0 < hm := by
      have : 0 < 1 - 0.516 * θ := by linarith
      positivity
    have hHS : ∀ c ∈ S, hm ≤ H c := by
      intro c hc
      have hl := hP.lip c pn (hSge c hc) hpos
      have hcp : |c - pn| ≤ 1.01 * (R / w) := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have := (abs_le.mp hl).2
      have h' := (abs_le.mp hl).1
      have hc' : θ * |c - pn| ≤ θ * (1.01 * (R / w)) := mul_le_mul_of_nonneg_left hcp hθ0
      have hθR : θ * (R / w) ≤ θ * (0.5106 * Hn) := mul_le_mul_of_nonneg_left hRw hθ0
      change Hn * (1 - 0.516 * θ) ≤ H c
      linarith
    have hlipS : ∀ c₁ ∈ S, ∀ c₂ ∈ S, |H c₁ - H c₂| ≤ θ * |c₁ - c₂| :=
      fun c₁ h₁ c₂ h₂ => hP.lip c₁ c₂ (hSge c₁ h₁) (hSge c₂ h₂)
    have hMS : ∀ c ∈ S, |c - X0| ≤ 1.532 * Hn := by
      intro c hc
      have hcp : |c - pn| ≤ 1.01 * (R / w) := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have : (1 + θ) * Hn / 2 ≤ 0.505 * Hn := by nlinarith
      calc |c - X0| ≤ |c - pn| + |pn - X0| := abs_sub_le _ _ _
        _ ≤ 1.01 * (R / w) + ((1 + θ) * Hn / 2 + R / w) := add_le_add hcp hB
        _ ≤ 1.532 * Hn := by nlinarith
    set Lc := (1 + θ * (1.532 * Hn) / hm) / hm
    have hLc0 : 0 ≤ Lc := by positivity
    have hLc : Lc ≤ lam0 / Hn := by
      have hq0 : (1 - 0.516 * θ) ≠ 0 := by linarith
      have hHn0 : Hn ≠ 0 := hHn.ne'
      have e : Lc = (1 + θ * 1.532 / (1 - 0.516 * θ)) / (1 - 0.516 * θ) / Hn := by
        simp only [Lc, hm]; field_simp
      rw [e]
      exact div_le_div_of_nonneg_right ((lip_numeric hθ0 hθ1).trans hlam) hHn.le
    -- the Lipschitz extension
    set lo := a - 1.01 * R
    set hi := a + 1.01 * R
    have hlohi : lo ≤ hi := by simp only [lo, hi]; linarith
    have hJS : ∀ v ∈ Icc lo hi, v / w ∈ S := by
      intro v hv
      have e : a / w = pn := by rw [ha]; field_simp
      have e1 : (pn - 1.01 * (R / w)) * w = a - 1.01 * R := by rw [ha]; field_simp
      have e2 : (pn + 1.01 * (R / w)) * w = a + 1.01 * R := by rw [ha]; field_simp
      constructor
      · rw [le_div_iff₀ hw0, e1]; exact hv.1
      · rw [div_le_iff₀ hw0, e2]; exact hv.2
    have hΦlip : LipschitzOnWith ⟨Lc / w, by positivity⟩ Φ (Icc lo hi) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro v₁ h₁ v₂ h₂
      simp only [Real.dist_eq, NNReal.coe_mk, Φ]
      have := Gs_lip hH hhm hθ0 hHS hlipS hMS (hJS v₁ h₁) (hJS v₂ h₂)
      calc |Gs H X0 (v₁ / w) - Gs H X0 (v₂ / w)| ≤ Lc * |v₁ / w - v₂ / w| := this
        _ = Lc / w * |v₁ - v₂| := by
          rw [← sub_div, abs_div, abs_of_pos hw0]; ring
    set Φt : ℝ → ℝ := fun v => (Icc lo hi).restrict Φ (projIcc lo hi hlohi v)
    have hΦt : LipschitzWith ⟨Lc / w, by positivity⟩ Φt := by
      have := hΦlip.to_restrict.comp (LipschitzWith.projIcc hlohi)
      exact this.weaken (mul_one _).le
    have hΦtΦ : ∀ v ∈ Icc lo hi, Φt v = Φ v := by
      intro v hv
      simp only [Φt, projIcc_of_mem hlohi hv]
      rfl
    have hamem : a ∈ Icc lo hi := ⟨by simp only [lo]; linarith, by simp only [hi]; linarith⟩
    have hint2 : ∫ v, g' v * (Φ v - Φ a) = ∫ v, g' v * (Φt v - Φt a) := by
      congr 1; funext v
      by_cases hv : v ∈ Icc (a - R) (a + R)
      · rw [hΦtΦ v ⟨by simp only [lo]; linarith [hv.1], by simp only [hi]; linarith [hv.2]⟩,
          hΦtΦ a hamem]
      · simp only [g']; rw [Set.indicator_of_notMem hv]; ring
    have hkr := kr_dual hg'i hg'm hsupp hΦt
    have hcdf : ∀ t, cdf g' t = cdf g t := fun t => by
      unfold cdf; exact (integral_congr_ae (hgg.symm.filter_mono ae_restrict_le))
    have hmass' : ∫ v, g' v = cN P tw X0m x d := by rw [← hmass]; exact integral_congr_ae hgg.symm
    have hKR : (∫⁻ t, ‖cdf g' t - (∫ v, g' v) * stepF a t‖ₑ).toReal = KRD P H tw X0m x d := by
      unfold KRD; congr 2; funext t; rw [hcdf, hmass']
    rw [hKR] at hkr
    have hKR0 : 0 ≤ KRD P H tw X0m x d := ENNReal.toReal_nonneg
    rw [hint2]
    calc kapN tw X0m P.labelVal x d n * |∫ v, g' v * (Φt v - Φt a)|
        ≤ 1 * |∫ v, g' v * (Φt v - Φt a)| :=
          mul_le_mul_of_nonneg_right hk.2 (abs_nonneg _)
      _ ≤ Lc / w * KRD P H tw X0m x d := by rw [one_mul]; exact hkr
      _ ≤ lam0 / Hn / w * KRD P H tw X0m x d := by gcongr
      _ = lam0 * KRD P H tw X0m x d / (w * Hn) := by field_simp
  · -- `G` is constant on the support
    push_neg at hB
    have hzero : ∀ v ∈ Icc (a - R) (a + R), Φ v = Φ a := by
      intro v hv
      set c := v / w
      have e1 : (pn - R / w) * w = a - R := by rw [ha]; field_simp
      have e2 : (pn + R / w) * w = a + R := by rw [ha]; field_simp
      have hc1 : pn - R / w ≤ c := by
        simp only [c]; rw [le_div_iff₀ hw0, e1]; exact hv.1
      have hc2 : c ≤ pn + R / w := by
        simp only [c]; rw [div_le_iff₀ hw0, e2]; exact hv.2
      rw [hΦa]
      simp only [Φ]
      change Gs H X0 c = Gs H X0 pn
      rcases le_or_gt (0.53 * X0m) pn with hbig | hsml
      · have hcX : X0m / 2 ≤ c := by nlinarith
        have hl := hP.lip c pn hcX hpos
        have hcp : |c - pn| ≤ R / w := abs_le.mpr ⟨by linarith, by linarith⟩
        have hHc : H c ≤ (1 + θ) * Hn := by
          have := (abs_le.mp hl).2
          nlinarith [mul_le_mul_of_nonneg_left hcp hθ0]
        rcases le_or_gt pn X0 with hle | hgt
        · rw [abs_of_nonpos (by linarith)] at hB
          rw [Gs_eq_zero_of hH (by linarith), Gs_eq_zero_of hH (by nlinarith)]
        · rw [abs_of_pos (by linarith)] at hB
          rw [Gs_eq_one_of hH (by linarith), Gs_eq_one_of hH (by nlinarith)]
      · -- far below `X₀`
        have hHc : ∀ c', 0.474 * X0m ≤ c' → c' ≤ 0.558 * X0m → H c' ≤ 0.108 * X0m := by
          intro c' h1 h2
          have hl := hH.lip.dist_le_mul c' (X0m / 2)
          simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
          have hs := hP.small (X0m / 2) le_rfl
          have := (abs_le.mp hl).2
          have : |c' - X0m / 2| ≤ 0.058 * X0m := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
        have hc0 : 0.474 * X0m ≤ c := by nlinarith
        have hc0' : c ≤ 0.558 * X0m := by nlinarith
        have hp0 : 0.474 * X0m ≤ pn := by linarith
        have hp0' : pn ≤ 0.558 * X0m := by linarith
        rw [Gs_eq_zero_of hH (by linarith [hHc c hc0 hc0']),
          Gs_eq_zero_of hH (by linarith [hHc pn hp0 hp0'])]
    have : ∫ v, g' v * (Φ v - Φ a) = 0 := by
      rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
      simp only [Pi.zero_apply]
      by_cases hv : v ∈ Icc (a - R) (a + R)
      · rw [hzero v hv]; ring
      · simp only [g']; rw [Set.indicator_of_notMem hv]; ring
    rw [this, abs_zero, mul_zero]

end KR

end
