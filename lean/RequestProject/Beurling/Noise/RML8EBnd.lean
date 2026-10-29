module

public import RequestProject.Beurling.Noise.MarginPoint

/-!
# Round 8: the boundary term `hbd` of Step 2 of Proposition 5.35(B)

`KR.RML8E.abs_int_Bavg_sub_le` : for a window width `H` that varies slowly on the scale of the
windows (`|H(z) - H(s)| ≤ κ H(s)` for `|z - s| ≤ H_*`, `κ ≤ 1/10`, `0 < H ≤ H_*` near
`[a, b]`, `H ≥ h_l > 0` on `[a, b]`) and `f` measurable with `|f| ≤ M` on
`[a - H_*, b + H_*]`,

  `|∫_a^b (B f(z) - f(z)) dz| ≤ M (3κ(b - a) + 8 H_*)`,   `B f(z) = H(z)⁻¹ ∫_{|s-z|≤H(z)/2} f`.

The proof is Fubini: `∫_a^b B f = ∫ f(s) w(s) ds` with
`w(s) = ∫_a^b H(z)⁻¹ 1[|s - z| ≤ H(z)/2] dz`; `|w(s) - 1| ≤ 3κ` at the interior points
`s ∈ [a + H_*, b - H_*]`, `0 ≤ w ≤ (1+κ)/(1-κ) ≤ 2` everywhere, `w = 0` off
`[a - H_*, b + H_*]`; the boundary strips have total length `4 H_*`.

`KR.RML8E.hbd_of` : the fields `hbd`, `hBnd0`, `hBnd` of `KR.RML6.G1BInputs` with
`Bnd := M(3κ(b-a) + 8H_*)`, once `M(3κ(b-a) + 8H_*) ≤ 40√y`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace KR.RML8E

/-- The window kernel `K(z, s) = H(z)⁻¹ 1[z - H(z)/2 ≤ s ≤ z + H(z)/2]`. -/
noncomputable def wk (H : ℝ → ℝ) (z s : ℝ) : ℝ :=
  if z - H z / 2 ≤ s ∧ s ≤ z + H z / 2 then (H z)⁻¹ else 0

/-- The weight `w(s) = ∫_{(a,b]} K(z, s) dz`. -/
noncomputable def wW (H : ℝ → ℝ) (a b s : ℝ) : ℝ := ∫ z in Ioc a b, wk H z s

section

variable {H : ℝ → ℝ}

lemma wk_nonneg (hH : ∀ z, 0 < H z) (z s : ℝ) : 0 ≤ wk H z s := by
  unfold wk; split_ifs
  · exact (inv_pos.mpr (hH z)).le
  · exact le_rfl

lemma Bavg_eq_int_wk (hH : ∀ z, 0 < H z) (f : ℝ → ℝ) (z : ℝ) :
    Margin.Bavg (H z) f z = ∫ s, wk H z s * f s := by
  unfold Margin.Bavg
  have hz := hH z
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, ← integral_const_mul]
  congr 1; funext s
  unfold wk
  simp only [Set.indicator, Set.mem_Icc]
  split_ifs <;> simp

lemma measurable_wk (hHm : Measurable H) : Measurable (Function.uncurry (wk H)) := by
  unfold wk Function.uncurry
  refine Measurable.ite ?_ ((hHm.comp measurable_fst).inv) measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_fst.sub ((hHm.comp measurable_fst).div_const 2))
      measurable_snd
  · exact measurableSet_le measurable_snd
      (measurable_fst.add ((hHm.comp measurable_fst).div_const 2))

/-- Standing hypotheses on the width. -/
structure WHyp (H : ℝ → ℝ) (a b Hs κ hl : ℝ) : Prop where
  meas : Measurable H
  pos : ∀ z, 0 < H z
  hab : a ≤ b
  Hs0 : 0 < Hs
  κ0 : 0 ≤ κ
  κ1 : κ ≤ 1 / 10
  le_Hs : ∀ s, a - Hs ≤ s → s ≤ b + Hs → H s ≤ Hs
  hl0 : 0 < hl
  low : ∀ z, a ≤ z → z ≤ b → hl ≤ H z
  close : ∀ s, a - Hs ≤ s → s ≤ b + Hs → ∀ z, a ≤ z → z ≤ b → |z - s| ≤ Hs →
    |H z - H s| ≤ κ * H s

variable {a b Hs κ hl : ℝ}

lemma WHyp.near (h : WHyp H a b Hs κ hl) {z s : ℝ} (hza : a ≤ z) (hzb : z ≤ b)
    (hw : wk H z s ≠ 0) : |z - s| ≤ Hs / 2 ∧ a - Hs ≤ s ∧ s ≤ b + Hs := by
  unfold wk at hw
  split_ifs at hw with hc
  · have hHz : H z ≤ Hs := h.le_Hs z (by linarith [h.Hs0]) (by linarith [h.Hs0])
    have hHz0 := h.pos z
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
    · linarith [hc.1]
    · linarith [hc.2]
  · exact absurd rfl hw

lemma WHyp.integrableOn_wk (h : WHyp H a b Hs κ hl) (s : ℝ) :
    IntegrableOn (fun z => wk H z s) (Ioc a b) := by
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioc]) ?_ hl⁻¹ ?_
  · exact ((measurable_wk h.meas).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (wk_nonneg h.pos z s)]
    unfold wk; split_ifs
    · exact inv_anti₀ h.hl0 (h.low z hz.1.le hz.2)
    · exact (inv_pos.mpr h.hl0).le

lemma WHyp.wW_nonneg (h : WHyp H a b Hs κ hl) (s : ℝ) : 0 ≤ wW H a b s :=
  setIntegral_nonneg measurableSet_Ioc fun z _ => wk_nonneg h.pos z s

lemma WHyp.wW_eq_zero (h : WHyp H a b Hs κ hl) {s : ℝ} (hs : s < a - Hs ∨ b + Hs < s) :
    wW H a b s = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  by_contra hw
  obtain ⟨-, h1, h2⟩ := h.near hz.1.le hz.2 hw
  rcases hs with hs | hs <;> linarith

lemma int_const_indicator_Icc {c u v : ℝ} (huv : u ≤ v) :
    ∫ z, (Icc u v).indicator (fun _ => c) z = c * (v - u) := by
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le huv,
    smul_eq_mul, mul_comm]

lemma WHyp.wW_le (h : WHyp H a b Hs κ hl) (s : ℝ) : wW H a b s ≤ (1 + κ) / (1 - κ) := by
  have hκ := h.κ1
  have hκ0 := h.κ0
  by_cases hs : a - Hs ≤ s ∧ s ≤ b + Hs
  · set hh := H s with hhdef
    have h0 : 0 < hh := h.pos s
    have hden : 0 < hh * (1 - κ) := by nlinarith
    set I := Icc (s - hh * (1 + κ) / 2) (s + hh * (1 + κ) / 2)
    have hpt : ∀ z ∈ Ioc a b, wk H z s ≤ I.indicator (fun _ => (hh * (1 - κ))⁻¹) z := by
      intro z hz
      by_cases hw : wk H z s = 0
      · rw [hw]; exact Set.indicator_nonneg (fun _ _ => (inv_pos.mpr hden).le) z
      · obtain ⟨hzs, -, -⟩ := h.near hz.1.le hz.2 hw
        have hcl := h.close s hs.1 hs.2 z hz.1.le hz.2 (by linarith [h.Hs0])
        rw [abs_le] at hcl
        unfold wk at hw ⊢
        split_ifs at hw ⊢ with hc
        · have hzI : z ∈ I := by
            constructor <;> nlinarith [hc.1, hc.2, hcl.1, hcl.2]
          rw [Set.indicator_of_mem hzI]
          exact inv_anti₀ hden (by linarith [hcl.1])
        · exact absurd rfl hw
    have hIint : Integrable (I.indicator (fun _ => (hh * (1 - κ))⁻¹)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
    calc wW H a b s ≤ ∫ z in Ioc a b, I.indicator (fun _ => (hh * (1 - κ))⁻¹) z :=
          setIntegral_mono_on (h.integrableOn_wk s) hIint.integrableOn measurableSet_Ioc hpt
      _ ≤ ∫ z, I.indicator (fun _ => (hh * (1 - κ))⁻¹) z :=
          setIntegral_le_integral hIint (Filter.Eventually.of_forall fun z =>
            Set.indicator_nonneg (fun _ _ => (inv_pos.mpr hden).le) z)
      _ = (1 + κ) / (1 - κ) := by
          rw [int_const_indicator_Icc (by nlinarith)]
          field_simp
          ring
  · push_neg at hs
    have : wW H a b s = 0 := by
      by_cases h1 : a - Hs ≤ s
      · exact h.wW_eq_zero (Or.inr (lt_of_not_ge fun h2 => (not_lt.mpr h2) (hs h1)))
      · exact h.wW_eq_zero (Or.inl (lt_of_not_ge h1))
    rw [this]; apply div_nonneg <;> linarith

lemma WHyp.wW_ge (h : WHyp H a b Hs κ hl) {s : ℝ} (hs1 : a + Hs ≤ s) (hs2 : s ≤ b - Hs) :
    (1 - κ) / (1 + κ) ≤ wW H a b s := by
  have hκ := h.κ1
  have hκ0 := h.κ0
  have hHs := h.Hs0
  have hsI : a - Hs ≤ s ∧ s ≤ b + Hs := ⟨by linarith, by linarith⟩
  set hh := H s with hhdef
  have h0 : 0 < hh := h.pos s
  have hhs : hh ≤ Hs := h.le_Hs s hsI.1 hsI.2
  have hden : 0 < hh * (1 + κ) := by nlinarith
  set I := Icc (s - hh * (1 - κ) / 2) (s + hh * (1 - κ) / 2)
  have hIsub : I ⊆ Ioc a b := by
    intro z hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hpt : ∀ z ∈ Ioc a b, I.indicator (fun _ => (hh * (1 + κ))⁻¹) z ≤ wk H z s := by
    intro z hz
    by_cases hzI : z ∈ I
    · rw [Set.indicator_of_mem hzI]
      have hzs : |z - s| ≤ Hs := by
        rw [abs_le]; constructor <;> nlinarith [hzI.1, hzI.2]
      have hcl := h.close s hsI.1 hsI.2 z hz.1.le hz.2 hzs
      rw [abs_le] at hcl
      have hHz := h.pos z
      unfold wk
      rw [if_pos ⟨by nlinarith [hzI.1, hzI.2, hcl.1], by nlinarith [hzI.1, hzI.2, hcl.1]⟩]
      exact inv_anti₀ hHz (by linarith [hcl.2])
    · rw [Set.indicator_of_notMem hzI]; exact wk_nonneg h.pos z s
  have hIint : Integrable (I.indicator (fun _ => (hh * (1 + κ))⁻¹)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  calc (1 - κ) / (1 + κ) = ∫ z, I.indicator (fun _ => (hh * (1 + κ))⁻¹) z := by
        rw [int_const_indicator_Icc (by nlinarith)]
        field_simp
        ring
    _ = ∫ z in Ioc a b, I.indicator (fun _ => (hh * (1 + κ))⁻¹) z := by
        rw [← integral_indicator measurableSet_Ioc]
        congr 1; funext z
        by_cases hz : z ∈ Ioc a b
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz (hIsub h'))]
    _ ≤ wW H a b s :=
        setIntegral_mono_on hIint.integrableOn (h.integrableOn_wk s) measurableSet_Ioc hpt

/-- The pointwise defect of the weight: `|w(s) - 1_{(a,b]}(s)|` is `≤ 3κ` inside, `≤ 2` on the
boundary strips, `0` outside. -/
lemma WHyp.defect_le (h : WHyp H a b Hs κ hl) (s : ℝ) :
    |wW H a b s - (Ioc a b).indicator (fun _ => (1 : ℝ)) s| ≤
      3 * κ * (Ioc a b).indicator (fun _ => (1 : ℝ)) s +
        2 * (Icc (a - Hs) (a + Hs)).indicator (fun _ => (1 : ℝ)) s +
        2 * (Icc (b - Hs) (b + Hs)).indicator (fun _ => (1 : ℝ)) s := by
  have hκ := h.κ1
  have hκ0 := h.κ0
  have hHs := h.Hs0
  have hw0 := h.wW_nonneg s
  have hw1 := h.wW_le s
  have hq : (1 + κ) / (1 - κ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hind : ∀ (S : Set ℝ) (x : ℝ), 0 ≤ S.indicator (fun _ => (1 : ℝ)) x ∧
      S.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
    intro S x; unfold Set.indicator; split_ifs <;> norm_num
  obtain ⟨i10, i11⟩ := hind (Ioc a b) s
  obtain ⟨i20, -⟩ := hind (Icc (a - Hs) (a + Hs)) s
  obtain ⟨i30, -⟩ := hind (Icc (b - Hs) (b + Hs)) s
  by_cases hA : s ∈ Icc (a - Hs) (a + Hs)
  · rw [Set.indicator_of_mem hA]
    rw [abs_le]; constructor <;> nlinarith
  by_cases hB : s ∈ Icc (b - Hs) (b + Hs)
  · rw [Set.indicator_of_mem hB]
    rw [abs_le]; constructor <;> nlinarith
  rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]
  simp only [Set.mem_Icc, not_and_or, not_le] at hA hB
  by_cases hin : a + Hs ≤ s ∧ s ≤ b - Hs
  · have hsI : s ∈ Ioc a b := ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_mem hsI]
    have hge := h.wW_ge hin.1 hin.2
    have e1 : 1 - (1 - κ) / (1 + κ) ≤ 3 * κ := by
      have : 1 - (1 - κ) / (1 + κ) = 2 * κ / (1 + κ) := by field_simp; ring
      rw [this, div_le_iff₀ (by linarith)]; nlinarith
    have e2 : (1 + κ) / (1 - κ) - 1 ≤ 3 * κ := by
      have hne : (1 : ℝ) - κ ≠ 0 := by linarith
      have : (1 + κ) / (1 - κ) - 1 = 2 * κ / (1 - κ) := by field_simp; ring
      rw [this, div_le_iff₀ (by linarith)]; nlinarith
    rw [abs_le]; constructor <;> linarith
  · -- outside: `s < a - Hs` or `s > b + Hs`
    have hout : s < a - Hs ∨ b + Hs < s := by
      push_neg at hin
      rcases hA with hA | hA
      · left; exact hA
      · rcases hB with hB | hB
        · by_cases hsa : a + Hs ≤ s
          · exact absurd (hin hsa) (not_lt.mpr (by linarith))
          · exact absurd hA (not_lt.mpr (by linarith))
        · right; exact hB
    rw [h.wW_eq_zero hout]
    have hsI : s ∉ Ioc a b := by
      intro hsI; rcases hout with ho | ho <;> linarith [hsI.1, hsI.2]
    rw [Set.indicator_of_notMem hsI]; simp

/-- **The boundary estimate**: `|∫_a^b (B f - f)| ≤ M (3κ(b - a) + 8 H_*)`. -/
theorem abs_int_Bavg_sub_le (h : WHyp H a b Hs κ hl) {f : ℝ → ℝ} (hfm : Measurable f)
    {M : ℝ} (hM0 : 0 ≤ M) (hfM : ∀ s, a - Hs ≤ s → s ≤ b + Hs → |f s| ≤ M) :
    |∫ z in a..b, (Margin.Bavg (H z) f z - f z)| ≤ M * (3 * κ * (b - a) + 8 * Hs) := by
  have hab := h.hab
  have hHs := h.Hs0
  have hκ0 := h.κ0
  set A := a - Hs
  set B := b + Hs
  -- the kernel on the product, cut to `z ∈ (a, b]`
  set F : ℝ × ℝ → ℝ := fun p => (Ioc a b).indicator (fun z => wk H z p.2) p.1 * f p.2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (hfm.comp measurable_snd)
    have : (fun p : ℝ × ℝ => (Ioc a b).indicator (fun z => wk H z p.2) p.1) =
        (Ioc a b ×ˢ univ).indicator (Function.uncurry (wk H)) := by
      funext p
      simp only [Set.indicator, Set.mem_prod, Set.mem_univ, and_true, Function.uncurry]
    rw [this]
    exact (measurable_wk h.meas).indicator (measurableSet_Ioc.prod MeasurableSet.univ)
  have hFb : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (Ioc a b ×ˢ Icc A B).indicator (fun _ => hl⁻¹ * M) p := by
    intro p
    simp only [F, Real.norm_eq_abs]
    by_cases hz : p.1 ∈ Ioc a b
    · rw [Set.indicator_of_mem hz]
      by_cases hw : wk H p.1 p.2 = 0
      · rw [hw, zero_mul, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg (inv_pos.mpr h.hl0).le hM0) p
      · obtain ⟨-, h1, h2⟩ := h.near hz.1.le hz.2 hw
        rw [Set.indicator_of_mem (show (p.1, p.2) ∈ Ioc a b ×ˢ Icc A B from
          Set.mk_mem_prod hz ⟨h1, h2⟩), abs_mul,
          abs_of_nonneg (wk_nonneg h.pos _ _)]
        refine mul_le_mul ?_ (hfM _ h1 h2) (abs_nonneg _) (inv_pos.mpr h.hl0).le
        unfold wk; split_ifs
        · exact inv_anti₀ h.hl0 (h.low _ hz.1.le hz.2)
        · exact (inv_pos.mpr h.hl0).le
    · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (inv_pos.mpr h.hl0).le hM0) p
  have hFi : Integrable F (volume.prod volume) := by
    refine Integrable.mono' ?_ hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
    refine (integrable_indicator_iff (measurableSet_Ioc.prod measurableSet_Icc)).mpr ?_
    refine integrableOn_const ?_
    rw [Measure.prod_prod]
    simp [Real.volume_Ioc, Real.volume_Icc, ENNReal.mul_eq_top]
  -- `∫_a^b B f = ∫ w f`
  have hBint : ∫ z in a..b, Margin.Bavg (H z) f z = ∫ s, wW H a b s * f s := by
    rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
    have e1 : (Ioc a b).indicator (fun z => Margin.Bavg (H z) f z) =
        fun z => ∫ s, F (z, s) := by
      funext z
      simp only [F]
      by_cases hz : z ∈ Ioc a b
      · rw [Set.indicator_of_mem hz, Bavg_eq_int_wk h.pos]
        congr 1; funext s; rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        simp [Set.indicator_of_notMem hz]
    rw [e1, show (∫ z, ∫ s, F (z, s)) = ∫ z, ∫ s, (fun z s => F (z, s)) z s from rfl,
      integral_integral_swap (f := fun z s => F (z, s)) hFi]
    congr 1; funext s
    simp only [F]
    rw [integral_mul_const]
    congr 1
    unfold wW
    rw [← integral_indicator measurableSet_Ioc]
  have hwfi : Integrable (fun s => wW H a b s * f s) := by
    have := hFi.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [F]
    rw [integral_mul_const]
    congr 1
    unfold wW
    rw [← integral_indicator measurableSet_Ioc]
  have hfi : IntegrableOn f (Ioc a b) := by
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc]) hfm.aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs]; exact hfM s (by linarith [hs.1]) (by linarith [hs.2])
  rw [intervalIntegral.integral_sub ?_ ?_]
  rotate_left
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have : IntegrableOn (fun z => ∫ s, F (z, s)) (Ioc a b) := hFi.integral_prod_left.integrableOn
    refine this.congr_fun (fun z hz => ?_) measurableSet_Ioc
    simp only [F]
    rw [Bavg_eq_int_wk h.pos]
    congr 1; funext s; rw [Set.indicator_of_mem hz]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hfi
  rw [hBint, intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc,
    ← integral_sub hwfi ((integrable_indicator_iff measurableSet_Ioc).mpr hfi)]
  -- the dominating function
  set g : ℝ → ℝ := fun s => M * (3 * κ * (Ioc a b).indicator (fun _ => (1 : ℝ)) s +
    2 * (Icc (a - Hs) (a + Hs)).indicator (fun _ => (1 : ℝ)) s +
    2 * (Icc (b - Hs) (b + Hs)).indicator (fun _ => (1 : ℝ)) s)
  have i1 : Integrable ((Ioc a b).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have i2 : ∀ u v : ℝ, Integrable ((Icc u v).indicator (fun _ => (1 : ℝ))) := fun u v =>
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hgi : Integrable g :=
    (((i1.const_mul (3 * κ)).add ((i2 _ _).const_mul 2)).add ((i2 _ _).const_mul 2)).const_mul M
  have hpt : ∀ s, ‖wW H a b s * f s - (Ioc a b).indicator f s‖ ≤ g s := by
    intro s
    rw [Real.norm_eq_abs]
    have e : wW H a b s * f s - (Ioc a b).indicator f s =
        (wW H a b s - (Ioc a b).indicator (fun _ => (1 : ℝ)) s) * f s := by
      by_cases hs : s ∈ Ioc a b
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]; ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]; ring
    rw [e, abs_mul]
    by_cases hsr : A ≤ s ∧ s ≤ B
    · have hf := hfM s hsr.1 hsr.2
      have hd := h.defect_le s
      have hd0 := abs_nonneg (wW H a b s - (Ioc a b).indicator (fun _ => (1 : ℝ)) s)
      calc |wW H a b s - (Ioc a b).indicator (fun _ => (1 : ℝ)) s| * |f s|
          ≤ (3 * κ * (Ioc a b).indicator (fun _ => (1 : ℝ)) s +
              2 * (Icc (a - Hs) (a + Hs)).indicator (fun _ => (1 : ℝ)) s +
              2 * (Icc (b - Hs) (b + Hs)).indicator (fun _ => (1 : ℝ)) s) * M :=
            mul_le_mul hd hf (abs_nonneg _) (by linarith)
        _ = g s := by simp only [g]; ring
    · have hout : s < a - Hs ∨ b + Hs < s := by
        push_neg at hsr
        by_cases h1 : A ≤ s
        · right; exact hsr h1
        · left; exact lt_of_not_ge h1
      have hsI : s ∉ Ioc a b := by
        intro hsI; rcases hout with ho | ho <;> linarith [hsI.1, hsI.2]
      rw [h.wW_eq_zero hout, Set.indicator_of_notMem hsI, sub_zero, abs_zero, zero_mul]
      have : ∀ (S : Set ℝ) (x : ℝ), 0 ≤ S.indicator (fun _ => (1 : ℝ)) x := fun S x =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have j1 := this (Ioc a b) s
      have j2 := this (Icc (a - Hs) (a + Hs)) s
      have j3 := this (Icc (b - Hs) (b + Hs)) s
      simp only [g]; positivity
  calc |∫ s, (wW H a b s * f s - (Ioc a b).indicator f s)|
      ≤ ∫ s, g s := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)
    _ = M * (3 * κ * (b - a) + 8 * Hs) := by
        have ia : ∫ s, (Ioc a b).indicator (fun _ => (1 : ℝ)) s = b - a := by
          rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le hab,
            smul_eq_mul, mul_one]
        have ib : ∀ u v : ℝ, u ≤ v → ∫ s, (Icc u v).indicator (fun _ => (1 : ℝ)) s = v - u :=
          fun u v huv => by rw [int_const_indicator_Icc huv, one_mul]
        have e : ∫ s, g s = M * (3 * κ * ∫ s, (Ioc a b).indicator (fun _ => (1 : ℝ)) s) +
            M * (2 * ∫ s, (Icc (a - Hs) (a + Hs)).indicator (fun _ => (1 : ℝ)) s) +
            M * (2 * ∫ s, (Icc (b - Hs) (b + Hs)).indicator (fun _ => (1 : ℝ)) s) := by
          simp only [g, mul_add]
          rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
          · exact (i1.const_mul _).const_mul _
          · exact ((i2 _ _).const_mul _).const_mul _
          · exact ((i1.const_mul _).const_mul _).add (((i2 _ _).const_mul _).const_mul _)
          · exact ((i2 _ _).const_mul _).const_mul _
        rw [e, ia, ib _ _ (by linarith), ib _ _ (by linarith)]
        ring

/-- **The fields `hbd`, `hBnd0`, `hBnd`** of `KR.RML6.G1BInputs`: with
`Bnd := M(3κ(b - a) + 8H_*)` on `J = [a, b]`, provided `M(3κ(b-a) + 8H_*) ≤ 40√y`. -/
theorem hbd_of (h : WHyp H a b Hs κ hl) {f : ℝ → ℝ} (hfm : Measurable f)
    {M y : ℝ} (hM0 : 0 ≤ M) (hfM : ∀ s, a - Hs ≤ s → s ≤ b + Hs → |f s| ≤ M)
    (hsize : M * (3 * κ * (b - a) + 8 * Hs) ≤ 40 * √y) :
    (∫ z in a..b, (Margin.Bavg (H z) f z - f z)) ≤ M * (3 * κ * (b - a) + 8 * Hs) ∧
      0 ≤ M * (3 * κ * (b - a) + 8 * Hs) ∧ M * (3 * κ * (b - a) + 8 * Hs) ≤ 40 * √y := by
  have hk := abs_int_Bavg_sub_le h hfm hM0 hfM
  refine ⟨(le_abs_self _).trans hk, (abs_nonneg _).trans hk, hsize⟩

end

end KR.RML8E

end
