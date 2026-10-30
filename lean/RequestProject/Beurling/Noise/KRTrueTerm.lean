module

public import RequestProject.Beurling.Noise.KRTrueProp

/-!
# Proposition 5.18: the terminal levels (step (iii) of the proof)

The `X₀`-near sources sit at terminal levels and have no children (Lemma 5.12); they add, at
the level `n = dw`, at most `TV(C_d)` for each `X₀`-near step `d → n`, i.e.
`|x/d - w X₀⁻| ≤ 1.02 H(x/d)`. Grouping by the parents gives the weight

  `η_{X₀}(v) = ∑_{w ∈ 𝒩, |v - w X₀⁻| ≤ 1.02 H(v)} 1/w`  (`etaX0`),

and `prop_5_18_terminal` proves the third bound of Proposition 5.18,

  `W^op_x(u) ≤ 5.1 C_N log(2u)/log x`  (`u ∈ {X₀/2, X₀}`, i.e. `1.52 log(2X₀) ≤ 1.53 log(2u)`),

from the named input `EtaX0Sum` (the bullets of step (iii): `η_{X₀} ≤ s_v` on `[v, 2v)` and
`∑_v log(2v) s_v ≤ 1.52 log(2X₀)`; the paper proves them from the lag bound of Corollary 3.8,
the target (6) and Lemma 6.26 for the absorbed set, for `v > X₀²/2`).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- The cofactors `w ≥ 2` with `v/w ≥ X₀⁻/2`. -/
noncomputable def CofH (P : BeurlingSystem) (X0m v : ℝ) : Finset ℕ :=
  ((P.elems (2 * v / X0m)).image iota).filter (2 ≤ ·)

/-- `η_{X₀}(v) = ∑_{w: |v - w X₀⁻| ≤ 1.02 H(v)} 1/w`. -/
noncomputable def etaX0 (P : BeurlingSystem) (H : ℝ → ℝ) (X0m v : ℝ) : ℝ :=
  open scoped Classical in
  ∑ m ∈ (CofH P X0m v).filter (fun m => |v - Vl P m * X0m| ≤ 1.02 * H v), 1 / Vl P m

/-- **Step (iii), bullets** (Proposition 5.18, proof): `η_{X₀} ≤ s_v` on `[v, 2v)`, `s_v ≥ 0`,
and `∑_v log(2v) s_v ≤ 1.52 log(2X₀)`. -/
def EtaX0Sum (P : BeurlingSystem) (H : ℝ → ℝ) (X0m X0 : ℝ) (Sc : Finset ℝ) (s : ℝ → ℝ) :
    Prop :=
  (∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → etaX0 P H X0m y ≤ s v) ∧
    ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1.52 * Real.log (2 * X0)

/-- **Step (iii), localized at a start `x`**: the bound `η_{X₀} ≤ s_v` on `[v, 2v)` is asked only
at the positions `y ≤ x` (the consumers evaluate `η_{X₀}` at the positions `x/n ≤ x`). -/
def EtaX0SumLoc (P : BeurlingSystem) (H : ℝ → ℝ) (X0m X0 : ℝ) (Sc : Finset ℝ) (s : ℝ → ℝ)
    (x : ℝ) : Prop :=
  (∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → y ≤ x → etaX0 P H X0m y ≤ s v) ∧
    ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1.52 * Real.log (2 * X0)

lemma EtaX0Sum.toLoc {P : BeurlingSystem} {H : ℝ → ℝ} {X0m X0 : ℝ} {Sc : Finset ℝ}
    {s : ℝ → ℝ} (h : EtaX0Sum P H X0m X0 Sc s) (x : ℝ) : EtaX0SumLoc P H X0m X0 Sc s x :=
  ⟨fun v hv => ⟨(h.1 v hv).1, fun y h1 h2 _ => (h.1 v hv).2 y h1 h2⟩, h.2⟩

lemma toReal_lintegral_le3 {f g k : ℝ → ℝ} {ι : Type*} (s : Finset ι) {h : ι → ℝ → ℝ}
    (hg : Integrable g) (hgm : Measurable g) (hh : ∀ i ∈ s, Integrable (h i))
    (hhm : ∀ i ∈ s, Measurable (h i)) (hk : Integrable k) (hkm : Measurable k)
    (hf : ∀ t, ‖f t‖ₑ ≤ ‖g t‖ₑ + ∑ i ∈ s, ‖h i t‖ₑ + ‖k t‖ₑ) :
    (∫⁻ t, ‖f t‖ₑ).toReal ≤ (∫⁻ t, ‖g t‖ₑ).toReal + ∑ i ∈ s, (∫⁻ t, ‖h i t‖ₑ).toReal +
      (∫⁻ t, ‖k t‖ₑ).toReal := by
  classical
  have h1 := toReal_lintegral_le (f := f) (g := g) (s := insert none (s.image some))
    (h := fun o => match o with | none => k | some i => h i) hg hgm
    (by
      intro o ho
      rcases Finset.mem_insert.mp ho with rfl | ho
      · exact hk
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho; exact hh i hi)
    (by
      intro o ho
      rcases Finset.mem_insert.mp ho with rfl | ho
      · exact hkm
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho; exact hhm i hi)
    (fun t => by
      rw [Finset.sum_insert (by simp),
        Finset.sum_image (fun a _ b _ h => Option.some_injective _ h)]
      calc ‖f t‖ₑ ≤ ‖g t‖ₑ + ∑ i ∈ s, ‖h i t‖ₑ + ‖k t‖ₑ := hf t
        _ = ‖g t‖ₑ + (‖k t‖ₑ + ∑ i ∈ s, ‖h i t‖ₑ) := by ring)
  rw [Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => Option.some_injective _ h)]
    at h1
  linarith

/-- `TV(C_n) ≤ a(n) + TV(S^{X₀}_n)` at every level. -/
theorem TVt_le_full {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (n : ℕ) :
    TVt P H tw X0m x n ≤ aLev P H tw X0m x n +
      (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hH := hP.reg
  have h0 : 0 ≤ (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal := ENNReal.toReal_nonneg
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : TVt P H tw X0m x n ≤ aLev P H tw X0m x n := by
      unfold TVt aLev TVn
      interval_cases n
      · rw [if_neg (by norm_num), if_neg (by norm_num), gK_le_one _ _ _ (by norm_num),
          gK_le_one _ _ _ (by norm_num)]
        simp only [enorm_zero, lintegral_zero, ENNReal.toReal_zero, zero_add]
        exact Finset.sum_nonneg fun _ _ => tauPart_nonneg _ _
      · rw [if_pos rfl, if_pos rfl]
        linarith [Finset.sum_nonneg (s := (Nat.divisors 1).filter (2 ≤ ·))
          (fun n' _ => tauPart_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x) n' 1)]
    linarith
  unfold TVt aLev TVn
  rw [if_neg (by omega), if_neg (by omega)]
  unfold tauPart
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
  refine toReal_lintegral_le3 _ (integrable_gK hH (constF_ok hκ) n).1
    (integrable_gK hH (constF_ok hκ) n).2
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 n).1)
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 n).2) (integrable_SX0 hH n).1 (integrable_SX0 hH n).2
    fun t => ?_
  have e := Etil_split (val := P.labelVal) (x := x) (tw := tw) hP hX0 hval2 hn t
  have e2 : gK P.labelVal x H (phiT tw X0m) n t =
      gK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) n t +
        Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) n t := by
    unfold Etil; ring
  rw [e2, e, ← add_assoc]
  exact (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
    (add_le_add le_rfl (enorm_sum_le _ _))) le_rfl)

/-- Below `X₀⁻/2` the sources vanish. -/
lemma srcStep_eq_zero_verylow {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    {d n : ℕ} (hd : d ∈ n.properDivisors) (hpos : ¬ X0m / 2 ≤ posn P.labelVal x n) (t : ℝ) :
    srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t = 0 := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  by_cases h1 : d = 1
  · subst h1; exact srcStep_one hval n t
  have hk : kapN tw X0m P.labelVal x d n = 0 := by
    unfold kapN; rw [nomFilter_eq_trueFilter hval]
    unfold trueFilter
    rw [if_neg (fun h => hpos (by linarith [h.2, hP.X0m_pos]))]
  unfold srcStep
  rw [if_neg h1]
  unfold Qd
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)]
  simp only [Pi.zero_apply]
  by_cases hg : gK P.labelVal x H (phiT tw X0m) d s = 0
  · rw [hg]; ring
  obtain ⟨hposd, hsd⟩ := hsupp d s hg
  rw [hk]
  by_cases hφ : trueFilter tw X0m d n (s / LemmaM.valN P.labelVal (n / d)) = 0
  · rw [show phiT tw X0m d n (s / LemmaM.valN P.labelVal (n / d)) = 0 from hφ]; ring
  · exact absurd (pos_of_centre hP hval2 hd hposd hsd (trueFilter_ne_zero hφ)) hpos

/-- The parents of the `X₀`-sources at `n`. -/
noncomputable def D0 (P : BeurlingSystem) (H : ℝ → ℝ) (X0m x X0 : ℝ) (n : ℕ) : Finset ℕ :=
  open scoped Classical in
  n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n ∧
    ¬ Terminal P.labelVal x H X0m X0 d ∧ X0m / 2 ≤ posn P.labelVal x n)

/-- `TV(S^{X₀}_n) ≤ ∑_{d → n X₀-near} a(d)` (the parents are non-terminal). -/
theorem SX0_le {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (n : ℕ) :
    (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal ≤
      ∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hH := hP.reg
  have hterm : ∀ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
      ∫⁻ t, ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t‖ₑ ≤
        if d ∈ D0 P H X0m x X0 n then ENNReal.ofReal (aLev P H tw X0m x d) else 0 := by
    intro d hd
    obtain ⟨hdm, hXd⟩ := Finset.mem_filter.mp hd
    by_cases h1 : d = 1
    · subst h1
      simp only [srcStep_one hval, enorm_zero, lintegral_zero]; exact zero_le
    by_cases hD : d ∈ D0 P H X0m x X0 n
    · rw [if_pos hD]
      have hTd : ¬ Terminal P.labelVal x H X0m X0 d := by
        unfold D0 at hD; exact (Finset.mem_filter.mp hD).2.2.1
      refine (lintegral_srcStep_le hH h1).trans ?_
      have hfin := (integrable_gKT (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m)
        hH d).1.2.ne
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      have := TVt_le_aLev (tw := tw) hP hX0 hp2 hTd
      unfold TVt at this; rwa [if_neg h1] at this
    · rw [if_neg hD]
      unfold D0 at hD
      simp only [Finset.mem_filter, not_and] at hD
      have hz : ∀ t,
          srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t = 0 := by
        intro t
        by_cases hpos : X0m / 2 ≤ posn P.labelVal x n
        · by_cases hT : Terminal P.labelVal x H X0m X0 d
          · exact srcStep_terminal hP hX0 hp2 hdm h1 hT t
          · exact absurd hpos (hD hdm hXd hT)
        · exact srcStep_eq_zero_verylow hP hp2 hdm hpos t
      simp [hz]
  have hle : ∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ ≤
      ∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
        if d ∈ D0 P H X0m x X0 n then ENNReal.ofReal (aLev P H tw X0m x d) else 0 := by
    calc ∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ
        ≤ ∫⁻ t, ∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
            ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t‖ₑ := by
          refine lintegral_mono fun t => ?_
          unfold SX0 SsrcP
          rw [enorm_neg]
          convert! enorm_sum_le _ _
      _ = ∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
            ∫⁻ t, ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t‖ₑ :=
          lintegral_finset_sum _ fun d _ => (integrable_srcStep hH d n).2.enorm
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsum : (∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
      if d ∈ D0 P H X0m x X0 n then ENNReal.ofReal (aLev P H tw X0m x d) else 0) ≤
      ENNReal.ofReal (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun d _ => aLev_nonneg d, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd; exact (Finset.mem_filter.mp hd).2
    · intro _ _ _; exact zero_le
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg fun d _ => aLev_nonneg d)
    (hle.trans hsum)

/-- **Regrouping the `X₀`-sources by their parents**:
`∑_{x/n ∈ [u,2u)} (∑_{d → n X₀-near} a(d))/n ≤ ∑_d (a(d)/d) η_{X₀}(x/d)`. -/
theorem regroupX0 {X0 : ℝ} (hp2 : ∀ j, 2 ≤ P.p j) (hXm : 0 < X0m) (u : ℝ) :
    ∑ n ∈ NW P x u, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n ≤
      ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  set F : ℕ → ℕ → ℝ := fun n d => aLev P H tw X0m x d / Vl P n
  have e1 : ∀ n ∈ NW P x u, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n =
      ∑ d ∈ D0 P H X0m x X0 n, F n d := fun n _ => by rw [Finset.sum_div]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := NAll P x X0m)
    (s' := fun d => (NW P x u).filter (fun n => d ∈ D0 P H X0m x X0 n))]
  · refine Finset.sum_le_sum fun d hd => ?_
    have hVd := KR.valN_labelVal_pos P d
    set T := (CofH P X0m (posn P.labelVal x d)).filter
      (fun m => |posn P.labelVal x d - Vl P m * X0m| ≤ 1.02 * H (posn P.labelVal x d))
    have hS : ∀ n ∈ (NW P x u).filter (fun n => d ∈ D0 P H X0m x X0 n),
        F n d = aLev P H tw X0m x d / Vl P d * (1 / Vl P (n / d)) ∧ n / d ∈ T ∧ d ∣ n := by
      intro n hn
      obtain ⟨-, hdD⟩ := Finset.mem_filter.mp hn
      unfold D0 at hdD
      obtain ⟨hdm, hXd, -, hpos⟩ := Finset.mem_filter.mp hdD
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hm2 := two_le_div_of_mem hdm
      have hVm := KR.valN_labelVal_pos P (n / d)
      have hpd : posn P.labelVal x d = posn P.labelVal x n * Vl P (n / d) := posn_mul hval hdn hn0
      have hVV : Vl P n = Vl P d * Vl P (n / d) := valN_div_mul hval hdn hn0
      refine ⟨?_, ?_, hdn⟩
      · simp only [F]; rw [hVV]; field_simp
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hm2⟩, ?_⟩
        · apply KR.mem_image_iota P (by omega)
          rw [le_div_iff₀ hXm, hpd]
          nlinarith
        · unfold X0Near at hXd
          rw [hpd]
          have e : posn P.labelVal x n * Vl P (n / d) - Vl P (n / d) * X0m =
              (posn P.labelVal x n - X0m) * Vl P (n / d) := by ring
          rw [e, abs_mul, abs_of_pos hVm, ← hpd]
          rw [le_div_iff₀ hVm] at hXd
          exact hXd
    calc ∑ n ∈ (NW P x u).filter (fun n => d ∈ D0 P H X0m x X0 n), F n d
        = ∑ n ∈ (NW P x u).filter (fun n => d ∈ D0 P H X0m x X0 n),
            aLev P H tw X0m x d / Vl P d * (1 / Vl P (n / d)) :=
          Finset.sum_congr rfl fun n hn => (hS n hn).1
      _ = ∑ m ∈ ((NW P x u).filter (fun n => d ∈ D0 P H X0m x X0 n)).image (· / d),
            aLev P H tw X0m x d / Vl P d * (1 / Vl P m) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only at hab
          have ha' := (hS a ha).2.2
          have hb' := (hS b hb).2.2
          rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
      _ ≤ ∑ m ∈ T, aLev P H tw X0m x d / Vl P d * (1 / Vl P m) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
            exact (hS n hn).2.1
          · intro m _ _
            exact mul_nonneg (div_nonneg (aLev_nonneg d) hVd.le)
              (one_div_nonneg.mpr (KR.valN_labelVal_pos P m).le)
      _ = aLev P H tw X0m x d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
          rw [← Finset.mul_sum]; rfl
  · intro n d
    constructor
    · rintro ⟨hn, hd⟩
      refine ⟨Finset.mem_filter.mpr ⟨hn, hd⟩, ?_⟩
      unfold D0 at hd
      obtain ⟨hdm, -, -, hpos⟩ := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
      apply mem_NAll_of_posn hd0 hXm
      rw [posn_mul hval hdn hn0]
      have hw := two_le_valN hval2 (two_le_div_of_mem hdm)
      nlinarith
    · rintro ⟨h, -⟩
      exact Finset.mem_filter.mp h

/-- Covering by the scales, for a general weight `η` with scale bounds `s`. -/
theorem cover_gen {Sc : Finset ℝ} {s η : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hs : ∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → η y ≤ s v) :
    ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * η (posn P.labelVal x d) ≤
      ∑ v ∈ Sc, Aw P H tw X0m x v * s v := by
  classical
  set G : ℕ → ℝ → ℝ := fun d v => aLev P H tw X0m x d / Vl P d * s v
  have hstep : ∀ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * η (posn P.labelVal x d) ≤
      ∑ v ∈ Sc.filter (fun v => d ∈ NW P x v), G d v := by
    intro d hd
    obtain ⟨v, hv, hdv⟩ := hcov d hd
    have hmem : v ∈ Sc.filter (fun v => d ∈ NW P x v) := Finset.mem_filter.mpr ⟨hv, hdv⟩
    have ha := div_nonneg (aLev_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x) d)
      (KR.valN_labelVal_pos P d).le
    calc aLev P H tw X0m x d / Vl P d * η (posn P.labelVal x d) ≤ G d v := by
          simp only [G]
          apply mul_le_mul_of_nonneg_left _ ha
          obtain ⟨-, hy⟩ := hs v hv
          obtain ⟨-, h1, h2⟩ := (mem_NW P (hSc v hv)).mp hdv
          exact hy _ h1 h2
      _ ≤ ∑ v ∈ Sc.filter (fun v => d ∈ NW P x v), G d v :=
          Finset.single_le_sum (f := fun v => G d v)
            (fun w hw => mul_nonneg ha (hs w (Finset.mem_filter.mp hw).1).1) hmem
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_comm' (t' := Sc) (s' := fun v => (NAll P x X0m).filter (fun d => d ∈ NW P x v))]
  · refine Finset.sum_le_sum fun v hv => ?_
    unfold Aw
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd; exact (Finset.mem_filter.mp hd).2
    · intro d _ _
      exact mul_nonneg (div_nonneg (aLev_nonneg d) (KR.valN_labelVal_pos P d).le) (hs v hv).1
  · intro d v
    simp only [Finset.mem_filter]
    tauto

lemma posn_le_self {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : posn P.labelVal x d ≤ x := by
  unfold posn
  exact div_le_self hx (LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r))

/-- `cover_gen` with the scale bounds asked only at the positions `y ≤ x`. -/
theorem cover_gen_loc {Sc : Finset ℝ} {s η : ℝ → ℝ} (hx : 0 ≤ x)
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hs : ∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → y ≤ x → η y ≤ s v) :
    ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * η (posn P.labelVal x d) ≤
      ∑ v ∈ Sc, Aw P H tw X0m x v * s v := by
  classical
  have h := cover_gen (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x)
    (η := fun y => if y ≤ x then η y else 0) hcov hSc (fun v hv => ⟨(hs v hv).1,
      fun y h1 h2 => by
        show (if y ≤ x then η y else 0) ≤ s v
        by_cases hyx : y ≤ x
        · rw [if_pos hyx]; exact (hs v hv).2 y h1 h2 hyx
        · rw [if_neg hyx]; exact (hs v hv).1⟩)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun d _ => ?_
  show _ = _ * (if posn P.labelVal x d ≤ x then η (posn P.labelVal x d) else 0)
  rw [if_pos (posn_le_self hx d)]

/-- **Proposition 5.18, the third bound** (terminal levels, step (iii)): with the inputs of
`prop_5_18` and `EtaX0Sum`, for every scale `u` with `1.52 log(2X₀) ≤ 1.53 log(2u)` (the paper's
`u ∈ {X₀/2, X₀}`), `W^op_x(u) ≤ 5.1 C_N log(2u)/log x`. -/
theorem prop_5_18_terminal {X0 ε θ lam0 CN : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hXm1 : 1 < X0m) (hCN : 0 ≤ CN)
    {Sc : Finset ℝ} {s s0 : ℝ → ℝ} (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hSc : ∀ v ∈ Sc, 1 / 2 ≤ v) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hNom : NomWeights P H tw X0m x Sc CN) (hTr : TransferBound P H tw X0m x Sc lam0 CN)
    (hX0s : EtaX0Sum P H X0m X0 Sc s0) {u : ℝ} (hu : u ∈ Sc)
    (hlog : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u)) :
    Wop P H tw X0m x u ≤ 5.1 * CN * Real.log (2 * u) / Real.log x := by
  classical
  have hXm : 0 < X0m := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc v hv]
  have hA := Aw_le hP hX0 hp2 ht hlam hx hXm1 hCN hcov hSc hEta hE hNom hTr
  have hLu : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith [hSc u hu])
  have h1 : Wop P H tw X0m x u ≤ Aw P H tw X0m x u + ∑ n ∈ NW P x u,
      (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n := by
    unfold Wop Aw
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P n).le
    exact (TVt_le_full hP hX0 hp2 n).trans (add_le_add le_rfl (SX0_le hP hX0 hp2 n))
  have h2 := (regroupX0 (tw := tw) (X0 := X0) hp2 hXm u).trans
    (cover_gen (tw := tw) hcov hSc0 hX0s.1)
  have h3 : ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v ≤
      2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) := by
    calc ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v
        ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * s0 v) :=
          Finset.sum_le_sum fun v hv => by
            have := mul_le_mul_of_nonneg_right (hA v hv) (hX0s.1 v hv).1
            calc Aw P H tw X0m x v * s0 v ≤ 2 * CN * Real.log (2 * v) / Real.log x * s0 v := this
              _ = _ := by ring
      _ = 2 * CN / Real.log x * ∑ v ∈ Sc, Real.log (2 * v) * s0 v := by rw [Finset.mul_sum]
      _ ≤ 2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) :=
          mul_le_mul_of_nonneg_left hX0s.2 (by positivity)
  have h4 := hA u hu
  have h5 : 2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) ≤
      2 * CN / Real.log x * (1.53 * Real.log (2 * u)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have e : 5.1 * CN * Real.log (2 * u) / Real.log x =
      2 * CN * Real.log (2 * u) / Real.log x + 2 * CN / Real.log x * (1.53 * Real.log (2 * u)) +
        0.04 * CN * Real.log (2 * u) / Real.log x := by ring
  have h6 : 0 ≤ 0.04 * CN * Real.log (2 * u) / Real.log x := by positivity
  linarith

/-- **`NomWeights` from Corollary 5.17(b)**: at scales `u ∈ [X₀⁻/2, x]` with
`log X₀ ≤ log(2u)`, given Corollary 5.9 at the start `x` and the `H_ord` sums with
`1 + ½λ₀A₀ ≤ 2.04`, `½λ₀A₁ ≤ 4.71`, the weights hold with `C_N = C_S(2.04 + 4.71/log X₀)`. -/
theorem nomWeights_of {ε θ lam0 CS A0 A1 X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hx : X0m ≤ x) (hx1 : 1 < x) (hCS : 0 ≤ CS) (hS : SaiasAt P tw X0m x CS)
    (hA : HordSums P ε A0 A1) (hX0 : 0 < Real.log X0) (h0 : 1 + 1 / 2 * lam0 * A0 ≤ 2.04)
    (h1 : 1 / 2 * lam0 * A1 ≤ 4.71) {Sc : Finset ℝ}
    (hSc : ∀ u ∈ Sc, X0m / 2 ≤ u ∧ u ≤ x ∧ 1 / 2 ≤ u ∧ Real.log X0 ≤ Real.log (2 * u)) :
    NomWeights P H tw X0m x Sc (CS * (2.04 + 4.71 / Real.log X0)) := by
  intro u hu
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hSc u hu
  have hb := cor_5_17_b (H := H) hP hp2 ht hlam hx hx1 hu1 hu2 hCS hS hA hu3
  exact cor_5_17_b_CN hCS hx1 hX0 hu4 h0 h1 hb

end KR

end
