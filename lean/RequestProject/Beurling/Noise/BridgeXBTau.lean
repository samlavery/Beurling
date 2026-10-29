module

public import RequestProject.Beurling.Noise.BridgeXB
public import RequestProject.Beurling.Noise.BridgeNear

/-!
# Lemma 5.27, Step 3: the `τ`-part, and the lemma

`xbTau_le` : under (HBS) and the inputs of Proposition 5.18,

  `𝒯(x) ≤ 4.3 C_N E_θ/log x`,

the paper's bound: the transferred `τ`-sources give `≤ 2.04 · 2 C_N E_θ/log x` (as in
`brNearPart`), and the part of `S^{X₀}_n` coming from `Ẽ_d` gives
`∑_d (TV(Ẽ_d)/d) η_{X₀}(x/d) ≤ (∑_v sup η_{X₀}) · 2.04 · 2 C_N E_θ/((log X₀⁻ + 1) log x)`,
which is negligible (`η ≤ θ/(log X₀⁻ + 1)` pointwise, `etaG_one_le`). Here `TV(Ẽ_d) ≤
∑_{n' ∣ d} TV(𝒯^nom_{n'→d} S^τ_{n'})` for a non-terminal `d` (`TVE_le`).

`KR.lemma_5_27` : **Lemma 5.27** (eq. (xb)):
`|R_res 1_{[X₀,∞)}(x) - ρ^sh_1(x)| ≤ 𝔅(x) + 4.3 C_N E_θ/log x`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- `TV(Ẽ_d) ≤ ∑_{n' ∣ d} TV(𝒯^nom_{n'→d} S^τ_{n'})` for a non-terminal `d ≥ 2`. -/
lemma TVE_le {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) {d : ℕ} (hd : 2 ≤ d) (hT : ¬ Terminal P.labelVal x H X0m X0 d) :
    TVE P H tw X0m x d ≤ ∑ n' ∈ d.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' d := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hH := hP.reg
  unfold TVE tauPart
  have h0 : (∫⁻ t, ‖(fun _ : ℝ => (0 : ℝ)) t‖ₑ).toReal = 0 := by simp
  refine (toReal_lintegral_le (g := fun _ => (0 : ℝ)) _ (integrable_zero _ _ _) measurable_const
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 d).1)
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 d).2) fun t => ?_).trans (by rw [h0, zero_add])
  have e := Etil_split (val := P.labelVal) (x := x) (tw := tw) hP hX0e hval2 hd t
  rw [SX0_eq_zero hP hX0e hval2 hT t, add_zero] at e
  rw [e, enorm_zero, zero_add]
  exact enorm_sum_le _ _

/-- `η(y) ≤ θ(y)/(log X₀⁻ + 1)`: every `τ`-near `w` has `y/w ≥ X₀⁻`. -/
lemma etaG_one_le (hXm1 : 1 < X0m) (y : ℝ) :
    etaG P H tw X0m (fun _ => 1) y ≤
      etaG P H tw X0m (fun y => Real.log y + 1) y / (Real.log X0m + 1) := by
  classical
  have hL : 0 < Real.log X0m + 1 := by have := Real.log_pos hXm1; linarith
  unfold etaG
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨-, -, hX⟩ := (Finset.mem_filter.mp hm)
  have hV := KR.valN_labelVal_pos P m
  have hlog : Real.log X0m ≤ Real.log (y / Vl P m) :=
    Real.log_le_log (by linarith) hX
  rw [div_div, le_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, one_mul, mul_div_cancel_left₀ _ hV.ne']
  show Real.log X0m + 1 ≤ Real.log (y / Vl P m) + 1
  linarith

/-- Regrouping the `𝔹₁` steps by their parents, with any weight `f ≥ 0`. -/
theorem regroupB1 {X0 : ℝ} (hp2 : ∀ j, 2 ≤ P.p j) (hXm : 0 < X0m) (f : ℕ → ℝ)
    (hf : ∀ d, 0 ≤ f d) :
    ∑ n ∈ levels P X0m x, (∑ d ∈ B1set P H X0m x X0 n, f d) / Vl P n ≤
      ∑ d ∈ NAll P x X0m, f d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  set T := levels P X0m x
  set F : ℕ → ℕ → ℝ := fun n d => f d / Vl P n
  have e1 : ∀ n ∈ T, (∑ d ∈ B1set P H X0m x X0 n, f d) / Vl P n =
      ∑ d ∈ B1set P H X0m x X0 n, F n d := fun n _ => by rw [Finset.sum_div]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := NAll P x X0m)
    (s' := fun d => T.filter (fun n => d ∈ B1set P H X0m x X0 n))]
  · refine Finset.sum_le_sum fun d hd => ?_
    have hVd := KR.valN_labelVal_pos P d
    set T' := (CofH P X0m (posn P.labelVal x d)).filter
      (fun m => |posn P.labelVal x d - Vl P m * X0m| ≤ 1.02 * H (posn P.labelVal x d))
    have hS : ∀ n ∈ T.filter (fun n => d ∈ B1set P H X0m x X0 n),
        F n d = f d / Vl P d * (1 / Vl P (n / d)) ∧ n / d ∈ T' ∧ d ∣ n := by
      intro n hn
      obtain ⟨hnT, hdD⟩ := Finset.mem_filter.mp hn
      obtain ⟨hdm, -, hXd, -⟩ := Finset.mem_filter.mp hdD
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hm2 := two_le_div_of_mem hdm
      have hVm := KR.valN_labelVal_pos P (n / d)
      have hpd : posn P.labelVal x d = posn P.labelVal x n * Vl P (n / d) := posn_mul hval hdn hn0
      have hVV : Vl P n = Vl P d * Vl P (n / d) := valN_div_mul hval hdn hn0
      have hpos : X0m / 2 ≤ posn P.labelVal x n :=
        posn_ge_of_mem_NAll (Finset.mem_filter.mp hnT).1 (by linarith)
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
    calc ∑ n ∈ T.filter (fun n => d ∈ B1set P H X0m x X0 n), F n d
        = ∑ n ∈ T.filter (fun n => d ∈ B1set P H X0m x X0 n),
            f d / Vl P d * (1 / Vl P (n / d)) :=
          Finset.sum_congr rfl fun n hn => (hS n hn).1
      _ = ∑ m ∈ (T.filter (fun n => d ∈ B1set P H X0m x X0 n)).image (· / d),
            f d / Vl P d * (1 / Vl P m) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only at hab
          have ha' := (hS a ha).2.2
          have hb' := (hS b hb).2.2
          rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
      _ ≤ ∑ m ∈ T', f d / Vl P d * (1 / Vl P m) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
            exact (hS n hn).2.1
          · intro m _ _
            exact mul_nonneg (div_nonneg (hf d) hVd.le)
              (one_div_nonneg.mpr (KR.valN_labelVal_pos P m).le)
      _ = f d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
          rw [← Finset.mul_sum]; rfl
  · intro n d
    constructor
    · rintro ⟨hn, hd⟩
      refine ⟨Finset.mem_filter.mpr ⟨hn, hd⟩, ?_⟩
      obtain ⟨hdm, -, -, -⟩ := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
      have hpos : X0m / 2 ≤ posn P.labelVal x n :=
        posn_ge_of_mem_NAll (Finset.mem_filter.mp hn).1 (by linarith)
      apply mem_NAll_of_posn hd0 hXm
      rw [posn_mul hval hdn hn0]
      have hw := two_le_valN hval2 (two_le_div_of_mem hdm)
      nlinarith
    · rintro ⟨h, -⟩
      exact Finset.mem_filter.mp h

/-- The cover by scales with any weight `f ≥ 0`. -/
theorem coverF {Sc : Finset ℝ} {s η : ℝ → ℝ} (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d)
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hs : ∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → η y ≤ s v) :
    ∑ d ∈ NAll P x X0m, f d / Vl P d * η (posn P.labelVal x d) ≤
      ∑ v ∈ Sc, (∑ d ∈ NW P x v, f d / Vl P d) * s v := by
  classical
  set G : ℕ → ℝ → ℝ := fun d v => f d / Vl P d * s v
  have hstep : ∀ d ∈ NAll P x X0m, f d / Vl P d * η (posn P.labelVal x d) ≤
      ∑ v ∈ Sc.filter (fun v => d ∈ NW P x v), G d v := by
    intro d hd
    obtain ⟨v, hv, hdv⟩ := hcov d hd
    have hmem : v ∈ Sc.filter (fun v => d ∈ NW P x v) := Finset.mem_filter.mpr ⟨hv, hdv⟩
    have ha := div_nonneg (hf d) (KR.valN_labelVal_pos P d).le
    calc f d / Vl P d * η (posn P.labelVal x d) ≤ G d v := by
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
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd; exact (Finset.mem_filter.mp hd).2
    · intro d _ _
      exact mul_nonneg (div_nonneg (hf d) (KR.valN_labelVal_pos P d).le) (hs v hv).1
  · intro d v
    simp only [Finset.mem_filter]
    tauto

/-- **Lemma 5.27, Step 3**: `𝒯(x) ≤ 4.3 C_N E_θ/log x`, with `C_N = C_S(2.04 + 4.71/log X₀)`,
`E_θ = ∑_v log(2v) θ_v` (Lemma 5.20 block bounds `ThetaBlk`), the `η_{X₀}` block bounds `s⁰`
with `∑_v s⁰_v ≤ 1.52` (step (iii) of the proof of Proposition 5.18), and the inputs of
Proposition 5.18. -/
theorem xbTau_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 th : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0b : ∀ v ∈ Sc, 0 ≤ s0 v ∧ ∀ y, v ≤ y → y < 2 * v → etaX0 P H X0m y ≤ s0 v)
    (hs0 : ∑ v ∈ Sc, s0 v ≤ 1.52) (hθ : ThetaBlk P H tw X0m Sc th) :
    xbTau P H tw X0m x X0 ≤
      4.3 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
        (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x := by
  classical
  set CN := max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)
  set Eθ := ∑ v ∈ Sc, Real.log (2 * v) * th v
  have hX := h.X0m_pos
  have hXm1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc1 v hv]
  have hCN : 0 ≤ CN := by
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  have hA := Aw_le hP hX0e hp2 ht hlam hx hXm1 hCN hcov hSc1 hEta hE
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc)
    (transferBound P h hXm hP hp2 ht htv hlam hlam1 hxZ hX0 hX0m hSc1 hSc)
  have hEθ : 0 ≤ Eθ := Finset.sum_nonneg fun v hv =>
    mul_nonneg (Real.log_nonneg (by linarith [hSc1 v hv])) (hθ v hv).1
  set L := levels P X0m x
  have hL0 : ∀ n ∈ L, n ≠ 0 := by
    intro n hn; have := (Finset.mem_filter.mp hn).2; omega
  have hlogX : 0 < Real.log X0m + 1 := by linarith
  -- the block bounds of `η`
  set sη : ℝ → ℝ := fun v => th v / (Real.log X0m + 1)
  have hEb : EtaBlk P H tw X0m Sc sη := fun v hv =>
    ⟨div_nonneg (hθ v hv).1 hlogX.le, fun y h1 h2 =>
      (etaG_one_le hXm1 y).trans (div_le_div_of_nonneg_right ((hθ v hv).2 y h1 h2) hlogX.le)⟩
  -- the `τ`-sources of a family of levels `T`
  have hsrc : ∀ T : Finset ℕ, (∀ n ∈ T, n ≠ 0) → ∀ ψ : ℝ → ℝ, (∀ y, X0m ≤ y → 0 ≤ ψ y) →
      (∀ n' ∈ (NAll P x X0m).filter (2 ≤ ·), ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n ≤
        2.04 * ψ (posn P.labelVal x n') *
          ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n')) →
      ∑ n ∈ T, ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n ≤
        2.04 * ∑ d ∈ NAll P x X0m,
          aLev P H tw X0m x d / Vl P d * etaG P H tw X0m ψ (posn P.labelVal x d) := by
    intro T hT ψ hψ0 htr
    refine (tau_to_src hP hp2 hX T).trans ?_
    have h2 : ∀ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
        ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n ≤
          2.04 * ((∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
            (ψ (posn P.labelVal x n') / Vl P n')) := by
      intro n' hn'
      obtain ⟨hn'A, -⟩ := Finset.mem_filter.mp hn'
      have hpos := posn_ge_of_mem_NAll hn'A hX
      refine (htr n' hn').trans ?_
      have hS := Stau_le (tw := tw) (x := x) hP hX0e hp2 n'
      have hVn := KR.valN_labelVal_pos P n'
      have hψ := hψ0 _ hpos
      have e : 2.04 * ψ (posn P.labelVal x n') *
          ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') =
          2.04 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal *
            (ψ (posn P.labelVal x n') / Vl P n')) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hS (div_nonneg hψ hVn.le)
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (regroupG (H := H) (X0 := X0) (tw := tw) (x := x) hp2 hXm1 ψ hψ0) (by norm_num)
  -- the first part
  set ψ : ℝ → ℝ := fun y => Real.log y + 1
  have hψ0 : ∀ y, X0m ≤ y → 0 ≤ ψ y := by
    intro y hy; simp only [ψ]
    have := Real.log_nonneg (show (1 : ℝ) ≤ y by linarith); linarith
  have hAθ : ∑ v ∈ Sc, Aw P H tw X0m x v * th v ≤ 2 * CN * Eθ / Real.log x := by
    calc ∑ v ∈ Sc, Aw P H tw X0m x v * th v
        ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * th v) :=
          Finset.sum_le_sum fun v hv => by
            have := mul_le_mul_of_nonneg_right (hA v hv) (hθ v hv).1
            calc Aw P H tw X0m x v * th v ≤ 2 * CN * Real.log (2 * v) / Real.log x * th v :=
                  this
              _ = _ := by ring
      _ = 2 * CN * Eθ / Real.log x := by rw [← Finset.mul_sum]; ring
  have hP1 : ∑ n ∈ L, (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n) / Vl P n ≤
      2.04 * (2 * CN * Eθ / Real.log x) := by
    have e : ∀ n ∈ L, (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n) / Vl P n =
        ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n :=
      fun n _ => Finset.sum_div _ _ _
    rw [Finset.sum_congr rfl e]
    refine (hsrc L hL0 ψ hψ0 fun n' hn' => ?_).trans ?_
    · obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
      exact transferInf h hXm hP hp2 ht hlam hlam1 hxZ hn'2 (posn_ge_of_mem_NAll hn'A hX) L hL0
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (cover_gen hcov hSc0 hθ).trans hAθ
  -- the second part
  set τd : ℕ → ℝ := fun d => ∑ n' ∈ d.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' d
  have hτ0 : ∀ d, 0 ≤ τd d := fun d => Finset.sum_nonneg fun n' _ => tauPart_nonneg _ _
  have hblk : ∀ v ∈ Sc, ∑ d ∈ NW P x v, τd d / Vl P d ≤
      2.04 * (2 * CN / Real.log x * (Eθ / (Real.log X0m + 1))) := by
    intro v hv
    have hT : ∀ n ∈ NW P x v, n ≠ 0 := fun n hn => ((mem_NW P (hSc0 v hv)).mp hn).1
    have e : ∀ d ∈ NW P x v, τd d / Vl P d =
        ∑ n' ∈ d.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' d / Vl P d :=
      fun d _ => Finset.sum_div _ _ _
    rw [Finset.sum_congr rfl e]
    refine (hsrc (NW P x v) hT (fun _ => 1) (fun _ _ => zero_le_one) fun n' hn' => ?_).trans ?_
    · obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
      have := transferBlock h hXm hP hp2 ht hlam hlam1 hxZ hn'2
        (posn_ge_of_mem_NAll hn'A hX) (hSc0 v hv)
      simpa using this
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (cover_gen hcov hSc0 hEb).trans ?_
      calc ∑ v ∈ Sc, Aw P H tw X0m x v * sη v
          ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * sη v) :=
            Finset.sum_le_sum fun v hv => by
              have := mul_le_mul_of_nonneg_right (hA v hv) (hEb v hv).1
              calc Aw P H tw X0m x v * sη v ≤ 2 * CN * Real.log (2 * v) / Real.log x * sη v :=
                    this
                _ = _ := by ring
        _ = 2 * CN / Real.log x * (Eθ / (Real.log X0m + 1)) := by
            rw [← Finset.mul_sum]
            congr 1
            simp only [sη, Eθ]
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun v _ => by ring
  have hP2 : ∑ n ∈ L, (∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) / Vl P n ≤
      1.52 * (2.04 * (2 * CN / Real.log x * (Eθ / (Real.log X0m + 1)))) := by
    have hstep : ∀ n ∈ L, (∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) / Vl P n ≤
        (∑ d ∈ B1set P H X0m x X0 n, τd d) / Vl P n := by
      intro n _
      apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P n).le
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨hdm, hd1, -, hT⟩ := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hd2 : 2 ≤ d := by
        rcases Nat.lt_or_ge d 2 with h' | h'
        · interval_cases d
          · have h2 := (Nat.mem_properDivisors.mp hdm).2; simp at hdn; omega
          · exact absurd rfl hd1
        · exact h'
      exact TVE_le hP hX0e hp2 hd2 hT
    refine (Finset.sum_le_sum hstep).trans ?_
    refine ((regroupB1 (X0 := X0) hp2 hX τd hτ0).trans (coverF τd hτ0 hcov hSc0 hX0b)).trans ?_
    set K := 2.04 * (2 * CN / Real.log x * (Eθ / (Real.log X0m + 1)))
    have hK0 : 0 ≤ K := by positivity
    calc ∑ v ∈ Sc, (∑ d ∈ NW P x v, τd d / Vl P d) * s0 v ≤ ∑ v ∈ Sc, K * s0 v :=
          Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hblk v hv) (hX0b v hv).1
      _ = K * ∑ v ∈ Sc, s0 v := by rw [Finset.mul_sum]
      _ ≤ K * 1.52 := mul_le_mul_of_nonneg_left hs0 hK0
      _ = 1.52 * K := by ring
  unfold xbTau
  have hsplit : ∑ n ∈ L, (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n +
      ∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) / Vl P n =
      ∑ n ∈ L, (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n) / Vl P n +
      ∑ n ∈ L, (∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) / Vl P n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => add_div _ _ _
  rw [hsplit]
  -- the numerics
  have hbig : (100000000 : ℝ) + 1 ≤ Real.log X0m + 1 := by linarith
  have hsm : Eθ / (Real.log X0m + 1) ≤ Eθ / 100000001 :=
    div_le_div_of_nonneg_left hEθ (by norm_num) (by linarith)
  have hq : 0 ≤ 2 * CN / Real.log x := by positivity
  have h1 := mul_le_mul_of_nonneg_left hsm hq
  have e : 4.3 * CN * Eθ / Real.log x = 2.15 * (2 * CN / Real.log x * Eθ) := by ring
  rw [e]
  have h3 : 2.04 * (2 * CN * Eθ / Real.log x) = 2.04 * (2 * CN / Real.log x * Eθ) := by ring
  have h4 : 0 ≤ 2 * CN / Real.log x * Eθ := mul_nonneg hq hEθ
  have h5 : 2 * CN / Real.log x * (Eθ / 100000001) = (2 * CN / Real.log x * Eθ) / 100000001 := by
    ring
  nlinarith

/-- **Lemma 5.27 (the `X₀` jump in exact chain form)**, eq. (xb): for a start `x ≥ X₀⁻`, under
(HBS) on `[1, Z]` and the inputs of Proposition 5.18,

  `|R_res 1_{[X₀,∞)}(x) - ρ^sh_1(x)| ≤ 𝔅(x) + 4.3 C_N E_θ/log x`,

with `𝔅(x)` as in eq. (frakB) (`xbB`; with the factor `1 + θ` in `𝔹₂`), `E_θ = ∑_v log(2v) θ_v`
(Lemma 5.20 block bounds, `ThetaBlk`) and `C_N = C_S(2.04 + 4.71/log X₀)`. Here `λ₀ ≥ 1 + 3θ`
(`θ` the Lipschitz constant of `H`), `λ₀ ≤ 1.001`. -/
theorem lemma_5_27 {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 3 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 th : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0b : ∀ v ∈ Sc, 0 ≤ s0 v ∧ ∀ y, v ≤ y → y < 2 * v → etaX0 P H X0m y ≤ s0 v)
    (hs0 : ∑ v ∈ Sc, s0 v ≤ 1.52) (hθ : ThetaBlk P H tw X0m Sc th) :
    |Rres P H tw X0m x ((Ici X0).indicator fun _ => 1) -
        rhoSh P tw X0m x ((Ici X0).indicator fun _ => 1)| ≤
      xbB P H tw X0m x X0 θ lam0 +
        4.3 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
          (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x := by
  have hlam2 : 1 + 2 * θ ≤ lam0 := by linarith [hP.theta_nonneg]
  exact (xb_split hP hX0e hp2 ht hlam hx).trans (add_le_add_right
    (xbTau_le h hXm hP hX0e hp2 ht htv hlam2 hlam1 hx hxZ hX0 hX0m hcov hSc1 hSc hEta hE hX0b
      hs0 hθ) _)

end KR

end
