module

public import RequestProject.Beurling.Noise.BridgeBR
public import RequestProject.Beurling.Noise.KRTransProp
public import RequestProject.Beurling.Noise.KRNormMain

/-!
# Proposition 5.26, the near-threshold part (`BRNearPart`)

The second bullet of the proof of Proposition 5.26: by the split Duhamel form (`Etil_split`,
Proposition 5.18) the true-minus-nominal kernel at a level `n ≥ 2` is
`Ẽ_n = ∑_{n' ∣ n} 𝒯^nom_{n'→n} S^τ_{n'} + S^{X₀}_n`.

* `τ`-near part: `|T_c| ≤ 2`, the transfer `∑_n TV(𝒯_{n'→n} S^τ_{n'})/n ≤
  2.04 (log(x/n') + 1) TV(S^τ_{n'})/n'` (`transferInf`), the `τ`-source bound (`Stau_le`), the
  regrouping by the parents with the weight `θ(v) = ∑_{w τ-near at v}(log(v/w) + B₁)/w`
  (`regroupG`), the block bounds `θ ≤ θ_v` on `[v, 2v)` (Lemma 5.20) and Proposition 5.18
  (`A(v) ≤ 2 C_N log(2v)/log x`) give `≤ 2 · 2.04 · 2 C_N E_θ/log x ≤ 8.4 C_N E_θ/log x`, with
  `E_θ = ∑_v log(2v) θ_v`.
* `X₀`-near part (terminal levels): `T_c` is within `o_{X₀}` of `T_c(X₀) = 0` on the support of
  `S^{X₀}_n` (`TermOsc`), and `∑_n TV(S^{X₀}_n)/n ≤ 2 C_N · 1.52 log(2X₀)/log x` by `SX0_le`,
  `regroupX0T`, `EtaX0Sum` and Proposition 5.18.

`KR.brNearPart` : `BRNearPart` under (HBS) and the inputs of `prop_5_18_hbs`, with the
Lemma 5.20 block bounds of `θ` (`ThetaBlk`), `EtaX0Sum` and `TermOsc` as named inputs.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

/-- **Lemma 5.20, the block bounds of `θ`**: `θ(y) = ∑_{w τ-near at y}(log(y/w) + B₁)/w ≤ θ_v`
on `[v, 2v)` (`B₁ = 1`), `θ_v ≥ 0`; the paper's `E_θ` is `∑_v log(2v) θ_v`. -/
def ThetaBlk (Sc : Finset ℝ) (th : ℝ → ℝ) : Prop :=
  ∀ v ∈ Sc, 0 ≤ th v ∧ ∀ y, v ≤ y → y < 2 * v →
    etaG P H tw X0m (fun y => Real.log y + 1) y ≤ th v

/-- **The oscillation of `T_c` at the terminal sources** (proof of Proposition 5.26, second
bullet): on the support of `S^{X₀}_n`, `|T_c| ≤ o_{X₀}` (`T_c` is within `o_{X₀}` of
`T_c(X₀) = 0` there). -/
def TermOsc (Tc : ℝ → ℝ) (oX0 : ℝ) : Prop :=
  ∀ n t, SX0 P.labelVal x H tw X0m n t ≠ 0 → |Tc t| ≤ oX0

variable {P H tw X0m x}

/-- `|∫ T f| ≤ c ∫|f|` if `|T| ≤ 2` and `|T| ≤ c` where `f ≠ 0`. -/
lemma abs_integral_mul_le {Tc f : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2)
    (hf : Integrable f) {c : ℝ} (hpt : ∀ t, f t ≠ 0 → |Tc t| ≤ c) :
    |∫ t, Tc t * f t| ≤ c * (∫⁻ t, ‖f t‖ₑ).toReal := by
  have hb : ∀ᵐ t ∂volume, ‖Tc t‖ ≤ 2 :=
    Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hTb t
  have hi : Integrable (fun t => Tc t * f t) := hf.bdd_mul (c := 2) hTm.aestronglyMeasurable hb
  rw [← integral_norm_eq_lintegral_enorm hf.1, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hi.abs (hf.norm.const_mul c) ?_)
  intro t
  simp only [abs_mul, Real.norm_eq_abs]
  by_cases h0 : f t = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hpt t h0) (abs_nonneg _)

/-- **The near-threshold part of the proof of Proposition 5.26** (`BRNearPart`), with
`C_N = C_S(2.04 + 4.71/log X₀)`. -/
theorem brNearPart {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 th : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0s : EtaX0SumLoc P H X0m X0 Sc s0 x) (hθ : ThetaBlk P H tw X0m Sc th)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) {o : ℝ → ℝ}
    (ho : 0 ≤ o X0) (hTo : TermOsc P H tw X0m x Tc (o X0)) :
    BRNearPart P H tw X0m x Tc o X0
      (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0))
      (∑ v ∈ Sc, Real.log (2 * v) * th v) := by
  classical
  set CN := max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)
  have hX := h.X0m_pos
  have hXm1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc1 v hv]
  have hCN : 0 ≤ CN := by
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hH := hP.reg
  have hA := Aw_le hP hX0e hp2 ht hlam hx hXm1 hCN hcov hSc1 hEta hE
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc)
    (transferBound P h hXm hP hp2 ht htv hlam hlam1 hxZ hX0 hX0m hSc1 hSc)
  set L := levels P X0m x
  have hL0 : ∀ n ∈ L, n ≠ 0 := by
    intro n hn
    have := (Finset.mem_filter.mp hn).2; omega
  -- the Duhamel form at each level
  set Tf : ℕ → ℕ → ℝ → ℝ := fun n' n =>
    Tch P.labelVal H (kapN tw X0m P.labelVal x) n' (Stau P.labelVal x H tw X0m n') n
  have hTf : ∀ n' n, Integrable (Tf n' n) := fun n' n =>
    (integrable_Tch hH _ n' (integrable_Stau hH n').1 (integrable_Stau hH n').2 n).1
  have hSX : ∀ n, Integrable (SX0 P.labelVal x H tw X0m n) := fun n => (integrable_SX0 hH n).1
  have hb : ∀ᵐ t ∂volume, ‖Tc t‖ ≤ 2 :=
    Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hTb t
  have hlev : ∀ n ∈ L, |(∫ t, Tc t * (gK P.labelVal x H (phiT tw X0m) n t -
      gNom P H tw X0m x n t)) / Vl P n| ≤
      (2 * ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n +
        o X0 * (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal) / Vl P n := by
    intro n hn
    have hn2 := (Finset.mem_filter.mp hn).2
    have hV := KR.valN_labelVal_pos P n
    rw [abs_div, abs_of_pos hV]
    apply div_le_div_of_nonneg_right _ hV.le
    have hsplit : (fun t => Tc t * (gK P.labelVal x H (phiT tw X0m) n t -
        gNom P H tw X0m x n t)) = fun t =>
        ∑ n' ∈ n.divisors.filter (2 ≤ ·), Tc t * Tf n' n t +
          Tc t * SX0 P.labelVal x H tw X0m n t := by
      funext t
      have := Etil_split (tw := tw) (x := x) hP hX0e hval2 hn2 t
      unfold Etil at this
      rw [this, mul_add, Finset.mul_sum]
    rw [hsplit, integral_add (integrable_finset_sum _ fun n' _ =>
        (hTf n' n).bdd_mul (c := 2) hTm.aestronglyMeasurable hb)
        ((hSX n).bdd_mul (c := 2) hTm.aestronglyMeasurable hb),
      integral_finset_sum _ fun n' _ =>
        (hTf n' n).bdd_mul (c := 2) hTm.aestronglyMeasurable hb]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun n' _ =>
        abs_integral_mul_le hTm hTb (hTf n' n) fun t _ => hTb t
    · exact abs_integral_mul_le hTm hTb (hSX n) fun t ht0 => hTo n t ht0
  unfold BRNearPart
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hlev).trans ?_)
  -- split into the two parts
  have hsum : ∑ n ∈ L, (2 * ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n +
        o X0 * (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal) / Vl P n =
      2 * ∑ n ∈ L, ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n +
        o X0 * ∑ n ∈ L, (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal / Vl P n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_div, mul_div_assoc, Finset.sum_div, mul_div_assoc]
  rw [hsum]
  -- the `τ`-near part
  set ψ : ℝ → ℝ := fun y => Real.log y + 1
  have hψ0 : ∀ y, X0m ≤ y → 0 ≤ ψ y := by
    intro y hy; simp only [ψ]
    have := Real.log_nonneg (show (1 : ℝ) ≤ y by linarith); linarith
  have htau : ∑ n ∈ L, ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n ≤
      2.04 * (2 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x) := by
    refine (tau_to_src hP hp2 hX L).trans ?_
    have h2 : ∀ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
        ∑ n ∈ L, tauPart P H tw X0m x n' n / Vl P n ≤
          2.04 * ((∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
            (ψ (posn P.labelVal x n') / Vl P n')) := by
      intro n' hn'
      obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
      have hpos := posn_ge_of_mem_NAll hn'A hX
      refine (transferInf h hXm hP hp2 ht hlam hlam1 hxZ hn'2 hpos L hL0).trans ?_
      have hS := Stau_le (tw := tw) (x := x) hP hX0e hp2 n'
      have hVn := KR.valN_labelVal_pos P n'
      have hψ := hψ0 _ hpos
      have e : 2.04 * (Real.log (posn P.labelVal x n') + 1) *
          ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') =
          2.04 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal *
            (ψ (posn P.labelVal x n') / Vl P n')) := by simp only [ψ]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hS (div_nonneg hψ hVn.le)
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine ((regroupG (H := H) (X0 := X0) (tw := tw) (x := x) hp2 hXm1 ψ hψ0).trans
      (cover_gen hcov hSc0 hθ)).trans ?_
    calc ∑ v ∈ Sc, Aw P H tw X0m x v * th v
        ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * th v) :=
          Finset.sum_le_sum fun v hv => by
            have := mul_le_mul_of_nonneg_right (hA v hv) (hθ v hv).1
            calc Aw P H tw X0m x v * th v ≤ 2 * CN * Real.log (2 * v) / Real.log x * th v :=
                  this
              _ = _ := by ring
      _ = 2 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x := by
          rw [← Finset.mul_sum]; ring
  -- the terminal part
  have hterm : ∑ n ∈ L, (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal / Vl P n ≤
      2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) := by
    calc ∑ n ∈ L, (∫⁻ t, ‖SX0 P.labelVal x H tw X0m n t‖ₑ).toReal / Vl P n
        ≤ ∑ n ∈ L, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n :=
          Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_right
            (SX0_le hP hX0e hp2 n) (KR.valN_labelVal_pos P n).le
      _ ≤ ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v :=
          (regroupX0T (tw := tw) (X0 := X0) hp2 hX L).trans
            (cover_gen_loc (by linarith) hcov hSc0 hX0s.1)
      _ ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * s0 v) :=
          Finset.sum_le_sum fun v hv => by
            have := mul_le_mul_of_nonneg_right (hA v hv) (hX0s.1 v hv).1
            calc Aw P H tw X0m x v * s0 v ≤ 2 * CN * Real.log (2 * v) / Real.log x * s0 v :=
                  this
              _ = _ := by ring
      _ = 2 * CN / Real.log x * ∑ v ∈ Sc, Real.log (2 * v) * s0 v := by rw [Finset.mul_sum]
      _ ≤ 2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) :=
          mul_le_mul_of_nonneg_left hX0s.2 (by positivity)
  have hEθ : 0 ≤ ∑ v ∈ Sc, Real.log (2 * v) * th v := Finset.sum_nonneg fun v hv =>
    mul_nonneg (Real.log_nonneg (by linarith [hSc1 v hv])) (hθ v hv).1
  have h1 := mul_le_mul_of_nonneg_left htau (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hterm ho
  have e1 : 2 * (2.04 * (2 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x)) =
      8.16 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x := by ring
  have e2 : o X0 * (2 * CN / Real.log x * (1.52 * Real.log (2 * X0))) =
      o X0 * (2 * CN) * (1.52 * Real.log (2 * X0)) / Real.log x := by ring
  have h3 : 8.16 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x ≤
      8.4 * CN * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log x := by
    apply div_le_div_of_nonneg_right _ hlx.le
    have := mul_nonneg hCN hEθ
    nlinarith
  rw [add_div]
  linarith

/-- **Proposition 5.26 (the bridge: operator versus sharp)** under (HBS): with the inputs of
`brNearPart` and the oscillation property `OscBound` of `o_u`,
`log x · |BR_c(x)| ≤ (5.1 C_N + C_S) ∑_u log(2u) o_u + 8.4 C_N E_θ`,
`C_S = max(2.01 C_BS, 1.4)`, `C_N = C_S(2.04 + 4.71/log X₀)`, `E_θ = ∑_v log(2v) θ_v`. -/
theorem prop_5_26_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 th : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hcovL : ∀ n ∈ levels P X0m x, ∃ u ∈ Sc, n ∈ NW P x u) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0s : EtaX0SumLoc P H X0m X0 Sc s0 x) (hθ : ThetaBlk P H tw X0m Sc th)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) {o : ℝ → ℝ}
    (hosc : OscBound P H x Tc Sc o) (hX0S : X0 ∈ Sc) (hTo : TermOsc P H tw X0m x Tc (o X0)) :
    Real.log x * |BRc P H tw X0m x Tc| ≤
      (5.1 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) +
        max (2.01 * BSaias.PhiInf 100000000) 1.4) * ∑ u ∈ Sc, Real.log (2 * u) * o u +
      8.4 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
        ∑ v ∈ Sc, Real.log (2 * v) * th v := by
  have hCS : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_of_le_right (by norm_num)
  have hCN : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0) := by
    positivity
  have hlx : 0 < Real.log x := Real.log_pos (by have := h.X0m_ge; norm_num at this; linarith)
  exact prop_5_26 hP (fun p _ => hp2 _) ht hx hlx hTm hTb hSc1 hosc
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc) hcovL
    (brNearPart h hXm hP hX0e hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hcov hSc1 hSc hEta hE hX0s
      hθ hTm hTb ((hosc X0 hX0S).1) hTo) hX0S hCN hCS

end KR

end
