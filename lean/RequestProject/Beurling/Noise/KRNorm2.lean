module

public import RequestProject.Beurling.Noise.KRNormMain

/-!
# Proposition 5.18, `∞`-norm bound, with a horizon-restricted `θ_*`

`prop_5_18_inf` takes `ThetaStar` (`θ(v) ≤ θ_*` for every real `v`). Its proof reads `θ` only at
the heights `x/d` of the levels `d ∈ NAll P x X₀⁻` (in `Sall_rec`), so `prop_5_18_inf_on` and
`Sall_rec_on` assume the bound only there. These are copies of `Sall_rec` / `prop_5_18_inf` with
that single hypothesis changed.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- **The recursion for `S`**, with `θ ≤ θ_*` only at the heights `x/d`, `d ∈ NAll`:
`S ≤ 2.04 (log x + B₁) + 2.04 θ_* S`. -/
theorem Sall_rec_on {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 θs : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z)
    (hθ : ∀ d ∈ NAll P x X0m,
      etaG P H tw X0m (fun y => Real.log y + 1) (posn P.labelVal x d) ≤ θs) :
    Sall P H tw X0m x ≤ 2.04 * (Real.log x + 1) + 2.04 * θs * Sall P H tw X0m x := by
  have hX := h.X0m_pos
  have hXm1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hx0 : 0 ≤ x := by linarith
  have hsplit : Sall P H tw X0m x = ∑ n ∈ NAll P x X0m, TVn P H tw X0m x n / Vl P n +
      ∑ n ∈ NAll P x X0m, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
        tauPart P H tw X0m x n' n / Vl P n := by
    unfold Sall aLev
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_div, Finset.sum_div]
  have hn0 : ∀ n ∈ NAll P x X0m, n ≠ 0 := by
    intro n hn
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hn
    exact (iota_pos e).ne'
  have hxZ' : x / X0m ≤ Z := by
    refine le_trans ?_ hxZ
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  have hnom : ∑ n ∈ NAll P x X0m, TVn P H tw X0m x n / Vl P n ≤ 2.04 * (Real.log x + 1) := by
    calc ∑ n ∈ NAll P x X0m, TVn P H tw X0m x n / Vl P n
        ≤ ∑ n ∈ NAll P x X0m, (eVariationOn (kN P H tw X0m x n) univ).toReal / Vl P n :=
          Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_right
            (TVn_le_kN hP hp2 ht hlam hx (hn0 n hn)) (KR.valN_labelVal_pos P n).le
      _ ≤ 2.04 * (Real.log x + 1) :=
          sum_kS_le (v := x) (y := x) h hXm hP hp2 ht hlam hlam1 hx (by linarith) hxZ'
  have hS0 : 0 ≤ Sall P H tw X0m x := Finset.sum_nonneg fun d _ =>
    div_nonneg (aLev_nonneg d) (KR.valN_labelVal_pos P d).le
  conv_lhs => rw [hsplit]
  refine add_le_add hnom ?_
  refine (tau_to_src hP hp2 hX _).trans ?_
  set ψ : ℝ → ℝ := fun y => Real.log y + 1
  have h2 : ∀ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
      ∑ n ∈ NAll P x X0m, tauPart P H tw X0m x n' n / Vl P n ≤
        2.04 * ((∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
          (ψ (posn P.labelVal x n') / Vl P n')) := by
    intro n' hn'
    obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
    have hpos := posn_ge_of_mem_NAll hn'A hX
    refine (transferInf h hXm hP hp2 ht hlam hlam1 hxZ hn'2 hpos _ hn0).trans ?_
    have hS := Stau_le (tw := tw) (x := x) hP hX0e hp2 n'
    have hVn := KR.valN_labelVal_pos P n'
    have hψ : 0 ≤ ψ (posn P.labelVal x n') := by
      simp only [ψ]; have := Real.log_nonneg (show (1 : ℝ) ≤ posn P.labelVal x n' by linarith)
      linarith
    have e : 2.04 * (Real.log (posn P.labelVal x n') + 1) *
        ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') =
        2.04 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal *
          (ψ (posn P.labelVal x n') / Vl P n')) := by simp only [ψ]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_right hS (div_nonneg hψ hVn.le)
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  have hψ0 : ∀ y, X0m ≤ y → 0 ≤ ψ y := by
    intro y hy; simp only [ψ]
    have := Real.log_nonneg (show (1 : ℝ) ≤ y by linarith); linarith
  have hreg := regroupG (H := H) (X0 := X0) (tw := tw) (x := x) hp2 hXm1 ψ hψ0
  have hθb : ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d *
      etaG P H tw X0m ψ (posn P.labelVal x d) ≤ θs * Sall P H tw X0m x := by
    unfold Sall
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have ha := div_nonneg (aLev_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x) d)
      (KR.valN_labelVal_pos P d).le
    rw [mul_comm θs]
    exact mul_le_mul_of_nonneg_left (hθ d (by assumption)) ha
  have : 2.04 * ∑ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
      (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
        (ψ (posn P.labelVal x n') / Vl P n') ≤ 2.04 * (θs * Sall P H tw X0m x) :=
    mul_le_mul_of_nonneg_left (hreg.trans hθb) (by norm_num)
  linarith

/-- **Proposition 5.18, the `∞`-norm bound**, with `θ ≤ θ_*` only at the heights `x/d` read
by the proof (horizon-restricted `ThetaStar`). Under (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸`, the
paper's width hypotheses (`PaperWidth`, `X₀⁻ = X₀ - H(X₀)/2`), `1 + 2θ ≤ λ₀ ≤ 1.001`, a start
`x ≥ X₀⁻` with `2x/X₀⁻ ≤ Z`, and a positive decision order: for a family of scales `Sc`
covering the levels, and the Lemma 5.20 / step (iii) quantities as hypotheses
(`ThetaStar θ_*` with `2.04 λ₀ θ_* ≤ 0.02`; `EtaBlk s` with `2.04 ∑ s ≤ 0.02`; scale bounds `s⁰`
of `η_{X₀}` with `∑ s⁰ ≤ 1.52`),

  `∑_{x/n ≥ X₀⁻/2} TV(C_n)/n ≤ 2.04 (log x + B₁)/(1 - 2.04 λ₀ θ_*) + 3.2` and
  `≤ 2.1 (log x + B₁) + 3.2`,  `B₁ = 1`.

The levels `x/n < X₀⁻/2` carry no mass (`TVt_eq_zero_low`). -/
theorem prop_5_18_inf_on {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 θs : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z) {Sc : Finset ℝ} {s s0 : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hθ0 : 0 ≤ θs) (hθ : ∀ d ∈ NAll P x X0m,
      etaG P H tw X0m (fun y => Real.log y + 1) (posn P.labelVal x d) ≤ θs)
    (hθs : 2.04 * lam0 * θs ≤ 0.02)
    (hEb : EtaBlk P H tw X0m Sc s) (hs : 2.04 * ∑ v ∈ Sc, s v ≤ 0.02)
    (hX0s : ∀ v ∈ Sc, 0 ≤ s0 v ∧ ∀ y, v ≤ y → y < 2 * v → etaX0 P H X0m y ≤ s0 v)
    (hs0 : ∑ v ∈ Sc, s0 v ≤ 1.52) :
    ∑ n ∈ NAll P x (X0m / 2), TVt P H tw X0m x n / Vl P n ≤
        2.04 * (Real.log x + 1) / (1 - 2.04 * lam0 * θs) + 3.2 ∧
      ∑ n ∈ NAll P x (X0m / 2), TVt P H tw X0m x n / Vl P n ≤ 2.1 * (Real.log x + 1) + 3.2 := by
  classical
  have hX := h.X0m_pos
  have hXm1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hlx : 0 ≤ Real.log x + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ x by linarith); linarith
  have hlam0 : 1 ≤ lam0 := by linarith [hP.theta_nonneg]
  set L := NAll P x (X0m / 2)
  have hsub : NAll P x X0m ⊆ L := by
    unfold NAll
    exact Finset.image_subset_image (P.elems_mono (div_le_div_of_nonneg_left (by linarith)
      (by linarith) (by linarith)))
  -- split into the non-`X₀` part and the terminal sources
  have h1 : ∑ n ∈ L, TVt P H tw X0m x n / Vl P n ≤
      ∑ n ∈ L, aLev P H tw X0m x n / Vl P n +
        ∑ n ∈ L, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P n).le
    exact (TVt_le_full hP hX0e hp2 n).trans (add_le_add le_rfl (SX0_le hP hX0e hp2 n))
  have h2 : ∑ n ∈ L, aLev P H tw X0m x n / Vl P n = Sall P H tw X0m x := by
    unfold Sall
    refine (Finset.sum_subset hsub fun n hnL hn => ?_).symm
    have hn0 : n ≠ 0 := by
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hnL
      exact (iota_pos e).ne'
    have hlow : posn P.labelVal x n < X0m := by
      by_contra hc; push_neg at hc
      exact hn (mem_NAll_of_posn hn0 hX hc)
    rw [aLev_eq_zero_low hP hp2 hx hlow, zero_div]
  -- the non-`X₀` part
  have hSrec := Sall_rec_on h hXm hP hX0e hp2 ht hlam hlam1 hx hxZ hθ
  have hden : 0 < 1 - 2.04 * θs := by nlinarith
  have hden' : 0 < 1 - 2.04 * lam0 * θs := by linarith
  have hSb : Sall P H tw X0m x ≤ 2.04 * (Real.log x + 1) / (1 - 2.04 * lam0 * θs) := by
    rw [le_div_iff₀ hden']
    have hS0 : 0 ≤ Sall P H tw X0m x := Finset.sum_nonneg fun d _ =>
      div_nonneg (aLev_nonneg d) (KR.valN_labelVal_pos P d).le
    have : 2.04 * lam0 * θs * Sall P H tw X0m x ≥ 2.04 * θs * Sall P H tw X0m x := by
      have : 2.04 * θs ≤ 2.04 * lam0 * θs := by nlinarith
      nlinarith
    nlinarith
  -- the terminal part
  have hblk := Aw_le_block h hXm hP hX0e hp2 ht hlam hlam1 hx hxZ hcov hSc hEb hs
  have h3 : ∑ n ∈ L, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n ≤ 3.2 := by
    refine (regroupX0T (tw := tw) (X0 := X0) hp2 hX L).trans ?_
    refine (cover_gen (tw := tw) hcov hSc hX0s).trans ?_
    calc ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v ≤ ∑ v ∈ Sc, 2.1 * s0 v :=
          Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hblk v hv) (hX0s v hv).1
      _ = 2.1 * ∑ v ∈ Sc, s0 v := by rw [Finset.mul_sum]
      _ ≤ 3.2 := by nlinarith
  have hmain : ∑ n ∈ L, TVt P H tw X0m x n / Vl P n ≤
      2.04 * (Real.log x + 1) / (1 - 2.04 * lam0 * θs) + 3.2 := by
    rw [h2] at h1; linarith
  refine ⟨hmain, hmain.trans ?_⟩
  have : 2.04 * (Real.log x + 1) / (1 - 2.04 * lam0 * θs) ≤ 2.1 * (Real.log x + 1) := by
    rw [div_le_iff₀ hden']
    nlinarith
  linarith

end KR

end
