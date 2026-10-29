module

public import RequestProject.Beurling.Noise.KRNormFix

/-!
# Proposition 5.18, the `∞`-norm bound

`prop_5_18_inf` proves the fourth bound of Proposition 5.18,

  `∑_n TV(C^x_n)/n ≤ 2.04 (log x + B₁)/(1 - 2.04 λ₀ θ_*) + 3.2 ≤ 2.1 (log x + B₁) + 3.2`,

`B₁ = 1`, the sum over all levels that carry mass (`x/n ≥ X₀⁻/2`; the other true kernels vanish,
`TVt_eq_zero_low`), by the paper's argument ("The ∞-norm"):

* the non-`X₀` part `S = ∑_{x/n ≥ X₀⁻} a(n)/n` (`aLev`) satisfies
  `S ≤ 2.04 (log x + B₁) + 2.04 θ_* S` (`Sall_rec`): Corollary 5.17(c) with the harmonic bound
  (`sum_kS_le`), the transfer `transferInf`, the source bound `Stau_le` and the regrouping with
  the weight `θ` (`regroupG`);
* the block bound `sup_u A(u) ≤ 2.1` (`Aw_le_block`): `W^nom ≤ 2.04` (`WS_le_block`), the block
  transfer `transferBlock` and the fixed point `fixed_point_const`, with `∑_v sup η` small;
* the terminal levels add `∑_n TV(S^{X₀}_n)/n ≤ ∑_v A(v) s⁰_v ≤ 2.1 · 1.52 ≤ 3.2`
  (`SX0_le`, `regroupX0T`, `cover_gen`).

The inputs that are not proved here are the quantities of Lemma 5.20 and of step (iii), as named
hypotheses: `ThetaStar` (`θ ≤ θ_*`, with `2.04 λ₀ θ_* ≤ 0.02`), `EtaBlk` (`η ≤ s_v` on the
blocks, with `2.04 ∑_v s_v ≤ 0.02`; the paper has `∑_v sup η ≤ E⁰_η/log X₀ ≤ e^{-0.99Λ}`) and the
scale bounds of `η_{X₀}` with `∑_v s⁰_v ≤ 1.52` (the second bullet of step (iii)).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- `TV(C_n^nom) ≤ TV` of the nominal kernel `kN` (distribution-function model). -/
lemma TVn_le_kN {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) {n : ℕ}
    (hn0 : n ≠ 0) :
    TVn P H tw X0m x n ≤ (eVariationOn (kN P H tw X0m x n) univ).toReal := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  unfold TVn
  by_cases h1 : n = 1
  · subst h1; rw [if_pos rfl, kN, kerV_one]
  rw [if_neg h1]
  have hn2 : 2 ≤ n := by omega
  obtain ⟨⟨hTV, -⟩, -⟩ := theorem_5_15_nominal (x := x) hP hval2 ht hlam hx hn2
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTV)
    (lintegral_gK_nom_le hval hP.reg hκ hn2)

/-- Below `X₀⁻` the non-`X₀` part vanishes: `a(n) = 0` for `x/n < X₀⁻`. -/
lemma aLev_eq_zero_low {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (hx : X0m ≤ x) {n : ℕ} (hlow : posn P.labelVal x n < X0m) :
    aLev P H tw X0m x n = 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hn1 : n ≠ 1 := by
    rintro rfl; unfold posn at hlow; rw [LemmaM.valN_one, div_one] at hlow; linarith
  unfold aLev
  have hTVn : TVn P H tw X0m x n = 0 := by
    unfold TVn
    rw [if_neg hn1]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 0 := by omega
      rw [gK_le_one _ _ _ (by norm_num)]; simp
    have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
    have hle := lintegral_gK_nom_le hval hP.reg hκ h2 (x := x)
    have hz : kerV P.labelVal x H (kapN tw X0m P.labelVal x) n = fun _ => 0 :=
      kN_eq_zero (P := P) (H := H) (tw := tw) h2 (by unfold posn at hlow; exact hlow)
    rw [hz, eVariationOn_zero_fun] at hle
    rw [nonpos_iff_eq_zero.mp hle, ENNReal.toReal_zero]
  rw [hTVn, zero_add]
  refine Finset.sum_eq_zero fun n' hn' => ?_
  have hn'n : n' ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hn').1
  unfold tauPart
  by_cases he : n' = n
  · subst he
    have : Stau P.labelVal x H tw X0m n' = fun _ => 0 :=
      funext fun t => Stau_eq_zero_low (tw := tw) hP hp2 hlow t
    rw [Tch_self, this]; simp
  · have hlt : n' < n := by
      have hn0 : n ≠ 0 := by
        rintro rfl; simp at hn'
      exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn'n) he
    have hz : Tch P.labelVal H (kapN tw X0m P.labelVal x) n'
        (Stau P.labelVal x H tw X0m n') n = fun _ => 0 := by
      funext t
      rw [Tch_eq _ hlt t]
      rw [Finset.sum_eq_zero fun d _ => ?_, neg_zero]
      have : kapN tw X0m P.labelVal x d n = 0 := by
        unfold kapN nomFilter
        rw [if_neg (fun h => absurd h.2 (by unfold posn at hlow; exact not_le.mpr hlow))]
      rw [this, zero_mul]
    rw [hz]; simp

/-- Above the masses: the true kernels vanish for `x/n < X₀⁻/2` (`n ≥ 2`). -/
lemma TVt_eq_zero_low {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    {n : ℕ} (hn1 : n ≠ 1) (hlow : posn P.labelVal x n < X0m / 2) :
    TVt P H tw X0m x n = 0 := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  unfold TVt
  rw [if_neg hn1]
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  have : gK P.labelVal x H (phiT tw X0m) n = fun _ => 0 := by
    funext t
    by_contra hc
    exact absurd (hsupp n t hc).1 (not_le.mpr hlow)
  rw [this]; simp

/-- Moving the `τ`-parts of a family of levels to the source levels `Src = {n' ≥ 2, x/n' ≥ X₀⁻}`:
`∑_{n ∈ T} ∑_{n' ∣ n} TV(𝒯_{n'→n} S^τ_{n'})/n ≤ ∑_{n' ∈ Src} ∑_{n ∈ T} TV(𝒯_{n'→n} S^τ_{n'})/n`. -/
lemma tau_to_src {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (hX : 0 < X0m)
    (T : Finset ℕ) :
    ∑ n ∈ T, ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n ≤
      ∑ n' ∈ (NAll P x X0m).filter (2 ≤ ·), ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n := by
  classical
  set Src := (NAll P x X0m).filter (2 ≤ ·)
  have h1 : ∀ n ∈ T, ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n / Vl P n ≤
      ∑ n' ∈ Src, tauPart P H tw X0m x n' n / Vl P n := by
    intro n _
    rw [← Finset.sum_filter_of_ne (p := fun n' => n' ∈ Src) (s := n.divisors.filter (2 ≤ ·))]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n' hn'; exact (Finset.mem_filter.mp hn').2
      · intro n' _ _
        exact div_nonneg (tauPart_nonneg _ _) (KR.valN_labelVal_pos P n).le
    · intro n' hn' hne
      refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hn').2⟩
      have hn'0 : n' ≠ 0 := by have := (Finset.mem_filter.mp hn').2; omega
      apply mem_NAll_of_posn hn'0 hX
      by_contra hlow; push_neg at hlow
      exact hne (by rw [tauPart_eq_zero_low hP hp2 hlow n, zero_div])
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  exact Finset.sum_comm

/-- **The block recursion**: `A(u) ≤ 2.04 + 2.04 ∑_v A(v) s_v`. -/
theorem Aw_block {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z) {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hEb : EtaBlk P H tw X0m Sc s) {u : ℝ} (hu0 : 0 < u) :
    Aw P H tw X0m x u ≤ 2.04 + 2.04 * ∑ v ∈ Sc, Aw P H tw X0m x v * s v := by
  have hX := h.X0m_pos
  have hXm1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hsplit : Aw P H tw X0m x u = ∑ n ∈ NW P x u, TVn P H tw X0m x n / Vl P n +
      ∑ n ∈ NW P x u, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
        tauPart P H tw X0m x n' n / Vl P n := by
    unfold Aw aLev
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_div, Finset.sum_div]
  rw [hsplit]
  have hx0 : 0 ≤ x := by linarith
  have hnom : ∑ n ∈ NW P x u, TVn P H tw X0m x n / Vl P n ≤ 2.04 := by
    refine (sum_TVn_le_Wnom hP hp2 ht hlam hx u).trans ?_
    change WS P H tw X0m x x u ≤ 2.04
    exact WS_le_block h hXm hP hp2 ht hlam hlam1 hx hxZ (by linarith) hu0
  refine add_le_add hnom ?_
  refine (tau_to_src hP hp2 hX _).trans ?_
  have h2 : ∀ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
      ∑ n ∈ NW P x u, tauPart P H tw X0m x n' n / Vl P n ≤
        2.04 * ((∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
          ((fun _ => (1 : ℝ)) (posn P.labelVal x n') / Vl P n')) := by
    intro n' hn'
    obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
    have hpos := posn_ge_of_mem_NAll hn'A hX
    refine (transferBlock h hXm hP hp2 ht hlam hlam1 hxZ hn'2 hpos hu0).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hS := Stau_le (tw := tw) (x := x) hP hX0e hp2 n'
    have hVn := KR.valN_labelVal_pos P n'
    rw [mul_div_assoc', mul_one]
    exact div_le_div_of_nonneg_right hS hVn.le
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (regroupG hp2 hXm1 (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)).trans
    (cover_gen hcov hSc hEb)

/-- **The block bound** `sup_u A(u) ≤ 2.1` (Proposition 5.18, proof, `∞`-norm part). -/
theorem Aw_le_block {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z) {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hEb : EtaBlk P H tw X0m Sc s) (hs : 2.04 * ∑ v ∈ Sc, s v ≤ 0.02) :
    ∀ u ∈ Sc, Aw P H tw X0m x u ≤ 2.1 := by
  have hfix := fixed_point_const Sc (Aw P H tw X0m x) s (a := 2.04) (b := 2.04) (q := 0.02)
    (by norm_num) (by norm_num) (by norm_num)
    (fun v _ => Finset.sum_nonneg fun n _ =>
      div_nonneg (aLev_nonneg n) (KR.valN_labelVal_pos P n).le)
    (fun v hv => (hEb v hv).1) hs
    (fun u hu => Aw_block h hXm hP hX0e hp2 ht hlam hlam1 hx hxZ hcov hSc hEb (hSc u hu))
  intro u hu
  exact (hfix u hu).trans (by norm_num)

/-- The non-`X₀` part `S = ∑_{x/n ≥ X₀⁻} a(n)/n`. -/
noncomputable def Sall (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ) : ℝ :=
  ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d

/-- **The recursion for `S`**: `S ≤ 2.04 (log x + B₁) + 2.04 θ_* S`. -/
theorem Sall_rec {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 θs : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z) (hθ : ThetaStar P H tw X0m θs) :
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
    exact mul_le_mul_of_nonneg_left (hθ.2 _) ha
  have : 2.04 * ∑ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
      (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
        (ψ (posn P.labelVal x n') / Vl P n') ≤ 2.04 * (θs * Sall P H tw X0m x) :=
    mul_le_mul_of_nonneg_left (hreg.trans hθb) (by norm_num)
  linarith

/-- **Proposition 5.18, the `∞`-norm bound.** Under (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸`, the
paper's width hypotheses (`PaperWidth`, `X₀⁻ = X₀ - H(X₀)/2`), `1 + 2θ ≤ λ₀ ≤ 1.001`, a start
`x ≥ X₀⁻` with `2x/X₀⁻ ≤ Z`, and a positive decision order: for a family of scales `Sc`
covering the levels, and the Lemma 5.20 / step (iii) quantities as hypotheses
(`ThetaStar θ_*` with `2.04 λ₀ θ_* ≤ 0.02`; `EtaBlk s` with `2.04 ∑ s ≤ 0.02`; scale bounds `s⁰`
of `η_{X₀}` with `∑ s⁰ ≤ 1.52`),

  `∑_{x/n ≥ X₀⁻/2} TV(C_n)/n ≤ 2.04 (log x + B₁)/(1 - 2.04 λ₀ θ_*) + 3.2` and
  `≤ 2.1 (log x + B₁) + 3.2`,  `B₁ = 1`.

The levels `x/n < X₀⁻/2` carry no mass (`TVt_eq_zero_low`). -/
theorem prop_5_18_inf {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 θs : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x)
    (hxZ : 2 * x / X0m ≤ Z) {Sc : Finset ℝ} {s s0 : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hθ : ThetaStar P H tw X0m θs) (hθs : 2.04 * lam0 * θs ≤ 0.02)
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
  have hθ0 := hθ.1
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
  have hSrec := Sall_rec h hXm hP hX0e hp2 ht hlam hlam1 hx hxZ hθ
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
