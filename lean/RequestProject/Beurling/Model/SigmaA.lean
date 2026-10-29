module

public import RequestProject.Beurling.Model.TcMeas
public import RequestProject.Beurling.Model.AbsorbSize
public import RequestProject.Beurling.Model.RankinGen
public import RequestProject.Beurling.Model.CapHSlope
public import RequestProject.Beurling.Model.CapHDiff

/-!
# Lemma 6.27(b): `K_𝒜 ρ̃ ≤ 1/2`, and `|T_c| ≤ 2`, below the horizon of (H_BS)

Lemma 6.27(b) (05-queue.tex): `K_𝒜` is the part of `K_pt` whose landing is absorbed, so its
cofactors `w` have all primes decided before the landing `y/w < y(y)`, hence of value
`≤ 1.12 y(y)` (the decision order of `TNP.Hyp`), and `w > y/y(y)`. With `ρ̃ ≤ 2` (`rhoT_le_two`,
(F1)), Rankin's bound with exponent `1 - 1/(2 log 3y)` (`HBS.rankin_gen`, from (H_BS) up to
`(3y)²`) gives `K_𝒜 ρ̃ ≤ 2 e^{8.3} log(3y) e^{-(L - log y)/(2 log 3y)}`; wherever `K_𝒜 ≠ 0`,
`Λ² < L` and `log 3y ≤ 23 √L` (`AbsorbSize`), so this is `≤ 1/2` (in fact astronomically
small). The paper's form is `K_𝒜 ρ̃ ≤ L⁻⁴`; `1/2` is what `|T_c| ≤ 2` needs.

* `KAbsR_le` : `K_𝒜 g(t) ≤ 1/2` for `0 ≤ g ≤ 2`, at heights `t/X₀⁻ ≤ Z`, under `TNP.Hyp` (whose
  (H_BS) is on `[1, Z]`);
* `TcR_abs_le` : `|T_c(t)| ≤ 2` there (§5.1: `T' = 1 - ρ_det + R' - ρ̄_𝒜 + K_𝒜 ρ̃`, with
  `j₀ = 1 - ρ_det(X₀)`).

The field `hTb : ∀ t, |T_c t| ≤ 2` of `RealMarginLoc` asks this at **every** height; on
`Good(< b)` (H_BS) is known only up to the horizon, so only `t/X₀⁻ ≤ Z` is available here.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **`ρ̃ ≤ 2`** ((F1): the box weights of the jitter law sum to at most `2`). -/
lemma rhoT_le_two (hc : Cond θ X₀) (hev : Even X₀) (ω : JitterΩ) (y : ℝ) :
    rhoT θ X₀ ω y ≤ 2 := by
  have h := (constructionLaw hc hev).slots ω y
  unfold rhoT
  have h2 : (∑' k, (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
      (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 y) ω) ≤ ENNReal.ofReal 2 := by
    rw [ENNReal.ofReal_ofNat]; exact h
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h2

lemma rhoT_nonneg (ω : JitterΩ) (y : ℝ) : 0 ≤ rhoT θ X₀ ω y := ENNReal.toReal_nonneg

section Main

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 2000000 in
/-- **Lemma 6.27(b)** (in the form `K_𝒜 g ≤ 1/2` for `0 ≤ g ≤ 2`), at heights `t/X₀⁻ ≤ Z`. -/
theorem KAbsR_le (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {g : ℝ → ℝ} (hg0 : ∀ z, 0 ≤ g z) (hg2 : ∀ z, g z ≤ 2) {t : ℝ} (htZ : t / Xm X₀ ≤ Z) :
    KAbsR θ X₀ ω g t ≤ 1 / 2 := by
  classical
  set P := PR θ X₀ ω with hP
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXmh := Xm_half hc
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_ge_one hX0 hX (le_refl (X₀ : ℝ)); unfold Xm; linarith
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  set W := (NAll P t (Xm X₀)).filter (2 ≤ ·) with hW
  set cond : ℕ → Prop := fun w => (∀ p ∈ w.primeFactors, twR θ X₀ ω p * Vl P w < t) ∧
    (10 ^ 7 ≤ Real.log t ∧ t / Vl P w < absorbY X₀ t) with hcond
  set A := W.filter cond with hA
  -- `K_𝒜 g ≤ 2 ∑_{w ∈ A} 1/w`
  have hK : KAbsR θ X₀ ω g t ≤ 2 * ∑ w ∈ A, 1 / Vl P w := by
    unfold KAbsR
    rw [← hP, ← hW, hA, Finset.mul_sum, Finset.sum_filter (p := cond)]
    apply Finset.sum_le_sum
    intro w _
    have hV := KR.Sharp.Vl_pos P w
    split_ifs <;> first
      | (rw [mul_one_div]; exact div_le_div_of_nonneg_right (hg2 _) hV.le)
      | norm_num
      | (exfalso; tauto)
  refine hK.trans ?_
  suffices hS : ∑ w ∈ A, 1 / Vl P w ≤ 1 / 4 by linarith
  rcases A.eq_empty_or_nonempty with hA0 | ⟨w0, hw0⟩
  · rw [hA0, Finset.sum_empty]; norm_num
  -- the absorbed range: `Λ² < log x`, `x = scale of t`
  have hw0' := Finset.mem_filter.mp hw0
  have hw0W := Finset.mem_filter.mp hw0'.1
  obtain ⟨-, hw0c⟩ := (KR.Sharp.mem_NAll_iff P hXm0).mp hw0W.1
  have hcut0 : Xm X₀ ≤ t / Vl P w0 := (KR.Sharp.le_div_iff_cut P hXm0).mp hw0c
  have habs0 : t / Vl P w0 < absorbY X₀ t := hw0'.2.2.2
  set x := dyadicScale (X₀ : ℝ) (max (X₀ : ℝ) t) with hxdef
  have hxX : (X₀ : ℝ) ≤ x := le_dyadicScale (by linarith) (le_max_left _ _)
  have hxt : x ≤ max (X₀ : ℝ) t := dyadicScale_le (by linarith) (by positivity)
  have hYx : absorbY X₀ t = absorbYAt X₀ x := rfl
  have hbig : Real.log X₀ ^ 2 < Real.log x := by
    by_contra hlow; push_neg at hlow
    have := absorbYAt_lt hX0 hX hxX hlow
    have e : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
    rw [hYx] at habs0
    linarith
  have hlogX : Real.log X₀ < Real.log x := by
    have : Real.log X₀ < Real.log X₀ ^ 2 := by nlinarith
    linarith
  have hxX' : (X₀ : ℝ) < x := by
    by_contra h; push_neg at h
    have := Real.log_le_log (by linarith) h; linarith
  have hxt' : x ≤ t := by
    rcases le_total (X₀ : ℝ) t with h | h
    · rwa [max_eq_right h] at hxt
    · rw [max_eq_left h] at hxt; linarith
  have ht0 : 0 < t := by linarith
  set L := Real.log t with hLdef
  have hlogxL : Real.log x ≤ L := Real.log_le_log (by linarith) hxt'
  have hL16 : 10 ^ 16 ≤ L := by
    have : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hX 2; norm_num at this ⊢; linarith
    linarith
  set Y := absorbYAt X₀ x with hYdef
  have hY23 : Real.log (3 * Y) ≤ 23 * Real.sqrt L :=
    (AbsorbSize.log_three_absorbYAt_le hX0 hX hxX hbig).trans
      (by have := Real.sqrt_le_sqrt hlogxL; linarith)
  have hYXm : Xm X₀ < Y := by rw [← hYx]; linarith
  have hY0 : 0 < Y := by linarith
  -- the cofactors as exponent vectors
  have hmem : ∀ w ∈ A, ∃ e ∈ P.elems (t / Xm X₀), iota e = w := by
    intro w hw
    have hwW := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
    exact Finset.mem_image.mp hwW
  choose! φ hφe hφi using hmem
  have hφinj : Set.InjOn φ A := by
    intro w1 h1 w2 h2 h12
    rw [← hφi w1 h1, ← hφi w2 h2, h12]
  have hVl : ∀ w ∈ A, Vl P w = P.val (φ w) := by
    intro w hw
    conv_lhs => rw [← hφi w hw]
    exact P.valN_iota _
  have hsum : ∑ w ∈ A, 1 / Vl P w = ∑ e ∈ A.image φ, 1 / P.val e := by
    rw [Finset.sum_image hφinj]
    exact Finset.sum_congr rfl fun w hw => by rw [hVl w hw]
  rw [hsum]
  -- Rankin
  set z := 3 * Y with hz
  set V := t / Y with hVdef
  have hV0 : 0 < V := by positivity
  have hdec : ∀ j, twR θ X₀ ω (qp j) < Y → P.p j ≤ z := by
    intro j hj
    rcases lt_or_ge (P.p j) (Xm X₀ / 2) with hlo | hhi
    · have e := hT.dec_lo j hlo
      rw [e] at hj; linarith
    · have h1 := hT.dec_hi j hhi
      have h2 := hT.width.small (P.p j) hhi
      rw [abs_le] at h1
      linarith [h1.1]
  have hS : ∀ e ∈ A.image φ, V < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    have hwc := (Finset.mem_filter.mp hw).2
    have hVw := KR.Sharp.Vl_pos P w
    refine ⟨?_, fun j hj => hdec j ?_⟩
    · rw [← hVl w hw, hVdef, div_lt_iff₀ hY0]
      have := hwc.2.2
      rw [hYx, div_lt_iff₀ hVw] at this; linarith
    · have hqp : qp j ∈ w.primeFactors := by
        rw [← hφi w hw, BeurlingSystem.primeFactors_iota]
        exact Finset.mem_image_of_mem _ hj
      have h1 := hwc.1 (qp j) hqp
      have h2 := hwc.2.2
      have h3 : twR θ X₀ ω (qp j) < t / Vl P w := by rw [lt_div_iff₀ hVw]; exact h1
      linarith
  have hlz : 100000000 ≤ Real.log z := by
    have : (X₀ : ℝ) ≤ z := by rw [hz]; linarith
    have := Real.log_le_log (by linarith) this
    norm_num at hX ⊢; linarith
  have hsqL : (47 : ℝ) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hzZ : z ^ 2 ≤ Z := by
    refine le_trans ?_ htZ
    have hz0 : 0 < z := by positivity
    rw [← Real.exp_log (show 0 < z ^ 2 by positivity),
      ← Real.exp_log (show 0 < t / Xm X₀ by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow, Real.log_div ht0.ne' hXm0.ne']
    have hXmL : Real.log (Xm X₀) ≤ Real.sqrt L := by
      have h1 : Real.log (Xm X₀) ≤ Real.log X₀ := Real.log_le_log hXm0 hXmX
      have h2 : Real.log X₀ ≤ Real.sqrt L := by
        rw [← Real.sqrt_sq (show 0 ≤ Real.log X₀ by linarith)]
        exact Real.sqrt_le_sqrt (by linarith)
      linarith
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
    push_cast
    nlinarith
  have hR := hT.hbs.rankin_gen hV0 hlz hzZ (A.image φ) hS
  refine hR.trans ?_
  -- numerics
  set q := Real.sqrt L with hq
  have hq2 : q ^ 2 = L := Real.sq_sqrt (by linarith)
  have hq8 : (10 : ℝ) ^ 8 ≤ q := by
    rw [hq, Real.le_sqrt (by norm_num) (by linarith)]; norm_num at hL16 ⊢; linarith
  have hlogY : Real.log Y ≤ 23 * q := by
    have : Real.log Y ≤ Real.log z := Real.log_le_log hY0 (by rw [hz]; linarith)
    linarith
  have hlogV : L - 23 * q ≤ Real.log V := by
    rw [hVdef, Real.log_div ht0.ne' hY0.ne']; linarith
  have hlz0 : 0 < Real.log z := by linarith
  have hE1 : -(Real.log V / (2 * Real.log z)) ≤ -((L - 23 * q) / (2 * (23 * q))) := by
    have hpos : 0 ≤ L - 23 * q := by nlinarith
    have : (L - 23 * q) / (2 * (23 * q)) ≤ Real.log V / (2 * Real.log z) := by
      calc (L - 23 * q) / (2 * (23 * q)) ≤ (L - 23 * q) / (2 * Real.log z) :=
            div_le_div_of_nonneg_left hpos (by positivity) (by linarith)
        _ ≤ Real.log V / (2 * Real.log z) :=
            div_le_div_of_nonneg_right hlogV (by positivity)
    linarith
  have hE2 : Real.log (Real.log z) ≤ Real.log 23 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hlz0 (by linarith)
  have hl23 : Real.log 23 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (4 : ℝ)
    have h := Real.exp_one_gt_d9
    have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e4]
    calc (23 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := by gcongr
  have hlq : Real.log q ≤ q / 1000 + 6 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < q / 1000 by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : Real.log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e7]
      calc (1000 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := by gcongr
    linarith
  have hfrac : (L - 23 * q) / (2 * (23 * q)) = q / 46 - 1 / 2 := by
    rw [← hq2]; field_simp; ring
  rw [hfrac] at hE1
  rw [← Real.exp_add]
  have hfin : -(Real.log V / (2 * Real.log z)) + (Real.log (Real.log z) + 8.3) ≤
      Real.log (1 / 4) := by
    have : Real.log (1 / 4) = -Real.log 4 := by rw [one_div, Real.log_inv]
    rw [this]
    have h4 : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e2]
      calc (4 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
        _ ≤ Real.exp 1 ^ 2 := by gcongr
    nlinarith
  calc Real.exp (-(Real.log V / (2 * Real.log z)) + (Real.log (Real.log z) + 8.3))
      ≤ Real.exp (Real.log (1 / 4)) := Real.exp_le_exp.mpr hfin
    _ = 1 / 4 := Real.exp_log (by norm_num)

omit hc in
lemma KAbsR_nonneg (ω : JitterΩ) {g : ℝ → ℝ} (hg0 : ∀ z, 0 ≤ g z) (t : ℝ) :
    0 ≤ KAbsR θ X₀ ω g t := by
  classical
  unfold KAbsR
  refine Finset.sum_nonneg fun w _ => ?_
  have hV := KR.Sharp.Vl_pos (PR θ X₀ ω) w
  split_ifs
  · exact div_nonneg (hg0 _) hV.le
  · exact le_rfl

/-- `1/(κ u) ≤ 1/100` for `u ≥ X₀`. -/
lemma inv_kappa_le {u : ℝ} (hu : (X₀ : ℝ) ≤ u) : 1 / (kappaParam X₀ * u) ≤ 1 / 100 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hXb := X₀_ge_two_pow hc.hX
  have hu0 : 0 < u := by linarith
  have hw := window_long hc.hX hu
  have hκ0 := (kappa_facts hc.hX).1
  have h1 : (2 * u) ^ (1 / 2 : ℝ) ≤ (2 * u) ^ (7 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (100 : ℝ) ≤ (2 * u) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by linarith)]
    have : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
    linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **`|T_c(t)| ≤ 2`** (§5.1: `|T'| ≤ 2` with the jump `j₀ = 1 - ρ_det(X₀)` removed), at heights
`t/X₀⁻ ≤ Z`, from Lemma 6.27(b) (`KAbsR_le`), `ρ_det ≤ 1 + 1/(κu)` (Lemma 7.1(1)),
`ρ̄_𝒜 ≤ 0.1/log u` and `|R'| ≤ 0.02/log u` (eq. (Rkprime)). -/
theorem TcR_abs_le (hev : Even X₀) (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {t : ℝ} (htZ : t / Xm X₀ ≤ Z) : |TcR θ X₀ ω (jzX X₀) t| ≤ 2 := by
  have hK := KAbsR_le hc ω hT (rhoT_nonneg (θ := θ) (X₀ := X₀) ω) (rhoT_le_two hc hev ω) htZ
  have hK0 := KAbsR_nonneg (θ := θ) (X₀ := X₀) ω (g := rhoT θ X₀ ω)
    (rhoT_nonneg (θ := θ) (X₀ := X₀) ω) t
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hκ0 := (kappa_facts hc.hX).1
  -- `0 ≤ ρ_det(X₀) ≤ 1.01`
  have hd0 : 0 ≤ Target.rhoDet X₀ (kappaParam X₀) X₀ := rhoDet_nonneg X₀ hκ0 hX0
  have hd1 : Target.rhoDet X₀ (kappaParam X₀) X₀ ≤ 1 + 1 / 100 :=
    (BaseRange.rhoDet_le_one_add X₀ hκ0 (by linarith)).trans
      (by linarith [inv_kappa_le hc (le_refl (X₀ : ℝ))])
  unfold TcR jzX
  rcases lt_or_ge t (X₀ : ℝ) with hlt | hge
  · have hT0 : TpCont θ X₀ ω t = 0 := by unfold TpCont; rw [if_neg (not_le.mpr hlt)]
    have hi : KR.Chain.ind X₀ t = 0 := by
      unfold KR.Chain.ind; exact Set.indicator_of_notMem (by simpa using hlt) _
    rw [hT0, hi, abs_le]; constructor <;> nlinarith
  · have hi : KR.Chain.ind X₀ t = 1 := by
      unfold KR.Chain.ind; exact Set.indicator_of_mem (by simpa using hge) _
    have ht0 : 0 < t := by linarith
    have hLt : 10 ^ 8 ≤ Real.log t := hc.hX.trans (Real.log_le_log (by linarith) hge)
    -- `ρ_det(t)`
    have hdt0 : 0 ≤ Target.rhoDet X₀ (kappaParam X₀) t := rhoDet_nonneg X₀ hκ0 ht0.le
    have hdt1 : Target.rhoDet X₀ (kappaParam X₀) t ≤ 1 + 1 / 100 :=
      (BaseRange.rhoDet_le_one_add X₀ hκ0 ht0).trans (by linarith [inv_kappa_le hc hge])
    -- `ρ̄_𝒜`
    set D := DF θ X₀ ω
    have hA1 : absorbedDensityCap (θ / 2) (absSet X₀ D) (uA θ) t ≤ 1 / 100 := by
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hA0 : 0 ≤ absorbedDensityCap (θ / 2) (absSet X₀ D) (uA θ) t := by
      refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) (by linarith))
      unfold absorbedBump
      split_ifs
      · by_cases hm : t ∈ Icc (uA θ a) a
        · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos ht0 _).le
        · rw [Set.indicator_of_notMem hm]
      · exact le_rfl
    -- `R'`
    have hR := abs_deriv_osc_le hc.hθ hc.hX (gammaD_range (θ := θ) hc.hX D) hge
    have hR1 : 0.02 / Real.log t ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hT1 : TpCont θ X₀ ω t = 1 - Target.rhoDet X₀ (kappaParam X₀) t -
        absorbedDensityCap (θ / 2) (absSet X₀ D) (uA θ) t +
        deriv (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) t := by
      unfold TpCont; rw [if_pos hge]
    rw [hT1, hi]
    have hR2 : |deriv (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) t| ≤
        1 / 100 := hR.trans hR1
    have hR' := abs_le.mp hR2
    rw [abs_le]
    constructor <;> nlinarith [hR'.1, hR'.2]

end Main

end BModel
