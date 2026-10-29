module

public import RequestProject.Beurling.Model.RhoAGood

/-!
# Lemma 6.27(b) in the paper's form: `K_𝒜 ρ̃ ≤ (log t)⁻⁴` below the horizon

The proof of `KAbsR_le` (`SigmaA.lean`) with the final numerics sharpened: Rankin's bound gives
`K_𝒜 g(t) ≤ 2 e^{8.3} log(3y) e^{-(L - log y)/(2 log 3y)}` with `log 3y ≤ 23√L`, which is
`≤ L⁻⁴` (`KAbsR_le_L4`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section Main

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 2000000 in
/-- **Lemma 6.27(b)**, `K_𝒜 g ≤ (log t)⁻⁴` for `0 ≤ g ≤ 2`, at heights `t/X₀⁻ ≤ Z`. -/
theorem KAbsR_le_L4 (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {g : ℝ → ℝ} (hg0 : ∀ z, 0 ≤ g z) (hg2 : ∀ z, g z ≤ 2) {t : ℝ} (htZ : t / Xm X₀ ≤ Z) :
    KAbsR θ X₀ ω g t ≤ Real.log t ^ (-4 : ℤ) := by
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
  have hL40 : 0 ≤ Real.log t ^ (-4 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]; positivity
  suffices hS : ∑ w ∈ A, 1 / Vl P w ≤ Real.log t ^ (-4 : ℤ) / 2 by linarith
  rcases A.eq_empty_or_nonempty with hA0 | ⟨w0, hw0⟩
  · rw [hA0, Finset.sum_empty]; linarith
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
  have hq0 : 0 < q := by linarith
  have hfin : -(Real.log V / (2 * Real.log z)) + (Real.log (Real.log z) + 8.3) ≤
      -(8 * Real.log q) - Real.log 2 := by
    linarith [hE1, hE2, hl23, hlq, hq8, Real.log_two_lt_d9]
  have hL4 : Real.log t ^ (-4 : ℤ) = (q ^ 8)⁻¹ := by
    rw [show Real.log t = q ^ 2 by rw [hq2], zpow_neg, zpow_ofNat, ← pow_mul]
  rw [hL4]
  calc Real.exp (-(Real.log V / (2 * Real.log z)) + (Real.log (Real.log z) + 8.3))
      ≤ Real.exp (-(8 * Real.log q) - Real.log 2) := Real.exp_le_exp.mpr hfin
    _ = (q ^ 8)⁻¹ / 2 := by
        rw [Real.exp_sub, Real.exp_neg, show (8 : ℝ) * Real.log q = Real.log (q ^ 8) by
          rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), Real.exp_log (by norm_num)]

end Main

end BModel
