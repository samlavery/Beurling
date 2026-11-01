module

public import RequestProject.Beurling.Noise.TauNearProofPt
public import RequestProject.Beurling.Noise.LemSRankin

/-!
# Lemma 5.20: harmonic sums over smooth elements

For a finite set `S` of `z`-smooth elements (`2 ≤ z`, `z² ≤ Z`, (HBS) on `[1, Z]`):

* `smooth_harm_le` : `∑_{m ∈ S} 1/m ≤ 1810 log z` (Euler product `∏_{p ≤ z} (1 - 1/p)⁻¹`, with
  `∑_{p ≤ z} 1/p ≤ log log z + 4.13` and `∑_{p ≤ z} log p/p² ≤ 2.2` from Lemma 5.1);
* `smooth_logharm_le` : `∑_{m ∈ S} log m/m ≤ 2·1810 log z (log z + 0.43)` (`log m = ∑ e_j log p_j`,
  `∑_{m ∈ S} e_j/m ≤ (2/p_j) · 1810 log z`, and Lemma 5.1(iii)).

These replace the paper's `∑_m 1/m ≤ 1.9 log P` and `∑_m log(8mP²)/m ≤ 5.4 log²P(1 + 5/log P)`
(crude constants; the margin of Lemma 5.20 absorbs them).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma exp_75_le : Real.exp 7.5 ≤ 1810 := by
  have he : Real.exp 1 ≤ 2.7182818286 := (Real.exp_one_lt_d9).le
  have h7 : Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he 7
  have hh : Real.exp 0.5 ≤ 1.65 := by
    have hsq : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 0.5]
  have e : Real.exp 7.5 = Real.exp 1 ^ 7 * Real.exp 0.5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have : (2.7182818286 : ℝ) ^ 7 ≤ 1096.7 := by norm_num
  nlinarith [Real.exp_pos 0.5, pow_pos (Real.exp_pos 1) 7]

/-- **The Euler-product bound** for `z`-smooth elements: `∑_{m ∈ S} 1/m ≤ 1810 log z`. -/
theorem smooth_harm_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ : z ^ 2 ≤ Z)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) :
    ∑ e ∈ S, 1 / P.val e ≤ 1810 * Real.log z := by
  have hzZ' : z ≤ Z := by nlinarith
  set J := P.primesLe z
  have hsupp : ∀ e ∈ S, e.support ⊆ J := fun e he i hi => by
    rw [mem_primesLe]; exact hS e he i hi
  have hE := P.sum_rpow_le_euler one_pos J S hsupp
  have hp2 : ∀ j ∈ J, 2 ≤ P.p j := fun j hj => h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ')
  have hx : ∀ j ∈ J, 0 ≤ P.p j ^ (-(1 : ℝ)) ∧ P.p j ^ (-(1 : ℝ)) < 1 := fun j hj => by
    rw [Real.rpow_neg_one]
    have := hp2 j hj
    exact ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith)⟩
  have hprod := LemS.prod_inv_le_exp J (fun j => P.p j ^ (-(1 : ℝ))) hx
  have hS1 : ∑ e ∈ S, 1 / P.val e = ∑ e ∈ S, P.val e ^ (-(1 : ℝ)) :=
    Finset.sum_congr rfl fun e _ => by rw [Real.rpow_neg_one, one_div]
  -- the exponent
  have hsum1 := h.sum_inv_p_le hz hzZ'
  have hsum2 := h.sum_log_div_sq_le_lemS (by linarith) hzZ
  have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hterm : ∀ j ∈ J, P.p j ^ (-(1 : ℝ)) + (P.p j ^ (-(1 : ℝ))) ^ 2 /
      (2 * (1 - P.p j ^ (-(1 : ℝ)))) ≤ 1 / P.p j + Real.log (P.p j) / P.p j ^ 2 / 0.6931 := by
    intro j hj
    have hp := hp2 j hj
    rw [Real.rpow_neg_one]
    have hx0 : 0 < (P.p j)⁻¹ := by positivity
    have hx1 : (P.p j)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hlp : Real.log 2 ≤ Real.log (P.p j) := Real.log_le_log (by norm_num) hp
    have h1 : (P.p j)⁻¹ ^ 2 / (2 * (1 - (P.p j)⁻¹)) ≤ (P.p j)⁻¹ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (P.p j)⁻¹]
    have h2 : (P.p j)⁻¹ ^ 2 ≤ Real.log (P.p j) / P.p j ^ 2 / 0.6931 := by
      rw [inv_pow, div_div, le_div_iff₀ (by positivity)]
      have : 0 < P.p j ^ 2 := by positivity
      field_simp
      linarith
    rw [one_div]; linarith
  have hexp : ∑ j ∈ J, (P.p j ^ (-(1 : ℝ)) + (P.p j ^ (-(1 : ℝ))) ^ 2 /
      (2 * (1 - P.p j ^ (-(1 : ℝ))))) ≤ Real.log (Real.log z) + 7.31 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    have : (∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2) / 0.6931 ≤ 2.2 / 0.6931 :=
      div_le_div_of_nonneg_right hsum2 (by norm_num)
    have : (2.2 : ℝ) / 0.6931 ≤ 3.18 := by norm_num
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  calc ∑ e ∈ S, 1 / P.val e ≤ Real.exp (Real.log (Real.log z) + 7.31) := by
        rw [hS1]; exact hE.trans (hprod.trans (Real.exp_le_exp.mpr hexp))
    _ = Real.exp 7.31 * Real.log z := by rw [Real.exp_add, Real.exp_log hlz]; ring
    _ ≤ 1810 * Real.log z := by
        have : Real.exp 7.31 ≤ Real.exp 7.5 := Real.exp_le_exp.mpr (by norm_num)
        nlinarith [exp_75_le]

/-- `∑_{e ∈ S} e_j/e ≤ (2/p_j)·1810 log z` for a finite set of `z`-smooth elements. -/
theorem smooth_mult_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ : z ^ 2 ≤ Z)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) (j : ℕ) (hj : P.p j ≤ z) :
    ∑ e ∈ S, (e j : ℝ) / P.val e ≤ 2 / P.p j * (1810 * Real.log z) := by
  classical
  have hzZ' : z ≤ Z := by nlinarith
  have hp2 : 2 ≤ P.p j := h.p_ge_two (hj.trans hzZ')
  set N := S.sup (fun e => e j)
  -- `e_j/e = ∑_{k < e_j} 1/e`
  have h1 : ∑ e ∈ S, (e j : ℝ) / P.val e =
      ∑ k ∈ range N, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e := by
    symm
    rw [Finset.sum_comm' (t' := S) (s' := fun e => (range N).filter (fun k => k + 1 ≤ e j))]
    · refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (range N).filter (fun k => k + 1 ≤ e j) = range (e j) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨-, h⟩; omega
        · intro hk
          exact ⟨lt_of_lt_of_le hk (Finset.le_sup (f := fun e => e j) he), by omega⟩
      rw [this, Finset.card_range]; ring
    · intro k e
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
  -- each layer
  have h2 : ∀ k, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e ≤
      (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) := by
    intro k
    set S' := S.filter (fun e => k + 1 ≤ e j)
    have hinj : Set.InjOn (fun e => e - Finsupp.single j (k + 1)) S' := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hla : Finsupp.single j (k + 1) ≤ a := Finsupp.single_le_iff.mpr ha'
      have hlb : Finsupp.single j (k + 1) ≤ b := Finsupp.single_le_iff.mpr hb'
      have := congrArg (· + Finsupp.single j (k + 1)) hab
      simp only [tsub_add_cancel_of_le hla, tsub_add_cancel_of_le hlb] at this
      exact this
    have hsm : ∀ e ∈ S'.image (fun e => e - Finsupp.single j (k + 1)),
        ∀ i ∈ e.support, P.p i ≤ z := by
      intro e he i hi
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
      apply hS e0 (Finset.mem_filter.mp he0).1 i
      rw [Finsupp.mem_support_iff] at hi ⊢
      intro h0; apply hi; simp [Finsupp.tsub_apply, h0]
    have hb := smooth_harm_le h hz hzZ _ hsm
    rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)] at hb
    calc ∑ e ∈ S', 1 / P.val e =
          ∑ e ∈ S', (P.p j)⁻¹ ^ (k + 1) * (1 / P.val (e - Finsupp.single j (k + 1))) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [P.val_sub_single (Finset.mem_filter.mp he).2, one_div, one_div, mul_inv, inv_pow]
          ring
      _ ≤ (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hb (by have := P.p_pos j; positivity)
  rw [h1]
  calc ∑ k ∈ range N, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e
      ≤ ∑ k ∈ range N, (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) :=
        Finset.sum_le_sum fun k _ => h2 k
    _ = (∑ k ∈ range N, (P.p j)⁻¹ ^ (k + 1)) * (1810 * Real.log z) := by rw [Finset.sum_mul]
    _ ≤ 2 / P.p j * (1810 * Real.log z) := by
        have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        -- geometric sum `∑_{k<N} x^{k+1} ≤ x/(1-x) ≤ 2x`
        set x := (P.p j)⁻¹
        have hx0 : 0 ≤ x := by positivity
        have hx1 : x ≤ 1 / 2 := by
          simp only [x]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have hcl : ∀ n : ℕ, (∑ k ∈ range n, x ^ (k + 1)) * (1 - x) = x - x ^ (n + 1) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
        have hgeo : ∀ n : ℕ, ∑ k ∈ range n, x ^ (k + 1) ≤ 2 * x := by
          intro n
          have h := hcl n
          have hpos : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
          have hS0 : 0 ≤ ∑ k ∈ range n, x ^ (k + 1) :=
            Finset.sum_nonneg fun k _ => pow_nonneg hx0 _
          nlinarith
        calc ∑ k ∈ range N, x ^ (k + 1) ≤ 2 * x := hgeo N
          _ = 2 / P.p j := by simp only [x]; rw [div_eq_mul_inv]

/-- `∑_{m ∈ S} log m/m ≤ 3620 log z (log z + 0.43)` for a finite set of `z`-smooth elements. -/
theorem smooth_logharm_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ : z ^ 2 ≤ Z)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) :
    ∑ e ∈ S, Real.log (P.val e) / P.val e ≤
      3620 * Real.log z * (Real.log z + 0.43) := by
  classical
  have hzZ' : z ≤ Z := by nlinarith
  set J := P.primesLe z
  have hlog : ∀ e ∈ S, Real.log (P.val e) = ∑ j ∈ J, (e j : ℝ) * Real.log (P.p j) := by
    intro e he
    rw [P.log_val]
    apply Finsupp.sum_of_support_subset
    · intro i hi; rw [P.mem_primesLe]; exact hS e he i hi
    · intro i _; simp
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  calc ∑ e ∈ S, Real.log (P.val e) / P.val e
      = ∑ j ∈ J, Real.log (P.p j) * ∑ e ∈ S, (e j : ℝ) / P.val e := by
        rw [Finset.sum_congr rfl fun e he => by rw [hlog e he, Finset.sum_div]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ j ∈ J, Real.log (P.p j) * (2 / P.p j * (1810 * Real.log z)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_left
          (smooth_mult_le h hz hzZ S hS j (P.mem_primesLe.mp hj)) (P.log_p_nonneg j)
    _ = 3620 * Real.log z * P.Sp z := by
        unfold BeurlingSystem.Sp
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 3620 * Real.log z * (Real.log z + 0.43) := by
        have := (P.lemma_5_1 h (by linarith) hzZ').2.2.1.2
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end KR.TNP

end
