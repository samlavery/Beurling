module

public import RequestProject.Beurling.Noise.LemSRankin

/-!
# A generic Rankin bound under (H_BS)

`HBS.rankin_gen`: for `z`-smooth elements of value `> V`, with `log z ≥ 10⁸` and (H_BS) up to
`z²`, `∑ 1/n ≤ V^{-1/(2 log z)} e^{log log z + 8.3}`. This is Rankin's bound with exponent
`1 - 1/(2 log z)` as in the proof of Lemma 6.27(b) (05-queue.tex), with the Euler product and
prime sums of the proof of Lemma 5.21(ii) (`HBS.lemS_rankin`).
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

set_option maxHeartbeats 2000000 in
/-- **Rankin's bound** (Lemma 6.27(b), exponent `1 - 1/(2 log z)`; Lemma 5.21(ii)): for a
finite set `S` of elements of value `> V` all of whose primes are `≤ z`,
`∑_{e ∈ S} 1/val e ≤ e^{-log V/(2 log z)} e^{log log z + 8.3}`. -/
theorem rankin_gen (h : P.HBS X0m Z η1 η2 ε1) {z V : ℝ} (hV : 0 < V)
    (hL : 100000000 ≤ Real.log z) (hzZ : z ^ 2 ≤ Z) (S : Finset (ℕ →₀ ℕ))
    (hS : ∀ e ∈ S, V < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z) :
    ∑ e ∈ S, 1 / P.val e ≤
      Real.exp (-(Real.log V / (2 * Real.log z))) * Real.exp (Real.log (Real.log z) + 8.3) := by
  set L := Real.log z with hLdef
  have hL0 : 0 < L := by linarith
  by_cases hz1 : 1 < z
  swap
  · -- `z ≤ 1`: every element of `S` is `0`
    push_neg at hz1
    have h0 : ∀ e ∈ S, e = 0 := by
      intro e he
      ext j
      by_contra hj
      have := (hS e he).2 j (Finsupp.mem_support_iff.mpr hj)
      have := P.one_lt j
      simp at hj; linarith
    have hval0 : P.val 0 = 1 := by simp [BeurlingSystem.val]
    rcases S.eq_empty_or_nonempty with hSe | ⟨e0, he0⟩
    · rw [hSe, Finset.sum_empty]; positivity
    · have hSsub : S ⊆ {0} := fun e he => by rw [Finset.mem_singleton]; exact h0 e he
      have hV1 : V < 1 := by
        have := (hS e0 he0).1; rw [h0 e0 he0, hval0] at this; exact this
      have hlogV : Real.log V < 0 := Real.log_neg hV hV1
      calc ∑ e ∈ S, 1 / P.val e ≤ ∑ e ∈ ({0} : Finset (ℕ →₀ ℕ)), 1 / P.val e :=
            Finset.sum_le_sum_of_subset_of_nonneg hSsub fun e _ _ =>
              (one_div_pos.mpr (P.val_pos e)).le
        _ = 1 := by simp [hval0]
        _ ≤ Real.exp (-(Real.log V / (2 * L))) * Real.exp (Real.log L + 8.3) := by
            have h1 : 1 ≤ Real.exp (-(Real.log V / (2 * L))) := Real.one_le_exp (by
              have : Real.log V / (2 * L) < 0 := div_neg_of_neg_of_pos hlogV (by positivity)
              linarith)
            have h2 : 1 ≤ Real.exp (Real.log L + 8.3) := Real.one_le_exp (by
              have := Real.log_nonneg (show (1 : ℝ) ≤ L by linarith); linarith)
            nlinarith
  have hz0 : 0 < z := by linarith
  have hz2 : 2 ≤ z := by
    have : Real.log 2 ≤ Real.log z := by
      have := Real.log_two_lt_d9; linarith
    exact (Real.log_le_log_iff (by norm_num) hz0).mp this
  have hzZ1 : z ≤ Z := by nlinarith
  -- the exponents
  set δ := 1 / (2 * L) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδs : δ ≤ 0.00000001 := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  set θ := 1 - δ with hθ
  have hθ0 : 0 < θ := by linarith
  -- Step 1: `1/val ≤ V^{-δ} val^{-θ}`
  have hpt : ∀ e ∈ S, 1 / P.val e ≤ Real.exp (-(Real.log V / (2 * L))) * P.val e ^ (-θ) := by
    intro e he
    have hYv := (hS e he).1
    have hv0 := P.val_pos e
    have e1 : 1 / P.val e = P.val e ^ (-δ) * P.val e ^ (-θ) := by
      rw [← Real.rpow_add hv0, hθ, show -δ + -(1 - δ) = (-1 : ℝ) by ring, Real.rpow_neg_one,
        one_div]
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : P.val e ^ (-δ) ≤ V ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hV hYv.le (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos hV, hδ]
    congr 1; field_simp
  -- Step 2: the Euler product
  set J := P.primesLe z
  have hSJ : ∀ e ∈ S, e.support ⊆ J := by
    intro e he j hj
    rw [P.mem_primesLe]; exact (hS e he).2 j hj
  have hEu := P.sum_rpow_le_euler hθ0 J S hSJ
  set x : ℕ → ℝ := fun j => P.p j ^ (-θ) with hxdef
  have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hxb : ∀ j ∈ J, 0 ≤ x j ∧ x j ≤ 0.51 := by
    intro j hj
    have hp2 : 2 ≤ P.p j := h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ1)
    refine ⟨by have := P.p_pos j; positivity, ?_⟩
    have : P.p j ^ (-θ) ≤ 2 ^ (-θ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    refine this.trans ?_
    rw [hθ, show -(1 - δ) = -1 + δ by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    have hd2 : (2 : ℝ) ^ δ ≤ 1.0001 := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have : Real.log 2 * δ ≤ 1 / 100000000 := by nlinarith [Real.log_two_lt_d9]
      refine (Real.exp_le_exp.mpr this).trans ?_
      have hb := Real.exp_bound' (x := (1 / 100000000 : ℝ)) (by norm_num) (by norm_num) (n := 2)
        (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hb
      linarith
    nlinarith
  have hprod := LemS.prod_inv_le_exp J x (fun j hj => ⟨(hxb j hj).1, by linarith [(hxb j hj).2]⟩)
  -- Step 3: the prime sums
  have hs1 := sum_inv_p_le h hz2 hzZ1
  have hs2 : P.Sp z ≤ L + 0.43 := by
    have := (P.lemma_5_1 h (by linarith) hzZ1).2.2.1.2; linarith
  have hs3 := sum_log_div_sq_le_lemS h (by linarith) hzZ
  have hlogp : ∀ j ∈ J, 0 ≤ Real.log (P.p j) ∧ Real.log (P.p j) ≤ L := fun j hj =>
    ⟨P.log_p_nonneg j, Real.log_le_log (P.p_pos j) (P.mem_primesLe.mp hj)⟩
  have hx1 : ∀ j ∈ J, x j ≤ 1 / P.p j + 1.65 * δ * (Real.log (P.p j) / P.p j) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    refine rpow_neg_le_lin (P.p_pos j) hl0 hδ0.le ?_
    rw [hδ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hx2 : ∀ j ∈ J, x j ^ 2 ≤ (1 / Real.log 2 + 6 * δ) * (Real.log (P.p j) / P.p j ^ 2) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    have hp2 : 2 ≤ P.p j := h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ1)
    refine rpow_neg_sq_le hp2 hδ0.le ?_
    have : 2 * δ * Real.log (P.p j) ≤ 2 * δ * L := mul_le_mul_of_nonneg_left hlL (by positivity)
    have h2 : 2 * δ * L = 1 := by rw [hδ]; field_simp
    linarith
  -- Step 4: assembly of the exponent
  have hsumx : ∑ j ∈ J, x j ≤ Real.log L + 4.13 + 1.65 * δ * (L + 0.43) := by
    calc ∑ j ∈ J, x j ≤ ∑ j ∈ J, (1 / P.p j + 1.65 * δ * (Real.log (P.p j) / P.p j)) :=
          Finset.sum_le_sum hx1
      _ = ∑ j ∈ J, 1 / P.p j + 1.65 * δ * P.Sp z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
      _ ≤ Real.log L + 4.13 + 1.65 * δ * (L + 0.43) := by
          have : 1.65 * δ * P.Sp z ≤ 1.65 * δ * (L + 0.43) :=
            mul_le_mul_of_nonneg_left hs2 (by positivity)
          linarith
  have hsumx2 : ∑ j ∈ J, x j ^ 2 / (2 * (1 - x j)) ≤ 3.25 := by
    have hc : 1 / Real.log 2 + 6 * δ ≤ 1.4428 := by
      have : 1 / Real.log 2 ≤ 1 / 0.6931471803 :=
        one_div_le_one_div_of_le (by norm_num) Real.log_two_gt_d9.le
      have : (1 : ℝ) / 0.6931471803 ≤ 1.4427 := by norm_num
      linarith
    calc ∑ j ∈ J, x j ^ 2 / (2 * (1 - x j))
        ≤ ∑ j ∈ J, 1.0205 * ((1 / Real.log 2 + 6 * δ) * (Real.log (P.p j) / P.p j ^ 2)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨h0, h1⟩ := hxb j hj
          have : x j ^ 2 / (2 * (1 - x j)) ≤ 1.0205 * x j ^ 2 := by
            rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (x j)]
          nlinarith [hx2 j hj]
      _ = 1.0205 * (1 / Real.log 2 + 6 * δ) * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 1.0205 * 1.4428 * 2.2 := by
          have h0 : 0 ≤ ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 :=
            Finset.sum_nonneg fun j _ => div_nonneg (P.log_p_nonneg j) (by positivity)
          have : 0 ≤ 1 / Real.log 2 + 6 * δ := by positivity
          calc 1.0205 * (1 / Real.log 2 + 6 * δ) * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2
              ≤ 1.0205 * 1.4428 * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 := by gcongr
            _ ≤ 1.0205 * 1.4428 * 2.2 := by gcongr
      _ ≤ 3.25 := by norm_num
  have hexp : ∑ j ∈ J, (x j + x j ^ 2 / (2 * (1 - x j))) ≤ Real.log L + 8.3 := by
    rw [Finset.sum_add_distrib]
    have : 1.65 * δ * (L + 0.43) ≤ 0.83 := by
      rw [hδ]; field_simp; nlinarith
    linarith
  calc ∑ e ∈ S, 1 / P.val e
        ≤ ∑ e ∈ S, Real.exp (-(Real.log V / (2 * L))) * P.val e ^ (-θ) := Finset.sum_le_sum hpt
    _ = Real.exp (-(Real.log V / (2 * L))) * ∑ e ∈ S, P.val e ^ (-θ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.log V / (2 * L))) * ∏ j ∈ J, (1 - P.p j ^ (-θ))⁻¹ :=
        mul_le_mul_of_nonneg_left hEu (Real.exp_pos _).le
    _ ≤ Real.exp (-(Real.log V / (2 * L))) * Real.exp (Real.log L + 8.3) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hprod.trans (Real.exp_le_exp.mpr hexp)

end HBS

end BeurlingSystem

end
