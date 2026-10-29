module

public import RequestProject.Beurling.Noise.LemSRankin

/-!
# Lemma 5.30 (Rankin bound for smooth elements)

`HBS.rankin_crude` : under (HBS) on `[1, Z]`, for `e^{10} ≤ z ≤ Z` and every `ℓ` (the paper:
`ℓ ≥ 0`),

  `v(ℓ, z) = ∑_{n ∈ 𝒩 ∩ (e^ℓ, 2e^ℓ], P⁺(n) ≤ z} 1/n ≤ e^{14} (log z) e^{-ℓ/log z}`.

The proof is the paper's: with `β = 1/log z` and `θ = 1 - β`, `1/n ≤ e^{-βℓ} n^{-θ}` on the
window, `∑ n^{-θ} ≤ ∏_{p ≤ z} (1 - p^{-θ})⁻¹` (free semigroup), and
`-log(1 - x) ≤ x + x²/(2(1-x))` with `x = p^{-θ} ≤ 0.55`. Since `p^β ≤ e`,
`p^{-θ} ≤ 1/p + (e-1)β log p/p` and `p^{-2θ} ≤ 3 log p/p²`; Lemma 5.1 gives
`∑_{p ≤ z} 1/p ≤ log log z + 4.13`, `∑_{p ≤ z} log p/p ≤ log z + 0.43` and
`∑_{p ≤ z} log p/p² ≤ 2.2 + 0.0706`. The exponent is at most `log log z + 13.5`.
(The paper bounds the square terms prime by prime; the constant `14` is the paper's.)
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- `e^a ≤ 1 + (e - 1) a` for `0 ≤ a ≤ 1` (convexity). -/
lemma exp_le_chord {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Real.exp a ≤ 1 + (Real.exp 1 - 1) * a := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (sub_nonneg.mpr h1) h0
    (by ring : (1 - a) + a = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at this
  linarith

/-- `∑_{p ≤ z} log p/p² ≤ 2.271` for `e^{10} ≤ z ≤ Z`. -/
lemma sum_log_div_sq_le' (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : Real.exp 10 ≤ z)
    (hzZ : z ≤ Z) : ∑ j ∈ P.primesLe z, Real.log (P.p j) / P.p j ^ 2 ≤ 2.271 := by
  have hz1 : 1 ≤ z := le_trans (Real.one_le_exp (by norm_num)) hz
  have hz0 : 0 < z := by linarith
  have hl := P.lemma_5_1 h hz1 hzZ
  have hrest := P.mertensS_eq_Sp_add z
  set L := Real.log z with hL
  have hL10 : 10 ≤ L := by
    rw [hL]; exact (Real.le_log_iff_exp_le hz0).mpr hz
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe z) (fun j => P.p j ^ 2 ≤ z)]
  -- the primes with `p² ≤ z`: part of `S(z) - S_p(z)`
  have h1 : ∑ j ∈ (P.primesLe z).filter (fun j => P.p j ^ 2 ≤ z),
      Real.log (P.p j) / P.p j ^ 2 ≤
      ∑ jk ∈ (P.pps z).filter (fun jk => 1 ≤ jk.2),
        Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) := by
    rw [← Finset.sum_image (f := fun jk : ℕ × ℕ => Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1))
      (s := (P.primesLe z).filter (fun j => P.p j ^ 2 ≤ z)) (g := fun j => (j, 1))
      (fun a _ b _ hab => by simpa using hab)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro jk hjk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_filter, mem_pps, le_refl, and_true]
      exact hj.2
    · intro jk _ _
      exact div_nonneg (P.log_p_nonneg _) (pow_pos (P.p_pos _) _).le
  -- the primes with `p² > z`: at most `S_p(z)/√z`
  have hsq : 0 < √z := Real.sqrt_pos.mpr hz0
  have h2 : ∑ j ∈ (P.primesLe z).filter (fun j => ¬ P.p j ^ 2 ≤ z),
      Real.log (P.p j) / P.p j ^ 2 ≤ P.Sp z / √z := by
    unfold Sp
    rw [Finset.sum_div]
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => div_nonneg (div_nonneg (P.log_p_nonneg j) (P.p_pos j).le) hsq.le))
    simp only [Finset.mem_filter, not_le] at hj
    have hp := P.p_pos j
    have hps : √z ≤ P.p j := by
      rw [Real.sqrt_le_left]; · exact hj.2.le
      · exact hp.le
    have hlp := P.log_p_nonneg j
    rw [div_div, pow_two]
    exact div_le_div_of_nonneg_left hlp (by positivity) (mul_le_mul_of_nonneg_left hps hp.le)
  have hSp : P.Sp z ≤ L + 0.43 := by linarith [hl.2.2.1.2]
  have hrest0 := hl.2.1.2
  have hSpl := hl.2.2.1.1
  -- `(L + 0.43)/√z ≤ 0.0706`
  have he5 : (148 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
    norm_num at this; linarith
  have hsqz : √z = Real.exp (L / 2) := by
    rw [hL, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz0]; ring_nf
  have hexpL : Real.exp 5 * (1 + (L - 10) / 2) ≤ Real.exp (L / 2) := by
    have := Real.add_one_le_exp ((L - 10) / 2)
    have e : Real.exp (L / 2) = Real.exp 5 * Real.exp ((L - 10) / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 5).le
  have h3 : P.Sp z / √z ≤ 0.0706 := by
    have hSp0 : 0 ≤ P.Sp z := Finset.sum_nonneg fun j _ =>
      div_nonneg (P.log_p_nonneg j) (P.p_pos j).le
    rw [div_le_iff₀ hsq, hsqz]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 5.30 (Rankin bound)**: under (HBS) on `[1, Z]`, for `e^{10} ≤ z ≤ Z` (and any `ℓ`),
`v(ℓ, z) ≤ e^{14} (log z) e^{-ℓ/log z}`. -/
theorem rankin_crude (h : P.HBS X0m Z η1 η2 ε1) {z ℓ : ℝ} (hz : Real.exp 10 ≤ z)
    (hzZ : z ≤ Z) :
    P.vSmooth (Real.exp ℓ) z ≤ Real.exp 14 * Real.log z * Real.exp (-(ℓ / Real.log z)) := by
  have hz1 : 1 ≤ z := le_trans (Real.one_le_exp (by norm_num)) hz
  have hz0 : 0 < z := by linarith
  set L := Real.log z with hLdef
  have hL10 : 10 ≤ L := by
    rw [hLdef]; exact (Real.le_log_iff_exp_le hz0).mpr hz
  have hL0 : 0 < L := by linarith
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ); linarith
    linarith
  set β := 1 / L with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 0.1 := by rw [hβ, div_le_iff₀ hL0]; linarith
  set θ := 1 - β with hθ
  have hθ0 : 0 < θ := by linarith
  set Y := Real.exp ℓ with hY
  have hY0 : 0 < Y := Real.exp_pos ℓ
  set S := (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z)
  -- Step 1: `1/n ≤ e^{-βℓ} n^{-θ}`
  have hpt : ∀ e ∈ S, 1 / P.val e ≤ Real.exp (-(ℓ / L)) * P.val e ^ (-θ) := by
    intro e he
    have hYv := (Finset.mem_filter.mp he).2.1
    have hv0 := P.val_pos e
    have e1 : 1 / P.val e = P.val e ^ (-β) * P.val e ^ (-θ) := by
      rw [← Real.rpow_add hv0, hθ, show -β + -(1 - β) = (-1 : ℝ) by ring, Real.rpow_neg_one,
        one_div]
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : P.val e ^ (-β) ≤ Y ^ (-β) := Real.rpow_le_rpow_of_nonpos hY0 hYv.le (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos hY0, hY, Real.log_exp, hβ]
    congr 1; field_simp
  -- Step 2: the Euler product
  set J := P.primesLe z
  have hSJ : ∀ e ∈ S, e.support ⊆ J := by
    intro e he j hj
    rw [P.mem_primesLe]; exact (Finset.mem_filter.mp he).2.2 j hj
  have hEu := P.sum_rpow_le_euler hθ0 J S hSJ
  set x : ℕ → ℝ := fun j => P.p j ^ (-θ) with hxdef
  have hp2 : ∀ j ∈ J, 2 ≤ P.p j := fun j hj => h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ)
  have hlogp : ∀ j ∈ J, 0 ≤ Real.log (P.p j) ∧ Real.log (P.p j) ≤ L := fun j hj =>
    ⟨P.log_p_nonneg j, Real.log_le_log (P.p_pos j) (P.mem_primesLe.mp hj)⟩
  have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hxb : ∀ j ∈ J, 0 ≤ x j ∧ x j ≤ 0.55 := by
    intro j hj
    refine ⟨by have := P.p_pos j; positivity, ?_⟩
    have : P.p j ^ (-θ) ≤ 2 ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hp2 j hj) (by linarith)
    refine this.trans ?_
    have h09 : (2 : ℝ) ^ (-θ) ≤ 2 ^ (-(0.9 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    refine h09.trans ?_
    rw [show (-(0.9 : ℝ)) = -1 + 0.1 by norm_num, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    have h01 : (2 : ℝ) ^ (0.1 : ℝ) ≤ 1.1 := by
      have h10 : ((2 : ℝ) ^ (0.1 : ℝ)) ^ (10 : ℕ) = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      by_contra hc
      push_neg at hc
      have : (1.1 : ℝ) ^ (10 : ℕ) < ((2 : ℝ) ^ (0.1 : ℝ)) ^ (10 : ℕ) :=
        pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
      rw [h10] at this; norm_num at this
    nlinarith
  have hprod := LemS.prod_inv_le_exp J x
    (fun j hj => ⟨(hxb j hj).1, by linarith [(hxb j hj).2]⟩)
  -- Step 3: pointwise bounds
  have hx1 : ∀ j ∈ J, x j ≤ 1 / P.p j + (Real.exp 1 - 1) * β * (Real.log (P.p j) / P.p j) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    have hp := P.p_pos j
    have e1 : x j = Real.exp (β * Real.log (P.p j)) / P.p j := by
      simp only [hxdef]
      rw [Real.rpow_def_of_pos hp, show Real.log (P.p j) * -θ =
        β * Real.log (P.p j) - Real.log (P.p j) by rw [hθ]; ring, Real.exp_sub, Real.exp_log hp]
    have ha1 : β * Real.log (P.p j) ≤ 1 := by
      rw [hβ, div_mul_eq_mul_div, one_mul, div_le_one hL0]; exact hlL
    have hc := exp_le_chord (mul_nonneg hβ0.le hl0) ha1
    rw [e1, div_le_iff₀ hp]
    have : (1 / P.p j + (Real.exp 1 - 1) * β * (Real.log (P.p j) / P.p j)) * P.p j =
        1 + (Real.exp 1 - 1) * (β * Real.log (P.p j)) := by field_simp
    rw [this]; exact hc
  have hx2 : ∀ j ∈ J, x j ^ 2 ≤ 3 * (Real.log (P.p j) / P.p j ^ 2) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    have hp := P.p_pos j
    have hlp2 : Real.log 2 ≤ Real.log (P.p j) := Real.log_le_log (by norm_num) (hp2 j hj)
    have e1 : x j ^ 2 = Real.exp (2 * (β * Real.log (P.p j))) / P.p j ^ 2 := by
      simp only [hxdef]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, Real.rpow_def_of_pos hp,
        show Real.log (P.p j) * (-θ * ((2 : ℕ) : ℝ)) =
          2 * (β * Real.log (P.p j)) - 2 * Real.log (P.p j) by rw [hθ]; push_cast; ring,
        Real.exp_sub, show 2 * Real.log (P.p j) = Real.log (P.p j ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    have ha1 : β * Real.log (P.p j) ≤ 1 := by
      rw [hβ, div_mul_eq_mul_div, one_mul, div_le_one hL0]; exact hlL
    have hE : Real.exp (2 * (β * Real.log (P.p j))) ≤ 3 * Real.log (P.p j) := by
      rcases le_or_gt (Real.log (P.p j)) 2.5 with hs | hs
      · have hb : 2 * (β * Real.log (P.p j)) ≤ 1 / 2 := by nlinarith
        have h1 : Real.exp (2 * (β * Real.log (P.p j))) ≤ Real.exp (1 / 2) :=
          Real.exp_le_exp.mpr hb
        have h2 : Real.exp (1 / 2) ≤ 1.65 := by
          have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          have h4 := Real.exp_one_lt_d9
          nlinarith [Real.exp_pos (1 / 2)]
        linarith
      · have h1 : Real.exp (2 * (β * Real.log (P.p j))) ≤ Real.exp 2 :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp 2 ≤ 7.39 := by
          have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          have h4 := Real.exp_one_lt_d9
          rw [h3]; nlinarith [Real.exp_pos 1]
        linarith
    rw [e1, div_le_iff₀ (by positivity)]
    have : 3 * (Real.log (P.p j) / P.p j ^ 2) * P.p j ^ 2 = 3 * Real.log (P.p j) := by
      field_simp
    rw [this]; exact hE
  -- Step 4: the prime sums
  have hs1 := sum_inv_p_le h hz2 hzZ
  have hs2 : P.Sp z ≤ L + 0.43 := by
    have := (P.lemma_5_1 h hz1 hzZ).2.2.1.2; linarith
  have hs3 := sum_log_div_sq_le' h hz hzZ
  have he1 : Real.exp 1 - 1 ≤ 1.7183 := by have := Real.exp_one_lt_d9; linarith
  have he1' : 0 ≤ Real.exp 1 - 1 := by have := Real.exp_one_gt_d9; linarith
  have hsumx : ∑ j ∈ J, x j ≤ Real.log L + 4.13 + 1.7923 := by
    calc ∑ j ∈ J, x j ≤ ∑ j ∈ J,
          (1 / P.p j + (Real.exp 1 - 1) * β * (Real.log (P.p j) / P.p j)) :=
          Finset.sum_le_sum hx1
      _ = ∑ j ∈ J, 1 / P.p j + (Real.exp 1 - 1) * β * P.Sp z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
      _ ≤ Real.log L + 4.13 + 1.7923 := by
          have hb : (Real.exp 1 - 1) * β * P.Sp z ≤ 1.7183 * β * (L + 0.43) := by
            have hSp0 : 0 ≤ P.Sp z := Finset.sum_nonneg fun j _ =>
              div_nonneg (P.log_p_nonneg j) (P.p_pos j).le
            gcongr
          have hc : 1.7183 * β * (L + 0.43) ≤ 1.7923 := by
            rw [hβ]; field_simp; nlinarith
          linarith
  have hsumx2 : ∑ j ∈ J, x j ^ 2 / (2 * (1 - x j)) ≤ 7.57 := by
    calc ∑ j ∈ J, x j ^ 2 / (2 * (1 - x j))
        ≤ ∑ j ∈ J, 10 / 9 * (3 * (Real.log (P.p j) / P.p j ^ 2)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨h0, h1⟩ := hxb j hj
          have : x j ^ 2 / (2 * (1 - x j)) ≤ 10 / 9 * x j ^ 2 := by
            rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (x j)]
          nlinarith [hx2 j hj]
      _ = 10 / 3 * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 7.57 := by linarith
  have hexp : ∑ j ∈ J, (x j + x j ^ 2 / (2 * (1 - x j))) ≤ Real.log L + 14 := by
    rw [Finset.sum_add_distrib]; linarith
  calc P.vSmooth (Real.exp ℓ) z = ∑ e ∈ S, 1 / P.val e := rfl
    _ ≤ ∑ e ∈ S, Real.exp (-(ℓ / L)) * P.val e ^ (-θ) := Finset.sum_le_sum hpt
    _ = Real.exp (-(ℓ / L)) * ∑ e ∈ S, P.val e ^ (-θ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ℓ / L)) * ∏ j ∈ J, (1 - P.p j ^ (-θ))⁻¹ :=
        mul_le_mul_of_nonneg_left hEu (Real.exp_pos _).le
    _ ≤ Real.exp (-(ℓ / L)) * Real.exp (Real.log L + 14) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hprod.trans (Real.exp_le_exp.mpr hexp)
    _ = Real.exp 14 * L * Real.exp (-(ℓ / L)) := by
        rw [Real.exp_add, Real.exp_log hL0]; ring

end HBS

end BeurlingSystem

end
