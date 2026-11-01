module

public import RequestProject.Beurling.Noise.TauNearLocMain
public import RequestProject.Beurling.Noise.LemSRankin

/-!
# Lemma 5.20's blocks with the weight `(log 3v)²` (round 12, sizes of Lemma 5.34)

The block majorant `s_η(v) = blk_K(v)` of Lemma 5.20 (`TauNearProofBlk.blk`, with `Ψ = 1`) is
summed against `(log 3v)²` over a `2`-separated family of scales (the dyadic blocks
`v_i = X₀⁻2ⁱ` of `Gsum`, `SK`). The new input is the second moment of the smooth harmonic sum:

* `prod_rankin_le` : `∏_{p ≤ z} (1 - p^{-θ})⁻¹ ≤ 5000 log z`, `θ = 1 - 1/(2 log z)` (Rankin, as in
  `lemS_rankin`, at the cofactor horizon `z ≤ Z` via `sum_log_div_sq_loc`);
* `smooth_logsq_le` : `∑_{m ∈ S} (log m)²/m ≤ 80000 (log z)³` for `z`-smooth `S`
  (`(log m)² ≤ 16 L² m^{1/(2L)}`);
* `scale_logsq_le` : `∑_{v} (log 3v)² ∑_{m ∈ SmB_k(v)} 1/m ≤ 6·10⁵ (log 3P_k)³`;
* `sum_blk_logsq_le` : `∑_v (log 3v)² blk_K(v) ≤ 7·10⁷ Φ₃(X₀⁻/2)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML12

open KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

lemma exp83_le : Real.exp 8.3 ≤ 5000 := by
  have h1 : Real.exp 8.3 = Real.exp 1 ^ 8 * Real.exp 0.3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 0.3 ≤ 1 / (1 - 0.3) := by
    have := Real.add_one_le_exp (-0.3)
    rw [Real.exp_neg] at this
    have hp := Real.exp_pos 0.3
    rw [le_div_iff₀ (by norm_num)]
    have : (Real.exp 0.3)⁻¹ * Real.exp 0.3 = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith
  rw [h1]
  have h4 : Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 8
  have := Real.exp_pos 0.3
  calc Real.exp 1 ^ 8 * Real.exp 0.3 ≤ 2.7182818286 ^ 8 * (1 / (1 - 0.3)) :=
        mul_le_mul h4 h3 this.le (by norm_num)
    _ ≤ 5000 := by norm_num

set_option maxHeartbeats 2000000 in
/-- **Rankin's Euler product at the cofactor horizon**: for `2 ≤ z ≤ Z`, `2500 ≤ Z`,
`L = log z ≥ 10⁷` and `θ = 1 - 1/(2L)`, `∏_{p ≤ z} (1 - p^{-θ})⁻¹ ≤ 5000 L`. -/
theorem prod_rankin_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz2 : 2 ≤ z) (hzZ : z ≤ Z)
    (hZ : 2500 ≤ Z) (hL : 10000000 ≤ Real.log z) :
    ∏ j ∈ P.primesLe z, (1 - P.p j ^ (-(1 - 1 / (2 * Real.log z))))⁻¹ ≤
      5000 * Real.log z := by
  set L := Real.log z with hLdef
  have hL0 : 0 < L := by linarith
  set δ := 1 / (2 * L) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδs : δ ≤ 0.0000001 := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  set θ' := 1 - δ with hθ
  set J := P.primesLe z
  set x : ℕ → ℝ := fun j => P.p j ^ (-θ') with hxdef
  have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hxb : ∀ j ∈ J, 0 ≤ x j ∧ x j ≤ 0.51 := by
    intro j hj
    have hp2 : 2 ≤ P.p j := h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ)
    refine ⟨by have := P.p_pos j; positivity, ?_⟩
    have : P.p j ^ (-θ') ≤ 2 ^ (-θ') :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    refine this.trans ?_
    rw [hθ, show -(1 - δ) = -1 + δ by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    have hd2 : (2 : ℝ) ^ δ ≤ 1.0001 := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have : Real.log 2 * δ ≤ 1 / 10000000 := by nlinarith [Real.log_two_lt_d9]
      refine (Real.exp_le_exp.mpr this).trans ?_
      have hb := Real.exp_bound' (x := (1 / 10000000 : ℝ)) (by norm_num) (by norm_num) (n := 2)
        (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hb
      linarith
    nlinarith
  have hprod := LemS.prod_inv_le_exp J x (fun j hj => ⟨(hxb j hj).1, by linarith [(hxb j hj).2]⟩)
  have hs1 := h.sum_inv_p_le hz2 hzZ
  have hs2 : P.Sp z ≤ L + 0.43 := by
    have := (P.lemma_5_1 h (by linarith) hzZ).2.2.1.2; linarith
  have hs3 := sum_log_div_sq_loc h (by linarith) hzZ hZ
  have hlogp : ∀ j ∈ J, 0 ≤ Real.log (P.p j) ∧ Real.log (P.p j) ≤ L := fun j hj =>
    ⟨P.log_p_nonneg j, Real.log_le_log (P.p_pos j) (P.mem_primesLe.mp hj)⟩
  have hx1 : ∀ j ∈ J, x j ≤ 1 / P.p j + 1.65 * δ * (Real.log (P.p j) / P.p j) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    refine HBS.rpow_neg_le_lin (P.p_pos j) hl0 hδ0.le ?_
    rw [hδ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hx2 : ∀ j ∈ J, x j ^ 2 ≤ (1 / Real.log 2 + 6 * δ) * (Real.log (P.p j) / P.p j ^ 2) := by
    intro j hj
    obtain ⟨hl0, hlL⟩ := hlogp j hj
    have hp2 : 2 ≤ P.p j := h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ)
    refine HBS.rpow_neg_sq_le hp2 hδ0.le ?_
    have : 2 * δ * Real.log (P.p j) ≤ 2 * δ * L := mul_le_mul_of_nonneg_left hlL (by positivity)
    have h2 : 2 * δ * L = 1 := by rw [hδ]; field_simp
    linarith
  have hsumx : ∑ j ∈ J, x j ≤ Real.log L + 4.13 + 1.65 * δ * (L + 0.43) := by
    calc ∑ j ∈ J, x j ≤ ∑ j ∈ J, (1 / P.p j + 1.65 * δ * (Real.log (P.p j) / P.p j)) :=
          Finset.sum_le_sum hx1
      _ = ∑ j ∈ J, 1 / P.p j + 1.65 * δ * P.Sp z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
      _ ≤ Real.log L + 4.13 + 1.65 * δ * (L + 0.43) := by
          have : 1.65 * δ * P.Sp z ≤ 1.65 * δ * (L + 0.43) :=
            mul_le_mul_of_nonneg_left hs2 (by positivity)
          linarith
  have hsumx2 : ∑ j ∈ J, x j ^ 2 / (2 * (1 - x j)) ≤ 3.33 := by
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
      _ ≤ 1.0205 * 1.4428 * 2.2568 := by
          have h0 : 0 ≤ ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 :=
            Finset.sum_nonneg fun j _ => div_nonneg (P.log_p_nonneg j) (by positivity)
          have : 0 ≤ 1 / Real.log 2 + 6 * δ := by positivity
          calc 1.0205 * (1 / Real.log 2 + 6 * δ) * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2
              ≤ 1.0205 * 1.4428 * ∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2 := by gcongr
            _ ≤ 1.0205 * 1.4428 * 2.2568 := by gcongr
      _ ≤ 3.33 := by norm_num
  have hexp : ∑ j ∈ J, (x j + x j ^ 2 / (2 * (1 - x j))) ≤ Real.log L + 8.3 := by
    rw [Finset.sum_add_distrib]
    have : 1.65 * δ * (L + 0.43) ≤ 0.83 := by
      rw [hδ]; field_simp; nlinarith
    linarith
  calc ∏ j ∈ J, (1 - P.p j ^ (-(1 - 1 / (2 * L))))⁻¹ = ∏ j ∈ J, (1 - x j)⁻¹ := rfl
    _ ≤ Real.exp (Real.log L + 8.3) := hprod.trans (Real.exp_le_exp.mpr hexp)
    _ = Real.exp 8.3 * L := by rw [Real.exp_add, Real.exp_log hL0]; ring
    _ ≤ 5000 * L := mul_le_mul_of_nonneg_right exp83_le hL0.le

/-- `(log m)² ≤ 16 L² m^{1/(2L)}` for `m ≥ 1`, `L > 0`. -/
lemma logsq_le_rpow {m L : ℝ} (hm : 1 ≤ m) (hL : 0 < L) :
    Real.log m ^ 2 ≤ 16 * L ^ 2 * m ^ (1 / (2 * L)) := by
  have hm0 : 0 < m := by linarith
  have hl0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have h1 := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < 1 / (4 * L) by positivity)
  have e1 : m ^ (1 / (4 * L)) / (1 / (4 * L)) = 4 * L * m ^ (1 / (4 * L)) := by
    field_simp
  rw [e1] at h1
  have e2 : m ^ (1 / (2 * L)) = (m ^ (1 / (4 * L))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; congr 1; push_cast; field_simp; ring
  rw [e2]
  have : Real.log m ^ 2 ≤ (4 * L * m ^ (1 / (4 * L))) ^ 2 := pow_le_pow_left₀ hl0 h1 2
  nlinarith

/-- **The second moment of the smooth harmonic sum**: for `z`-smooth `S`, `2 ≤ z ≤ Z`,
`2500 ≤ Z`, `log z ≥ 10⁷`: `∑_{m ∈ S} (log m)²/m ≤ 80000 (log z)³`. -/
theorem smooth_logsq_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz2 : 2 ≤ z) (hzZ : z ≤ Z)
    (hZ : 2500 ≤ Z) (hL : 10000000 ≤ Real.log z) (S : Finset (ℕ →₀ ℕ))
    (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) :
    ∑ e ∈ S, Real.log (P.val e) ^ 2 / P.val e ≤ 80000 * Real.log z ^ 3 := by
  set L := Real.log z with hLdef
  have hL0 : 0 < L := by linarith
  have hθ0 : 0 < 1 - 1 / (2 * L) := by
    have : 1 / (2 * L) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hpt : ∀ e ∈ S, Real.log (P.val e) ^ 2 / P.val e ≤
      16 * L ^ 2 * P.val e ^ (-(1 - 1 / (2 * L))) := by
    intro e _
    have hv1 := P.one_le_val e
    have hv0 := P.val_pos e
    have h1 := logsq_le_rpow hv1 hL0
    have e1 : P.val e ^ (1 / (2 * L)) / P.val e = P.val e ^ (-(1 - 1 / (2 * L))) := by
      rw [show -(1 - 1 / (2 * L)) = 1 / (2 * L) + (-1) by ring, Real.rpow_add hv0,
        Real.rpow_neg_one, div_eq_mul_inv]
    calc Real.log (P.val e) ^ 2 / P.val e ≤ 16 * L ^ 2 * P.val e ^ (1 / (2 * L)) / P.val e :=
          div_le_div_of_nonneg_right h1 hv0.le
      _ = 16 * L ^ 2 * P.val e ^ (-(1 - 1 / (2 * L))) := by rw [mul_div_assoc, e1]
  have hsupp : ∀ e ∈ S, e.support ⊆ P.primesLe z := fun e he i hi => by
    rw [mem_primesLe]; exact hS e he i hi
  have hE := P.sum_rpow_le_euler hθ0 (P.primesLe z) S hsupp
  have hR := prod_rankin_le h hz2 hzZ hZ hL
  calc ∑ e ∈ S, Real.log (P.val e) ^ 2 / P.val e
      ≤ ∑ e ∈ S, 16 * L ^ 2 * P.val e ^ (-(1 - 1 / (2 * L))) := Finset.sum_le_sum hpt
    _ = 16 * L ^ 2 * ∑ e ∈ S, P.val e ^ (-(1 - 1 / (2 * L))) := by rw [Finset.mul_sum]
    _ ≤ 16 * L ^ 2 * (5000 * L) :=
        mul_le_mul_of_nonneg_left (hE.trans hR) (by positivity)
    _ = 80000 * L ^ 3 := by ring

/-- `∑_{m ∈ U_k} (log m)²/m ≤ 80000 (log 3P_k)³`. -/
theorem U_logsq_loc (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hZ0 : 2500 ≤ Z)
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (k : ℕ) :
    ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) ^ 2 / P.val e ≤
      80000 * Real.log (3 * Pk X0m k) ^ 3 := by
  have hX := h.width.X0m_pos
  have hk1 := Pk_ge_one hX h.hXm k
  have hlk := log_Pk_ge hX h.hXm k
  have hl3 : Real.log (Pk X0m k) ≤ Real.log (3 * Pk X0m k) :=
    Real.log_le_log (by linarith) (by linarith)
  rcases (Sc.biUnion (SmB P X0m k)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
  · exact smooth_logsq_le h.hbs (by linarith) (U_horizon_loc hX hZ0 hZ k hne) hZ0
      (by linarith) _ (U_smooth hX k)

/-- **The `(log 3v)²`-weighted scale sum** at one level `k` of Lemma 5.20. -/
theorem scale_logsq_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ0 : 2500 ≤ Z) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (k : ℕ) :
    ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * ∑ e ∈ SmB P X0m k v, 1 / P.val e ≤
      600000 * Real.log (3 * Pk X0m k) ^ 3 := by
  have hX := h.width.X0m_pos
  have hk1 := Pk_ge_one hX h.hXm k
  have hk0 := Pk_pos hX k
  set a := Real.log (12 * Pk X0m k ^ 2) with ha
  set L' := Real.log (3 * Pk X0m k) with hL'
  have hL'0 : 0 ≤ L' := Real.log_nonneg (by linarith)
  have hlP : 0 ≤ Real.log (Pk X0m k) := Real.log_nonneg hk1
  have ha3 : a ≤ 3 * L' := by
    rw [ha, hL', Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num)
      hk0.ne', Real.log_pow]
    have h12 : Real.log 12 ≤ 3 * Real.log 3 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    push_cast; linarith
  have ha0 : 0 ≤ a := Real.log_nonneg (by nlinarith)
  have hsc := scale_sum (P := P) hX hS k (L := fun v => Real.log (3 * v) ^ 2)
    (Lb := fun m => (a + Real.log m) ^ 2) (fun v _ => sq_nonneg _) (by
      intro v hv e he
      simp only [SmB, Finset.mem_filter] at he
      have h1 := he.2.1
      have hv1 := hSc v hv
      have hve := P.val_pos e
      rw [div_lt_iff₀ (by positivity)] at h1
      have hl0 : 0 ≤ Real.log (3 * v) := Real.log_nonneg (by linarith)
      have hlt : Real.log (3 * v) ≤ a + Real.log (P.val e) := by
        rw [ha, ← Real.log_mul (by positivity) hve.ne']
        exact Real.log_le_log (by linarith) (by nlinarith)
      exact pow_le_pow_left₀ hl0 hlt 2)
  have hH := U_harm_loc h.hbs h.width hZ0 hZ k hk1
  have hLs := U_logsq_loc h hZ0 hZ k
  have hU : ∑ e ∈ Sc.biUnion (SmB P X0m k), (a + Real.log (P.val e)) ^ 2 / P.val e ≤
      2 * a ^ 2 * ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e +
        2 * ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) ^ 2 / P.val e := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hve := P.val_pos e
    rw [show 2 * a ^ 2 * (1 / P.val e) + 2 * (Real.log (P.val e) ^ 2 / P.val e) =
      (2 * a ^ 2 + 2 * Real.log (P.val e) ^ 2) / P.val e by ring]
    apply div_le_div_of_nonneg_right _ hve.le
    nlinarith [sq_nonneg (a - Real.log (P.val e))]
  have ha2 : a ^ 2 ≤ 9 * L' ^ 2 := by nlinarith
  calc ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * ∑ e ∈ SmB P X0m k v, 1 / P.val e
      ≤ 3 * ∑ e ∈ Sc.biUnion (SmB P X0m k), (a + Real.log (P.val e)) ^ 2 / P.val e := hsc
    _ ≤ 3 * (2 * (9 * L' ^ 2) * (1810 * L') + 2 * (80000 * L' ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine hU.trans ?_
        have h0 : 0 ≤ ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e :=
          Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le
        gcongr
    _ ≤ 600000 * L' ^ 3 := by nlinarith [pow_nonneg hL'0 3]

/-- **Lemma 5.20's block majorant against `(log 3v)²`**: for a `2`-separated family of scales
`v ≥ 1` with `18 v ≤ Z²`, `∑_v (log 3v)² s_η(v) ≤ 7·10⁷ Φ₃(X₀⁻/2)`, `s_η = blk_K(·)` (`Ψ = 1`). -/
theorem sum_blk_logsq_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ0 : 2500 ≤ Z) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (K : ℕ) :
    ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * blk P H X0m K (fun _ => 1) v ≤
      70000000 * Phi H 3 (X0m / 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  unfold blk
  have eswap : ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * ∑ k ∈ range K, 56 * H (Pk X0m k) * 1 /
      Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e = ∑ k ∈ range K, ∑ v ∈ Sc,
        Real.log (3 * v) ^ 2 * (56 * H (Pk X0m k) * 1 / Pk X0m k *
          ∑ e ∈ SmB P X0m k v, 1 / P.val e) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.mul_sum _ _ _
  rw [eswap]
  have hk : ∀ k ∈ range K, ∑ v ∈ Sc, Real.log (3 * v) ^ 2 *
      (56 * H (Pk X0m k) * 1 / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e) ≤
      33600000 * Phi H 3 (Pk X0m k) := by
    intro k _
    have hk0 := Pk_pos hX k
    have hk1 := Pk_ge_one hX h.hXm k
    have hH0 := (hP.reg.pos (Pk X0m k)).le
    have hc0 : 0 ≤ 56 * H (Pk X0m k) * 1 / Pk X0m k := by positivity
    have e : ∑ v ∈ Sc, Real.log (3 * v) ^ 2 *
        (56 * H (Pk X0m k) * 1 / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e) =
        56 * H (Pk X0m k) * 1 / Pk X0m k *
          ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * ∑ e ∈ SmB P X0m k v, 1 / P.val e := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by ring
    rw [e]
    have h1 := scale_logsq_le h hS hSc hZ0 hZ k
    have hl3 : Real.log (3 * Pk X0m k) ≤ Real.log (Pk X0m k) + 2 := by
      rw [Real.log_mul (by norm_num) hk0.ne']
      have : Real.log 3 < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have := Real.exp_one_gt_d9
        have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e2]; nlinarith
      linarith
    have hl30 : 0 ≤ Real.log (3 * Pk X0m k) := Real.log_nonneg (by linarith)
    have hcube : Real.log (3 * Pk X0m k) ^ 3 ≤ (Real.log (Pk X0m k) + 2) ^ 3 :=
      pow_le_pow_left₀ hl30 hl3 3
    unfold Phi
    calc 56 * H (Pk X0m k) * 1 / Pk X0m k *
          ∑ v ∈ Sc, Real.log (3 * v) ^ 2 * ∑ e ∈ SmB P X0m k v, 1 / P.val e
        ≤ 56 * H (Pk X0m k) * 1 / Pk X0m k * (600000 * (Real.log (Pk X0m k) + 2) ^ 3) :=
          mul_le_mul_of_nonneg_left (h1.trans (by nlinarith)) hc0
      _ = 33600000 * (H (Pk X0m k) * (Real.log (Pk X0m k) + 2) ^ 3 / Pk X0m k) := by
          field_simp; ring
  have hd := decay_sum hP h.hXm (a := 3) le_rfl K
  rw [Pk_zero] at hd
  have hphi := Phi_nonneg hP 3 (le_refl (X0m / 2)) (by
    have := Pk_ge_one hX h.hXm 0; rwa [Pk_zero] at this)
  calc ∑ k ∈ range K, ∑ v ∈ Sc, Real.log (3 * v) ^ 2 *
        (56 * H (Pk X0m k) * 1 / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e)
      ≤ ∑ k ∈ range K, 33600000 * Phi H 3 (Pk X0m k) := Finset.sum_le_sum hk
    _ = 33600000 * ∑ k ∈ range K, Phi H 3 (Pk X0m k) := by rw [Finset.mul_sum]
    _ ≤ 33600000 * (2.05 * Phi H 3 (X0m / 2)) := by gcongr
    _ ≤ 70000000 * Phi H 3 (X0m / 2) := by nlinarith

end KR.RML12

end
