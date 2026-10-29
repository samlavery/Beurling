module

public import RequestProject.Beurling.Noise.LemSiii
public import RequestProject.Beurling.Noise.LemSEuler

/-!
# Lemma 5.21(ii), last bound: Rankin's bound

`HBS.lemS_rankin` : for `log 3v ≥ 10⁸`, `u_y > log 3v` and `y/v ≤ Z`,
`ω_y(v) ≤ 5 (log 3v)^{1.65} e^{-u_y/2}`.

Proof (the paper's): with `z = 3v`, `L = log z`, `δ = 1/(2L)`, `θ = 1 - δ`, the cofactors are
`z`-smooth and `> Y = y/2v`, so `1/w ≤ Y^{-δ} w^{-θ}`, `Y^{-δ} = e^{-u_y/2}`, and
`∑ w^{-θ} ≤ ∏_{p ≤ z} (1 - p^{-θ})⁻¹ ≤ exp ∑ (x_p + x_p²/(2(1-x_p)))`, `x_p = p^{-θ}`. By
Lemma 5.1, `∑_{p ≤ z} 1/p ≤ log L + 4.13`, `∑ log p/p ≤ L + 0.43`, `∑ log p/p² ≤ 2.2`; this gives
`∑ x_p ≤ log L + 4.96` and `∑ x_p²/(2(1-x_p)) ≤ 3.25`, so the product is `≤ e^{8.3} L`, and
`e^{8.3} L ≤ 5 L^{1.65}` as `L ≥ 10⁸`.
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- Below `X₀⁻`, at most one generalized prime is `≤ 2`, namely `p₀ = 2`. -/
lemma primes_le_two_subset (h : P.HBS X0m Z η1 η2 ε1) (hZ : 2 ≤ Z) (z : ℝ) :
    (P.primesLe z).filter (fun j => ¬ 2 < P.p j) ⊆ {0} := by
  intro j hj
  rw [Finset.mem_filter] at hj
  have hle : P.p j ≤ 2 := le_of_not_gt hj.2
  have hX := h.X0m_ge
  have hq := h.ident (x := 2) (by linarith) hZ j (Or.inl hle)
  rw [hq] at hle
  have h2 : qp j ≤ 2 := by exact_mod_cast hle
  have hpr := (qp_prime j).two_le
  have : qp j = qp 0 := by
    rw [show qp 0 = 2 from Nat.nth_prime_zero_eq_two]; omega
  rw [Finset.mem_singleton]; exact qp_injective this

/-- `∑_{p ≤ z} 1/p ≤ log log z + 4.13` (Lemma 5.1(iv) from `2`, and `p₀ = 2`). -/
lemma sum_inv_p_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ : z ≤ Z) :
    ∑ j ∈ P.primesLe z, 1 / P.p j ≤ Real.log (Real.log z) + 4.13 := by
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe z) (fun j => 2 < P.p j)]
  have h1 := h.mertens_iv (y := 2) (x := z) le_rfl hz hzZ
  have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have h1' : ∑ j ∈ (P.primesLe z).filter (fun j => 2 < P.p j), 1 / P.p j ≤
      Real.log (Real.log z / Real.log 2) + 2.2 / Real.log 2 := by
    have := (abs_le.mp h1).2; linarith
  rw [Real.log_div hlz.ne' (by linarith)] at h1'
  have hll2 : -Real.log (Real.log 2) ≤ 0.4428 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / Real.log 2 by positivity)
    rw [Real.log_div (by norm_num) (by linarith), Real.log_one] at this
    have : 1 / Real.log 2 ≤ 1 / 0.6931 := one_div_le_one_div_of_le (by norm_num) hl2.le
    linarith
  have h22 : 2.2 / Real.log 2 ≤ 3.175 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : ∑ j ∈ (P.primesLe z).filter (fun j => ¬ 2 < P.p j), 1 / P.p j ≤ 1 / 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (primes_le_two_subset h (hz.trans hzZ) z)
      (fun j _ _ => (one_div_pos.mpr (P.p_pos j)).le)).trans ?_
    rw [Finset.sum_singleton]
    have : 2 ≤ P.p 0 := by
      have := h.ident (x := 2) (by linarith [h.X0m_ge]) (hz.trans hzZ) 0
      by_cases hp : P.p 0 ≤ 2
      · rw [this (Or.inl hp)]
        have h0 : qp 0 = 2 := Nat.nth_prime_zero_eq_two
        rw [h0]; norm_num
      · linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  linarith

/-- `∑_{p ≤ z} log p/p² ≤ 2.2` (the prime-power part of `S(z²)`, Lemma 5.1(ii), (iii)). -/
lemma sum_log_div_sq_le (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 1 ≤ z) (hzZ : z ^ 2 ≤ Z) :
    ∑ j ∈ P.primesLe z, Real.log (P.p j) / P.p j ^ 2 ≤ 2.2 := by
  have hz2 : 1 ≤ z ^ 2 := by nlinarith
  have hl := P.lemma_5_1 h hz2 hzZ
  have hrest := P.mertensS_eq_Sp_add (z ^ 2)
  have hsub : ∑ j ∈ P.primesLe z, Real.log (P.p j) / P.p j ^ 2 ≤
      ∑ jk ∈ (P.pps (z ^ 2)).filter (fun jk => 1 ≤ jk.2),
        Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) := by
    rw [← Finset.sum_image (f := fun jk : ℕ × ℕ => Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1))
      (s := P.primesLe z) (g := fun j => (j, 1)) (fun a _ b _ hab => by simpa using hab)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro jk hjk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
      rw [mem_primesLe] at hj
      simp only [Finset.mem_filter, mem_pps, le_refl, and_true]
      exact pow_le_pow_left₀ (P.p_pos j).le hj 2
    · intro jk _ _
      exact div_nonneg (P.log_p_nonneg _) (pow_pos (P.p_pos _) _).le
  linarith [hl.2.1.2, hl.2.2.1.1]

/-- `p^{-θ} ≤ 1/p + 1.65 δ log p/p` for `θ = 1 - δ`, `0 ≤ δ log p ≤ 1/2`. -/
lemma rpow_neg_le_lin {p δ : ℝ} (hp : 0 < p) (hl0 : 0 ≤ Real.log p) (hδ0 : 0 ≤ δ)
    (ha : δ * Real.log p ≤ 1 / 2) :
    p ^ (-(1 - δ)) ≤ 1 / p + 1.65 * δ * (Real.log p / p) := by
  have e1 : p ^ (-(1 - δ)) = Real.exp (δ * Real.log p) / p := by
    rw [Real.rpow_def_of_pos hp, show Real.log p * -(1 - δ) =
      δ * Real.log p - Real.log p by ring, Real.exp_sub, Real.exp_log hp]
  set a := δ * Real.log p with hadef
  have ha0 : 0 ≤ a := mul_nonneg hδ0 hl0
  have hea : Real.exp a ≤ 1 + 1.65 * a := by
    have h1 : Real.exp a * (1 - a) ≤ 1 := by
      have := Real.add_one_le_exp (-a)
      rw [Real.exp_neg] at this
      have hp' := Real.exp_pos a
      have : (Real.exp a)⁻¹ * Real.exp a = 1 := inv_mul_cancel₀ hp'.ne'
      nlinarith
    have h2 : Real.exp a ≤ 1.6488 := by
      have : Real.exp a ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr ha
      refine this.trans ?_
      have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h4 := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2)]
    nlinarith
  rw [e1, div_le_iff₀ hp]
  have : 1.65 * δ * (Real.log p / p) * p = 1.65 * a := by rw [hadef]; field_simp
  rw [add_mul, this, one_div_mul_cancel hp.ne']
  exact hea

/-- `(p^{-θ})² ≤ (1/log 2 + 6δ) log p/p²` for `θ = 1 - δ`, `p ≥ 2`, `0 ≤ 2δ log p ≤ 1`. -/
lemma rpow_neg_sq_le {p δ : ℝ} (hp2 : 2 ≤ p) (hδ0 : 0 ≤ δ) (hb : 2 * δ * Real.log p ≤ 1) :
    (p ^ (-(1 - δ))) ^ 2 ≤ (1 / Real.log 2 + 6 * δ) * (Real.log p / p ^ 2) := by
  have hp : 0 < p := by linarith
  have hlp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : (p ^ (-(1 - δ))) ^ 2 = Real.exp (2 * δ * Real.log p) / p ^ 2 := by
    rw [Real.rpow_def_of_pos hp, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) *
      (Real.log p * -(1 - δ)) = 2 * δ * Real.log p - 2 * Real.log p by push_cast; ring,
      Real.exp_sub, show 2 * Real.log p = Real.log (p ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  set a := 2 * δ * Real.log p with hadef
  have ha0 : 0 ≤ a := by have := Real.log_nonneg (show (1 : ℝ) ≤ p by linarith); positivity
  have hE : Real.exp a ≤ 1 + 3 * a := by
    have h1 : Real.exp a * (1 - a) ≤ 1 := by
      have := Real.add_one_le_exp (-a)
      rw [Real.exp_neg] at this
      have hp' := Real.exp_pos a
      have : (Real.exp a)⁻¹ * Real.exp a = 1 := inv_mul_cancel₀ hp'.ne'
      nlinarith
    have h2 : Real.exp a ≤ 3 := by
      have := Real.exp_le_exp.mpr hb
      have h4 := Real.exp_one_lt_d9
      linarith
    nlinarith
  rw [e1]
  have hq : 0 < p ^ 2 := by positivity
  have h1 : 1 ≤ Real.log p / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  have h2 : 1 + 3 * a ≤ (1 / Real.log 2 + 6 * δ) * Real.log p := by
    have e : (1 / Real.log 2 + 6 * δ) * Real.log p = Real.log p / Real.log 2 + 3 * a := by
      rw [hadef]; field_simp; ring
    rw [e]; linarith
  rw [div_le_iff₀ hq]
  have : (1 / Real.log 2 + 6 * δ) * (Real.log p / p ^ 2) * p ^ 2 =
      (1 / Real.log 2 + 6 * δ) * Real.log p := by field_simp
  rw [this]
  linarith

/-- `e^{8.3} L ≤ 5 L^{1.65}` for `L ≥ 10⁸`. -/
lemma exp82_le {L : ℝ} (hL : 100000000 ≤ L) :
    Real.exp (Real.log L + 8.3) ≤ 5 * L ^ (1.65 : ℝ) := by
  have hL0 : 0 < L := by linarith
  rw [Real.exp_add, Real.exp_log hL0]
  have h82 : Real.exp 8.3 ≤ 5000 := by
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
  have hL65 : 1000 ≤ L ^ (0.65 : ℝ) := by
    have h1 : L ^ (1 / 2 : ℝ) ≤ L ^ (0.65 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : L ^ (1 / 2 : ℝ) = √L := (Real.sqrt_eq_rpow L).symm
    have h3 : 10000 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
    linarith
  have e : L ^ (1.65 : ℝ) = L * L ^ (0.65 : ℝ) := by
    rw [show (1.65 : ℝ) = 1 + 0.65 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  rw [e]
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Lemma 5.21(ii), Rankin's bound**: `LemSRankin` holds. -/
theorem lemS_rankin (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) :
    P.LemSRankin Z t v := by
  intro y hy hyZ hu
  set z := 3 * v with hzdef
  set L := Real.log z with hLdef
  have hL0 : 0 < L := by linarith
  set Y := y / (2 * v) with hYdef
  have hY0 : 0 < Y := by positivity
  set u := uY y v with hudef
  have hlogY : Real.log Y = u * L := by
    rw [hudef, uY, div_mul_cancel₀ _ hL0.ne']
  have hz1 : 1 < z := by
    by_contra hc; push_neg at hc
    have : Real.log z ≤ 0 := Real.log_nonpos (by positivity) hc
    linarith
  have hz0 : 0 < z := by linarith
  -- horizons
  have huL : L ^ 2 < Real.log Y := by rw [hlogY]; nlinarith
  have hzZ : z ^ 2 ≤ Z := by
    have h1 : Real.log (z ^ 2) < Real.log Y := by
      rw [Real.log_pow]; push_cast; nlinarith
    have h2 : z ^ 2 < Y := (Real.log_lt_log_iff (by positivity) hY0).mp h1
    have h3 : Y ≤ y / v := by
      rw [hYdef, div_le_div_iff₀ (by positivity) hv]; nlinarith
    linarith
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
  -- Step 1: `ω ≤ Y^{-δ} ∑ w^{-θ}`
  set S := (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z)
  have hω : P.omegaW t y v ≤ ∑ e ∈ S, 1 / P.val e := omegaW_le_vSmooth hd y hv
  have hpt : ∀ e ∈ S, 1 / P.val e ≤ Real.exp (-(u / 2)) * P.val e ^ (-θ) := by
    intro e he
    have hYv := (Finset.mem_filter.mp he).2.1
    have hv0 := P.val_pos e
    have e1 : 1 / P.val e = P.val e ^ (-δ) * P.val e ^ (-θ) := by
      rw [← Real.rpow_add hv0, hθ, show -δ + -(1 - δ) = (-1 : ℝ) by ring, Real.rpow_neg_one,
        one_div]
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : P.val e ^ (-δ) ≤ Y ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hY0 hYv.le (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos hY0, hlogY, hδ]
    congr 1; field_simp
  -- Step 2: the Euler product
  set J := P.primesLe z
  have hSJ : ∀ e ∈ S, e.support ⊆ J := by
    intro e he j hj
    rw [P.mem_primesLe]; exact (Finset.mem_filter.mp he).2.2 j hj
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
  have hs3 := sum_log_div_sq_le h (by linarith) hzZ
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
  have hfinal := exp82_le hL
  calc P.omegaW t y v ≤ ∑ e ∈ S, 1 / P.val e := hω
    _ ≤ ∑ e ∈ S, Real.exp (-(u / 2)) * P.val e ^ (-θ) := Finset.sum_le_sum hpt
    _ = Real.exp (-(u / 2)) * ∑ e ∈ S, P.val e ^ (-θ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(u / 2)) * ∏ j ∈ J, (1 - P.p j ^ (-θ))⁻¹ :=
        mul_le_mul_of_nonneg_left hEu (Real.exp_pos _).le
    _ ≤ Real.exp (-(u / 2)) * Real.exp (Real.log L + 8.3) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hprod.trans (Real.exp_le_exp.mpr hexp)
    _ ≤ Real.exp (-(u / 2)) * (5 * L ^ (1.65 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfinal (Real.exp_pos _).le
    _ = 5 * Real.log (3 * v) ^ (1.65 : ℝ) * Real.exp (-(uY y v / 2)) := by ring

end HBS

end BeurlingSystem

end
