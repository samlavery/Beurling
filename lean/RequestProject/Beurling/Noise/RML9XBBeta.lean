module

public import RequestProject.Beurling.Noise.RML9XBRd

/-!
# Proposition 5.31(iii): the window sums of `R(d)` at the small cofactors

* `exp4_le`, `tail_num` : numerics (`(J+3)·2.2181·e^{4-0.002J} ≤ e^{-Λ}/J` for `J ≥ 600Λ⁴`);
* `tail_hord` : `∑_{m, log m > L} H_ord(m) m^{ε-2} ≤ 2.2181 e^{-0.04 L}` (from `A₀(ε+0.04)`);
* `Rdwin_bound` : for `1 ≤ w ≤ W₁ = e^{100}`, by (TVD-sums) and Lemma 5.32 (`SD_le_SI`),
  `∑_{V(d) ∈ (N/w)[1∓1.7δ]} R(d) ≤ 250δ((Λ + log w + 1.4)(1 + A₀) + A₁)/J + e^{-Λ}/J`,
  `A₀ = 2.0674`, `A₁ = 9.4091` (Corollary 5.17 constants, `hordSumsB`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma exp4_le : Real.exp 4 ≤ 55 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  calc Real.exp 1 ^ 4 ≤ 2.72 ^ 4 := pow_le_pow_left₀ h0.le (by linarith) 4
    _ ≤ 55 := by norm_num

/-- `(J + 3) · 2.2181 · e^{4 - 0.002 J} ≤ e^{-Λ}/J` for `J ≥ 600Λ⁴`, `Λ ≥ 10⁸`. -/
lemma tail_num {Λ J : ℝ} (hΛ : 100000000 ≤ Λ) (hJ : 600 * Λ ^ 4 ≤ J) :
    (J + 3) * 2.2181 * Real.exp (4 - 0.002 * J) ≤ Real.exp (-Λ) / J := by
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hΛ2 : 100000000 * Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ24 : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hJ0 : 0 < J := by nlinarith
  set x := 0.001 * J with hx
  have hx0 : 0 ≤ x := by positivity
  have hxΛ : Λ ≤ x := by nlinarith
  have hxbig : 2000000000 ≤ x := by nlinarith
  have h3 : x ^ 3 / 6 ≤ Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx0 3
    simpa [Nat.factorial] using this
  have hex : Real.exp Λ ≤ Real.exp x := Real.exp_le_exp.mpr hxΛ
  have e1 : Real.exp (4 - 0.002 * J) = Real.exp 4 / (Real.exp x * Real.exp x) := by
    rw [← Real.exp_add, ← Real.exp_sub]; congr 1; rw [hx]; ring
  have e2 : Real.exp (-Λ) = 1 / Real.exp Λ := by rw [Real.exp_neg, one_div]
  rw [e1, e2, mul_div_assoc', div_le_div_iff₀ (by positivity) hJ0,
    one_div_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]
  have hJx : J = 1000 * x := by rw [hx]; ring
  have h4 := exp4_le
  have hpos := Real.exp_pos x
  -- `(J+3)·2.2181·e⁴·J·e^Λ ≤ e^x·e^x`
  have hA : (J + 3) * 2.2181 * Real.exp 4 * J ≤ x ^ 3 / 6 := by
    rw [hJx]
    have : (1000 * x + 3) * 2.2181 * Real.exp 4 * (1000 * x) ≤
        (1000 * x + 3) * 2.2181 * 55 * (1000 * x) := by gcongr
    refine this.trans ?_
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have h5 : 2000000000 * x ^ 2 ≤ x ^ 3 := by
      have := mul_le_mul_of_nonneg_right hxbig hx2
      nlinarith
    nlinarith
  have hB : 0 ≤ (J + 3) * 2.2181 * Real.exp 4 * J := by positivity
  calc (J + 3) * 2.2181 * Real.exp 4 * J * Real.exp Λ
      ≤ x ^ 3 / 6 * Real.exp x := mul_le_mul hA hex (Real.exp_pos _).le (by positivity)
    _ ≤ Real.exp x * Real.exp x := mul_le_mul_of_nonneg_right h3 hpos.le

open scoped Classical in
/-- **The tail of `A₀`**: `∑_{m ∈ Dset, L < log m} H_ord(m) m^{ε-2} ≤ 2.2181 e^{-0.04 L}`. -/
lemma tail_hord {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε : ℝ} (hε : ε ≤ 0.005) (hZ : 2 * y / X0m ≤ Z) (L : ℝ) :
    ∑ m ∈ Dset P X0m y, (if L < Real.log (Vl P m)
      then (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) else 0) ≤
      2.2181 * Real.exp (-(0.04 * L)) := by
  rw [← Finset.sum_filter]
  set s := (Dset P X0m y).filter (fun m => L < Real.log (Vl P m))
  have hs : ∀ m ∈ s, 2 ≤ m ∧ LemmaM.valN P.labelVal m ≤ 2 * y / X0m := fun m hm =>
    ⟨(mem_Dset.mp (Finset.mem_filter.mp hm).1).2, Dset_val_le (Finset.mem_filter.mp hm).1⟩
  have hA := hordA0_1955 P h hXm (ε := ε + 0.04) (by linarith) hZ s hs
  calc ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)
      ≤ ∑ m ∈ s, Real.exp (-(0.04 * L)) *
          ((BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (ε + 0.04 - 2)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hV := KR.valN_labelVal_pos P m
        have hL := (Finset.mem_filter.mp hm).2
        have e : Vl P m ^ (ε - 2) = Vl P m ^ (ε + 0.04 - 2) * Vl P m ^ (-0.04 : ℝ) := by
          rw [← Real.rpow_add hV]; ring_nf
        have hp : Vl P m ^ (-0.04 : ℝ) ≤ Real.exp (-(0.04 * L)) := by
          rw [Real.rpow_def_of_pos hV]
          exact Real.exp_le_exp.mpr (by nlinarith)
        rw [e]
        have h0 : 0 ≤ (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε + 0.04 - 2) :=
          mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hV.le _)
        calc (BSCert.X0Band.Hord m : ℝ) * (Vl P m ^ (ε + 0.04 - 2) * Vl P m ^ (-0.04 : ℝ))
            = ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε + 0.04 - 2)) *
                Vl P m ^ (-0.04 : ℝ) := by ring
          _ ≤ ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε + 0.04 - 2)) *
                Real.exp (-(0.04 * L)) := mul_le_mul_of_nonneg_left hp h0
          _ = _ := by ring
    _ = Real.exp (-(0.04 * L)) * ∑ m ∈ s,
          (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (ε + 0.04 - 2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-(0.04 * L)) * 2.2181 := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = _ := by ring

end KR.RML9

end
