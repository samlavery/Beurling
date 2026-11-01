module

public import RequestProject.Beurling.Noise.LemSMain

/-!
# Proposition 5.38, Step 4: `log t · S(t) ≤ E_S`

The source term of the variation recursion (Step 3) is

  `S(t) = o_t + 2η(t) + 2 ∑_w (κ_w/w) ε_{1.02H(t)/w}(t/w)/H(t/w) + 1.0001 ∑_w (κ_w/w) δ(t/w)`,

and Lemma 5.22 gives `ε/H ≤ 2ν̂`, so the last two terms are at most `4 ∑_{v'} ω_t(v') ν̂(v')` and
`1.0001 ∑_{v'} ω_t(v') sup_{[v',2v')} δ` over dyadic scales `v'`, with the filtered cofactor
weights `ω_t(v')` of Lemma 5.21.

* `Margin.Var.one_add_mul_rho_le` : `(1 + u) ρ(u) ≤ 2`;
* `Margin.Var.logt_omega_le` : **the bullets of Step 4**: `log t · ω_t(v') ≤ 2.9 log(3v')` for
  every scale with `log 3v' ≥ 10⁸`, from Lemma 5.21 (i)–(ii) (`HBS.lemma_5_21`). The paper has
  `4.3` (from `2.4` and `4.2`);
* `Margin.Var.step4` : the assembly `log t · S(t) ≤ E_S` with
  `E_S = sup log v·o_v + 2 sup log y·η(y) + 27 ∑ log(3v) ν̂(v) + E_δ`,
  `E_δ = 4.3 ∑ log(3v) sup δ`.
-/

@[expose] public section

open Finset Real

namespace Margin.Var

/-- `(1 + u) ρ(u) ≤ 2` (`ρ(u) ≤ 1/u` for `u ≥ 1`, `ρ = 1` below `1`). -/
lemma one_add_mul_rho_le (u : ℝ) : (1 + u) * Dickman.rho u ≤ 2 := by
  rcases le_or_gt 1 u with h1 | h1
  · have h := Dickman.rho_le_inv h1
    have h0 := Dickman.rho_pos u
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  · rw [Dickman.rho_of_le_one h1.le]; linarith

lemma one_add_exp_le {u : ℝ} (hu : 30 < u) :
    (1 + u) * Real.exp (-(0.7 * u * Real.log u)) ≤ 1 := by
  have hlog : 3 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h.le 3
    norm_num at this; linarith
  have h1 : Real.log (1 + u) ≤ 0.7 * u * Real.log u := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
    nlinarith
  calc (1 + u) * Real.exp (-(0.7 * u * Real.log u))
      = Real.exp (Real.log (1 + u) - 0.7 * u * Real.log u) := by
        rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

lemma rankin_small {L u : ℝ} (hL : 100000000 ≤ L) (hu : L < u) :
    (1 + u) * (5 * L ^ (1.65 : ℝ) * Real.exp (-(u / 2))) ≤ 1 := by
  have hu0 : 0 < u := by linarith
  have hLu : L ^ (1.65 : ℝ) ≤ u ^ 2 := by
    calc L ^ (1.65 : ℝ) ≤ L ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = L ^ 2 := by norm_cast
      _ ≤ u ^ 2 := pow_le_pow_left₀ (by linarith) hu.le 2
  have he : (u / 2) ^ 4 / 24 ≤ Real.exp (u / 2) := by
    have := Real.pow_div_factorial_le_exp (x := u / 2) (by positivity) 4
    norm_num [Nat.factorial] at this ⊢; linarith
  have hk : 5 * (1 + u) * u ^ 2 ≤ (u / 2) ^ 4 / 24 := by
    have hu8 : 100000000 ≤ u := by linarith
    have hu3 : 0 ≤ u ^ 3 := by positivity
    have h1 : 100000000 * u ^ 3 ≤ u ^ 4 := by
      have := mul_le_mul_of_nonneg_right hu8 hu3
      nlinarith
    have h2 : 5 * (1 + u) * u ^ 2 ≤ 10 * u ^ 3 := by nlinarith
    nlinarith
  have hexp := Real.exp_pos (u / 2)
  rw [Real.exp_neg]
  have hL0 : 0 ≤ L ^ (1.65 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc (1 + u) * (5 * L ^ (1.65 : ℝ) * (Real.exp (u / 2))⁻¹)
      = 5 * (1 + u) * L ^ (1.65 : ℝ) / Real.exp (u / 2) := by field_simp
    _ ≤ 5 * (1 + u) * u ^ 2 / Real.exp (u / 2) := by
        apply div_le_div_of_nonneg_right _ hexp.le
        exact mul_le_mul_of_nonneg_left hLu (by positivity)
    _ ≤ 1 := by rw [div_le_one hexp]; linarith

variable {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- **Step 4, the bullets**: `log t · ω_t(v') ≤ 2.9 log(3v')` (paper: `4.3 log 3v'`). -/
theorem logt_omega_le (h : P.HBS X0m Z η1 η2 ε1) {tw : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall tw v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {t : ℝ}
    (ht : 0 < t) (hZ : t / v ≤ Z) :
    Real.log t * P.omegaW tw t v ≤ 2.9 * Real.log (3 * v) := by
  obtain ⟨hi, -, hii, hiii, hR, -⟩ := h.lemma_5_21 hd hv hL
  set L := Real.log (3 * v)
  set u := BeurlingSystem.HBS.uY t v
  have hL0 : 0 < L := by linarith
  have hω0 : 0 ≤ P.omegaW tw t v :=
    Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le
  -- `log t ≤ (1 + u) L`
  have hlt : Real.log t ≤ (1 + u) * L := by
    have e1 : Real.log t = Real.log (t / (2 * v)) + Real.log (2 * v) := by
      rw [Real.log_div ht.ne' (by positivity)]; ring
    have e2 : Real.log (t / (2 * v)) = u * L := by
      simp only [u, BeurlingSystem.HBS.uY]; rw [div_mul_cancel₀ _ hL0.ne']
    have e3 : Real.log (2 * v) ≤ L := Real.log_le_log (by positivity) (by linarith)
    linarith
  rcases le_or_gt (Real.log t) 0 with hneg | hpos
  · nlinarith
  have hu1 : -1 < u := by
    by_contra hc; push_neg at hc; nlinarith
  have hmul : Real.log t * P.omegaW tw t v ≤ (1 + u) * L * P.omegaW tw t v :=
    mul_le_mul_of_nonneg_right hlt hω0
  rcases le_or_gt u 30 with h30 | h30
  · have hb := hii t ht hZ h30
    have he : Real.exp 0.02 ≤ 1.0203 := by
      have := Real.exp_bound' (x := 0.02) (by norm_num) (by norm_num) (n := 3) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
    have hr := one_add_mul_rho_le u
    have hρ := Dickman.rho_pos u
    unfold BSaias.C0 at hb
    calc Real.log t * P.omegaW tw t v ≤ (1 + u) * L * P.omegaW tw t v := hmul
      _ ≤ (1 + u) * L * (2 * 0.70 * Dickman.rho u * Real.exp 0.02) :=
          mul_le_mul_of_nonneg_left hb (by nlinarith)
      _ = L * (1.4 * Real.exp 0.02) * ((1 + u) * Dickman.rho u) := by ring
      _ ≤ L * (1.4 * Real.exp 0.02) * 2 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ 2.9 * L := by nlinarith
  rcases le_or_gt u L with hLu | hLu
  · have hb := hiii t ht hZ h30 hLu
    have hr := one_add_exp_le h30
    unfold BSaias.C0 at hb
    calc Real.log t * P.omegaW tw t v ≤ (1 + u) * L * P.omegaW tw t v := hmul
      _ ≤ (1 + u) * L * (2 * 0.70 * Real.exp (-(0.7 * u * Real.log u))) :=
          mul_le_mul_of_nonneg_left hb (by nlinarith)
      _ = 1.4 * L * ((1 + u) * Real.exp (-(0.7 * u * Real.log u))) := by ring
      _ ≤ 1.4 * L * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ 2.9 * L := by linarith
  · have hb := hR t ht hZ hLu
    have hr := rankin_small hL hLu
    calc Real.log t * P.omegaW tw t v ≤ (1 + u) * L * P.omegaW tw t v := hmul
      _ ≤ (1 + u) * L * (5 * L ^ (1.65 : ℝ) * Real.exp (-(u / 2))) :=
          mul_le_mul_of_nonneg_left hb (by nlinarith)
      _ = L * ((1 + u) * (5 * L ^ (1.65 : ℝ) * Real.exp (-(u / 2)))) := by ring
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left hr hL0.le
      _ ≤ 2.9 * L := by linarith

/-- **Step 4, assembly**: `log t · S(t) ≤ E_S`. Here `Vs` is the finite set of dyadic scales
`v'` met by the cofactors, `ω v'` the filtered cofactor weights, `ν v' = ν̂(v')` (Lemma 5.22) and
`δ v' = sup_{[v',2v')} δ`; `so ≥ log t · o_t` and `sη ≥ log t · η(t)`. -/
theorem step4 {lt S o η so sη : ℝ} (Vs : Finset ℝ) (ω ν δ : ℝ → ℝ) (hlt : 0 ≤ lt)
    (ho : lt * o ≤ so) (hη : lt * η ≤ sη) (hν : ∀ v ∈ Vs, 0 ≤ ν v)
    (hδ : ∀ v ∈ Vs, 0 ≤ δ v) (hω0 : ∀ v ∈ Vs, 0 ≤ ω v)
    (hω : ∀ v ∈ Vs, lt * ω v ≤ 2.9 * Real.log (3 * v))
    (hS : S ≤ o + 2 * η + 4 * ∑ v ∈ Vs, ω v * ν v + 1.0001 * ∑ v ∈ Vs, ω v * δ v) :
    lt * S ≤ so + 2 * sη + 27 * ∑ v ∈ Vs, Real.log (3 * v) * ν v +
      4.3 * ∑ v ∈ Vs, Real.log (3 * v) * δ v := by
  have h1 : lt * ∑ v ∈ Vs, ω v * ν v ≤ 2.9 * ∑ v ∈ Vs, Real.log (3 * v) * ν v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    have := mul_le_mul_of_nonneg_right (hω v hv) (hν v hv)
    linarith
  have h2 : lt * ∑ v ∈ Vs, ω v * δ v ≤ 2.9 * ∑ v ∈ Vs, Real.log (3 * v) * δ v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    have := mul_le_mul_of_nonneg_right (hω v hv) (hδ v hv)
    linarith
  have hn1 : 0 ≤ ∑ v ∈ Vs, Real.log (3 * v) * ν v := by
    have : 0 ≤ ∑ v ∈ Vs, lt * ω v * ν v :=
      Finset.sum_nonneg fun v hv => mul_nonneg (mul_nonneg hlt (hω0 v hv)) (hν v hv)
    have e : lt * ∑ v ∈ Vs, ω v * ν v = ∑ v ∈ Vs, lt * ω v * ν v := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    linarith
  have hn2 : 0 ≤ ∑ v ∈ Vs, Real.log (3 * v) * δ v := by
    have : 0 ≤ ∑ v ∈ Vs, lt * ω v * δ v :=
      Finset.sum_nonneg fun v hv => mul_nonneg (mul_nonneg hlt (hω0 v hv)) (hδ v hv)
    have e : lt * ∑ v ∈ Vs, ω v * δ v = ∑ v ∈ Vs, lt * ω v * δ v := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    linarith
  have := mul_le_mul_of_nonneg_left hS hlt
  nlinarith

end Margin.Var

end
