module

public import RequestProject.BSCert.DickmanCert

/-!
# Dickman bounds for Lemma 5.21

* `rho_le_exp_one_sub` : `ρ(u) ≤ e^{1-u}` for `u ≥ 1` (decay with `r ≥ r(1) = 1`, (R3));
* `rho_mul_prod_le` : `ρ(k + f) ∏_{j=1}^{k} (j + f) ≤ 1` for `0 ≤ f ≤ 1` (iterating
  `u ρ(u) ≤ ρ(u-1)`, (R1)); this is the paper's `ρ(u) ≤ 1/Γ(u+1)` along `u - ℕ`;
* `prod_ge` : `∏_{j=1}^{k} (j + f) ≥ k! (k+1)^f` (Bernoulli);
* `rho_exp_le_big` : for `u > 30` and `a ≤ 1.3·10⁻⁵ u`, `ρ(u) e^{a} ≤ 2 e^{-0.7 u log u}` (the
  numerical form of Lemma 5.21(ii) for `30 < u_y ≤ log 3v`).
-/

@[expose] public section

open Finset Real

namespace LemS

lemma ratio_one : Dickman.ratio 1 = 1 := by
  rw [Dickman.ratio_one_two le_rfl (by norm_num)]; simp

/-- `ρ(u) ≤ e^{1-u}` for `u ≥ 1`. -/
lemma rho_le_exp_one_sub {u : ℝ} (hu : 1 ≤ u) : Dickman.rho u ≤ Real.exp (1 - u) := by
  have h := Dickman.rho_le_exp (w := 1) (t := u) le_rfl hu
  rw [Dickman.rho_of_le_one le_rfl, ratio_one, one_mul, one_mul] at h
  convert h using 2; ring

/-- `ρ(k + f) ∏_{j=1}^{k} (j + f) ≤ 1` for `0 ≤ f ≤ 1`. -/
lemma rho_mul_prod_le (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (k : ℕ) :
    Dickman.rho (k + f) * ∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f) ≤ 1 := by
  induction k with
  | zero => simp [Dickman.rho_of_le_one hf1]
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have h := Dickman.mul_rho_le (u := ((k + 1 : ℕ) : ℝ) + f) (by push_cast; linarith)
    have e : ((k + 1 : ℕ) : ℝ) + f - 1 = (k : ℝ) + f := by push_cast; ring
    rw [e] at h
    have hP : 0 ≤ ∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f) :=
      Finset.prod_nonneg fun j _ => by positivity
    calc Dickman.rho (((k + 1 : ℕ) : ℝ) + f) *
          ((∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f)) * (((k + 1 : ℕ) : ℝ) + f))
        = ((((k + 1 : ℕ) : ℝ) + f) * Dickman.rho (((k + 1 : ℕ) : ℝ) + f)) *
            ∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f) := by ring
      _ ≤ Dickman.rho ((k : ℝ) + f) * ∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f) :=
          mul_le_mul_of_nonneg_right h hP
      _ ≤ 1 := ih

/-- `∏_{j=1}^{k} (j + f) ≥ k! (k+1)^f` for `0 ≤ f ≤ 1`. -/
lemma prod_ge (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (k : ℕ) :
    (k.factorial : ℝ) * ((k : ℝ) + 1) ^ f ≤ ∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ]
    push_cast
    have hk : (0 : ℝ) < k + 1 := by positivity
    -- `(k+2)^f ≤ (k+1)^f (1 + f/(k+1))`
    have hb := rpow_one_add_le_one_add_mul_self (s := 1 / ((k : ℝ) + 1))
      (by have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
          linarith) hf0 hf1
    have e1 : ((k : ℝ) + 1 + 1) ^ f = ((k : ℝ) + 1) ^ f * (1 + 1 / ((k : ℝ) + 1)) ^ f := by
      rw [← Real.mul_rpow hk.le (by positivity)]
      congr 1; field_simp
    have hpos : 0 ≤ ((k : ℝ) + 1) ^ f := by positivity
    calc ((k : ℝ) + 1) * (k.factorial : ℝ) * ((k : ℝ) + 1 + 1) ^ f
        = (k.factorial : ℝ) * ((k : ℝ) + 1) ^ f * (((k : ℝ) + 1) *
            (1 + 1 / ((k : ℝ) + 1)) ^ f) := by rw [e1]; ring
      _ ≤ (k.factorial : ℝ) * ((k : ℝ) + 1) ^ f * (((k : ℝ) + 1) *
            (1 + f * (1 / ((k : ℝ) + 1)))) := by
          gcongr
      _ = (k.factorial : ℝ) * ((k : ℝ) + 1) ^ f * ((k : ℝ) + 1 + f) := by
          congr 1; field_simp
      _ ≤ (∏ j ∈ Finset.Icc 1 k, ((j : ℝ) + f)) * ((k : ℝ) + 1 + f) :=
          mul_le_mul_of_nonneg_right ih (by positivity)

/-- `log 30 ≥ 3.34`. -/
lemma log_30_ge : (3.34 : ℝ) ≤ Real.log 30 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 0.17 ≤ 1 / (1 - 0.17) := by
    have := Real.add_one_le_exp (-0.17)
    rw [Real.exp_neg] at this
    rw [le_div_iff₀ (by norm_num)]
    have hp := Real.exp_pos 0.17
    have : 0.83 ≤ (Real.exp 0.17)⁻¹ := by linarith
    have := (le_inv_comm₀ (by norm_num) hp).mp this
    nlinarith
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have e : Real.exp 3.34 = Real.exp 1 ^ 3 * Real.exp 0.17 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3
  have h4 : Real.exp 0.17 ^ 2 ≤ (1 / (1 - 0.17)) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h1 2
  have h5 : 0 ≤ Real.exp 0.17 ^ 2 := by positivity
  calc Real.exp 1 ^ 3 * Real.exp 0.17 ^ 2 ≤ 2.7182818286 ^ 3 * (1 / (1 - 0.17)) ^ 2 :=
        mul_le_mul h3 h4 h5 (by norm_num)
    _ ≤ 30 := by norm_num

/-- `log k! ≥ k log k - k`. -/
lemma log_factorial_ge (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hf] at h
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at this
  linarith

/-- **Numerical form of Lemma 5.21(ii) for `u > 30`**: if `a ≤ 1.3·10⁻⁵ u` then
`ρ(u) e^{a} ≤ 2 e^{-0.7 u log u}`. -/
lemma rho_exp_le_big {u a : ℝ} (hu : 30 < u) (ha : a ≤ 0.000013 * u) :
    Dickman.rho u * Real.exp a ≤ 2 * Real.exp (-(0.7 * u * Real.log u)) := by
  set k := ⌊u⌋₊ with hk
  set f := u - k with hf
  have hku : (k : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hku' : u < k + 1 := Nat.lt_floor_add_one u
  have hk30 : 30 ≤ k := by
    have : (30 : ℝ) ≤ k := by
      have := Nat.le_floor (show ((30 : ℕ) : ℝ) ≤ u by push_cast; linarith)
      exact_mod_cast this
    exact_mod_cast this
  have hk30r : (30 : ℝ) ≤ k := by exact_mod_cast hk30
  have hf0 : 0 ≤ f := by rw [hf]; linarith
  have hf1 : f ≤ 1 := by rw [hf]; linarith
  have hu_eq : u = k + f := by rw [hf]; ring
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ := rho_mul_prod_le f hf0 hf1 k
  have hpr := prod_ge f hf0 hf1 k
  rw [← hu_eq] at hρ
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hkf : 0 < (k.factorial : ℝ) * ((k : ℝ) + 1) ^ f := by positivity
  -- `ρ(u) ≤ 1/(k! (k+1)^f)`
  have hρ' : Dickman.rho u ≤ 1 / ((k.factorial : ℝ) * ((k : ℝ) + 1) ^ f) := by
    rw [le_div_iff₀ hkf]
    have := Dickman.rho_pos u
    nlinarith
  -- the logarithmic inequality
  have hlogk : 3.34 ≤ Real.log k :=
    log_30_ge.trans (Real.log_le_log (by norm_num) hk30r)
  have hlf := log_factorial_ge k (by omega)
  have hlk1 : Real.log ((k : ℝ) + 1) ≤ Real.log k + 1 / k := by
    have : Real.log (((k : ℝ) + 1) / k) ≤ ((k : ℝ) + 1) / k - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk0.ne'] at this
    have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have hlu : Real.log u ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by linarith) hku'.le
  have hlog2 : 0.693 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlk1nn : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
  have key : a - (k : ℝ) * Real.log k + k - f * Real.log ((k : ℝ) + 1) ≤
      Real.log 2 - 0.7 * u * Real.log u := by
    have h1 : 0.7 * u * Real.log u ≤ 0.7 * u * Real.log ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlu (by linarith)
    have h2 : 0.7 * u * Real.log ((k : ℝ) + 1) ≤
        0.7 * k * (Real.log k + 1 / k) + 0.7 * f * Real.log ((k : ℝ) + 1) := by
      rw [hu_eq]
      have := mul_le_mul_of_nonneg_left hlk1 (show (0 : ℝ) ≤ 0.7 * k by positivity)
      nlinarith
    have e : 0.7 * (k : ℝ) * (Real.log k + 1 / k) = 0.7 * k * Real.log k + 0.7 := by
      field_simp
    have h3 : 0.3 * (k : ℝ) * 3.34 ≤ 0.3 * k * Real.log k :=
      mul_le_mul_of_nonneg_left hlogk (by positivity)
    have h4 : 0 ≤ f * Real.log ((k : ℝ) + 1) := mul_nonneg hf0 hlk1nn
    nlinarith
  calc Dickman.rho u * Real.exp a
      ≤ 1 / ((k.factorial : ℝ) * ((k : ℝ) + 1) ^ f) * Real.exp a :=
        mul_le_mul_of_nonneg_right hρ' (Real.exp_pos a).le
    _ = Real.exp (a - Real.log (k.factorial : ℝ) - f * Real.log ((k : ℝ) + 1)) := by
        rw [Real.exp_sub, Real.exp_sub, Real.exp_log hfact, mul_comm f,
          Real.exp_mul, Real.exp_log (by positivity)]
        field_simp
    _ ≤ Real.exp (Real.log 2 - 0.7 * u * Real.log u) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = 2 * Real.exp (-(0.7 * u * Real.log u)) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]; ring

end LemS

end
