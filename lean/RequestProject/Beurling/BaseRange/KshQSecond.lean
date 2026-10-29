module

public import RequestProject.Beurling.BaseRange.EulerQ
public import RequestProject.Beurling.Noise.KptLemma73

/-!
# Lemma 7.3(c): the second bound for the rational operator `K^sh_ℚ`

This proves the named input `KR.Sharp.KshQF1Second` (`Noise/KptLemma73.lean`): for `x ≥ X₀`
with `v = log x/Λ ≥ 4`, `U = 1 + 2 log v`,

  `|K^sh_ℚ(f₁ 1_{[X₀,∞)})(x)| ≤ (U/log x)³ (log U + 1.01) + 2e^γ e^{Ein(2)} (v/U) v⁻⁴ Λ⁻³`,

following bullets 1–2 of the proof of Lemma 7.3(c), with `y = x^{1/U}`:

* components with `q = x/m ≥ y`: `|f₁(q)| ≤ (log y)⁻³/log q`, and
  `∑_{2 ≤ m ≤ x/y} 1/(m log(x/m)) ≤ log(log x/log y) = log U` (`sum_inv_mul_log_le`);
* components with `q ∈ [X₀, y)`: `|f₁(q)| ≤ Λ⁻⁴`, the cofactor `m > x/y` is `y`-smooth (the
  filter `P⁺(m) ≤ x/m`), and Rankin's method with exponent `1 - σ`, `σ = 2/log y`, gives
  `∑ 1/m ≤ (x/y)^{-σ} ∏_{p ≤ y}(1 - p^{σ-1})⁻¹ ≤ v⁻⁴ · 2e^γ e^{Ein(2)} log y`
  (`rankinConst_le`).

* `kshQF1Second` : **`KR.Sharp.KshQF1Second X₀`** for `log X₀ ≥ 10⁸` under (84).
-/

@[expose] public section

open Real Finset BSCert.Consts BSCert.EiFn

namespace BaseRange

lemma abs_ite_le (c : Prop) [Decidable c] (a : ℝ) : |(if c then a else 0)| ≤ |a| := by
  split_ifs <;> simp

/-- `2 e^γ ≥ 1.81 · 1.0001 · 1.001`. -/
lemma two_exp_gamma_ge : 1.82 ≤ 2 * Real.exp Real.eulerMascheroniConstant := by
  have h := Real.one_half_lt_eulerMascheroniConstant
  have := Real.add_one_le_exp Real.eulerMascheroniConstant
  linarith

set_option maxHeartbeats 1600000 in
/-- **The rational half of the second bound of Lemma 7.3(c)** (`KR.Sharp.KshQF1Second`). -/
theorem kshQF1Second {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) :
    KR.Sharp.KshQF1Second X0 := by
  classical
  intro x hx hv
  set κ := Construction.kappaParam X0
  set Λ := Real.log X0 with hΛdef
  set L := Real.log x with hLdef
  set v := L / Λ with hvdef
  set U := Uf v with hUdef
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hx0 : 0 < x := by linarith
  have hLΛ : Λ ≤ L := Real.log_le_log hX0 hx
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < v := by linarith
  have hU1 : 1 ≤ U := Uf_ge_one (by linarith)
  have hU0 : 0 < U := by linarith
  have hlogv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hv0
  have hU2v : U ≤ 2 * v := by simp only [hUdef, Uf]; linarith
  set ly := L / U with hly
  have hlyL : ly ≤ L := div_le_self hL0.le hU1
  have hly_big : Λ / 2 ≤ ly := by
    rw [hly, le_div_iff₀ hU0]
    have : Λ * v = L := by rw [hvdef]; field_simp
    nlinarith
  have hly0 : 0 < ly := by linarith
  set y := Real.exp ly with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ly := Real.log_exp ly
  have hyx : y ≤ x := by rw [hy, ← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hlyL
  have hey : Real.exp 1 ≤ y := Real.exp_le_exp.mpr (by linarith)
  set σ := 2 / ly with hσ
  have hσ0 : 0 < σ := by positivity
  have hσs : σ ≤ 1 / 10 ^ 7 := by
    rw [hσ, div_le_iff₀ hly0]; nlinarith
  set M := ⌊x / X0⌋₊ with hM
  -- the terms
  set T : ℕ → ℝ := fun m =>
    if (Pplus m : ℝ) ≤ x / m then f1 X0 κ (x / m) / m else 0 with hT
  have hq : ∀ m ∈ Icc 2 M, (X0 : ℝ) ≤ x / m ∧ (0 : ℝ) < m := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    refine ⟨?_, hm0⟩
    rw [le_div_iff₀ hm0]
    have : (m : ℝ) ≤ x / X0 :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))
    rw [le_div_iff₀ hX0] at this; linarith
  -- `|f₁(q)| ≤ (log q)^{-4}` for `q ≥ X₀`
  have hf1 : ∀ q : ℝ, (X0 : ℝ) ≤ q → |f1 X0 κ q| ≤ 1 / Real.log q ^ 3 * (1 / Real.log q) := by
    intro q hq
    have hlq : Λ ≤ Real.log q := Real.log_le_log hX0 hq
    have h1 := abs_f1_le hX hH hq
    have h2 := f0_le hX1 (BModel.kappa_facts hX).1 hq
    have h0 := f0_nonneg hX1 (BModel.kappa_facts hX).1 hq
    rw [zpow_neg, zpow_ofNat, ← one_div] at h1
    have hlq0 : 0 < Real.log q := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  unfold KR.Sharp.secondHalf
  rw [← hLdef, ← hΛdef, ← hvdef, ← hUdef]
  unfold KshQ
  rw [← hM]
  change |∑ m ∈ Icc 2 M, T m| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 M) (fun m : ℕ => (m : ℝ) ≤ x / y)]
  -- bullet 1
  have hB1 : ∑ m ∈ (Icc 2 M).filter (fun m : ℕ => (m : ℝ) ≤ x / y), |T m| ≤
      (U / L) ^ 3 * (Real.log U + 1.01) := by
    set K := ⌊x / y⌋₊ with hK
    have hterm : ∀ m ∈ (Icc 2 M).filter (fun m : ℕ => (m : ℝ) ≤ x / y),
        |T m| ≤ 1 / ly ^ 3 * (1 / ((m : ℝ) * Real.log (x / m))) := by
      intro m hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_filter.mp hm
      obtain ⟨hqX, hm0⟩ := hq m hm1
      have hqy : y ≤ x / m := by rw [le_div_iff₀ hm0]; rw [le_div_iff₀ hy0] at hmy; linarith
      have hlq : ly ≤ Real.log (x / m) := by rw [← hlogy]; exact Real.log_le_log hy0 hqy
      have hlq0 : 0 < Real.log (x / m) := by linarith
      refine (abs_ite_le _ _).trans ?_
      rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
      refine (hf1 _ hqX).trans ?_
      have h3 : 1 / Real.log (x / m) ^ 3 ≤ 1 / ly ^ 3 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hly0.le hlq 3)
      calc 1 / Real.log (x / m) ^ 3 * (1 / Real.log (x / m))
          ≤ 1 / ly ^ 3 * (1 / Real.log (x / m)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = 1 / ly ^ 3 * (1 / ((m : ℝ) * Real.log (x / m))) * m := by field_simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hxy1 : 1 ≤ x / y := by rw [le_div_iff₀ hy0]; linarith
    have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hxy1)
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hxK : y ≤ x / K := by
      rw [le_div_iff₀ hK0]
      have : (K : ℝ) ≤ x / y := Nat.floor_le (by positivity)
      rw [le_div_iff₀ hy0] at this; linarith
    have hsub : (Icc 2 M).filter (fun m : ℕ => (m : ℝ) ≤ x / y) ⊆ Icc 2 K := by
      intro m hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm1).1, Nat.le_floor hmy⟩
    have hnn : ∀ m ∈ Icc 2 K, m ∉ (Icc 2 M).filter (fun m : ℕ => (m : ℝ) ≤ x / y) →
        0 ≤ 1 / ((m : ℝ) * Real.log (x / m)) := by
      intro m hm _
      have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hmK : (m : ℝ) ≤ x / y :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))
      have : y ≤ x / m := by rw [le_div_iff₀ hm0]; rw [le_div_iff₀ hy0] at hmK; linarith
      have : 0 < Real.log (x / m) := Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
      positivity
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have h2 := sum_inv_mul_log_le hK1 (hey.trans hxK)
    have h3 : Real.log ly ≤ Real.log (Real.log (x / K)) := by
      apply Real.log_le_log hly0
      rw [← hlogy]; exact Real.log_le_log hy0 hxK
    have h4 : Real.log L - Real.log ly = Real.log U := by
      rw [← Real.log_div hL0.ne' hly0.ne', hly]; field_simp
    have hU3 : (U / L) ^ 3 = 1 / ly ^ 3 := by rw [hly]; field_simp
    have hlU : 0 ≤ Real.log U := Real.log_nonneg hU1
    rw [hU3]
    have : 0 < 1 / ly ^ 3 := by positivity
    have hS : ∑ m ∈ (Icc 2 M).filter (fun m : ℕ => (m : ℝ) ≤ x / y),
        1 / ((m : ℝ) * Real.log (x / m)) ≤ Real.log U := by
      rw [← hLdef] at h2; linarith
    nlinarith
  -- bullet 2
  set N := ⌊y⌋₊ with hN
  have hB2 : ∑ m ∈ (Icc 2 M).filter (fun m : ℕ => ¬ (m : ℝ) ≤ x / y), |T m| ≤
      1 / Λ ^ 4 * Real.exp (-(σ * (L - ly))) * Rankin.rankinConst (N + 1) (1 - σ) := by
    set S := ((Icc 2 M).filter (fun m : ℕ => ¬ (m : ℝ) ≤ x / y)).filter
      (fun m : ℕ => (Pplus m : ℝ) ≤ x / m) with hS
    have hsplit : ∑ m ∈ (Icc 2 M).filter (fun m : ℕ => ¬ (m : ℝ) ≤ x / y), |T m| =
        ∑ m ∈ S, |T m| := by
      rw [hS]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro m _ hne
      by_contra h
      apply hne
      simp [hT, h]
    rw [hsplit]
    have hθ : 0 < 1 - σ := by linarith
    have hterm : ∀ m ∈ S, |T m| ≤ 1 / Λ ^ 4 * (Real.exp (-(σ * (L - ly))) *
        (m : ℝ) ^ (-(1 - σ))) := by
      intro m hm
      obtain ⟨hm1', hP⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_filter.mp hm1'
      obtain ⟨hqX, hm0⟩ := hq m hm1
      have hlq : Λ ≤ Real.log (x / m) := Real.log_le_log hX0 hqX
      refine (abs_ite_le _ _).trans ?_
      rw [abs_div, abs_of_pos hm0]
      have hf := hf1 _ hqX
      have h4 : 1 / Real.log (x / m) ^ 3 * (1 / Real.log (x / m)) ≤ 1 / Λ ^ 4 := by
        rw [div_mul_div_comm, one_mul, ← pow_succ]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hΛ0.le hlq 4)
      -- `1/m ≤ (x/y)^{-σ} m^{-(1-σ)}`
      have hmxy : x / y < m := lt_of_not_ge hmy
      have hxy0 : 0 < x / y := div_pos hx0 hy0
      have hr : 1 / (m : ℝ) ≤ Real.exp (-(σ * (L - ly))) * (m : ℝ) ^ (-(1 - σ)) := by
        have e1 : Real.exp (-(σ * (L - ly))) = (x / y) ^ (-σ) := by
          rw [Real.rpow_def_of_pos hxy0, Real.log_div hx0.ne' hy0.ne', hlogy, ← hLdef]
          congr 1; ring
        rw [e1]
        have h5 : (x / y) ^ (-σ) * (m : ℝ) ^ (-(1 - σ)) ≥ (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-(1 - σ)) :=
          by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos hxy0 hmxy.le (by linarith)
        have h6 : (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-(1 - σ)) = 1 / m := by
          rw [← Real.rpow_add hm0, show -σ + -(1 - σ) = (-1 : ℝ) by ring, Real.rpow_neg_one,
            one_div]
        linarith
      calc |f1 X0 κ (x / m)| / m ≤ 1 / Λ ^ 4 * (1 / m) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right (hf.trans h4) (by positivity)
        _ ≤ 1 / Λ ^ 4 * (Real.exp (-(σ * (L - ly))) * (m : ℝ) ^ (-(1 - σ))) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    -- Rankin
    have hsmooth : ∀ m ∈ S, m ∈ (N + 1).smoothNumbers := by
      intro m hm
      obtain ⟨hm1', hP⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_filter.mp hm1'
      obtain ⟨hqX, hm0⟩ := hq m hm1
      have hmxy : x / y < m := lt_of_not_ge hmy
      have hqy : x / m < y := by
        rw [div_lt_iff₀ hm0]; rw [div_lt_iff₀ hy0] at hmxy; linarith
      rw [Nat.mem_smoothNumbers]
      refine ⟨by have := (Finset.mem_Icc.mp hm1).1; omega, fun p hp => ?_⟩
      have hpf : p ∈ m.primeFactors := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp
      have hpP : p ≤ Pplus m := by
        unfold Pplus; exact Finset.le_sup (f := id) hpf
      have : (p : ℝ) < y := by
        have : (p : ℝ) ≤ Pplus m := by exact_mod_cast hpP
        linarith
      have : p ≤ N := Nat.le_floor this.le
      omega
    have hsum := (Rankin.hasSum_smooth_rpow (N + 1) hθ).2
    have e : ∑ m ∈ S, (m : ℝ) ^ (-(1 - σ)) =
        ∑ m ∈ S.subtype (fun m => m ∈ (N + 1).smoothNumbers), ((m : ℕ) : ℝ) ^ (-(1 - σ)) := by
      exact (Finset.sum_subtype_of_mem (fun n : ℕ => (n : ℝ) ^ (-(1 - σ))) hsmooth).symm
    rw [e]
    exact sum_le_hasSum _ (fun _ _ => by positivity) hsum
  -- the numerics
  have hN2 : 2 ≤ N := Nat.le_floor (by
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    push_cast; linarith)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hσN : σ * Real.log N ≤ 2 := by
    have : Real.log N ≤ ly := by rw [← hlogy]; exact Real.log_le_log hN0 hNy
    rw [hσ, div_mul_eq_mul_div, div_le_iff₀ hly0]; linarith
  have hyN1 : y < ((N + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one y
  have hlogN1 : ly ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← hlogy]; exact Real.log_le_log hy0 hyN1.le
  have hlogN1' : Real.log ((N + 1 : ℕ) : ℝ) ≤ ly + 1 := by
    have : ((N + 1 : ℕ) : ℝ) ≤ 2 * y := by
      have : (1 : ℝ) ≤ y := by linarith [Real.add_one_le_exp (1 : ℝ)]
      push_cast; linarith
    have h := Real.log_le_log (by positivity) this
    rw [Real.log_mul (by norm_num) hy0.ne', hlogy] at h
    have := Real.log_two_lt_d9; linarith
  have hR := rankinConst_le hσ0 (by linarith) hN2 hσN (by linarith)
  have hexp : Real.exp (-(σ * (L - ly))) = 1 / v ^ 4 := by
    have e1 : σ * (L - ly) = 2 * (U - 1) := by
      rw [hσ, hly]; field_simp
    have e2 : 2 * (U - 1) = 4 * Real.log v := by simp only [hUdef, Uf]; ring
    rw [e1, e2, show -(4 * Real.log v) = Real.log v * (-4 : ℝ) by ring, ← Real.rpow_def_of_pos hv0,
      Real.rpow_neg hv0.le, one_div]
    norm_num
  have hc : 1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (Ein 2 + 840 * σ) ≤
      2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly := by
    rw [Real.exp_add]
    have h1 : Real.exp (840 * σ) ≤ 1.0001 := by
      have : 840 * σ ≤ 1 / 10000 := by linarith
      have h2 := Real.exp_bound_div_one_sub_of_interval (by positivity : (0:ℝ) ≤ 840 * σ)
        (by linarith)
      have : 1 / (1 - 840 * σ) ≤ 1.0001 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have h3 : Real.log ((N + 1 : ℕ) : ℝ) ≤ 1.0001 * ly := by nlinarith
    have hg := two_exp_gamma_ge
    have hE := Real.exp_pos (Ein 2)
    have h4 : 1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (840 * σ) ≤ 1.82 * ly := by
      have h5 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by linarith
      calc 1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (840 * σ)
          ≤ 1.8 * (1.0001 * ly) * 1.0001 :=
            mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by positivity)
        _ ≤ 1.82 * ly := by nlinarith
    have : 1.8 * Real.log ((N + 1 : ℕ) : ℝ) * (Real.exp (Ein 2) * Real.exp (840 * σ)) =
        (1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (840 * σ)) * Real.exp (Ein 2) := by ring
    rw [this]
    have : 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly =
        (2 * Real.exp Real.eulerMascheroniConstant * ly) * Real.exp (Ein 2) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hE.le
    nlinarith
  have hfinal : 1 / Λ ^ 4 * Real.exp (-(σ * (L - ly))) * Rankin.rankinConst (N + 1) (1 - σ) ≤
      2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / U) / v ^ 4 /
        Λ ^ 3 := by
    rw [hexp]
    have h0 : 0 ≤ 1 / Λ ^ 4 * (1 / v ^ 4) := by positivity
    calc 1 / Λ ^ 4 * (1 / v ^ 4) * Rankin.rankinConst (N + 1) (1 - σ)
        ≤ 1 / Λ ^ 4 * (1 / v ^ 4) *
            (2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly) :=
          mul_le_mul_of_nonneg_left (hR.trans hc) h0
      _ = 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / U) / v ^ 4 /
            Λ ^ 3 := by
          rw [hly]
          have : L = Λ * v := by rw [hvdef]; field_simp
          rw [this]
          field_simp
  linarith

end BaseRange
