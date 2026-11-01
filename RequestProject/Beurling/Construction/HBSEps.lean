module

public import RequestProject.Beurling.Construction.RealisedLow
public import RequestProject.Beurling.SmoothTailsCert

/-!
# The error profile `ε₁` for (HBS)

`hbsEps X₀ v = 10 v^{-2/5} + min(κ + (κX₀ + 1)/v, Ψ(2v, X₀)/v)`, with `κ = X₀^{-5/12 + 0.02}`.
The first term covers the lag, the absorbed part, the oscillation and the initial range; the
second covers the rigid error (`|E_rig(v)| ≤ min(κv + κX₀ + 1, Ψ(2v, X₀))`).

* `smoothCount_le_rpow_large`: `Ψ(Y, X₀) ≤ Y^{0.85}` once `log Y ≥ 20 X₀^{0.3}` (Rankin's bound with
  the Euler-product estimate of Lemma 6.22(c));
* `dyadic_rpow_sum_le`: sums of `w_k^{-a}` over dyadic points `w_k ∈ [x/2^{k+1}, x/2^k]`,
  `w_k ≥ W`, are at most `(2/W)^a/(1 - 2^{-a})`;
* `hbsEps_mul_log_le` and `hbsEps_dyadic_sum_le`: the conditions `ε₁(v) log v ≤ 10⁻³` and
  `∑_k ε₁(w_k) ≤ 10⁻³` of (HBS), for `v, w_k ≥ X₀/2`.
-/

@[expose] public section

open Set Real Finset

namespace Construction

/-- **The error profile of (HBS)** for the construction. -/
noncomputable def hbsEps (X₀ : ℕ) (v : ℝ) : ℝ :=
  10 * v ^ (-(2 / 5 : ℝ)) +
    min (kappaParam X₀ + (kappaParam X₀ * X₀ + 1) / v) ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v)

lemma logX_pos_aux {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : (0 : ℝ) < X₀ := by
  rcases (Nat.cast_nonneg X₀ : (0 : ℝ) ≤ X₀).lt_or_eq with h | h
  · exact h
  · rw [← h, Real.log_zero] at hX; norm_num at hX

lemma log_ge_half_of {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v) :
    Real.log X₀ / 2 ≤ Real.log v := by
  have h0 := logX_pos_aux hX
  have h1 : Real.log ((X₀ : ℝ) / 2) ≤ Real.log v := Real.log_le_log (by positivity) hv
  rw [Real.log_div h0.ne' (by norm_num)] at h1
  have := Real.log_two_lt_d9
  linarith

lemma rpow_ge_of_half {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v)
    {c : ℝ} (hc : 0 ≤ c) : 1 + c * (Real.log X₀ / 2) ≤ v ^ c := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  rw [Real.rpow_def_of_pos hv0]
  have := Real.add_one_le_exp (Real.log v * c)
  have := log_ge_half_of hX hv
  nlinarith

lemma rpow_neg_le_of_half {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v)
    {c : ℝ} (hc : 0 ≤ c) : v ^ (-c) ≤ 1 / (1 + c * (Real.log X₀ / 2)) := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  rw [Real.rpow_neg hv0.le, ← one_div]
  have hpos : 0 < 1 + c * (Real.log X₀ / 2) := by nlinarith
  exact one_div_le_one_div_of_le hpos (rpow_ge_of_half hX hv hc)

/-- **Smooth numbers far above `X₀`**: `Ψ(Y, X₀) ≤ Y^{0.85}` when `log Y ≥ 20 X₀^{0.3}`. -/
theorem smoothCount_le_rpow_large {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {Y : ℝ} (hY0 : 0 < Y)
    (hY : 20 * (X₀ : ℝ) ^ (0.3 : ℝ) ≤ Real.log Y) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤ Y ^ (0.85 : ℝ) := by
  have h0 := logX_pos_aux hX
  set Λ := Real.log X₀ with hΛ
  have hX3 : 3 ≤ X₀ := by
    by_contra h
    push_neg at h
    have : (X₀ : ℝ) ≤ 2 := by exact_mod_cast (by omega : X₀ ≤ 2)
    have := Real.log_le_sub_one_of_pos h0
    linarith
  set u0 := Real.exp (Λ / 4) with hu0
  have hlu0 : Real.log u0 = Λ / 4 := Real.log_exp _
  have hu0big : 10 ^ 4 ≤ u0 := by
    have := Real.add_one_le_exp (Λ / 4); linarith
  -- `log (Λ/4) ≤ 0.06 Λ`
  have hsq := Real.log_le_rpow_div (x := Λ / 4) (ε := 1 / 2) (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hsq
  have hs2 : Real.sqrt (Λ / 4) ^ 2 = Λ / 4 := Real.sq_sqrt (by linarith)
  have hs5 : 5000 ≤ Real.sqrt (Λ / 4) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hlogΛ : Real.log (Λ / 4) ≤ 0.06 * Λ := by nlinarith
  have hlogΛ0 : 0 ≤ Real.log (Λ / 4) := Real.log_nonneg (by linarith)
  have hlog_ul : Real.log (u0 * Real.log u0) = Λ / 4 + Real.log (Λ / 4) := by
    rw [Real.log_mul (by positivity) (by rw [hlu0]; positivity), hlu0]
  set σ := 1 - Real.log (u0 * Real.log u0) / Λ with hσ
  have hσeq : σ = 3 / 4 - Real.log (Λ / 4) / Λ := by
    rw [hσ, hlog_ul]; field_simp; ring
  have hdiv1 : Real.log (Λ / 4) / Λ ≤ 0.06 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hdiv0 : 0 ≤ Real.log (Λ / 4) / Λ := div_nonneg hlogΛ0 (by linarith)
  have hσ1 : 0.69 ≤ σ := by rw [hσeq]; linarith
  have hσ2 : σ ≤ 0.75 := by rw [hσeq]; linarith
  have hE := SmoothTails.euler_estimate hX3 hu0big hσ1
  have hR := Rankin.smoothCount_le_rankin X₀ (show 0 < σ by linarith) hY0.le
  have hRpos : 0 < Rankin.rankinConst X₀ σ := by
    unfold Rankin.rankinConst
    apply Finset.prod_pos
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
    positivity
  -- the exponent comparison
  have hX03 : (X₀ : ℝ) ^ (0.3 : ℝ) = Real.exp (0.05 * Λ) * u0 := by
    rw [Real.rpow_def_of_pos h0, hu0, ← Real.exp_add]; congr 1; ring
  have he1 : 10 ^ 6 ≤ Real.exp (0.05 * Λ) := by
    have := Real.add_one_le_exp (0.05 * Λ); linarith
  have hu0Λ : 1 + Λ / 4 ≤ u0 := by
    have := Real.add_one_le_exp (Λ / 4); linarith
  have he2 : 1 + 0.3 * Λ ≤ (X₀ : ℝ) ^ (0.3 : ℝ) := by
    rw [Real.rpow_def_of_pos h0]
    have := Real.add_one_le_exp (Λ * 0.3); linarith
  have hlΛ : Real.log Λ ≤ Λ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hexp : 1.42 * Real.log Λ + 1.42 * u0 + 5.5 ≤ 0.1 * Real.log Y := by
    have : 10 ^ 6 * u0 ≤ (X₀ : ℝ) ^ (0.3 : ℝ) := by rw [hX03]; nlinarith
    nlinarith
  have hRle : Rankin.rankinConst X₀ σ ≤ Y ^ (0.1 : ℝ) := by
    rw [← Real.exp_log hRpos, Real.rpow_def_of_pos hY0]
    apply Real.exp_le_exp.mpr
    rw [← hΛ] at hE
    linarith
  have hY1 : 1 ≤ Y := by
    by_contra h; push_neg at h
    have := Real.log_nonpos hY0.le h.le
    have : 0 < (X₀ : ℝ) ^ (0.3 : ℝ) := by positivity
    linarith
  have hYσ : Y ^ σ ≤ Y ^ (0.75 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 hσ2
  calc (Rankin.smoothCount X₀ Y : ℝ) ≤ Y ^ σ * Rankin.rankinConst X₀ σ := hR
    _ ≤ Y ^ (0.75 : ℝ) * Y ^ (0.1 : ℝ) :=
        mul_le_mul hYσ hRle hRpos.le (by positivity)
    _ = Y ^ (0.85 : ℝ) := by rw [← Real.rpow_add hY0]; norm_num

/-- **Dyadic sums of powers**: if `x/2^{k+1} ≤ w_k ≤ x/2^k` and `w_k ≥ W > 0` for `k ∈ K`, then
`∑_{k ∈ K} w_k^{-a} ≤ (2/W)^a / (1 - 2^{-a})` for `a > 0`. -/
theorem dyadic_rpow_sum_le {a W x : ℝ} (ha : 0 < a) (hW : 0 < W) (K : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ K, x / 2 ^ (k + 1) ≤ w k ∧ w k ≤ x / 2 ^ k ∧ W ≤ w k) :
    ∑ k ∈ K, w k ^ (-a) ≤ (2 / W) ^ a / (1 - 2 ^ (-a)) := by
  have hq0 : 0 < (2 : ℝ) ^ (-a) := by positivity
  have hq1 : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : 0 ≤ (2 / W) ^ a := by positivity
  rcases K.eq_empty_or_nonempty with hK | hne
  · subst hK; simp only [Finset.sum_empty]
    exact div_nonneg hC (by linarith)
  set m := K.max' hne with hm
  have hmK : m ∈ K := K.max'_mem hne
  have hxm : W ≤ x / 2 ^ m := (hw m hmK).2.2.trans (hw m hmK).2.1
  set q := (2 : ℝ) ^ (-a) with hq
  have hterm : ∀ k ∈ K, w k ^ (-a) ≤ (2 / W) ^ a * q ^ (m - k) := by
    intro k hk
    have hkm : k ≤ m := K.le_max' k hk
    obtain ⟨h1, -, h3⟩ := hw k hk
    have hw0 : 0 < w k := lt_of_lt_of_le hW h3
    have hpow : (2 : ℝ) ^ (k + 1) * 2 ^ (m - k) = 2 ^ m * 2 := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    have hlow : W / 2 * 2 ^ (m - k) ≤ w k := by
      refine le_trans ?_ h1
      rw [le_div_iff₀ (by positivity)]
      have h2m : W * 2 ^ m ≤ x := by rwa [le_div_iff₀ (by positivity)] at hxm
      calc W / 2 * 2 ^ (m - k) * 2 ^ (k + 1) = W * (2 ^ (k + 1) * 2 ^ (m - k)) / 2 := by ring
        _ = W * 2 ^ m := by rw [hpow]; ring
        _ ≤ x := h2m
    calc w k ^ (-a) ≤ (W / 2 * 2 ^ (m - k)) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = (2 / W) ^ a * q ^ (m - k) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
            ← Real.inv_rpow (by positivity), inv_div, hq, ← Real.rpow_natCast,
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
            mul_comm, mul_comm (-a)]; ring
  calc ∑ k ∈ K, w k ^ (-a) ≤ ∑ k ∈ K, (2 / W) ^ a * q ^ (m - k) := Finset.sum_le_sum hterm
    _ ≤ ∑ k ∈ Finset.range (m + 1), (2 / W) ^ a * q ^ (m - k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; rw [Finset.mem_range]; have := K.le_max' k hk; omega
        · intros; positivity
    _ = (2 / W) ^ a * ∑ j ∈ Finset.range (m + 1), q ^ j := by
        rw [← Finset.mul_sum, ← Finset.sum_range_reflect (fun j => q ^ j) (m + 1)]
        congr 1
    _ ≤ (2 / W) ^ a * (1 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        rw [one_div, ← tsum_geometric_of_lt_one hq0.le hq1]
        exact Summable.sum_le_tsum _ (fun j _ => by positivity)
          (summable_geometric_of_lt_one hq0.le hq1)
    _ = (2 / W) ^ a / (1 - q) := by ring

lemma one_le_X_aux {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : (1 : ℝ) ≤ X₀ := by
  have h0 := logX_pos_aux hX
  by_contra h; push_neg at h
  have := Real.log_nonpos h0.le h.le; linarith

lemma kappa_pos_aux {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : 0 < kappaParam (X₀ : ℝ) :=
  Real.rpow_pos_of_pos (logX_pos_aux hX) _

lemma kappa_le_aux {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    kappaParam (X₀ : ℝ) ≤ 1 / (1 + 0.39 * (Real.log X₀ / 2)) := by
  unfold kappaParam
  calc (X₀ : ℝ) ^ (-5 / 12 + 2 * (0.01 : ℝ)) ≤ (X₀ : ℝ) ^ (-(0.39 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_X_aux hX) (by norm_num)
    _ ≤ _ := rpow_neg_le_of_half hX (by linarith [logX_pos_aux hX]) (by norm_num)

lemma kappa_mul_X03_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    kappaParam (X₀ : ℝ) * (X₀ : ℝ) ^ (0.3 : ℝ) ≤ 1 / (1 + 0.09 * (Real.log X₀ / 2)) := by
  have h0 := logX_pos_aux hX
  unfold kappaParam
  rw [← Real.rpow_add h0]
  calc (X₀ : ℝ) ^ (-5 / 12 + 2 * (0.01 : ℝ) + 0.3) ≤ (X₀ : ℝ) ^ (-(0.09 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_X_aux hX) (by norm_num)
    _ ≤ _ := rpow_neg_le_of_half hX (by linarith) (by norm_num)

lemma X03_div_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    (X₀ : ℝ) ^ (0.3 : ℝ) / X₀ ≤ 1 / (1 + 0.7 * (Real.log X₀ / 2)) := by
  have h0 := logX_pos_aux hX
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add h0,
    show (0.3 : ℝ) + -1 = -(0.7 : ℝ) by norm_num]
  exact rpow_neg_le_of_half hX (by linarith) (by norm_num)

lemma inv_X_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : 1 / (X₀ : ℝ) ≤ 1 / (1 + Real.log X₀) := by
  have h0 := logX_pos_aux hX
  apply one_div_le_one_div_of_le (by linarith)
  have := Real.add_one_le_exp (Real.log X₀)
  rw [Real.exp_log h0] at this; linarith

/-- The two regimes of the second term of `ε₁`. -/
lemma hbsMin_cases {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v) :
    min (kappaParam X₀ + (kappaParam X₀ * X₀ + 1) / v) ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v)
      ≤ 2 * v ^ (-(0.15 : ℝ)) ∨ Real.log v < 20 * (X₀ : ℝ) ^ (0.3 : ℝ) := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  by_cases hc : 20 * (X₀ : ℝ) ^ (0.3 : ℝ) ≤ Real.log (2 * v)
  · left
    refine (min_le_right _ _).trans ?_
    have hS := smoothCount_le_rpow_large hX (by positivity : 0 < 2 * v) hc
    rw [div_le_iff₀ hv0]
    have h2 : (2 : ℝ) ^ (0.85 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (0.85 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc (Rankin.smoothCount X₀ (2 * v) : ℝ) ≤ (2 * v) ^ (0.85 : ℝ) := hS
      _ = 2 ^ (0.85 : ℝ) * v ^ (0.85 : ℝ) := Real.mul_rpow (by norm_num) hv0.le
      _ ≤ 2 * v ^ (0.85 : ℝ) := by gcongr
      _ = 2 * v ^ (-(0.15 : ℝ)) * v := by
          rw [mul_assoc, ← Real.rpow_add_one hv0.ne']; norm_num
  · right
    push_neg at hc
    have : Real.log v ≤ Real.log (2 * v) := Real.log_le_log hv0 (by linarith)
    linarith

lemma rpow_mul_log_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    v ^ (-a) * Real.log v ≤ 1 / b * (1 / (1 + (a - b) * (Real.log X₀ / 2))) := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hl := Real.log_le_rpow_div hv0.le hb
  have hp : v ^ (-a) * v ^ b = v ^ (-(a - b)) := by rw [← Real.rpow_add hv0]; ring_nf
  have hr := rpow_neg_le_of_half hX hv (show (0 : ℝ) ≤ a - b by linarith)
  have hpos : 0 ≤ v ^ (-a) := by positivity
  calc v ^ (-a) * Real.log v ≤ v ^ (-a) * (v ^ b / b) := by gcongr
    _ = 1 / b * v ^ (-(a - b)) := by rw [← hp]; ring
    _ ≤ _ := by gcongr

/-- `ε₁(v) log v ≤ 10⁻³` for `v ≥ X₀/2`. -/
theorem hbsEps_mul_log_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ}
    (hv : (X₀ : ℝ) / 2 ≤ v) : hbsEps X₀ v * Real.log v ≤ 1 / 1000 := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hlogv0 : 0 ≤ Real.log v := by have := log_ge_half_of hX hv; linarith
  have hκ0 := kappa_pos_aux hX
  set Λ := Real.log X₀ with hΛ
  have hA := rpow_mul_log_le hX hv (a := 2 / 5) (b := 0.2) (by norm_num) (by norm_num)
  have hAv : 1 / (0.2 : ℝ) * (1 / (1 + (2 / 5 - 0.2) * (Λ / 2))) ≤ 1 / 100000 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  unfold hbsEps
  rw [add_mul]
  rcases hbsMin_cases hX hv with hm | hm
  · have hB := rpow_mul_log_le hX hv (a := 0.15) (b := 0.05) (by norm_num) (by norm_num)
    have hBv : 1 / (0.05 : ℝ) * (1 / (1 + (0.15 - 0.05) * (Λ / 2))) ≤ 1 / 100000 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := mul_le_mul_of_nonneg_right hm hlogv0
    nlinarith
  · have hm' := min_le_left (kappaParam (X₀ : ℝ) + (kappaParam X₀ * X₀ + 1) / v)
      ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v)
    have hk : (kappaParam (X₀ : ℝ) * X₀ + 1) / v ≤ 2 * kappaParam (X₀ : ℝ) + 2 * (1 / X₀) := by
      rw [div_le_iff₀ hv0]
      have : (kappaParam (X₀ : ℝ) * X₀ + 1) = (2 * kappaParam (X₀ : ℝ) + 2 * (1 / X₀)) * (X₀ / 2) := by
        field_simp
      rw [this]; gcongr
    have hmin0 : 0 ≤ min (kappaParam (X₀ : ℝ) + (kappaParam X₀ * X₀ + 1) / v)
        ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v) := le_min (by positivity) (by positivity)
    have h1 : min (kappaParam (X₀ : ℝ) + (kappaParam X₀ * X₀ + 1) / v)
        ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v) * Real.log v ≤
        (3 * kappaParam (X₀ : ℝ) + 2 * (1 / X₀)) * (20 * (X₀ : ℝ) ^ (0.3 : ℝ)) := by
      apply mul_le_mul (by linarith) hm.le hlogv0 (by positivity)
    have h2 : (3 * kappaParam (X₀ : ℝ) + 2 * (1 / X₀)) * (20 * (X₀ : ℝ) ^ (0.3 : ℝ)) =
        60 * (kappaParam (X₀ : ℝ) * (X₀ : ℝ) ^ (0.3 : ℝ)) + 40 * ((X₀ : ℝ) ^ (0.3 : ℝ) / X₀) := by
      field_simp; ring
    have h3 := kappa_mul_X03_le hX
    have h4 := X03_div_le hX
    have h3v : 1 / (1 + 0.09 * (Λ / 2)) ≤ 1 / 1000000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h4v : 1 / (1 + 0.7 * (Λ / 2)) ≤ 1 / 1000000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith

lemma one_sub_two_rpow_neg_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    0.69 * a / 2 ≤ 1 - (2 : ℝ) ^ (-a) := by
  have hl := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  rw [Real.rpow_def_of_pos (by norm_num)]
  set t := a * Real.log 2 with ht
  have heq : Real.log 2 * -a = -t := by rw [ht]; ring
  rw [heq]
  have he := Real.add_one_le_exp t
  have hm : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-t)
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 0.7 := by nlinarith
  have h1 : Real.exp (-t) * (1 + t) ≤ 1 := by nlinarith
  nlinarith

lemma four_div_rpow_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 ≤ a) :
    (4 / (X₀ : ℝ)) ^ a ≤ 1 / (1 + a * (Real.log X₀ / 2)) := by
  have h0 := logX_pos_aux hX
  rw [Real.rpow_def_of_pos (by positivity), Real.log_div (by norm_num) h0.ne']
  have hl4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  set y := (Real.log 4 - Real.log X₀) * a with hy
  have hy' : y + a * (Real.log X₀ / 2) ≤ 0 := by rw [hy]; nlinarith
  have he := Real.add_one_le_exp (a * (Real.log X₀ / 2))
  have hm : Real.exp y * Real.exp (a * (Real.log X₀ / 2)) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr hy'
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.exp_pos y]

lemma dyadic_X {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {x : ℝ}
    (K : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ K, x / 2 ^ (k + 1) ≤ w k ∧ w k ≤ x / 2 ^ k ∧ (X₀ : ℝ) / 2 ≤ w k) :
    ∑ k ∈ K, w k ^ (-a) ≤ 1 / (1 + a * (Real.log X₀ / 2)) * (2 / (0.69 * a)) := by
  have h0 := logX_pos_aux hX
  have hd := dyadic_rpow_sum_le ha (W := (X₀ : ℝ) / 2) (by positivity) K w hw
  have h4 : 2 / ((X₀ : ℝ) / 2) = 4 / X₀ := by field_simp; ring
  rw [h4] at hd
  refine hd.trans ?_
  have h1 := four_div_rpow_le hX ha.le
  have h2 := one_sub_two_rpow_neg_ge ha ha1
  rw [div_eq_mul_inv]
  apply mul_le_mul h1 _ (inv_nonneg.mpr (by linarith)) (div_nonneg zero_le_one (by nlinarith))
  rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
  linarith

lemma dyadic_X_one {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ}
    (K : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ K, x / 2 ^ (k + 1) ≤ w k ∧ w k ≤ x / 2 ^ k ∧ (X₀ : ℝ) / 2 ≤ w k) :
    ∑ k ∈ K, w k ^ (-(1 : ℝ)) ≤ 8 * (1 / X₀) := by
  have h0 := logX_pos_aux hX
  have hd := dyadic_rpow_sum_le one_pos (W := (X₀ : ℝ) / 2) (by positivity) K w hw
  refine hd.trans (le_of_eq ?_)
  rw [Real.rpow_one, Real.rpow_neg_one]
  field_simp; norm_num

/-- Pointwise majorant of `ε₁` by a sum of negative powers. -/
lemma hbsEps_le_split {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {v : ℝ} (hv : (X₀ : ℝ) / 2 ≤ v) :
    hbsEps X₀ v ≤ 10 * v ^ (-(2 / 5 : ℝ)) + 2 * v ^ (-(0.15 : ℝ)) +
      3 * kappaParam (X₀ : ℝ) * v ^ (-(1 / (20 * (X₀ : ℝ) ^ (0.3 : ℝ)))) +
      (kappaParam (X₀ : ℝ) * X₀ + 1) * v ^ (-(1 : ℝ)) := by
  have h0 := logX_pos_aux hX
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hκ0 := kappa_pos_aux hX
  set a0 := 1 / (20 * (X₀ : ℝ) ^ (0.3 : ℝ)) with ha0
  unfold hbsEps
  have hp1 : 0 ≤ 3 * kappaParam (X₀ : ℝ) * v ^ (-a0) := by positivity
  have hp2 : 0 ≤ (kappaParam (X₀ : ℝ) * X₀ + 1) * v ^ (-(1 : ℝ)) := by positivity
  have hp3 : 0 ≤ 2 * v ^ (-(0.15 : ℝ)) := by positivity
  rcases hbsMin_cases hX hv with hm | hm
  · linarith
  · have hva : v ^ a0 ≤ 3 := by
      rw [Real.rpow_def_of_pos hv0]
      have : Real.log v * a0 ≤ 1 := by
        rw [ha0, mul_one_div, div_le_one (by positivity)]; linarith
      calc Real.exp (Real.log v * a0) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hvpos : 0 < v ^ a0 := by positivity
    have hle : kappaParam (X₀ : ℝ) ≤ 3 * kappaParam (X₀ : ℝ) * v ^ (-a0) := by
      rw [Real.rpow_neg hv0.le, ← div_eq_mul_inv, le_div_iff₀ hvpos]
      nlinarith
    have hk : (kappaParam (X₀ : ℝ) * X₀ + 1) / v =
        (kappaParam (X₀ : ℝ) * X₀ + 1) * v ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    have := min_le_left (kappaParam (X₀ : ℝ) + (kappaParam X₀ * X₀ + 1) / v)
      ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v)
    linarith

/-- `∑_k ε₁(w_k) ≤ 10⁻³` over dyadic points `w_k ≥ X₀/2`. -/
theorem hbsEps_dyadic_sum_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (K : Finset ℕ)
    (w : ℕ → ℝ)
    (hw : ∀ k ∈ K, x / 2 ^ (k + 1) ≤ w k ∧ w k ≤ x / 2 ^ k ∧ (X₀ : ℝ) / 2 ≤ w k) :
    ∑ k ∈ K, hbsEps X₀ (w k) ≤ 1 / 1000 := by
  have h0 := logX_pos_aux hX
  have hκ0 := kappa_pos_aux hX
  set Λ := Real.log X₀ with hΛ
  set a0 := 1 / (20 * (X₀ : ℝ) ^ (0.3 : ℝ)) with ha0
  have hX03 : 1 ≤ (X₀ : ℝ) ^ (0.3 : ℝ) := Real.one_le_rpow (one_le_X_aux hX) (by norm_num)
  have ha0pos : 0 < a0 := by positivity
  have ha01 : a0 ≤ 1 := by rw [ha0, div_le_one (by positivity)]; linarith
  have hsum := Finset.sum_le_sum (fun k hk => hbsEps_le_split hX (hw k hk).2.2)
  rw [← ha0] at hsum
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have s1 := dyadic_X hX (a := 2 / 5) (by norm_num) (by norm_num) K w hw
  have s2 := dyadic_X hX (a := 0.15) (by norm_num) (by norm_num) K w hw
  have s3 := dyadic_X hX ha0pos ha01 K w hw
  have s4 := dyadic_X_one hX K w hw
  have s1v : 1 / (1 + 2 / 5 * (Λ / 2)) * (2 / (0.69 * (2 / 5))) ≤ (1 : ℝ) / 100000 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have s2v : 1 / (1 + 0.15 * (Λ / 2)) * (2 / (0.69 * 0.15)) ≤ (1 : ℝ) / 100000 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have s3v : 1 / (1 + a0 * (Λ / 2)) * (2 / (0.69 * a0)) ≤ 2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ) := by
    have hle : 1 / (1 + a0 * (Λ / 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have heq : 2 / (0.69 * a0) = 2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ) := by
      rw [ha0]; field_simp
    rw [heq]
    calc 1 / (1 + a0 * (Λ / 2)) * (2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ))
        ≤ 1 * (2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ)) := by gcongr
      _ = _ := one_mul _
  have h3 := kappa_mul_X03_le hX
  have h3v : 1 / (1 + 0.09 * (Λ / 2)) ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hk := kappa_le_aux hX
  have hkv : 1 / (1 + 0.39 * (Λ / 2)) ≤ 1 / 10000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hi := inv_X_le hX
  have hiv : 1 / (1 + Λ) ≤ 1 / 100000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e4 : (kappaParam (X₀ : ℝ) * X₀ + 1) * (8 * (1 / X₀)) = 8 * kappaParam (X₀ : ℝ) + 8 * (1 / X₀) := by
    field_simp
  have t3 : 3 * kappaParam (X₀ : ℝ) * ∑ k ∈ K, w k ^ (-a0) ≤
      3 * kappaParam (X₀ : ℝ) * (2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ)) := by
    gcongr; exact s3.trans s3v
  have t4 : (kappaParam (X₀ : ℝ) * X₀ + 1) * ∑ k ∈ K, w k ^ (-(1 : ℝ)) ≤
      (kappaParam (X₀ : ℝ) * X₀ + 1) * (8 * (1 / X₀)) := by
    gcongr
  have e3 : 3 * kappaParam (X₀ : ℝ) * (2 / 0.69 * 20 * (X₀ : ℝ) ^ (0.3 : ℝ)) =
      3 * (2 / 0.69 * 20) * (kappaParam (X₀ : ℝ) * (X₀ : ℝ) ^ (0.3 : ℝ)) := by ring
  rw [e4] at t4
  rw [e3] at t3
  linarith

lemma hbsEps_nonneg {X₀ : ℕ} {v : ℝ} (hv : 0 < v) : 0 ≤ hbsEps X₀ v := by
  unfold hbsEps
  have h1 : 0 ≤ kappaParam (X₀ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ v ^ (-(2 / 5 : ℝ)) := Real.rpow_nonneg hv.le _
  have h3 : 0 ≤ min (kappaParam X₀ + (kappaParam X₀ * X₀ + 1) / v)
      ((Rankin.smoothCount X₀ (2 * v) : ℝ) / v) :=
    le_min (by positivity) (by positivity)
  linarith

end Construction

end
