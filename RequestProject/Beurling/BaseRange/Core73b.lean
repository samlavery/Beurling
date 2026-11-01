module

public import RequestProject.Beurling.BaseRange.ThetaDiff

/-!
# `Lemma73bCore` (proof of Lemma 7.3(b), Steps 1–3 and the decision-order mismatch)

The parameters of Step 3 (`kval_diff_le`) for the realised system `P` against the rational
system `ratSys`, with `x = u/X₀`, `Λ = log X₀`, `y = X₀⁻/2`, `L = log u`:

* `D₀ = ∑_{d rigid} 1/d ≤ 5Λ` (`D0_le`, Rankin and `zinf_le`, the Mertens product below `X₀⁻`);
* `ℓ_u = ∑_{X₀⁻ ≤ p ≤ x} 1/p ≤ S₁`, `e^{S₁} ≤ 3L/Λ` (`S1_le`, `exp_S1_le`, Lemma 5.1(iv));
* `∑ 1/p² ≤ 12.8/X₀⁻` (`Q2_le`);
* `B = 8κ + 2.1/√y ≤ 9κ` (Step 1 `delta_le_of_hbsEps`, Step 2 `thetaF_diff_le`);

and the assembly `lemma73bCore_of`.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

lemma one_le_prod_of_one_le (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have := Finset.prod_le_prod₀ (s := s) (f := fun _ => (1 : ℝ)) (g := f) (fun _ _ => zero_le_one) hf
  simpa using this

lemma prod_le_prod_of_subset_one_le {s t : Finset ℕ} (f : ℕ → ℝ) (h : s ⊆ t)
    (hf : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff h]
  have h1 := one_le_prod_of_one_le (t \ s) f (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)
  have h2 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => by linarith [hf i (h hi)])
  nlinarith

/-! ### Numerics -/

section numerics

variable {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
include hX

lemma X0_pos' : (0 : ℝ) < X0 := by
  rcases (Nat.cast_nonneg X0 : (0 : ℝ) ≤ X0).lt_or_eq with h | h
  · exact h
  · rw [← h, Real.log_zero] at hX; norm_num at hX

lemma exp_one_le_X0 : Real.exp 1 ≤ X0 := by
  rw [← Real.exp_log (X0_pos' hX)]; exact Real.exp_le_exp.mpr (by linarith)

/-- `κ X₀ ≥ 2`. -/
lemma kappa_mul_X0_ge : 2 ≤ Construction.kappaParam X0 * X0 := by
  have hX0 := X0_pos' hX
  rw [kappa_eq_exp hX0]
  have e : Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) * X0 =
      Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X0) := by
    rw [Real.exp_add, Real.exp_log hX0]
  rw [e]
  have := Real.add_one_le_exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X0)
  nlinarith

/-- `κ² X₀ ≥ 18`. -/
lemma kappa_sq_mul_X0_ge : 18 ≤ Construction.kappaParam X0 ^ 2 * X0 := by
  have hX0 := X0_pos' hX
  rw [kappa_eq_exp hX0]
  have e : Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) ^ 2 * X0 =
      Real.exp (2 * (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) + Real.log X0) := by
    rw [Real.exp_add, Real.exp_log hX0, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e]
  have := Real.add_one_le_exp (2 * (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) + Real.log X0)
  nlinarith

/-- `B = 8κ + 2.1/√(X₀⁻/2) ≤ 9κ`. -/
lemma B_le {X0m : ℝ} (hXm1 : (X0 : ℝ) / 2 ≤ X0m) :
    2 * (4 * Construction.kappaParam X0) + 2.1 / Real.sqrt (X0m / 2) ≤
      9 * Construction.kappaParam X0 := by
  have hX0 := X0_pos' hX
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  set κ := Construction.kappaParam X0
  have hk := kappa_sq_mul_X0_ge hX
  have hXs : 0 < Real.sqrt (X0m / 2) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (X0m / 2) ^ 2 = X0m / 2 := Real.sq_sqrt (by linarith)
  have : 2.1 ≤ κ * Real.sqrt (X0m / 2) := by
    have h1 : (2.1 : ℝ) ^ 2 ≤ (κ * Real.sqrt (X0m / 2)) ^ 2 := by
      rw [mul_pow, hsq]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp h1
  have : 2.1 / Real.sqrt (X0m / 2) ≤ κ := by rw [div_le_iff₀ hXs]; linarith
  linarith

/-- `1/X₀⁻ ≤ κ`. -/
lemma inv_X0m_le {X0m : ℝ} (hXm1 : (X0 : ℝ) / 2 ≤ X0m) :
    1 / X0m ≤ Construction.kappaParam X0 := by
  have hX0 := X0_pos' hX
  have := kappa_mul_X0_ge hX
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end numerics

/-! ### The parameters of Step 3 -/

section params

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- **Step 1** on `[0, x]`: `|N_𝒩(v) - ⌊v⌋| ≤ 4κ v`. -/
lemma hloc_A {P : BeurlingSystem} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) {x : ℝ} (hxZ : x ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v) :
    ∀ v, 0 ≤ v → v ≤ x → |P.N v - ⌊v⌋₊| ≤ 4 * Construction.kappaParam X0 * v := by
  intro v hv0 hvx
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have h0 : 0 ≤ 4 * Construction.kappaParam X0 * v := by positivity
  rcases lt_or_ge v 1 with h1 | h1
  · rw [P.N_eq_zero h1, Nat.floor_eq_zero.mpr h1]; simpa using h0
  rcases lt_or_ge v X0m with h2 | h2
  · rw [h.floor_eq v h1 h2 (hvx.trans hxZ)]; simpa using h0
  exact delta_le_of_hbsEps hX (hXm1.trans h2) (hloc v h2 (hvx.trans hxZ))

/-- The large primes `≤ x` lie in `[X₀⁻, x]`. -/
lemma Lg_mem {S : BeurlingSystem} {a b : ℝ} {c : ℝ → ℝ} (hS : S.HBS X0m Z a b c)
    (hXZ : X0m ≤ Z) {x : ℝ} {j : ℕ} (hj : j ∈ S3.Lg S (J1 X0m) x) :
    X0m ≤ S.p j ∧ S.p j ≤ x := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj
  exact ⟨large_ge hS hXZ h2, S.mem_primesLe.mp h1⟩

lemma Lg_subset {S : BeurlingSystem} {a b : ℝ} {c : ℝ → ℝ} (hS : S.HBS X0m Z a b c)
    (hXZ : X0m ≤ Z) (x : ℝ) :
    S3.Lg S (J1 X0m) x ⊆
      (S.primesLe (max x (X0m / 2))).filter (fun j => X0m / 2 < S.p j) := by
  intro j hj
  obtain ⟨h1, h2⟩ := Lg_mem hS hXZ hj
  have := hS.X0m_pos
  exact Finset.mem_filter.mpr ⟨S.mem_primesLe.mpr (h2.trans (le_max_left _ _)), by linarith⟩

/-- `ℓ_u ≤ S₁` (Lemma 5.1(iv)). -/
lemma S1_le {S : BeurlingSystem} {a b : ℝ} {c : ℝ → ℝ} (hS : S.HBS X0m Z a b c)
    (hXZ : X0m ≤ Z) {x : ℝ} (hxZ : x ≤ Z) :
    ∑ j ∈ S3.Lg S (J1 X0m) x, 1 / S.p j ≤
      Real.log (Real.log (max x (X0m / 2)) / Real.log (X0m / 2)) + 2.2 / Real.log (X0m / 2) := by
  have hX7 := hS.X0m_ge
  have hm := hS.mertens_iv (y := X0m / 2) (x := max x (X0m / 2)) (by linarith)
    (le_max_right _ _) (max_le hxZ (by linarith))
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => 1 / S.p j)
    (Lg_subset hS hXZ x) (fun j _ _ => (one_div_pos.mpr (S.p_pos j)).le)
  have := (abs_le.mp hm).2
  linarith

/-- `∑_{large} 1/p² ≤ 12.8/X₀⁻`. -/
lemma Q2_le {S : BeurlingSystem} {a b : ℝ} {c : ℝ → ℝ} (hS : S.HBS X0m Z a b c)
    (hXZ : X0m ≤ Z) {x : ℝ} (hxZ : x ≤ Z) :
    ∑ j ∈ S3.Lg S (J1 X0m) x, 1 / S.p j ^ 2 ≤ 12.8 / X0m := by
  have hX7 := hS.X0m_ge
  have h1 : ∑ j ∈ S3.Lg S (J1 X0m) x, 1 / S.p j ^ 2 ≤
      ∑ j ∈ S3.Lg S (J1 X0m) x, Real.log (S.p j) / S.p j ^ 2 := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hp := (Lg_mem hS hXZ hj).1
    have hl : 1 ≤ Real.log (S.p j) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    exact div_le_div_of_nonneg_right hl (by positivity)
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => Real.log (S.p j) / S.p j ^ 2)
    (Lg_subset hS hXZ x) (fun j _ _ => div_nonneg (S.log_p_nonneg j) (by positivity))
  have h3 := hS.sum_log_div_sq_le (Y := max x (X0m / 2)) (b := X0m / 2) (by linarith)
    (le_max_right _ _) (max_le hxZ (by linarith))
  have e : 6.4 / (X0m / 2) = 12.8 / X0m := by field_simp; norm_num
  linarith

/-- `D₀ = ∑_{d rigid} 1/d ≤ 5Λ` (Rankin and the Mertens product below `X₀⁻`). -/
lemma D0_le {P : BeurlingSystem} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : X0m ≤ Z)
    (x : ℝ) : ∑ d ∈ S3.Drig P (J1 X0m) x, 1 / P.val d ≤ 5 * Real.log X0 := by
  have hX0 := X0_pos' hX
  have hX7 := h.X0m_ge
  have hZ3 : 3 ≤ Z := by linarith
  have hl4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; have := Real.log_two_lt_d9; linarith
  have hlXm : Real.log X0 - Real.log 4 ≤ Real.log (X0m / 2) := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlXm' : Real.log X0m ≤ Real.log X0 := Real.log_le_log (by linarith) hXm2
  have hlXm'' : Real.log X0 - Real.log 4 ≤ Real.log X0m := by
    have := Real.log_le_log (by positivity) (show X0m / 2 ≤ X0m by linarith); linarith
  -- Rankin
  have hR := rankin_elems P (J := J1 X0m) (θ := 1) one_pos (S3.Drig P (J1 X0m) x)
    (fun e he => (Finset.mem_filter.mp he).2)
  simp only [Real.rpow_neg_one] at hR
  rw [show (∑ d ∈ S3.Drig P (J1 X0m) x, 1 / P.val d) =
    ∑ d ∈ S3.Drig P (J1 X0m) x, (P.val d)⁻¹ by simp only [one_div]]
  refine hR.trans ?_
  have hfac : ∀ j, 1 ≤ (1 - P.p j ^ (-(1 : ℝ)))⁻¹ := by
    intro j
    have hp := P.one_lt j
    rw [Real.rpow_neg_one]
    have h0 : 0 < 1 - (P.p j)⁻¹ := by
      have : (P.p j)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
      linarith
    have : 1 - (P.p j)⁻¹ ≤ 1 := by have := inv_pos.mpr (P.p_pos j); linarith
    exact one_le_inv₀ h0 |>.mpr this
  have hsub : Finset.range (J1 X0m) ⊆ P.primesLe X0m := by
    intro j hj
    exact P.mem_primesLe.mpr (small_eq h hXZ (Finset.mem_range.mp hj)).2.le
  have h1 := prod_le_prod_of_subset_one_le (fun j => (1 - P.p j ^ (-(1 : ℝ)))⁻¹) hsub
    (fun j _ => hfac j)
  have h2 := h.zinf_le hZ3 (by linarith) le_rfl hXZ
  simp only [Real.rpow_neg_one] at h1 h2
  refine h1.trans (h2.trans ?_)
  -- numerics
  have hceil : Real.log (⌈X0m⌉₊ : ℝ) ≤ Real.log X0 := by
    apply Real.log_le_log (by have := Nat.le_ceil X0m; linarith)
    exact_mod_cast Nat.ceil_le.mpr hXm2
  have hceil0 : 0 ≤ Real.log (⌈X0m⌉₊ : ℝ) :=
    Real.log_nonneg (by have := Nat.le_ceil X0m; linarith)
  have hly : 0 < Real.log (X0m / 2) := by linarith
  have hrat : Real.log X0m / Real.log (X0m / 2) ≤ 1.02 := by
    rw [div_le_iff₀ hly]; linarith
  have hexp : Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) ≤ 2.72 := by
    have h1 : 2.2 / Real.log (X0m / 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hly]; linarith
    have h2 : 25.6 / X0m ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hr0 : 0 ≤ Real.log X0m / Real.log (X0m / 2) := div_nonneg (by linarith) hly.le
  calc 1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log X0m / Real.log (X0m / 2)) *
        Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m)
      ≤ 1.8 * Real.log X0 * 1.02 * 2.72 := by
        gcongr
    _ ≤ 5 * Real.log X0 := by nlinarith

/-- `e^{S₁} ≤ 3 log u/Λ`. -/
lemma exp_S1_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) {u : ℝ} (hu : (X0 : ℝ) ≤ u) :
    Real.exp (Real.log (Real.log (max (u / X0) (X0m / 2)) / Real.log (X0m / 2)) +
      2.2 / Real.log (X0m / 2)) ≤ 3 * Real.log u / Real.log X0 := by
  have hX0 := X0_pos' hX
  have hX1 : (1 : ℝ) ≤ X0 := by have := exp_one_le_X0 hX; linarith [Real.add_one_le_exp (1:ℝ)]
  have hl4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; have := Real.log_two_lt_d9; linarith
  have hlXm : Real.log X0 - Real.log 4 ≤ Real.log (X0m / 2) := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hly : 0 < Real.log (X0m / 2) := by linarith
  have hy1 : 1 < X0m / 2 := by
    by_contra hc; push_neg at hc
    have := Real.log_le_log (by linarith) hc; rw [Real.log_one] at this; linarith
  have hY : 0 < Real.log (max (u / X0) (X0m / 2)) :=
    Real.log_pos (lt_of_lt_of_le hy1 (le_max_right _ _))
  have hYu : Real.log (max (u / X0) (X0m / 2)) ≤ Real.log u := by
    apply Real.log_le_log (lt_of_lt_of_le (by linarith) (le_max_right _ _))
    apply max_le
    · exact div_le_self (by linarith) hX1
    · linarith
  rw [Real.exp_add, Real.exp_log (div_pos hY hly)]
  have he : Real.exp (2.2 / Real.log (X0m / 2)) ≤ 2.72 := by
    have : 2.2 / Real.log (X0m / 2) ≤ 1 := by rw [div_le_iff₀ hly]; linarith
    calc Real.exp (2.2 / Real.log (X0m / 2)) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hΛ : 0 < Real.log X0 := by linarith
  have h1 : Real.log (max (u / X0) (X0m / 2)) / Real.log (X0m / 2) ≤
      1.1 * Real.log u / Real.log X0 := by
    rw [div_le_div_iff₀ hly hΛ]
    nlinarith
  calc Real.log (max (u / X0) (X0m / 2)) / Real.log (X0m / 2) *
        Real.exp (2.2 / Real.log (X0m / 2))
      ≤ 1.1 * Real.log u / Real.log X0 * 2.72 :=
        mul_le_mul h1 he (Real.exp_pos _).le (by
          have : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
          positivity)
    _ ≤ 3 * Real.log u / Real.log X0 := by
        have : 0 ≤ Real.log u / Real.log X0 :=
          div_nonneg (Real.log_nonneg (by linarith)) hΛ.le
        rw [mul_div_assoc, mul_div_assoc]; nlinarith

end params

/-! ### The assembly -/

/-- **`Lemma73bCore` for a system with (HBS), the local count (Step 1 input), the decision order
and Corollary 6.3(ii)**: `|K^sh_ℚ(f₀1)(u) - K_pt(f₀1)(u)| ≤ (1 + 10⁻³) κ (log u)³` on
`[X₀, x_max]`. Inputs:

* `h` : (HBS) on `[1, Z]` with `X₀/2 ≤ X₀⁻ ≤ X₀`, `x_max/X₀ ≤ Z`;
* `hloc` : `|N_𝒩(v) - ⌊v⌋| ≤ ε_HBS(v) v` on `[X₀⁻, Z]` (the conclusion of `BModel.hbs_local`);
* `hdhi`, `hdlo` : the decision order (`|t(p) - p| ≤ H(p)`, `t(p) = p` below `X₀⁻/2`);
* `hlip`, `hsmall` : `H` is `10⁻²`-Lipschitz and `≤ y/10` on `[X₀⁻/2, ∞)` (`PaperWidth`);
* `hcount` : Corollary 6.3(ii) (`46 H(p₀)` primes in `|p - p₀| ≤ 1.71 H(p₀)`);
* `hrat`, `hηκ` : `H(s) ≤ η_H s` on `[X₀⁻/2, ∞)` with `η_H ≤ κ`. -/
theorem lemma73bCore_of {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    {X0 : ℕ} {xmax : ℝ} (h : P.HBS X0m Z η1 η2 ε1) (hX : 10 ^ 8 ≤ Real.log X0)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hZ : xmax / X0 ≤ Z) (hXZ : X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (H : ℝ → ℝ)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    {ηH : ℝ} (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη0 : 0 ≤ ηH)
    (hηκ : ηH ≤ Construction.kappaParam X0) :
    Lemma73bCore P tw X0m X0 xmax := by
  intro u hu hux
  set κ := Construction.kappaParam (X0 : ℝ) with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX0 := X0_pos' hX
  have hXe := exp_one_le_X0 hX
  have hX1 : (1 : ℝ) < X0 := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXe
  have hu0 : 0 < u := by linarith
  have hX7 := h.X0m_ge
  have hQ := ratSys_hbs (X0m := X0m) (Z := Z) hX7
  set x := u / (X0 : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hX0]; linarith
  have hxZ : x ≤ Z := (div_le_div_of_nonneg_right hux hX0.le).trans hZ
  set Λ := Real.log (X0 : ℝ) with hΛdef
  set L := Real.log u with hLdef
  have hΛ : 10 ^ 8 ≤ Λ := hX
  have hLΛ : Λ ≤ L := Real.log_le_log hX0 hu
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlxL : Real.log x ≤ L := Real.log_le_log (by linarith) (div_le_self hu0.le hX1.le)
  have hXm' : Real.exp 1 ≤ X0m / 2 := by
    have : X0m / 2 ≥ X0 / 4 := by linarith
    have h4 : Real.exp 1 * 4 ≤ X0 := by
      rw [← Real.exp_log hX0]
      have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.exp 1 * 4 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
        _ = Real.exp 3 := by rw [← Real.exp_add, ← Real.exp_add]; norm_num
        _ ≤ Real.exp (Real.log X0) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- Step 3: the realised against the rational system
  set B := 2 * (4 * κ) + 2.1 / Real.sqrt (X0m / 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB9 : B ≤ 9 * κ := B_le hX hXm1
  have hpq : ∀ j < J1 X0m, P.p j = ratSys.p j := fun j hj => (small_eq h hXZ hj).1
  have h3 := S3.kval_diff_le (P := P) (Q := ratSys) (J1 := J1 X0m) hpq hXe hκ0 hκ1 hu0 hXm' hB0
    (fun j hj => (small_eq h hXZ hj).2) (fun j hj => large_ge h hXZ hj)
    (fun j hj => (small_eq hQ hXZ hj).2) (fun j hj => large_ge hQ hXZ hj)
    (thetaF_diff_le h (A := 4 * κ) (by positivity) hxZ hXZ (hloc_A h hX hXm1 hxZ hloc))
    (D0_le h hX hXm1 hXm2 hXZ x) (S1_le h hXZ hxZ) (S1_le hQ hXZ hxZ) (Q2_le h hXZ hxZ)
    (Q2_le hQ hXZ hxZ) (h.harm_le hx1 hxZ) (hQ.harm_le hx1 hxZ)
  -- the decision-order mismatch
  have hm := kpt_sub_kval_le P tw H hXe (by linarith) hXm2 hu0 hκ0 hκ1 hdhi hdlo hlip hsmall
    hcount hrat hη0 (h.harm_le hx1 hxZ)
  rw [kshQ_eq_kval hX1 hκ0 hu0]
  set E := Real.exp (Real.log (Real.log (max x (X0m / 2)) / Real.log (X0m / 2)) +
    2.2 / Real.log (X0m / 2)) with hEdef
  have hE : E ≤ 3 * L / Λ := exp_S1_le hX hXm1 hXm2 hu
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hQ2 : 12.8 / X0m ≤ 12.8 * κ := by
    have := inv_X0m_le hX hXm1
    rw [div_eq_mul_one_div]; nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hL1 : 1 ≤ L := by linarith
  -- the four terms
  have hT1 : 12 * B * Real.log x ^ 2 * (5 * Λ) / Λ * E ≤ 1620 * κ * L ^ 3 / Λ := by
    have e : 12 * B * Real.log x ^ 2 * (5 * Λ) / Λ * E = 60 * B * Real.log x ^ 2 * E := by
      field_simp; ring
    rw [e]
    calc 60 * B * Real.log x ^ 2 * E ≤ 60 * (9 * κ) * L ^ 2 * (3 * L / Λ) := by
          gcongr
      _ = 1620 * κ * L ^ 3 / Λ := by ring
  have hT2 : 5 * Λ / Λ * (12.8 / X0m) * E ≤ 192 * κ * L / Λ := by
    have e : 5 * Λ / Λ * (12.8 / X0m) * E = 5 * (12.8 / X0m) * E := by field_simp
    rw [e]
    calc 5 * (12.8 / X0m) * E ≤ 5 * (12.8 * κ) * (3 * L / Λ) := by
          gcongr
      _ = 192 * κ * L / Λ := by ring
  have hT3 : 2 * (12.8 / X0m * (Real.log x + 1) / Λ) ≤ 51.2 * κ * L / Λ := by
    have : 12.8 / X0m * (Real.log x + 1) ≤ 12.8 * κ * (2 * L) :=
      mul_le_mul hQ2 (by linarith) (by positivity) (by positivity)
    have : 12.8 / X0m * (Real.log x + 1) / Λ ≤ 12.8 * κ * (2 * L) / Λ :=
      div_le_div_of_nonneg_right this hΛ0.le
    calc 2 * (12.8 / X0m * (Real.log x + 1) / Λ) ≤ 2 * (12.8 * κ * (2 * L) / Λ) := by linarith
      _ = 51.2 * κ * L / Λ := by ring
  have hT4 : 56 * ηH * (Real.log x + 1) / Λ ≤ 112 * κ * L / Λ := by
    apply div_le_div_of_nonneg_right _ hΛ0.le
    have : ηH * (Real.log x + 1) ≤ κ * (2 * L) :=
      mul_le_mul hηκ (by linarith) (by positivity) hκ0.le
    linarith
  have hsum : 1620 * κ * L ^ 3 / Λ + 192 * κ * L / Λ + 51.2 * κ * L / Λ + 112 * κ * L / Λ ≤
      (1 + 1 / 10 ^ 3) * κ * L ^ 3 := by
    have hLL : L ≤ L ^ 3 := by
      have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      calc L = L * 1 := (mul_one L).symm
        _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = L ^ 3 := by ring
    have hk3 : 0 ≤ κ * L ^ 3 := by positivity
    have ha : κ * L ≤ κ * L ^ 3 := mul_le_mul_of_nonneg_left hLL hκ0.le
    have e : 1620 * κ * L ^ 3 / Λ + 192 * κ * L / Λ + 51.2 * κ * L / Λ + 112 * κ * L / Λ =
        (1620 * (κ * L ^ 3) + 355.2 * (κ * L)) / Λ := by ring
    rw [e, div_le_iff₀ hΛ0]
    have hb : κ * L ^ 3 * 1976 ≤ κ * L ^ 3 * ((1 + 1 / 10 ^ 3) * Λ) :=
      mul_le_mul_of_nonneg_left (by linarith) hk3
    linarith
  have htri : |S3.Kval ratSys X0 κ u - KR.Sharp.Kpt P tw X0m (f0cut X0) u| ≤
      |S3.Kval P X0 κ u - S3.Kval ratSys X0 κ u| +
        |KR.Sharp.Kpt P tw X0m (f0cut X0) u - S3.Kval P X0 κ u| := by
    have := abs_sub_le (S3.Kval ratSys X0 κ u) (S3.Kval P X0 κ u)
      (KR.Sharp.Kpt P tw X0m (f0cut X0) u)
    rw [abs_sub_comm (S3.Kval ratSys X0 κ u) (S3.Kval P X0 κ u),
      abs_sub_comm (S3.Kval P X0 κ u) (KR.Sharp.Kpt P tw X0m (f0cut X0) u)] at this
    exact this
  have hfin := add_le_add h3 hm
  refine htri.trans (hfin.trans ?_)
  have := add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
  linarith
end BaseRange
