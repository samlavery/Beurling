module

public import RequestProject.Beurling.Queue6.RhoNoise

/-!
# The `ν`, `δ` inputs of Step 4 (`hS4_of`) and the (SW) sums of Lemma 5.22

With `L_m = log u_m = Λ + m log 2` (`u_m = 2^m X₀`, `Λ = log X₀`) and `A = log X₀⁻`:

* `s2_decay` : `s₂(u) ≤ 9 e^{-A/2} L^{-3}` (`e^{-max(A, B)} ≤ e^{-A/2} e^{-B/2}` and
  `L⁴ e^{-B/2} ≤ 1`, `B = ½√(L log L)`);
* `nuQ X₀ v = 1.1 s₂(v) + 1.1 s₂(2v) + 105 (log v)^{-6}`, `dQ X₀ v = 30 log(4v)/H(v)`:
  the per-scale noise and `H`-variation of Step 2 (Lemma 5.22, the `ν`, `δ` of `hS4_of`);
* `err_le_nuQ` : the error of Step 2 (`hS2err`'s left side) at `z` is
  `≤ 2 ν(u₁) + δ(u₁)` for `0 ≤ m* ≤ 3.1 log z + 4.2`, `u₁` the block of `z`;
* `sum_nuQ_le`, `sum_dQ_le` : for every finite set of scales `M`,
  `∑_{m ∈ M} log(3u_m) ν(u_m) ≤ 200 Λ^{-4}` and `∑_{m ∈ M} log(3u_m) δ(u_m) ≤ Λ^{-4}`
  (the (SW) sums; `Λ ≥ 10⁸`, so both are `≤ 2·10⁻³⁰`);
* `logy_nuB_le` : `log y · ν̄(y) ≤ 10⁻²⁶` (the size in `hsmall2` for the noise of `rho_noise`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono

namespace Queue6

open BModel

variable (X₀ : ℕ)

/-- The per-scale noise `ν(v) = 1.1 s₂(v) + 1.1 s₂(2v) + 105 (log v)^{-6}`. -/
noncomputable def nuQ (v : ℝ) : ℝ :=
  1.1 * s2E3 X₀ v + 1.1 * s2E3 X₀ (2 * v) + 105 / Real.log v ^ 6

/-- The per-scale `H`-variation term `δ(v) = 30 log(4v)/H(v)`. -/
noncomputable def dQ (v : ℝ) : ℝ := 30 * Real.log (4 * v) / capH X₀ v

variable {X₀} {θ : ℝ} (hc : Cond θ X₀)
include hc

lemma log_uS (m : ℕ) : Real.log (uS X₀ m) = Real.log X₀ + m * Real.log 2 := by
  have hX0 : (0 : ℝ) < X₀ := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  unfold uS
  rw [Real.log_mul (by positivity) hX0.ne', Real.log_pow]; ring

/-- `e^{-A/2} ≤ Λ^{-10}`, `A = log X₀⁻`, `Λ = log X₀`. -/
lemma expA_le : Real.exp (-(Real.log (Xm X₀)) / 2) ≤ 1 / Real.log X₀ ^ 10 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  set Λ := Real.log X₀ with hset1
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    unfold Xm; linarith
  have hA : Λ - 0.02 ≤ Real.log (Xm X₀) := by
    have h1 := Real.log_le_log (by positivity) hXm
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have : -0.02 ≤ Real.log 0.99 := by
      have := Real.add_one_le_exp (-0.02 : ℝ)
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h2 := Real.exp_le_exp.mpr (show (-0.02 : ℝ) ≤ -0.02 by norm_num)
      have : Real.exp (-0.02) ≤ 0.99 := by
        have h3 := Real.add_one_le_exp (0.02 : ℝ)
        have h4 : Real.exp (-0.02) * Real.exp 0.02 = 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (-0.02)]
      exact this
    linarith
  have hΛ0 : 0 < Λ := by linarith
  -- `Λ^{10} e^{-A/2} ≤ 1`: `10 log Λ ≤ (Λ - 0.02)/2`
  have hlog : 10 * Real.log Λ ≤ (Λ - 0.02) / 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < Λ / 10 ^ 6 by positivity)
    rw [Real.log_div hΛ0.ne' (by norm_num)] at this
    have h6 : Real.log ((10 : ℝ) ^ 6) ≤ 14 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (14 : ℝ)
      have he := Real.exp_one_gt_d9
      have e : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
      have : (2.7 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) (by linarith) 14
      rw [e]; nlinarith
    norm_num at this h6 ⊢; linarith
  rw [le_div_iff₀ (by positivity)]
  have e : Λ ^ 10 = Real.exp (10 * Real.log Λ) := by
    rw [show 10 * Real.log Λ = Real.log (Λ ^ 10) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [e, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- **`s₂(u) ≤ 9 e^{-A/2} L^{-3}`** for `u ≥ X₀`, `L = log u`. -/
lemma s2_decay {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    s2E3 X₀ u ≤ 9 * Real.exp (-(Real.log (Xm X₀)) / 2) / Real.log u ^ 3 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, hll⟩ := logs_of_ge hX0 hc.hX hu
  set L := Real.log u with hset2
  set A := Real.log (Xm X₀) with hset3
  set B := Real.sqrt (L * Real.log L) / 2 with hset4
  have hL0 : 0 < L := by linarith
  -- `L⁴ ≤ e^{B/2}`
  have hll18 : 18 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have he := Real.exp_one_lt_d9
    have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 18
    rw [e]; nlinarith
  have hB : 4 * Real.log L ≤ B / 2 := by
    -- `√(L log L) ≥ 16 log L` as `L ≥ 256 log L`
    have hlL : Real.log L ≤ L / 1000 + 7 := by
      have := Real.log_le_sub_one_of_pos (show 0 < L / 1000 by positivity)
      rw [Real.log_div hL0.ne' (by norm_num)] at this
      have : Real.log 1000 ≤ 7 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he := Real.exp_one_gt_d9
        have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
        have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
        rw [e]; nlinarith
      linarith
    have h1 : (16 * Real.log L) ^ 2 ≤ L * Real.log L := by nlinarith
    have h2 : 16 * Real.log L ≤ Real.sqrt (L * Real.log L) :=
      Real.le_sqrt_of_sq_le h1
    show 4 * Real.log L ≤ Real.sqrt (L * Real.log L) / 2 / 2
    linarith
  have hL4 : L ^ 4 ≤ Real.exp (B / 2) := by
    rw [show L ^ 4 = Real.exp (4 * Real.log L) by
      rw [show 4 * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]]
    exact Real.exp_le_exp.mpr hB
  have hA0 : 0 ≤ A := by
    have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
      have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
      unfold Xm; linarith
    exact Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
  have hB0 : 0 ≤ B := by positivity
  have hmax : Real.exp (-(max A B)) ≤ Real.exp (-A / 2) * Real.exp (-(B / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := le_max_left A B
    have := le_max_right A B
    linarith
  unfold s2E3
  rw [le_div_iff₀ (by positivity)]
  have hBe : Real.exp (-(B / 2)) * Real.exp (B / 2) = 1 := by rw [← Real.exp_add]; simp
  have hEA := Real.exp_pos (-A / 2)
  have hEB := Real.exp_pos (-(B / 2))
  calc 9 * L * Real.exp (-max A B) * L ^ 3 = 9 * L ^ 4 * Real.exp (-max A B) := by ring
    _ ≤ 9 * Real.exp (B / 2) * (Real.exp (-A / 2) * Real.exp (-(B / 2))) := by
        gcongr
    _ = 9 * Real.exp (-A / 2) := by
        have : Real.exp (B / 2) * Real.exp (-(B / 2)) = 1 := by rw [mul_comm]; exact hBe
        linear_combination 9 * Real.exp (-A / 2) * this

/-- **The telescoping bound**: `∑_{m < N} L_m^{-2} ≤ Λ^{-2} + 1.45 Λ^{-1}`. -/
lemma sum_inv_sq_le (N : ℕ) :
    ∑ m ∈ range N, 1 / Real.log (uS X₀ m) ^ 2 ≤
      1 / Real.log X₀ ^ 2 + 1.45 / Real.log X₀ := by
  set Λ := Real.log X₀ with hset5
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  have hl2 : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set c := Real.log 2 with hset6
  have hL : ∀ m : ℕ, Real.log (uS X₀ m) = Λ + m * c := fun m => log_uS hc m
  have hpos : ∀ m : ℕ, 0 < Λ + m * c := fun m => by
    have : (0 : ℝ) ≤ m * c := by positivity
    linarith
  -- `L_{m+1}^{-2} ≤ (1/c) (L_m^{-1} - L_{m+1}^{-1})`
  have hstep : ∀ m : ℕ, 1 / (Λ + ((m + 1 : ℕ) : ℝ) * c) ^ 2 ≤
      (1 / c) * (1 / (Λ + m * c) - 1 / (Λ + ((m + 1 : ℕ) : ℝ) * c)) := by
    intro m
    have h1 := hpos m
    have h2 := hpos (m + 1)
    have e : 1 / (Λ + m * c) - 1 / (Λ + ((m + 1 : ℕ) : ℝ) * c) =
        c / ((Λ + m * c) * (Λ + ((m + 1 : ℕ) : ℝ) * c)) := by
      push_cast; field_simp; ring
    rw [e, div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : Λ + m * c ≤ Λ + ((m + 1 : ℕ) : ℝ) * c := by push_cast; nlinarith
    rw [one_mul, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this h2.le) (by linarith)
  have htel : ∀ N : ℕ, ∑ m ∈ range N, 1 / (Λ + ((m + 1 : ℕ) : ℝ) * c) ^ 2 ≤
      (1 / c) * (1 / Λ - 1 / (Λ + (N : ℝ) * c)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have := hstep N
      calc _ ≤ (1 / c) * (1 / Λ - 1 / (Λ + (N : ℝ) * c)) +
            (1 / c) * (1 / (Λ + N * c) - 1 / (Λ + ((N + 1 : ℕ) : ℝ) * c)) := add_le_add ih this
        _ = (1 / c) * (1 / Λ - 1 / (Λ + ((N + 1 : ℕ) : ℝ) * c)) := by ring
  rcases N with _ | N
  · simp; positivity
  · rw [sum_range_succ']
    have h0 : 1 / Real.log (uS X₀ 0) ^ 2 = 1 / Λ ^ 2 := by rw [hL]; simp
    have e : ∑ m ∈ range N, 1 / Real.log (uS X₀ (m + 1)) ^ 2 =
        ∑ m ∈ range N, 1 / (Λ + ((m + 1 : ℕ) : ℝ) * c) ^ 2 :=
      sum_congr rfl fun m _ => by rw [hL]
    rw [e, h0]
    have h1 := htel N
    have h2 : 0 < Λ + (N : ℝ) * c := hpos N
    have h3 : (1 / c) * (1 / Λ - 1 / (Λ + (N : ℝ) * c)) ≤ 1.45 / Λ := by
      have : 1 / Λ - 1 / (Λ + (N : ℝ) * c) ≤ 1 / Λ := by
        have : 0 < 1 / (Λ + (N : ℝ) * c) := by positivity
        linarith
      have hc0 : 0 < c := by linarith
      calc (1 / c) * (1 / Λ - 1 / (Λ + (N : ℝ) * c)) ≤ (1 / c) * (1 / Λ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 1.45 / Λ := by
            rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    linarith

/-- The per-scale summand: `log(3u) ν(u) ≤ 30 e^{-A/2} L^{-2} + 107 L^{-5}`. -/
lemma log_nuQ_le (m : ℕ) :
    Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m) ≤
      30 * Real.exp (-(Real.log (Xm X₀)) / 2) / Real.log (uS X₀ m) ^ 2 +
        107 / Real.log (uS X₀ m) ^ 5 := by
  obtain ⟨hu, hl, -, -⟩ := uS_facts hc m
  obtain ⟨hu', hl', -, -⟩ := uS_facts hc (m + 1)
  set L := Real.log (uS X₀ m) with hset7
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < uS X₀ m := by linarith [X₀_ge_two_pow hc.hX]
  have hl3 : Real.log (3 * uS X₀ m) ≤ 1.01 * L := by
    rw [Real.log_mul (by norm_num) hu0.ne']
    have : Real.log 3 ≤ 1.2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.add_one_le_exp (0.2 : ℝ)
      have h2 := Real.exp_one_gt_d9
      have h3 : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hl30 : 0 ≤ Real.log (3 * uS X₀ m) :=
    Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
  set e := Real.exp (-(Real.log (Xm X₀)) / 2) with hset8
  have he0 : 0 < e := Real.exp_pos _
  have hs1 := s2_decay hc hu
  have h2u : 2 * uS X₀ m = uS X₀ (m + 1) := (uS_succ m).symm
  have hs2 := s2_decay hc hu'
  rw [← h2u] at hs2
  have hLL : L ≤ Real.log (2 * uS X₀ m) := Real.log_le_log hu0 (by linarith)
  have hs2' : s2E3 X₀ (2 * uS X₀ m) ≤ 9 * e / L ^ 3 :=
    hs2.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hL0.le hLL 3))
  have hs1p := s2E3_pos hc (uS X₀ m) hl
  have hs2p : 0 < s2E3 X₀ (2 * uS X₀ m) := s2E3_pos hc _ (hl.trans hLL)
  have hnu : nuQ X₀ (uS X₀ m) ≤ 1.1 * (9 * e / L ^ 3) + 1.1 * (9 * e / L ^ 3) +
      105 / L ^ 6 := by
    unfold nuQ; gcongr
  have hnu0 : 0 ≤ 1.1 * (9 * e / L ^ 3) + 1.1 * (9 * e / L ^ 3) + 105 / L ^ 6 := by positivity
  calc Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m)
      ≤ (1.01 * L) * (1.1 * (9 * e / L ^ 3) + 1.1 * (9 * e / L ^ 3) + 105 / L ^ 6) :=
        mul_le_mul hl3 hnu (by unfold nuQ; positivity) (by positivity)
    _ = 19.998 * e / L ^ 2 + 106.05 / L ^ 5 := by field_simp; ring
    _ ≤ 30 * e / L ^ 2 + 107 / L ^ 5 := by
        gcongr <;> norm_num

/-- **The (SW) sum of the noise**: `∑_{m ∈ M} log(3u_m) ν(u_m) ≤ 200 Λ^{-4}`. -/
theorem sum_nuQ_le (M : Finset ℕ) :
    ∑ m ∈ M, Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m) ≤ 200 / Real.log X₀ ^ 4 := by
  set Λ := Real.log X₀ with hset9
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  have hΛ0 : 0 < Λ := by linarith
  set N := M.sup id + 1 with hset10
  have hMN : M ⊆ range N := fun m hm => mem_range.mpr (by
    have := le_sup (f := id) hm; simp only [id] at this; omega)
  set e := Real.exp (-(Real.log (Xm X₀)) / 2) with hset11
  have he : e ≤ 1 / Λ ^ 10 := expA_le hc
  have hterm : ∀ m, Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m) ≤
      (30 * e + 107 / Λ ^ 3) * (1 / Real.log (uS X₀ m) ^ 2) := fun m => by
    have h := log_nuQ_le hc m
    obtain ⟨hu, hl, -, -⟩ := uS_facts hc m
    set L := Real.log (uS X₀ m) with hset12
    have hLΛ : Λ ≤ L := by
      rw [hset12, log_uS hc m]; have : (0 : ℝ) ≤ m * Real.log 2 := by positivity
      linarith
    have hL0 : 0 < L := by linarith
    have : 107 / L ^ 5 ≤ 107 / Λ ^ 3 * (1 / L ^ 2) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have : Λ ^ 3 * L ^ 2 ≤ L ^ 5 := by
        have : Λ ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hΛ0.le hLΛ 3
        nlinarith [pow_pos hL0 2]
      nlinarith
    calc _ ≤ 30 * e / L ^ 2 + 107 / L ^ 5 := h
      _ ≤ 30 * e * (1 / L ^ 2) + 107 / Λ ^ 3 * (1 / L ^ 2) := by
          have : 30 * e / L ^ 2 = 30 * e * (1 / L ^ 2) := by ring
          linarith
      _ = (30 * e + 107 / Λ ^ 3) * (1 / L ^ 2) := by ring
  have hnn : ∀ m ∈ range N, 0 ≤ Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m) := fun m _ => by
    obtain ⟨hu, hl, -, -⟩ := uS_facts hc m
    have := s2E3_pos hc (uS X₀ m) hl
    have hu0 : 1 ≤ 3 * uS X₀ m := by linarith [X₀_ge_two_pow hc.hX]
    have h2 : (2 : ℝ) ^ 16 ≤ X₀ := X₀_ge_two_pow hc.hX
    have h3 := s2E3_pos hc (2 * uS X₀ m) (hl.trans (Real.log_le_log (by linarith) (by linarith)))
    have h6 : 0 ≤ 105 / Real.log (uS X₀ m) ^ 6 := by positivity
    exact mul_nonneg (Real.log_nonneg hu0) (by unfold nuQ; linarith)
  calc ∑ m ∈ M, Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m)
      ≤ ∑ m ∈ range N, Real.log (3 * uS X₀ m) * nuQ X₀ (uS X₀ m) :=
        sum_le_sum_of_subset_of_nonneg hMN fun m hm _ => hnn m hm
    _ ≤ ∑ m ∈ range N, (30 * e + 107 / Λ ^ 3) * (1 / Real.log (uS X₀ m) ^ 2) :=
        sum_le_sum fun m _ => hterm m
    _ = (30 * e + 107 / Λ ^ 3) * ∑ m ∈ range N, 1 / Real.log (uS X₀ m) ^ 2 := by
        rw [mul_sum]
    _ ≤ (30 * e + 107 / Λ ^ 3) * (1 / Λ ^ 2 + 1.45 / Λ) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le hc N) (by positivity)
    _ ≤ 200 / Λ ^ 4 := by
        have h1 : 30 * e ≤ 30 / Λ ^ 10 := by
          have := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 30)
          exact this.trans (le_of_eq (by ring))
        have hΛ1 : 1 ≤ Λ := by linarith
        have : (30 * e + 107 / Λ ^ 3) ≤ 108 / Λ ^ 3 := by
          have : 30 / Λ ^ 10 ≤ 1 / Λ ^ 3 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h4 : Λ ^ 4 ≤ Λ ^ 10 := pow_le_pow_right₀ hΛ1 (by norm_num)
            have : 30 * Λ ^ 3 ≤ Λ ^ 4 := by
              have : Λ ^ 4 = Λ * Λ ^ 3 := by ring
              nlinarith [pow_pos hΛ0 3]
            linarith
          have e2 : 108 / Λ ^ 3 = 1 / Λ ^ 3 + 107 / Λ ^ 3 := by ring
          linarith
        have h2 : 1 / Λ ^ 2 + 1.45 / Λ ≤ 1.46 / Λ := by
          rw [div_add_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos hΛ0 2]
        calc (30 * e + 107 / Λ ^ 3) * (1 / Λ ^ 2 + 1.45 / Λ)
            ≤ 108 / Λ ^ 3 * (1.46 / Λ) :=
              mul_le_mul this h2 (by positivity) (by positivity)
          _ = 157.68 / Λ ^ 4 := by field_simp; ring
          _ ≤ 200 / Λ ^ 4 := by gcongr; norm_num

/-- **The (SW) sum of the `H`-variation**: `∑_{m ∈ M} log(3u_m) δ(u_m) ≤ Λ^{-4}`. -/
theorem sum_dQ_le (M : Finset ℕ) :
    ∑ m ∈ M, Real.log (3 * uS X₀ m) * dQ X₀ (uS X₀ m) ≤ 1 / Real.log X₀ ^ 4 := by
  set Λ := Real.log X₀ with hset13
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  have hΛ0 : 0 < Λ := by linarith
  set N := M.sup id + 1 with hset14
  have hMN : M ⊆ range N := fun m hm => mem_range.mpr (by
    have := le_sup (f := id) hm; simp only [id] at this; omega)
  have hterm : ∀ m, Real.log (3 * uS X₀ m) * dQ X₀ (uS X₀ m) ≤
      1 / Λ ^ 6 * (1 / Real.log (uS X₀ m) ^ 2) := fun m => by
    obtain ⟨hu, hl, hH1, -⟩ := uS_facts hc m
    obtain ⟨h32, -⟩ := capH_big hc hu
    set L := Real.log (uS X₀ m) with hset15
    have hLΛ : Λ ≤ L := by
      rw [hset15, log_uS hc m]; have : (0 : ℝ) ≤ m * Real.log 2 := by positivity
      linarith
    have hL0 : 0 < L := by linarith
    have hu0 : 0 < uS X₀ m := by linarith [X₀_ge_two_pow hc.hX]
    have hl34 : Real.log (3 * uS X₀ m) ≤ L + 2 ∧ Real.log (4 * uS X₀ m) ≤ L + 2 := by
      rw [Real.log_mul (by norm_num) hu0.ne', Real.log_mul (by norm_num) hu0.ne']
      have h4 : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith
      have h3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      constructor <;> linarith
    have hl30 : 0 ≤ Real.log (3 * uS X₀ m) :=
      Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    have hl40 : 0 ≤ Real.log (4 * uS X₀ m) :=
      Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    unfold dQ
    have hH0 : 0 < capH X₀ (uS X₀ m) := by linarith
    rw [show Real.log (3 * uS X₀ m) * (30 * Real.log (4 * uS X₀ m) / capH X₀ (uS X₀ m)) =
      30 * (Real.log (3 * uS X₀ m) * Real.log (4 * uS X₀ m)) / capH X₀ (uS X₀ m) by ring]
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ hH0 (by positivity)]
    have hprod : Real.log (3 * uS X₀ m) * Real.log (4 * uS X₀ m) ≤ (L + 2) ^ 2 := by
      have := mul_le_mul hl34.1 hl34.2 hl40 (by linarith)
      nlinarith
    have hL2 : (L + 2) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
    have hL32 : 60 * L ^ 2 * (Λ ^ 6 * L ^ 2) ≤ L ^ 32 := by
      have : Λ ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ hΛ0.le hLΛ 6
      have h10 : 60 * L ^ 10 ≤ L ^ 32 := by
        have : L ^ 32 = L ^ 10 * L ^ 22 := by ring
        have h22 : (60 : ℝ) ≤ L ^ 22 := le_trans (by norm_num) (hl.trans (le_self_pow₀
          (by linarith) (by norm_num)))
        nlinarith [pow_pos hL0 10]
      nlinarith [pow_pos hL0 4, pow_pos hΛ0 6]
    have hP : Real.log (3 * uS X₀ m) * Real.log (4 * uS X₀ m) ≤ 2 * L ^ 2 := hprod.trans hL2
    have hpos6 : 0 ≤ Λ ^ 6 * L ^ 2 := by positivity
    calc 30 * (Real.log (3 * uS X₀ m) * Real.log (4 * uS X₀ m)) * (Λ ^ 6 * L ^ 2)
        ≤ 30 * (2 * L ^ 2) * (Λ ^ 6 * L ^ 2) := by gcongr
      _ = 60 * L ^ 2 * (Λ ^ 6 * L ^ 2) := by ring
      _ ≤ L ^ 32 := hL32
      _ ≤ 1 * capH X₀ (uS X₀ m) := by rw [one_mul]; exact h32
  have hnn : ∀ m ∈ range N, 0 ≤ Real.log (3 * uS X₀ m) * dQ X₀ (uS X₀ m) := fun m _ => by
    obtain ⟨hu, hl, hH1, -⟩ := uS_facts hc m
    have hu0 : 1 ≤ 3 * uS X₀ m := by linarith [X₀_ge_two_pow hc.hX]
    have : 0 ≤ Real.log (4 * uS X₀ m) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (3 * uS X₀ m) := Real.log_nonneg hu0
    unfold dQ; positivity
  calc ∑ m ∈ M, Real.log (3 * uS X₀ m) * dQ X₀ (uS X₀ m)
      ≤ ∑ m ∈ range N, Real.log (3 * uS X₀ m) * dQ X₀ (uS X₀ m) :=
        sum_le_sum_of_subset_of_nonneg hMN fun m hm _ => hnn m hm
    _ ≤ ∑ m ∈ range N, 1 / Λ ^ 6 * (1 / Real.log (uS X₀ m) ^ 2) :=
        sum_le_sum fun m _ => hterm m
    _ = 1 / Λ ^ 6 * ∑ m ∈ range N, 1 / Real.log (uS X₀ m) ^ 2 := by rw [mul_sum]
    _ ≤ 1 / Λ ^ 6 * (1 / Λ ^ 2 + 1.45 / Λ) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le hc N) (by positivity)
    _ ≤ 1 / Λ ^ 4 := by
        rw [mul_add, div_mul_div_comm, div_mul_div_comm, one_mul, one_mul]
        have h1 : 1 / (Λ ^ 6 * Λ ^ 2) ≤ 1 / (2 * Λ ^ 4) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          have : 2 * Λ ^ 4 ≤ Λ ^ 8 := by
            have : Λ ^ 8 = Λ ^ 4 * Λ ^ 4 := by ring
            have h4 : (2 : ℝ) ≤ Λ ^ 4 := le_trans (by norm_num) (hΛ.trans (le_self_pow₀
              (by linarith) (by norm_num)))
            nlinarith [pow_pos hΛ0 4]
          nlinarith
        have h2 : 1.45 / (Λ ^ 6 * Λ) ≤ 1 / (2 * Λ ^ 4) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : Λ ^ 6 * Λ = Λ ^ 4 * Λ ^ 3 := by ring
          have h3 : (3 : ℝ) ≤ Λ ^ 3 := le_trans (by norm_num) (hΛ.trans (le_self_pow₀
            (by linarith) (by norm_num)))
          rw [this]; nlinarith [pow_pos hΛ0 4]
        have e : 1 / (2 * Λ ^ 4) + 1 / (2 * Λ ^ 4) = 1 / Λ ^ 4 := by field_simp; ring
        linarith

/-- **The Step 2 error is `2ν(u₁) + δ(u₁)`**: for `0 ≤ m* ≤ 3.1 log z + 4.2` and `X₀ ≤ z`,
`2 ε_z/H(z) + (3.3 + 2.1 m*) δ_z ≤ 2 ν(u₁) + δ(u₁)`, `u₁ = u_{m₁(z)}`. -/
theorem err_le_nuQ {z mst : ℝ} (hz : (X₀ : ℝ) ≤ z) (hm0 : 0 ≤ mst)
    (hm : mst ≤ 3.1 * Real.log z + 4.2) :
    2 * s2ε X₀ z / Hc X₀ z + (3.3 + 2.1 * mst) * s2δ X₀ z ≤
      2 * nuQ X₀ (uS X₀ (m1z X₀ z)) + dQ X₀ (uS X₀ (m1z X₀ z)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX0p : (0 : ℝ) < X₀ := by linarith [X₀_ge_two_pow hc.hX]
  have h := hS2err_R hc z mst
  set m1 := m1z X₀ z with hset16
  set u1 := uS X₀ m1 with hset17
  obtain ⟨hu1X, hl1, hH1, -⟩ := uS_facts hc m1
  obtain ⟨hm1a, hm1b⟩ := mB_spec hX0p (le_max_right (z - Hc X₀ z) (X₀ : ℝ))
  have hH0 := Hc_nonneg (X₀ := X₀) z
  have hu1z : u1 ≤ z := hm1a.trans (max_le (by linarith) hz)
  have hz4 : z ≤ 4 * u1 := by
    have h2 : max (z - Hc X₀ z) (X₀ : ℝ) < 2 * u1 := by
      have := hm1b; rw [uS_succ] at this; exact this
    have hHz : Hc X₀ z ≤ z / 10 ^ 7 := by have := Hc_le hc z; rwa [max_eq_left hz] at this
    have := le_max_left (z - Hc X₀ z) (X₀ : ℝ)
    linarith
  have hHH : capH X₀ u1 ≤ Hc X₀ z := by
    rw [Hc_eq hz]
    exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hu1X) (mem_Ici.mpr hz) hu1z
  have hH1p : 0 < capH X₀ u1 := by linarith
  have h2u : uS X₀ (m1 + 1) = 2 * u1 := uS_succ m1
  -- `(6.6 + 4.2 m*)/H(z) ≤ 30 log(4u₁)/H(u₁)`
  have hlz : Real.log z ≤ Real.log (4 * u1) := Real.log_le_log (by linarith) hz4
  have hl4 : 2 ≤ Real.log (4 * u1) := by
    have h1 := Real.log_le_log (by linarith) (show u1 ≤ 4 * u1 by linarith)
    have h2 : Real.log u1 = Real.log (uS X₀ m1) := rfl
    linarith
  have hd : (6.6 + 4.2 * mst) / Hc X₀ z ≤ dQ X₀ u1 := by
    unfold dQ
    have h1 : 6.6 + 4.2 * mst ≤ 30 * Real.log (4 * u1) := by nlinarith
    calc (6.6 + 4.2 * mst) / Hc X₀ z ≤ (6.6 + 4.2 * mst) / capH X₀ u1 :=
          div_le_div_of_nonneg_left (by linarith) hH1p hHH
      _ ≤ 30 * Real.log (4 * u1) / capH X₀ u1 := div_le_div_of_nonneg_right h1 hH1p.le
  rw [h2u] at h
  unfold nuQ
  have e : 2 * (1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ (2 * u1) + 105 / Real.log u1 ^ 6) =
      2.2 * s2E3 X₀ u1 + 2.2 * s2E3 X₀ (2 * u1) + 210 / Real.log u1 ^ 6 := by ring
  rw [e]
  linarith

/-- **The size of `ν̄`** (for `hsmall2`): `log y · ν̄(y) ≤ 10⁻²⁶`, `X₀ ≤ y`. -/
theorem logy_nuB_le {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    Real.log y * nuB X₀ y ≤ 1 / 10 ^ 26 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX0p : (0 : ℝ) < X₀ := by linarith [X₀_ge_two_pow hc.hX]
  set m1 := m1z X₀ y with hset18
  set u1 := uS X₀ m1 with hset19
  have h : nuB X₀ y ≤ 1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ (uS X₀ (m1 + 1)) +
      106 / Real.log u1 ^ 6 := nuB_le hc hy
  obtain ⟨hu1X, hl1, -, -⟩ := uS_facts hc m1
  obtain ⟨hu2X, hl2, -, -⟩ := uS_facts hc (m1 + 1)
  obtain ⟨hm1a, hm1b⟩ := mB_spec hX0p (le_max_right (y - Hc X₀ y) (X₀ : ℝ))
  have hH0 := Hc_nonneg (X₀ := X₀) y
  have hu1y : u1 ≤ y := hm1a.trans (max_le (by linarith) hy)
  have hy4 : y ≤ 4 * u1 := by
    have h2 : max (y - Hc X₀ y) (X₀ : ℝ) < 2 * u1 := by
      have := hm1b; rw [uS_succ] at this; exact this
    have hHz : Hc X₀ y ≤ y / 10 ^ 7 := by have := Hc_le hc y; rwa [max_eq_left hy] at this
    have := le_max_left (y - Hc X₀ y) (X₀ : ℝ)
    linarith
  set L := Real.log u1 with hset20
  have hL0 : 0 < L := by linarith
  have hu10 : 0 < u1 := by linarith [X₀_ge_two_pow hc.hX]
  have hly : Real.log y ≤ 2 * L := by
    have h1 := Real.log_le_log (by linarith) hy4
    rw [Real.log_mul (by norm_num) hu10.ne'] at h1
    have : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith
    linarith
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
  set e := Real.exp (-(Real.log (Xm X₀)) / 2) with hset21
  have he : e ≤ 1 / Real.log X₀ ^ 10 := expA_le hc
  have hs1 : s2E3 X₀ u1 ≤ 9 * e / L ^ 3 := s2_decay hc hu1X
  have hs2 := s2_decay hc hu2X
  have hLL : L ≤ Real.log (uS X₀ (m1 + 1)) := Real.log_le_log hu10 (by rw [uS_succ]; linarith)
  have hs2' : s2E3 X₀ (uS X₀ (m1 + 1)) ≤ 9 * e / L ^ 3 :=
    hs2.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hL0.le hLL 3))
  have hnuB0 : 0 ≤ nuB X₀ y := by
    unfold nuB
    have := s2ε_ge hc y
    have : 0 ≤ Real.log (4 * y) := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    have : 0 < Hc X₀ y := lt_of_lt_of_le one_pos
      (capH_ge_one hX0 hc.hX (le_max_right y (X₀ : ℝ)))
    positivity
  have hb : nuB X₀ y ≤ 19.8 * e / L ^ 3 + 106 / L ^ 6 := by
    have : 1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ (uS X₀ (m1 + 1)) ≤ 19.8 * e / L ^ 3 := by
      have e2 : 19.8 * e / L ^ 3 = 1.1 * (9 * e / L ^ 3) + 1.1 * (9 * e / L ^ 3) := by ring
      linarith
    linarith
  have hΛ := hc.hX
  have hLΛ : Real.log X₀ ≤ L := by
    have hLd : L = Real.log (uS X₀ m1) := rfl
    rw [hLd, log_uS hc m1]; have : (0 : ℝ) ≤ m1 * Real.log 2 := by positivity
    linarith
  calc Real.log y * nuB X₀ y ≤ (2 * L) * (19.8 * e / L ^ 3 + 106 / L ^ 6) :=
        mul_le_mul hly hb hnuB0 (by positivity)
    _ = 39.6 * e / L ^ 2 + 212 / L ^ 5 := by field_simp; ring
    _ ≤ 1 / 10 ^ 26 := by
        have hL8 : (10 : ℝ) ^ 8 ≤ L := hl1
        have h1 : 39.6 * e / L ^ 2 ≤ 39.6 / 10 ^ 96 := by
          have hΛ10 : (10 : ℝ) ^ 80 ≤ Real.log X₀ ^ 10 := by
            have := pow_le_pow_left₀ (by norm_num) hΛ 10; norm_num at this ⊢; linarith
          have he' : e ≤ 1 / 10 ^ 80 := he.trans (div_le_div_of_nonneg_left (by norm_num)
            (by norm_num) hΛ10)
          have hL2 : (10 : ℝ) ^ 16 ≤ L ^ 2 := by
            have := pow_le_pow_left₀ (by norm_num) hL8 2; norm_num at this ⊢; linarith
          calc 39.6 * e / L ^ 2 ≤ 39.6 * (1 / 10 ^ 80) / 10 ^ 16 := by
                gcongr
            _ = 39.6 / 10 ^ 96 := by norm_num
        have h2 : 212 / L ^ 5 ≤ 212 / 10 ^ 40 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          have := pow_le_pow_left₀ (by norm_num) hL8 5; norm_num at this ⊢; linarith
        have : (39.6 : ℝ) / 10 ^ 96 + 212 / 10 ^ 40 ≤ 1 / 10 ^ 26 := by norm_num
        linarith

end Queue6

end
