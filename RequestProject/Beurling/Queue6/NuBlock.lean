module

public import RequestProject.Beurling.Queue6.RhoLow
public import RequestProject.Beurling.Queue6.NuModel
public import RequestProject.Beurling.Queue6.S4Inputs
public import RequestProject.Beurling.Model.TBoundGood

/-!
# Lemma 5.22 on the dyadic blocks: `BModel.Nu522` for the realised system

Blocks `[v_i, 2v_i)`, `v_i = X₀⁻2ⁱ` (block `0` is `(-∞, 2X₀⁻)`, read at `r ≥ X₀⁻`). With
`ℓ_i = log X₀ + (i - 2) log 2` and `A = e^{-log X₀⁻/2}` the block bound is the explicit majorant
at the block's left end

  `ν̄_i = 19.8 A ℓ_i⁻⁴ + 106 ℓ_i⁻⁶` (`nbQ`):

* `s2_decay4` : `s₂(u) ≤ 9 A L_u⁻⁴` (as `s2_decay`, with `L⁵ ≤ e^{B/2}`);
* `nuB_low_le` : `ν̄(r) ≤ ν̄(X₀)` for `0 < r < X₀` (`H`, `ε` are constant below `X₀`);
* `nuB_le_nbQ` : `ν̄(r) ≤ ν̄_i` for `X₀⁻ ≤ r` in the block `i` (`nuB_le`, the block `u₁` of
  `max(r, X₀)` has `log u₁ ≥ ℓ_i`);
* `nu522_R` : **`Nu522 θ X₀ ω b nbQ`** (with `ϑ = 0`) a.s. on `Good(< t) ∩ NiceEv`, `b ≤ t`
  (`nuModel_eq`, `rho_noise_Xm` at `r + 2H(r) ≤ b ≤ t`); `nu522_tE2` : a.s. on `Good(< tE2 b)`;
* `tele_sum` : `∑_{i<N} (a + ic)^{-(n+1)} ≤ a^{-(n+1)} + (n c aⁿ)⁻¹` (`n ≥ 1`, Bernoulli);
* `sum_nbQ_le` : `∑_{i<N} log(3v_i)² ν̄_i ≤ 10⁻²²` (the `1/ℓ²` and `1/ℓ⁴` telescoping);
* `log_nbQ_le` : `log y · ν̄_i ≤ 10⁻²⁷` for `0 ≤ y ≤ 16 v_i`.
-/

@[expose] public section

open Set Real Finset MeasureTheory Construction CaplLink QueueMono

namespace Queue6

open BModel

variable (X₀ : ℕ)

/-- `ℓ_i = log X₀ + (i - 2) log 2` (`= log(X₀2ⁱ/4)`). -/
noncomputable def ellQ (i : ℕ) : ℝ := Real.log X₀ + ((i : ℝ) - 2) * Real.log 2

/-- **The block bound** `ν̄_i = 19.8 e^{-log X₀⁻/2} ℓ_i⁻⁴ + 106 ℓ_i⁻⁶` of Lemma 5.22. -/
noncomputable def nbQ (i : ℕ) : ℝ :=
  19.8 * Real.exp (-(Real.log (Xm X₀)) / 2) / ellQ X₀ i ^ 4 + 106 / ellQ X₀ i ^ 6

variable {X₀}

/-! ### Telescoping -/

/-- `n c (x + c)^{-(n+1)} ≤ x^{-n} - (x + c)^{-n}` (Bernoulli). -/
lemma step_tele {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (n : ℕ) :
    (n : ℝ) * c / (x + c) ^ (n + 1) ≤ 1 / x ^ n - 1 / (x + c) ^ n := by
  set y := x + c with hye
  have hy : 0 < y := by positivity
  have hcx : 0 ≤ c / x := by positivity
  have hB : 1 + n * (c / x) ≤ (1 + c / x) ^ n := one_add_mul_le_pow (by linarith) n
  have e : 1 + c / x = y / x := by rw [hye]; field_simp
  rw [e, div_pow] at hB
  have hxn : 0 < x ^ n := pow_pos hx n
  have hyn : 0 < y ^ n := pow_pos hy n
  have h1 : (1 + n * (c / x)) / y ^ n ≤ 1 / x ^ n := by
    rw [div_le_div_iff₀ hyn hxn]; rw [le_div_iff₀ hxn] at hB; linarith
  have h2 : (n : ℝ) * c / y ^ (n + 1) ≤ n * (c / x) / y ^ n := by
    rw [pow_succ, div_le_div_iff₀ (by positivity) hyn]
    have e3 : (n : ℝ) * (c / x) * (y ^ n * y) = n * c * y ^ n * (y / x) := by
      field_simp
    rw [e3]
    have hyx : 1 ≤ y / x := by rw [le_div_iff₀ hx]; linarith
    have : 0 ≤ (n : ℝ) * c * y ^ n := by positivity
    nlinarith
  have e2 : (1 + n * (c / x)) / y ^ n = 1 / y ^ n + n * (c / x) / y ^ n := by ring
  linarith

/-- **Telescoping**: `∑_{i<N} (a + ic)^{-(n+1)} ≤ a^{-(n+1)} + (n c aⁿ)⁻¹` for `a, c > 0`,
`n ≥ 1`. -/
lemma tele_sum {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    ∑ i ∈ range N, 1 / (a + i * c) ^ (n + 1) ≤ 1 / a ^ (n + 1) + 1 / (n * c * a ^ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ i : ℕ, 0 < a + i * c := fun i => by positivity
  have hst : ∀ M : ℕ, ∑ i ∈ range M, 1 / (a + ((i + 1 : ℕ) : ℝ) * c) ^ (n + 1) ≤
      (1 / (n * c)) * (1 / a ^ n - 1 / (a + M * c) ^ n) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have hs := step_tele (hpos M) hc.le n
      have e : a + ((M + 1 : ℕ) : ℝ) * c = a + M * c + c := by push_cast; ring
      rw [e]
      have hs' : 1 / (a + M * c + c) ^ (n + 1) ≤
          (1 / (n * c)) * (1 / (a + M * c) ^ n - 1 / (a + M * c + c) ^ n) := by
        rw [show (1 / (n * c)) * (1 / (a + M * c) ^ n - 1 / (a + M * c + c) ^ n) =
          (1 / (a + M * c) ^ n - 1 / (a + M * c + c) ^ n) / (n * c) by ring,
          le_div_iff₀ (by positivity)]
        calc 1 / (a + M * c + c) ^ (n + 1) * (n * c) = n * c / (a + M * c + c) ^ (n + 1) := by
              ring
          _ ≤ _ := hs
      calc _ ≤ (1 / (n * c)) * (1 / a ^ n - 1 / (a + M * c) ^ n) +
            (1 / (n * c)) * (1 / (a + M * c) ^ n - 1 / (a + M * c + c) ^ n) :=
            add_le_add ih hs'
        _ = (1 / (n * c)) * (1 / a ^ n - 1 / (a + M * c + c) ^ n) := by ring
  rcases N with _ | N
  · simp; positivity
  · rw [sum_range_succ']
    have h1 := hst N
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have h2 : (1 / (n * c)) * (1 / a ^ n - 1 / (a + N * c) ^ n) ≤ 1 / (n * c * a ^ n) := by
      have : 0 < 1 / (a + N * c) ^ n := by have := hpos N; positivity
      rw [show 1 / (n * c * a ^ n) = (1 / (n * c)) * (1 / a ^ n) by field_simp]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

variable {θ : ℝ} (hc : Cond θ X₀)
include hc

/-! ### The majorant -/

/-- **`s₂(u) ≤ 9 e^{-A/2} L⁻⁴`** for `u ≥ X₀`, `L = log u`. -/
lemma s2_decay4 {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    s2E3 X₀ u ≤ 9 * Real.exp (-(Real.log (Xm X₀)) / 2) / Real.log u ^ 4 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, hll⟩ := logs_of_ge hX0 hc.hX hu
  set L := Real.log u with hset2
  set A := Real.log (Xm X₀) with hset3
  set B := Real.sqrt (L * Real.log L) / 2 with hset4
  have hL0 : 0 < L := by linarith
  have hll18 : 18 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have he := Real.exp_one_lt_d9
    have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 18
    rw [e]; nlinarith
  have hB : 5 * Real.log L ≤ B / 2 := by
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
    have h1 : (20 * Real.log L) ^ 2 ≤ L * Real.log L := by nlinarith
    have h2 : 20 * Real.log L ≤ Real.sqrt (L * Real.log L) :=
      Real.le_sqrt_of_sq_le h1
    show 5 * Real.log L ≤ Real.sqrt (L * Real.log L) / 2 / 2
    linarith
  have hL5 : L ^ 5 ≤ Real.exp (B / 2) := by
    rw [show L ^ 5 = Real.exp (5 * Real.log L) by
      rw [show 5 * Real.log L = Real.log (L ^ 5) by rw [Real.log_pow]; norm_num,
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
  calc 9 * L * Real.exp (-max A B) * L ^ 4 = 9 * L ^ 5 * Real.exp (-max A B) := by ring
    _ ≤ 9 * Real.exp (B / 2) * (Real.exp (-A / 2) * Real.exp (-(B / 2))) := by
        gcongr
    _ = 9 * Real.exp (-A / 2) := by
        have : Real.exp (B / 2) * Real.exp (-(B / 2)) = 1 := by rw [mul_comm]; exact hBe
        linear_combination 9 * Real.exp (-A / 2) * this

/-- `ℓ_i ≥ 9·10⁷`. -/
lemma ellQ_ge (i : ℕ) : 9 * 10 ^ 7 ≤ ellQ X₀ i := by
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : (0 : ℝ) ≤ i * Real.log 2 := by positivity
  unfold ellQ; have := hc.hX; nlinarith

lemma nbQ_nonneg (i : ℕ) : 0 ≤ nbQ X₀ i := by
  have := ellQ_ge hc i
  unfold nbQ; positivity

omit hc in
/-- `ν̄(r) ≤ ν̄(X₀)` for `0 < r < X₀`. -/
lemma nuB_low_le {r : ℝ} (hr0 : 0 < r) (hr : r < X₀) : nuB X₀ r ≤ nuB X₀ X₀ := by
  have hH : Hc X₀ r = Hc X₀ X₀ := by unfold Hc; rw [max_eq_right hr.le, max_self]
  have hH0 := Hc_nonneg (X₀ := X₀) X₀
  have hm : m1z X₀ r = m1z X₀ X₀ := by
    unfold m1z; rw [hH, max_eq_right (by linarith), max_eq_right (by linarith)]
  have hs : s2ε X₀ r = s2ε X₀ X₀ := by unfold s2ε; rw [hm, max_eq_right hr.le, max_self]
  unfold nuB
  rw [hH, hs]
  have : Real.log (4 * r) ≤ Real.log (4 * X₀) := Real.log_le_log (by linarith) (by linarith)
  gcongr

/-- **`ν̄(r) ≤ ν̄_i`** for `X₀⁻ ≤ r` in the block `i`. -/
theorem nuB_le_nbQ {i : ℕ} {r : ℝ} (hr : Xm X₀ ≤ r) (hb : InBlk X₀ i r) :
    nuB X₀ r ≤ nbQ X₀ i := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hbig := X₀_ge_two_pow hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    unfold Xm; linarith
  set y := max r (X₀ : ℝ) with hye
  have hy : (X₀ : ℝ) ≤ y := le_max_right _ _
  have hry : r ≤ y := le_max_left _ _
  have hle : nuB X₀ r ≤ nuB X₀ y := by
    rcases lt_or_ge r X₀ with h | h
    · rw [hye, max_eq_right h.le]; exact nuB_low_le (by linarith) h
    · rw [hye, max_eq_left h]
  refine hle.trans ?_
  set m1 := m1z X₀ y
  set u1 := uS X₀ m1 with hu1e
  have h := nuB_le hc hy
  obtain ⟨hu1X, hl1, -, -⟩ := uS_facts hc m1
  obtain ⟨hu2X, hl2, -, -⟩ := uS_facts hc (m1 + 1)
  have hu10 : 0 < u1 := by linarith
  set L := Real.log u1 with hLe
  have hL0 : 0 < L := by linarith
  set A := Real.exp (-(Real.log (Xm X₀)) / 2) with hAe
  have hA0 : 0 < A := Real.exp_pos _
  have hs1 : s2E3 X₀ u1 ≤ 9 * A / L ^ 4 := s2_decay4 hc hu1X
  have hLL : L ≤ Real.log (uS X₀ (m1 + 1)) := Real.log_le_log hu10 (by rw [uS_succ]; linarith)
  have hs2 : s2E3 X₀ (uS X₀ (m1 + 1)) ≤ 9 * A / L ^ 4 :=
    (s2_decay4 hc hu2X).trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hL0.le hLL 4))
  have hb1 : nuB X₀ y ≤ 19.8 * A / L ^ 4 + 106 / L ^ 6 := by
    have e2 : 19.8 * A / L ^ 4 = 1.1 * (9 * A / L ^ 4) + 1.1 * (9 * A / L ^ 4) := by ring
    linarith
  -- `ℓ_i ≤ L`
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hℓ : ellQ X₀ i ≤ L := by
    unfold ellQ
    rcases lt_or_ge i 2 with hi | hi
    · have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast hi.le
      have : Real.log X₀ ≤ L := Real.log_le_log hX0p hu1X
      nlinarith
    · have hi0 : i ≠ 0 := by omega
      have hv : Xm X₀ * 2 ^ i ≤ r := hb.2.resolve_left hi0
      obtain ⟨hm1a, hm1b⟩ := mB_spec hX0p (le_max_right (y - Hc X₀ y) (X₀ : ℝ))
      have h2u : max (y - Hc X₀ y) (X₀ : ℝ) < 2 * u1 := by
        have := hm1b; rw [uS_succ] at this; exact this
      have hHy : Hc X₀ y ≤ y / 10 ^ 7 := by have := Hc_le hc y; rwa [max_eq_left hy] at this
      have h4 : (X₀ : ℝ) * 2 ^ i / 4 ≤ u1 := by
        have := le_max_left (y - Hc X₀ y) (X₀ : ℝ)
        have hp : (0 : ℝ) < 2 ^ i := by positivity
        nlinarith
      have hlog := Real.log_le_log (by positivity) h4
      rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
      push_cast at hlog
      linarith
  have hℓ0 : 0 < ellQ X₀ i := by linarith [ellQ_ge hc i]
  refine hb1.trans ?_
  unfold nbQ
  gcongr

variable (hev : Even X₀)
include hev

/-- **`BModel.Nu522` for the realised system** (Lemma 5.22 on the blocks, `ϑ = 0`,
`ν̄_i = nbQ X₀ i`): a.s., on `Good(< t) ∩ NiceEv` with `b ≤ t`. -/
theorem nu522_R : ∀ᵐ ω ∂jitterMeasure, ∀ (t : ℕ) (b : ℝ), ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → b ≤ t → Nu522 θ X₀ ω b (nbQ X₀) := by
  filter_upwards [rho_noise_Xm hc hev] with ω hω
  intro t b hG hN hbt
  refine ⟨fun i => nbQ_nonneg hc i, fun _ => 0, fun _ => by simp, fun hO i r hr hrb hblk => ?_⟩
  rw [nuModel_eq hc hev ω hO r, zero_div, add_zero, abs_sub_comm]
  exact (hω t hG hN r hr (by linarith)).trans (nuB_le_nbQ hc hr hblk)

/-- **`BModel.Nu522` on `Good(< tE2 b)`** (the event of `Theorem21InputsH`), `b : ℤ`. -/
theorem nu522_tE2 : ∀ᵐ ω ∂jitterMeasure, ∀ b : ℤ, ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) →
    Nu522 θ X₀ ω b (nbQ X₀) := by
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  filter_upwards [nu522_R hc hev, hnice] with ω hω hN
  intro b hG
  have hb : (b : ℝ) ≤ ((tE2 b : ℕ) : ℝ) := by
    unfold tE2; exact_mod_cast Int.self_le_toNat b
  exact hω _ _ hG hN hb

omit hev

/-! ### The sums -/

set_option maxHeartbeats 1600000 in
/-- **The block sum** `∑_{i<N} log(3v_i)² ν̄_i ≤ 10⁻²²`, `v_i = X₀⁻2ⁱ`. -/
theorem sum_nbQ_le (N : ℕ) :
    ∑ i ∈ range N, Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * nbQ X₀ i ≤ 1 / 10 ^ 22 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hbig := X₀_ge_two_pow hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    unfold Xm; linarith
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_nonneg (X₀ : ℝ) (X₀ : ℝ); unfold Xm; linarith
  set Λ := Real.log X₀ with hΛe
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  set c := Real.log 2 with hce
  have hc1 := Real.log_two_lt_d9
  have hc0 := Real.log_two_gt_d9
  set a := Λ - 2 * c with hae
  have ha : 9 * 10 ^ 7 ≤ a := by rw [hae]; nlinarith
  have ha0 : 0 < a := by linarith
  have hc0' : 0 < c := by linarith
  have hell : ∀ i : ℕ, ellQ X₀ i = a + i * c := fun i => by unfold ellQ; rw [hae]; ring
  set A := Real.exp (-(Real.log (Xm X₀)) / 2) with hAe
  have hA0 : 0 < A := Real.exp_pos _
  have hA : A ≤ 1 / Λ ^ 10 := expA_le hc
  have hΛ10 : (10 : ℝ) ^ 80 ≤ Λ ^ 10 := by
    have := pow_le_pow_left₀ (by norm_num) hΛ 10; norm_num at this ⊢; linarith
  have hA' : A ≤ 1 / 10 ^ 80 :=
    hA.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ10)
  -- the summand
  have hterm : ∀ i : ℕ, Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * nbQ X₀ i ≤
      1.0003 * (19.8 * A) * (1 / (a + i * c) ^ (1 + 1)) +
        1.0003 * 106 * (1 / (a + i * c) ^ (3 + 1)) := by
    intro i
    set ℓ := a + i * c with hℓe
    have hℓ : 9 * 10 ^ 7 ≤ ℓ := by have := ellQ_ge hc i; rw [hell] at this; exact this
    have hℓ0 : 0 < ℓ := by linarith
    have hv0 : 1 ≤ 3 * (Xm X₀ * 2 ^ i) := by
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hlg0 : 0 ≤ Real.log (3 * (Xm X₀ * 2 ^ i)) := Real.log_nonneg hv0
    have hlg : Real.log (3 * (Xm X₀ * 2 ^ i)) ≤ 1.0001 * ℓ := by
      have h1 : Real.log (3 * (Xm X₀ * 2 ^ i)) ≤ Real.log (3 * ((X₀ : ℝ) * 2 ^ i)) :=
        Real.log_le_log (by linarith) (by gcongr)
      rw [Real.log_mul (x := 3) (y := (X₀ : ℝ) * 2 ^ i) (by norm_num) (by positivity),
        Real.log_mul (x := (X₀ : ℝ)) (y := 2 ^ i) (by positivity) (by positivity),
        Real.log_pow] at h1
      have h3 : Real.log 3 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have : Λ + i * c ≤ ℓ + 2 * c := by rw [hℓe, hae]; linarith
      linarith
    have hsq : Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 ≤ 1.0003 * ℓ ^ 2 := by
      have := pow_le_pow_left₀ hlg0 hlg 2
      nlinarith
    have hnb : nbQ X₀ i = 19.8 * A / ℓ ^ 4 + 106 / ℓ ^ 6 := by unfold nbQ; rw [hell]
    rw [hnb]
    have hnb0 : 0 ≤ 19.8 * A / ℓ ^ 4 + 106 / ℓ ^ 6 := by positivity
    calc _ ≤ 1.0003 * ℓ ^ 2 * (19.8 * A / ℓ ^ 4 + 106 / ℓ ^ 6) :=
          mul_le_mul_of_nonneg_right hsq hnb0
      _ = _ := by field_simp; ring
  refine (sum_le_sum fun i _ => hterm i).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h2 := tele_sum ha0 hc0' (n := 1) le_rfl N
  have h4 := tele_sum ha0 hc0' (n := 3) (by norm_num) N
  have hs2 : ∑ i ∈ range N, 1 / (a + i * c) ^ (1 + 1) ≤ 1 := by
    refine h2.trans ?_
    have e1 : 1 / a ^ (1 + 1) ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ a ^ (1 + 1) := by norm_num; nlinarith
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have e2 : 1 / (((1 : ℕ) : ℝ) * c * a ^ 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; nlinarith
    linarith
  have hs4 : ∑ i ∈ range N, 1 / (a + i * c) ^ (3 + 1) ≤ 1 / (6 * 10 ^ 31) + 1 / (15 * 10 ^ 23) := by
    refine h4.trans ?_
    have ha3 : (729 : ℝ) * 10 ^ 21 ≤ a ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) ha 3; norm_num at this ⊢; linarith
    have ha4 : (6 : ℝ) * 10 ^ 31 ≤ a ^ (3 + 1) := by
      have := pow_le_pow_left₀ (by norm_num) ha 4; norm_num at this ⊢; linarith
    have e1 : 1 / a ^ (3 + 1) ≤ 1 / (6 * 10 ^ 31) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha4
    have e2 : 1 / (((3 : ℕ) : ℝ) * c * a ^ 3) ≤ 1 / (15 * 10 ^ 23) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have := mul_le_mul hc0.le ha3 (by norm_num) hc0'.le
      push_cast; nlinarith
    linarith
  have hS2 : 0 ≤ ∑ i ∈ range N, 1 / (a + i * c) ^ (1 + 1) :=
    sum_nonneg fun i _ => by have : 0 < a + i * c := by positivity
                             positivity
  calc 1.0003 * (19.8 * A) * ∑ i ∈ range N, 1 / (a + i * c) ^ (1 + 1) +
        1.0003 * 106 * ∑ i ∈ range N, 1 / (a + i * c) ^ (3 + 1)
      ≤ 1.0003 * (19.8 * (1 / 10 ^ 80)) * 1 +
          1.0003 * 106 * (1 / (6 * 10 ^ 31) + 1 / (15 * 10 ^ 23)) := by
        have t1 : 1.0003 * (19.8 * A) * ∑ i ∈ range N, 1 / (a + i * c) ^ (1 + 1) ≤
            1.0003 * (19.8 * (1 / 10 ^ 80)) * 1 :=
          mul_le_mul (by linarith) hs2 hS2 (by norm_num)
        have t2 : 1.0003 * 106 * ∑ i ∈ range N, 1 / (a + i * c) ^ (3 + 1) ≤
            1.0003 * 106 * (1 / (6 * 10 ^ 31) + 1 / (15 * 10 ^ 23)) :=
          mul_le_mul_of_nonneg_left hs4 (by norm_num)
        linarith
    _ ≤ 1 / 10 ^ 22 := by norm_num

/-- **The size of `ν̄_i`**: `log y · ν̄_i ≤ 10⁻²⁷` for `0 ≤ y ≤ 16 v_i`, `v_i = X₀⁻2ⁱ`. -/
theorem log_nbQ_le {i : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 16 * (Xm X₀ * 2 ^ i)) :
    Real.log y * nbQ X₀ i ≤ 1 / 10 ^ 27 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_nonneg (X₀ : ℝ) (X₀ : ℝ); unfold Xm; linarith
  have hnb0 := nbQ_nonneg hc i
  rcases le_or_gt y 1 with h1 | h1
  · have : Real.log y ≤ 0 := Real.log_nonpos hy0 h1
    have : Real.log y * nbQ X₀ i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this hnb0
    have : (0 : ℝ) < 1 / 10 ^ 27 := by norm_num
    linarith
  set ℓ := ellQ X₀ i with hℓe
  have hℓ : 9 * 10 ^ 7 ≤ ℓ := ellQ_ge hc i
  have hc1 := Real.log_two_lt_d9
  have hly : Real.log y ≤ 2 * ℓ := by
    have h2 : y ≤ (X₀ : ℝ) * 2 ^ (i + 4) := by
      rw [pow_add]; have : (0 : ℝ) < 2 ^ i := by positivity
      nlinarith
    have h3 := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h3
    rw [hℓe]; unfold ellQ; push_cast at h3
    have : (0 : ℝ) ≤ i * Real.log 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
    nlinarith [hc.hX]
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg h1.le
  set A := Real.exp (-(Real.log (Xm X₀)) / 2) with hAe
  have hA : A ≤ 1 / Real.log X₀ ^ 10 := expA_le hc
  have hΛ10 : (10 : ℝ) ^ 80 ≤ Real.log X₀ ^ 10 := by
    have := pow_le_pow_left₀ (by norm_num) hc.hX 10; norm_num at this ⊢; linarith
  have hA' : A ≤ 1 / 10 ^ 80 :=
    hA.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ10)
  have hA0 : 0 < A := Real.exp_pos _
  have hℓ0 : 0 < ℓ := by linarith
  have hnb : nbQ X₀ i = 19.8 * A / ℓ ^ 4 + 106 / ℓ ^ 6 := rfl
  have hℓ3 : (10 : ℝ) ^ 21 ≤ ℓ ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hℓ 3; norm_num at this ⊢; linarith
  have hℓ5 : (10 : ℝ) ^ 35 ≤ ℓ ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hℓ 5; norm_num at this ⊢; linarith
  calc Real.log y * nbQ X₀ i ≤ (2 * ℓ) * (19.8 * A / ℓ ^ 4 + 106 / ℓ ^ 6) :=
        mul_le_mul hly (le_of_eq hnb) hnb0 (by positivity)
    _ = 39.6 * A / ℓ ^ 3 + 212 / ℓ ^ 5 := by field_simp; ring
    _ ≤ 39.6 * (1 / 10 ^ 80) / 10 ^ 21 + 212 / 10 ^ 35 := by gcongr
    _ ≤ 1 / 10 ^ 27 := by norm_num

end Queue6

end
