module

public import RequestProject.Beurling.Queue
public import RequestProject.Beurling.Main

/-!
# Bookkeeping (Section 3.5) and the lag bound (Proposition 4.1)

* `Greedy.count_identity` : **Lemma 3.6 (count identity)**: if `V` increases by `A j + P j` at
  step `j`, then `V j = V 0 + j + Q j`.
* `Greedy.queue_le_of_windows` : the **reduction** at the end of Section 3.5: if every slot window
  ending at `j` has excess of arrivals over slots at most `B`, then `Q j ≤ B`.
* `Bookkeeping.two_sided_lag` : **Corollary 3.8 (two-sided lag)**, the accounting step: from the
  decomposition `N(x) = V_j - C((x, s_{j+1})) + E₊ - E₋`, Lemma 3.6 and the bounds on the terms,
  `-(H/2)(1 + κ₊/log x) - 4 ≤ D(x) ≤ max Q + (H/2)(1 + κ₊/log x) + 3`.
* `Bookkeeping.queueBound_le_H` : `B ≤ H` from `B ≤ 34 M₁ L²`, `H ≥ M₁²` and `H ≥ H_std`
  (after (75)).
* `Bookkeeping.lag_le_rpow` : the numerical part of **Proposition 4.1**: if
  `|D| ≤ B + 3H + 3` with `B ≤ H`, `log H ≤ 8ℓ² + 10⁻⁶L` and `L = log x ≥ 10⁸ - 1`, then
  `|D| ≤ x^η` for every `η ≥ 5·10⁻⁵`.
* `Bookkeeping.lagExponent_ge` : `η = min(θ, 1/2 - θ)/2 ≥ 5·10⁻⁵` for `θ ≤ 1/2 - 10⁻⁴`.
-/

@[expose] public section

open Finset Real

namespace Greedy

/-- **Lemma 3.6 (count identity)**, re-indexed so that the first slot is `1` and `Q 0 = 0`:
if `V` increases by `A j + P j` at step `j` (one count for each composite arriving in the slot
and one for the prime placed, if any), then `V j = V 0 + j + Q j`. -/
theorem count_identity (A V : ℕ → ℤ)
    (hV : ∀ j, V (j + 1) = V j + A (j + 1) + greedyPrime A j) (j : ℕ) :
    V j = V 0 + j + greedyQueue A j := by
  induction j with
  | zero => simp [greedyQueue]
  | succ j ih =>
    rw [hV, ih]
    simp only [greedyPrime, greedyQueue]
    push_cast; ring

/-- **The reduction of Section 3.5**: if every slot window `(i, j]` has excess of composite
arrivals over slots at most `B`, then the queue satisfies `Q j ≤ B` (by Lindley's formula). -/
theorem queue_le_of_windows (A : ℕ → ℤ) (j : ℕ) (B : ℤ)
    (h : ∀ i ≤ j, ∑ l ∈ Ioc i j, A l - ((j : ℤ) - i) ≤ B) : greedyQueue A j ≤ B := by
  rw [greedyQueue_lindley, sup'_le_iff]
  intro i hi
  exact h i (Nat.lt_succ_iff.mp (mem_range.mp hi))

end Greedy

namespace Bookkeeping

/-- **Corollary 3.8 (two-sided lag)**, the accounting step. Let `x ∈ J_j`, so that
`T(x) ∈ [j + ϑ, j + 1 + ϑ)` with `ϑ ∈ (0, 1/2]`. Write `N(x) = V_j - C + E₊ - E₋`, where by
Lemma 3.6 `V_j = j + 1 + Q_j`, `C = C((x, s_{j+1})) ∈ [0, A_j]`, `Q_j - A_j ≥ -1`, and the landing
errors satisfy `0 ≤ E± ≤ W + 1 + ε` with `W = (H/2)(1 + κ₊/log x)` and `ε ≤ 1/2`. Then
`-W - 4 ≤ N(x) - T(x) ≤ Q_max + W + 3` whenever `Q_j ≤ Q_max`. -/
theorem two_sided_lag {j T N Q A C Ep Em ϑ W ε Qmax : ℝ}
    (hN : N = (j + 1 + Q) - C + Ep - Em) (hT1 : j + ϑ ≤ T) (hT2 : T < j + 1 + ϑ)
    (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1 / 2) (hC0 : 0 ≤ C) (hCA : C ≤ A) (hQA : -1 ≤ Q - A)
    (hEp0 : 0 ≤ Ep) (hEp : Ep ≤ W + 1 + ε) (hEm0 : 0 ≤ Em) (hEm : Em ≤ W + 1 + ε)
    (hε : ε ≤ 1 / 2) (hQ : Q ≤ Qmax) :
    -W - 4 ≤ N - T ∧ N - T ≤ Qmax + W + 3 := by
  constructor <;> linarith

/-- `34 L² ≤ e^{4 (log L)²}` once `log L ≥ 2`. -/
lemma thirtyfour_sq_le {L : ℝ} (hL : 2 ≤ Real.log L) (hL0 : 0 < L) :
    34 * L ^ 2 ≤ Real.exp (4 * Real.log L ^ 2) := by
  have h34 : Real.log 34 < 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 4]
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 34 * L ^ 2)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  nlinarith

/-- **`B ≤ H` at every scale** (after (75)): from `B ≤ 34 M₁ L²`, `H ≥ M₁²` and
`H ≥ H_std = e^{8ℓ²}` with `ℓ = log L ≥ 2`. -/
theorem queueBound_le_H {B M₁ H L : ℝ} (hB : B ≤ 34 * M₁ * L ^ 2)
    (hM : M₁ ^ 2 ≤ H) (hstd : Real.exp (8 * Real.log L ^ 2) ≤ H) (hL : 2 ≤ Real.log L)
    (hL0 : 0 < L) : B ≤ H := by
  have h1 := thirtyfour_sq_le hL hL0
  have hH0 : 0 ≤ H := le_trans (Real.exp_pos _).le hstd
  have hsq : Real.exp (4 * Real.log L ^ 2) ^ 2 = Real.exp (8 * Real.log L ^ 2) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hM' : M₁ ≤ Real.sqrt H := Real.le_sqrt_of_sq_le hM
  have hE' : Real.exp (4 * Real.log L ^ 2) ≤ Real.sqrt H :=
    Real.le_sqrt_of_sq_le (by rw [hsq]; exact hstd)
  calc B ≤ M₁ * (34 * L ^ 2) := by linarith
    _ ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul hM' (h1.trans hE') (by positivity) (Real.sqrt_nonneg _)
    _ = H := Real.mul_self_sqrt hH0

/-- `log 7 < 2`. -/
lemma log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]; nlinarith

/-- `log (10⁸) < 19`. -/
lemma log_1e8_lt : Real.log (10 ^ 8 : ℝ) < 19 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  have h : Real.exp 19 = Real.exp 1 ^ 19 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 19
  have h2 : (10 : ℝ) ^ 8 < 2.7182818283 ^ 19 := by norm_num
  linarith

/-- `(log L)² ≤ 361 L / L₀` for `L ≥ L₀ = 10⁸ - 1`. -/
lemma log_sq_le {L : ℝ} (hL : 10 ^ 8 - 1 ≤ L) :
    Real.log L ^ 2 ≤ 361 * (L / (10 ^ 8 - 1)) := by
  set L₀ : ℝ := 10 ^ 8 - 1
  have hL₀ : 0 < L₀ := by norm_num [L₀]
  set t := L / L₀ with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hL₀]; linarith
  have hLt : L = L₀ * t := by rw [ht]; field_simp
  have hlogL₀ : Real.log L₀ < 19 :=
    lt_of_le_of_lt (Real.log_le_log hL₀ (by norm_num [L₀])) log_1e8_lt
  have hlogL₀0 : 0 ≤ Real.log L₀ := Real.log_nonneg (by norm_num [L₀])
  have hst : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht1
  have hlogt : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.sqrt t)
    have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
      rw [Real.log_sqrt (by linarith)]; ring
    linarith
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog : Real.log L = Real.log L₀ + Real.log t := by
    rw [hLt, Real.log_mul hL₀.ne' (by linarith)]
  have hb : Real.log L ≤ 19 * Real.sqrt t := by rw [hlog]; nlinarith
  have hb0 : 0 ≤ Real.log L := by rw [hlog]; positivity
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  nlinarith

/-- **Proposition 4.1, the numerical part.** If `|D| ≤ B + 3H + 3` with `B ≤ H`, `H ≥ 1`,
`log H ≤ 8ℓ² + 10⁻⁶ L` (`L = log x`, `ℓ = log L`) and `L ≥ 10⁸ - 1`, then `|D| ≤ x^η` for every
`η ≥ 5·10⁻⁵`. -/
theorem lag_le_rpow {x D B H η : ℝ} (hx : 0 < x) (hL : 10 ^ 8 - 1 ≤ Real.log x)
    (hH1 : 1 ≤ H) (hBH : B ≤ H)
    (hlogH : Real.log H ≤ 8 * Real.log (Real.log x) ^ 2 + 1e-6 * Real.log x)
    (hη : 5e-5 ≤ η) (hD : |D| ≤ B + 3 * H + 3) : |D| ≤ x ^ η := by
  have h7 : |D| ≤ 7 * H := by linarith
  have hsq := log_sq_le hL
  have hlog7H : Real.log (7 * H) ≤ η * Real.log x := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := log_seven_lt_two
    have hdiv : Real.log x / (10 ^ 8 - 1) ≤ Real.log x / 9e7 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    have hLpos : 0 < Real.log x := by linarith
    nlinarith
  calc |D| ≤ 7 * H := h7
    _ = Real.exp (Real.log (7 * H)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (η * Real.log x) := Real.exp_le_exp.mpr hlog7H
    _ = x ^ η := by rw [Real.rpow_def_of_pos hx, mul_comm]

/-- `η = min(θ, 1/2 - θ)/2 ≥ 5·10⁻⁵` for `θ ∈ [10⁻⁴, 1/2 - 10⁻⁴]`; in particular on
`[1/20, 1/2 - 10⁻⁴]`. This is where `θ ≤ θ₁ = 1/2 - 10⁻⁴` is used. -/
theorem lagExponent_ge {θ : ℝ} (h1 : 1 / 10000 ≤ θ) (h2 : θ ≤ 1 / 2 - 1 / 10000) :
    5e-5 ≤ lagExponent θ := by
  unfold lagExponent
  have : 1 / 10000 ≤ min θ (1 / 2 - θ) := le_min h1 (by linarith)
  linarith

end Bookkeeping

end
