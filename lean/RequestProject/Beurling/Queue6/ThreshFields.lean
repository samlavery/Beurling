module

public import RequestProject.Beurling.Queue6.CountISmall
public import RequestProject.Beurling.Model.CapHSlope

/-!
# The fields of `BeurlingSystem.ThreshHyp` for `P(ω)`, `t = tJ`, `H = Hc X₀`

* `countI_R` : **`countI`** (both cases: `countI_small`, `countI_large`), on `Good(< t₀) ∩ NiceEv`;
* `H_mono_R`, `H_two_R`, `Hx_ge_R`, `logH_R` : the fields `H_mono`, `H_two`, `Hx_ge`, `logH`;
* `jitSmall_R` : `|t(p_j) - p_j| ≤ t(p_j)/200`, the consequence of `jit` and `H_small` that the
  proof of Lemma 5.23 uses (`ThreshHyp.t_le`, `caseII`): `H_small` (`H(z) ≤ z/100` for all
  `z ≥ 1`) is false for `Hc` at `z < 100 H(X₀)`, but it is only read at `z = t(p_j)`, and there
  `t(p_j) = p_j` for the rational primes.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- **The field `H_mono`**. -/
lemma H_mono_R : MonotoneOn (Hc X₀) (Ici 1) :=
  (KR.WidthReal.Hc_mono hc.hX).monotoneOn _

/-- **The field `Hx_ge`**. -/
lemma Hx_ge_R (x : ℝ) : 1 ≤ Hc X₀ x :=
  capH_ge_one (Nat.cast_nonneg _) hc.hX (le_max_right _ _)

/-- **The field `logH`**: `16 log log x ≤ log H(x)` for `X₀ ≤ x`. -/
lemma logH_R {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : 16 * Real.log (Real.log x) ≤ Real.log (Hc X₀ x) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, hll⟩ := logs_of_ge hX0 hc.hX hx
  have hstd : Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ Hc X₀ x := by
    rw [Hc_eq hx]; exact le_max_left _ _
  have h2 : 2 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 ≤ 9 := by
      have he := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    linarith
  have := Real.log_le_log (Real.exp_pos _) hstd
  rw [Real.log_exp] at this
  nlinarith

/-- **The field `H_two`**: `H(2z) ≤ 1.000003 H(z)` for `z ≥ 1`. -/
lemma H_two_R {z : ℝ} (hz : 1 ≤ z) : Hc X₀ (2 * z) ≤ 1.000003 * Hc X₀ z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  set a := max z (X₀ : ℝ)
  set b := max (2 * z) (X₀ : ℝ)
  have ha : (X₀ : ℝ) ≤ a := le_max_right _ _
  have ha0 : 0 < a := by linarith
  have hab : a ≤ b := max_le_max (by linarith) le_rfl
  have hb2 : b ≤ 2 * a := max_le (by linarith [le_max_left z (X₀ : ℝ)]) (by linarith)
  have hS := CapHSlopeProof.capHSlope hc.hX a b ha hab
  have hr : (b / a) ^ (4 / 1000000 : ℝ) ≤ (2 : ℝ) ^ (4 / 1000000 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by rw [div_le_iff₀ ha0]; linarith) (by norm_num)
  have h2 : (2 : ℝ) ^ (4 / 1000000 : ℝ) ≤ 1.000003 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hl := Real.log_two_lt_d9
    set y := Real.log 2 * (4 / 1000000)
    have hy0 : 0 ≤ y := by have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
    have hy : y ≤ 2.7726e-6 := by show Real.log 2 * (4 / 1000000) ≤ _; nlinarith
    have h1 := Real.add_one_le_exp (-y)
    have h3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-y) := Real.exp_pos _
    nlinarith
  have hH0 := capH_nonneg (X₀ : ℝ) a
  show capH X₀ b ≤ 1.000003 * capH X₀ a
  calc capH X₀ b ≤ (b / a) ^ (4 / 1000000 : ℝ) * capH X₀ a := hS
    _ ≤ 1.000003 * capH X₀ a := mul_le_mul_of_nonneg_right (hr.trans h2) hH0

/-- **`|t(p_j) - p_j| ≤ t(p_j)/200`** (what `jit` and `H_small` are used for). -/
lemma jitSmall_R (ω : JitterΩ) (j : ℕ) :
    |tJ θ X₀ ω j - (PR θ X₀ ω).p j| ≤ tJ θ X₀ ω j / 200 := by
  have ht := t_ge_R hc ω j
  rcases tJ_cases hc ω j with ⟨h1, -⟩ | ⟨k, h1, h2⟩
  · rw [h1, sub_self, abs_zero]; linarith [two_le_p hc ω j]
  · have hj := jit_R hc ω j
    rw [h1, Hc_slot hc ω k] at hj
    rw [h1]
    have hs := slotF_ge hc k ω
    have hH : HF θ X₀ k ω ≤ slotF θ X₀ k ω / 10 ^ 7 := capH_le_div hc.hX hs
    rw [abs_le] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]

variable (D : Sec5Family) (hev : Even X₀)
include hev

open Classical in
/-- **The field `countI` of `ThreshHyp`** for `P(ω)` (`t = tJ`, `H = Hc X₀`), on
`Good(< t₀) ∩ NiceEv`, `X₀³ ≤ x ≤ t₀`, `6H(x) x^{-1/3} ≤ δ ≤ 1/4`. -/
theorem countI_R {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {x δ : ℝ} (hx3 : (X₀ : ℝ) ^ 3 ≤ x) (hxt : x ≤ t₀)
    (hδge : 6 * Hc X₀ x / x ^ (1 / 3 : ℝ) ≤ δ) (hδ : δ ≤ 1 / 4) :
    ∀ j ∈ (PR θ X₀ ω).primesLe x, (PR θ X₀ ω).p j ≤ √(δ * x / (2 * Hc X₀ x)) →
      (((PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j).card : ℝ) ≤ 4 * δ * x / (PR θ X₀ ω).p j ^ 2 := by
  intro j _ hpj
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hbig := X₀_ge_two_pow hc.hX
  have hX2 : (4 : ℝ) ≤ (X₀ : ℝ) ^ 2 := by nlinarith
  have hX3 : 2 * (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 3 := by
    have : (X₀ : ℝ) ^ 3 = X₀ * X₀ ^ 2 := by ring
    nlinarith
  have hx0 : 0 < x := by linarith
  have hδ0 : 0 < δ := by
    have h1 : 0 < 6 * Hc X₀ x := by linarith [Hx_ge_R hc x]
    have h2 : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
    exact lt_of_lt_of_le (div_pos h1 h2) hδge
  rcases le_or_gt ((PR θ X₀ ω).p j) (1.01 * x ^ (1 / 4 : ℝ)) with h | h
  · exact countI_small hc D hev hG hN hx3 hxt hδge hδ h
  · exact countI_large hc hev hN hδ0 hδ (by linarith) hpj h

end Queue6

end
