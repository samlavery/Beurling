module

public import Mathlib

/-!
# Lemma A.3 (pattern sum), second inequality, and the slot bounds `τ_j` (A.tau)

Appendix A, Section A.1 ("Slot positions") and Lemma A.3: put `Xm := X₀ - H(X₀)/2`,
`σ_j := X₀ + 0.99(j-1)` and `τ_j := max(Xm, σ_j - 2H(σ_j))` (eq. (A.tau)). Then
`∏_{j ≤ k} (1 - 1/τ_j)^{-k} ≤ e^{(3H(X₀)+2)k/X₀} (1 + k/X₀)^{1.02k}`.

We index `j` from `0` (`σ_j = X₀ + 0.99 j`). The hypotheses on `H` are the ones the paper uses:
`H(v)/v` non-increasing on `[X₀, ∞)` (Theorem 6.23(c)), `1 ≤ H(X₀)` and `H(X₀)/X₀ ≤ 5·10⁻⁴`
(the paper has `H(X₀) > 200` and `H(X₀)/X₀ ≤ e^{-10⁷}`), and `X₀ ≥ 1000`.

* `RankFull.tauSlot` : `τ_j`;
* `RankFull.one_lt_tauSlot` : `τ_j > 1`;
* `RankFull.sum_inv_tau_le` : `∑_{j<k} 1/(τ_j - 1) ≤ (3H(X₀)+2)/X₀ + 1.02 log(1 + k/X₀)`;
* `RankFull.pattern_sum_tail` : **Lemma A.3**, second inequality.
-/

@[expose] public section

open Finset Real

namespace RankFull

/-- The slot bound `τ_j = max(X₀ - H(X₀)/2, σ_j - 2H(σ_j))`, `σ_j = X₀ + 0.99 j` (eq. (A.tau),
indexed from `0`). -/
noncomputable def tauSlot (H : ℝ → ℝ) (X₀ : ℝ) (j : ℕ) : ℝ :=
  max (X₀ - H X₀ / 2) (X₀ + 0.99 * j - 2 * H (X₀ + 0.99 * j))

/-- The standing hypotheses on `H` at `X₀`. -/
structure SlotHyp (H : ℝ → ℝ) (X₀ : ℝ) : Prop where
  hX₀ : 1000 ≤ X₀
  hH1 : 1 ≤ H X₀
  hHsmall : H X₀ ≤ 0.0005 * X₀
  hanti : AntitoneOn (fun v => H v / v) (Set.Ici X₀)

namespace SlotHyp

variable {H : ℝ → ℝ} {X₀ : ℝ} (h : SlotHyp H X₀)
include h

lemma X₀_pos : 0 < X₀ := by linarith [h.hX₀]

lemma Xm_sub_one : 0.989 * X₀ ≤ X₀ - H X₀ / 2 - 1 := by
  have := h.hHsmall; have := h.hX₀; linarith

/-- `H(w) - H(v) ≤ (w - v) H(X₀)/X₀` for `X₀ ≤ v ≤ w` (from `H(v)/v` non-increasing). -/
lemma H_incr {v w : ℝ} (hv : X₀ ≤ v) (hvw : v ≤ w) : H w - H v ≤ (w - v) * (H X₀ / X₀) := by
  have hv0 : 0 < v := lt_of_lt_of_le h.X₀_pos hv
  have hw0 : 0 < w := lt_of_lt_of_le hv0 hvw
  have h1 : H w / w ≤ H v / v := h.hanti (Set.mem_Ici.mpr hv) (Set.mem_Ici.mpr (hv.trans hvw)) hvw
  have h2 : H v / v ≤ H X₀ / X₀ := h.hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hv) hv
  have h3 : H w ≤ w * (H v / v) := by rwa [div_le_iff₀ hw0, mul_comm] at h1
  have h4 : H v = v * (H v / v) := by field_simp
  have h5 : 0 ≤ w - v := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h5]

/-- `σ_j - 2H(σ_j) ≥ X₀ - 2H(X₀) + 0.989 j`. -/
lemma g_ge (j : ℕ) :
    X₀ - 2 * H X₀ + 0.989 * j ≤ X₀ + 0.99 * j - 2 * H (X₀ + 0.99 * j) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have := h.H_incr (v := X₀) (w := X₀ + 0.99 * j) le_rfl (by linarith)
  have hε : H X₀ / X₀ ≤ 0.0005 := by
    rw [div_le_iff₀ h.X₀_pos]; linarith [h.hHsmall]
  have : (X₀ + 0.99 * j - X₀) * (H X₀ / X₀) ≤ 0.99 * j * 0.0005 := by
    rw [show X₀ + 0.99 * j - X₀ = 0.99 * j by ring]
    exact mul_le_mul_of_nonneg_left hε (by positivity)
  linarith

omit h in
lemma tau_ge_Xm (j : ℕ) : X₀ - H X₀ / 2 ≤ tauSlot H X₀ j := le_max_left _ _

/-- `τ_j > 1`. -/
theorem one_lt_tauSlot (j : ℕ) : 1 < tauSlot H X₀ j := by
  have := tau_ge_Xm (H := H) (X₀ := X₀) j; have := h.Xm_sub_one; have := h.hX₀; linarith

end SlotHyp

/-- `∑_{i=1}^{n} 1/(a + b i) ≤ (1/b) log(1 + bn/a)` for `a, b > 0`. -/
lemma sum_inv_arith_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ i ∈ range n, 1 / (a + b * (i + 1)) ≤ 1 / b * Real.log (1 + b * n / a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 < 1 + b * n / a := by positivity
    have h2 : 0 < 1 + b * (n + 1 : ℕ) / a := by positivity
    have hlog : Real.log (1 + b * (n + 1 : ℕ) / a) - Real.log (1 + b * n / a) ≥
        b / (a + b * (n + 1)) := by
      rw [← Real.log_div h2.ne' h1.ne']
      have hq : 0 < (1 + b * (n + 1 : ℕ) / a) / (1 + b * n / a) := div_pos h2 h1
      have := Real.one_sub_inv_le_log_of_pos hq
      have heq : 1 - ((1 + b * (n + 1 : ℕ) / a) / (1 + b * n / a))⁻¹ = b / (a + b * (n + 1)) := by
        push_cast
        field_simp
        ring
      linarith
    have : 1 / (a + b * ((n : ℝ) + 1)) = 1 / b * (b / (a + b * (n + 1))) := by
      field_simp
    rw [this]
    have hb' : 0 < 1 / b := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog.le hb'.le]

/-- `(1 - 1/τ)^{-1} ≤ e^{1/(τ - 1)}` for `τ > 1`. -/
lemma inv_one_sub_inv_le_exp {τ : ℝ} (hτ : 1 < τ) : (1 - τ⁻¹)⁻¹ ≤ Real.exp (1 / (τ - 1)) := by
  have h0 : 0 < 1 - τ⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hτ)
  have h1 : 0 < (1 - τ⁻¹)⁻¹ := inv_pos.mpr h0
  rw [← Real.exp_log h1]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv]
  have := Real.one_sub_inv_le_log_of_pos h0
  have heq : 1 - (1 - τ⁻¹)⁻¹ = -(1 / (τ - 1)) := by
    have : τ - 1 ≠ 0 := by linarith
    have : τ ≠ 0 := by linarith
    field_simp
    ring
  linarith

namespace SlotHyp

variable {H : ℝ → ℝ} {X₀ : ℝ} (h : SlotHyp H X₀)
include h

/-- The slot-sum bound in the proof of Lemma A.3:
`∑_{j<k} 1/(τ_j - 1) ≤ (3H(X₀)+2)/X₀ + 1.02 log(1 + k/X₀)`. -/
theorem sum_inv_tau_le (k : ℕ) :
    ∑ j ∈ range k, 1 / (tauSlot H X₀ j - 1) ≤
      (3 * H X₀ + 2) / X₀ + 1.02 * Real.log (1 + k / X₀) := by
  set h0 := H X₀ with hh0
  set a := X₀ - h0 / 2 - 1 with ha
  have hX := h.hX₀
  have ha0 : 0.989 * X₀ ≤ a := h.Xm_sub_one
  have ha_pos : 0 < a := by linarith
  set n1 := ⌈2 * h0 / 0.989⌉₊ with hn1
  have hn1le : (n1 : ℝ) ≤ 2 * h0 / 0.989 + 1 := (Nat.ceil_lt_add_one (by
    have := h.hH1; positivity)).le
  have hn1ge : 2 * h0 / 0.989 ≤ n1 := Nat.le_ceil _
  -- pointwise bound
  have hpt : ∀ j : ℕ, 1 / (tauSlot H X₀ j - 1) ≤
      (if j < n1 then 1 / a else 0) + (if n1 ≤ j then 1 / (a + 0.989 * (j - n1 : ℕ)) else 0) := by
    intro j
    have hτ := tau_ge_Xm (H := H) (X₀ := X₀) j
    by_cases hj : j < n1
    · rw [if_pos hj, if_neg (by omega), add_zero]
      exact one_div_le_one_div_of_le ha_pos (by linarith)
    · rw [if_neg hj, if_pos (by omega), zero_add]
      push_neg at hj
      have hg := h.g_ge j
      have hjn : ((j - n1 : ℕ) : ℝ) = j - n1 := by rw [Nat.cast_sub hj]
      have hτ2 : X₀ - 2 * h0 + 0.989 * j ≤ tauSlot H X₀ j := hg.trans (le_max_right _ _)
      have : a + 0.989 * (j - n1 : ℕ) ≤ tauSlot H X₀ j - 1 := by
        rw [hjn]
        have : 0.989 * (n1 : ℝ) ≥ 2 * h0 := by
          have := mul_le_mul_of_nonneg_left hn1ge (by norm_num : (0 : ℝ) ≤ 0.989)
          rw [mul_div_cancel₀ _ (by norm_num)] at this; linarith
        have := h.hH1
        linarith
      have hp : 0 < a + 0.989 * (j - n1 : ℕ) := by positivity
      exact one_div_le_one_div_of_le hp this
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ range k) => hpt j
  rw [Finset.sum_add_distrib] at hsum
  -- the first part: at most `n1` terms `1/a`
  have hfirst : ∑ j ∈ range k, (if j < n1 then 1 / a else 0) ≤ n1 * (1 / a) := by
    rw [← Finset.sum_filter]
    calc ∑ j ∈ (range k).filter (· < n1), 1 / a = ((range k).filter (· < n1)).card * (1 / a) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n1 * (1 / a) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (range k).filter (· < n1) ⊆ range n1 := fun j hj => by
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; exact hj.2
          exact_mod_cast (Finset.card_le_card this).trans (by simp)
  -- the second part: `∑_{i<k} 1/(a + 0.989 i)`
  have hsecond : ∑ j ∈ range k, (if n1 ≤ j then 1 / (a + 0.989 * (j - n1 : ℕ)) else 0) ≤
      ∑ i ∈ range k, 1 / (a + 0.989 * i) := by
    rw [← Finset.sum_filter]
    have hfil : (range k).filter (n1 ≤ ·) = Finset.Ico n1 k := by
      ext j; simp [Finset.mem_Ico]; omega
    rw [hfil, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (by omega)
    · intro i _ _; positivity
  have hlogpart : ∑ i ∈ range k, 1 / (a + 0.989 * i) ≤
      1 / a + 1 / 0.989 * Real.log (1 + 0.989 * k / a) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp; positivity
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [add_comm 1 k', Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, add_zero]
      have := sum_inv_arith_le ha_pos (by norm_num : (0 : ℝ) < 0.989) k'
      push_cast at this ⊢
      have hmono : Real.log (1 + 0.989 * k' / a) ≤ Real.log (1 + 0.989 * (k' + 1) / a) :=
        Real.log_le_log (by positivity) (by gcongr; linarith)
      have : 0 < (1 : ℝ) / 0.989 := by norm_num
      nlinarith
  -- compare with the paper's constants
  have hc1 : ((n1 : ℝ) + 1) * (1 / a) ≤ (3 * h0 + 2) / X₀ := by
    have hX0 : 0 < X₀ := h.X₀_pos
    have hh1 := h.hH1
    have hhs := h.hHsmall
    rw [div_eq_mul_one_div (3 * h0 + 2), mul_one_div, mul_one_div, div_le_div_iff₀ ha_pos hX0]
    -- `(n1 + 1) X₀ ≤ (3h0 + 2) a`
    have hn : (n1 : ℝ) + 1 ≤ 2.03 * h0 + 2 := by
      have : 2 * h0 / 0.989 ≤ 2.0223 * h0 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    have : (3 * h0 + 2) * (h0 / 2 + 1) ≤ 0.97 * h0 * X₀ := by nlinarith
    calc ((n1 : ℝ) + 1) * X₀ ≤ (2.03 * h0 + 2) * X₀ := by gcongr
      _ ≤ (3 * h0 + 2) * a := by rw [ha]; nlinarith
  have hc2 : 1 / 0.989 * Real.log (1 + 0.989 * k / a) ≤ 1.02 * Real.log (1 + k / X₀) := by
    have hX0 : 0 < X₀ := h.X₀_pos
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hl : Real.log (1 + 0.989 * k / a) ≤ Real.log (1 + k / X₀) := by
      apply Real.log_le_log (by positivity)
      have : 0.989 * k / a ≤ k / X₀ := by
        rw [div_le_div_iff₀ ha_pos hX0]; nlinarith
      linarith
    have hl0 : 0 ≤ Real.log (1 + 0.989 * k / a) := Real.log_nonneg (by
      have : 0 ≤ 0.989 * k / a := by positivity
      linarith)
    have : (1 : ℝ) / 0.989 ≤ 1.02 := by norm_num
    nlinarith
  calc ∑ j ∈ range k, 1 / (tauSlot H X₀ j - 1)
      ≤ n1 * (1 / a) + (1 / a + 1 / 0.989 * Real.log (1 + 0.989 * k / a)) := by
        linarith
    _ = ((n1 : ℝ) + 1) * (1 / a) + 1 / 0.989 * Real.log (1 + 0.989 * k / a) := by ring
    _ ≤ (3 * h0 + 2) / X₀ + 1.02 * Real.log (1 + k / X₀) := add_le_add hc1 hc2

/-- **Lemma A.3 (pattern sum)**, second inequality:
`∏_{j<k} (1 - 1/τ_j)^{-k} ≤ e^{(3H(X₀)+2)k/X₀} (1 + k/X₀)^{1.02k}`. -/
theorem pattern_sum_tail (k : ℕ) :
    ∏ j ∈ range k, (1 - (tauSlot H X₀ j)⁻¹)⁻¹ ^ k ≤
      Real.exp ((3 * H X₀ + 2) * k / X₀) * (1 + k / X₀) ^ (1.02 * (k : ℝ)) := by
  have hX0 : 0 < X₀ := h.X₀_pos
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hbase : 0 < 1 + (k : ℝ) / X₀ := by positivity
  calc ∏ j ∈ range k, (1 - (tauSlot H X₀ j)⁻¹)⁻¹ ^ k
      ≤ ∏ j ∈ range k, Real.exp (1 / (tauSlot H X₀ j - 1)) ^ k := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀
            (h.one_lt_tauSlot j))).le) k
        · intro j _
          exact pow_le_pow_left₀ (inv_nonneg.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀
            (h.one_lt_tauSlot j))).le) (inv_one_sub_inv_le_exp (h.one_lt_tauSlot j)) k
    _ = Real.exp (k * ∑ j ∈ range k, 1 / (tauSlot H X₀ j - 1)) := by
        rw [Finset.mul_sum, Real.exp_sum]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (k * ((3 * H X₀ + 2) / X₀ + 1.02 * Real.log (1 + k / X₀))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h.sum_inv_tau_le k) hk0)
    _ = Real.exp ((3 * H X₀ + 2) * k / X₀) * (1 + k / X₀) ^ (1.02 * (k : ℝ)) := by
        rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
        congr 1
        ring

end SlotHyp

end RankFull
