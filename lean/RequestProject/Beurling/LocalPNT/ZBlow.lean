module

public import RequestProject.Beurling.LocalPNT.Defs
public import RequestProject.Beurling.LocalPNT.ZBlowZinf
public import RequestProject.Beurling.LocalPNT.ZBlowAux

/-!
# Lemma 4.3 (The base factor at all heights)

For `0 < a ≤ 8`, `Λ = log X₀ ≥ 10⁸`, `σ ≥ 1 - a/Λ`, `s ≠ 1` and `Ê(s) = Z_B(s) - s/(s-1)`:
`|Ê(s)| ≤ 2.1 e^a Λ + 4.04 e^{Ein(a)} min(1, κ(1+|s|)) e^γ Λ + 3κe^a + 1`
(`lemma_4_3`), hence `|Ê(s)| ≤ C_a (1 + κ|s|) e^γ Λ`, `C_a = 2.1 e^a + 5 e^{Ein(a)}`
(`lemma_4_3'`); `log C_8 < 439.4` (`log_C8_lt`); and `|Ê(s) + 1| ≤ 2` for `|s - 1| ≤ 1/8`
(`EHat_add_one_near_pole`).

The proof follows the paper, from the identity (with `I_n = ∫_n^{n+1} x^{-s} dx`)
`Ê = [∑_{n<X₀} n^{-s} - 1 - ∑_{n<X₀} I_n] + (1 - W)(Z_∞ - ∑_{n<X₀} n^{-s}) + (boundary terms)`
(`EHat_eq`), but the bracket is bounded without `ζ`: the trivial bound
`|∑_{n<X₀} n^{-s}|, ∑_{n<X₀} |I_n| ≤ e^a ∑_{n<X₀} 1/n ≤ e^a (1 + Λ)` already gives
`2 e^a (1 + Λ) + 1 ≤ 2.1 e^a Λ + 1`. The rigid part uses `|1 - W| ≤ κ(1+|s|)` when
`κ(1+|s|) ≤ 1` and `|1 - W| ≤ 1 + (1+κ)^σ` always, `|S_{≥X₀}| ≤ Z_∞(σ)` (and
`≤ X₀^{1-σ} Z_∞(1)` for `σ ≥ 1`), `Z_∞(σ) ≤ Z_∞(1) e^{Ein(a) + 1/2}` (`ZinfR_le_exp_Ein`),
`Z_∞(1) ≤ 1.8 Λ` (`Mertens.ZinfR_one_le`) and `e^γ ≥ e^{1/2}`, since `(2 + κ)·1.8 ≤ 4.04`.
-/

@[expose] public section

open Complex Real Finset BaseFactor

namespace LocalPNT

/-! ### Preliminaries -/

lemma kap_eq {X₀ : ℕ} (hX0 : (0 : ℝ) < X₀) :
    kap X₀ = Real.exp (-(119 / 300 * Real.log X₀)) := by
  unfold kap Construction.kappaParam
  rw [Real.rpow_def_of_pos hX0]
  congr 1; ring

/-- The facts on `X₀` and `κ` used below. -/
lemma kap_facts {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    (0 : ℝ) < X₀ ∧ 3 ≤ X₀ ∧ 0 < kap X₀ ∧ kap X₀ ≤ 1 / 10 ^ 7 ∧ 1 / (X₀ : ℝ) ≤ kap X₀ := by
  have h3 := Mertens.three_le_of_log (X₀ := X₀) (by linarith)
  have hX0 : (0 : ℝ) < X₀ := by exact_mod_cast (by omega : 0 < X₀)
  refine ⟨hX0, h3, by rw [kap_eq hX0]; exact Real.exp_pos _, ?_, ?_⟩
  · rw [kap_eq hX0]
    have h1 := Real.add_one_le_exp (119 / 300 * Real.log X₀)
    have h2 : Real.exp (-(119 / 300 * Real.log X₀)) * Real.exp (119 / 300 * Real.log X₀) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-(119 / 300 * Real.log X₀))
    nlinarith
  · rw [kap_eq hX0, one_div, ← Real.exp_log hX0, ← Real.exp_neg, Real.log_exp]
    exact Real.exp_le_exp.mpr (by linarith)

/-- `∑_{1 ≤ n < N} 1/n ≤ 1 + log N`. -/
lemma sum_inv_Ico_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log (N - 1)
  have e : ((harmonic (N - 1) : ℚ) : ℝ) = ∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [harmonic, add_comm]
  rw [e] at h
  refine h.trans ?_
  rcases Nat.lt_or_ge N 2 with h2 | h2
  · have : N - 1 = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg N]
  · have : (1 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ N - 1)
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    linarith [Real.log_le_log (by linarith) this]

/-- `n^{-σ} ≤ e^a/n` for `1 ≤ n ≤ X₀` and `σ ≥ 1 - a/Λ`. -/
lemma rpow_neg_le_exp_div {X₀ : ℕ} (hX0 : (0 : ℝ) < X₀) (hΛ : 0 < Real.log X₀) {a σ : ℝ}
    (ha : 0 ≤ a) (hσ : 1 - a / Real.log X₀ ≤ σ) {n : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X₀) :
    (n : ℝ) ^ (-σ) ≤ Real.exp a * (1 / n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnX' : (n : ℝ) ≤ X₀ := by exact_mod_cast hnX
  have hδ0 : 0 ≤ a / Real.log X₀ := div_nonneg ha hΛ.le
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (a / Real.log X₀ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    _ = (n : ℝ) ^ (a / Real.log X₀) * (1 / n) := by
        rw [Real.rpow_sub_one (by linarith)]; ring
    _ ≤ (X₀ : ℝ) ^ (a / Real.log X₀) * (1 / n) := by
        gcongr
    _ = Real.exp a * (1 / n) := by
        rw [Real.rpow_def_of_pos hX0]; congr 2; field_simp

/-- The decomposition of `Ê` (proof of Lemma 4.3). -/
lemma EHat_eq {X₀ : ℕ} (hX : 1 ≤ X₀) {s : ℂ} (hs1 : s ≠ 1) :
    EHat X₀ s = (headSum X₀ s - 1 - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n) +
      (1 - Wfac (kap X₀) s) * (Zinf X₀ s - headSum X₀ s) + boundary X₀ (kap X₀) s := by
  rw [sum_intCpow s hs1 hX]
  have hs : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold EHat ZBcont
  field_simp
  ring

lemma exp_gamma_ge : (1.625 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have h2 := Real.exp_le_exp.mpr Real.one_half_lt_eulerMascheroniConstant.le
  norm_num at h1
  linarith

/-! ### The rigid part -/

/-- `|(1 - W(s)) S_{≥X₀}(s)| ≤ (2 + κ) min(1, κ(1+|s|)) Z_∞(1) e^{Ein(a) + 1/2}`. -/
lemma norm_rigid_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 8)
    {s : ℂ} (hs : 1 - a / Real.log X₀ ≤ s.re) :
    ‖(1 - Wfac (kap X₀) s) * (Zinf X₀ s - headSum X₀ s)‖ ≤
      (2 + kap X₀) * min 1 (kap X₀ * (1 + ‖s‖)) * (ZinfR X₀ 1 * Real.exp (Ein a + 1 / 2)) := by
  obtain ⟨hX0, h3, hκ, hκs, hκX⟩ := kap_facts hX
  set κ := kap X₀ with hκdef
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hδ1 : a / Real.log X₀ ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ hΛ0]; nlinarith
  have hσ0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ0
  have hX1 : 1 ≤ X₀ := by omega
  have hZ1 : 0 ≤ ZinfR X₀ 1 := (ZinfR_pos X₀ one_pos).le
  have hEin : 1 ≤ Real.exp (Ein a + 1 / 2) :=
    Real.one_le_exp (by linarith [Ein_nonneg ha.le])
  set Zb := ZinfR X₀ 1 * Real.exp (Ein a + 1 / 2) with hZb
  have hZ1b : ZinfR X₀ 1 ≤ Zb := le_mul_of_one_le_right hZ1 hEin
  have hSσ : ‖Zinf X₀ s - headSum X₀ s‖ ≤ Zb := by
    have h := norm_smooth_ge_le hX1 hσ0 (s := s) le_rfl
    rw [sub_self, Real.rpow_zero, one_mul] at h
    exact h.trans (ZinfR_le_exp_Ein hX ha ha8 hs)
  rw [norm_mul]
  rcases le_or_gt (κ * (1 + ‖s‖)) 1 with hm | hm
  · rw [min_eq_right hm]
    have hW := norm_one_sub_Wfac_le hκ hs0 hm
    calc ‖1 - Wfac κ s‖ * ‖Zinf X₀ s - headSum X₀ s‖ ≤ (κ * (1 + ‖s‖)) * Zb :=
          mul_le_mul hW hSσ (norm_nonneg _) (by positivity)
      _ ≤ (2 + κ) * (κ * (1 + ‖s‖)) * Zb := by
          have : 0 ≤ κ * (1 + ‖s‖) * Zb := by positivity
          nlinarith
  · rw [min_eq_left hm.le, mul_one]
    have hW : ‖1 - Wfac κ s‖ ≤ 1 + (1 + κ) ^ s.re :=
      (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_Wfac_le_rpow hκ hσ0.le])
    rcases le_or_gt s.re 1 with hσ1 | hσ1
    · have h1 : (1 + κ) ^ s.re ≤ 1 + κ := by
        calc (1 + κ) ^ s.re ≤ (1 + κ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hσ1
          _ = 1 + κ := Real.rpow_one _
      exact mul_le_mul (by linarith) hSσ (norm_nonneg _) (by linarith)
    · have hS1 := norm_smooth_ge_le hX1 one_pos (s := s) hσ1.le
      have hX1' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX1
      have hκX₀ : 1 + κ ≤ (X₀ : ℝ) := by
        have : (3 : ℝ) ≤ X₀ := by exact_mod_cast h3
        linarith
      have hp1 : (X₀ : ℝ) ^ (1 - s.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hX1' (by linarith)
      have hp0 : 0 ≤ (X₀ : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hX0.le _
      have hp2 : (1 + κ) ^ s.re * (X₀ : ℝ) ^ (1 - s.re) ≤ 1 + κ := by
        have e : (1 + κ) ^ s.re = (1 + κ) * (1 + κ) ^ (s.re - 1) := by
          rw [Real.rpow_sub (by linarith), Real.rpow_one]; field_simp
        have h4 : (1 + κ) ^ (s.re - 1) ≤ (X₀ : ℝ) ^ (s.re - 1) :=
          Real.rpow_le_rpow (by linarith) hκX₀ (by linarith)
        have h5 : (X₀ : ℝ) ^ (s.re - 1) * (X₀ : ℝ) ^ (1 - s.re) = 1 := by
          rw [← Real.rpow_add hX0]; simp
        rw [e]
        calc (1 + κ) * (1 + κ) ^ (s.re - 1) * (X₀ : ℝ) ^ (1 - s.re) ≤
              (1 + κ) * (X₀ : ℝ) ^ (s.re - 1) * (X₀ : ℝ) ^ (1 - s.re) := by gcongr
          _ = 1 + κ := by rw [mul_assoc, h5, mul_one]
      calc ‖1 - Wfac κ s‖ * ‖Zinf X₀ s - headSum X₀ s‖ ≤
            (1 + (1 + κ) ^ s.re) * ((X₀ : ℝ) ^ (1 - s.re) * ZinfR X₀ 1) :=
            mul_le_mul hW hS1 (norm_nonneg _) (by positivity)
        _ = (X₀ ^ (1 - s.re) + (1 + κ) ^ s.re * (X₀ : ℝ) ^ (1 - s.re)) * ZinfR X₀ 1 := by
            ring
        _ ≤ (2 + κ) * Zb := by
            have : ((X₀ : ℝ) ^ (1 - s.re) + (1 + κ) ^ s.re * (X₀ : ℝ) ^ (1 - s.re)) ≤ 2 + κ := by
              linarith
            calc _ ≤ (2 + κ) * ZinfR X₀ 1 := mul_le_mul_of_nonneg_right this hZ1
              _ ≤ _ := mul_le_mul_of_nonneg_left hZ1b (by linarith)

/-! ### Lemma 4.3 -/

/-- **Lemma 4.3 (The base factor at all heights)**, first bound: for `0 < a ≤ 8`,
`σ ≥ 1 - a/Λ` and `s ≠ 1`,
`|Ê(s)| ≤ 2.1 e^a Λ + 4.04 e^{Ein(a)} min(1, κ(1+|s|)) e^γ Λ + 3κe^a + 1`. -/
theorem lemma_4_3 {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 8)
    {s : ℂ} (hs : 1 - a / Real.log X₀ ≤ s.re) (hs1 : s ≠ 1) :
    ‖EHat X₀ s‖ ≤ 2.1 * Real.exp a * Real.log X₀ +
      4.04 * Real.exp (Ein a) * min 1 (kap X₀ * (1 + ‖s‖)) *
        Real.exp Real.eulerMascheroniConstant * Real.log X₀ +
      3 * kap X₀ * Real.exp a + 1 := by
  obtain ⟨hX0, h3, hκ, hκs, hκX⟩ := kap_facts hX
  set κ := kap X₀ with hκdef
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hσ0 : 0 < s.re := by
    have : a / Λ ≤ 1 / 10 ^ 7 := by rw [div_le_iff₀ hΛ0]; nlinarith
    linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ0
  have hX1 : 1 ≤ X₀ := by omega
  have hEa := Real.exp_pos a
  rw [EHat_eq hX1 hs1]
  -- the bracket
  have hsum : ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re) ≤ Real.exp a * (1 + Λ) := by
    calc ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re) ≤
          ∑ n ∈ Finset.Ico 1 X₀, Real.exp a * (1 / (n : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
          exact rpow_neg_le_exp_div hX0 hΛ0 ha.le hs h1 h2.le
      _ ≤ Real.exp a * (1 + Λ) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_inv_Ico_le hX1) hEa.le
  have hH : ‖headSum X₀ s‖ ≤ Real.exp a * (1 + Λ) := by
    unfold headSum
    refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) hsum)
    refine Finset.sum_congr rfl fun n hn => ?_
    have : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos this, Complex.neg_re]
  have hI : ‖∑ n ∈ Finset.Ico 1 X₀, intCpow s n‖ ≤ Real.exp a * (1 + Λ) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn =>
      norm_intCpow_le hs1 hσ0.le (Finset.mem_Ico.mp hn).1).trans hsum)
  have hbr : ‖headSum X₀ s - 1 - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n‖ ≤
      2.1 * Real.exp a * Λ + 1 := by
    have h1 := norm_sub_le (headSum X₀ s - 1) (∑ n ∈ Finset.Ico 1 X₀, intCpow s n)
    have h2 := norm_sub_le (headSum X₀ s) 1
    rw [norm_one] at h2
    nlinarith
  -- the rigid part
  have hrig := norm_rigid_le hX ha ha8 hs
  have hrig' : (2 + κ) * min 1 (κ * (1 + ‖s‖)) * (ZinfR X₀ 1 * Real.exp (Ein a + 1 / 2)) ≤
      4.04 * Real.exp (Ein a) * min 1 (κ * (1 + ‖s‖)) *
        Real.exp Real.eulerMascheroniConstant * Λ := by
    have hZ := Mertens.ZinfR_one_le (X₀ := X₀) (by linarith)
    have hm0 : 0 ≤ min 1 (κ * (1 + ‖s‖)) := le_min zero_le_one (by positivity)
    have hg := Real.exp_le_exp.mpr Real.one_half_lt_eulerMascheroniConstant.le
    rw [Real.exp_add]
    have hE0 := Real.exp_pos (Ein a)
    have hh0 := Real.exp_pos (1 / 2 : ℝ)
    have hZ0 : 0 ≤ ZinfR X₀ 1 := (ZinfR_pos X₀ one_pos).le
    calc (2 + κ) * min 1 (κ * (1 + ‖s‖)) * (ZinfR X₀ 1 * (Real.exp (Ein a) * Real.exp (1 / 2)))
          ≤ (2 + κ) * min 1 (κ * (1 + ‖s‖)) * (1.8 * Λ * (Real.exp (Ein a) *
            Real.exp Real.eulerMascheroniConstant)) := by
          gcongr
      _ = ((2 + κ) * 1.8) * (Real.exp (Ein a) * min 1 (κ * (1 + ‖s‖)) *
            Real.exp Real.eulerMascheroniConstant * Λ) := by ring
      _ ≤ 4.04 * (Real.exp (Ein a) * min 1 (κ * (1 + ‖s‖)) *
            Real.exp Real.eulerMascheroniConstant * Λ) := by
          gcongr
          linarith
      _ = _ := by ring
  -- the boundary
  have hB := norm_boundary_le_three (X₀ := X₀) (by linarith) hκ (by linarith) hκX ha.le
    (by linarith) hs hs0
  have h1 := norm_add_le (headSum X₀ s - 1 - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n +
    (1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s)) (boundary X₀ κ s)
  have h2 := norm_add_le (headSum X₀ s - 1 - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n)
    ((1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s))
  linarith

/-- **Lemma 4.3**, second bound: `|Ê(s)| ≤ C_a (1 + κ|s|) e^γ log X₀`,
`C_a = 2.1 e^a + 5 e^{Ein(a)}`. -/
theorem lemma_4_3' {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 8)
    {s : ℂ} (hs : 1 - a / Real.log X₀ ≤ s.re) (hs1 : s ≠ 1) :
    ‖EHat X₀ s‖ ≤ (2.1 * Real.exp a + 5 * Real.exp (Ein a)) * (1 + kap X₀ * ‖s‖) *
      Real.exp Real.eulerMascheroniConstant * Real.log X₀ := by
  obtain ⟨_, _, hκ, hκs, _⟩ := kap_facts hX
  refine (lemma_4_3 hX ha ha8 hs hs1).trans ?_
  set κ := kap X₀
  set Λ := Real.log X₀
  set G := Real.exp Real.eulerMascheroniConstant
  have hG := exp_gamma_ge
  have hEa : 1 ≤ Real.exp a := Real.one_le_exp ha.le
  have hEin : 0 < Real.exp (Ein a) := Real.exp_pos _
  have hm : min 1 (κ * (1 + ‖s‖)) ≤ 1 := min_le_left _ _
  have hm0 : 0 ≤ min 1 (κ * (1 + ‖s‖)) := le_min zero_le_one (by positivity)
  have hk : 1 ≤ 1 + κ * ‖s‖ := by have := norm_nonneg s; nlinarith
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hX
  have e1 : 4.04 * Real.exp (Ein a) * min 1 (κ * (1 + ‖s‖)) * G * Λ ≤
      5 * Real.exp (Ein a) * G * Λ := by
    have : 0 ≤ Real.exp (Ein a) * G * Λ := by positivity
    nlinarith
  have e2 : 2.1 * Real.exp a * Λ + 3 * κ * Real.exp a + 1 ≤ 2.1 * Real.exp a * G * Λ := by
    have h1 : 2.1 * Real.exp a * Λ * 1.625 ≤ 2.1 * Real.exp a * Λ * G :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h2 : 3 * κ * Real.exp a ≤ Real.exp a := by nlinarith
    have h3 : 2 * Real.exp a ≤ 1.3125 * Real.exp a * Λ := by nlinarith
    nlinarith
  have e3 : (2.1 * Real.exp a + 5 * Real.exp (Ein a)) * G * Λ ≤
      (2.1 * Real.exp a + 5 * Real.exp (Ein a)) * (1 + κ * ‖s‖) * G * Λ := by
    have : 0 ≤ (2.1 * Real.exp a + 5 * Real.exp (Ein a)) * G * Λ := by positivity
    nlinarith
  nlinarith

/-- `log C_8 < 439.4`, `C_8 = 2.1 e^8 + 5 e^{Ein(8)}` (Lemma 4.3 with `a = 8`). -/
theorem log_C8_lt : Real.log (2.1 * Real.exp 8 + 5 * Real.exp (Ein 8)) < 439.4 := by
  have hE := Real.exp_le_exp.mpr Ein_eight_le
  set E := Real.exp 437.73 with hEdef
  have hE1 : (90000 : ℝ) ≤ E := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 437.73 by norm_num)
    norm_num at this ⊢; linarith
  have h8 := exp_eight_le
  have h167 : (5.2 : ℝ) < Real.exp 1.67 := by
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.67 by norm_num) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hsplit : Real.exp 439.4 = E * Real.exp 1.67 := by
    rw [hEdef, ← Real.exp_add]; norm_num
  rw [Real.log_lt_iff_lt_exp (by positivity), hsplit]
  have hE0 : 0 < E := Real.exp_pos _
  have h1 : E * 5.2 < E * Real.exp 1.67 := mul_lt_mul_of_pos_left h167 hE0
  linarith

/-- **Lemma 4.3 near the pole**: `|Ê(s) + 1| ≤ 2` for `σ ≥ 1 - 8/Λ`, `0 < |s - 1| ≤ 1/8`. -/
theorem EHat_add_one_near_pole {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {s : ℂ}
    (hs : 1 - 8 / Real.log X₀ ≤ s.re) (hs1 : ‖s - 1‖ ≤ 1 / 8) (hs1' : s ≠ 1) :
    ‖EHat X₀ s + 1‖ ≤ 2 := by
  obtain ⟨hX0, h3, hκ, hκs, hκX⟩ := kap_facts hX
  set κ := kap X₀ with hκdef
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hX1 : 1 ≤ X₀ := by omega
  have hre := Complex.abs_re_le_norm (s - 1)
  rw [Complex.sub_re, Complex.one_re] at hre
  have hσ78 : 7 / 8 ≤ s.re := by linarith [(abs_le.mp (hre.trans hs1)).1]
  have hσ0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ0
  have hsn : ‖s‖ ≤ 9 / 8 := by
    have := norm_le_norm_add_norm_sub' s 1
    rw [norm_one] at this; linarith
  have e : EHat X₀ s + 1 = (headSum X₀ s - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n) +
      (1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s) + boundary X₀ κ s := by
    rw [EHat_eq hX1 hs1']; ring
  rw [e]
  -- the bracket: `∑_{n<X₀} (n^{-s} - I_n)`
  have hbr : ‖headSum X₀ s - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n‖ ≤ 1.21 := by
    unfold headSum
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Ico 1 X₀, ‖((n : ℝ) : ℂ) ^ (-s) - intCpow s n‖ ≤
          ∑ n ∈ Finset.Ico 1 X₀, ‖s‖ / 2 * (n : ℝ) ^ (-s.re - 1) :=
          Finset.sum_le_sum fun n hn =>
            norm_cpow_sub_intCpow_le hs1' hs0 hσ0.le (Finset.mem_Ico.mp hn).1
      _ = ‖s‖ / 2 * ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re - 1) := by rw [Finset.mul_sum]
      _ ≤ 9 / 16 * (1 + 8 / 7) := by
          have h1 := sum_rpow_neg_le hσ0 X₀
          have h2 : 1 / s.re ≤ 8 / 7 := by
            rw [div_le_div_iff₀ hσ0 (by norm_num)]; linarith
          have h0 : 0 ≤ ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re - 1) :=
            Finset.sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
          calc ‖s‖ / 2 * ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re - 1) ≤
                9 / 16 * ∑ n ∈ Finset.Ico 1 X₀, (n : ℝ) ^ (-s.re - 1) := by
                apply mul_le_mul_of_nonneg_right _ h0; linarith
            _ ≤ 9 / 16 * (1 + 8 / 7) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
      _ ≤ 1.21 := by norm_num
  -- the rigid part
  have hm : κ * (1 + ‖s‖) ≤ 1 := by nlinarith
  have hrig : ‖(1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s)‖ ≤ 0.01 := by
    rw [norm_mul]
    have hW := norm_one_sub_Wfac_le hκ hs0 hm
    have hS := norm_smooth_ge_le hX1 hσ0 (s := s) le_rfl
    rw [sub_self, Real.rpow_zero, one_mul] at hS
    have hZ := ZinfR_le_exp_Ein hX (by norm_num) le_rfl hs
    have hZ1 := Mertens.ZinfR_one_le (X₀ := X₀) (by linarith)
    have hE := Real.exp_le_exp.mpr (show Ein 8 + 1 / 2 ≤ 438.23 by linarith [Ein_eight_le])
    -- `κ Λ e^{438.23} ≤ 100 e^{438.23 + Λ/100 - 119Λ/300}` is tiny
    have hΛe : Λ ≤ 100 * Real.exp (Λ / 100) := by
      have := Real.add_one_le_exp (Λ / 100); linarith
    have htiny : κ * (100 * Real.exp (Λ / 100)) * Real.exp 438.23 ≤ 1 / 10 ^ 3 := by
      rw [hκdef, kap_eq hX0, ← hΛ]
      set y := 119 / 300 * Λ - Λ / 100 - 438.23 with hy
      have e2 : Real.exp (-(119 / 300 * Λ)) * (100 * Real.exp (Λ / 100)) * Real.exp 438.23 =
          100 * Real.exp (-y) := by
        rw [mul_comm (Real.exp _) (100 * _), mul_assoc 100, mul_assoc 100, ← Real.exp_add,
          ← Real.exp_add]
        congr 2; rw [hy]; ring
      rw [e2]
      have hy5 : 10 ^ 5 ≤ y := by rw [hy]; nlinarith
      have h1 := Real.add_one_le_exp y
      have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      have h4 := Real.exp_pos (-y)
      nlinarith
    have hZ0 : 0 ≤ ZinfR X₀ 1 := (ZinfR_pos X₀ one_pos).le
    calc ‖1 - Wfac κ s‖ * ‖Zinf X₀ s - headSum X₀ s‖ ≤
          (κ * (1 + ‖s‖)) * (ZinfR X₀ 1 * Real.exp (Ein 8 + 1 / 2)) :=
          mul_le_mul hW (hS.trans hZ) (norm_nonneg _) (by positivity)
      _ ≤ (κ * (17 / 8)) * ((1.8 * (100 * Real.exp (Λ / 100))) * Real.exp 438.23) := by
          gcongr
          · linarith
          · linarith
      _ = 3.825 * (κ * (100 * Real.exp (Λ / 100)) * Real.exp 438.23) := by ring
      _ ≤ 3.825 * (1 / 10 ^ 3) := by gcongr
      _ ≤ 0.01 := by norm_num
  -- the boundary
  have hB := norm_boundary_le_three (X₀ := X₀) (by linarith) hκ (by linarith) hκX
    (by norm_num : (0 : ℝ) ≤ 8) (by linarith) hs hs0
  have hB' : 3 * κ * Real.exp 8 ≤ 0.01 := by
    have := exp_eight_le
    nlinarith
  have h1 := norm_add_le (headSum X₀ s - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n +
    (1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s)) (boundary X₀ κ s)
  have h2 := norm_add_le (headSum X₀ s - ∑ n ∈ Finset.Ico 1 X₀, intCpow s n)
    ((1 - Wfac κ s) * (Zinf X₀ s - headSum X₀ s))
  linarith

end LocalPNT

end
