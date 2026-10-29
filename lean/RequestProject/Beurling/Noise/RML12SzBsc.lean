module

public import RequestProject.Beurling.Model.OscBlockG

/-!
# A sharper form of eq. (osc), second display (round 12)

`BModel.sum_oscG_le` (Model) gives `∑_j (log 3v_j)² o_j ≤ e^{-41}`. Its proof actually gives
`≤ 34·10⁻⁴³ + 2.0001/(δ M)` with `M = L_* - 4 log 2 ≥ 3.928·10¹⁸`; the `G`-term of Lemma 5.34
(`Gsum`) contains `o_j` twice (once as `o_j`, once inside `F̄_r(j)`), so the sharper constant
`7.4·10⁻¹⁹ ≤ e^{-41}/2` is needed: `sum_oscG_sharp` is the same proof with the final
constants tightened.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP Absorbed
  AbsorbEmpty QueueMono

namespace BModel.RML12

variable {X₀ : ℕ}

set_option maxHeartbeats 2000000 in
/-- **eq. (osc), second display, sharp**: `∑_{j ≤ J} (log 3v_j)² o_j ≤ 7.4·10⁻¹⁹`. -/
theorem sum_oscG_sharp (hX : 10 ^ 8 ≤ Real.log X₀) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i ≤
      74 / 10 ^ 20 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hXm0 : 0 < Xm X₀ := by linarith
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.6931 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlog6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  have hlog60 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  set Λ := Real.log (Xm X₀ / 2) with hΛ
  have hΛ1 : 10 ^ 8 - 2 ≤ Λ := by
    have h1 : Real.log ((X₀ : ℝ) / 4) ≤ Λ := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hLs : (3.929 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  set M := Lstar X₀ - 4 * δ with hM
  have hM0 : 3.928 * 10 ^ 18 ≤ M := by linarith
  have hMp : 0 < M := by linarith
  set φ : ℕ → ℝ := fun i => psi1 M (Λ + i * δ - δ) with hφ
  -- split each term
  have hsplit : ∀ i : ℕ, Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i ≤
      (Xm X₀ * 2 ^ i) ^ (-(1 / 20 : ℝ)) + 2.0001 / δ * (φ i - φ (i + 1)) := by
    intro i
    obtain ⟨e1, e2, e3⟩ := logs_blk hX i
    set u := Xm X₀ * 2 ^ i with hu
    have hu1 : Xm X₀ ≤ u := by
      rw [hu]; have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hu4 : (X₀ : ℝ) ≤ 4 * u := by linarith
    have hn := nonA3_le hX hu4
    set ℓ := Λ + i * δ with hℓ
    have hℓ1 : 10 ^ 8 - 2 ≤ ℓ := by
      have : (0 : ℝ) ≤ i * δ := by positivity
      linarith
    have hlℓ : Real.log (u / 2) = ℓ := by rw [e1]
    have hA : Real.log (3 * u) ^ 2 * (2 * (if Lstar X₀ < Real.log (4 * u) then
        (Real.log (u / 2) ^ 4)⁻¹ else 0)) ≤ 2.0001 / δ * (φ i - φ (i + 1)) := by
      have e4 : Λ + ((i + 1 : ℕ) : ℝ) * δ - δ = ℓ := by push_cast; ring
      simp only [hφ, e4]
      rw [e3, e2, hlℓ]
      split_ifs with hL
      · have hgap := psi1_gap hMp (by linarith) (show M ≤ ℓ - δ by linarith)
        have hℓ0 : 0 < ℓ := by linarith
        have key : (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) ≤ 2.0001 / ℓ ^ 2 := by
          rw [show (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) = 2 * (ℓ + Real.log 6) ^ 2 / ℓ ^ 4 by
            field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (ℓ + Real.log 6) ^ 2 ≤ 1.00005 * ℓ ^ 2 := by nlinarith
          have : 0 < ℓ ^ 2 := by positivity
          nlinarith
        calc (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) ≤ 2.0001 / ℓ ^ 2 := key
          _ = 2.0001 / δ * (δ / ℓ ^ 2) := by field_simp
          _ ≤ 2.0001 / δ * (psi1 M (ℓ - δ) - psi1 M ℓ) :=
              mul_le_mul_of_nonneg_left hgap (by positivity)
      · have := psi1_anti hMp (show ℓ - δ ≤ ℓ by linarith)
        have : 0 ≤ psi1 M (ℓ - δ) - psi1 M ℓ := by linarith
        simp only [mul_zero]
        positivity
    unfold obG Bsc
    rw [← hu]
    have e : Real.log (3 * u) ^ 2 * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) /
        (kappaParam X₀ * u) + 2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 4 : ℝ)) +
        2 * (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0)) =
        Real.log (3 * u) ^ 2 * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) /
        (kappaParam X₀ * u) + 2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 4 : ℝ))) +
        Real.log (3 * u) ^ 2 * (2 * (if Lstar X₀ < Real.log (4 * u) then
          (Real.log (u / 2) ^ 4)⁻¹ else 0)) := by ring
    rw [e]
    linarith
  have hφ0 : ∀ i, 0 ≤ φ i := fun i => psi1_nonneg hMp _
  have hT := tele_le (f := fun i => 2.0001 / δ * (φ i - φ (i + 1))) (C := 2.0001 / δ)
    (by positivity) hφ0 (fun i => le_rfl) (J + 1)
  have hg := sum_geom_twentieth hXm0 (J + 1)
  have hq := Xm_rpow_le hX
  have hφ00 : φ 0 ≤ M⁻¹ := by
    simp only [hφ]; unfold psi1
    exact inv_anti₀ hMp (le_max_right _ _)
  have hA : 2.0001 / δ * φ 0 ≤ 7347 / 10 ^ 22 := by
    calc 2.0001 / δ * φ 0 ≤ 2.0001 / δ * M⁻¹ :=
          mul_le_mul_of_nonneg_left hφ00 (by positivity)
      _ ≤ 7347 / 10 ^ 22 := by
          rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc ∑ i ∈ Finset.range (J + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i
      ≤ ∑ i ∈ Finset.range (J + 1), ((Xm X₀ * 2 ^ i) ^ (-(1 / 20 : ℝ)) +
          2.0001 / δ * (φ i - φ (i + 1))) := Finset.sum_le_sum fun i _ => hsplit i
    _ = ∑ i ∈ Finset.range (J + 1), (Xm X₀ * 2 ^ i) ^ (-(1 / 20 : ℝ)) +
          ∑ i ∈ Finset.range (J + 1), 2.0001 / δ * (φ i - φ (i + 1)) :=
        Finset.sum_add_distrib
    _ ≤ 34 * (1 / 10 ^ 43) + 7347 / 10 ^ 22 := by nlinarith
    _ ≤ 74 / 10 ^ 20 := by norm_num

end BModel.RML12

end
