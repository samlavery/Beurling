module

public import RequestProject.Beurling.Noise.RML7GMain
public import RequestProject.Beurling.Noise.RML8GSum

/-!
# Lemma 5.34, second bullet (correction #110), with the paper's constant

* `gScaleBound_Kpt_tight` : `GScaleBound` for `G = K_pt F` with `A = C'_S ∑_j (log 3v_j)² M_j`,
  `C'_S = 10` (Lemma 5.21(iii) applied once; the old `gScaleBound_Kpt` paid each scale's
  window three times and had `70`).
-/

@[expose] public section

open Finset Real BeurlingSystem KR.Sharp KR.TNP

namespace KR.RML7G

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **`GScaleBound` for `G = K_pt F` with the paper's constant** (Lemma 5.34, second bullet,
correction #110): `A = C'_S ∑_j (log 3v_j)² M_j`, `C'_S = 10`, with the scale weights
`Gb y u = ∑_j M_j Om8 v_j u` (Lemma 5.21(iii) applied once, `scale_sum_tight`). -/
theorem gScaleBound_Kpt_tight (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (hO : KR.Ops.OpHyp P H X0m)
    {X0 x : ℝ} (hX0 : 12 ≤ X0) (Nf : ℝ → ℕ) (F : ℝ → ℝ) {J : ℕ}
    (hJ : x + H x / 2 ≤ X0m * 2 ^ J) (hx1 : 1 ≤ x - H x / 2)
    (hwin : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 → 2 * y / X0m ≤ Z)
    (M : ℕ → ℝ) (hM0 : ∀ j, 0 ≤ M j)
    (hF : ∀ j < J, ∀ s, X0m * 2 ^ j ≤ s → s < 2 * (X0m * 2 ^ j) →
      s ≤ (x + H x / 2) / 2 → |F s| ≤ M j) :
    GScaleBound P H X0 (Kpt P tw X0m F) x
      (10 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j) Nf
      (fun y u => ∑ j ∈ range J, M j * RML8G.Om8 (X0m * 2 ^ j) u) := by
  have hX := h.width.X0m_pos
  have hXm := h.hXm
  have hp2 := hO.p2
  have hbs := h.hbs
  have hv0 : ∀ j : ℕ, 0 < X0m * 2 ^ j := fun j => by positivity
  have hvX : ∀ j : ℕ, X0m ≤ X0m * 2 ^ j := fun j => by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : ∀ j : ℕ, 100000000 ≤ Real.log (3 * (X0m * 2 ^ j)) := fun j =>
    hXm.trans (Real.log_le_log hX (by linarith [hvX j]))
  have hds : ∀ j : ℕ, P.DecidedSmall (tI tw) (X0m * 2 ^ j) := fun j => decidedSmall_of h (hv0 j)
  intro y hy1 hy2
  have hy0 : 1 ≤ y := by linarith
  have hZy := hwin y hy1 hy2
  have hyJ : y ≤ X0m * 2 ^ J := by linarith
  have hFy : ∀ j < J, ∀ s, X0m * 2 ^ j ≤ s → s < 2 * (X0m * 2 ^ j) → s ≤ y / 2 →
      |F s| ≤ M j := fun j hj s h1 h2 h3 => hF j hj s h1 h2 (by linarith)
  -- `t/v ≤ Z` below `y`
  have htZ : ∀ j : ℕ, ∀ t, 0 < t → t ≤ y → t / (X0m * 2 ^ j) ≤ Z := by
    intro j t ht hty
    have h1 : t / (X0m * 2 ^ j) ≤ t / X0m := div_le_div_of_nonneg_left ht.le hX (hvX j)
    have h2 : t / X0m ≤ 2 * y / X0m := div_le_div_of_nonneg_right (by linarith) hX.le
    linarith
  have hSs0 : ∀ u, ∀ j : ℕ, 0 ≤ RML8G.Om8 (X0m * 2 ^ j) u := fun u j => RML8G.Om8_nonneg _ _
  refine ⟨?_, ?_, ?_⟩
  · -- `log y · |G y| ≤ A`
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy0
    have hpt := abs_Kpt_le P tw hX hp2 F hyJ M hM0 hFy
    calc Real.log y * |Kpt P tw X0m F y|
        ≤ Real.log y * ∑ j ∈ range J, P.omegaW (tI tw) y (X0m * 2 ^ j) * M j :=
          mul_le_mul_of_nonneg_left hpt hly
      _ = ∑ j ∈ range J, (Real.log y * P.omegaW (tI tw) y (X0m * 2 ^ j)) * M j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j ∈ range J, (2.9 * Real.log (3 * (X0m * 2 ^ j))) * M j := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hM0 j)
          exact Margin.Var.logt_omega_le hbs (hds j) (hv0 j) (hL j) (by linarith)
            (htZ j y (by linarith) le_rfl)
      _ ≤ 10 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          have hl := hL j
          have : 2.9 * Real.log (3 * (X0m * 2 ^ j)) ≤
              10 * Real.log (3 * (X0m * 2 ^ j)) ^ 2 := by nlinarith
          nlinarith [hM0 j]
  · intro u hu
    have hupos : 3 ≤ u := by
      obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (hSs0 u j), ?_⟩
    intro n hn hn2 t ht
    by_cases ht2 : t < 2 * X0m
    · rw [KR.Ops.Kpt_zero_low hX hp2 F ht2, abs_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (hSs0 u j)
    push_neg at ht2
    obtain ⟨-, hnu1, hnu2⟩ := (mem_NW P (by linarith : (0 : ℝ) < u)).mp hn
    have hV2 : 2 ≤ Vl P n := KR.Ops.Vl_ge_two (P := P) hp2 hn2
    set s := posn P.labelVal y n with hs
    have hsdef : s = y / LemmaM.valN P.labelVal n := rfl
    have hsy : s ≤ y / 2 := by
      rw [hsdef]; exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hV2
    rw [← hsdef] at hnu1 hnu2
    have hsX : X0m / 2 ≤ s := by
      by_contra hc; push_neg at hc
      have := hO.low s hc
      have h1 := (abs_le.mp ht).2
      linarith
    have hHs := hO.small s hsX
    have hHs0 := (hO.pos s).le
    obtain ⟨ht1, ht1'⟩ := abs_le.mp ht
    have hT1 : 0.89 * u ≤ t := by linarith
    have hT2 : t ≤ 2.21 * u := by linarith
    have hT4 : t ≤ 0.56 * y := by linarith
    have ht0 : 0 < t := by linarith
    have htJ : t ≤ X0m * 2 ^ J := by linarith
    have hFt : ∀ j < J, ∀ s', X0m * 2 ^ j ≤ s' → s' < 2 * (X0m * 2 ^ j) → s' ≤ t / 2 →
        |F s'| ≤ M j := fun j hj s' h1 h2 h3 => hFy j hj s' h1 h2 (by linarith)
    refine (abs_Kpt_le P tw hX hp2 F htJ M hM0 hFt).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm (M j)]
    refine mul_le_mul_of_nonneg_right ?_ (hM0 j)
    have htZt := htZ j t ht0 (by linarith)
    by_cases htv : t < X0m * 2 ^ j
    · rw [omegaW_eq_zero_of_lt (tI tw) (hv0 j) htv]; exact RML8G.Om8_nonneg _ _
    push_neg at htv
    unfold RML8G.Om8
    rw [if_neg (by push_neg; linarith)]
    refine (hbs.omega_le_OmB (hds j) (hv0 j) (hL j) ht0 htZt).trans (LemS.OmB_anti (hL j) ?_)
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hT1 (by positivity))
  · -- the scale sum
    calc ∑ u ∈ dyScales X0 y (Nf y), Real.log (2 * u) *
          ∑ j ∈ range J, M j * RML8G.Om8 (X0m * 2 ^ j) u
        = ∑ j ∈ range J, M j * ∑ u ∈ dyScales X0 y (Nf y),
            Real.log (2 * u) * RML8G.Om8 (X0m * 2 ^ j) u := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => by ring
      _ ≤ ∑ j ∈ range J, M j * (10 * Real.log (3 * (X0m * 2 ^ j)) ^ 2) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hM0 j)
          exact RML8G.scale_sum_tight hX0 (hv0 j) (hL j)
      _ ≤ 10 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          have := hM0 j
          have := sq_nonneg (Real.log (3 * (X0m * 2 ^ j)))
          nlinarith

end KR.RML7G

end
