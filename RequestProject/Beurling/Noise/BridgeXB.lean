module

public import RequestProject.Beurling.Noise.BridgeXBStep

/-!
# Lemma 5.27 (the `X₀` jump in exact chain form): Steps 1–2 summed

`xb_split` : for a start `x`,

  `|R_res 1_{[X₀,∞)}(x) - ρ^sh_1(x)| ≤ 𝔅(x) + 𝒯(x)`,

where (`xbB`, eq. (frakB))

  `𝔅(x) = ∑_{n ∈ 𝔹₀} |c_n|/(2n) + ∑_{(d,w) ∈ 𝔹₁} TV(D_d)/(2dw)`
         `+ λ₀ ∑_{(d,w) ∈ 𝔹₂} ‖D_d‖_KR/(dw·wH_n)`

over the levels `n ≥ 2` with `x/n ≥ X₀⁻/2` (all others carry no mass), with
`𝔹₀ = {n : |x/n - X₀| ≤ H_n/2}`, `𝔹₁` the `X₀`-near steps with a non-terminal parent `d ≥ 2`
(a terminal parent contributes nothing, `xbStep_terminal`), and `𝔹₂` the steps `d ≥ 2` that are not
`X₀`-near with `|x/n - X₀| ≤ (1 + θ)H_n/2 + R_d/w`; and the `τ`-part (`xbTau`)

  `𝒯(x) = ∑_n n⁻¹ [∑_{n' ∣ n} TV(𝒯^nom_{n'→n} S^τ_{n'}) + ∑_{(d,w) ∈ 𝔹₁} TV(Ẽ_d)]`

(Step 3 of the paper; it is bounded in `BridgeXBTau.lean`).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

open scoped Classical in
/-- The bound of one step in `𝔅`. -/
noncomputable def xbBstep (X0 θ lam0 : ℝ) (d n : ℕ) : ℝ :=
  if d = 1 then 0 else
    if X0Near P.labelVal x H X0m d n then
      (if Terminal P.labelVal x H X0m X0 d then 0 else 1 / 2 * TVD P H tw X0m x d)
    else if |posn P.labelVal x n - X0| ≤ (1 + θ) * H (posn P.labelVal x n) / 2 +
          1.02 * H (posn P.labelVal x d) / Vl P (n / d)
      then lam0 * KRD P H tw X0m x d / (Vl P (n / d) * H (posn P.labelVal x n)) else 0

open scoped Classical in
/-- **`𝔅(x)`** (eq. (frakB)). -/
noncomputable def xbB (X0 θ lam0 : ℝ) : ℝ :=
  ∑ n ∈ levels P X0m x, ((if |posn P.labelVal x n - X0| ≤ H (posn P.labelVal x n) / 2
      then |cN P tw X0m x n| / 2 else 0) +
    ∑ d ∈ n.properDivisors, xbBstep P H tw X0m x X0 θ lam0 d n) / Vl P n

open scoped Classical in
/-- The parents of the `𝔹₁` steps: `X₀`-near, `d ≥ 2`, non-terminal. -/
noncomputable def B1set (X0 : ℝ) (n : ℕ) : Finset ℕ :=
  n.properDivisors.filter (fun d => d ≠ 1 ∧ X0Near P.labelVal x H X0m d n ∧
    ¬ Terminal P.labelVal x H X0m X0 d)

/-- **The `τ`-part** `𝒯(x)` of the proof of Lemma 5.27 (Step 3). -/
noncomputable def xbTau (X0 : ℝ) : ℝ :=
  ∑ n ∈ levels P X0m x, (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n +
    ∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) / Vl P n

variable {P H tw X0m x}

lemma abs_setIntegral_le_TV {f : ℝ → ℝ} (hf : Integrable f) (S : Set ℝ) :
    |∫ t in S, f t| ≤ (∫⁻ t, ‖f t‖ₑ).toReal := by
  rw [← integral_norm_eq_lintegral_enorm hf.1]
  refine (abs_integral_le_integral_abs).trans ?_
  exact setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun t => abs_nonneg _)

/-- **The bound at one level.** -/
theorem xb_level_bound {ε θ lam0 X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (hlam : 1 + 3 * θ ≤ lam0) {n : ℕ}
    (hn : n ∈ levels P X0m x) :
    |(∫ t in Ici X0, gK P.labelVal x H (phiT tw X0m) n t) -
        cN P tw X0m x n * (if X0 ≤ posn P.labelVal x n then 1 else 0)| ≤
      ((if |posn P.labelVal x n - X0| ≤ H (posn P.labelVal x n) / 2
        then |cN P tw X0m x n| / 2 else 0) +
        ∑ d ∈ n.properDivisors, xbBstep P H tw X0m x X0 θ lam0 d n) +
      (∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n +
        ∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d) := by
  classical
  have hH := hP.reg
  obtain ⟨hnA, hn2⟩ := Finset.mem_filter.mp hn
  have hXm := hP.X0m_pos
  have hpos : X0m / 2 ≤ posn P.labelVal x n := posn_ge_of_mem_NAll hnA (by linarith)
  rw [level_identity hP hX0e hp2 hn2]
  -- the three parts
  have hA : |cN P tw X0m x n * (Gs H X0 (posn P.labelVal x n) -
      (if X0 ≤ posn P.labelVal x n then 1 else 0))| ≤
      if |posn P.labelVal x n - X0| ≤ H (posn P.labelVal x n) / 2
        then |cN P tw X0m x n| / 2 else 0 := by
    rw [abs_mul]
    have := abs_Gs_sub_ind_le hH X0 (posn P.labelVal x n)
    by_cases h1 : |posn P.labelVal x n - X0| ≤ H (posn P.labelVal x n) / 2
    · rw [if_pos h1] at this ⊢
      calc |cN P tw X0m x n| * _ ≤ |cN P tw X0m x n| * (1 / 2) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |cN P tw X0m x n| / 2 := by ring
    · rw [if_neg h1] at this ⊢
      rw [le_antisymm this (abs_nonneg _), mul_zero]
  have hB : ∀ d ∈ n.properDivisors, |xbStep P H tw X0m x X0 d n| ≤
      xbBstep P H tw X0m x X0 θ lam0 d n +
        (if d ∈ B1set P H X0m x X0 n then TVE P H tw X0m x d else 0) := by
    intro d hd
    unfold xbBstep
    by_cases h1 : d = 1
    · subst h1; rw [xbStep_one]
      have : (1 : ℕ) ∉ B1set P H X0m x X0 n := fun h => (Finset.mem_filter.mp h).2.1 rfl
      simp [this]
    rw [if_neg h1]
    by_cases hX : X0Near P.labelVal x H X0m d n
    · rw [if_pos hX]
      by_cases hT : Terminal P.labelVal x H X0m X0 d
      · have : d ∉ B1set P H X0m x X0 n := fun h => (Finset.mem_filter.mp h).2.2.2 hT
        rw [if_pos hT, if_neg this, xbStep_terminal hP hX0e hp2 X0 hd h1 hT]
        simp
      · have hm : d ∈ B1set P H X0m x X0 n := Finset.mem_filter.mpr ⟨hd, h1, hX, hT⟩
        rw [if_neg hT, if_pos hm]
        exact near_bound hP hp2 X0 hd h1 hX
    · have : d ∉ B1set P H X0m x X0 n := fun h => hX (Finset.mem_filter.mp h).2.2.1
      rw [if_neg hX, if_neg this, add_zero]
      exact far_bound hP hX0e hp2 hlam hd h1 hpos hX
  have hBs : |∑ d ∈ n.properDivisors, xbStep P H tw X0m x X0 d n| ≤
      ∑ d ∈ n.properDivisors, xbBstep P H tw X0m x X0 θ lam0 d n +
        ∑ d ∈ B1set P H X0m x X0 n, TVE P H tw X0m x d := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hB).trans (le_of_eq ?_))
    have hsub : B1set P H X0m x X0 n ⊆ n.properDivisors := Finset.filter_subset _ _
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  have hC : |∫ t in Ici X0, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
      Tch P.labelVal H (kapN tw X0m P.labelVal x) n' (Stau P.labelVal x H tw X0m n') n t| ≤
      ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n := by
    have hi : ∀ n', Integrable
        (Tch P.labelVal H (kapN tw X0m P.labelVal x) n' (Stau P.labelVal x H tw X0m n') n) :=
      fun n' => (integrable_Tch hH _ n' (integrable_Stau hH n').1 (integrable_Stau hH n').2 n).1
    rw [integral_finset_sum _ fun n' _ => (hi n').integrableOn]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
    exact abs_setIntegral_le_TV (hi n') _
  calc _ ≤ |cN P tw X0m x n * (Gs H X0 (posn P.labelVal x n) -
          (if X0 ≤ posn P.labelVal x n then 1 else 0))| +
        |∑ d ∈ n.properDivisors, xbStep P H tw X0m x X0 d n| +
        |∫ t in Ici X0, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
          Tch P.labelVal H (kapN tw X0m P.labelVal x) n' (Stau P.labelVal x H tw X0m n') n t| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

/-- **Lemma 5.27, Steps 1–2**: `|R_res 1_{[X₀,∞)}(x) - ρ^sh_1(x)| ≤ 𝔅(x) + 𝒯(x)`. -/
theorem xb_split {ε θ lam0 X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (hlam : 1 + 3 * θ ≤ lam0) (hx : X0m ≤ x) :
    |Rres P H tw X0m x ((Ici X0).indicator fun _ => 1) -
        rhoSh P tw X0m x ((Ici X0).indicator fun _ => 1)| ≤
      xbB P H tw X0m x X0 θ lam0 + xbTau P H tw X0m x X0 := by
  have hXm := hP.X0m_pos
  unfold Rres
  rw [rhoSh_eq ht hXm hx, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  unfold xbB xbTau
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hV := KR.valN_labelVal_pos P n
  rw [← sub_div, abs_div, abs_of_pos hV, ← add_div]
  apply div_le_div_of_nonneg_right _ hV.le
  have e1 : ∫ t, (Ici X0).indicator (fun _ => (1 : ℝ)) t * gK P.labelVal x H (phiT tw X0m) n t =
      ∫ t in Ici X0, gK P.labelVal x H (phiT tw X0m) n t := by
    rw [← integral_indicator measurableSet_Ici]
    congr 1; funext t
    simp only [Set.indicator]; split_ifs <;> ring
  have e2 : (Ici X0).indicator (fun _ => (1 : ℝ)) (posn P.labelVal x n) =
      if X0 ≤ posn P.labelVal x n then 1 else 0 := by
    simp only [Set.indicator, Set.mem_Ici]
  rw [e1, e2]
  exact xb_level_bound hP hX0e hp2 hlam hn

end KR

end
