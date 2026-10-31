module

public import RequestProject.Beurling.Model.G1BDec34

/-!
# The jump at `X₀` in Step 3 of Proposition 5.35(B): the fields `hjS`, `hN`, `hHN`

04f-bridge.tex, proof of Proposition 5.35, range (B), Step 3, second bullet ("The jump of `T'`
at `X₀`"): only the levels `n ∈ [y/X₀ (1-2δ), y/X₀]` see the jump, and with `N_* = y/X₀`,
`I = [N_*(1-2δ), N_*]`,

  `#(𝒩 ∩ I) ≤ 4.01 δ N_* + 2H(N_*) + 2 + N_*^{θ/2}`

(the lag bound at both ends of `I`, the target count `T(I) ≤ 2.0001|I| + 1 + #𝒜(I)` and Lemma 6.26
on windows of length `u^{θ/2}`). This count is the named input `JumpCountR` (the displayed claim
of the paper). From it (`hjS_R`): `jS ≤ 4.1δ + 3H(N_*)/N_* + 2N_*^{θ/2-1}`. The side conditions
`hN` (`e^{log y/2} ≤ N_*`) and `hHN` (`H(N_*) ≤ N_*^{1/8}`) hold on range (B) (`hN_R`, `hHN_R`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

open Classical in
variable (θ X₀) in
/-- **The jump count** (04f-bridge.tex, Proposition 5.35(B), Step 3, second bullet): with
`N_* = y/X₀`, `#(𝒩 ∩ (N_*(1-2δ), N_*]) ≤ 4.01 δ N_* + 2H(N_*) + 2 + N_*^{θ/2}`. -/
def JumpCountR (ω : JitterΩ) (y δ : ℝ) : Prop :=
  ((((PR θ X₀ ω).elems (y / X₀)).filter
      (fun e => y / X₀ * (1 - 2 * δ) < (PR θ X₀ ω).val e)).card : ℝ) ≤
    4.01 * δ * (y / X₀) + 2 * Queue6.Hc X₀ (y / X₀) + 2 + (y / X₀) ^ (thetaB θ)

/-- On range (B) (`log y > X₀^{1/100}`, `Λ ≥ 10⁸`): `2 log X₀ ≤ log y`. -/
lemma two_logX_le {y : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) (hy0 : 0 < y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) : 2 * Real.log X₀ ≤ Real.log y := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  rw [Real.rpow_def_of_pos (by linarith)] at hyB
  set Λ := Real.log X₀
  have h2 := Real.pow_div_factorial_le_exp (x := Λ * (1 / 100)) (by positivity) 2
  norm_num [Nat.factorial] at h2
  have : 2 * Λ ≤ (Λ * (1 / 100)) ^ 2 / 2 := by nlinarith
  linarith

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc

/-- `N_* = y/X₀ ≥ e^{log y/2}` (the field `hN`), and `N_* ≥ X₀`. -/
theorem hN_R {y : ℝ} (hy0 : 0 < y) (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    Real.exp (Real.log y / 2) ≤ y / X₀ ∧ (X₀ : ℝ) ≤ y / X₀ := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have h2 := two_logX_le hc.hX hy0 hyB
  have hXp : (0 : ℝ) < X₀ := by linarith
  have e1 : y / X₀ = Real.exp (Real.log y - Real.log X₀) := by
    rw [Real.exp_sub, Real.exp_log hy0, Real.exp_log hXp]
  rw [e1]
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · calc (X₀ : ℝ) = Real.exp (Real.log X₀) := (Real.exp_log hXp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- `H(N_*) ≤ N_*^{1/8}` (the field `hHN`), `H(N_*) ≥ 0` (`hHN0`). -/
theorem hHN_R {y : ℝ} (hy0 : 0 < y) (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    0 ≤ Queue6.Hc X₀ (y / X₀) ∧ Queue6.Hc X₀ (y / X₀) ≤ (y / X₀) ^ (1 / 8 : ℝ) := by
  have hN := (hN_R hc hy0 hyB).2
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  unfold Queue6.Hc
  rw [max_eq_left hN]
  exact ⟨capH_nonneg _ _, InitialRange.capH_le_rpow hX0 hc.hX hN⟩

include hev in
set_option maxHeartbeats 1000000 in
/-- **The field `hjS`** (Step 3, second bullet), from the jump count `JumpCountR`:
`jS ≤ 4.1δ + 3H(N_*)/N_* + 2N_*^{θ/2-1}`, `N_* = y/X₀`, for `0 < δ ≤ 1/1000`. -/
theorem hjS_R (ω : JitterΩ) {y δ : ℝ} (hy0 : 0 < y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 1000)
    (hJ : JumpCountR θ X₀ ω y δ) :
    jS θ X₀ ω y δ ≤ 4.1 * δ + 3 * Queue6.Hc X₀ (y / X₀) / (y / X₀) +
      2 * (y / X₀) ^ (thetaB θ - 1) := by
  classical
  set P := PR θ X₀ ω with hP
  set N := y / X₀ with hNdef
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  obtain ⟨-, hNX⟩ := hN_R hc hy0 hyB
  have hN0 : 0 < N := by linarith
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  set F := (P.elems N).filter (fun e => N * (1 - 2 * δ) < P.val e) with hF
  -- each term is `< 1/(N(1-2δ))`
  have hlow : 0 < N * (1 - 2 * δ) := mul_pos hN0 (by linarith)
  have hsum : jS θ X₀ ω y δ ≤ F.card * (1 / (N * (1 - 2 * δ))) := by
    unfold jS
    calc _ ≤ ∑ e ∈ F, 1 / (N * (1 - 2 * δ)) := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg (s := ((P.elems (y / Xm X₀)).filter
            fun e => (X₀ : ℝ) ≤ y / P.val e ∧ (1 - 2 * δ) * (y / P.val e) < X₀)) (t := F) ?_
            ?_).trans (Finset.sum_le_sum fun e he => ?_)
          · intro e he
            obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp he
            have hv := P.val_pos e
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · rw [mem_elems, hNdef, le_div_iff₀ hXp]
              rw [le_div_iff₀ hv] at h1; linarith
            · rw [hNdef]
              have : (1 - 2 * δ) * y < X₀ * P.val e := by
                rw [mul_div_assoc', div_lt_iff₀ hv] at h2; linarith
              rw [div_mul_eq_mul_div, div_lt_iff₀ hXp]; linarith
          · intro e _ _; exact div_nonneg zero_le_one (P.val_pos e).le
          · obtain ⟨-, he⟩ := Finset.mem_filter.mp he
            exact one_div_le_one_div_of_le hlow he.le
      _ = F.card * (1 / (N * (1 - 2 * δ))) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (F.card : ℝ) ≤ 4.01 * δ * N + 2 * Queue6.Hc X₀ N + 2 + N ^ (thetaB θ) := hJ
  -- numerics
  set H := Queue6.Hc X₀ N
  have hH3 : 3 ≤ H := by
    have hstd := (capH_conditions (Nat.cast_nonneg _) hc.hX hNX).2.1
    have hLN : 10 ^ 8 ≤ Real.log N := hc.hX.trans (Real.log_le_log hXp hNX)
    have hll : 1 ≤ Real.log (Real.log N) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have h1 := Real.add_one_le_exp (8 * Real.log (Real.log N) ^ 2)
    have : H = capH (X₀ : ℝ) N := by
      show Queue6.Hc X₀ N = _
      unfold Queue6.Hc; rw [max_eq_left hNX]
    rw [this]; nlinarith
  have hpow : N ^ (thetaB θ) = N ^ (thetaB θ - 1) * N := by
    rw [Real.rpow_sub hN0, Real.rpow_one, div_mul_cancel₀ _ hN0.ne']
  have hp0 : 0 < N ^ (thetaB θ - 1) := Real.rpow_pos_of_pos hN0 _
  have hinv : 1 / (N * (1 - 2 * δ)) ≤ (1 + 4 * δ) / N := by
    rw [div_le_div_iff₀ hlow hN0]
    have : 0 ≤ 2 * δ - 8 * δ ^ 2 := by nlinarith
    nlinarith [mul_nonneg hN0.le this]
  calc jS θ X₀ ω y δ ≤ F.card * (1 / (N * (1 - 2 * δ))) := hsum
    _ ≤ (4.01 * δ * N + 2 * H + 2 + N ^ (thetaB θ)) * ((1 + 4 * δ) / N) :=
        mul_le_mul hcard hinv (by positivity) (by positivity)
    _ ≤ 4.1 * δ + 3 * H / N + 2 * N ^ (thetaB θ - 1) := by
        rw [hpow]
        have e : (4.01 * δ * N + 2 * H + 2 + N ^ (thetaB θ - 1) * N) * ((1 + 4 * δ) / N) =
            4.01 * δ * (1 + 4 * δ) + (2 * H + 2) * (1 + 4 * δ) / N +
              N ^ (thetaB θ - 1) * (1 + 4 * δ) := by
          field_simp
          ring
        rw [e]
        have h1 : (2 * H + 2) * (1 + 4 * δ) / N ≤ 3 * H / N :=
          div_le_div_of_nonneg_right (by nlinarith) hN0.le
        nlinarith

end

end BModel

end
