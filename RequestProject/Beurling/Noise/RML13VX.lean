module

public import RequestProject.Beurling.Noise.MarginChain2
public import RequestProject.Beurling.Noise.RML6Var2Tail
public import RequestProject.Beurling.Noise.RML7Canon
public import RequestProject.Beurling.Noise.KptDefs

/-!
# Proposition 5.38, Step 5: the size of `V_{X₀}`

`V_{X₀}(t) = log t · j ∑_{|t/M − X₀| ≤ R₀} H_ord(M) M^{ε'−2}` (`Margin.Rec.VX`) at the canonical
parameters (`ε' = 0.045`, `R₀ = X₀ − 1.21 X₀⁻/2`). Every `M` in the sum has
`M ≥ L = t/(2X₀)`, `M ≤ 2t/X₀⁻ ≤ Z`, so `M^{−1.955} ≤ M^{−1.8} L^{−0.155}` and Lemma 5.21's
`∑ H_ord(M) M^{−1.8} ≤ 7.55` (`KR.hord18_set`) give, for `t ≥ X₀^{1.01}` and `j ≤ 1.0001/Λ`,

  `V_{X₀}(t) ≤ 7.56/Λ · log t · e^{−0.155 log t/102} ≤ 10⁻⁶`  (`VX_le`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace BModel.RML13

/-- **The size of `V_{X₀}`** (Proposition 5.38, Step 5): `V_{X₀}(t) ≤ 10⁻⁶` for
`X₀^{1.01} ≤ t`, `2t/X₀⁻ ≤ Z` (the (HBS) horizon), `0 ≤ j ≤ 1.0001/Λ`. -/
theorem VX_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {P : BeurlingSystem}
    {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} {εH ES jP : ℝ}
    (hbs : P.HBS (Xm X₀) Z η1 η2 ε1) (hXm : 100000000 ≤ Real.log (Xm X₀))
    (hXm1 : 0.99 * (X₀ : ℝ) ≤ Xm X₀)
    (hj0 : 0 ≤ jP) (hj : jP ≤ 1.0001 / Real.log X₀) {t : ℝ}
    (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) (htZ : 2 * t / Xm X₀ ≤ Z) :
    KR.Chain.VX P (RML7.canonP X₀ εH ES jP) t ≤ 1 / 10 ^ 6 := by
  set Λ := Real.log X₀ with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    rcases (Nat.cast_nonneg (α := ℝ) X₀).lt_or_eq with h | h
    · exact h
    · rw [hΛdef, ← h, Real.log_zero] at hX; linarith
  have hXm0 : 0 < Xm X₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set u := Real.log t with hudef
  have hu : 1.01 * Λ ≤ u := by
    have := Real.log_le_log (by positivity) ht
    rwa [Real.log_rpow hX0] at this
  set L := t / (2 * X₀) with hLdef
  have hL0 : 0 < L := by positivity
  have hlogL : u / 102 ≤ Real.log L := by
    rw [hLdef, Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) hX0.ne']
    have := Real.log_two_lt_d9
    nlinarith
  set p := RML7.canonP X₀ εH ES jP
  set F := (KR.NAll P t (p.Xm / 2)).filter
    (fun M => |t / Margin.Rec.Vv P M - p.X0| ≤ p.R0)
  have hmem : ∀ M ∈ F, L ≤ KR.Vl P M ∧ KR.Vl P M ≤ 2 * t / Xm X₀ ∧ 2 ≤ M := by
    intro M hM
    rw [Finset.mem_filter] at hM
    have hV := KR.Sharp.Vl_pos P M
    have hab := abs_le.mp hM.2
    simp only [p, RML7.canonP, Margin.Rec.Vv] at hab
    have h1 : t / KR.Vl P M ≤ 2 * X₀ := by linarith
    have h2 : 0.6 * Xm X₀ ≤ t / KR.Vl P M := by linarith
    have hLV : L ≤ KR.Vl P M := by
      rw [hLdef, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hV] at h1; linarith
    refine ⟨hLV, ?_, ?_⟩
    · rw [le_div_iff₀ hV] at h2
      rw [le_div_iff₀ hXm0]; nlinarith
    · have hn := ((KR.Sharp.mem_NAll_iff P (by simp only [p, RML7.canonP]; linarith)).mp
        hM.1).1
      by_contra hlt
      have h1M : M = 1 := by omega
      rw [h1M, KR.Sharp.Vl_one] at hLV
      have hXu : Real.log (2 * X₀) < u := by
        rw [Real.log_mul (by norm_num) hX0.ne']
        have := Real.log_two_lt_d9; linarith
      have : 2 * (X₀ : ℝ) < t := by
        rw [hudef] at hXu
        exact (Real.log_lt_log_iff (by positivity) ht0).mp hXu
      rw [hLdef, div_le_one (by positivity)] at hLV
      linarith
  have hexp : ∀ M ∈ F, Margin.Rec.Aw P p M ≤ (BSCert.X0Band.Hord M : ℝ) *
      LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ)) * Real.exp (-(0.155 / 102 * u)) := by
    intro M hM
    obtain ⟨hLV, -, -⟩ := hmem M hM
    have hV := KR.Sharp.Vl_pos P M
    unfold Margin.Rec.Aw
    simp only [p, RML7.canonP, Margin.Rec.Vv]
    rw [show (0.045 : ℝ) - 2 = -(1.8 : ℝ) + -(0.155 : ℝ) by norm_num, Real.rpow_add hV,
      ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Real.rpow_def_of_pos hV, Real.exp_le_exp]
    have := Real.log_le_log hL0 hLV
    nlinarith
  have hsum := KR.hord18_set P hbs hXm htZ F fun M hM => ⟨(hmem M hM).2.2, (hmem M hM).2.1⟩
  have hS : ∑ M ∈ F, Margin.Rec.Aw P p M ≤ 7.55 * Real.exp (-(0.155 / 102 * u)) := by
    refine (Finset.sum_le_sum hexp).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
  have hS0 : 0 ≤ ∑ M ∈ F, Margin.Rec.Aw P p M :=
    Finset.sum_nonneg fun M _ => by
      unfold Margin.Rec.Aw
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (KR.Sharp.Vl_pos P M).le _)
  have hu0 : 0 < u := by linarith
  have hme := KR.mul_exp_neg_le (c := 0.155 / 102) (by norm_num) hu0
  have hj' : p.j ≤ 1.0001 / Λ := hj
  have hpj : 0 ≤ p.j := hj0
  have h1 : KR.Chain.VX P p t ≤ u * (1.0001 / Λ * (7.55 * Real.exp (-(0.155 / 102 * u)))) := by
    unfold KR.Chain.VX
    exact mul_le_mul_of_nonneg_left (mul_le_mul hj' hS hS0 (by positivity)) hu0.le
  have h2 : u * (1.0001 / Λ * (7.55 * Real.exp (-(0.155 / 102 * u)))) =
      1.0001 * 7.55 / Λ * (u * Real.exp (-(0.155 / 102 * u))) := by
    field_simp
  have h3 : 2 / ((0.155 / 102) ^ 2 * u) ≤ 2 / ((0.155 / 102) ^ 2 * Λ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h4 : 1.0001 * 7.55 / Λ * (u * Real.exp (-(0.155 / 102 * u))) ≤
      1.0001 * 7.55 / Λ * (2 / ((0.155 / 102) ^ 2 * Λ)) :=
    mul_le_mul_of_nonneg_left (hme.trans h3) (by positivity)
  have h5 : 1.0001 * 7.55 / Λ * (2 / ((0.155 / 102) ^ 2 * Λ)) ≤ 1 / 10 ^ 6 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith
