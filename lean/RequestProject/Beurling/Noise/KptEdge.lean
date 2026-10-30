module

public import RequestProject.Beurling.Noise.KptDefs
public import RequestProject.Beurling.Noise.KRHord
public import RequestProject.Beurling.BaseRange.Margin

/-!
# The edge expansion (★) of Lemma 7.3(d)(i) for the realised resolvent

`ρ_edge := (1 + K_pt)⁻¹ μ_edge` (eq. (shdecomp)) is realised as `rhoEdge = R_sh μ_edge`
(`KR.Sharp.Rsh`). Lemma 7.3's named input `BaseRange.EdgeExpansion`,

  `ρ_edge(x) = ∑_{n ≤ x} μ(n)/n · μ_edge(x/n)`  (`X₀ ≤ x ≤ X₀^{1.9}`),

is proved here (`edgeExpansion`), as in the first display of the proof of (d)(i): if
`μ_edge(x/n) ≠ 0` then `x/n > 2X₀/(1+κ)`, so `n < x(1+κ)/(2X₀) ≤ X₀^{0.9} < X₀⁻`; such `n` are
rational integers (`valN_eq_nat`, from (HBS)), their primes are decided at most at their values,
every product in `χ^t_x(n)` is at most `n² < x`, so `c_n(x) = μ(n)` (Lemma 5.5).

Hypotheses: (HBS) on `[1, Z]` with `X₀ ≤ Z`, `X₀/2 ≤ X₀⁻ ≤ X₀`, `log X₀ ≥ 10⁸`, a positive
decision order with `t(p) ≤ p` for the primes `p < X₀⁻` (in the paper `t(p) = p` there).
-/

@[expose] public section

open Finset BeurlingSystem Real
open scoped ArithmeticFunction.Moebius

namespace KR.Sharp

variable (P : BeurlingSystem)

/-- The realised edge response `ρ_edge = (1 + K_pt)⁻¹ μ_edge`. -/
noncomputable def rhoEdge (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (x : ℝ) : ℝ :=
  Rsh P tw X0m (BaseRange.muEdge X0 (Construction.kappaParam X0)) x

/-- A rational integer `n < X₀⁻` (with `n ≤ Z`) has value `n`. -/
lemma valN_eq_nat {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {n : ℕ}
    (hn : n ≠ 0) (hX : (n : ℝ) < X0m) (hZ : (n : ℝ) ≤ Z) : Vl P n = n := by
  have hlab : ∀ r ∈ n.primeFactors, P.labelVal r = r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrn : (r : ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactors hr
    have := h.ident (x := (n : ℝ)) hX hZ (Nat.count Nat.Prime r)
      (Or.inr (by rw [exists_qp_eq hrp]; exact hrn))
    unfold labelVal
    rw [this, exists_qp_eq hrp]
  unfold Vl LemmaM.valN
  have e : (n.factorization.prod fun p k => P.labelVal p ^ k) =
      n.factorization.prod fun p k => ((p : ℝ) ^ k) := by
    apply Finsupp.prod_congr
    intro p hp
    rw [Nat.support_factorization] at hp
    rw [hlab p hp]
  rw [e]
  have := Nat.prod_factorization_pow_eq_self hn
  conv_rhs => rw [← this]
  simp only [Finsupp.prod]
  push_cast
  rfl

/-- `μ_edge(u) ≠ 0` forces `u > 2X₀/(1+κ)`. -/
lemma muEdge_eq_zero {X0 : ℕ} {κ u : ℝ} (hκ : 0 < κ) (hu : u ≤ 2 * X0 / (1 + κ)) :
    BaseRange.muEdge X0 κ u = 0 := by
  unfold BaseRange.muEdge
  refine Finset.sum_eq_zero fun N hN => ?_
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hN).1
  unfold BaseRange.edgeTerm
  rw [if_neg]
  rintro ⟨h1, -⟩
  have hN0 : (0 : ℝ) < N := by linarith
  rw [div_lt_div_iff₀ (by linarith) hN0] at h1
  rw [le_div_iff₀ (by linarith)] at hu
  nlinarith [Nat.cast_nonneg (α := ℝ) X0]

/-- **(★) for the realised resolvent** (the named input `EdgeExpansion` of Lemma 7.3). -/
theorem edgeExpansion {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0)
    (hZ : (X0 : ℝ) ≤ Z) {tw : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p) :
    BaseRange.EdgeExpansion X0 (rhoEdge P tw X0m X0) := by
  classical
  intro x hx1 hx2
  set κ := Construction.kappaParam X0
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := BaseRange.one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hXm0 : 0 < X0m := by linarith
  have hx0 : 0 < x := by linarith
  set B := x * (1 + κ) / (2 * X0) with hB
  -- sizes: `B ≤ X₀^{0.9} < X₀/2`, `B² ≤ x`, `B ≤ x/X₀⁻`, `B ≤ x`
  have hx19 : x ≤ (X0 : ℝ) ^ (2 : ℝ) := hx2.trans
    (Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num))
  have hX2 : (X0 : ℝ) ^ (2 : ℝ) = (X0 : ℝ) * X0 := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]; ring
  have h09 : (X0 : ℝ) ^ (1.9 : ℝ) = (X0 : ℝ) * (X0 : ℝ) ^ (0.9 : ℝ) := by
    rw [show (1.9 : ℝ) = 1 + 0.9 by norm_num, Real.rpow_add hX0, Real.rpow_one]
  have hsmall : (X0 : ℝ) ^ (0.9 : ℝ) * 4 < X0 := by
    have h01 : (4 : ℝ) < (X0 : ℝ) ^ (0.1 : ℝ) := by
      rw [← Real.exp_log hX0, ← Real.exp_mul]
      have : (4 : ℝ) < Real.exp 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      exact this.trans (Real.exp_lt_exp.mpr (by nlinarith))
    have hsplit : (X0 : ℝ) = (X0 : ℝ) ^ (0.9 : ℝ) * (X0 : ℝ) ^ (0.1 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have hp : 0 < (X0 : ℝ) ^ (0.9 : ℝ) := Real.rpow_pos_of_pos hX0 _
    nlinarith
  have hBX : B < X0m := by
    have : B ≤ (X0 : ℝ) ^ (0.9 : ℝ) := by
      rw [hB, div_le_iff₀ (by positivity)]
      have := hx2; rw [h09] at this
      nlinarith [Real.rpow_pos_of_pos hX0 (0.9 : ℝ)]
    nlinarith
  have hBsq : B * B ≤ x := by
    rw [hB]
    have : x * (1 + κ) * (x * (1 + κ)) ≤ x * (2 * X0 * (2 * X0)) := by
      have h4 : (1 + κ) * (1 + κ) ≤ 4 := by nlinarith
      rw [hX2] at hx19
      have hxx : 0 ≤ x * x := by positivity
      calc x * (1 + κ) * (x * (1 + κ)) = x * x * ((1 + κ) * (1 + κ)) := by ring
        _ ≤ x * x * 4 := mul_le_mul_of_nonneg_left h4 hxx
        _ = x * x * 4 := rfl
        _ ≤ x * ((X0 : ℝ) * X0) * 4 := by
            have := mul_le_mul_of_nonneg_left hx19 hx0.le; linarith
        _ = x * (2 * X0 * (2 * X0)) := by ring
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    linarith
  have hBx : B ≤ x := by
    rw [hB, div_le_iff₀ (by positivity)]
    have : 1 + κ ≤ 2 * X0 := by linarith
    exact mul_le_mul_of_nonneg_left this hx0.le
  have hBcut : B ≤ x / X0m := by
    rw [hB, div_le_div_iff₀ (by positivity) hXm0]
    have : (1 + κ) * X0m ≤ 2 * X0 := by nlinarith
    calc x * (1 + κ) * X0m = x * ((1 + κ) * X0m) := by ring
      _ ≤ x * (2 * X0) := mul_le_mul_of_nonneg_left this hx0.le
  -- the terms with `n ≥ B` vanish on both sides
  have hzero : ∀ v : ℝ, 0 < v → B ≤ v → BaseRange.muEdge X0 κ (x / v) = 0 := by
    intro v hv hBv
    apply muEdge_eq_zero hκ0
    rw [div_le_div_iff₀ hv (by linarith)]
    rw [hB, div_le_iff₀ (by positivity)] at hBv
    nlinarith
  set S := (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) < B)
  have hS_Icc : S ⊆ Finset.Icc 1 ⌊x⌋₊ := Finset.filter_subset _ _
  have hS_mem : ∀ n ∈ S, n ≠ 0 ∧ Vl P n = n ∧ (n : ℝ) < B := by
    intro n hn
    obtain ⟨hn1, hnB⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn1).1; omega
    exact ⟨hn0, valN_eq_nat P h hn0 (hnB.trans hBX) (by linarith [hnB.trans hBX]), hnB⟩
  have hS_A : S ⊆ NAll P x X0m := by
    intro n hn
    obtain ⟨hn0, hVn, hnB⟩ := hS_mem n hn
    rw [mem_NAll_iff P hXm0, hVn]; exact ⟨hn0, by linarith⟩
  -- the left side
  unfold rhoEdge
  rw [Rsh_eq_moebius P ht hXm0 (by linarith)]
  rw [← Finset.sum_subset hS_A]
  · rw [← Finset.sum_subset hS_Icc]
    · refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hn0, hVn, hnB⟩ := hS_mem n hn
      rw [hVn]
      by_cases hsq : Squarefree n
      · have hchi : LemmaM.chi tw P.labelVal x n := by
          refine ⟨hsq, fun p hp => ?_⟩
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hlp : P.labelVal p ≤ Vl P n := by
            unfold Vl
            rw [← KR.valN_prime P.labelVal hpp]
            exact KR.valN_dvd_le P (Nat.dvd_of_mem_primeFactors hp) hn0
          have htp : tw p ≤ n := by
            rw [← hVn]; exact (hdec p hpp (by linarith)).trans hlp
          have hvs : LemmaM.valS P.labelVal (n.primeFactors.filter
              fun q => LemmaM.rk tw p ≤ LemmaM.rk tw q) ≤ n := by
            rw [← hVn]
            unfold Vl
            rw [LemmaM.valN_of_squarefree _ hsq]
            exact LemmaM.valS_mono _ (fun r _ => P.one_le_labelVal r)
              (Finset.filter_subset _ _)
          have hvs0 : 0 ≤ LemmaM.valS P.labelVal (n.primeFactors.filter
              fun q => LemmaM.rk tw p ≤ LemmaM.rk tw q) :=
            LemmaM.valS_nonneg _ (fun r _ => P.one_le_labelVal r)
          have htp0 := (ht p hpp).le
          have hn0' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          calc tw p * _ ≤ (n : ℝ) * n := mul_le_mul htp hvs hvs0 hn0'
            _ < B * B := mul_self_lt_mul_self hn0' hnB
            _ ≤ x := hBsq
        rw [if_pos hchi]; ring
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
    · intro n hn hnS
      have hn1 := Finset.mem_Icc.mp hn
      have : ¬ (n : ℝ) < B := fun hlt => hnS (Finset.mem_filter.mpr ⟨hn, hlt⟩)
      push_neg at this
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1.1
      rw [hzero n hnpos this]; ring
  · intro n hnA hnS
    have hn0 := ((mem_NAll_iff P hXm0).mp hnA).1
    by_cases hVB : Vl P n < B
    · exfalso
      have hVX : Vl P n < X0m := hVB.trans hBX
      have hVn : Vl P n = n := KR.valN_eq_self P h hn0 hVX (by unfold Vl at hVX; linarith)
      rw [hVn] at hVB
      exact hnS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_floor (by linarith)⟩, hVB⟩)
    · push_neg at hVB
      rw [hzero _ (Vl_pos P n) hVB]; ring

end KR.Sharp

end
