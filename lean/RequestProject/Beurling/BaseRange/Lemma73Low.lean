module

public import RequestProject.Beurling.BaseRange.Lemma73R

/-!
# Lemma 7.3's inputs with the horizon `X₀⁻` (the windows `b < 4X₀ + 2`)

`lemma73Inputs_R'` : `lemma73Inputs_R` with the horizon hypothesis `X₀ ≤ Z` weakened to
`X₀⁻ ≤ Z` (with `x_max/X₀⁻ ≤ Z`). The only use of `X₀ ≤ Z` was in the edge expansion, which reads
`𝒩` at integers `< X₀⁻`; `edgeExpansion'` is that proof with `X₀⁻ ≤ Z`.
-/

@[expose] public section

open Finset BeurlingSystem Real
open scoped ArithmeticFunction.Moebius

namespace KR.Sharp

variable (P : BeurlingSystem)

/-- **(★) for the realised resolvent**, as `edgeExpansion` (Noise/KptEdge) with the horizon
hypothesis `X₀⁻ ≤ Z` in place of `X₀ ≤ Z` (only integers `< X₀⁻` are read). -/
theorem edgeExpansion' {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0)
    (hZ : X0m ≤ Z) {tw : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < tw p)
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

namespace BaseRange

open Construction BModel CaplLink

/-- **`lemma73Inputs_complete` with the horizon `X₀⁻ ≤ Z`** (no `X₀ ≤ Z`). -/
theorem lemma73Inputs_complete' {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : X0m ≤ Z) {tw : ℕ → ℝ}
    (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p) {xmax : ℝ} (hZ : xmax / X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (H : ℝ → ℝ)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    {ηH : ℝ} (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη0 : 0 ≤ ηH)
    (hηκ : ηH ≤ Construction.kappaParam X0) :
    Lemma73Inputs X0 xmax (mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) := by
  have hXm0 : 0 < X0m := lt_of_lt_of_le (by norm_num) h.X0m_ge
  have hZ0 : xmax / X0 ≤ Z := by
    rcases le_or_gt 0 xmax with hx | hx
    · exact le_trans (div_le_div_of_nonneg_left hx hXm0 hXm2) hZ
    · have h1 : xmax / X0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le (Nat.cast_nonneg _)
      linarith
  exact ⟨lemma73b_of P hX hH hXp
      (lemma73bCore_of h hX hXm1 hXm2 hZ0 hXZ hloc H hdhi hdlo hlip hsmall hcount hrat hη0 hηκ),
    KR.Sharp.lemma73c_of P hX hH (kptF1Bound P h hX hH hXm1 hXm2 hdec2 hZ0) (kshQF1Second hX hH),
    KR.Sharp.edgeExpansion' P h hX hXm1 hXm2 hXZ ht hdec,
    lemma73diii_full h hX hH hXm1 hXm2 hZ hXZ ht hloc H hdhi hdlo hlip hsmall hcount hrat hη0
      hηκ⟩

/-- `lemma73Inputs_tnp` with the horizon `X₀⁻ ≤ Z`. -/
theorem lemma73Inputs_tnp' {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ}
    {X0m Z η1 η2 ε θ' : ℝ} {ε1 : ℝ → ℝ} (hT : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ')
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : X0m ≤ Z)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    {xmax : ℝ} (hZ : xmax / X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (hηκ : H (X0m / 2) / (X0m / 2) ≤ Construction.kappaParam X0) :
    Lemma73Inputs X0 xmax (mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) := by
  have hW := hT.width
  have hX0m := hW.X0m_pos
  obtain ⟨ht, hdec2⟩ := tnp_dec hT
  refine lemma73Inputs_complete' hT.hbs hX hH hXp hXm1 hXm2 hXZ ht hdec hdec2 hZ hloc H
    hT.dec_hi hT.dec_lo ?_ hW.small hT.count (fun s hs => ratio_of_RH hW hs)
    (div_nonneg (hW.reg.pos _).le (by linarith)) hηκ
  intro y z hy hz
  have := hW.lip y z hy hz
  have h0 := abs_nonneg (y - z)
  have : θ' * |y - z| ≤ 1 / 100 * |y - z| := mul_le_mul_of_nonneg_right hW.theta_le h0
  linarith

variable {θ : ℝ} {X₀ : ℕ}

/-- **`lemma73Inputs_R` with the horizon `x_max/X₀⁻ ≤ Z` only** (no `X₀ ≤ Z`): this covers the
windows `b < 4X₀ + 2`, where the horizon of `Good(< b)` is `Zc b = X₀⁻`. -/
theorem lemma73Inputs_R' (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    {Z η1 η2 ε : ℝ} {ε1 : ℝ → ℝ} (hbs : (Queue6.PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : KR.WidthReal.CapHSlope X₀ ε)
    (hD : KR.WidthReal.CapHDiff X₀) (hH : HuxleyFrom X₀) (hXZ : Xm X₀ ≤ Z) {xmax : ℝ}
    (hZ : xmax / Xm X₀ ≤ Z)
    (hloc : ∀ v, Xm X₀ ≤ v → v ≤ Z →
      |(Queue6.PR θ X₀ ω).N v - ⌊v⌋₊| ≤ Construction.hbsEps X₀ v * v) :
    Lemma73Inputs X₀ xmax
      (mu0R (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀)
      (KR.Sharp.mu1R (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hX
  have hXp : ¬ X₀.Prime := by
    intro hp
    have h2 : X₀ = 2 := (Nat.Prime.even_iff hp).mp hev
    have : (3 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀); rw [Real.exp_log hX0] at this; linarith
    rw [h2] at this; norm_num at this
  have hT := Queue6.tnpHyp_R hc hev hSG hX1 hbs
    (KR.WidthReal.paperWidth_Hc hX hε0 hε hS hD)
  obtain ⟨h1, h2⟩ := Xm_facts hc
  exact lemma73Inputs_tnp' hT hX hH hXp h1 h2 hXZ (twR_le_labelVal hc ω) hZ hloc
    (Hc_Xm_half_le_kappa hc)

end BaseRange
