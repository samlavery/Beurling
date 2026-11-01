module

public import RequestProject.Beurling.BaseRange.EdgeNum

/-!
# Lemma 7.3(d)(i),(ii): the edge term at `X₀`

§7.2 defines the edge source (the part of `K_ℚ MA[ℙ]` below `X₀`)

  `μ_edge(u) = ∑_{N ≥ 2} N⁻¹ MA_{κq}[rational primes ≥ max(P⁺(N), X₀)](q)|_{q = u/N}
      · 1[u/N ∈ (X₀/(1+κ), X₀)]`,

and `ρ_edge = (1 + K_pt)⁻¹ μ_edge`. In the proof of (d)(i), for `X₀ ≤ x ≤ X₀^{1.9}` every
cofactor `n` with `μ_edge(x/n) ≠ 0` is a rational integer `< X₀⁻`, decided before `X₀`, and
Lemma M (Lemma 5.5) gives the coefficient `c_n(x) = μ(n)`; so

  `ρ_edge(x) = ∑_n μ(n)/n · μ_edge(x/n)`.                                  (★)

* `muEdge` : `μ_edge`; `MAPfrom`, `Pplus` : the window density of the primes `≥ T`, and `P⁺`;
* `edge_identity` : **(d)(i)**, the arithmetic: the right side of (★) equals
  `-∑_{N ≥ 2} μ(N) MA[ℙ](x/N)/N · 1[x/N ∈ (X₀/(1+κ), X₀)]`, whenever every such `N` is `< X₀`
  (true for `x ≤ X₀^{1.9}`, `edge_N_lt`), because `∑_{d ∣ N, d < N} μ(d) = -μ(N)`;
* `edge_ii` : **(d)(ii)**: from the formula of (d)(i), for `X₀ ≤ x ≤ X₀^{1.01}`,
  `ρ_edge(x) log x ≥ -0.167` (at most one `N` occurs, a negative term needs `μ(N) = 1`, so
  `N ≥ 6`, and `MA[ℙ] ≤ 1.0001/Λ` on the partial windows);
* `EdgeExpansion` : the expansion (★) of `ρ_edge`, stated as a named hypothesis (it is Lemma M
  applied to the realised resolvent, whose operator `K_pt` is not formalized in this
  repository); `lemma_7_3_d_i`, `lemma_7_3_d_ii` : (d)(i),(ii) from it.
-/

@[expose] public section

open Real Finset
open scoped ArithmeticFunction.Moebius

namespace BaseRange

/-- `P⁺(m)`, the largest prime factor (`0` for `m = 1`). -/
def Pplus (m : ℕ) : ℕ := m.primeFactors.sup id

lemma Pplus_le {m : ℕ} (hm : 1 ≤ m) : Pplus m ≤ m := by
  unfold Pplus
  apply Finset.sup_le
  intro p hp
  exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)

/-- The window density of the rational primes `≥ T` at `q`. -/
noncomputable def MAPfrom (T : ℕ) (κ q : ℝ) : ℝ := newPrimeCount T q ((1 + κ) * q) / (κ * q)

lemma MAPfrom_X0 (X0 : ℕ) (κ q : ℝ) : MAPfrom X0 κ q = MAP X0 κ q := rfl

/-- The edge window `(X₀/(1+κ), X₀)`. -/
def InEdge (X0 : ℕ) (κ u : ℝ) : Prop := (X0 : ℝ) / (1 + κ) < u ∧ u < X0

open Classical in
/-- The summand of `μ_edge` at the cofactor `N`. -/
noncomputable def edgeTerm (X0 : ℕ) (κ u : ℝ) (N : ℕ) : ℝ :=
  if InEdge X0 κ (u / N) then MAPfrom (max X0 (Pplus N)) κ (u / N) / N else 0

/-- `μ_edge(u)`, the part of `K_ℚ MA[ℙ]` below `X₀` (§7.2). -/
noncomputable def muEdge (X0 : ℕ) (κ u : ℝ) : ℝ :=
  ∑ N ∈ Icc 2 ⌊u⌋₊, edgeTerm X0 κ u N

open Classical in
/-- The right side of (d)(i): `-∑_{N ≥ 2} μ(N) MA[ℙ](x/N)/N · 1[x/N ∈ (X₀/(1+κ), X₀)]`. -/
noncomputable def edgeFormula (X0 : ℕ) (κ x : ℝ) : ℝ :=
  -∑ N ∈ Icc 2 ⌊x⌋₊, if InEdge X0 κ (x / N) then (μ N : ℝ) * MAP X0 κ (x / N) / N else 0

/-! ### The Möbius sum over proper divisors -/

lemma sum_properDivisors_moebius {N : ℕ} (hN : 2 ≤ N) :
    ∑ d ∈ N.properDivisors, (μ d : ℝ) = -(μ N : ℝ) := by
  have h1 : ∑ d ∈ N.divisors, (μ d : ℤ) = 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f N)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply] at this
    rw [this, ArithmeticFunction.one_apply_ne (by omega)]
  have h2 : ∑ d ∈ N.divisors, (μ d : ℝ) = 0 := by exact_mod_cast h1
  rw [← Nat.insert_self_properDivisors (by omega), Finset.sum_insert
    Nat.self_notMem_properDivisors] at h2
  linarith

/-! ### (d)(i): the identity -/

/-- **Lemma 7.3(d)(i)**, the arithmetic identity: if every `N ≤ x` with
`x/N ∈ (X₀/(1+κ), X₀)` is `< X₀`, then `∑_{n ≤ x} μ(n)/n · μ_edge(x/n)` equals the formula of
(d)(i). -/
theorem edge_identity {X0 : ℕ} {κ x : ℝ}
    (hN : ∀ N : ℕ, 1 ≤ N → InEdge X0 κ (x / N) → N < X0) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * muEdge X0 κ (x / n) = edgeFormula X0 κ x := by
  classical
  set X := ⌊x⌋₊ with hX
  set s := (Icc 1 X ×ˢ Icc 2 X).filter fun p : ℕ × ℕ => p.1 * p.2 ≤ X with hs
  set F : ℕ × ℕ → ℝ := fun p => (μ p.1 : ℝ) / p.1 * edgeTerm X0 κ (x / p.1) p.2 with hF
  -- step 1: the double sum over the pairs `(n, M)` with `nM ≤ x`
  have h1 : ∑ n ∈ Icc 1 X, (μ n : ℝ) / n * muEdge X0 κ (x / n) = ∑ p ∈ s, F p := by
    rw [hs, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    unfold muEdge
    rw [Finset.mul_sum]
    have hfl : ⌊x / n⌋₊ = X / n := by rw [hX]; exact Nat.floor_div_natCast x n
    rw [hfl]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext M
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨h2, hM⟩
        refine ⟨⟨h2, hM.trans (Nat.div_le_self _ _)⟩, ?_⟩
        calc n * M ≤ n * (X / n) := Nat.mul_le_mul_left _ hM
          _ ≤ X := Nat.mul_div_le X n
      · rintro ⟨⟨h2, -⟩, hM⟩
        refine ⟨h2, ?_⟩
        rw [Nat.le_div_iff_mul_le (by omega)]; linarith [mul_comm n M]
    · intro M _; rfl
  -- step 2: group by `N = nM`
  have h2 : ∑ p ∈ s, F p = ∑ N ∈ Icc 2 X, ∑ p ∈ s.filter (fun p => p.1 * p.2 = N), F p := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro p hp
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Icc]
    constructor
    · nlinarith [hp.1.1.1, hp.1.2.1]
    · exact hp.2
  -- step 3: each fibre
  have h3 : ∀ N ∈ Icc 2 X, ∑ p ∈ s.filter (fun p => p.1 * p.2 = N), F p =
      -(if InEdge X0 κ (x / N) then (μ N : ℝ) * MAP X0 κ (x / N) / N else 0) := by
    intro N hNmem
    have hN2 : 2 ≤ N := (Finset.mem_Icc.mp hNmem).1
    have hNX : N ≤ X := (Finset.mem_Icc.mp hNmem).2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    -- the fibre is `{(d, N/d) : d ∣ N, d < N}`
    have hfib : ∑ p ∈ s.filter (fun p => p.1 * p.2 = N), F p =
        ∑ d ∈ N.properDivisors, F (d, N / d) := by
      have hmem : ∀ p : ℕ × ℕ, p ∈ s.filter (fun p => p.1 * p.2 = N) ↔
          (1 ≤ p.1 ∧ p.1 ≤ X) ∧ (2 ≤ p.2 ∧ p.2 ≤ X) ∧ p.1 * p.2 = N := by
        intro p
        simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1.1, h1.2, h2⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, h2⟩, by omega⟩, h3⟩
      have hp2 : ∀ p ∈ s.filter (fun p => p.1 * p.2 = N), p.2 = N / p.1 := by
        intro p hp
        obtain ⟨h1, -, h3⟩ := (hmem p).mp hp
        rw [← h3, Nat.mul_div_cancel_left _ (by omega)]
      apply Finset.sum_nbij' (fun p => p.1) (fun d => (d, N / d))
      · intro p hp
        obtain ⟨h1, h2, h3⟩ := (hmem p).mp hp
        simp only [Nat.mem_properDivisors]
        refine ⟨⟨p.2, h3.symm⟩, ?_⟩
        nlinarith [h1.1, h2.1]
      · intro d hd
        simp only [Nat.mem_properDivisors] at hd
        rw [hmem]
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
        have hdN : d * (N / d) = N := Nat.mul_div_cancel' hd.1
        have hq2 : 2 ≤ N / d := by
          by_contra hc; push_neg at hc
          have h1 : N / d ≤ 1 := by omega
          have h2 : d * (N / d) ≤ d * 1 := Nat.mul_le_mul_left d h1
          omega
        exact ⟨⟨hd0, by omega⟩, ⟨hq2, (Nat.div_le_self _ _).trans hNX⟩, hdN⟩
      · intro p hp
        have := hp2 p hp
        ext
        · rfl
        · exact this.symm
      · intro d _; rfl
      · intro p hp
        rw [← hp2 p hp]
    rw [hfib]
    -- each term: `μ(d)/N · MA[ℙ](x/N) · 1[x/N ∈ W]`
    have hterm : ∀ d ∈ N.properDivisors, F (d, N / d) =
        (μ d : ℝ) * (if InEdge X0 κ (x / N) then MAP X0 κ (x / N) / N else 0) := by
      intro d hd
      have hd' := Nat.mem_properDivisors.mp hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
      have hdN : d * (N / d) = N := Nat.mul_div_cancel' hd'.1
      have hq0 : 0 < N / d := by
        rcases Nat.eq_zero_or_pos (N / d) with h | h
        · rw [h] at hdN; omega
        · exact h
      have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
      have hqr : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast hq0
      have hNr : ((N / d : ℕ) : ℝ) * d = N := by exact_mod_cast (by rw [mul_comm]; exact hdN)
      have hxx : x / d / ((N / d : ℕ) : ℝ) = x / N := by
        rw [div_div, mul_comm, hNr]
      simp only [hF, edgeTerm]
      rw [hxx]
      by_cases hW : InEdge X0 κ (x / N)
      · rw [if_pos hW, if_pos hW]
        have hNlt := hN N (by omega) hW
        have hmax : max X0 (Pplus (N / d)) = X0 := by
          apply max_eq_left
          have := Pplus_le (by omega : 1 ≤ N / d)
          have : N / d ≤ N := Nat.div_le_self _ _
          omega
        rw [hmax, MAPfrom_X0]
        field_simp
        rw [← hNr]
        ring
      · rw [if_neg hW, if_neg hW]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_properDivisors_moebius hN2]
    by_cases hW : InEdge X0 κ (x / N)
    · rw [if_pos hW, if_pos hW]; ring
    · rw [if_neg hW, if_neg hW]; ring
  rw [h1, h2, Finset.sum_congr rfl h3, Finset.sum_neg_distrib]
  rfl

/-- For `x ≤ X₀^{1.9}`, every `N` with `x/N ∈ (X₀/(1+κ), X₀)` is `< X₀`. -/
lemma edge_N_lt {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (X0 : ℝ) ^ (1.9 : ℝ)) (N : ℕ) (hN : 1 ≤ N)
    (hW : InEdge X0 (Construction.kappaParam X0) (x / N)) : N < X0 := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hW.1
  rw [div_lt_div_iff₀ (by linarith) hN0] at h1
  -- `N < (1+κ) x/X₀ ≤ 2 X₀^{0.9} < X₀`
  have h2 : (N : ℝ) < 2 * (X0 : ℝ) ^ (1.9 : ℝ) / X0 := by
    rw [lt_div_iff₀ hX0]; nlinarith
  have h3 : 2 * (X0 : ℝ) ^ (1.9 : ℝ) / X0 < X0 := by
    rw [div_lt_iff₀ hX0, rpow_eq_exp hX0]
    have e : (X0 : ℝ) * X0 = Real.exp (2 * Real.log X0) := by
      rw [← Real.exp_log hX0, ← Real.exp_add, Real.log_exp]; ring_nf
    rw [e]
    have hsplit : Real.exp (2 * Real.log X0) =
        Real.exp (1.9 * Real.log X0) * Real.exp (0.1 * Real.log X0) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have h2' : (2 : ℝ) < Real.exp (0.1 * Real.log X0) := by
      have := Real.add_one_le_exp (0.1 * Real.log X0); nlinarith
    have := Real.exp_pos (1.9 * Real.log X0)
    nlinarith
  have : (N : ℝ) < X0 := by linarith
  exact_mod_cast this

/-! ### (d)(ii) -/

/-- **Lemma 7.3(d)(ii)**: for `X₀ ≤ x ≤ X₀^{1.01}` the formula of (d)(i) satisfies
`(formula) · log x ≥ -0.167`. -/
theorem edge_ii {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {x : ℝ}
    (hx1 : (X0 : ℝ) ≤ x) (hx : x ≤ (X0 : ℝ) ^ (1.01 : ℝ)) :
    -0.167 ≤ edgeFormula X0 (Construction.kappaParam X0) x * Real.log x := by
  classical
  set κ := Construction.kappaParam X0
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hL : 10 ^ 8 ≤ Real.log x := log_ge_of_ge hX hx1
  set T : ℕ → ℝ := fun N => if InEdge X0 κ (x / N) then (μ N : ℝ) * MAP X0 κ (x / N) / N else 0
  by_cases hex : ∃ N0 ∈ Icc 2 ⌊x⌋₊, InEdge X0 κ (x / N0)
  · obtain ⟨N0, hN0mem, hW0⟩ := hex
    have hN02 : 2 ≤ N0 := (Finset.mem_Icc.mp hN0mem).1
    have hsum : ∑ N ∈ Icc 2 ⌊x⌋₊, T N = T N0 := by
      apply Finset.sum_eq_single_of_mem _ hN0mem
      intro N hN hne
      simp only [T]
      rw [if_neg]
      intro hW
      exact hne (edge_N_unique hX hx1 hx (by have := (Finset.mem_Icc.mp hN).1; omega)
        (by omega) hW hW0)
    unfold edgeFormula
    rw [show (∑ N ∈ Icc 2 ⌊x⌋₊, if InEdge X0 κ (x / N) then (μ N : ℝ) * MAP X0 κ (x / N) / N
      else 0) = ∑ N ∈ Icc 2 ⌊x⌋₊, T N from rfl, hsum]
    simp only [T, if_pos hW0]
    have hN0r : (0 : ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
    have hq0 : 0 < x / N0 := div_pos hx0 hN0r
    have hMA0 : 0 ≤ MAP X0 κ (x / N0) := MAP_nonneg X0 hκ0.le hq0.le
    have hlx0 : 0 ≤ Real.log x := by linarith
    -- the sign of `μ(N₀)`
    have hμ : μ N0 = 1 ∨ μ N0 ≤ 0 := by
      rcases ArithmeticFunction.abs_moebius_le_one (n := N0) |> abs_le.mp with ⟨h1, h2⟩
      omega
    rcases hμ with hμ1 | hμ0
    · have h6 := six_le_of_moebius_eq_one hN02 hμ1
      have hMA := MAP_le_edge hX hH hW0.1 hW0.2
      have hlog : Real.log x ≤ Real.log N0 + Real.log X0 := by
        rw [← Real.log_mul hN0r.ne' hX0.ne']
        apply Real.log_le_log hx0
        have := hW0.2; rw [div_lt_iff₀ hN0r] at this; linarith
      have := edge_ii_term h6 hX hMA hlx0 hlog
      rw [hμ1]; push_cast
      have e : -(1 * MAP X0 κ (x / N0) / N0) * Real.log x =
          -(MAP X0 κ (x / N0) / N0 * Real.log x) := by ring
      rw [e]; exact this
    · have : ((μ N0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hμ0
      have h : 0 ≤ -((μ N0 : ℝ) * MAP X0 κ (x / N0) / N0) * Real.log x := by
        apply mul_nonneg _ hlx0
        rw [neg_nonneg]
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg this hMA0)
          hN0r.le
      linarith
  · push_neg at hex
    unfold edgeFormula
    rw [Finset.sum_eq_zero fun N hN => if_neg (hex N hN)]
    norm_num

/-! ### `ρ_edge` from the expansion (★) -/

/-- **The expansion (★) of `ρ_edge`** used in the proof of Lemma 7.3(d)(i): for
`X₀ ≤ x ≤ X₀^{1.9}`, `ρ_edge(x) = ∑_n μ(n)/n · μ_edge(x/n)`. In the paper this is Lemma M
(Lemma 5.5; formalized as `LemmaM.lemma_M`) applied to the realised resolvent
`(1 + K_pt)⁻¹`: the cofactors are rational integers `< X₀⁻`, decided at their values, so
`c_n(x) = μ(n)`. The realised operator `K_pt` is not formalized in this repository, so the
expansion is a named hypothesis on the function `ρ_edge`. -/
def EdgeExpansion (X0 : ℕ) (ρedge : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, (X0 : ℝ) ≤ x → x ≤ (X0 : ℝ) ^ (1.9 : ℝ) →
    ρedge x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * muEdge X0 (Construction.kappaParam X0) (x / n)

/-- **Lemma 7.3(d)(i)**: for `X₀ ≤ x ≤ X₀^{1.9}`,
`ρ_edge(x) = -∑_{N ≥ 2: x/N ∈ (X₀/(1+κ), X₀)} μ(N) MA[ℙ](x/N)/N`. -/
theorem lemma_7_3_d_i {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {ρedge : ℝ → ℝ}
    (hρ : EdgeExpansion X0 ρedge) {x : ℝ} (hx1 : (X0 : ℝ) ≤ x)
    (hx : x ≤ (X0 : ℝ) ^ (1.9 : ℝ)) :
    ρedge x = edgeFormula X0 (Construction.kappaParam X0) x := by
  have hx0 : 0 < x := by linarith [one_lt_of_log hX]
  rw [hρ x hx1 hx]
  exact edge_identity (edge_N_lt hX hx0 hx)

/-- **Lemma 7.3(d)(ii)**: for `X₀ ≤ x ≤ X₀^{1.01}`, `ρ_edge(x) log x ≥ -0.167`. -/
theorem lemma_7_3_d_ii {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0)
    {ρedge : ℝ → ℝ} (hρ : EdgeExpansion X0 ρedge) {x : ℝ} (hx1 : (X0 : ℝ) ≤ x)
    (hx : x ≤ (X0 : ℝ) ^ (1.01 : ℝ)) : -0.167 ≤ ρedge x * Real.log x := by
  have hX1 := one_lt_of_log hX
  have h19 : (X0 : ℝ) ^ (1.01 : ℝ) ≤ (X0 : ℝ) ^ (1.9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
  rw [lemma_7_3_d_i hX hρ hx1 (hx.trans h19)]
  exact edge_ii hX hH hx1 hx

end BaseRange
