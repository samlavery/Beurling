module

public import RequestProject.Beurling.BaseRange.GEdgeNT

/-!
# Lemma 7.3(d)(iii): the bound on `g = (1 + K'_ℚ)⁻¹ μ_edge`

`gEdge_bound` : **`|g(x)| ≤ (1.0001/Λ)(κ + X₀/x)` for `x ≥ X₀`** (`GEdgeBound`), from:

* `gEdge_eq` : `g(x) = ∑_{n ≤ x} c_n(x)/n · μ_edge(x/n)` with the Lemma M coefficients of the
  rational system;
* `regroup` : the double sum regrouped by `N = n M` (as in (d)(i));
* `coeff_window_le` : the coefficient of each window prime is `≤ 1` in absolute value, so each
  `N`-term is at most `MA[ℙ](x/N)/N ≤ 1.0001/(NΛ)` (`MAP_le_edge`, from (huxley));
* `∑_{x/X₀ < N < (1+κ)x/X₀} 1/N ≤ κ + X₀/x`.
-/

@[expose] public section

open Real Finset BeurlingSystem
open scoped ArithmeticFunction.Moebius

namespace BaseRange

lemma valN_lv {n : ℕ} (hn : n ≠ 0) : LemmaM.valN lv n = n := by
  unfold LemmaM.valN
  rw [Finsupp.prod_congr (g2 := fun p k => ((p ^ k : ℕ) : ℝ)) (fun p hp => by
    rw [lv_prime (Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp))]
    push_cast; rfl)]
  have := Nat.factorization_prod_pow_eq_self hn
  unfold Finsupp.prod at this ⊢
  rw [← Nat.cast_prod, this]

lemma Vl_ratSys {n : ℕ} (hn : n ≠ 0) : KR.Vl ratSys n = n := valN_lv hn

/-- The Lemma M coefficient of the rational system. -/
noncomputable def cQ (X0 : ℕ) (x : ℝ) (n : ℕ) : ℝ := (LemmaM.coeff tQ lv X0 x n : ℝ)

lemma tQ_pos : ∀ p, p.Prime → 0 < tQ p := fun p hp => by
  unfold tQ; exact_mod_cast hp.pos

open Classical in
lemma cQ_eq {X0 : ℕ} {x : ℝ} (hx : (X0 : ℝ) ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    cQ X0 x n = (μ n : ℝ) * (if LemmaM.chi tQ lv x n then 1 else 0) *
      (if (X0 : ℝ) ≤ x / n then 1 else 0) := by
  unfold cQ
  rw [LemmaM.lemma_M tQ lv tQ_pos (fun r _ => ratSys.one_le_labelVal r) (Nat.cast_nonneg _) hx hn,
    valN_lv (by omega)]
  push_cast
  split_ifs <;> simp

/-- `g(x) = ∑_{n ≤ x} c_n(x)/n · μ_edge(x/n)`. -/
lemma gEdge_eq {X0 : ℕ} (hX : 1 < (X0 : ℝ)) {x : ℝ} (hx : (X0 : ℝ) ≤ x) :
    gEdge X0 x = ∑ n ∈ Icc 1 ⌊x⌋₊, cQ X0 x n / n *
      muEdge X0 (Construction.kappaParam X0) (x / n) := by
  classical
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hx0 : 0 < x := by linarith
  unfold gEdge KR.Sharp.Rsh
  have hN : KR.NAll ratSys x X0 = Icc 1 ⌊x / X0⌋₊ := by
    ext n
    rw [KR.Sharp.mem_NAll_iff ratSys hX0, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Vl_ratSys h1] at h2
      exact ⟨Nat.one_le_iff_ne_zero.mpr h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rw [Vl_ratSys (by omega)]
      exact (Nat.le_floor_iff (by positivity)).mp h2
  rw [hN]
  have hsub : Icc 1 ⌊x / X0⌋₊ ⊆ Icc 1 ⌊x⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    exact Nat.floor_le_floor (div_le_self hx0.le hX.le)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Vl_ratSys (by omega)]
    unfold cQ
    ring
  · intro n hn hn'
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hlt : ¬ (X0 : ℝ) ≤ x / n := by
      intro h
      apply hn'
      refine Finset.mem_Icc.mpr ⟨hn1, Nat.le_floor ?_⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [le_div_iff₀ hn0] at h
      rw [le_div_iff₀ hX0]; linarith
    rw [cQ_eq hx hn1, if_neg hlt]
    ring

/-- **The regrouping by `N = n M`** (as in (d)(i), with arbitrary coefficients). -/
lemma regroup (a : ℕ → ℝ) (X0 : ℕ) (κ x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, a n * muEdge X0 κ (x / n) =
      ∑ N ∈ Icc 2 ⌊x⌋₊, ∑ d ∈ N.properDivisors, a d * edgeTerm X0 κ (x / d) (N / d) := by
  classical
  set X := ⌊x⌋₊ with hX
  set s := (Icc 1 X ×ˢ Icc 2 X).filter fun p : ℕ × ℕ => p.1 * p.2 ≤ X with hs
  set F : ℕ × ℕ → ℝ := fun p => a p.1 * edgeTerm X0 κ (x / p.1) p.2 with hF
  have h1 : ∑ n ∈ Icc 1 X, a n * muEdge X0 κ (x / n) = ∑ p ∈ s, F p := by
    rw [hs, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    unfold muEdge
    rw [Finset.mul_sum]
    have hfl : ⌊x / n⌋₊ = X / n := by rw [hX]; exact Nat.floor_div_natCast x n
    rw [hfl, ← Finset.sum_filter]
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
  have h2 : ∑ p ∈ s, F p = ∑ N ∈ Icc 2 X, ∑ p ∈ s.filter (fun p => p.1 * p.2 = N), F p := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro p hp
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Icc]
    constructor
    · nlinarith [hp.1.1.1, hp.1.2.1]
    · exact hp.2
  have h3 : ∀ N ∈ Icc 2 X, ∑ p ∈ s.filter (fun p => p.1 * p.2 = N), F p =
      ∑ d ∈ N.properDivisors, F (d, N / d) := by
    intro N hNmem
    have hN2 : 2 ≤ N := (Finset.mem_Icc.mp hNmem).1
    have hNX : N ≤ X := (Finset.mem_Icc.mp hNmem).2
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
  rw [h1, h2, Finset.sum_congr rfl h3]

/-! ### One `N`-term -/

lemma div_div_natDiv {x : ℝ} {N d : ℕ} (hd : d ∈ N.properDivisors) (hN : 2 ≤ N) :
    x / d / ((N / d : ℕ) : ℝ) = x / N := by
  have hd' := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
  have hdN : d * (N / d) = N := Nat.mul_div_cancel' hd'.1
  have hNr : ((N / d : ℕ) : ℝ) * d = N := by exact_mod_cast (by rw [mul_comm]; exact hdN)
  rw [div_div, mul_comm, hNr]

open Classical in
/-- **The `N`-term of `g` is at most `MA[ℙ](x/N)/N`**. -/
lemma nterm_le {X0 : ℕ} (hX : 1 < (X0 : ℝ)) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) {N : ℕ} (hN : 2 ≤ N) :
    |∑ d ∈ N.properDivisors, cQ X0 x d / d * edgeTerm X0 κ (x / d) (N / d)| ≤
      if InEdge X0 κ (x / N) then MAP X0 κ (x / N) / N else 0 := by
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hx0 : 0 < x := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set q := x / N with hq
  have hq0 : 0 < q := div_pos hx0 hN0
  set b := (1 + κ) * q with hb
  have hb0 : 0 ≤ b := by positivity
  -- rewrite each term
  have hterm : ∀ d ∈ N.properDivisors, cQ X0 x d / d * edgeTerm X0 κ (x / d) (N / d) =
      if InEdge X0 κ q then cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q / N else 0 := by
    intro d hd
    have hd' := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
    have hdN : d * (N / d) = N := Nat.mul_div_cancel' hd'.1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hNr : (d : ℝ) * ((N / d : ℕ) : ℝ) = N := by exact_mod_cast hdN
    unfold edgeTerm
    rw [div_div_natDiv hd hN]
    split_ifs
    · have hq0' : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos (N / d) with h | h
        · rw [h, mul_zero] at hdN; omega
        · exact_mod_cast h
      calc cQ X0 x d / d * (MAPfrom (max X0 (Pplus (N / d))) κ q / ((N / d : ℕ) : ℝ))
          = cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q / ((d : ℝ) * ((N / d : ℕ) : ℝ)) := by
            ring
        _ = _ := by rw [hNr]
    · ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hW : InEdge X0 κ q
  · simp only [if_pos hW]
    rw [← Finset.sum_div, abs_div, abs_of_pos hN0]
    apply div_le_div_of_nonneg_right _ hN0.le
    -- the window primes
    set W := (Finset.range (⌊b⌋₊ + 1)).filter fun p => p.Prime ∧ X0 ≤ p ∧ q ≤ p with hWdef
    have hcount : ∀ d ∈ N.properDivisors, (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ) =
        ∑ p ∈ W, if Pplus (N / d) ≤ p then 1 else 0 := by
      intro d _
      rw [newPrimeCount_eq_card' _ hb0, Finset.sum_boole, ← Finset.filter_filter]
      congr 2
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, max_le_iff, hWdef]
      tauto
    have hc : ∀ d ∈ N.properDivisors, cQ X0 x d = (μ d : ℝ) *
        (if LemmaM.chi tQ lv x d then 1 else 0) := by
      intro d hd
      have hd' := Nat.mem_properDivisors.mp hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
      have hle : (X0 : ℝ) ≤ x / d := by
        have h2 : 2 * d ≤ N := by
          obtain ⟨k, hk⟩ := hd'.1
          have hk2 : 2 ≤ k := by
            by_contra hc; push_neg at hc
            interval_cases k <;> omega
          calc 2 * d ≤ k * d := Nat.mul_le_mul_right _ hk2
            _ = N := by rw [hk]; ring
        have h2r : 2 * (d : ℝ) ≤ N := by exact_mod_cast h2
        have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
        have hW1 := hW.1
        rw [div_lt_iff₀ (by linarith)] at hW1
        rw [le_div_iff₀ hdr]
        have : x = q * N := by rw [hq]; field_simp
        rw [this]
        nlinarith
      rw [cQ_eq hx hd0, if_pos hle]
      ring
    have hκq : 0 < κ * q := mul_pos hκ hq0
    have hsum1 : ∑ d ∈ N.properDivisors, cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q =
        (∑ d ∈ N.properDivisors, cQ X0 x d *
          (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ)) / (κ * q) := by
      unfold MAPfrom
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    have hsum2 : ∑ d ∈ N.properDivisors, cQ X0 x d *
        (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ) =
        ∑ p ∈ W, ∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
          (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0) := by
      rw [Finset.sum_congr rfl (fun d hd => by rw [hcount d hd, Finset.mul_sum])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hc d hd]
      split_ifs <;> ring
    have hpN : ∀ p ∈ W, (p : ℝ) * N < 2 * x := by
      intro p hp
      obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
      have hpb : (p : ℝ) ≤ b := by
        have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hb0)
      have : b * N = (1 + κ) * x := by rw [hb, hq]; field_simp
      nlinarith
    have hbound : |∑ p ∈ W, ∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
        (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0)| ≤ W.card := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ p ∈ W, |∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
            (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0)| ≤ ∑ p ∈ W, (1 : ℝ) :=
            Finset.sum_le_sum fun p hp => coeff_window_le hN (hpN p hp)
        _ = W.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hW : (W.card : ℝ) = newPrimeCount X0 q b := by
      rw [newPrimeCount_eq_card' X0 hb0]
    rw [hsum1, hsum2, abs_div, abs_of_pos hκq]
    unfold MAP
    rw [← hb, ← hW]
    exact div_le_div_of_nonneg_right hbound hκq.le
  · simp only [if_neg hW, Finset.sum_const_zero, abs_zero, le_refl]

/-! ### The bound on `g` -/

open Classical in
/-- `∑_{N: x/N ∈ (X₀/(1+κ), X₀)} 1/N ≤ κ + X₀/x`. -/
lemma sum_edge_inv_le {X0 : ℕ} (hX : 1 < (X0 : ℝ)) {κ : ℝ} (hκ : 0 < κ) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) :
    ∑ N ∈ (Icc 2 ⌊x⌋₊).filter (fun N : ℕ => InEdge X0 κ (x / N)), (1 : ℝ) / (N : ℝ) ≤
      κ + X0 / x := by
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hx0 : 0 < x := by linarith
  set E := (Icc 2 ⌊x⌋₊).filter (fun N : ℕ => InEdge X0 κ (x / N))
  set a := x / X0
  set b := (1 + κ) * x / X0
  have ha0 : 0 ≤ a := by positivity
  have hab : a ≤ b := by
    show x / X0 ≤ (1 + κ) * x / X0
    apply div_le_div_of_nonneg_right _ hX0.le; nlinarith
  have hmem : ∀ N ∈ E, a < N ∧ (N : ℝ) < b := by
    intro N hN
    obtain ⟨hN1, hW⟩ := Finset.mem_filter.mp hN
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hN1).1
    have hN0 : (0 : ℝ) < N := by linarith
    obtain ⟨h1, h2⟩ := hW
    constructor
    · show x / X0 < N
      rw [div_lt_iff₀ hX0]; rw [div_lt_iff₀ hN0] at h2; linarith
    · show (N : ℝ) < (1 + κ) * x / X0
      rw [lt_div_iff₀ hX0]
      rw [div_lt_div_iff₀ (by linarith) hN0] at h1; linarith
  have hsub : E ⊆ (Finset.Icc 1 ⌊b⌋₊).filter fun p : ℕ => a < p ∧ (p : ℝ) ≤ b := by
    intro N hN
    obtain ⟨h1, h2⟩ := hmem N hN
    have hN2 : 2 ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor h2.le⟩, h1, h2.le⟩
  have hcard : (E.card : ℝ) ≤ b - a + 1 :=
    (by exact_mod_cast Finset.card_le_card hsub : (E.card : ℝ) ≤ _).trans (card_Ioc_le ha0 hab)
  have hterm : ∀ N ∈ E, (1 : ℝ) / N ≤ X0 / x := by
    intro N hN
    have h1 := (hmem N hN).1
    have hN0 : (0 : ℝ) < N := lt_of_le_of_lt ha0 h1
    rw [div_le_div_iff₀ hN0 hx0]
    show 1 * x ≤ X0 * N
    have : x / X0 < N := h1
    rw [div_lt_iff₀ hX0] at this; linarith
  calc ∑ N ∈ E, (1 : ℝ) / N ≤ ∑ N ∈ E, (X0 : ℝ) / x := Finset.sum_le_sum hterm
    _ = E.card * (X0 / x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (b - a + 1) * (X0 / x) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = κ + X0 / x := by
        show ((1 + κ) * x / X0 - x / X0 + 1) * (X0 / x) = κ + X0 / x
        field_simp; ring

/-- **The bound on `g`** (proof of Lemma 7.3(d)(iii)): `|g(x)| ≤ (1.0001/Λ)(κ + X₀/x)` for
`x ≥ X₀`, under (huxley). -/
theorem gEdge_bound {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) :
    GEdgeBound X0 := by
  classical
  intro x hx
  set κ := Construction.kappaParam X0 with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hκlt : κ < 1 := by
    have := kappa_le_tiny (X0 := (X0 : ℝ)) (by linarith [one_lt_of_log hX]) hX
    linarith
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ : 0 < Real.log X0 := by linarith
  rw [gEdge_eq hX1 hx, regroup (fun n => cQ X0 x n / n)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ N ∈ Icc 2 ⌊x⌋₊, |∑ d ∈ N.properDivisors, cQ X0 x d / d *
      edgeTerm X0 κ (x / d) (N / d)| ≤
      if InEdge X0 κ (x / N) then 1.0001 / Real.log X0 * (1 / N) else 0 := by
    intro N hN
    have hN2 := (Finset.mem_Icc.mp hN).1
    refine (nterm_le hX1 hκ0 hκlt hx hN2).trans ?_
    split_ifs with hW
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (MAP_le_edge hX hH hW.1 hW.2) (by positivity)
    · exact le_rfl
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_edge_inv_le hX1 hκ0 hx) (by positivity)

end BaseRange
