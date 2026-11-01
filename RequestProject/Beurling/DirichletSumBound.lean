module

public import RequestProject.Beurling.BoxL2

/-!
# The Dirichlet sum `S` in the proof of Lemma 4.8(ii)

Let `n_0 ≤ … ≤ n_{m-1}` be reals (counted with multiplicity) in `[X, 2^J X]`, `X ≥ 2`, such that

* each window `[n_i, n_i + 2]` contains at most `2 (n_i + 2)^η + 5` elements of the list, and
* each dyadic interval `(N, 2N]` contains at most `1.02 N` of them.

Then (`dirichlet_sum_box`), with `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`, `Γ ≥ 0`, `0 ≤ η ≤ 1/8`,

  `∬_Q |∑_i n_i^{-s}|² ≤ (25 √(Γ + 1/2) X^{η/2 - 1/4} + 40 (2^J X)^{η/2 + 1/4})²`.

This is the bound `‖S‖ ≤ 11 X₀^{-3/16} + 22 a_k^{η/2+1/4} Γ^{-1/2}` of the paper (there with the
normalisation `‖F‖² = Γ⁻¹ ∬_Q |F|²`), with slightly larger constants. The proof splits the list
into the dyadic blocks `(2^{j-1} X, 2^j X]`, applies the block estimate `box_block` to each block
and Minkowski's inequality `box_minkowski` to the sum, and sums two geometric series.
-/

@[expose] public section

open Complex MeasureTheory Set Finset GoodHeights

namespace GoodHeights

/-- The dyadic block index of `x ≥ X`: the least `j` with `x ≤ 2^j X`. -/
noncomputable def blockIdx (X x : ℝ) : ℕ := sInf {j : ℕ | x ≤ 2 ^ j * X}

lemma blockIdx_spec {X x : ℝ} {J : ℕ} (hX : 0 < X) (hXx : X ≤ x) (hx : x ≤ 2 ^ J * X) :
    blockIdx X x ≤ J ∧ 2 ^ blockIdx X x * X / 2 < x ∧ x ≤ 2 * (2 ^ blockIdx X x * X / 2) := by
  have hne : ({j : ℕ | x ≤ 2 ^ j * X} : Set ℕ).Nonempty := ⟨J, hx⟩
  have hmem : x ≤ 2 ^ blockIdx X x * X := Nat.sInf_mem hne
  refine ⟨Nat.sInf_le hx, ?_, by linarith⟩
  rcases Nat.eq_zero_or_pos (blockIdx X x) with h0 | hpos
  · rw [h0]; simp; linarith
  · have hlt : blockIdx X x - 1 < blockIdx X x := Nat.sub_lt hpos one_pos
    have hnot := Nat.notMem_of_lt_sInf hlt
    simp only [mem_setOf_eq, not_le] at hnot
    have e : (2 : ℝ) ^ blockIdx X x = 2 * 2 ^ (blockIdx X x - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; linarith

lemma four_rpow_le {η : ℝ} (hη : η ≤ 1 / 8) : (4 : ℝ) ^ η ≤ 1.19 := by
  calc (4 : ℝ) ^ η ≤ 4 ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη
    _ ≤ (1.19 ^ (8 : ℝ)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 1.19 := by rw [← Real.rpow_mul (by norm_num)]; norm_num

/-- The bound for one block. -/
lemma block_coeff_le {N η Γ : ℝ} (hN : 1 ≤ N) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hΓ : 0 ≤ Γ) :
    Real.sqrt (0.51 * (2 * (2 * N + 2) ^ η + 5) * (Γ + 1 / 2 + 2 * Real.pi * (N + 1)) *
        N ^ (-(1 / 2 : ℝ))) ≤
      1.95 * Real.sqrt (Γ + 1 / 2) * N ^ (η / 2 - 1 / 4) + 6.92 * N ^ (η / 2 + 1 / 4) := by
  have hN0 : 0 < N := by linarith
  have hK : 2 * (2 * N + 2) ^ η + 5 ≤ 7.38 * N ^ η := by
    have h1 : (2 * N + 2) ^ η ≤ (4 * N) ^ η :=
      Real.rpow_le_rpow (by linarith) (by linarith) hη0
    rw [Real.mul_rpow (by norm_num) hN0.le] at h1
    have h2 := four_rpow_le hη
    have h3 : 1 ≤ N ^ η := Real.one_le_rpow hN hη0
    have h4 : 0 ≤ N ^ η := by positivity
    nlinarith
  have hpi : 2 * Real.pi * (N + 1) ≤ 12.57 * N := by
    have := Real.pi_lt_d4; nlinarith
  set P := Γ + 1 / 2
  have hP : 0 ≤ P := by positivity
  have hA : 0 ≤ 1.95 * Real.sqrt P * N ^ (η / 2 - 1 / 4) := by positivity
  have hB : 0 ≤ 6.92 * N ^ (η / 2 + 1 / 4) := by positivity
  rw [Real.sqrt_le_left (by positivity)]
  have e1 : (N ^ (η / 2 - 1 / 4)) ^ 2 = N ^ η * N ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; norm_num; ring_nf
  have e2 : (N ^ (η / 2 + 1 / 4)) ^ 2 = N ^ η * N ^ (-(1 / 2 : ℝ)) * N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      show (η / 2 + 1 / 4) * ((2 : ℕ) : ℝ) = η + (-(1 / 2 : ℝ)) + 1 by push_cast; ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
  have hsq : (1.95 * Real.sqrt P * N ^ (η / 2 - 1 / 4)) ^ 2 = 3.8025 * P * (N ^ η * N ^ (-(1 / 2 : ℝ))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hP, e1]; ring
  have hsq2 : (6.92 * N ^ (η / 2 + 1 / 4)) ^ 2 = 47.8864 * (N ^ η * N ^ (-(1 / 2 : ℝ)) * N) := by
    rw [mul_pow, e2]; ring
  have hNh : 0 ≤ N ^ (-(1 / 2 : ℝ)) := by positivity
  have hNe : 0 ≤ N ^ η := by positivity
  calc 0.51 * (2 * (2 * N + 2) ^ η + 5) * (P + 2 * Real.pi * (N + 1)) * N ^ (-(1 / 2 : ℝ))
      ≤ 0.51 * (7.38 * N ^ η) * (P + 12.57 * N) * N ^ (-(1 / 2 : ℝ)) := by
        gcongr
    _ ≤ 3.8025 * P * (N ^ η * N ^ (-(1 / 2 : ℝ))) +
          47.8864 * (N ^ η * N ^ (-(1 / 2 : ℝ)) * N) := by
        have : 0 ≤ N ^ η * N ^ (-(1 / 2 : ℝ)) := by positivity
        nlinarith
    _ = (1.95 * Real.sqrt P * N ^ (η / 2 - 1 / 4)) ^ 2 + (6.92 * N ^ (η / 2 + 1 / 4)) ^ 2 := by
        rw [hsq, hsq2]
    _ ≤ _ := by nlinarith

/-- The geometric series with negative exponent. -/
lemma dyadic_rpow {X p : ℝ} (hX : 0 < X) (j : ℕ) :
    (2 ^ j * X / 2) ^ p = (X / 2) ^ p * ((2 : ℝ) ^ p) ^ j := by
  rw [show (2 : ℝ) ^ j * X / 2 = 2 ^ j * (X / 2) by ring,
    Real.mul_rpow (by positivity) (by positivity), mul_comm]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

lemma two_rpow_neg_le : (2 : ℝ) ^ (-(3 / 16) : ℝ) ≤ 0.8784 := by
  calc (2 : ℝ) ^ (-(3 / 16) : ℝ) = ((2 : ℝ) ^ (-3 : ℝ)) ^ (1 / 16 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ (0.8784 ^ (16 : ℝ)) ^ (1 / 16 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
          Real.rpow_natCast]
        norm_num
    _ = 0.8784 := by rw [← Real.rpow_mul (by norm_num)]; norm_num

lemma two_rpow_quarter_le : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.1893 := by
  calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (1.1893 ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    _ = 1.1893 := by rw [← Real.rpow_mul (by norm_num)]; norm_num

lemma le_two_rpow_quarter : 1.189 ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
  calc (1.189 : ℝ) = (1.189 ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

lemma geom_neg {X p : ℝ} (hX : 0 < X) (hp1 : -(1 / 4) ≤ p) (hp : p ≤ -(3 / 16)) (J : ℕ) :
    ∑ j ∈ range (J + 1), (2 ^ j * X / 2) ^ p ≤ 9.79 * X ^ p := by
  simp only [dyadic_rpow hX]
  rw [← Finset.mul_sum]
  set r := (2 : ℝ) ^ p
  have hr0 : 0 ≤ r := by positivity
  have hr : r ≤ 0.8784 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp).trans two_rpow_neg_le
  have hgeom : ∑ j ∈ range (J + 1), r ^ j ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J + 1) hr0 (by linarith)
    simpa using this
  have h2 : (X / 2) ^ p = X ^ p * (2 : ℝ) ^ (-p) := by
    rw [Real.div_rpow hX.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  have h3 : (2 : ℝ) ^ (-p) ≤ 1.1893 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans two_rpow_quarter_le
  have h4 : 1 / (1 - r) ≤ 8.2237 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hXp : 0 ≤ X ^ p := by positivity
  have hg0 : 0 ≤ ∑ j ∈ range (J + 1), r ^ j := Finset.sum_nonneg fun j _ => by positivity
  rw [h2]
  calc X ^ p * 2 ^ (-p) * ∑ j ∈ range (J + 1), r ^ j ≤ X ^ p * 1.1893 * 8.2237 := by
        gcongr; exact hgeom.trans h4
    _ ≤ 9.79 * X ^ p := by nlinarith

/-- The geometric series with positive exponent. -/
lemma geom_pos {X q : ℝ} (hX : 0 < X) (hq : 1 / 4 ≤ q) (J : ℕ) :
    ∑ j ∈ range (J + 1), (2 ^ j * X / 2) ^ q ≤ 5.3 * (2 ^ J * X) ^ q := by
  simp only [dyadic_rpow hX]
  rw [← Finset.mul_sum]
  set r := (2 : ℝ) ^ q
  have hr : 1.189 ≤ r :=
    le_two_rpow_quarter.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq)
  have hgeom : ∑ j ∈ range (J + 1), r ^ j ≤ r ^ (J + 1) / (r - 1) := by
    rw [geom_sum_eq (by linarith), div_le_div_iff_of_pos_right (by linarith)]; linarith
  have hkey : (X / 2) ^ q * r ^ (J + 1) = (2 ^ J * X) ^ q := by
    rw [← dyadic_rpow hX]; congr 1; rw [pow_succ]; ring
  have hXq : 0 ≤ (X / 2) ^ q := by positivity
  calc (X / 2) ^ q * ∑ j ∈ range (J + 1), r ^ j ≤ (X / 2) ^ q * (r ^ (J + 1) / (r - 1)) := by
        gcongr
    _ = (2 ^ J * X) ^ q / (r - 1) := by rw [← hkey]; ring
    _ ≤ 5.3 * (2 ^ J * X) ^ q := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ (2 ^ J * X) ^ q := by positivity
        nlinarith

/-- **The Dirichlet sum `S` in the proof of Lemma 4.8(ii).** Let `n_0 ≤ … ≤ n_{m-1}` be reals in
`[X, 2^J X]`, `X ≥ 2`, such that every window `[n_i, n_i + 2]` contains at most
`2 (n_i + 2)^η + 5` of them and every dyadic interval `(N, 2N]` with `N ≥ 1` at most `1.02 N`.
Then for `0 ≤ η ≤ 1/8` and `Γ ≥ 0`, on `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`,
`∬_Q |∑_i n_i^{-s}|² ≤ (25 √(Γ + 1/2) X^{η/2-1/4} + 40 (2^J X)^{η/2+1/4})²`. -/
theorem dirichlet_sum_box {m J : ℕ} {X η Γ : ℝ} (hX : 2 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hΓ : 0 ≤ Γ) {n : Fin m → ℝ} (hmono : Monotone n)
    (hrange : ∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X)
    (hwin : ∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5)
    (hcount : ∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
      1.02 * N) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4),
        ENNReal.ofReal (‖∑ i, ((n i : ℝ) : ℂ) ^ (-z)‖ ^ 2) ≤
      ENNReal.ofReal ((25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) +
        40 * (2 ^ J * X) ^ (η / 2 + 1 / 4)) ^ 2) := by
  have hX0 : 0 < X := by linarith
  set bi : Fin m → ℕ := fun i => blockIdx X (n i)
  have hbi : ∀ i, bi i ≤ J ∧ 2 ^ bi i * X / 2 < n i ∧ n i ≤ 2 * (2 ^ bi i * X / 2) :=
    fun i => blockIdx_spec hX0 (hrange i).1 (hrange i).2
  set Nj : ℕ → ℝ := fun j => 2 ^ j * X / 2
  have hNj : ∀ j, 1 ≤ Nj j := by
    intro j
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    simp only [Nj]; nlinarith
  set sj : ℕ → Finset (Fin m) := fun j => univ.filter (fun i => bi i = j)
  set g : ℕ → ℂ → ℂ := fun j z => ∑ i ∈ sj j, ((n i : ℝ) : ℂ) ^ (-z)
  have hn0 : ∀ i, 0 < n i := fun i => by linarith [(hrange i).1]
  have hsplit : ∀ z : ℂ, ∑ i, ((n i : ℝ) : ℂ) ^ (-z) = ∑ j ∈ range (J + 1), g j z := by
    intro z
    simp only [g, sj]
    rw [Finset.sum_fiberwise_of_maps_to (g := bi) (fun i _ => mem_range.mpr
      (Nat.lt_succ_of_le (hbi i).1))]
  simp_rw [hsplit]
  set P := Γ + 1 / 2
  set p := η / 2 - 1 / 4
  set q := η / 2 + 1 / 4
  set c : ℕ → ℝ := fun j => 1.95 * Real.sqrt P * Nj j ^ p + 6.92 * Nj j ^ q
  have hc : ∀ j ∈ range (J + 1), 0 < c j := by
    intro j _
    have : 0 < Nj j := by linarith [hNj j]
    simp only [c]; positivity
  have hgm : ∀ j, Measurable (g j) := by
    intro j
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (Continuous.measurable (continuous_const.cpow continuous_neg (fun _ => Or.inl (by
        simp only [Complex.ofReal_re]; exact hn0 i))))
  have hblock : ∀ j ∈ range (J + 1), ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4),
      ENNReal.ofReal (‖g j z‖ ^ 2) ≤ ENNReal.ofReal (c j ^ 2) := by
    intro j _
    set Kr : ℝ := 2 * (2 * Nj j + 2) ^ η + 5
    have hKr : 5 ≤ Kr := by
      have h1 := hNj j
      have : 0 ≤ (2 * Nj j + 2) ^ η := by positivity
      simp only [Kr]; linarith
    set K : ℕ := ⌊Kr⌋₊
    have hK : 0 < K := Nat.floor_pos.mpr (by linarith)
    have hKle : (K : ℝ) ≤ Kr := Nat.floor_le (by linarith)
    have hrng : ∀ i ∈ sj j, Nj j < n i ∧ n i ≤ 2 * Nj j := by
      intro i hi
      simp only [sj, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := hbi i; rw [hi] at this; exact ⟨this.2.1, this.2.2⟩
    have hw : ∀ i ∈ sj j, (univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card ≤ K := by
      intro i hi
      apply Nat.le_floor
      refine (hwin i).trans ?_
      have : (n i + 2) ^ η ≤ (2 * Nj j + 2) ^ η :=
        Real.rpow_le_rpow (by linarith [hn0 i]) (by linarith [(hrng i hi).2]) hη0
      simp only [Kr]; linarith
    have hb := box_block hK (hNj j) hmono (sj j) hrng hw hΓ
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard : ((sj j).card : ℝ) ≤ 1.02 * Nj j := by
      refine le_trans ?_ (hcount (Nj j) (hNj j))
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hrng i hi)
    have hN0 : 0 < Nj j := by linarith [hNj j]
    have hcoef := block_coeff_le (hNj j) hη0 hη hΓ
    have hpow : Nj j * Nj j ^ (-(3 / 2 : ℝ)) = Nj j ^ (-(1 / 2 : ℝ)) := by
      nth_rewrite 1 [← Real.rpow_one (Nj j)]
      rw [← Real.rpow_add hN0]; norm_num
    have hpos : 0 ≤ 2 * Real.pi * (Nj j + 1) := by positivity
    have hsq : 0.51 * Kr * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) * Nj j ^ (-(1 / 2 : ℝ)) ≤
        c j ^ 2 := by
      have h0 : 0 ≤ 0.51 * Kr * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) *
          Nj j ^ (-(1 / 2 : ℝ)) := by positivity
      rw [← Real.sqrt_le_left (by simp only [c]; positivity)]
      exact hcoef
    have hpp : 0 ≤ Nj j ^ (-(3 / 2 : ℝ)) := by positivity
    calc 1 / 2 * (K * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) * ((sj j).card * Nj j ^ (-(3 / 2 : ℝ))))
        ≤ 1 / 2 * (Kr * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) *
            (1.02 * Nj j * Nj j ^ (-(3 / 2 : ℝ)))) := by
          gcongr
      _ = 0.51 * Kr * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) *
            (Nj j * Nj j ^ (-(3 / 2 : ℝ))) := by ring
      _ = 0.51 * Kr * (Γ + 1 / 2 + 2 * Real.pi * (Nj j + 1)) * Nj j ^ (-(1 / 2 : ℝ)) := by
          rw [hpow]
      _ ≤ c j ^ 2 := hsq
  refine (box_minkowski (range (J + 1)) hgm hc _ hblock).trans (ENNReal.ofReal_le_ofReal ?_)
  have hsumc : ∑ j ∈ range (J + 1), c j ≤
      25 * Real.sqrt P * X ^ p + 40 * (2 ^ J * X) ^ q := by
    simp only [c, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := geom_neg hX0 (p := p) (by simp only [p]; linarith) (by simp only [p]; linarith) J
    have h2 := geom_pos hX0 (q := q) (by simp only [q]; linarith) J
    have hs : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
    have hXp : 0 ≤ X ^ p := by positivity
    have hXq : 0 ≤ (2 ^ J * X) ^ q := by positivity
    have : 1.95 * Real.sqrt P * ∑ j ∈ range (J + 1), Nj j ^ p ≤ 1.95 * Real.sqrt P * (9.79 * X ^ p) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have h0 : 0 ≤ ∑ j ∈ range (J + 1), c j := Finset.sum_nonneg fun j hj => (hc j hj).le
  exact pow_le_pow_left₀ h0 hsumc 2

end GoodHeights

end
