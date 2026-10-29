module

public import RequestProject.Beurling.Construction.Scales

/-!
# The arrivals of the slot model are the composites of the realised system

Section 3.4 of the paper defines the arrivals `A_j` of the hard greedy rule as the number of
composite elements of the realised system `P(ω)` whose value lies in the slot `J_j = [s_j, s_{j+1})`.
Here this link is formalized (`ArrivalsLinked`): the composites are counted over the realised
primes themselves (the rational primes `p < X₀` and the placed primes, `RealisedIdx`), as exponent
vectors with at least two prime factors (counted with multiplicity).

With the link, the condition that **the greedy rule places infinitely many primes** is no longer an
input: it is proved (`placed_infinite_of_linked`). If only finitely many primes were placed, the
elements of value below `y` would number at most `(log₂ y + 1)^m` (`m` primes, all `≥ 2`); the
target grows linearly (`target_ge_linear`), so the slot starts grow at most linearly
(`slot_le_linear`), and after the last placement the queue would have to absorb one unit per slot
with only polylogarithmically many arrivals, which is impossible.

`Theorem21InputsN` is `Theorem21InputsM` with the condition "infinitely many placed primes" replaced
by the link `ArrivalsLinked`; it implies `Theorem21InputsM` (`theorem21InputsM_of_N`), hence
Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Set Real CaplLink SlotModel Target Oscillation Absorbed Filter QueueMono Greedy Bookkeeping
  DesignedZero GoodHeights Decomp

namespace Construction

section Link

variable {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ) (U : ℕ → ℝ)

/-- The value `∏ p_i^{e_i}` of an element of the realised system, as an exponent vector over the
realised primes. -/
noncomputable def idxVal (e : RealisedIdx M →₀ ℕ) : ℝ :=
  e.prod fun i n => realisedVal M H U i ^ n

/-- The composite elements (at least two prime factors, with multiplicity) of value in `[a, b)`. -/
def compositeSet (a b : ℝ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | 2 ≤ e.sum (fun _ n => n) ∧ a ≤ idxVal M H U e ∧ idxVal M H U e < b}

/-- The number of composite elements of the realised system in the relative slot `k`,
`[s_k, s_{k+1})`. -/
noncomputable def compositeArr (k : ℕ) : ℤ :=
  ((compositeSet M H U (M.slot k) (M.slot (k + 1))).ncard : ℤ)

/-- **The arrivals are the composites of the realised system**: at every relative slot `k ≥ 1`
(paper's slot `j = X₀ - 1 + k`), `A_j` is the number of composite elements of `P(ω)` with value in
`J_j = [s_j, s_{j+1})`. -/
def ArrivalsLinked : Prop := ∀ k, M.arr (k + 1) = compositeArr M H U (k + 1)

end Link

/-! ### Counting elements over finitely many primes -/

lemma pow_le_finsupp_prod {I : Type*} (v : I → ℝ) (hv : ∀ i, 1 ≤ v i) (e : I →₀ ℕ) (i : I) :
    v i ^ e i ≤ e.prod fun j n => v j ^ n := by
  classical
  by_cases hi : i ∈ e.support
  · unfold Finsupp.prod
    rw [← Finset.mul_prod_erase _ _ hi]
    have h1 : 1 ≤ ∏ x ∈ e.support.erase i, v x ^ e x := by
      simpa using Finset.prod_le_prod (s := e.support.erase i) (f := fun _ => (1 : ℝ))
        (g := fun x => v x ^ e x) (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (hv j))
    have h0 : 0 ≤ v i ^ e i := pow_nonneg (by linarith [hv i]) _
    nlinarith
  · have : e i = 0 := by simpa using hi
    rw [this, pow_zero]
    unfold Finsupp.prod
    simpa using Finset.prod_le_prod (s := e.support) (f := fun _ => (1 : ℝ))
      (g := fun x => v x ^ e x) (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (hv j))

/-- **Few elements over finitely many primes**: with `m` primes, all `≥ 2`, there are at most
`(⌊log₂ y⌋ + 1)^m` elements of value `< y`. -/
theorem ncard_val_lt_le {I : Type*} [Finite I] (v : I → ℝ) (hv : ∀ i, 2 ≤ v i) {y : ℝ}
    (hy : 0 < y) :
    {e : I →₀ ℕ | (e.prod fun i n => v i ^ n) < y}.ncard ≤
      (⌊Real.logb 2 y⌋₊ + 1) ^ Nat.card I := by
  classical
  set B := ⌊Real.logb 2 y⌋₊
  let g : (I → Fin (B + 1)) → (I →₀ ℕ) := fun f => Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)
  have hsub : {e : I →₀ ℕ | (e.prod fun i n => v i ^ n) < y} ⊆ g '' univ := by
    intro e he
    have hb : ∀ i, e i < B + 1 := by
      intro i
      have h1 := pow_le_finsupp_prod v (fun j => by linarith [hv j]) e i
      have h2 : (2 : ℝ) ^ e i ≤ v i ^ e i := pow_le_pow_left₀ (by norm_num) (hv i) _
      have h3 : (2 : ℝ) ^ ((e i : ℕ) : ℝ) ≤ y := by
        rw [Real.rpow_natCast]; exact (h2.trans h1).trans (le_of_lt he)
      have h4 : ((e i : ℕ) : ℝ) ≤ Real.logb 2 y :=
        (Real.le_logb_iff_rpow_le (by norm_num) hy).mpr h3
      exact Nat.lt_succ_of_le (Nat.le_floor h4)
    refine ⟨fun i => ⟨e i, hb i⟩, mem_univ _, ?_⟩
    ext i
    simp [g]
  calc _ ≤ (g '' univ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ (univ : Set (I → Fin (B + 1))).ncard := ncard_image_le (toFinite _)
    _ = (B + 1) ^ Nat.card I := by
        rw [ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma finite_val_lt {I : Type*} [Finite I] (v : I → ℝ) (hv : ∀ i, 2 ≤ v i) (y : ℝ) :
    {e : I →₀ ℕ | (e.prod fun i n => v i ^ n) < y}.Finite := by
  classical
  rcases le_or_gt y 0 with hy | hy
  · refine Set.Finite.subset (Set.finite_empty) fun e he => ?_
    have : 0 ≤ e.prod fun i n => v i ^ n := by
      unfold Finsupp.prod
      exact Finset.prod_nonneg fun j _ => pow_nonneg (by linarith [hv j]) _
    exact absurd he (not_lt.mpr (hy.trans this))
  · set B := ⌊Real.logb 2 y⌋₊
    let g : (I → Fin (B + 1)) → (I →₀ ℕ) :=
      fun f => Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)
    refine Set.Finite.subset ((Set.finite_univ).image g) fun e he => ?_
    have hb : ∀ i, e i < B + 1 := by
      intro i
      have h1 := pow_le_finsupp_prod v (fun j => by linarith [hv j]) e i
      have h2 : (2 : ℝ) ^ e i ≤ v i ^ e i := pow_le_pow_left₀ (by norm_num) (hv i) _
      have h3 : (2 : ℝ) ^ ((e i : ℕ) : ℝ) ≤ y := by
        rw [Real.rpow_natCast]; exact (h2.trans h1).trans (le_of_lt he)
      have h4 : ((e i : ℕ) : ℝ) ≤ Real.logb 2 y :=
        (Real.le_logb_iff_rpow_le (by norm_num) hy).mpr h3
      exact Nat.lt_succ_of_le (Nat.le_floor h4)
    refine ⟨fun i => ⟨e i, hb i⟩, mem_univ _, ?_⟩
    ext i
    simp [g]

/-! ### The target grows linearly -/

lemma two_pow_forty_le_of_logX {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    (2 : ℝ) ^ (40 : ℕ) ≤ X₀ := by
  have hX0 : 0 < X₀ := lt_trans one_pos (one_lt_of_logX hX0' hX)
  have h1 : Real.log ((2 : ℝ) ^ (40 : ℕ)) ≤ Real.log X₀ := by
    rw [Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; nlinarith
  exact (Real.log_le_log_iff (by positivity) hX0).mp h1

/-- `2 x^θ log* x ≤ x/10` for `x ≥ X₀`, `θ ≤ 1/2`. -/
lemma osc_bound_le_tenth {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {θ : ℝ} (hθ : θ ≤ 1 / 2)
    {x : ℝ} (hx : X₀ ≤ x) : 2 * x ^ θ * (logStar x : ℝ) ≤ x / 10 := by
  have h40 := two_pow_forty_le_of_logX hX0' hX
  have hx40 : (2 : ℝ) ^ (40 : ℕ) ≤ x := h40.trans hx
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (by norm_num)) hx40
  have hx0 : 0 < x := by linarith
  have hls := logStar_le_rpow hx1 (show (0 : ℝ) < 0.05 by norm_num)
  have hθx : x ^ θ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ
  have hsplit : x = x ^ (0.55 : ℝ) * x ^ (0.45 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h45 : (2 : ℝ) ^ (18 : ℕ) ≤ x ^ (0.45 : ℝ) := by
    have e : ((2 : ℝ) ^ (40 : ℕ)) ^ (0.45 : ℝ) = 2 ^ (18 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hx40 (by norm_num)
  have h55 : x ^ (1 / 2 : ℝ) * x ^ (0.05 : ℝ) = x ^ (0.55 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hpos : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  have hpos2 : 0 ≤ x ^ (0.05 : ℝ) := Real.rpow_nonneg hx0.le _
  have hpos3 : 0 ≤ x ^ (0.55 : ℝ) := Real.rpow_nonneg hx0.le _
  calc 2 * x ^ θ * (logStar x : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) * ((1 / 0.05 + 1) * x ^ (0.05 : ℝ)) := by
        gcongr
    _ = 42 * x ^ (0.55 : ℝ) := by rw [← h55]; ring
    _ ≤ x ^ (0.55 : ℝ) * x ^ (0.45 : ℝ) / 10 := by nlinarith
    _ = x / 10 := by rw [← hsplit]

/-- **The target grows linearly**: `T(x) ≥ 0.7 x - X₀ - 1` for `x ≥ X₀`, for any non-negative
absorbed count, absorbed density capped by `0.1/log u`, and oscillation bounded by
`2 x^θ log* x` with `R(X₀) = 0`. -/
theorem target_ge_linear {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {θ : ℝ} (hθ : θ ≤ 1 / 2)
    {cntA rhoA R : ℝ → ℝ} (hc : ∀ x, 0 ≤ cntA x) (hrho : ∀ u, (X₀ : ℝ) ≤ u → rhoA u ≤ 1 / 10)
    (hR : ∀ x, (X₀ : ℝ) ≤ x → |R x| ≤ 2 * x ^ θ * (logStar x : ℝ)) (hR0 : R X₀ = 0) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) :
    7 / 10 * x - X₀ - 1 ≤ target X₀ (kappaParam X₀) cntA rhoA R x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hκ0 := kappa_pos_aux hX
  have hκ1 : kappaParam (X₀ : ℝ) ≤ 1 / 10 := (kappa_le_aux hX).trans (by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith)
  have hT : target X₀ (kappaParam X₀) cntA rhoA R x =
      x + rigidErr X₀ (kappaParam X₀) x + (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u) + R x := by
    simp only [target, if_neg (not_lt.mpr hx), rigidErr, hR0]; ring
  rw [hT]
  have hr := abs_le.mp (abs_rigidErr_le_fine X₀ hκ0 hX1n hx)
  have hint : (∫ u in (X₀ : ℝ)..x, rhoA u) ≤ (x - X₀) / 10 := by
    by_cases hi : IntervalIntegrable rhoA MeasureTheory.volume (X₀ : ℝ) x
    · have := intervalIntegral.integral_mono_on hx hi
        (intervalIntegrable_const (c := (1 / 10 : ℝ))) (fun u hu => hrho u hu.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    · rw [intervalIntegral.integral_undef hi]; linarith
  have hRx := (abs_le.mp (hR x hx)).1
  have hosc := osc_bound_le_tenth (X₀ := (X₀ : ℝ)) (Nat.cast_nonneg _) hX hθ hx
  have hcx := hc x
  have : kappaParam (X₀ : ℝ) * x ≤ x / 10 := by nlinarith
  have : kappaParam (X₀ : ℝ) * X₀ ≤ X₀ := by nlinarith
  linarith

/-! ### Infinitely many primes are placed -/

/-- The prime decision is `0` or `1`. -/
lemma greedyPrime_eq_zero_of_ne_one {A : ℕ → ℤ} (hA : ∀ k, 0 ≤ A k) {j : ℕ}
    (h : greedyPrime A j ≠ 1) : greedyPrime A j = 0 := by
  have hq := greedyQueue_nonneg A j
  have ha := hA (j + 1)
  unfold greedyPrime at h ⊢
  omega

/-- After the last placement the queue absorbs one unit per slot. -/
lemma queue_of_no_placement {A : ℕ → ℤ} (hA : ∀ k, 0 ≤ A k) {J : ℕ}
    (hno : ∀ k, J ≤ k → greedyPrime A k ≠ 1) (n : ℕ) :
    greedyQueue A (J + n) = greedyQueue A J + (∑ i ∈ Finset.range n, A (J + i + 1)) - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 := greedyPrime_eq_zero_of_ne_one hA (hno (J + n) (by omega))
    have e : greedyQueue A (J + (n + 1)) =
        greedyQueue A (J + n) + A (J + n + 1) + greedyPrime A (J + n) - 1 := by
      show greedyQueue A (J + n + 1) = _
      simp only [greedyQueue, greedyPrime]
    rw [e, h0, ih, Finset.sum_range_succ]
    push_cast; ring

section Infinite

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- The slot starts grow at most linearly: `s_k ≤ 2 (2 X₀ + k + 1)`. -/
lemma slot_le_linear (hX : 10 ^ 8 ≤ Real.log X₀)
    (hT : ∀ x, (X₀ : ℝ) ≤ x → 7 / 10 * x - X₀ - 1 ≤ M.T x) (k : ℕ) :
    M.slot k ≤ 2 * (2 * X₀ + k + 1) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  apply M.slot_le
  refine ⟨by linarith, ?_⟩
  have := hT (2 * (2 * X₀ + k + 1)) (by linarith)
  unfold level
  linarith [M.hϑ]

/-- Every realised prime is `≥ 2`. -/
lemma realisedVal_ge_two (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (i : RealisedIdx M) :
    2 ≤ realisedVal M (capH X₀) U i := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h40 := two_pow_forty_le_of_logX hX0 hX
  cases i with
  | inl p =>
    show (2 : ℝ) ≤ ((p.1 : ℕ) : ℝ)
    exact_mod_cast p.2.1.two_le
  | inr k =>
    obtain ⟨h1, h2⟩ := primeValueOf_ge M hU hX hTlow k.1
    show 2 ≤ primeValueOf M (capH X₀) U k.1
    have : (2 : ℝ) ^ (40 : ℕ) ≥ 3 := by norm_num
    linarith

/-- **The greedy rule places infinitely many primes**, given that the arrivals are the composites of
the realised system and the target grows linearly. -/
theorem placed_infinite_of_growth (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊)
    (hT : ∀ x, (X₀ : ℝ) ≤ x → 7 / 10 * x - X₀ - 1 ≤ M.T x)
    (hlink : ArrivalsLinked M (capH X₀) U) : {k | placedAt M k}.Infinite := by
  classical
  intro hfin
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  -- the realised primes are finitely many
  haveI : Finite {k // placedAt M k} := hfin.to_subtype
  haveI : Finite {p : ℕ // p.Prime ∧ p < X₀} :=
    (Set.finite_lt_nat X₀).subset (fun p hp => hp.2) |>.to_subtype
  haveI : Finite (RealisedIdx M) := inferInstance
  set m := Nat.card (RealisedIdx M)
  set v := realisedVal M (capH X₀) U
  have hv := realisedVal_ge_two hU hX hTlow (M := M)
  -- the last placement
  obtain ⟨J, hJ⟩ := hfin.bddAbove
  have hno : ∀ k, J + 1 ≤ k → greedyPrime M.arr k ≠ 1 := by
    intro k hk hpl
    have := hJ (show k ∈ {k | placedAt M k} from hpl)
    omega
  set J0 := J + 1
  set Q0 := greedyQueue M.arr J0
  -- arrivals over slots `J0 + 1, …, J0 + n` are composites below `s_{J0 + n + 1}`
  have hsum : ∀ n, (∑ i ∈ Finset.range n, M.arr (J0 + i + 1)) ≤
      ({e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧ M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧
        idxVal M (capH X₀) U e < M.slot (J0 + n + 1)}.ncard : ℤ) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact_mod_cast Nat.zero_le _
    | succ n ih =>
      rw [Finset.sum_range_succ, hlink (J0 + n)]
      unfold compositeArr
      have hmono := M.slot_mono (show J0 + n + 1 ≤ J0 + (n + 1) + 1 by omega)
      have hmono0 := M.slot_mono (show J0 + 1 ≤ J0 + n + 1 by omega)
      have hfinS : {e : RealisedIdx M →₀ ℕ | idxVal M (capH X₀) U e <
          M.slot (J0 + (n + 1) + 1)}.Finite := finite_val_lt v hv _
      have hunion : {e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧
            M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧
            idxVal M (capH X₀) U e < M.slot (J0 + n + 1)} ∪
          compositeSet M (capH X₀) U (M.slot (J0 + n + 1)) (M.slot (J0 + n + 1 + 1)) =
          {e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧
            M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧
            idxVal M (capH X₀) U e < M.slot (J0 + (n + 1) + 1)} := by
        ext e
        simp only [compositeSet, mem_union, mem_setOf_eq]
        constructor
        · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1, h2, by linarith⟩
          · exact ⟨h1, by linarith, by rw [show J0 + (n + 1) + 1 = J0 + n + 1 + 1 by omega]; exact h3⟩
        · rintro ⟨h1, h2, h3⟩
          by_cases h : idxVal M (capH X₀) U e < M.slot (J0 + n + 1)
          · exact Or.inl ⟨h1, h2, h⟩
          · push_neg at h
            exact Or.inr ⟨h1, h, by rw [show J0 + n + 1 + 1 = J0 + (n + 1) + 1 by omega]; exact h3⟩
      have hdisj : Disjoint {e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧
            M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧
            idxVal M (capH X₀) U e < M.slot (J0 + n + 1)}
          (compositeSet M (capH X₀) U (M.slot (J0 + n + 1)) (M.slot (J0 + n + 1 + 1))) := by
        rw [Set.disjoint_left]
        rintro e ⟨-, -, h3⟩ ⟨-, h2, -⟩
        linarith
      have hf1 : {e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧
            M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧
            idxVal M (capH X₀) U e < M.slot (J0 + n + 1)}.Finite :=
        hfinS.subset fun e he => by
          simp only [mem_setOf_eq] at he ⊢; linarith [he.2.2]
      have hf2 : (compositeSet M (capH X₀) U (M.slot (J0 + n + 1))
          (M.slot (J0 + n + 1 + 1))).Finite :=
        hfinS.subset fun e he => by
          simp only [compositeSet, mem_setOf_eq] at he ⊢
          rw [show J0 + (n + 1) + 1 = J0 + n + 1 + 1 by omega]; exact he.2.2
      rw [← hunion, ncard_union_eq hdisj hf1 hf2]
      push_cast
      linarith
  -- the contradiction
  have hQ : ∀ n : ℕ, (n : ℝ) ≤ Q0 + (3 * Real.log (2 * (2 * X₀ + J0 + n + 2))) ^ m := by
    intro n
    have hq := queue_of_no_placement M.arr_nonneg (J := J0) hno n
    have hq0 := greedyQueue_nonneg M.arr (J0 + n)
    set y := M.slot (J0 + n + 1)
    have hy1 : 1 ≤ y := M.one_le_slot _
    have hyle : y ≤ 2 * (2 * X₀ + (J0 + n + 1 : ℕ) + 1) := slot_le_linear hX hT _
    have hcount := ncard_val_lt_le v hv (y := y) (by linarith)
    have hsub := ncard_le_ncard (s := {e : RealisedIdx M →₀ ℕ | 2 ≤ e.sum (fun _ n => n) ∧
        M.slot (J0 + 1) ≤ idxVal M (capH X₀) U e ∧ idxVal M (capH X₀) U e < y})
      (t := {e : RealisedIdx M →₀ ℕ | (e.prod fun i n => v i ^ n) < y})
      (fun e he => he.2.2) (finite_val_lt v hv y)
    have h1 := hsum n
    have hc' := hsub.trans hcount
    have hint : (n : ℤ) ≤ Q0 + (((⌊Real.logb 2 y⌋₊ + 1) ^ m : ℕ) : ℤ) := by
      have := (Nat.cast_le (α := ℤ)).mpr hc'
      linarith
    have hintR : (n : ℝ) ≤ Q0 + ((⌊Real.logb 2 y⌋₊ : ℝ) + 1) ^ m := by
      have := (Int.cast_le (R := ℝ)).mpr hint
      push_cast at this
      exact this
    -- `⌊log₂ y⌋ + 1 ≤ 3 log(2(2X₀ + J0 + n + 2))`
    set z := 2 * (2 * (X₀ : ℝ) + J0 + n + 2)
    have hyz : y ≤ z := by
      have : ((J0 + n + 1 : ℕ) : ℝ) = J0 + n + 1 := by push_cast; ring
      rw [this] at hyle; linarith
    have hz3 : 3 ≤ z := by
      have : (0 : ℝ) ≤ J0 := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    have hlogz : 1 ≤ Real.log z := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hlog2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hfl : (⌊Real.logb 2 y⌋₊ : ℝ) + 1 ≤ 3 * Real.log z := by
      have hlb : Real.logb 2 y ≤ 2 * Real.log z := by
        rw [Real.logb, div_le_iff₀ (by linarith)]
        have := Real.log_le_log (by linarith) hyz
        have := Real.log_nonneg hy1
        nlinarith
      have := Nat.floor_le (Real.logb_nonneg (b := 2) (by norm_num) hy1)
      linarith
    have hpow : ((⌊Real.logb 2 y⌋₊ : ℝ) + 1) ^ m ≤ (3 * Real.log z) ^ m :=
      pow_le_pow_left₀ (by positivity) hfl m
    linarith
  -- `n ≤ Q0 + 3^m (log(2n + c))^m` fails for large `n`
  set c : ℝ := 2 * (2 * (X₀ : ℝ) + J0 + 2)
  have hc0 : 0 ≤ c := by positivity
  have hlim := Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-c / 2 - Q0) m (by norm_num)
  have hev1 := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 3 ^ m by positivity))
  have hev2 : ∀ᶠ z : ℝ in atTop, 0 < 1 / 2 * z + (-c / 2 - Q0) :=
    (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_gt_atTop 0)
  obtain ⟨Z0, hZ0⟩ := (hev1.and hev2).exists_forall_of_atTop
  set n := ⌈max Z0 0⌉₊
  have hn : max Z0 0 ≤ n := Nat.le_ceil _
  have hz : Z0 ≤ 2 * (n : ℝ) + c := by
    have := le_max_left Z0 0
    have := le_max_right Z0 0
    linarith
  obtain ⟨h1, h2⟩ := hZ0 _ hz
  have hzeq : 2 * (2 * (X₀ : ℝ) + J0 + n + 2) = 2 * n + c := by ring
  have hbig := hQ n
  rw [hzeq] at hbig
  rw [div_lt_div_iff₀ h2 (by positivity)] at h1
  have e3 : (3 * Real.log (2 * (n : ℝ) + c)) ^ m = 3 ^ m * Real.log (2 * (n : ℝ) + c) ^ m := by
    rw [mul_pow]
  rw [e3] at hbig
  nlinarith

end Infinite

/-- The paper's target grows linearly, with the designed oscillation. -/
theorem T_ge_of_formula {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {P : BeurlingSystem} {A : Set ℝ} {u : ℝ → ℝ} {a : ℕ → ℝ}
    {M : SlotModel X₀}
    (hT : ∀ x, M.T x = target X₀ (kappaParam X₀) (countA A) (absorbedDensityCap (θ / 2) A u)
      (osc θ (designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    7 / 10 * x - X₀ - 1 ≤ M.T x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  rw [hT x]
  have hsp := switchOn_spacing (X₀ : ℝ)
  have hα : ∀ k, |designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a k| ≤ 2 := by
    intro k
    have hm := designedAlpha_mem P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀) a
      (heightScale_switchOn_pos θ hX1.le) k
    rw [abs_of_nonneg (by linarith [hm.1])]
    exact hm.2
  refine target_ge_linear hX (by linarith [hθ.2]) (fun x => ?_) (fun v hv => ?_)
    (fun v hv => abs_osc_le hsp hα (by linarith)) ?_ hx
  · unfold countA; positivity
  · unfold absorbedDensityCap
    refine (min_le_right _ _).trans ?_
    have hl : 10 ^ 8 ≤ Real.log v := hX.trans (Real.log_le_log (by linarith) hv)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · exact osc_eq_zero_of_le hsp (by linarith : (0 : ℝ) < X₀) (switchOn_zero_ge _)

/-- The target of `PartIRestJ` grows linearly, with the designed oscillation. -/
theorem partIRestJ_T_ge {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {P : BeurlingSystem} {A : Set ℝ} {u : ℝ → ℝ} {a : ℕ → ℝ}
    {M : SlotModel X₀} (hI : PartIRestJ θ X₀ P A u a M) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    7 / 10 * x - X₀ - 1 ≤ M.T x :=
  T_ge_of_formula hθ hX hI.1 hx

/-- **Infinitely many primes are placed** in a slot model whose target is the paper's target and
whose arrivals are the composites of the realised system. -/
theorem placed_infinite_of_linked {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (M : SlotModel X₀) {U : ℕ → ℝ}
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) {a : ℕ → ℝ}
    (hI : PartIRestJ θ X₀ (realisedSystem M (capH X₀) U) (realisedA M (capH X₀) U)
      (fun n => solveU (θ / 2) n) a M)
    (hlink : ArrivalsLinked M (capH X₀) U) : {k | placedAt M k}.Infinite := by
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hI.1 x]
    simp only [target, if_pos hx]
  exact placed_infinite_of_growth hU hX hTlow (fun x hx => partIRestJ_T_ge hθ hX hI hx) hlink

/-- **Theorem 2.1, hypothesis on the concrete construction, with the arrivals tied to the
realised system.** `Theorem21InputsM` with the condition that the greedy rule places infinitely
many primes replaced by `ArrivalsLinked`: the arrivals of the slot model are the composites of
`P(ω)` in the slots. -/
def Theorem21InputsN : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ArrivalsLinked (M ω) (capH X₀) ω ∧
        PartIRestJ θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (θ / 2) n) (constructionScale X₀) (M ω) ∧
        Theorem410RestM θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (θ / 2) n) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsN` implies `Theorem21InputsM`: infinitely many primes are placed. -/
theorem theorem21InputsM_of_N (h : Theorem21InputsN) : Theorem21InputsM := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hlink, hI, hC, hcl⟩ := hP ω hG hω
  exact ⟨placed_infinite_of_linked hθ hlog (M ω) hω hI hlink, hI, hC, hcl⟩

/-- Theorem 2.1 from `Theorem21InputsN`. -/
theorem theorem21_of_N (h : Theorem21InputsN) : Theorem21 :=
  theorem21_of_M (theorem21InputsM_of_N h)

/-- **Corollary 2.2** from `Theorem21InputsN`. -/
theorem corollary_2_2_of_N (h : Theorem21InputsN) : ¬ QuestionQ :=
  corollary_2_2_of_M (theorem21InputsM_of_N h)

end Construction

end
