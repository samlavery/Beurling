module

public import RequestProject.Beurling.BaseRange.Lemma73cReal

/-!
# §7.2: the realised smooth part `μ₀`, the decomposition (86), and Lemma 7.3(b)

With the realised operator `K_pt` (`KR.Sharp.Kpt`) and the source `S = (1 - ρ_det) 1_{[X₀,∞)}` of
the base range, define

  `μ₀ := S - MA[ℙ]1 - K_pt(MA[ℙ]1) - μ_edge - μ₁`   (`mu0R`), `MA[ℙ]1 = MA[ℙ] 1_{[X₀,∞)}`.

Then `S = (1 + K_pt)(MA[ℙ]1) + μ_edge + μ₀ + μ₁` identically, and applying `R_sh = (1 + K_pt)⁻¹`
gives **(86)** (`shdecomp`): `ρ^sh = MA[ℙ] + ρ_edge + R_sh μ₀ + R_sh μ₁` on `[X₀⁻, ∞)`.
Moreover `μ₀ = 0` below `X₀` (`mu0R_eq_zero`).

On `[X₀, ∞)`, as in §7.2 (`mu0R_split`),

  `μ₀ = [S - MA[ℙ] - K_ℚ MA[ℙ] - μ_edge] + [(K_ℚ - K^sh_ℚ) MA[ℙ]] + [(K^sh_ℚ - K_pt)(f₀ 1)]`:

* the first bracket is the exact rational identity (85) (`eq:ratid`) up to `1/(κu)`
  (`ratid`): the non-rigid integers of the window are counted by their largest prime;
* the second is the partial windows of Lemma 7.1(3) (`partial_windows_le`): `≤ κ log u/Λ`;
* the third is Steps 1–3 of the proof of (b) together with the decision-order mismatch of
  "the rest": the named hypothesis `Lemma73bCore`.

`lemma73b_of` : **Lemma 7.3(b)** for `mu0R` from `Lemma73bCore`.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-! ### `P⁺` -/

lemma Pplus_mem {n : ℕ} (hn : 1 < n) : Pplus n ∈ n.primeFactors := by
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup _ (Nat.nonempty_primeFactors.mpr hn) id
  unfold Pplus; rw [hpe]; exact hp

lemma le_Pplus {n p : ℕ} (hp : p ∈ n.primeFactors) : p ≤ Pplus n := by
  unfold Pplus; exact Finset.le_sup (f := id) hp

lemma Pplus_mul_prime {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hmp : Pplus m ≤ p) :
    Pplus (m * p) = p := by
  unfold Pplus at hmp ⊢
  rw [Nat.primeFactors_mul (by omega) hp.ne_zero, hp.primeFactors, Finset.sup_union,
    Finset.sup_singleton]
  exact max_eq_right hmp

lemma Pplus_one : Pplus 1 = 0 := by simp [Pplus]

lemma Pplus_div_le {n : ℕ} (hn : 1 < n) : Pplus (n / Pplus n) ≤ Pplus n := by
  have hP := Pplus_mem hn
  have hdvd : n / Pplus n ∣ n := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hP)
  unfold Pplus
  exact Finset.sup_mono (Nat.primeFactors_mono hdvd (by omega))

/-! ### The rational component operator `K_ℚ` -/

/-- `K_ℚ(MA[ℙ] 1_{[X₀,∞)})(u) = ∑_{2 ≤ m ≤ u/X₀} m⁻¹ MA_{κq}[primes ≥ max(P⁺(m), X₀)](q)|_{q=u/m}`
(the component form of §7.2, including the partial windows). -/
noncomputable def KQ (X0 : ℕ) (κ u : ℝ) : ℝ :=
  ∑ m ∈ Icc 2 ⌊u / X0⌋₊, MAPfrom (max X0 (Pplus m)) κ (u / m) / m

/-- The non-rigid integers of the window `[u, (1+κ)u]`. -/
noncomputable def nonRigid (X0 : ℕ) (κ u : ℝ) : Finset ℕ :=
  (windowInts κ u).filter fun n => ∃ p ∈ n.primeFactors, X0 ≤ p

lemma mem_windowInts {κ u : ℝ} (hu : 0 < u) (hκ : 0 < κ) {n : ℕ} :
    n ∈ windowInts κ u ↔ u ≤ n ∧ (n : ℝ) ≤ (1 + κ) * u := by
  rw [windowInts, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.ceil_le.mp h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))⟩
  · rintro ⟨h1, h2⟩; exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩

/-- The window integers split into rigid ones and non-rigid ones. -/
lemma card_window_eq {X0 : ℕ} {κ u : ℝ} (hu : 0 < u) :
    (windowInts κ u).card = (rigidSet X0 κ u).card + (nonRigid X0 κ u).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := windowInts κ u) (fun n => ∃ p ∈ n.primeFactors, X0 ≤ p)
  rw [← hsplit, add_comm]
  congr 1
  apply congrArg
  ext n
  simp only [Finset.mem_filter, rigidSet, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers,
    windowInts, Finset.mem_Icc, not_exists, not_and, not_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hn0 : n ≠ 0 := by
      intro h; subst h
      have := Nat.ceil_le.mp h1; push_cast at this; linarith
    refine ⟨⟨h2, hn0, fun p hp => h3 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)⟩,
      Nat.ceil_le.mp h1⟩
  · rintro ⟨⟨h2, hn0, h3⟩, h1⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, h2⟩,
      fun p hp => h3 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)⟩

/-- The new primes `≥ T` in `[a, b]` as a finset. -/
lemma newPrimeCount_eq_card' (T : ℕ) {a b : ℝ} (hb : 0 ≤ b) :
    newPrimeCount T a b =
      ((Finset.range (⌊b⌋₊ + 1)).filter fun p => p.Prime ∧ T ≤ p ∧ a ≤ p).card := by
  classical
  unfold newPrimeCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_floor h4), h1, h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩
    exact ⟨h1, h2, h3, (Nat.cast_le.mpr (Nat.lt_succ_iff.mp h4)).trans (Nat.floor_le hb)⟩

/-- **The non-rigid integers counted by their largest prime**:
`#nonRigid = ∑_{1 ≤ m ≤ (1+κ)u/X₀} #{p ≥ max(X₀, P⁺(m)) prime : u/m ≤ p ≤ (1+κ)u/m}`. -/
theorem card_nonRigid {X0 : ℕ} (hX0 : 1 ≤ X0) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) :
    ((nonRigid X0 κ u).card : ℝ) = ∑ m ∈ Icc 1 ⌊(1 + κ) * u / X0⌋₊,
      (newPrimeCount (max X0 (Pplus m)) (u / m) ((1 + κ) * (u / m)) : ℝ) := by
  classical
  have hX0r : (0 : ℝ) < X0 := by exact_mod_cast hX0
  set M := ⌊(1 + κ) * u / X0⌋₊
  -- facts on the elements of `nonRigid`
  have hfacts : ∀ n ∈ nonRigid X0 κ u, 1 < n ∧ X0 ≤ Pplus n ∧ (Pplus n).Prime ∧
      Pplus n ∣ n ∧ u ≤ n ∧ (n : ℝ) ≤ (1 + κ) * u := by
    intro n hn
    obtain ⟨hw, ⟨p, hp, hpX⟩⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := (mem_windowInts hu hκ).mp hw
    have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
    have hn1 : 1 < n := by
      have := Nat.le_of_mem_primeFactors hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    have hP := Pplus_mem hn1
    exact ⟨hn1, hpX.trans (le_Pplus hp), Nat.prime_of_mem_primeFactors hP,
      Nat.dvd_of_mem_primeFactors hP, h1, h2⟩
  have hmaps : ∀ n ∈ nonRigid X0 κ u, n / Pplus n ∈ Icc 1 M := by
    intro n hn
    obtain ⟨hn1, hPX, hPp, hPd, h1, h2⟩ := hfacts n hn
    obtain ⟨m, hm⟩ := hPd
    have hP0 : 0 < Pplus n := hPp.pos
    have hmeq : n / Pplus n = m := Nat.div_eq_of_eq_mul_right hP0 hm
    rw [hmeq, Finset.mem_Icc]
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm; omega
      · exact h
    refine ⟨hm1, Nat.le_floor ?_⟩
    rw [le_div_iff₀ hX0r]
    have : (n : ℝ) = Pplus n * m := by exact_mod_cast hm
    have hPXr : (X0 : ℝ) ≤ Pplus n := by exact_mod_cast hPX
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n / Pplus n)
    (fun n hn => Finset.mem_coe.mpr (hmaps n (Finset.mem_coe.mp hn)))]
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hb0 : (0 : ℝ) ≤ (1 + κ) * (u / m) := by positivity
  rw [newPrimeCount_eq_card' _ hb0]
  norm_cast
  -- the fibre over `m` is `{m p}` for the primes `p ≥ max(X₀, P⁺(m))` of `[u/m, (1+κ)u/m]`
  apply Finset.card_nbij' (fun n => Pplus n) (fun p => m * p)
  · intro n hn
    obtain ⟨hn1, hm'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    obtain ⟨hn1', hPX, hPp, hPd, h1, h2⟩ := hfacts n hn1
    obtain ⟨k, hk⟩ := hPd
    have hP0 : 0 < Pplus n := hPp.pos
    have hkm : k = m := by rw [← hm']; exact (Nat.div_eq_of_eq_mul_right hP0 hk).symm
    subst hkm
    have hPm : Pplus k ≤ Pplus n := by
      have := Pplus_div_le hn1'
      rwa [Nat.div_eq_of_eq_mul_right hP0 hk] at this
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    have hnr : (n : ℝ) = Pplus n * k := by exact_mod_cast hk
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hPp, max_le hPX hPm, ?_⟩
    · rw [mul_div_assoc', le_div_iff₀ hm0]; nlinarith
    · rw [div_le_iff₀ hm0]; nlinarith
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp
    obtain ⟨hp1, hpp, hpT, hpa⟩ := hp
    have hpX : X0 ≤ p := le_of_max_le_left hpT
    have hPm : Pplus m ≤ p := le_of_max_le_right hpT
    have hpb : (p : ℝ) ≤ (1 + κ) * (u / m) :=
      (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hp1)).trans (Nat.floor_le hb0)
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · simp only [nonRigid, Finset.mem_filter]
      refine ⟨(mem_windowInts hu hκ).mpr ⟨?_, ?_⟩, ⟨p, ?_, hpX⟩⟩
      · push_cast; rw [div_le_iff₀ hm0] at hpa; linarith
      · push_cast; rw [mul_div_assoc', le_div_iff₀ hm0] at hpb; linarith
      · exact hpp.mem_primeFactors (dvd_mul_left p m) (Nat.mul_ne_zero (by omega) hpp.ne_zero)
    · rw [Pplus_mul_prime hm1 hpp hPm, Nat.mul_div_cancel _ hpp.pos]
  · intro n hn
    obtain ⟨hn1, hm'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    obtain ⟨-, -, hPp, hPd, -, -⟩ := hfacts n hn1
    simp only
    rw [← hm', Nat.div_mul_cancel hPd]
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp
    obtain ⟨-, hpp, hpT, -⟩ := hp
    exact Pplus_mul_prime hm1 hpp (le_of_max_le_right hpT)

lemma windowInts_card_ge {κ u : ℝ} (hu : 0 < u) :
    κ * u - 1 ≤ ((windowInts κ u).card : ℝ) := by
  rw [windowInts, Nat.card_Icc]
  set b := (1 + κ) * u
  have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu.le
  have h2 : b - 1 < (⌊b⌋₊ : ℝ) := Nat.sub_one_lt_floor b
  rcases le_or_gt ⌈u⌉₊ (⌊b⌋₊ + 1) with hc | hc
  · rw [Nat.cast_sub hc]; push_cast
    have : b = κ * u + u := by simp only [b]; ring
    linarith
  · have : (⌊b⌋₊ : ℝ) + 1 < ⌈u⌉₊ := by exact_mod_cast hc
    have : b = κ * u + u := by simp only [b]; ring
    have : (0 : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈u⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- `#nonRigid/(κu) = MA[ℙ](u) + K_ℚ(MA[ℙ]1)(u) + μ_edge(u)` for `u ≥ X₀` (`X₀` not prime). -/
theorem nonRigid_eq {X0 : ℕ} (hX0 : 2 ≤ X0) (hXp : ¬ X0.Prime) {κ u : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hu : (X0 : ℝ) ≤ u) :
    ((nonRigid X0 κ u).card : ℝ) / (κ * u) = MAP X0 κ u + KQ X0 κ u + muEdge X0 κ u := by
  classical
  have hX0r : (2 : ℝ) ≤ X0 := by exact_mod_cast hX0
  have hu0 : 0 < u := by linarith
  have hκu : 0 < κ * u := mul_pos hκ hu0
  set M := ⌊(1 + κ) * u / X0⌋₊ with hM
  set M0 := ⌊u / X0⌋₊ with hM0
  have hM0M : M0 ≤ M := Nat.floor_le_floor (div_le_div_of_nonneg_right (by nlinarith)
    (by positivity))
  rw [card_nonRigid (by omega) hκ hu0, Finset.sum_div]
  set t : ℕ → ℝ := fun m => MAPfrom (max X0 (Pplus m)) κ (u / m) / m with ht
  have hterm : ∀ m ∈ Icc 1 M, (newPrimeCount (max X0 (Pplus m)) (u / m)
      ((1 + κ) * (u / m)) : ℝ) / (κ * u) = t m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    simp only [ht, MAPfrom]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have h1M : 1 ≤ M := by
    apply Nat.le_floor
    rw [le_div_iff₀ (by positivity)]; push_cast; nlinarith
  rw [← Finset.sum_Ioc_add_eq_sum_Icc h1M]
  have ht1 : MAPfrom (max X0 (Pplus 1)) κ (u / ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) = MAP X0 κ u := by
    simp only [Nat.cast_one, div_one, Pplus_one, max_eq_left (Nat.zero_le X0)]
    rfl
  rw [ht1, show Finset.Ioc 1 M = Icc 2 M from rfl]
  suffices hA : ∑ m ∈ Icc 2 M, t m = KQ X0 κ u + muEdge X0 κ u by
    change ∑ m ∈ Icc 2 M, t m + MAP X0 κ u = _
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 M) (fun m => m ≤ M0)]
  have hf1 : (Icc 2 M).filter (fun m => m ≤ M0) = Icc 2 M0 := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hf1, show KQ X0 κ u = ∑ m ∈ Icc 2 M0, t m from rfl]
  congr 1
  -- the components below `X₀`
  have hzero : ∀ m ∈ (Icc 2 M).filter (fun m => ¬ m ≤ M0),
      ¬ InEdge X0 κ (u / (m : ℝ)) → t m = 0 := by
    intro m hm hW
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by have := (Finset.mem_Icc.mp hm1).1; omega)
    have hqX : u / m < X0 := by
      by_contra hc; push_neg at hc
      apply hm2
      apply Nat.le_floor
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hm0] at hc; linarith
    have hq : u / m ≤ X0 / (1 + κ) := by
      by_contra hc; push_neg at hc; exact hW ⟨hc, hqX⟩
    simp only [ht]
    have hb : (1 + κ) * (u / m) ≤ X0 := by
      rw [le_div_iff₀ (by linarith)] at hq; linarith
    have h0 : newPrimeCount (max X0 (Pplus m)) (u / m) ((1 + κ) * (u / m)) = 0 := by
      unfold newPrimeCount
      convert Set.ncard_empty ℕ
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp, hpT, -, hpb⟩
      have h1 : X0 ≤ p := le_of_max_le_left hpT
      have h2 : (p : ℝ) ≤ X0 := hpb.trans hb
      have : p = X0 := le_antisymm (by exact_mod_cast h2) h1
      exact hXp (this ▸ hp)
    simp only [MAPfrom, h0, Nat.cast_zero, zero_div]
  unfold muEdge
  rw [← Finset.sum_filter_add_sum_filter_not ((Icc 2 M).filter (fun m => ¬ m ≤ M0))
    (fun m : ℕ => InEdge X0 κ (u / (m : ℝ)))]
  have hz2 : ∑ m ∈ ((Icc 2 M).filter (fun m => ¬ m ≤ M0)).filter
      (fun m : ℕ => ¬ InEdge X0 κ (u / (m : ℝ))), t m = 0 :=
    Finset.sum_eq_zero fun m hm => hzero m (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2
  rw [hz2, add_zero]
  have hedge : ∀ N : ℕ, 2 ≤ N → InEdge X0 κ (u / (N : ℝ)) →
      N ≤ M ∧ ¬ N ≤ M0 ∧ N ≤ ⌊u⌋₊ := by
    intro N hN hW
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    obtain ⟨h1, h2⟩ := hW
    rw [div_lt_div_iff₀ (by linarith) hN0] at h1
    rw [div_lt_iff₀ hN0] at h2
    have hN1 : (N : ℝ) * X0 < (1 + κ) * u := by linarith
    refine ⟨Nat.le_floor ?_, ?_, Nat.le_floor ?_⟩
    · rw [le_div_iff₀ (by positivity)]; linarith
    · intro hc
      have : (N : ℝ) ≤ u / X0 := (Nat.cast_le.mpr hc).trans (Nat.floor_le (by positivity))
      rw [le_div_iff₀ (by positivity)] at this; linarith
    · have : (N : ℝ) * 2 < 2 * u := by nlinarith
      linarith
  set E := (Icc 2 M).filter (fun m : ℕ => InEdge X0 κ (u / (m : ℝ))) with hE
  have hEa : ((Icc 2 M).filter (fun m => ¬ m ≤ M0)).filter
      (fun m : ℕ => InEdge X0 κ (u / (m : ℝ))) = E := by
    ext m
    simp only [hE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, (hedge m h1.1 h3).2.1⟩, h3⟩
  have hEb : (Icc 2 ⌊u⌋₊).filter (fun m : ℕ => InEdge X0 κ (u / (m : ℝ))) = E := by
    ext m
    simp only [hE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨⟨h1, (hedge m h1 h3).1⟩, h3⟩
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨⟨h1, (hedge m h1 h3).2.2⟩, h3⟩
  rw [hEa]
  have hmu : ∑ N ∈ Icc 2 ⌊u⌋₊, edgeTerm X0 κ u N =
      ∑ N ∈ (Icc 2 ⌊u⌋₊).filter (fun m : ℕ => InEdge X0 κ (u / (m : ℝ))), t N := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun N _ => ?_
    simp only [edgeTerm, ht]
  rw [hmu, hEb]

/-- **The rational identity (85)** (`eq:ratid`) in the base range: for `u ≥ X₀` (`X₀` not
prime), `|1 - ρ_det(u) - (MA[ℙ](u) + K_ℚ(MA[ℙ]1)(u) + μ_edge(u))| ≤ 1/(κu)`. -/
theorem ratid {X0 : ℕ} (hX0 : 2 ≤ X0) (hXp : ¬ X0.Prime) {κ u : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hu : (X0 : ℝ) ≤ u) :
    |1 - Target.rhoDet X0 κ u - (MAP X0 κ u + KQ X0 κ u + muEdge X0 κ u)| ≤ 1 / (κ * u) := by
  have hX0r : (2 : ℝ) ≤ X0 := by exact_mod_cast hX0
  have hu0 : 0 < u := by linarith
  have hκu : 0 < κ * u := mul_pos hκ hu0
  rw [← nonRigid_eq hX0 hXp hκ hκ1 hu]
  have hW := card_window_eq (X0 := X0) (κ := κ) hu0
  have hup := windowInts_card_le hκ hu0
  have hlo := windowInts_card_ge (κ := κ) hu0
  unfold Target.rhoDet
  rw [rigidCount_eq]
  have hWr : ((windowInts κ u).card : ℝ) = (rigidSet X0 κ u).card + (nonRigid X0 κ u).card := by
    exact_mod_cast hW
  have e : 1 - ((rigidSet X0 κ u).card : ℝ) / (κ * u) - ((nonRigid X0 κ u).card : ℝ) / (κ * u) =
      (κ * u - (windowInts κ u).card) / (κ * u) := by
    rw [hWr]; field_simp; ring
  rw [e, abs_div, abs_of_pos hκu]
  apply div_le_div_of_nonneg_right _ hκu.le
  rw [abs_le]; constructor <;> linarith

end BaseRange
