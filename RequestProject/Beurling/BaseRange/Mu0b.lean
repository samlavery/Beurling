module

public import RequestProject.Beurling.BaseRange.Mu0

/-!
# §7.2: the decomposition (86) for the realised system and Lemma 7.3(b)

Continuation of `Mu0.lean`: the partial windows (`partial_windows_le`), the linearity of the
operators, the realised `μ₀` (`mu0R`), the decomposition (86) (`shdecomp`), the split of `μ₀`
(`mu0R_split`), and **Lemma 7.3(b)** (`lemma73b_of`) from the named hypothesis
`Lemma73bCore` (Steps 1–3 of the proof of (b) and the decision-order mismatch).
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-! ### Monotonicity of the window counts in the threshold -/

lemma newPrimeCount_anti {T T' : ℕ} (hTT : T ≤ T') (a b : ℝ) (hb : 0 ≤ b) :
    newPrimeCount T' a b ≤ newPrimeCount T a b := by
  rw [newPrimeCount_eq_card' _ hb, newPrimeCount_eq_card' _ hb]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hTT.trans hp.2.2.1, hp.2.2.2⟩

lemma newPrimeCount_eq_of_le {T P : ℕ} {q b : ℝ} (hPq : (P : ℝ) ≤ q) :
    newPrimeCount (max T P) q b = newPrimeCount T q b := by
  unfold newPrimeCount
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, le_of_max_le_left h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, max_le h2 ?_, h3, h4⟩
    have : (P : ℝ) ≤ p := hPq.trans h3
    exact_mod_cast this

lemma newPrimeCount_eq_zero_of_lt {T : ℕ} {q b : ℝ} (hb : b < T) : newPrimeCount T q b = 0 := by
  unfold newPrimeCount
  convert! Set.ncard_empty ℕ
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2, -, h4⟩
  have : (T : ℝ) ≤ p := by exact_mod_cast h2
  linarith

/-- `MA[ℙ](q) ≤ 1.0001/Λ` for `q ≥ X₀`. -/
lemma MAP_le_of_ge {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq : (X0 : ℝ) ≤ q) : MAP X0 (Construction.kappaParam X0) q ≤ 1.0001 / Real.log X0 := by
  have h := (MAP_log_bounds hX hH hq).2
  have hL := log_ge_of_ge hX hq
  have hlq : Real.log X0 ≤ Real.log q := Real.log_le_log (by linarith [one_lt_of_log hX]) hq
  have hε : Real.log q ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hL
  have hΛ0 : 0 < Real.log X0 := by linarith
  have hm0 := MAP_nonneg X0 (BModel.kappa_facts hX).1.le (by linarith [one_lt_of_log hX] :
    (0 : ℝ) ≤ q)
  rw [le_div_iff₀ hΛ0]
  have : MAP X0 (Construction.kappaParam X0) q * Real.log X0 ≤
      MAP X0 (Construction.kappaParam X0) q * Real.log q := mul_le_mul_of_nonneg_left hlq hm0
  linarith

/-- **The partial windows** (Lemma 7.1(3), used in "the rest" of the proof of (b)):
`|K_ℚ(MA[ℙ]1)(u) - K^sh_ℚ(MA[ℙ]1)(u)| ≤ κ log u/Λ` for `u ≥ X₀`. -/
theorem partial_windows_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {u : ℝ}
    (hu : (X0 : ℝ) ≤ u) :
    |KQ X0 (Construction.kappaParam X0) u - KshQ X0 (MAP X0 (Construction.kappaParam X0)) u| ≤
      Construction.kappaParam X0 * Real.log u / Real.log X0 := by
  classical
  set κ := Construction.kappaParam X0 with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hu0 : 0 < u := by linarith
  have hΛ0 : 0 < Real.log X0 := by linarith
  set M0 := ⌊u / X0⌋₊
  -- the difference per cofactor
  set D : ℕ → ℝ := fun m => MAPfrom (max X0 (Pplus m)) κ (u / m) / m -
    (if (Pplus m : ℝ) ≤ u / m then MAP X0 κ (u / m) / m else 0) with hD
  have hdiff : KQ X0 κ u - KshQ X0 (MAP X0 κ) u = ∑ m ∈ Icc 2 M0, D m := by
    unfold KQ KshQ; rw [← Finset.sum_sub_distrib]
  have hq : ∀ m ∈ Icc 2 M0, (X0 : ℝ) ≤ u / m ∧ (0 : ℝ) < m := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    refine ⟨?_, hm0⟩
    rw [le_div_iff₀ hm0]
    have : (m : ℝ) ≤ u / X0 :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))
    rw [le_div_iff₀ hX0] at this; linarith
  -- `D m = 0` for complete windows, and `D m ≥ 0`
  set S := (Icc 2 M0).filter (fun m => u / m < Pplus m ∧ (Pplus m : ℝ) ≤ (1 + κ) * (u / m))
    with hS
  have hDS : ∑ m ∈ Icc 2 M0, D m = ∑ m ∈ S, MAPfrom (max X0 (Pplus m)) κ (u / m) / m := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hqX, hm0⟩ := hq m hm
    simp only [hD]
    by_cases hc : (Pplus m : ℝ) ≤ u / m
    · rw [if_pos hc, if_neg (fun h => absurd hc (not_le.mpr h.1))]
      unfold MAPfrom MAP
      rw [newPrimeCount_eq_of_le hc]; ring
    · rw [if_neg hc, sub_zero]
      push_neg at hc
      by_cases hc2 : (Pplus m : ℝ) ≤ (1 + κ) * (u / m)
      · rw [if_pos ⟨hc, hc2⟩]
      · rw [if_neg (fun h => hc2 h.2)]
        push_neg at hc2
        unfold MAPfrom
        have hT : (1 + κ) * (u / m) < ((max X0 (Pplus m) : ℕ) : ℝ) :=
          lt_of_lt_of_le hc2 (by exact_mod_cast le_max_right _ _)
        rw [newPrimeCount_eq_zero_of_lt hT]; simp
  rw [hdiff, hDS]
  have hnn : 0 ≤ ∑ m ∈ S, MAPfrom (max X0 (Pplus m)) κ (u / m) / m := by
    apply Finset.sum_nonneg; intro m _
    unfold MAPfrom; positivity
  rw [abs_of_nonneg hnn]
  -- reindex `m = m'' p`, `p = P⁺(m)`
  set d : ℕ → ℕ → ℝ := fun m'' p => if (X0 : ℝ) ≤ u / (p * m'') then
    MAPfrom (max X0 p) κ (u / (p * m'')) else 0 with hd
  have hdb : ∀ m'' p, 0 ≤ d m'' p ∧ d m'' p ≤ 1.01 / Real.log X0 := by
    intro m'' p
    simp only [hd]
    split_ifs with hc
    · have hq0 : 0 < u / (p * m'') := lt_of_lt_of_le hX0 hc
      refine ⟨by unfold MAPfrom; positivity, ?_⟩
      have h1 : MAPfrom (max X0 p) κ (u / (p * m'')) ≤ MAP X0 κ (u / (p * m'')) := by
        unfold MAPfrom MAP
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast newPrimeCount_anti (le_max_left _ _) _ _ (by positivity)
      have h2 := MAP_le_of_ge hX hH hc
      have : 1.0001 / Real.log X0 ≤ 1.01 / Real.log X0 :=
        div_le_div_of_nonneg_right (by norm_num) hΛ0.le
      linarith
    · exact ⟨le_rfl, by positivity⟩
  set T := (Icc 1 ⌊u⌋₊).sigma (fun m'' => partialPs X0 κ u m'')
  set φ : ℕ → (Σ _ : ℕ, ℕ) := fun m => ⟨m / Pplus m, Pplus m⟩
  have hmemS : ∀ m ∈ S, 1 < m ∧ (Pplus m).Prime ∧ m / Pplus m * Pplus m = m := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hP := Pplus_mem (by omega : 1 < m)
    exact ⟨by omega, Nat.prime_of_mem_primeFactors hP,
      Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hP)⟩
  have hφT : ∀ m ∈ S, φ m ∈ T := by
    intro m hm
    obtain ⟨hm1, hpp, hmeq⟩ := hmemS m hm
    obtain ⟨hmI, hlt, hle⟩ := Finset.mem_filter.mp hm
    obtain ⟨hqX, hm0⟩ := hq m hmI
    set p := Pplus m
    set m'' := m / p
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hm''1 : 1 ≤ m'' := by
      rcases Nat.eq_zero_or_pos m'' with h | h
      · rw [h, zero_mul] at hmeq; omega
      · exact h
    have hm''0 : (0 : ℝ) < m'' := by exact_mod_cast hm''1
    have hmr : (m : ℝ) = m'' * p := by exact_mod_cast hmeq.symm
    simp only [φ, T, Finset.mem_sigma, Finset.mem_Icc, partialPs, Finset.mem_filter]
    have hmu : (m'' : ℝ) ≤ u := by
      have : (m : ℝ) ≤ u := by
        have := (hq m hmI).1
        rw [le_div_iff₀ hm0] at this; nlinarith
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
      have : (m'' : ℝ) ≤ m := by rw [hmr]; nlinarith
      linarith
    have hsq1 : Real.sqrt (u / m'') < p := by
      rw [Real.sqrt_lt' hp0, div_lt_iff₀ hm''0]
      rw [hmr, div_lt_iff₀ (by positivity)] at hlt
      nlinarith
    have hsq2 : (p : ℝ) ≤ Real.sqrt ((1 + κ) * u / m'') := by
      rw [Real.le_sqrt' hp0, le_div_iff₀ hm''0]
      rw [hmr] at hle
      rw [mul_div_assoc', le_div_iff₀ (by positivity)] at hle
      nlinarith
    refine ⟨⟨hm''1, Nat.le_floor hmu⟩, ⟨Nat.one_le_iff_ne_zero.mpr hpp.ne_zero, Nat.le_floor hsq2⟩,
      hsq1, hsq2, ?_⟩
    rw [show (p : ℝ) * m'' = m by rw [hmr]; ring]
    exact hqX
  have hinj : Set.InjOn φ S := by
    intro m1 hm1 m2 hm2 h
    simp only [φ, Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := (hmemS m1 hm1).2.2
    have e2 := (hmemS m2 hm2).2.2
    rw [← e1, ← e2, h1, eq_of_heq h2]
  have hval : ∀ m ∈ S, MAPfrom (max X0 (Pplus m)) κ (u / m) / m =
      d (φ m).1 (φ m).2 / ((φ m).2 * (φ m).1) := by
    intro m hm
    obtain ⟨hm1, hpp, hmeq⟩ := hmemS m hm
    have hmr : (m : ℝ) = (m / Pplus m : ℕ) * Pplus m := by exact_mod_cast hmeq.symm
    simp only [φ, hd]
    have hpm : ((Pplus m : ℕ) : ℝ) * ((m / Pplus m : ℕ) : ℝ) = m := by rw [hmr]; ring
    rw [hpm, if_pos (hq m (Finset.mem_filter.mp hm).1).1]
  calc ∑ m ∈ S, MAPfrom (max X0 (Pplus m)) κ (u / m) / m
      = ∑ x ∈ S.image φ, d x.1 x.2 / (x.2 * x.1) := by
        rw [Finset.sum_image hinj]; exact Finset.sum_congr rfl hval
    _ ≤ ∑ x ∈ T, d x.1 x.2 / (x.2 * x.1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
          exact hφT m hm
        · intro x _ _
          exact div_nonneg (hdb _ _).1 (by positivity)
    _ = ∑ m'' ∈ Icc 1 ⌊u⌋₊, ∑ p ∈ partialPs X0 κ u m'', d m'' p / (p * m'') := by
        rw [Finset.sum_sigma]
    _ ≤ κ * Real.log u / Real.log X0 := by
        have hκX : 100 ≤ κ * X0 := by
          have := BModel.window_long hX (le_refl (X0 : ℝ))
          have h7 : (100 : ℝ) ≤ (2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) := by
            have h2X : (10 ^ 12 : ℝ) ≤ 2 * X0 := by
              have := Real.pow_div_factorial_le_exp (Real.log X0) (by linarith) 2
              rw [Real.exp_log hX0] at this
              norm_num [Nat.factorial] at this
              nlinarith
            calc (100 : ℝ) = (10 ^ 12 : ℝ) ^ (1 / 6 : ℝ) := by
                  rw [show (10 ^ 12 : ℝ) = 100 ^ (6 : ℝ) by norm_num, ← Real.rpow_mul
                    (by norm_num)]; norm_num
              _ ≤ (2 * (X0 : ℝ)) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by norm_num) h2X (by norm_num)
              _ ≤ (2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          linarith
        have hlu : 2 ≤ Real.log u := by linarith [log_ge_of_ge hX hu]
        exact partial_correction_le hκ0 hX0 hκX (by linarith) hlu hΛ0 d hdb

/-! ### Linearity -/

variable (P : BeurlingSystem)

lemma Kpt_add (tw : ℕ → ℝ) (X0m : ℝ) (g1 g2 : ℝ → ℝ) (y : ℝ) :
    KR.Sharp.Kpt P tw X0m (fun z => g1 z + g2 z) y =
      KR.Sharp.Kpt P tw X0m g1 y + KR.Sharp.Kpt P tw X0m g2 y := by
  classical
  unfold KR.Sharp.Kpt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

lemma Rsh_add (tw : ℕ → ℝ) (X0m : ℝ) (g1 g2 : ℝ → ℝ) (y : ℝ) :
    KR.Sharp.Rsh P tw X0m (fun z => g1 z + g2 z) y =
      KR.Sharp.Rsh P tw X0m g1 y + KR.Sharp.Rsh P tw X0m g2 y := by
  unfold KR.Sharp.Rsh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma KshQ_add (X0 : ℕ) (h1 h2 : ℝ → ℝ) (x : ℝ) :
    KshQ X0 (fun q => h1 q + h2 q) x = KshQ X0 h1 x + KshQ X0 h2 x := by
  classical
  unfold KshQ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

/-! ### The realised `μ₀` and the decomposition (86) -/

/-- `MA[ℙ] 1_{[X₀,∞)}`. -/
noncomputable def MAPcut (X0 : ℕ) (u : ℝ) : ℝ :=
  if (X0 : ℝ) ≤ u then MAP X0 (Construction.kappaParam X0) u else 0

/-- `f₀ 1_{[X₀,∞)}`. -/
noncomputable def f0cut (X0 : ℕ) (u : ℝ) : ℝ :=
  if (X0 : ℝ) ≤ u then f0 X0 (Construction.kappaParam X0) u else 0

/-- The source of the base range, `S = (1 - ρ_det) 1_{[X₀,∞)}` (`T'_cont - R' + ρ̄_𝒜`). -/
noncomputable def srcBase (X0 : ℕ) (u : ℝ) : ℝ :=
  if (X0 : ℝ) ≤ u then 1 - Target.rhoDet X0 (Construction.kappaParam X0) u else 0

/-- **The realised smooth part** `μ₀ = S - (1 + K_pt)(MA[ℙ]1) - μ_edge - μ₁` of §7.2. -/
noncomputable def mu0R (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (u : ℝ) : ℝ :=
  srcBase X0 u - MAPcut X0 u - KR.Sharp.Kpt P tw X0m (MAPcut X0) u -
    muEdge X0 (Construction.kappaParam X0) u - KR.Sharp.mu1R P tw X0m X0 u

lemma src_eq (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) :
    srcBase X0 = fun u => (MAPcut X0 u + KR.Sharp.Kpt P tw X0m (MAPcut X0) u) +
      muEdge X0 (Construction.kappaParam X0) u + mu0R P tw X0m X0 u +
        KR.Sharp.mu1R P tw X0m X0 u := by
  funext u; unfold mu0R; ring

/-- **The decomposition (86)** (`eq:shdecomp`) for the realised system: for `y ≥ X₀⁻ > 0`,
`ρ^sh(y) = MA[ℙ]1(y) + ρ_edge(y) + R_sh μ₀(y) + R_sh μ₁(y)`, `ρ^sh = R_sh S`. -/
theorem shdecomp (tw : ℕ → ℝ) {X0m : ℝ} (hXm : 0 < X0m) (X0 : ℕ) {y : ℝ} (hy : X0m ≤ y) :
    KR.Sharp.Rsh P tw X0m (srcBase X0) y = MAPcut X0 y + KR.Sharp.rhoEdge P tw X0m X0 y +
      KR.Sharp.Rsh P tw X0m (mu0R P tw X0m X0) y +
        KR.Sharp.Rsh P tw X0m (KR.Sharp.mu1R P tw X0m X0) y := by
  rw [src_eq P tw X0m X0, Rsh_add, Rsh_add, Rsh_add,
    KR.Sharp.Rsh_one_add_Kpt P tw hXm hy (MAPcut X0)]
  rfl

lemma Kpt_zero_below (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} {g : ℝ → ℝ}
    (hg : ∀ z : ℝ, z < X0 → g z = 0) {u : ℝ} (hu : u < X0) (hu0 : 0 ≤ u) :
    KR.Sharp.Kpt P tw X0m g u = 0 := by
  classical
  unfold KR.Sharp.Kpt
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs
  · rw [hg _ (lt_of_le_of_lt (div_le_self hu0
      (LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r))) hu), zero_div]
  · rfl

lemma muEdge_zero_below {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u : ℝ} (hu : u < X0) :
    muEdge X0 (Construction.kappaParam X0) u = 0 := by
  unfold muEdge
  refine Finset.sum_eq_zero fun N hN => ?_
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hN).1
  unfold edgeTerm
  rw [if_neg]
  rintro ⟨h1, -⟩
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  have hN0 : (0 : ℝ) < N := by linarith
  rw [div_lt_div_iff₀ (by linarith) hN0] at h1
  nlinarith

/-- `μ₁ = 0` below `X₀`. -/
lemma mu1R_zero_below (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} {u : ℝ}
    (hu : u < X0) (hu0 : 0 ≤ u) : KR.Sharp.mu1R P tw X0m X0 u = 0 := by
  have hX0 : (0 : ℝ) < X0 := by linarith
  unfold KR.Sharp.mu1R
  have h1 : KshQ X0 (f1 X0 (Construction.kappaParam X0)) u = 0 := by
    unfold KshQ
    rw [Finset.Icc_eq_empty, Finset.sum_empty]
    have : ⌊u / X0⌋₊ = 0 := Nat.floor_eq_zero.mpr (by rw [div_lt_one hX0]; exact hu)
    omega
  have h2 : KR.Sharp.Kpt P tw X0m (KR.Sharp.f1cut X0) u = 0 :=
    Kpt_zero_below P tw X0m (fun z hz => by unfold KR.Sharp.f1cut; rw [if_neg (not_le.mpr hz)])
      hu hu0
  rw [h1, h2, sub_zero]

/-- `μ₀ = 0` below `X₀`. -/
lemma mu0R_zero_below (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u : ℝ}
    (hu : u < X0) (hu0 : 0 ≤ u) : mu0R P tw X0m X0 u = 0 := by
  unfold mu0R
  rw [mu1R_zero_below P tw X0m hu hu0, muEdge_zero_below hX hu,
    Kpt_zero_below P tw X0m (fun z hz => by unfold MAPcut; rw [if_neg (not_le.mpr hz)]) hu hu0]
  simp [srcBase, MAPcut, not_le.mpr hu]

/-- **The split of `μ₀`** on `[X₀, ∞)` (§7.2). -/
theorem mu0R_split (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) {u : ℝ} (hu : (X0 : ℝ) ≤ u) :
    mu0R P tw X0m X0 u =
      (1 - Target.rhoDet X0 (Construction.kappaParam X0) u -
        (MAP X0 (Construction.kappaParam X0) u + KQ X0 (Construction.kappaParam X0) u +
          muEdge X0 (Construction.kappaParam X0) u)) +
      (KQ X0 (Construction.kappaParam X0) u -
        KshQ X0 (MAP X0 (Construction.kappaParam X0)) u) +
      (KshQ X0 (f0 X0 (Construction.kappaParam X0)) u -
        KR.Sharp.Kpt P tw X0m (f0cut X0) u) := by
  have hcut : MAPcut X0 = fun z => f0cut X0 z + KR.Sharp.f1cut X0 z := by
    funext z; unfold MAPcut f0cut KR.Sharp.f1cut f1; split_ifs <;> ring
  have hmap : MAP X0 (Construction.kappaParam X0) =
      fun q => f0 X0 (Construction.kappaParam X0) q + f1 X0 (Construction.kappaParam X0) q := by
    funext q; unfold f1; ring
  have hK : KR.Sharp.Kpt P tw X0m (MAPcut X0) u =
      KR.Sharp.Kpt P tw X0m (f0cut X0) u + KR.Sharp.Kpt P tw X0m (KR.Sharp.f1cut X0) u := by
    rw [hcut, Kpt_add]
  have hS : KshQ X0 (MAP X0 (Construction.kappaParam X0)) u =
      KshQ X0 (f0 X0 (Construction.kappaParam X0)) u +
        KshQ X0 (f1 X0 (Construction.kappaParam X0)) u := by
    conv_lhs => rw [hmap]
    rw [KshQ_add]
  unfold mu0R KR.Sharp.mu1R
  simp only [srcBase, MAPcut, if_pos hu]
  rw [hK, hS]
  ring

/-! ### Lemma 7.3(b) -/

/-- **Named hypothesis: Steps 1–3 of the proof of Lemma 7.3(b) and the decision-order
mismatch** ("the rest", corrections #53, #99), on `Good(<xmax)`: for `X₀ ≤ u ≤ xmax`,
`|(K^sh_ℚ - K_pt)(f₀ 1_{[X₀,∞)})(u)| ≤ (1 + 10⁻³) κ (log u)³`. The paper bounds the symmetric
telescoping `(K^val_pt - K^sh_ℚ)(f₀1)` by `7.4 κ (log u)³/Λ ≤ κ (log u)³` (Step 3, from
`|ψ_𝒩 - ψ| ≤ 5κ t log² t` on `[1, √u]`, Step 2, from `|N_𝒩 - ⌊·⌋| ≤ δ`, Step 1) and the
decision-order mismatch `(K_pt - K^val_pt)(f₀1)` by `10⁻³ κ (log u)³`. -/
def Lemma73bCore (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (xmax : ℝ) : Prop :=
  ∀ u : ℝ, (X0 : ℝ) ≤ u → u ≤ xmax →
    |KshQ X0 (f0 X0 (Construction.kappaParam X0)) u - KR.Sharp.Kpt P tw X0m (f0cut X0) u| ≤
      (1 + 1 / 10 ^ 3) * Construction.kappaParam X0 * Real.log u ^ 3

/-- **Lemma 7.3(b)** for the realised `μ₀`, from `Lemma73bCore`, (84), the rational identity
(85) (`ratid`) and the partial windows (`partial_windows_le`). `X₀` is even (§2), so not prime. -/
theorem lemma73b_of {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
    (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime) {xmax : ℝ} (hcore : Lemma73bCore P tw X0m X0 xmax) :
    Lemma73b X0 xmax (mu0R P tw X0m X0) := by
  intro u hu hux
  set κ := Construction.kappaParam X0 with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hu0 : 0 < u := by linarith
  have hX2 : 2 ≤ X0 := by
    have : (2 : ℝ) ≤ X0 := by
      have := Real.add_one_le_exp (Real.log X0); rw [Real.exp_log hX0] at this; linarith
    exact_mod_cast this
  have hL := log_ge_of_ge hX hu
  have hΛ0 : 0 < Real.log X0 := by linarith
  rw [mu0R_split P tw X0m X0 hu]
  have h1 := ratid hX2 hXp hκ0 hκ1 hu
  have h2 := partial_windows_le hX hH hu
  have h3 := hcore u hu hux
  -- `1/(κu) ≤ 10⁻³ κ (log u)³` and `κ log u/Λ ≤ 10⁻³ κ (log u)³`
  have hκ2 : 1000 ≤ κ * κ * u := by
    have hlow : (2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) ≤ κ * X0 := BModel.window_long hX le_rfl
    have hκX : κ * X0 ≤ κ * u := mul_le_mul_of_nonneg_left hu hκ0.le
    -- `κ² X₀ = X₀^{0.2067}` is huge
    have e : κ * κ * X0 = Real.exp ((2 * (-5 / 12 + 2 * 0.01) + 1) * Real.log X0) := by
      rw [hκdef, kappa_eq_exp hX0, ← Real.exp_add, ← Real.exp_log hX0, ← Real.exp_add,
        Real.log_exp]
      congr 1; ring
    have hbig : 1000 ≤ κ * κ * X0 := by
      rw [e]
      have := Real.add_one_le_exp ((2 * (-5 / 12 + 2 * 0.01) + 1) * Real.log X0)
      nlinarith
    nlinarith
  have hL3 : 1 ≤ Real.log u ^ 3 := one_le_pow₀ (by linarith)
  have hK3 : 0 ≤ κ * Real.log u ^ 3 := by positivity
  have hA : 1 / (κ * u) ≤ 1 / 10 ^ 3 * κ * Real.log u ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 10 ^ 3 * κ * Real.log u ^ 3 * (κ * u) =
        1 / 10 ^ 3 * (κ * κ * u) * Real.log u ^ 3 := by ring
    rw [e]
    have : 1 / 10 ^ 3 * 1000 * 1 ≤ 1 / 10 ^ 3 * (κ * κ * u) * Real.log u ^ 3 :=
      mul_le_mul (by linarith) hL3 (by norm_num) (by positivity)
    linarith
  have hB : κ * Real.log u / Real.log X0 ≤ 1 / 10 ^ 3 * κ * Real.log u ^ 3 := by
    rw [div_le_iff₀ hΛ0]
    have h1 : κ * Real.log u ≤ κ * Real.log u ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hκ0.le
      have : 1 ≤ Real.log u ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    have h2 : κ * Real.log u ^ 3 ≤ 1 / 10 ^ 3 * κ * Real.log u ^ 3 * Real.log X0 := by
      have e : 1 / 10 ^ 3 * κ * Real.log u ^ 3 * Real.log X0 =
          (κ * Real.log u ^ 3) * (1 / 10 ^ 3 * Real.log X0) := by ring
      rw [e]
      exact le_mul_of_one_le_right hK3 (by linarith)
    linarith
  calc |_ + _ + _| ≤ |_| + |_| + |_| := abs_add_three _ _ _
    _ ≤ 1 / (κ * u) + κ * Real.log u / Real.log X0 + (1 + 1 / 10 ^ 3) * κ * Real.log u ^ 3 := by
        gcongr
    _ ≤ 2 * κ * Real.log u ^ 3 := by nlinarith

/-- **The realised inputs of Lemma 7.3** with `μ₀ = mu0R`, `μ₁ = mu1R`, `ρ_edge = rhoEdge`:
(c) and the edge expansion are proved; (b) is reduced to `Lemma73bCore`; (d)(iii) remains. -/
theorem lemma73Inputs_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : (X0 : ℝ) ≤ Z) {tw : ℕ → ℝ}
    (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p) {xmax : ℝ} (hZ : xmax / X0 ≤ Z)
    (hcore : Lemma73bCore P tw X0m X0 xmax)
    (hd : Lemma73diii X0 xmax (KR.Sharp.rhoEdge P tw X0m X0)) :
    Lemma73Inputs X0 xmax (mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) :=
  lemma73Inputs_realised P h hX hH hXm1 hXm2 hXZ ht hdec hdec2 hZ
    (lemma73b_of P hX hH hXp hcore) hd

end BaseRange
