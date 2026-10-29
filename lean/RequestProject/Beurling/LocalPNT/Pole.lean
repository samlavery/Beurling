module

public import RequestProject.Beurling.LocalPNT.Transfer

/-!
# Step 4 of the proof of Theorem 5.24: the pole term

`-ζ_J'/ζ_J(1+η) = ∑_{p_j ≤ y} ∑_{m ≥ 1} log p_j · p_j^{-m(1+η)}`. The prime powers `≤ y` contribute
`∫_{[1,y]} u^{-η} dS(u) ≤ 1/η + 0.43` by Lemma 5.1(ii) and partial summation, the others at most
`3 y^{-η}`. So `-ζ_J'/ζ_J(1+η) ≤ 1/η + 0.43 + 3y^{-η}` (`pole_le`).
-/

@[expose] public section

open Set Real MeasureTheory Finset Construction

namespace LocalPNT

/-- Real Abel summation for a finite family of points in `[1, y]`. -/
lemma abel_finset {ι : Type*} (s : Finset ι) (u w : ι → ℝ) {y η : ℝ}
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ y) (hη : 0 < η) :
    ∑ i ∈ s, w i * u i ^ (-η) = (∑ i ∈ s, w i) * y ^ (-η) +
      η * ∫ x in Ioc 1 y, ∑ i ∈ s, (Ici (u i)).indicator (fun x => w i * x ^ (-η - 1)) x := by
  classical
  have hint : ∀ i ∈ s, IntegrableOn
      (fun x => (Ici (u i)).indicator (fun x : ℝ => w i * x ^ (-η - 1)) x) (Ioc 1 y) := by
    intro i _
    refine IntegrableOn.indicator ?_ measurableSet_Ici
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1])))
  rw [integral_finset_sum _ hint, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h1, h2⟩ := hu i hi
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : (Ioc 1 y ∩ Ici (u i) : Set ℝ) =ᵐ[volume] (Ioc (u i) y : Set ℝ) := by
    rcases h1.lt_or_eq with h1 | h1
    · have : Ioc 1 y ∩ Ici (u i) = Icc (u i) y := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
      rw [this]; exact Ioc_ae_eq_Icc.symm
    · rw [← h1]
      have : Ioc 1 y ∩ Ici (1 : ℝ) = Ioc 1 y := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
        exact ⟨fun h => h.1, fun h => ⟨h, h.1.le⟩⟩
      rw [this]
  rw [setIntegral_congr_set hset, integral_const_mul, ← intervalIntegral.integral_of_le h2,
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le h2]; intro h0; linarith [h0.1]⟩)]
  rw [show -η - 1 + 1 = -η by ring]
  field_simp
  ring

/-- `∑_{k : p^{k+1} > y} p^{-(k+1)} ≤ 2/y` for `p ≥ 2`, `y > 0`. -/
lemma tsum_tail_inv_pow_le {p y : ℝ} (hp : 2 ≤ p) (hy : 0 < y) :
    Summable (fun k : ℕ => if y < p ^ (k + 1) then (p ^ (k + 1))⁻¹ else 0) ∧
    ∑' k : ℕ, (if y < p ^ (k + 1) then (p ^ (k + 1))⁻¹ else 0) ≤ 2 / y := by
  classical
  have hp0 : 0 < p := by linarith
  have hr : p⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
  have hr0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hgeom : Summable (fun k : ℕ => (p ^ (k + 1))⁻¹) := by
    have := (summable_geometric_of_lt_one hr0 (by linarith)).mul_left p⁻¹
    refine this.congr fun k => ?_
    rw [← inv_pow, pow_succ]; ring
  have hsum : Summable (fun k : ℕ => if y < p ^ (k + 1) then (p ^ (k + 1))⁻¹ else 0) :=
    hgeom.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> [exact le_rfl; positivity])
  refine ⟨hsum, ?_⟩
  have hex : ∃ k : ℕ, y < p ^ (k + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y (by linarith : (1 : ℝ) < p)
    exact ⟨n, hn.trans_le (pow_le_pow_right₀ (by linarith) (Nat.le_succ n))⟩
  set k₀ := Nat.find hex
  have hk₀ : y < p ^ (k₀ + 1) := Nat.find_spec hex
  have hmono : ∀ k, k₀ ≤ k → y < p ^ (k + 1) := fun k hk =>
    hk₀.trans_le (pow_le_pow_right₀ (by linarith) (by omega))
  rw [← hsum.sum_add_tsum_nat_add k₀]
  have hz : ∑ i ∈ Finset.range k₀, (if y < p ^ (i + 1) then (p ^ (i + 1))⁻¹ else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg]; exact Nat.find_min hex (Finset.mem_range.mp hi)
  rw [hz, zero_add]
  have he : ∀ i : ℕ, (if y < p ^ (i + k₀ + 1) then (p ^ (i + k₀ + 1))⁻¹ else 0) =
      (p ^ (k₀ + 1))⁻¹ * p⁻¹ ^ i := by
    intro i
    rw [if_pos (hmono _ (by omega)), show i + k₀ + 1 = (k₀ + 1) + i by ring, pow_add, mul_inv,
      inv_pow]
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
  have h1 : (1 - p⁻¹)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : (p ^ (k₀ + 1))⁻¹ ≤ y⁻¹ := inv_anti₀ hy hk₀.le
  calc (p ^ (k₀ + 1))⁻¹ * (1 - p⁻¹)⁻¹ ≤ y⁻¹ * 2 :=
        mul_le_mul h2 h1 (inv_nonneg.mpr (by linarith)) (inv_nonneg.mpr hy.le)
    _ = 2 / y := by ring

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `∫_1^y (log u + 0.43) η u^{-η-1} du + (log y + 0.43) y^{-η} = 1/η + 0.43 - y^{-η}/η`. -/
lemma integral_log_rpow {η : ℝ} (hη : 0 < η) (hy : 1 ≤ y) :
    η * ∫ x in Ioc 1 y, (Real.log x + 0.43) * x ^ (-η - 1) =
      1 / η + 0.43 - y ^ (-η) / η - (Real.log y + 0.43) * y ^ (-η) := by
  rw [← intervalIntegral.integral_of_le hy]
  have hderiv : ∀ x ∈ Set.uIcc 1 y, HasDerivAt
      (fun x : ℝ => -(Real.log x + 0.43) * x ^ (-η) / η - x ^ (-η) / η ^ 2)
      ((Real.log x + 0.43) * x ^ (-η - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hy] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 := Real.hasDerivAt_log hx0.ne'
    have h2 := Real.hasDerivAt_rpow_const (x := x) (p := -η) (Or.inl hx0.ne')
    have := (((h1.add_const 0.43).neg.mul h2).div_const η).sub (h2.div_const (η ^ 2))
    convert this using 1
    simp only [Pi.neg_apply, Pi.add_apply]
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
    ring
  have hcont : IntervalIntegrable (fun x : ℝ => (Real.log x + 0.43) * x ^ (-η - 1)) volume 1 y := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hy] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact ((Real.continuousAt_log hx0.ne').add continuousAt_const).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')) |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  simp only [Real.log_one, Real.one_rpow]
  field_simp
  ring

/-- **Step 4**: `∑_{p^k ≤ y} log p · p^{-k(1+η)} ≤ 1/η + 0.43`. -/
theorem pps_sum_le {η : ℝ} (hη : 0 < η) :
    ∑ jk ∈ P.pps y, Real.log (P.p jk.1) * (P.p jk.1 ^ (jk.2 + 1)) ^ (-(1 + η)) ≤ 1 / η + 0.43 := by
  have H := h.hbs
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  have hu : ∀ jk ∈ P.pps y, 1 ≤ P.p jk.1 ^ (jk.2 + 1) ∧ P.p jk.1 ^ (jk.2 + 1) ≤ y :=
    fun jk hjk => ⟨P.one_le_pow' _ _, (BeurlingSystem.mem_pps P).mp hjk⟩
  have e1 : ∀ jk ∈ P.pps y, Real.log (P.p jk.1) * (P.p jk.1 ^ (jk.2 + 1)) ^ (-(1 + η)) =
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) * (P.p jk.1 ^ (jk.2 + 1)) ^ (-η) := by
    intro jk _
    have hp : 0 < P.p jk.1 ^ (jk.2 + 1) := P.pp_pos jk
    rw [show -(1 + η) = -1 + -η by ring, Real.rpow_add hp, Real.rpow_neg_one]
    field_simp
  rw [Finset.sum_congr rfl e1, abel_finset (P.pps y) _ _ hu hη]
  -- `W(x) = S(x)` for `x ≤ y`
  have hW : ∀ x ∈ Ioc 1 y, ∑ jk ∈ P.pps y, (Ici (P.p jk.1 ^ (jk.2 + 1))).indicator
      (fun x => Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) * x ^ (-η - 1)) x =
      P.mertensS x * x ^ (-η - 1) := by
    intro x hx
    unfold BeurlingSystem.mertensS
    rw [Finset.sum_mul]
    have hsub : P.pps x = (P.pps y).filter (fun jk => P.p jk.1 ^ (jk.2 + 1) ≤ x) := by
      ext jk; simp only [BeurlingSystem.mem_pps, Finset.mem_filter]
      exact ⟨fun h => ⟨h.trans hx.2, h⟩, fun h => h.2⟩
    rw [hsub, Finset.sum_filter]
    refine Finset.sum_congr rfl fun jk _ => ?_
    by_cases hc : P.p jk.1 ^ (jk.2 + 1) ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ici _ from hc), if_pos hc]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ici _ from hc), if_neg hc]
  rw [setIntegral_congr_fun measurableSet_Ioc hW]
  have hS : ∀ x ∈ Ioc 1 y, P.mertensS x * x ^ (-η - 1) ≤ (Real.log x + 0.43) * x ^ (-η - 1) := by
    intro x hx
    have := (H.mertensS_sub_log_mem hx.1.le hx.2).2
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith [hx.1]) _)
  have hint2 : IntegrableOn (fun x : ℝ => (Real.log x + 0.43) * x ^ (-η - 1)) (Ioc 1 y) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact ((Real.continuousAt_log hx0.ne').add continuousAt_const).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')) |>.continuousWithinAt
  have hint1 : IntegrableOn (fun x : ℝ => P.mertensS x * x ^ (-η - 1)) (Ioc 1 y) := by
    have : IntegrableOn (fun x => ∑ jk ∈ P.pps y, (Ici (P.p jk.1 ^ (jk.2 + 1))).indicator
        (fun x => Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) * x ^ (-η - 1)) x) (Ioc 1 y) := by
      refine integrable_finset_sum _ fun jk _ => ?_
      refine IntegrableOn.indicator ?_ measurableSet_Ici
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      intro x hx
      exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [hx.1])))).continuousWithinAt
    exact this.congr_fun hW measurableSet_Ioc
  have hle := setIntegral_mono_on hint1 hint2 measurableSet_Ioc hS
  have hval := h.integral_log_rpow hη hy1
  have hSy := (H.mertensS_sub_log_mem hy1 le_rfl).2
  have hyη : 0 ≤ y ^ (-η) := Real.rpow_nonneg (by linarith) _
  have hSy' : (∑ jk ∈ P.pps y, Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1)) = P.mertensS y := rfl
  rw [hSy']
  have h1 : P.mertensS y * y ^ (-η) ≤ (Real.log y + 0.43) * y ^ (-η) :=
    mul_le_mul_of_nonneg_right (by linarith) hyη
  have h2 : η * ∫ x in Ioc 1 y, P.mertensS x * x ^ (-η - 1) ≤
      η * ∫ x in Ioc 1 y, (Real.log x + 0.43) * x ^ (-η - 1) :=
    mul_le_mul_of_nonneg_left hle hη.le
  have h3 : 0 ≤ y ^ (-η) / η := div_nonneg hyη hη.le
  linarith

/-- The real Dirichlet series of `-ζ_J'/ζ_J`: `G(j,k) = 1_{j ∈ J} log p_j (p_j^{k+1})^{-σ}`. -/
noncomputable def Gser (σ : ℝ) (jk : ℕ × ℕ) : ℝ :=
  if jk.1 ∈ P.primesLe y then Real.log (P.p jk.1) * (P.p jk.1 ^ (jk.2 + 1)) ^ (-σ) else 0

omit h in
lemma hasSum_Gser_fiber {σ : ℝ} (hσ : 0 < σ) (j : ℕ) (hj : j ∈ P.primesLe y) :
    HasSum (fun k => Gser (P := P) (y := y) σ (j, k))
      (Real.log (P.p j) * (P.p j ^ (-σ) / (1 - P.p j ^ (-σ)))) := by
  have hp0 := P.p_pos j
  have hq0 : 0 ≤ P.p j ^ (-σ) := Real.rpow_nonneg hp0.le _
  have hq1 : P.p j ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)
  have := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (P.p j ^ (-σ))).mul_left
    (Real.log (P.p j))
  convert this using 1
  · funext k
    simp only [Gser, if_pos hj]
    have e : (P.p j ^ (k + 1)) ^ (-σ) = (P.p j ^ (-σ)) ^ (k + 1) := by
      rw [← Real.rpow_natCast (P.p j), ← Real.rpow_mul hp0.le, mul_comm, Real.rpow_mul hp0.le,
        Real.rpow_natCast]
    rw [e, pow_succ']

omit h in
lemma Gser_nonneg {σ : ℝ} (jk : ℕ × ℕ) : 0 ≤ Gser (P := P) (y := y) σ jk := by
  unfold Gser; split_ifs
  · exact mul_nonneg (P.log_p_nonneg _) (Real.rpow_nonneg (P.pp_pos jk).le _)
  · exact le_rfl

omit h in
lemma summable_Gser {σ : ℝ} (hσ : 0 < σ) : Summable (Gser (P := P) (y := y) σ) := by
  refine (summable_prod_of_nonneg (fun jk => Gser_nonneg jk)).mpr ⟨fun j => ?_, ?_⟩
  · by_cases hj : j ∈ P.primesLe y
    · exact (hasSum_Gser_fiber hσ j hj).summable
    · have hj' : ¬ P.p j ≤ y := by simpa using hj
      simp only [Gser, BeurlingSystem.mem_primesLe, hj', if_false]; exact summable_zero
  · refine summable_of_ne_finset_zero (s := P.primesLe y) fun j hj => ?_
    have hj' : ¬ P.p j ≤ y := by simpa using hj
    simp [Gser, hj']

/-- **Step 4**: `-ζ_J'/ζ_J(1+η) = ∑_{p_j ≤ y} log p_j p_j^{-σ}/(1 - p_j^{-σ})`
`≤ 1/η + 0.43 + 3y^{-η}`. -/
theorem pole_le {η : ℝ} (hη : 0 < η) :
    ∑ j ∈ P.primesLe y, Real.log (P.p j) * (P.p j ^ (-(1 + η)) / (1 - P.p j ^ (-(1 + η)))) ≤
      1 / η + 0.43 + 3 * y ^ (-η) := by
  classical
  set σ := 1 + η
  have hσ : 0 < σ := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hS := summable_Gser (P := P) (y := y) hσ
  -- `∑' G = ∑_{j ∈ J} (fiber sums)`
  have htot : ∑' jk, Gser (P := P) (y := y) σ jk =
      ∑ j ∈ P.primesLe y, Real.log (P.p j) * (P.p j ^ (-σ) / (1 - P.p j ^ (-σ))) := by
    rw [hS.tsum_prod' (fun j => ?_)]
    · rw [tsum_eq_sum (s := P.primesLe y)]
      · exact Finset.sum_congr rfl fun j hj => (hasSum_Gser_fiber hσ j hj).tsum_eq
      · intro j hj
        have hj' : ¬ P.p j ≤ y := by simpa using hj
        simp [Gser, hj']
    · by_cases hj : j ∈ P.primesLe y
      · exact (hasSum_Gser_fiber hσ j hj).summable
      · have hj' : ¬ P.p j ≤ y := by simpa using hj
        simp only [Gser, BeurlingSystem.mem_primesLe, hj', if_false]; exact summable_zero
  rw [← htot]
  -- split along `pps y`
  set A := P.pps y
  have hAJ : ∀ jk ∈ A, jk.1 ∈ P.primesLe y := by
    intro jk hjk
    rw [BeurlingSystem.mem_primesLe]
    exact (le_self_pow₀ (P.one_lt _).le (Nat.succ_ne_zero _)).trans
      ((BeurlingSystem.mem_pps P).mp hjk)
  have hsplit : ∀ jk, Gser (P := P) (y := y) σ jk =
      (if jk ∈ A then Gser (P := P) (y := y) σ jk else 0) +
        (if jk ∈ A then 0 else Gser (P := P) (y := y) σ jk) := by
    intro jk; split_ifs <;> ring
  have hfinS : HasSum (fun jk => if jk ∈ A then Gser (P := P) (y := y) σ jk else 0)
      (∑ jk ∈ A, Gser (P := P) (y := y) σ jk) := by
    have : HasSum (fun jk => if jk ∈ A then Gser (P := P) (y := y) σ jk else 0)
        (∑ jk ∈ A, if jk ∈ A then Gser (P := P) (y := y) σ jk else 0) :=
      hasSum_sum_of_ne_finset_zero (fun jk hjk => by simp [hjk])
    convert this using 1
    exact Finset.sum_congr rfl fun jk hjk => by rw [if_pos hjk]
  have hrestS : Summable (fun jk => if jk ∈ A then 0 else Gser (P := P) (y := y) σ jk) :=
    hS.of_nonneg_of_le (fun jk => by split_ifs <;> [exact le_rfl; exact Gser_nonneg jk])
      (fun jk => by split_ifs <;> [exact Gser_nonneg jk; exact le_rfl])
  have hT : ∑' jk, Gser (P := P) (y := y) σ jk = ∑ jk ∈ A, Gser (P := P) (y := y) σ jk +
      ∑' jk, (if jk ∈ A then 0 else Gser (P := P) (y := y) σ jk) := by
    rw [← hfinS.tsum_eq, ← hfinS.summable.tsum_add hrestS]
    exact tsum_congr hsplit
  rw [hT]
  -- the finite part
  have hA : ∑ jk ∈ A, Gser (P := P) (y := y) σ jk ≤ 1 / η + 0.43 := by
    have := h.pps_sum_le hη
    refine le_of_eq_of_le (Finset.sum_congr rfl fun jk hjk => ?_) this
    simp only [Gser, if_pos (hAJ jk hjk), σ]
  -- the tail: majorant `y^{-η} 1_{j ∈ J, p^{k+1} > y} log p / p^{k+1}`
  set M : ℕ × ℕ → ℝ := fun jk => if jk.1 ∈ P.primesLe y then
    Real.log (P.p jk.1) * (if y < P.p jk.1 ^ (jk.2 + 1) then (P.p jk.1 ^ (jk.2 + 1))⁻¹ else 0)
    else 0
  have hMfib : ∀ j ∈ P.primesLe y, Summable (fun k => M (j, k)) ∧
      ∑' k, M (j, k) ≤ Real.log (P.p j) * (2 / y) := by
    intro j hj
    have h2 := h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)
    obtain ⟨hs, hle⟩ := tsum_tail_inv_pow_le h2 hy0
    simp only [M, if_pos hj]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hle (P.log_p_nonneg j)
  have hM0 : ∀ jk, 0 ≤ M jk := by
    intro jk; simp only [M]
    by_cases h1 : jk.1 ∈ P.primesLe y
    · rw [if_pos h1]
      apply mul_nonneg (P.log_p_nonneg _)
      split_ifs
      · exact inv_nonneg.mpr (P.pp_pos jk).le
      · exact le_rfl
    · rw [if_neg h1]
  have hMS : Summable M := by
    refine (summable_prod_of_nonneg hM0).mpr ⟨fun j => ?_, ?_⟩
    · by_cases hj : j ∈ P.primesLe y
      · exact (hMfib j hj).1
      · have hj' : ¬ P.p j ≤ y := by simpa using hj
        simp only [M, BeurlingSystem.mem_primesLe, hj', if_false]; exact summable_zero
    · refine summable_of_ne_finset_zero (s := P.primesLe y) fun j hj => ?_
      have hj' : ¬ P.p j ≤ y := by simpa using hj
      simp [M, hj']
  have hMtot : ∑' jk, M jk ≤ 2 * 1.42 := by
    rw [hMS.tsum_prod' (fun j => ?_)]
    · rw [tsum_eq_sum (s := P.primesLe y)]
      · calc ∑ j ∈ P.primesLe y, ∑' k, M (j, k) ≤ ∑ j ∈ P.primesLe y,
              Real.log (P.p j) * (2 / y) := Finset.sum_le_sum fun j hj => (hMfib j hj).2
          _ = 2 / y * ∑ j ∈ P.primesLe y, Real.log (P.p j) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ 2 / y * P.psi y := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [BeurlingSystem.psi_eq_sum]
              have hinj : ∀ j ∈ P.primesLe y, (j, 0) ∈ P.pps y := by
                intro j hj; simpa using (BeurlingSystem.mem_primesLe P).mp hj
              calc ∑ j ∈ P.primesLe y, Real.log (P.p j) =
                    ∑ jk ∈ (P.primesLe y).image (fun j => (j, 0)), Real.log (P.p jk.1) := by
                    rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
                _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                    (fun jk hjk => by
                      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk; exact hinj j hj)
                    (fun jk _ _ => P.log_p_nonneg _)
          _ ≤ 2 / y * (1.42 * y) := mul_le_mul_of_nonneg_left
              (h.hbs.psi_le hy0.le le_rfl) (by positivity)
          _ = 2 * 1.42 := by field_simp
      · intro j hj
        have hj' : ¬ P.p j ≤ y := by simpa using hj
        simp [M, hj']
    · by_cases hj : j ∈ P.primesLe y
      · exact (hMfib j hj).1
      · have hj' : ¬ P.p j ≤ y := by simpa using hj
        simp only [M, BeurlingSystem.mem_primesLe, hj', if_false]; exact summable_zero
  have hmaj : ∀ jk, (if jk ∈ A then 0 else Gser (P := P) (y := y) σ jk) ≤ y ^ (-η) * M jk := by
    intro jk
    by_cases hA' : jk ∈ A
    · rw [if_pos hA']; exact mul_nonneg (Real.rpow_nonneg hy0.le _) (hM0 jk)
    rw [if_neg hA']
    simp only [Gser, M]
    by_cases hj : jk.1 ∈ P.primesLe y
    · rw [if_pos hj, if_pos hj]
      have hgt : y < P.p jk.1 ^ (jk.2 + 1) := by
        by_contra hc; push_neg at hc; exact hA' ((BeurlingSystem.mem_pps P).mpr hc)
      rw [if_pos hgt]
      have hq := P.pp_pos jk
      have e : (P.p jk.1 ^ (jk.2 + 1)) ^ (-σ) =
          (P.p jk.1 ^ (jk.2 + 1)) ^ (-η) * (P.p jk.1 ^ (jk.2 + 1))⁻¹ := by
        rw [show -σ = -η + -1 by ring, Real.rpow_add hq, Real.rpow_neg_one]
      rw [e]
      have : (P.p jk.1 ^ (jk.2 + 1)) ^ (-η) ≤ y ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos hy0 hgt.le (by linarith)
      have hl := P.log_p_nonneg jk.1
      have hi : 0 ≤ (P.p jk.1 ^ (jk.2 + 1))⁻¹ := by positivity
      calc Real.log (P.p jk.1) * ((P.p jk.1 ^ (jk.2 + 1)) ^ (-η) * (P.p jk.1 ^ (jk.2 + 1))⁻¹)
          ≤ Real.log (P.p jk.1) * (y ^ (-η) * (P.p jk.1 ^ (jk.2 + 1))⁻¹) := by gcongr
        _ = _ := by ring
    · rw [if_neg hj, if_neg hj]; simp
  have hrest : ∑' jk, (if jk ∈ A then 0 else Gser (P := P) (y := y) σ jk) ≤ y ^ (-η) * 2.84 := by
    calc _ ≤ ∑' jk, y ^ (-η) * M jk := hrestS.tsum_le_tsum hmaj (hMS.mul_left _)
      _ = y ^ (-η) * ∑' jk, M jk := tsum_mul_left
      _ ≤ y ^ (-η) * 2.84 := mul_le_mul_of_nonneg_left (by linarith)
          (Real.rpow_nonneg hy0.le _)
  have hyη : 0 ≤ y ^ (-η) := Real.rpow_nonneg hy0.le _
  linarith

end LPHyp

end LocalPNT

end
