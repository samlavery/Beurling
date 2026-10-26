module

public import RequestProject.Beurling.Zeros48.Elements

/-!
# The target below `a_k`: jumps and continuous part (proof of Lemma 4.8(ii))

The target (6) is `T = Ψ + #A + T_cont`, where `Ψ(x)` counts the `X₀`-smooth integers `≤ x`,
`#A` counts `A ∩ [0, x]` and `T_cont(x) = (x - X₀) - ∫_{X₀}^x ρ_det - ∫_{X₀}^x ρ̄_A + R(x) - R(X₀)`
for `x ≥ X₀` (`0` below `X₀`) (`target_eq_jump_add_cont`). With `N = Ψ + #A + #ℬ`
(`N_eq_psi_add_countA_add`) the lag is `D = #ℬ - T_cont` (`lag_eq_residual_sub_cont`).

Also: the residual elements lie above `X₀⁻ = X₀ - H(X₀)/2` (`residual_val_ge`), and measurable
versions of `ρ_det` and `ρ̄_A` agreeing with them on `[X₀, a]` (`rhoDetF`, `rhoAF`).
-/

@[expose] public section

open Set Finset MeasureTheory Construction Target Rankin Absorbed Decomp Oscillation CaplLink

namespace Zeros48

/-- The continuous part `T_cont` of the target (6) (`0` below `X₀`). -/
noncomputable def contPart (X₀ : ℕ) (κ : ℝ) (rhoA R : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < X₀ then 0 else
    (x - X₀) - (∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u) - (∫ u in (X₀ : ℝ)..x, rhoA u) + (R x - R X₀)

/-- Below `X₀ + 1` (with `X₀` itself `X₀`-smooth) every positive integer is `X₀`-smooth. -/
lemma smoothNumbersUpTo_eq_Icc {X₀ N : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers) (hN : N ≤ X₀) :
    Nat.smoothNumbersUpTo N X₀ = Finset.Icc 1 N := by
  ext n
  rw [Nat.mem_smoothNumbersUpTo, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mem_smoothNumbers.mp h2).1, h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases (h2.trans hN).lt_or_eq with h | h
    · exact Nat.mem_smoothNumbers_of_lt h1 h
    · rw [h]; exact hXs

lemma smoothCount_eq_floor {X₀ : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers) {x : ℝ}
    (hx : ⌊x⌋₊ ≤ X₀) : smoothCount X₀ x = ⌊x⌋₊ := by
  unfold smoothCount
  rw [smoothNumbersUpTo_eq_Icc hXs hx]
  simp

lemma countA_eq_zero_of_lt {A : Set ℕ} {c x : ℝ} (hc : 0 ≤ c) (hA : ∀ n ∈ A, c < n)
    (hx : x < c) :
    countA A x = 0 := by
  unfold countA
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [if_neg]
  intro hkA
  have h1 := hA k hkA
  have h2 : (k : ℝ) ≤ x := by
    rcases le_or_gt 0 x with h0 | h0
    · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans (Nat.floor_le h0)
    · rw [Nat.floor_of_nonpos h0.le] at hk
      have : k = 0 := by simpa using hk
      subst this
      push_cast at h1
      linarith
  linarith

/-- **The target splits into its jumps and its continuous part**: `T = Ψ + #A + T_cont` on
`ℝ`, if `X₀` is `X₀`-smooth and `A` lies above `X₀`. -/
theorem target_eq_jump_add_cont {X₀ : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers) {κ : ℝ} {A : Set ℕ}
    (hA : ∀ n ∈ A, (X₀ : ℝ) < n) (rhoA R : ℝ → ℝ) (x : ℝ) :
    target X₀ κ (countA A) rhoA R x =
      smoothCount X₀ x + countA A x + contPart X₀ κ rhoA R x := by
  unfold target contPart
  split_ifs with h
  · have hfl : ⌊x⌋₊ ≤ X₀ := (Nat.floor_le_floor h.le).trans (by simp)
    rw [smoothCount_eq_floor hXs hfl, countA_eq_zero_of_lt (Nat.cast_nonneg _) hA h]
    ring
  · have hX : smoothCount X₀ (X₀ : ℝ) = X₀ := by
      rw [smoothCount_eq_floor hXs (by simp)]; simp
    rw [hX]
    ring

/-- **The lag is the residual count minus the continuous part**: `D = #ℬ - T_cont` on `[0, ∞)`. -/
theorem lag_eq_residual_sub_cont {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}
    (h : RealisedOK M H U) (hXs : X₀ ∈ X₀.smoothNumbers)
    (hA : ∀ n ∈ realisedA M H U, (X₀ : ℝ) < n) {κ : ℝ} (rhoA R : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (realisedSystem M H U).N x - target X₀ κ (countA (realisedA M H U)) rhoA R x =
      ((residualLe h x).card : ℝ) - contPart X₀ κ rhoA R x := by
  rw [N_eq_psi_add_countA_add h hx, target_eq_jump_add_cont hXs hA rhoA R x]
  ring

/-- **The residual elements lie above `X₀⁻ = X₀ - H(X₀)/2`**: below `X₀⁻` the realised system is
`ℕ`, all of which is rigid. -/
theorem residual_val_ge {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ} (h : RealisedOK M (capH X₀) U)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (hXs : X₀ ∈ X₀.smoothNumbers)
    {e : ℕ →₀ ℕ} (he : e ∈ residual h) :
    (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ (realisedSystem M (capH X₀) U).val e := by
  set P := realisedSystem M (capH X₀) U
  by_contra hlt
  push_neg at hlt
  set v := P.val e
  have hv1 : 1 ≤ v := P.one_le_val e
  have hH0 := capH_nonneg (X₀ : ℝ) (X₀ : ℝ)
  have hvX : v < X₀ := by linarith
  have hA : ∀ n ∈ realisedA M (capH X₀) U, (X₀ : ℝ) < n := fun n hn => by
    have := (realisedA_large h hU hX hTlow hn).2
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    linarith
  have h1 := realised_floor_eq h hU hX hTlow hv1 hlt
  have h2 := N_eq_psi_add_countA_add h (x := v) (by linarith)
  have hfl : ⌊v⌋₊ ≤ X₀ := (Nat.floor_le_floor hvX.le).trans (by simp)
  rw [smoothCount_eq_floor hXs hfl, countA_eq_zero_of_lt (Nat.cast_nonneg _) hA hvX, h1] at h2
  have hmem : e ∈ residualLe h v := by
    simp only [residualLe, Finset.mem_filter, BeurlingSystem.mem_elems]
    exact ⟨le_rfl, he⟩
  have hpos : (1 : ℝ) ≤ (residualLe h v).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨e, hmem⟩
  linarith

/-! ### Measurable versions of `ρ_det` and `ρ̄_A` on `[X₀, a]` -/

/-- `ρ_det` as a finite sum of ramps, valid on `(0, a]`. -/
noncomputable def rhoDetF (X₀ : ℕ) (κ a u : ℝ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo ⌊(1 + κ) * a⌋₊ X₀,
    (Icc ((n : ℝ) / (1 + κ)) n).indicator (fun u => 1 / (κ * u)) u

lemma measurable_rhoDetF (X₀ : ℕ) (κ a : ℝ) : Measurable (rhoDetF X₀ κ a) := by
  unfold rhoDetF
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (measurable_const.div (measurable_const.mul measurable_id)).indicator measurableSet_Icc

lemma rhoDet_eq_rhoDetF (X₀ : ℕ) {κ a u : ℝ} (hκ : 0 < κ) (hu : 0 < u) (hua : u ≤ a) :
    rhoDet X₀ κ u = rhoDetF X₀ κ a u := by
  classical
  set Sb := Nat.smoothNumbersUpTo ⌊(1 + κ) * a⌋₊ X₀ with hSb
  have hset : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)) =
      Sb.filter (fun n : ℕ => u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u) := by
    ext n
    simp only [Finset.mem_filter, hSb, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : (n : ℝ) ≤ (1 + κ) * u :=
        (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
      refine ⟨⟨Nat.le_floor ?_, h2⟩, h3, h4⟩
      nlinarith
    · rintro ⟨⟨-, h2⟩, h3, h4⟩
      exact ⟨⟨Nat.le_floor h4, h2⟩, h3⟩
  unfold rhoDet rigidCount rhoDetF
  rw [hset]
  rw [div_eq_mul_one_div, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u
  · have hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n :=
      ⟨by rw [div_le_iff₀ (by linarith)]; linarith [hn.2], hn.1⟩
    rw [if_pos hn, Set.indicator_of_mem hmem]; simp
  · have hmem : u ∉ Icc ((n : ℝ) / (1 + κ)) n := by
      rintro ⟨h1, h2⟩
      apply hn
      refine ⟨h2, ?_⟩
      rw [div_le_iff₀ (by linarith)] at h1; linarith
    rw [if_neg hn, Set.indicator_of_notMem hmem]; simp

lemma rhoDet_nonneg (X₀ : ℕ) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) : 0 ≤ rhoDet X₀ κ u :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hu.le)

/-- A crude bound `ρ_det(u) ≤ 3/κ` for `u ≥ 1`, `κ ≤ 1`. -/
lemma rhoDet_le (X₀ : ℕ) {κ u : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hu : 1 ≤ u) :
    rhoDet X₀ κ u ≤ 3 / κ := by
  have hu0 : 0 < u := by linarith
  unfold rhoDet rigidCount
  have hcard : (((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter
      fun n : ℕ => u ≤ (n : ℝ)).card : ℝ) ≤ (1 + κ) * u + 1 := by
    have h1 : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter
        fun n : ℕ => u ≤ (n : ℝ)).card ≤ ⌊(1 + κ) * u⌋₊ + 1 := by
      refine (Finset.card_filter_le _ _).trans ?_
      unfold Nat.smoothNumbersUpTo
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊(1 + κ) * u⌋₊ : ℕ) : ℝ) ≤ (1 + κ) * u := Nat.floor_le (by positivity)
    calc _ ≤ ((⌊(1 + κ) * u⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ (1 + κ) * u + 1 := by push_cast; linarith
  rw [div_le_div_iff₀ (mul_pos hκ hu0) hκ]
  have h3 : (1 + κ) * u + 1 ≤ 3 * u := by nlinarith
  have := mul_le_mul_of_nonneg_right (hcard.trans h3) hκ.le
  linarith

/-- `ρ̄_A` with the sum over `A` truncated to `n ≤ 2a`, valid on `[1, a]`. -/
noncomputable def rhoAF (b : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (a v : ℝ) : ℝ :=
  min (∑ n ∈ Finset.range (⌊2 * a⌋₊ + 1), absorbedBump b A u n v) (0.1 / Real.log v)

lemma measurable_rhoAF (b : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (a : ℝ) : Measurable (rhoAF b A u a) := by
  unfold rhoAF
  refine Measurable.min (Finset.measurable_sum _ fun n _ => ?_)
    (measurable_const.div Real.measurable_log)
  unfold absorbedBump
  split_ifs
  · exact (measurable_id.pow_const _).indicator measurableSet_Icc
  · exact measurable_const

lemma absorbedDensityCap_eq_rhoAF {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {A : Set ℕ} {u : ℕ → ℝ}
    (hu : ∀ n ∈ A, 0 ≤ u n ∧ u n + u n ^ b = n) {a v : ℝ} (hv : 1 ≤ v) (hva : v ≤ a) :
    absorbedDensityCap b A u v = rhoAF b A u a v := by
  unfold absorbedDensityCap rhoAF absorbedDensity
  congr 1
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  unfold absorbedBump
  split_ifs with hA
  · rw [Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩
    obtain ⟨hu0, hue⟩ := hu n hA
    have h3 : u n ^ b ≤ v ^ b := Real.rpow_le_rpow hu0 h1 hb.le
    have h4 : v ^ b ≤ v := by
      calc v ^ b ≤ v ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv hb1
        _ = v := Real.rpow_one v
    have h5 : (n : ℝ) ≤ 2 * a := by linarith
    have h6 : (⌊2 * a⌋₊ + 1 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h7 : 2 * a < ⌊2 * a⌋₊ + 1 := Nat.lt_floor_add_one _
    push_cast at h6
    linarith
  · rfl

lemma absorbedDensityCap_nonneg {b : ℝ} {A : Set ℕ} {u : ℕ → ℝ} {v : ℝ} (hv : 1 < v) :
    0 ≤ absorbedDensityCap b A u v := by
  unfold absorbedDensityCap absorbedDensity
  refine le_min (tsum_nonneg fun n => absorbedBump_nonneg (X₀ := v) (by linarith) le_rfl) ?_
  exact div_nonneg (by norm_num) (Real.log_nonneg hv.le)

lemma absorbedDensityCap_le {b : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (v : ℝ) :
    absorbedDensityCap b A u v ≤ 0.1 / Real.log v := min_le_right _ _

end Zeros48

end
