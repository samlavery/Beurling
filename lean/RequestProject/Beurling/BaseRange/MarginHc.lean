module

public import RequestProject.Beurling.Noise.MarginRealLoc
public import RequestProject.Beurling.BaseRange.Window
public import RequestProject.Beurling.Model.Choices

/-!
# Proposition 5.38(c) (Step 6(c)): the source bounds on `[X₀, 2X₀)`

The field `hc` of `BModel.RealMarginLoc`. For `X₀ ≤ t < 2X₀`:

* `TpCont_eq_low` : `T'_cont(t) = 1 - ρ_det(t)` (`𝒜 = ∅` there, `absDenCap_zero_low`, and
  `R' = 0` below the first switch-on point `exp(X₀²)`, `deriv_osc_zero_low`);
* `one_sub_rhoDet_le_low` : `1 - ρ_det(y) ≤ MA[ℙ](y) + 1/(κy) ≤ 1.000002/Λ` near `X₀`;
* `slotSum_le` : the box weight at `y ∈ [X₀⁻, X₀)` of the decided primes is
  `≤ (∫_{X₀}^{X₀+H/2+1/8} T'_cont + 1)/H(X₀) ≤ 0.50001/Λ` (the slot count of `placed_gap`);
* `compDen_le_low` : the compensator density is `≤ ½ × (that box weight at t/2)`, as only the
  cofactor `w = 2` has `t/w ≥ X₀⁻`;
* `margin_hc` : **the field `hc`**: `m(t) = T'_cont(t) - r/2` with
  `T'_cont(t) ≥ (0.99 - 10⁻⁹)/log t` (`one_sub_rhoDet_ge_099`), `r ≤ 0.5001/Λ`,
  `log t ≤ Λ + 0.7`.

Also `jzX_le` : `j₀ = jzX X₀ ≤ 1.0001/Λ` (this is `BaseRange.jz_le`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6 BModel
open scoped ENNReal

namespace BaseRange

variable {θ : ℝ} {X₀ : ℕ}

/-- **`j₀ ≤ 1.0001/Λ`**: `jzX X₀ = 1 - ρ_det(X₀)` is the left side of `jz_le`. -/
theorem jzX_le (hX : 10 ^ 8 ≤ Real.log X₀) (hH : HuxleyFrom X₀) :
    jzX X₀ ≤ 1.0001 / Real.log X₀ := by
  unfold jzX; exact jz_le hX hH

/-! ### `T'_cont` below `2X₀` -/

lemma switchOn_ge (X : ℝ) : ∀ k, switchOn X 0 ≤ switchOn X k
  | 0 => le_rfl
  | k + 1 => by
      have := switchOn_ge X k
      show switchOn X 0 ≤ Real.exp (switchOn X k)
      linarith [Real.add_one_le_exp (switchOn X k)]

lemma two_X0_lt_switchOn (hX : 10 ^ 8 ≤ Real.log X₀) :
    2 * (X₀ : ℝ) < switchOn (X₀ : ℝ) 0 := by
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  show 2 * (X₀ : ℝ) < Real.exp ((X₀ : ℝ) ^ 2)
  have h3 : (3 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀); rw [Real.exp_log hX0] at this; linarith
  have := Real.add_one_le_exp ((X₀ : ℝ) ^ 2)
  nlinarith

/-- `R = 0` on `(0, exp(X₀²))`, so `R' = 0` there. -/
lemma deriv_osc_zero_low (α γ : ℕ → ℝ) {y : ℝ} (hy0 : 0 < y)
    (hy : y < switchOn (X₀ : ℝ) 0) :
    deriv (Oscillation.osc θ α γ (switchOn X₀)) y = 0 := by
  have hev : Oscillation.osc θ α γ (switchOn X₀) =ᶠ[nhds y] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hy0 hy] with x hx
    unfold Oscillation.osc
    have hxp : ∀ k, 0 < switchOn (X₀ : ℝ) k := fun k =>
      lt_of_lt_of_le (Real.exp_pos _) (switchOn_ge (X₀ : ℝ) k)
    refine (tsum_congr fun k => ?_).trans tsum_zero
    unfold Oscillation.oscTerm
    rw [Real.smoothTransition.zero_of_nonpos, mul_zero]
    apply Real.log_nonpos (div_pos hx.1 (hxp k)).le
    rw [div_le_one (hxp k)]
    exact (hx.2.le.trans (switchOn_ge _ k))
  rw [hev.deriv_eq]; simp

/-- **`𝒜` is empty below `2X₀`**: the capped absorbed density vanishes on `[X₀, 2X₀)`. -/
lemma absDenCap_zero_low (hc : Cond θ X₀) (ω : JitterΩ) {y : ℝ} (hy0 : (X₀ : ℝ) ≤ y)
    (hy : y < 2 * X₀) :
    absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) y = 0 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hb : 0 < thetaB θ := thetaB_pos (by linarith [hc.hθ.1])
  have hb1 : thetaB θ ≤ 1 := (thetaB_le_quarter (by linarith [hc.hθ.2])).trans (by norm_num)
  have hzero : absorbedDensity (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) y = 0 := by
    unfold absorbedDensity
    refine (tsum_congr fun a => ?_).trans tsum_zero
    unfold absorbedBump
    split_ifs with ha
    · rw [Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      obtain ⟨-, e, -, -, -, k, -, -, hk⟩ := ha
      have ha0 : 0 ≤ a := by linarith
      obtain ⟨hu0, hu⟩ := solveU_spec hb ha0
      have hu1 : uA θ a = solveU (thetaB θ) a := rfl
      rw [← hu1] at hu0 hu
      have hub : uA θ a ^ (thetaB θ) ≤ 2 * X₀ := by
        rcases le_or_gt 1 (uA θ a) with h | h
        · calc uA θ a ^ (thetaB θ) ≤ uA θ a ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h hb1
            _ = uA θ a := Real.rpow_one _
            _ ≤ 2 * X₀ := by linarith
        · have : uA θ a ^ (thetaB θ) ≤ 1 := Real.rpow_le_one hu0 h.le hb.le
          have : (1 : ℝ) ≤ 2 * X₀ := by linarith [one_lt_of_log hX]
          linarith
      have ha4 : a ≤ 4 * X₀ := by linarith
      -- `y(a) < X₀⁻ ≤ v_k`
      have hvk : Xm X₀ ≤ (DF θ X₀ ω).v k := valF_ge_Xm hc k ω
      set m := max (X₀ : ℝ) a
      have hXm' : (X₀ : ℝ) ≤ m := le_max_left _ _
      have hm4 : m ≤ 4 * X₀ := max_le (by linarith) ha4
      set z := dyadicScale (X₀ : ℝ) m
      have hz1 : (X₀ : ℝ) ≤ z := le_dyadicScale hX0 hXm'
      have hz2 : z ≤ m := dyadicScale_le hX0 (by linarith)
      have hlogz : Real.log z ≤ Real.log X₀ ^ 2 := by
        have h1 : Real.log z ≤ Real.log (4 * X₀) := Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul (by norm_num) hX0.ne'] at h1
        have : Real.log 4 < 2 := by
          have := Real.log_two_lt_d9
          have e : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
          linarith
        nlinarith
      have := AbsorbEmpty.absorbYAt_lt hX0.le hX hz1 hlogz
      have e : AbsorbEmpty.absorbY (X₀ : ℝ) a = AbsorbEmpty.absorbYAt (X₀ : ℝ) z := rfl
      unfold Xm at hvk
      linarith
    · rfl
  unfold absorbedDensityCap
  rw [hzero]
  apply min_eq_left
  have : 0 < Real.log y := Real.log_pos (by linarith [one_lt_of_log hX])
  positivity

/-- **`T'_cont = 1 - ρ_det` on `[X₀, 2X₀)`**. -/
lemma TpCont_eq_low (hc : Cond θ X₀) (ω : JitterΩ) {y : ℝ} (hy0 : (X₀ : ℝ) ≤ y)
    (hy : y < 2 * X₀) :
    TpCont θ X₀ ω y = 1 - Target.rhoDet X₀ (kappaParam X₀) y := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  unfold TpCont
  rw [if_pos hy0, absDenCap_zero_low hc ω hy0 hy,
    deriv_osc_zero_low _ _ (by linarith) (lt_trans hy (two_X0_lt_switchOn hX))]
  ring

/-! ### `1 - ρ_det` near `X₀` -/

/-- Every integer of `[y, (1+κ)y]`, `X₀ ≤ y`, `(1+κ)y < 2X₀`, is `X₀`-smooth or a new prime. -/
lemma windowInts_subset_low {X0 : ℕ} {κ y : ℝ} (hX : 1 ≤ X0) (hκ : 0 < κ) (hy : (X0 : ℝ) ≤ y)
    (hy2 : (1 + κ) * y < 2 * X0) :
    windowInts κ y ⊆ rigidSet X0 κ y ∪ newSet X0 κ y := by
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hyn : y ≤ (n : ℝ) := Nat.ceil_le.mp hn'.1
  have hX0 : (1 : ℝ) ≤ X0 := by exact_mod_cast hX
  have hκy : 0 ≤ (1 + κ) * y := by nlinarith
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnb : (n : ℝ) ≤ (1 + κ) * y := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hκy)
  by_cases hs : ∀ p ∈ n.primeFactorsList, p < X0
  · refine Finset.mem_union_left _ ?_
    simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers]
    exact ⟨⟨hn'.2, by omega, hs⟩, hyn⟩
  · push_neg at hs
    obtain ⟨p, hp, hpX⟩ := hs
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_primeFactorsList hp
    have hk : k = 1 := by
      by_contra hk1
      have hk0 : k ≠ 0 := by rintro rfl; simp at hn1
      have hk2 : 2 ≤ k := by omega
      have h1 : (2 * X0 : ℝ) ≤ ((p * k : ℕ) : ℝ) := by
        push_cast
        have : (X0 : ℝ) ≤ p := by exact_mod_cast hpX
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith
      linarith
    subst hk
    refine Finset.mem_union_right _ ?_
    simp only [newSet, Finset.mem_filter, mul_one]
    exact ⟨by simpa using hn, hpp, hpX⟩

/-- `1 - ρ_det(y) ≤ MA[ℙ](y) + 1/(κy)` for `X₀ ≤ y`, `(1+κ)y < 2X₀`. -/
lemma one_sub_rhoDet_le_MAP {X0 : ℕ} {κ y : ℝ} (hκ : 0 < κ) (hX : 1 ≤ X0)
    (hy : (X0 : ℝ) ≤ y) (hy2 : (1 + κ) * y < 2 * X0) :
    1 - Target.rhoDet X0 κ y ≤ MAP X0 κ y + 1 / (κ * y) := by
  have hX0 : (1 : ℝ) ≤ X0 := by exact_mod_cast hX
  have hy0 : 0 < y := by linarith
  have hκy := mul_pos hκ hy0
  have hcard : (windowInts κ y).card ≤ (rigidSet X0 κ y).card + (newSet X0 κ y).card :=
    (Finset.card_le_card (windowInts_subset_low hX hκ hy hy2)).trans (Finset.card_union_le _ _)
  have hlow : κ * y - 1 ≤ ((windowInts κ y).card : ℝ) := by
    rw [windowInts, Nat.card_Icc]
    have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
    have h2 : (1 + κ) * y - 1 < (⌊(1 + κ) * y⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    rcases Nat.lt_or_ge (⌊(1 + κ) * y⌋₊ + 1) ⌈y⌉₊ with h | h
    · have : ((⌊(1 + κ) * y⌋₊ + 1 : ℕ) : ℝ) < ⌈y⌉₊ := by exact_mod_cast h
      push_cast at this
      have : κ * y - 1 < 0 := by linarith
      have : (0 : ℝ) ≤ ((⌊(1 + κ) * y⌋₊ + 1 - ⌈y⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [Nat.cast_sub h]; push_cast; linarith
  have hc : κ * y - 1 ≤ ((rigidSet X0 κ y).card : ℝ) + (newSet X0 κ y).card := by
    refine hlow.trans ?_; exact_mod_cast hcard
  unfold Target.rhoDet MAP
  rw [rigidCount_eq, newPrimeCount_eq_card X0 (by positivity)]
  have key : 1 ≤ (((rigidSet X0 κ y).card : ℝ) + (newSet X0 κ y).card + 1) / (κ * y) := by
    rw [le_div_iff₀ hκy]; linarith
  have e : (((rigidSet X0 κ y).card : ℝ) + (newSet X0 κ y).card + 1) / (κ * y) =
      ((rigidSet X0 κ y).card : ℝ) / (κ * y) + (newSet X0 κ y).card / (κ * y) + 1 / (κ * y) := by
    ring
  linarith

/-- **`T'_cont ≤ 1.000002/Λ` on `[X₀, X₀ + X₀/2]`** (from (huxley) via Lemma 7.3(a)). -/
lemma TpCont_le_low (hc : Cond θ X₀) (hH : HuxleyFrom X₀) (ω : JitterΩ) {y : ℝ}
    (hy0 : (X₀ : ℝ) ≤ y) (hy : y ≤ 3 / 2 * X₀) :
    TpCont θ X₀ ω y ≤ 1.000002 / Real.log X₀ := by
  have hX := hc.hX
  set κ := kappaParam (X₀ : ℝ)
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hκs : κ ≤ 1 / 10 ^ 21 := kappa_le_tiny hX0 hX
  have hy2 : (1 + κ) * y < 2 * X₀ := by nlinarith
  rw [TpCont_eq_low hc ω hy0 (by linarith)]
  have h1 := one_sub_rhoDet_le_MAP hκ0 (by exact_mod_cast hX1.le) hy0 hy2
  have h2 := (lemma_7_3_a hX hH hy0).2
  have hL : Real.log X₀ ≤ Real.log y := Real.log_le_log hX0 hy0
  have hΛ : 0 < Real.log X₀ := by linarith
  have hε : Real.log y ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le (hX.trans hL)
  -- `MA[ℙ](y) ≤ (1 + 10⁻²⁴)/Λ`
  have hMAP : MAP X₀ κ y ≤ (1 + 1 / 10 ^ 24) / Real.log X₀ := by
    have hMAP0 : 0 ≤ MAP X₀ κ y := MAP_nonneg X₀ hκ0.le (by linarith)
    rw [le_div_iff₀ hΛ]
    have : MAP X₀ κ y * Real.log X₀ ≤ MAP X₀ κ y * Real.log y :=
      mul_le_mul_of_nonneg_left hL hMAP0
    linarith
  -- `1/(κ y) ≤ 10⁻⁷/Λ`: `κ X₀ = e^{0.6033Λ} ≥ (0.3Λ)²`
  have hkX : (0.09 : ℝ) * Real.log X₀ ^ 2 ≤ κ * X₀ := by
    have e : κ * X₀ = Real.exp (Real.log X₀ * (181 / 300)) := by
      rw [show κ = Real.exp (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ))) from kappa_eq_exp hX0]
      nth_rewrite 2 [← Real.exp_log hX0]
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    have h3 := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ Real.log X₀ * (181 / 300) by positivity) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3
    norm_num at h3
    have : 0 ≤ Real.log X₀ * (181 / 300) := by positivity
    nlinarith
  have hky : κ * X₀ ≤ κ * y := mul_le_mul_of_nonneg_left hy0 hκ0.le
  have hinv : 1 / (κ * y) ≤ 1 / 10 ^ 6 / Real.log X₀ := by
    have hky0 : 0 < κ * y := by nlinarith
    rw [div_le_div_iff₀ hky0 hΛ]
    have : (10 : ℝ) ^ 6 * Real.log X₀ ≤ 0.09 * Real.log X₀ ^ 2 := by nlinarith
    nlinarith
  have : (1 + 1 / 10 ^ 24) / Real.log X₀ + 1 / 10 ^ 6 / Real.log X₀ ≤ 1.000002 / Real.log X₀ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hΛ.le
  linarith

/-! ### The slot count near `X₀` -/

/-- **Placed slots in `(X₀, b]`**: at most `C(b) - C(X₀) + 1` (`placed_gap`). -/
lemma window_count_C {U : ℕ → ℝ} {M : SlotModel X₀} (W : WinFacts θ M U) (S₀ : Set ℕ)
    (hS₀ : ∀ m ∈ S₀, placedAt M m ∧ UnitJumpAt X₀ (DM M U) (M.slot (m + 1)))
    {b : ℝ} (hb : (X₀ : ℝ) ≤ b) :
    ({m | m ∈ S₀ ∧ (X₀ : ℝ) < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}.ncard : ℝ) ≤
      contD θ X₀ (DM M U) b - contD θ X₀ (DM M U) X₀ + 1 := by
  classical
  set S := {m | m ∈ S₀ ∧ (X₀ : ℝ) < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}
  set C := contD θ X₀ (DM M U)
  have hCb : 0 ≤ C b - C X₀ := by have := W.cmono _ _ le_rfl hb; linarith
  set g : ℕ → ℕ := fun m => ⌊C (M.slot (m + 1)) - C X₀⌋₊
  have hpos : ∀ m ∈ S, 0 ≤ C (M.slot (m + 1)) - C X₀ := by
    intro m hm
    have := W.cmono _ _ le_rfl hm.2.1.le
    linarith
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' hg
    by_contra hne
    have h3 : (g m : ℝ) = g m' := by rw [hg]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := placed_gap W (hS₀ m hm.1).2 (hS₀ m' hm'.1).2 hlt (hS₀ m hm.1).1
        (hS₀ m' hm'.1).1 hm.2.1
      have h1 := Nat.floor_le (hpos m hm)
      have h2 := Nat.lt_floor_add_one (C (M.slot (m' + 1)) - C X₀)
      simp only [g] at h3
      linarith
    · have := placed_gap W (hS₀ m' hm'.1).2 (hS₀ m hm.1).2 hlt (hS₀ m' hm'.1).1
        (hS₀ m hm.1).1 hm'.2.1
      have h1 := Nat.floor_le (hpos m' hm')
      have h2 := Nat.lt_floor_add_one (C (M.slot (m + 1)) - C X₀)
      simp only [g] at h3
      linarith
  have hmaps : Set.MapsTo g S (Finset.range (⌊C b - C X₀⌋₊ + 1) : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    have := W.cmono _ _ hm.2.1.le hm.2.2
    linarith
  have hcard := Set.ncard_le_ncard_of_injOn g hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at hcard
  have h1 : ((⌊C b - C X₀⌋₊ + 1 : ℕ) : ℝ) ≤ C b - C X₀ + 1 := by
    push_cast; linarith [Nat.floor_le hCb]
  have hc : (S.ncard : ℝ) ≤ ((⌊C b - C X₀⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- `H(X₀) ≥ 10⁶ Λ`. -/
lemma capH_X0_ge (hX : 10 ^ 8 ≤ Real.log X₀) :
    10 ^ 6 * Real.log X₀ ≤ capH X₀ X₀ := by
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hΛ : 0 < Real.log X₀ := by linarith
  have hL : 18 ≤ Real.log (Real.log X₀) := by
    rw [Real.le_log_iff_exp_le hΛ]
    have h1 : Real.exp 18 ≤ 10 ^ 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 18 := by gcongr
        _ ≤ 10 ^ 8 := by norm_num
    linarith
  have h1 : Real.exp (Real.log (Real.log X₀) + 14) ≤
      Real.exp (8 * Real.log (Real.log X₀) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.exp_add, Real.exp_log hΛ] at h1
  have h2 := AbsorbEmpty.exp_fourteen_ge
  unfold capH
  have h3 : 10 ^ 6 * Real.log X₀ ≤ Real.log X₀ * Real.exp 14 := by nlinarith
  exact (h3.trans h1).trans (le_max_left _ _)

/-- **The box weight below `X₀`**: for `y ∈ [X₀⁻, X₀)`,
`∑_k 1[A_k] H_k⁻¹ 1[y ∈ box_k] ≤ 0.50001/Λ`. -/
theorem slotSum_le (hc : Cond θ X₀) (hev : Even X₀) (hH : HuxleyFrom X₀) (ω : JitterΩ)
    {y : ℝ} (hy2 : y < X₀) :
    ∑' n, (lawA θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (RankFull.box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 y) ω ≤
        ENNReal.ofReal (0.50001 / Real.log X₀) := by
  classical
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hΛ : 0 < Real.log X₀ := by linarith
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set H₀ := capH X₀ X₀ with hH₀
  have hH0big := capH_X0_ge hX
  have hH0pos : 0 < H₀ := by nlinarith
  have hH0le : H₀ ≤ X₀ / 40 := KR.WidthReal.capH_le_tenth hX le_rfl
  set bb := (X₀ : ℝ) + (H₀ + 1 / 4) / 2 with hbb
  set N := {n | ω ∈ lawA θ X₀ n ∧ y ∈ RankFull.box (slotF θ X₀ n ω) (HF θ X₀ n ω)} with hN
  have hf : ∀ n, (lawA θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (RankFull.box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 y) ω =
      if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0 := by
    intro n
    by_cases h1 : ω ∈ lawA θ X₀ n
    · by_cases h2 : y ∈ RankFull.box (slotF θ X₀ n ω) (HF θ X₀ n ω)
      · simp [hN, h1, h2]
      · simp [hN, h2]
    · simp [hN, h1]
  simp_rw [hf]
  -- each box of `N`: `H₀ ≤ H_n` and `s_n ≤ X₀ + (H₀ + 1/4)/2`
  have hbox : ∀ n ∈ N, H₀ ≤ HF θ X₀ n ω ∧ slotF θ X₀ n ω ≤ bb := by
    intro n hn
    have hs := slotF_ge hc n ω
    obtain ⟨hb1, hb2⟩ := hn.2
    have hmono := capH_monotoneOn (Nat.cast_nonneg X₀) hX (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hs) hs
    have hup := Queue6.H_slot_le hc hs (q := y) hb1
    have hHc : Queue6.Hc X₀ y = H₀ := by
      unfold Queue6.Hc; rw [max_eq_right hy2.le]
    rw [hHc] at hup
    refine ⟨hmono, ?_⟩
    have : slotF θ X₀ n ω ≤ y + HF θ X₀ n ω / 2 := by linarith [hb1]
    unfold HF at this
    rw [hbb]; linarith
  set S₀ := {m | ω ∈ lawA θ X₀ m}
  have hS₀ : ∀ m ∈ S₀, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1)) := by
    intro m hm
    have h1 := hm.1
    have h2 := hm.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨h1, h2⟩
  have hslot1 := (limModel_slot_one h hev).1
  have hNsub : N ⊆ {m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ bb} := by
    intro n hn
    have h2 := (hbox n hn).2
    simp only [slotF] at h2
    rw [hMe] at h2
    exact ⟨hn.1, lt_of_lt_of_le hslot1 (h.limModel.slot_mono (by omega)), h2⟩
  have hWfin : {m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ bb}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hNfin : N.Finite := hWfin.subset hNsub
  have hbbX : (X₀ : ℝ) ≤ bb := by rw [hbb]; linarith
  have hcount := window_count_C (winFacts h) S₀ hS₀ hbbX
  -- `C(bb) - C(X₀) = ∫ T'_cont ≤ (bb - X₀) 1.000002/Λ`
  obtain ⟨hint, hI⟩ := integral_TpCont hc ω hbbX hbbX
  have hDF : DF θ X₀ ω = DM h.limModel (Ucl ω) := by unfold DF; rw [hMe]
  rw [hDF, max_self] at hI
  have hTle : ∫ t in (X₀ : ℝ)..bb, TpCont θ X₀ ω t ≤
      ∫ t in (X₀ : ℝ)..bb, (1.000002 / Real.log X₀ : ℝ) := by
    apply intervalIntegral.integral_mono_on hbbX hint intervalIntegrable_const
    intro t ht
    exact TpCont_le_low hc hH ω ht.1 (by rw [hbb] at ht; linarith [ht.2])
  rw [intervalIntegral.integral_const, smul_eq_mul, hI] at hTle
  have hNcard : (N.ncard : ℝ) ≤ (bb - X₀) * (1.000002 / Real.log X₀) + 1 := by
    have h1 : (N.ncard : ℝ) ≤ ({m | m ∈ S₀ ∧ (X₀ : ℝ) < h.limModel.slot (m + 1) ∧
        h.limModel.slot (m + 1) ≤ bb}.ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hNsub hWfin
    linarith
  -- the sum
  have hsum : ∑' n, (if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0) ≤
      ∑' n, (if n ∈ N then ENNReal.ofReal H₀⁻¹ else 0) := by
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs with hn
    · exact ENNReal.ofReal_le_ofReal (inv_anti₀ hH0pos (hbox n hn).1)
    · exact le_rfl
  refine hsum.trans ?_
  rw [tsum_eq_sum (s := hNfin.toFinset) (fun n hn => by
    simp only [Set.Finite.mem_toFinset] at hn; simp [hn])]
  rw [Finset.sum_congr rfl (fun b hb => if_pos ((Set.Finite.mem_toFinset _).mp hb)),
    Finset.sum_const, nsmul_eq_mul]
  rw [← Set.ncard_eq_toFinset_card N hNfin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← div_eq_mul_inv, div_le_iff₀ hH0pos]
  have e : bb - X₀ = (H₀ + 1 / 4) / 2 := by rw [hbb]; ring
  rw [e] at hNcard
  -- `((H₀ + 1/4)/2 · 1.000002/Λ + 1) ≤ 0.50001 H₀/Λ`
  have key : (H₀ + 1 / 4) / 2 * 1.000002 + Real.log X₀ ≤ 0.50001 * H₀ := by nlinarith
  have : ((H₀ + 1 / 4) / 2 * (1.000002 / Real.log X₀) + 1) ≤
      0.50001 / Real.log X₀ * H₀ := by
    have e1 : (H₀ + 1 / 4) / 2 * (1.000002 / Real.log X₀) + 1 =
        ((H₀ + 1 / 4) / 2 * 1.000002 + Real.log X₀) / Real.log X₀ := by field_simp
    have e2 : 0.50001 / Real.log X₀ * H₀ = 0.50001 * H₀ / Real.log X₀ := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right key hΛ.le
  linarith

/-! ### The compensator below `2X₀` -/

lemma two_lt_X0 (hX : 10 ^ 8 ≤ Real.log X₀) : 2 < X₀ := by
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have : (3 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀); rw [Real.exp_log hX0] at this; linarith
  exact_mod_cast (show (2 : ℝ) < X₀ by linarith)

/-- The cofactor `2`. -/
noncomputable def wTwo (hX : 10 ^ 8 ≤ Real.log X₀) : PIdx X₀ →₀ ℕ :=
  Finsupp.single (Sum.inl ⟨2, Nat.prime_two, two_lt_X0 hX⟩) 1

lemma eval_wTwo (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) : eval D (wTwo hX) = 2 := by
  unfold eval wTwo
  rw [Finsupp.prod_single_index (by simp)]
  simp [pval]

/-- **The only live cofactor of value `< 3` is `2`.** -/
lemma eq_wTwo (hc : Cond θ X₀) {ω : JitterΩ} {w : PIdx X₀ →₀ ℕ} (hl : Live (DD θ X₀ ω) w)
    (hw : w ≠ 0) (h3 : eval (DD θ X₀ ω) w < 3) : w = wTwo hc.hX := by
  classical
  have hX := hc.hX
  set D := DD θ X₀ ω
  have hgt : ∀ i ∈ w.support, 1 < pval D i := fun i hi => pval_gt_one hc hl i hi
  -- `eval ≥ pval i ^ w i`
  have hge : ∀ i ∈ w.support, pval D i ^ w i ≤ eval D w := by
    intro i hi
    unfold eval Finsupp.prod
    rw [← Finset.mul_prod_erase _ _ hi]
    have h1 : 1 ≤ ∏ j ∈ w.support.erase i, pval D j ^ w j := by
      have := Finset.prod_le_prod₀ (s := w.support.erase i) (f := fun _ => (1 : ℝ))
        (g := fun j => pval D j ^ w j) (fun _ _ => zero_le_one)
        (fun j hj => one_le_pow₀ (hgt j (Finset.mem_of_mem_erase hj)).le)
      simpa using this
    have h0 : 0 ≤ pval D i ^ w i := pow_nonneg (by linarith [hgt i hi]) _
    nlinarith
  have hpv : ∀ i ∈ w.support, pval D i < 3 := by
    intro i hi
    have hwi : 1 ≤ w i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have : pval D i ≤ pval D i ^ w i := by
      calc pval D i = pval D i ^ 1 := (pow_one _).symm
        _ ≤ pval D i ^ w i := pow_le_pow_right₀ (hgt i hi).le hwi
    linarith [hge i hi]
  set i2 : PIdx X₀ := Sum.inl ⟨2, Nat.prime_two, two_lt_X0 hX⟩
  have hsupp : ∀ i ∈ w.support, i = i2 := by
    intro i hi
    have := hpv i hi
    rcases i with ⟨p, hp, hpX⟩ | k
    · simp only [pval] at this
      have hp3 : p < 3 := by exact_mod_cast this
      have hp2 := hp.two_le
      have : p = 2 := by omega
      subst this; rfl
    · exfalso
      have h0 : D.v k < 3 := this
      have h1 : Xm X₀ ≤ D.v k := valF_ge_Xm hc k ω
      have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
      have h100 : (100 : ℝ) ≤ X₀ := by
        have := Real.add_one_le_exp (Real.log X₀); rw [Real.exp_log hX0] at this; linarith
      have hH := KR.WidthReal.capH_le_tenth hX (le_refl (X₀ : ℝ))
      unfold Xm at h1
      linarith
  obtain ⟨i0, hi0⟩ := Finsupp.support_nonempty_iff.mpr hw
  have hi0' := hsupp i0 hi0
  subst hi0'
  have hwi : w i2 = 1 := by
    have h1 : 1 ≤ w i2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0)
    have h2 := hge i2 hi0
    simp only [i2, pval] at h2
    push_cast at h2
    by_contra hne
    have h4 : 2 ≤ w i2 := by omega
    have : (2 : ℝ) ^ 2 ≤ 2 ^ w i2 := pow_le_pow_right₀ (by norm_num) h4
    linarith
  unfold wTwo
  rw [Finsupp.eq_single_iff]
  exact ⟨fun i hi => Finset.mem_singleton.mpr (hsupp i hi), hwi⟩

/-- **The compensator density below `2X₀`**: `c(t) ≤ ½ ∑_k 1[A_k] H_k⁻¹ 1[t/2 ∈ box_k]`. -/
lemma compDen_le_half (hc : Cond θ X₀) (ω : JitterΩ) {t : ℝ} (ht0 : 0 < t) (ht : t < 2 * X₀) :
    compDen θ X₀ ω t ≤ ENNReal.ofReal (1 / 2) * ∑' n, (lawA θ X₀ n).indicator
      (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
        (RankFull.box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 (t / 2)) ω := by
  classical
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hXm3 : t / Xm X₀ < 3 := by
    have hH := KR.WidthReal.capH_le_tenth hX (le_refl (X₀ : ℝ))
    have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
    rw [div_lt_iff₀ hXm]
    unfold Xm at *; nlinarith
  unfold compDen
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  unfold compTerm
  by_cases hk : ω ∈ lawA θ X₀ k
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    have hinner : (∑' w : PIdx X₀ →₀ ℕ, if w ∈ cofP θ X₀ k ω ∧
        Xm X₀ ≤ t / eval (DD θ X₀ ω) w ∧
        ¬ (10 ^ 7 ≤ Real.log t ∧ t / eval (DD θ X₀ ω) w < AbsorbEmpty.absorbY X₀ t) then
        (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (t / eval (DD θ X₀ ω) w) *
          ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0) ≤
        (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (t / 2) *
          ENNReal.ofReal (1 / 2) := by
      set c := (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (t / 2) *
        ENNReal.ofReal (1 / 2)
      have hc' : ∑' w : PIdx X₀ →₀ ℕ, (if w = wTwo hX then c else 0) = c := by simp
      rw [← hc']
      refine ENNReal.tsum_le_tsum fun w => ?_
      split_ifs with h1 h2
      · subst h2
        rw [eval_wTwo]
        simp only [c, one_div]
        exact le_rfl
      · exfalso
        obtain ⟨⟨hl, hw0, -⟩, hXm, -⟩ := h1
        have he := eval_pos hc hl
        have : eval (DD θ X₀ ω) w < 3 := by
          rw [le_div_iff₀ he] at hXm
          have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
          rw [div_lt_iff₀ hXm0] at hXm3
          nlinarith
        exact h2 (eq_wTwo hc hl hw0 this)
      · exact zero_le
      · exact le_rfl
    calc ENNReal.ofReal (HF θ X₀ k ω)⁻¹ * (∑' w : PIdx X₀ →₀ ℕ, _)
        ≤ ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
          ((RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (t / 2) *
            ENNReal.ofReal (1 / 2)) := mul_le_mul_right hinner _
      _ = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
          (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (t / 2)) := by ring
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, mul_zero]

/-! ### The field `hc` -/

/-- **Proposition 5.38(c), Step 6(c)**: the field `hc` of `BModel.RealMarginLoc`, for every
`ω`, from (huxley) and the slot rule. -/
theorem margin_hc (hc : Cond θ X₀) (hev : Even X₀) (hH : HuxleyFrom X₀) (ω : JitterΩ)
    (b : ℝ) :
    ∀ t, (X₀ : ℝ) ≤ t → t < 2 * X₀ → t ≤ b →
      (∃ Tp, marginM θ X₀ ω t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
      (∃ Tp rt, marginM θ X₀ ω t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
        rt ≤ 0.5001 / Real.log X₀ ∧ Real.log t ≤ Real.log X₀ + 0.7) := by
  intro t ht1 ht2 _
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hΛ : 0 < Real.log X₀ := by linarith
  have ht0 : 0 < t := by linarith
  right
  refine ⟨TpCont θ X₀ ω t, 2 * (compDen θ X₀ ω t).toReal, ?_, ?_, ?_, ?_⟩
  · unfold marginM; ring
  · rw [TpCont_eq_low hc ω ht1 ht2]
    exact one_sub_rhoDet_ge_099 hX hH ht1
  · have h1 := compDen_le_half hc ω ht0 ht2
    have h2 := slotSum_le hc hev hH ω (y := t / 2) (by linarith)
    have h3 : compDen θ X₀ ω t ≤ ENNReal.ofReal (1 / 2 * (0.50001 / Real.log X₀)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      exact h1.trans (mul_le_mul_right h2 _)
    have h4 := ENNReal.toReal_le_of_le_ofReal (by positivity) h3
    have : 2 * (1 / 2 * (0.50001 / Real.log X₀)) ≤ 0.5001 / Real.log X₀ := by
      rw [show 2 * (1 / 2 * (0.50001 / Real.log X₀)) = 0.50001 / Real.log X₀ by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hΛ.le
    linarith
  · have h1 : Real.log t ≤ Real.log (2 * X₀) := Real.log_le_log ht0 ht2.le
    rw [Real.log_mul (by norm_num) hX0.ne'] at h1
    have := Real.log_two_lt_d9
    linarith

end BaseRange
