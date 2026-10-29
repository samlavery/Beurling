module

public import RequestProject.Beurling.Noise.MarginRealLoc
public import RequestProject.Beurling.BaseRange.Window
public import RequestProject.Beurling.Model.Choices

/-!
# Proposition 5.38(c) (Step 6(c)): the source bounds on `[X₀, 2X₀)`

The field `hc` of `BModel.RealMarginLoc`. For `X₀ ≤ t < 2X₀`:

* `TpCont_eq_low` : `T'_cont(t) = 1 - ρ_det(t)` (`𝒜 = ∅` there, `absDenCap_zero_low`, and
  `R' = 0` below the first switch-on point `exp(X₀²)`, `deriv_osc_zero_low`);
* `one_sub_rhoDet_le_low` : `1 - ρ_det(y) ≤ MA[ℙ](y) + 1/(κy) ≤ 1.000001/Λ` near `X₀`;
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
    absorbedDensityCap (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) y = 0 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_of_log hX]
  have hb : 0 < θ / 2 := by linarith [hc.hθ.1]
  have hb1 : θ / 2 ≤ 1 := by linarith [hc.hθ.2]
  have hzero : absorbedDensity (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) y = 0 := by
    unfold absorbedDensity
    refine (tsum_congr fun a => ?_).trans tsum_zero
    unfold absorbedBump
    split_ifs with ha
    · rw [Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      obtain ⟨-, e, -, -, -, k, -, -, hk⟩ := ha
      have ha0 : 0 ≤ a := by linarith
      obtain ⟨hu0, hu⟩ := solveU_spec hb ha0
      have hu1 : uA θ a = solveU (θ / 2) a := rfl
      rw [← hu1] at hu0 hu
      have hub : uA θ a ^ (θ / 2) ≤ 2 * X₀ := by
        rcases le_or_gt 1 (uA θ a) with h | h
        · calc uA θ a ^ (θ / 2) ≤ uA θ a ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h hb1
            _ = uA θ a := Real.rpow_one _
            _ ≤ 2 * X₀ := by linarith
        · have : uA θ a ^ (θ / 2) ≤ 1 := Real.rpow_le_one hu0 h.le hb.le
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

/-- **`T'_cont ≤ 1.000001/Λ` on `[X₀, X₀ + X₀/2]`** (from (huxley) via Lemma 7.3(a)). -/
lemma TpCont_le_low (hc : Cond θ X₀) (hH : HuxleyFrom X₀) (ω : JitterΩ) {y : ℝ}
    (hy0 : (X₀ : ℝ) ≤ y) (hy : y ≤ 3 / 2 * X₀) :
    TpCont θ X₀ ω y ≤ 1.000001 / Real.log X₀ := by
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
    have e : κ * X₀ = Real.exp (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀) := by
      rw [show κ = Real.exp (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ))) from kappa_eq_exp hX0,
        Real.exp_add, Real.exp_log hX0]
    rw [e]
    have h3 := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀ by nlinarith) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3
    norm_num at h3
    nlinarith
  have hky : κ * X₀ ≤ κ * y := mul_le_mul_of_nonneg_left hy0 hκ0.le
  have hinv : 1 / (κ * y) ≤ 1 / 10 ^ 7 / Real.log X₀ := by
    rw [div_le_div_iff₀ (by nlinarith) hΛ]
    nlinarith
  have : (1 + 1 / 10 ^ 24) / Real.log X₀ + 1 / 10 ^ 7 / Real.log X₀ ≤ 1.000001 / Real.log X₀ := by
    rw [div_add_div_same]
    exact div_le_div_of_nonneg_right (by norm_num) hΛ.le
  linarith

end BaseRange
