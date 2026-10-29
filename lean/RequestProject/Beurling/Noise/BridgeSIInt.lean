module

public import RequestProject.BSCert.DickmanFn

/-!
# Lemma 5.32, Region 1: the block sum against the integral

With `J̃ > 0`, `u(ℓ) = ℓ/(J̃ - ℓ)`, `ℓ_k = ℓ₀ + k log 2` and `σ_k = J̃ - ℓ_k - 2 log 2`,

  `∑_{k ∈ K} ρ(u_k - 1)/(ℓ_k σ_k) ≤ (1 + 3 log 2/S₀)/log 2 · (1/J̃) (log⁺(1/u(ℓ₀ - log 2)) + 1)`

for every set `K ⊆ [0, n)` of indices with `σ_k ≥ S₀ > 0` (`block_sum_le`). This is the paper's
comparison of the dyadic sum with `(log 2)⁻¹ ∫ f`, `f(ℓ) = ρ(u(ℓ) - 1)/(ℓ(J̃ - ℓ))`, and
`∫ f dℓ = J̃⁻¹ ∫ ρ(u - 1) du/u` (`ℓ = J̃u/(1+u)`), with `∫_c^d ρ(u-1) du/u ≤ log⁺(1/c) + 1` by
(R1). Here each term is compared with the integral over the preceding interval
`[ℓ_k - log 2, ℓ_k]`, where `ρ(u(ℓ) - 1) ≥ ρ(u_k - 1)` (`ρ` is non-increasing), instead of the
total-variation bound of the paper.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace BridgeSI

/-- `u(ℓ) = ℓ/(J̃ - ℓ)`. -/
noncomputable def uOf (Jt ℓ : ℝ) : ℝ := ℓ / (Jt - ℓ)

/-- `f(ℓ) = ρ(u(ℓ) - 1)/(ℓ(J̃ - ℓ))`. -/
noncomputable def fOf (Jt ℓ : ℝ) : ℝ := Dickman.rho (uOf Jt ℓ - 1) / (ℓ * (Jt - ℓ))

lemma uOf_mono {Jt a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Jt) : uOf Jt a ≤ uOf Jt b := by
  unfold uOf
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma continuousOn_fOf {Jt a b : ℝ} (ha : 0 < a) (hb : b < Jt) :
    ContinuousOn (fOf Jt) (Icc a b) := by
  intro ℓ hℓ
  apply ContinuousAt.continuousWithinAt
  have h1 : Jt - ℓ ≠ 0 := by linarith [hℓ.2]
  have h2 : ℓ * (Jt - ℓ) ≠ 0 := mul_ne_zero (by linarith [hℓ.1]) h1
  unfold fOf uOf
  exact ((Dickman.continuous_rho.continuousAt).comp
    ((continuousAt_id.div (continuousAt_const.sub continuousAt_id) h1).sub
      continuousAt_const)).div (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)) h2

lemma fOf_nonneg {Jt ℓ : ℝ} (hℓ : 0 < ℓ) (hJ : ℓ < Jt) : 0 ≤ fOf Jt ℓ := by
  unfold fOf
  exact div_nonneg (Dickman.rho_pos _).le (mul_pos hℓ (by linarith)).le

/-- `∫_c^d ρ(u-1) du/u ≤ max(0, log(1/c)) + 1` for `0 < c ≤ d`. -/
lemma integral_rho_div_le {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    ∫ u in c..d, Dickman.rho (u - 1) / u ≤ max 0 (Real.log (1 / c)) + 1 := by
  have hcont : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable (fun u => Dickman.rho (u - 1) / u) volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousOn.div
      continuousOn_id (fun u hu => ne_of_gt (by linarith [hu.1]))
  -- the integrand is at most `1/u`
  have hle1 : ∀ a b : ℝ, 0 < a → a ≤ b →
      ∫ u in a..b, Dickman.rho (u - 1) / u ≤ Real.log (b / a) := by
    intro a b ha hab
    rw [← integral_inv_of_pos ha (by linarith)]
    apply integral_mono_on hab (hcont a b ha hab)
    · exact (continuousOn_inv₀.mono (fun u hu => by
        rw [uIcc_of_le hab] at hu; exact ne_of_gt (by linarith [hu.1]))).intervalIntegrable
    · intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      rw [div_eq_mul_inv]
      have := Dickman.rho_le_one (u - 1)
      have hi : 0 < u⁻¹ := inv_pos.mpr hu0
      nlinarith
  have hmax : 0 ≤ max 0 (Real.log (1 / c)) := le_max_left _ _
  rcases le_or_gt d 1 with hd1 | hd1
  · -- `d ≤ 1`
    refine (hle1 c d hc hcd).trans ?_
    have : Real.log (d / c) ≤ Real.log (1 / c) :=
      Real.log_le_log (div_pos (by linarith) hc) (div_le_div_of_nonneg_right hd1 hc.le)
    linarith [le_max_right 0 (Real.log (1 / c))]
  rcases le_or_gt 1 c with hc1 | hc1
  · -- `c ≥ 1`: `(R1)`
    rw [Dickman.integral_shift_div hc1 (by linarith)]
    have := Dickman.rho_pos d
    have := Dickman.rho_le_one c
    linarith
  · -- `c < 1 < d`
    rw [← integral_add_adjacent_intervals (hcont c 1 hc hc1.le) (hcont 1 d one_pos hd1.le)]
    have h1 := hle1 c 1 hc hc1.le
    rw [Dickman.integral_shift_div le_rfl hd1.le]
    have := Dickman.rho_pos d
    have := Dickman.rho_le_one 1
    linarith [le_max_right 0 (Real.log (1 / c))]

/-- **Change of variables**: `∫_a^b f = J̃⁻¹ ∫_{u(a)}^{u(b)} ρ(u-1) du/u` for `0 < a ≤ b < J̃`. -/
lemma integral_fOf {Jt a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Jt) :
    ∫ ℓ in a..b, fOf Jt ℓ =
      Jt⁻¹ * ∫ u in uOf Jt a..uOf Jt b, Dickman.rho (u - 1) / u := by
  have hJ : 0 < Jt := by linarith
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (uOf Jt) (Jt / (Jt - x) ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have h1 : Jt - x ≠ 0 := by linarith [hx.2]
    have := (hasDerivAt_id' x).div ((hasDerivAt_id' x).const_sub Jt) h1
    unfold uOf
    convert this using 1
    field_simp; ring
  have hcont' : ContinuousOn (fun x => Jt / (Jt - x) ^ 2) (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 2)
      (pow_ne_zero 2 (by linarith [hx.2]))
  have hg : ContinuousOn (fun u => Jt⁻¹ * (Dickman.rho (u - 1) / u)) (uOf Jt '' uIcc a b) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := hu
    rw [uIcc_of_le hab] at hx
    have hpos : 0 < uOf Jt x := by
      unfold uOf; exact div_pos (by linarith [hx.1]) (by linarith [hx.2])
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul (((Dickman.continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousAt).div continuousAt_id hpos.ne')
  have hcv := integral_comp_mul_deriv' hderiv hcont' hg
  rw [intervalIntegral.integral_const_mul] at hcv
  rw [← hcv]
  apply integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have h1 : Jt - x ≠ 0 := by linarith [hx.2]
  have h2 : x ≠ 0 := by linarith [hx.1]
  simp only [Function.comp, fOf, uOf]
  field_simp

/-- **The block sum against the integral** (Lemma 5.32, Region 1). -/
theorem block_sum_le {Jt ℓ0 S0 : ℝ} {n : ℕ} (K : Finset ℕ) (hK : ∀ k ∈ K, k < n)
    (hℓ0 : Real.log 2 < ℓ0) (htop : ℓ0 + n * Real.log 2 < Jt) (hS0 : 0 < S0)
    (hσ : ∀ k ∈ K, S0 ≤ Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2) :
    ∑ k ∈ K, Dickman.rho (uOf Jt (ℓ0 + k * Real.log 2) - 1) /
        ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2)) ≤
      (1 + 3 * Real.log 2 / S0) / Real.log 2 *
        (Jt⁻¹ * (max 0 (Real.log (1 / uOf Jt (ℓ0 - Real.log 2))) + 1)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := 1 + 3 * Real.log 2 / S0 with hc
  have hc0 : 0 < c := by positivity
  set a : ℕ → ℝ := fun i => ℓ0 - Real.log 2 + i * Real.log 2 with ha
  have ha0 : ∀ i, 0 < a i := fun i => by
    simp only [ha]
    have h1 : 0 < ℓ0 - Real.log 2 := by linarith
    have h2 : (0 : ℝ) ≤ i * Real.log 2 := by positivity
    linarith
  have hJt : ∀ i, i ≤ n → a i < Jt := by
    intro i hi
    simp only [ha]
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    nlinarith
  have hint : ∀ i, i < n → IntervalIntegrable (fOf Jt) volume (a i) (a (i + 1)) := by
    intro i hi
    have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact continuousOn_fOf (ha0 i) (hJt (i + 1) hi)
  -- (ii)-(iii): each term against the integral over the preceding interval
  have hterm : ∀ k ∈ K, Dickman.rho (uOf Jt (ℓ0 + k * Real.log 2) - 1) /
      ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2)) ≤
      c / Real.log 2 * ∫ ℓ in a k..a (k + 1), fOf Jt ℓ := by
    intro k hk
    have hkn := hK k hk
    set lk := ℓ0 + k * Real.log 2 with hlk
    have hak : a k = lk - Real.log 2 := by simp only [ha, hlk]; ring
    have hak1 : a (k + 1) = lk := by simp only [ha, hlk]; push_cast; ring
    have hlkJ : lk < Jt := by rw [← hak1]; exact hJt (k + 1) hkn
    have hlk0 : 0 < lk := by rw [← hak1]; exact ha0 (k + 1)
    set σ := Jt - lk - 2 * Real.log 2 with hσdef
    have hσk : S0 ≤ σ := hσ k hk
    have hσ0 : 0 < σ := by linarith
    set g := Dickman.rho (uOf Jt lk - 1) / (lk * σ) with hg
    -- `g ≤ c · f(ℓ)` on `[ℓ_k - log 2, ℓ_k]`
    have hpt : ∀ ℓ ∈ Icc (a k) (a (k + 1)), g / c ≤ fOf Jt ℓ := by
      intro ℓ hℓ
      rw [hak, hak1] at hℓ
      have hℓ0 : 0 < ℓ := by linarith [hℓ.1, ha0 k, hak]
      have hρ : Dickman.rho (uOf Jt lk - 1) ≤ Dickman.rho (uOf Jt ℓ - 1) :=
        Dickman.rho_antitone (by linarith [uOf_mono hℓ0 hℓ.2 hlkJ])
      have hden : ℓ * (Jt - ℓ) ≤ lk * (Jt - lk + Real.log 2) := by
        have h1 : Jt - ℓ ≤ Jt - lk + Real.log 2 := by linarith [hℓ.1]
        have h2 : 0 < Jt - ℓ := by linarith [hℓ.2]
        exact mul_le_mul hℓ.2 h1 h2.le hlk0.le
      have hcσ : c * σ = Jt - lk + Real.log 2 + (3 * Real.log 2 / S0 * σ - 3 * Real.log 2) := by
        rw [hc, hσdef]; ring
      have hextra : 0 ≤ 3 * Real.log 2 / S0 * σ - 3 * Real.log 2 := by
        rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ hS0]; nlinarith
      have hden2 : ℓ * (Jt - ℓ) ≤ lk * (c * σ) := by
        rw [hcσ]; nlinarith
      have hpos : 0 < ℓ * (Jt - ℓ) := mul_pos hℓ0 (by linarith [hℓ.2])
      rw [hg, div_div, fOf]
      calc Dickman.rho (uOf Jt lk - 1) / (lk * σ * c)
          ≤ Dickman.rho (uOf Jt ℓ - 1) / (lk * σ * c) :=
            div_le_div_of_nonneg_right hρ (by positivity)
        _ ≤ Dickman.rho (uOf Jt ℓ - 1) / (ℓ * (Jt - ℓ)) := by
            apply div_le_div_of_nonneg_left (Dickman.rho_pos _).le hpos
            linarith
    have hlen : a (k + 1) - a k = Real.log 2 := by rw [hak, hak1]; ring
    have hle : a k ≤ a (k + 1) := by linarith
    have hmono : ∫ ℓ in a k..a (k + 1), g / c ≤ ∫ ℓ in a k..a (k + 1), fOf Jt ℓ :=
      integral_mono_on hle _root_.intervalIntegrable_const (hint k hkn) hpt
    rw [intervalIntegral.integral_const, hlen, smul_eq_mul] at hmono
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    have : g = c * (Real.log 2 * (g / c)) / Real.log 2 := by field_simp
    calc g * Real.log 2 = c * (Real.log 2 * (g / c)) := by field_simp
      _ ≤ c * ∫ ℓ in a k..a (k + 1), fOf Jt ℓ := mul_le_mul_of_nonneg_left hmono hc0.le
  -- (iv): sum of the integrals
  have hsum : ∑ k ∈ K, ∫ ℓ in a k..a (k + 1), fOf Jt ℓ ≤ ∫ ℓ in a 0..a n, fOf Jt ℓ := by
    rw [← intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hint i hi)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; exact Finset.mem_range.mpr (hK k hk)
    · intro i hi _
      have hin := Finset.mem_range.mp hi
      have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
      apply integral_nonneg hle
      intro ℓ hℓ
      exact fOf_nonneg (lt_of_lt_of_le (ha0 i) hℓ.1) (lt_of_le_of_lt hℓ.2 (hJt (i + 1) hin))
  -- (v)-(vi)
  have h0n : a 0 ≤ a n := by simp only [ha]; push_cast; nlinarith
  have hcv := integral_fOf (ha0 0) h0n (hJt n le_rfl)
  have hu0 : 0 < uOf Jt (a 0) := by
    unfold uOf; exact div_pos (ha0 0) (by linarith [hJt 0 (Nat.zero_le n)])
  have hun : uOf Jt (a 0) ≤ uOf Jt (a n) := uOf_mono (ha0 0) h0n (hJt n le_rfl)
  have hR := integral_rho_div_le hu0 hun
  have ha0e : a 0 = ℓ0 - Real.log 2 := by simp only [ha]; ring
  rw [ha0e] at hR hcv
  have hJ0 : 0 < Jt := lt_of_lt_of_le (ha0 n) (hJt n le_rfl).le
  calc ∑ k ∈ K, Dickman.rho (uOf Jt (ℓ0 + k * Real.log 2) - 1) /
        ((ℓ0 + k * Real.log 2) * (Jt - (ℓ0 + k * Real.log 2) - 2 * Real.log 2))
      ≤ ∑ k ∈ K, c / Real.log 2 * ∫ ℓ in a k..a (k + 1), fOf Jt ℓ := Finset.sum_le_sum hterm
    _ = c / Real.log 2 * ∑ k ∈ K, ∫ ℓ in a k..a (k + 1), fOf Jt ℓ := by rw [Finset.mul_sum]
    _ ≤ c / Real.log 2 * ∫ ℓ in a 0..a n, fOf Jt ℓ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ c / Real.log 2 * (Jt⁻¹ * (max 0 (Real.log (1 / uOf Jt (ℓ0 - Real.log 2))) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [ha0e, hcv]
        exact mul_le_mul_of_nonneg_left hR (inv_pos.mpr hJ0).le

end BridgeSI

end
