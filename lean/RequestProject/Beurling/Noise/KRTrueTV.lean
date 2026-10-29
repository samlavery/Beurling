module

public import Mathlib

/-!
# The total variation of an absolutely continuous measure

For an integrable density `g` with distribution function `G(t) = ∫_{s ≤ t} g`, the total variation
of the measure `g(t) dt` is `∫ |g|`. We prove the direction used in §5.9.4 (Proposition 5.18):

* `lintegral_enorm_le_eVariationOn` : `∫ |g| ≤ TV(G) = eVariationOn G univ`,

and the easy converse `eVariationOn_cdf_le` : `eVariationOn G univ ≤ ∫ |g|`. Together, the
total variation of the measure `g dt` in the distribution-function model of `KRFacts.lean`
(`eVariationOn` of its distribution function) is the `L¹` norm of its density.

The proof of the first inequality: `G` is differentiable with `G' = g` almost everywhere
(Lebesgue's differentiation theorem, `LocallyIntegrable.ae_hasDerivAt_integral`); the dyadic
slopes of `G` on the intervals of length `2^{-N}` containing `t` tend to `G'(t)` (a straddle
argument); and Fatou's lemma bounds `∫ |g|` by the `liminf` of the dyadic sums
`∑ |G(b) - G(a)|`, each of which is at most the variation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KR

/-- The distribution function `t ↦ ∫_{s ≤ t} g(s) ds`. -/
noncomputable def cdf (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Iic t, g s

variable {g : ℝ → ℝ}

lemma cdf_sub (hg : Integrable g) {a b : ℝ} (hab : a ≤ b) :
    cdf g b - cdf g a = ∫ s in Ioc a b, g s := by
  unfold cdf
  rw [← Iic_union_Ioc_eq_Iic hab, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
    hg.integrableOn hg.integrableOn]
  ring

lemma abs_cdf_sub_le (hg : Integrable g) {a b : ℝ} (hab : a ≤ b) :
    ‖cdf g b - cdf g a‖ₑ ≤ ∫⁻ s in Ioc a b, ‖g s‖ₑ := by
  rw [cdf_sub hg hab]; exact enorm_integral_le_lintegral_enorm _

/-- **Converse**: `TV(G) ≤ ∫ |g|`. -/
theorem eVariationOn_cdf_le (hg : Integrable g) :
    eVariationOn (cdf g) univ ≤ ∫⁻ s, ‖g s‖ₑ := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, -⟩ := p
  have tel : ∀ m, ∑ i ∈ Finset.range m, ∫⁻ s in Ioc (u i) (u (i + 1)), ‖g s‖ₑ =
      ∫⁻ s in Ioc (u 0) (u m), ‖g s‖ₑ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
        (Set.Ioc_disjoint_Ioc_of_le le_rfl),
        Set.Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le m)) (hu (Nat.le_succ m))]
  calc ∑ i ∈ Finset.range n, edist (cdf g (u (i + 1))) (cdf g (u i))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ s in Ioc (u i) (u (i + 1)), ‖g s‖ₑ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_eq_enorm_sub]; exact abs_cdf_sub_le hg (hu (Nat.le_succ i))
    _ = ∫⁻ s in Ioc (u 0) (u n), ‖g s‖ₑ := tel n
    _ ≤ ∫⁻ s, ‖g s‖ₑ := setLIntegral_le_lintegral _ _

/-- `G' = g` almost everywhere. -/
lemma ae_hasDerivAt_cdf (hg : Integrable g) : ∀ᵐ t, HasDerivAt (cdf g) (g t) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with t ht
  have h0 := ht 0
  have e : cdf g = fun y => cdf g 0 + ∫ s in (0 : ℝ)..y, g s := by
    funext y
    rcases le_total 0 y with hy | hy
    · rw [intervalIntegral.integral_of_le hy, ← cdf_sub hg hy]; ring
    · rw [intervalIntegral.integral_of_ge hy, ← cdf_sub hg hy]; ring
  rw [e]
  exact h0.const_add _

/-- **Straddle**: if `G'(t) = L`, the slopes over intervals `[a, b] ∋ t` with `b - a → 0` tend
to `L`. -/
lemma tendsto_straddle {G : ℝ → ℝ} {L t : ℝ} (hG : HasDerivAt G L t) {a b : ℕ → ℝ}
    (ha : ∀ N, a N ≤ t) (hb : ∀ N, t ≤ b N) (hab : ∀ N, a N < b N)
    (hlen : Tendsto (fun N => b N - a N) atTop (𝓝 0)) :
    Tendsto (fun N => (G (b N) - G (a N)) / (b N - a N)) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlo := hasDerivAt_iff_isLittleO.mp hG
  have hev := hlo.def (c := ε / 2) (by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hlen) δ hδ
  refine ⟨N0, fun N hN => ?_⟩
  have hl := hN0 N hN
  simp only [Real.dist_eq, sub_zero] at hl
  have hpos : 0 < b N - a N := by linarith [hab N]
  rw [abs_of_pos hpos] at hl
  have hbt : dist (b N) t < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hb N])]; linarith [ha N]
  have hat : dist (a N) t < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [ha N])]; linarith [hb N]
  have h1 := hball hbt
  have h2 := hball hat
  simp only [Real.norm_eq_abs, smul_eq_mul] at h1 h2
  rw [Real.dist_eq]
  have key : |G (b N) - G (a N) - (b N - a N) * L| ≤ ε / 2 * (b N - a N) := by
    have e : G (b N) - G (a N) - (b N - a N) * L =
        (G (b N) - G t - (b N - t) * L) - (G (a N) - G t - (a N - t) * L) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by linarith [hb N] : 0 ≤ b N - t),
      abs_of_nonpos (by linarith [ha N] : a N - t ≤ 0)] at *
    nlinarith
  have e2 : (G (b N) - G (a N)) / (b N - a N) - L =
      (G (b N) - G (a N) - (b N - a N) * L) / (b N - a N) := by field_simp
  rw [e2, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  nlinarith

/-! ## The dyadic slopes -/

/-- The dyadic grid `u_N(i) = (i - N 2^N)/2^N`. -/
noncomputable def grid (N i : ℕ) : ℝ := ((i : ℝ) - N * 2 ^ N) / 2 ^ N

lemma grid_mono (N : ℕ) : Monotone (grid N) := by
  intro i j hij
  unfold grid
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

lemma grid_succ (N i : ℕ) : grid N (i + 1) = grid N i + 1 / 2 ^ N := by
  unfold grid; push_cast; field_simp; ring

/-- The dyadic slope function: on the tile `[u_N(i), u_N(i+1))`, `i < 2N 2^N`, it is the slope
of `G` over the tile. -/
noncomputable def dyad (G : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 * N * 2 ^ N), (Ico (grid N i) (grid N (i + 1))).indicator
    (fun _ => (G (grid N (i + 1)) - G (grid N i)) * 2 ^ N) t

lemma measurable_dyad (G : ℝ → ℝ) (N : ℕ) : Measurable (dyad G N) := by
  unfold dyad
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator measurableSet_Ico

lemma lintegral_dyad_le (G : ℝ → ℝ) (N : ℕ) :
    ∫⁻ t, ‖dyad G N t‖ₑ ≤ eVariationOn G univ := by
  have hsum : ∀ t, ‖dyad G N t‖ₑ ≤ ∑ i ∈ Finset.range (2 * N * 2 ^ N),
      (Ico (grid N i) (grid N (i + 1))).indicator
        (fun _ => ‖(G (grid N (i + 1)) - G (grid N i)) * 2 ^ N‖ₑ) t := by
    intro t
    unfold dyad
    refine (enorm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : t ∈ Ico (grid N i) (grid N (i + 1))
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, enorm_zero]
  calc ∫⁻ t, ‖dyad G N t‖ₑ
      ≤ ∫⁻ t, ∑ i ∈ Finset.range (2 * N * 2 ^ N), (Ico (grid N i) (grid N (i + 1))).indicator
          (fun _ => ‖(G (grid N (i + 1)) - G (grid N i)) * 2 ^ N‖ₑ) t := lintegral_mono hsum
    _ = ∑ i ∈ Finset.range (2 * N * 2 ^ N), ‖(G (grid N (i + 1)) - G (grid N i)) * 2 ^ N‖ₑ *
          volume (Ico (grid N i) (grid N (i + 1))) := by
        rw [lintegral_finset_sum _ fun i _ => measurable_const.indicator measurableSet_Ico]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_indicator_const measurableSet_Ico]
    _ = ∑ i ∈ Finset.range (2 * N * 2 ^ N), edist (G (grid N (i + 1))) (G (grid N i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.volume_Ico, grid_succ, edist_eq_enorm_sub, enorm_mul]
        have h2 : (0 : ℝ) < 2 ^ N := by positivity
        rw [show grid N i + 1 / 2 ^ N - grid N i = (2 ^ N)⁻¹ by ring,
          Real.enorm_eq_ofReal_abs ((2 : ℝ) ^ N), abs_of_pos h2, mul_assoc,
          ← ENNReal.ofReal_mul h2.le, mul_inv_cancel₀ h2.ne', ENNReal.ofReal_one, mul_one]
    _ ≤ eVariationOn G univ :=
        eVariationOn.sum_le G _ (grid_mono N) (fun _ => mem_univ _)

/-- On the tile containing `t` (for `N > |t|`), `dyad G N t` is the slope of `G` over it. -/
lemma dyad_eq (G : ℝ → ℝ) {N : ℕ} {t : ℝ} (ht : |t| < N) :
    ∃ i, grid N i ≤ t ∧ t < grid N (i + 1) ∧
      dyad G N t = (G (grid N (i + 1)) - G (grid N i)) * 2 ^ N := by
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  set k : ℤ := ⌊t * 2 ^ N⌋ + N * 2 ^ N
  have hk0 : 0 ≤ k := by
    have h1 : -(N : ℝ) < t := (abs_lt.mp ht).1
    have h3 : -((N : ℝ) * 2 ^ N) < t * 2 ^ N := by nlinarith
    have h4 : -((N : ℤ) * 2 ^ N) < ⌊t * 2 ^ N⌋ + 1 := by
      have := Int.lt_floor_add_one (t * 2 ^ N)
      have h5 : ((-((N : ℤ) * 2 ^ N) : ℤ) : ℝ) < ((⌊t * 2 ^ N⌋ + 1 : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast h5
    simp only [k]; omega
  set i := k.toNat
  have hik : (i : ℤ) = k := Int.toNat_of_nonneg hk0
  have hi : (i : ℝ) = ⌊t * 2 ^ N⌋ + N * 2 ^ N := by
    have : ((i : ℤ) : ℝ) = (k : ℝ) := by rw [hik]
    simp only [k] at this; push_cast at this; exact_mod_cast this
  have hlo : grid N i ≤ t := by
    unfold grid; rw [hi, div_le_iff₀ h2]
    have := Int.floor_le (t * 2 ^ N); linarith
  have hhi : t < grid N (i + 1) := by
    unfold grid; push_cast; rw [hi, lt_div_iff₀ h2]
    have := Int.lt_floor_add_one (t * 2 ^ N); linarith
  refine ⟨i, hlo, hhi, ?_⟩
  have hirange : i < 2 * N * 2 ^ N := by
    have h1 : t < N := (abs_lt.mp ht).2
    have : (i : ℝ) < 2 * N * 2 ^ N := by
      rw [hi]
      have := Int.floor_le (t * 2 ^ N)
      nlinarith
    exact_mod_cast this
  unfold dyad
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem (show t ∈ Ico (grid N i) (grid N (i + 1)) from ⟨hlo, hhi⟩)]
  · intro j _ hji
    apply indicator_of_notMem
    rintro ⟨hj1, hj2⟩
    rcases lt_or_gt_of_ne hji with h | h
    · have : grid N (j + 1) ≤ grid N i := grid_mono N (by omega)
      linarith
    · have : grid N (i + 1) ≤ grid N j := grid_mono N (by omega)
      linarith
  · intro h; exact absurd (Finset.mem_range.mpr hirange) h

/-- **`∫ |g| ≤ TV(G)`** for an integrable density `g` and `G(t) = ∫_{s ≤ t} g`. -/
theorem lintegral_enorm_le_eVariationOn (hg : Integrable g) :
    ∫⁻ t, ‖g t‖ₑ ≤ eVariationOn (cdf g) univ := by
  have hconv : ∀ᵐ t, Tendsto (fun N => ‖dyad (cdf g) N t‖ₑ) atTop (𝓝 ‖g t‖ₑ) := by
    filter_upwards [ae_hasDerivAt_cdf hg] with t ht
    apply (continuous_enorm.tendsto _).comp
    obtain ⟨N0, hN0⟩ := exists_nat_gt |t|
    have hspec : ∀ N, ∃ i, (N0 ≤ N → (grid N i ≤ t ∧ t < grid N (i + 1) ∧
        dyad (cdf g) N t = (cdf g (grid N (i + 1)) - cdf g (grid N i)) * 2 ^ N)) := by
      intro N
      by_cases hN : N0 ≤ N
      · obtain ⟨i, h⟩ := dyad_eq (cdf g) (N := N) (t := t)
          (lt_of_lt_of_le hN0 (by exact_mod_cast hN))
        exact ⟨i, fun _ => h⟩
      · exact ⟨0, fun h => absurd h hN⟩
    choose I hI using hspec
    -- shift so that the straddle hypotheses hold for all indices
    set a : ℕ → ℝ := fun N => grid (N + N0) (I (N + N0))
    set b : ℕ → ℝ := fun N => grid (N + N0) (I (N + N0) + 1)
    have hab : ∀ N, b N - a N = 1 / 2 ^ (N + N0) := fun N => by
      simp only [a, b]; rw [grid_succ]; ring
    have hT := tendsto_straddle ht (a := a) (b := b)
      (fun N => ((hI (N + N0)) (by omega)).1) (fun N => ((hI (N + N0)) (by omega)).2.1.le)
      (fun N => by rw [← sub_pos, hab]; positivity)
      (by
        simp_rw [hab]
        have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)
        have h2 := this.comp (tendsto_add_atTop_nat N0)
        refine h2.congr fun N => ?_
        simp [Function.comp, one_div, inv_pow])
    rw [← tendsto_add_atTop_iff_nat N0]
    refine hT.congr fun N => ?_
    rw [((hI (N + N0)) (by omega)).2.2, hab]
    simp only [a, b]
    field_simp
  calc ∫⁻ t, ‖g t‖ₑ = ∫⁻ t, liminf (fun N => ‖dyad (cdf g) N t‖ₑ) atTop := by
        apply lintegral_congr_ae
        filter_upwards [hconv] with t ht
        exact ht.liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ t, ‖dyad (cdf g) N t‖ₑ) atTop :=
        lintegral_liminf_le fun N => (measurable_dyad _ N).enorm
    _ ≤ eVariationOn (cdf g) univ :=
        liminf_le_of_le (by isBoundedDefault) fun c hc => by
          obtain ⟨N, hN⟩ := hc.exists
          exact hN.trans (lintegral_dyad_le _ N)

end KR

end
