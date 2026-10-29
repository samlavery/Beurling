module

public import RequestProject.Beurling.Construction.JitterRegular
public import RequestProject.Beurling.Positivity

/-!
# Positivity of the target (Lemma 3.3) and the slope of its continuous part

For `x ≥ X₀` the target (6) splits as `T(x) = X₀ + J(x) + C(x)` (`target_eq_split`), with the
jump part `J(x) = Ψ(x, X₀) - Ψ(X₀, X₀) + #(A ∩ [1, x])` and the continuous part
`C(x) = ∫_{X₀}^x T'_cont`, `T'_cont = 1 - ρ_det - ρ̄_A + R'`. Here, for an arbitrary absorbed set
`A`, the parameters of Section 2.2 and heights in the designed range `[Γ_k, 2Γ_k]`:

* `rhoDet_le` : the rigid part of Lemma 3.3, `ρ_det(u) ≤ 1 + 1/(κu) - 0.99/log u`, from the
  short-interval prime number theorem (84) (`ShortIntervalPNTFrom`, a named hypothesis: the
  Heath-Brown / Huxley theorem is not in Mathlib);
* `abs_deriv_osc_le` : the oscillation slope bound `|R'(u)| ≤ 0.02/log u` (proof of Lemma 3.3);
* `contPart_upper`, `contPart_lower` : `0.08 (x'-x)/log x' ≤ C(x') - C(x) ≤ 1.01 (x'-x)`;
* `contPart_continuousOn` : `C` is continuous on `[X₀, ∞)`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology

namespace BModel

/-- (84) of the paper (Heath-Brown short-interval PNT with Huxley's range, threshold `X_Hux`),
in the form used in Lemma 3.3: from `x₁` on. -/
def ShortIntervalPNTFrom (x₁ : ℝ) : Prop :=
  ∀ q a b : ℝ, x₁ ≤ q → q ≤ a → b ≤ 2 * q → (2 * q) ^ (7 / 12 : ℝ) ≤ b - a →
    (1 - Real.log q ^ (-3 : ℤ)) * (b - a) / Real.log (2 * q) ≤
      ({p : ℕ | p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b}.ncard : ℝ)

/-- (84) of the paper holds from some threshold `X_Hux` on. -/
def ShortIntervalPNT : Prop := ∃ x₁ : ℝ, ShortIntervalPNTFrom x₁

/-- The continuous part `C(x) = ∫_{X₀}^x (1 - ρ_det - ρ̄_A) + R(x) - R(X₀)` of the target (6). -/
noncomputable def contPart (X₀ : ℕ) (κ : ℝ) (rhoA R : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x - X₀) - (∫ u in (X₀ : ℝ)..x, Target.rhoDet X₀ κ u) - (∫ u in (X₀ : ℝ)..x, rhoA u) +
    (R x - R X₀)

/-- The jump part `J(x) = Ψ(x, X₀) - Ψ(X₀, X₀) + #(A ∩ [1, x])` of the target (6). -/
noncomputable def jumpPart (X₀ : ℕ) (cntA : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((Rankin.smoothCount X₀ x : ℝ) - Rankin.smoothCount X₀ X₀) + cntA x

/-- The split `T = X₀ + J + C` of the target (6) on `[X₀, ∞)`. -/
theorem target_eq_split {X₀ : ℕ} {κ : ℝ} {cntA rhoA R : ℝ → ℝ} {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    Target.target X₀ κ cntA rhoA R x = X₀ + jumpPart X₀ cntA x + contPart X₀ κ rhoA R x := by
  simp only [Target.target, if_neg (not_lt.mpr hx), jumpPart, contPart]
  ring

/-- The heights lie in the designed range `[Γ_k, 2Γ_k]` (Lemma 4.8). -/
def DesignedRange (θ : ℝ) (X₀ : ℕ) (γ : ℕ → ℝ) : Prop :=
  ∀ k, γ k ∈ Set.Icc
    (DesignedZero.heightScale θ Construction.kappa0Param (Construction.switchOn X₀ k))
    (2 * DesignedZero.heightScale θ Construction.kappa0Param (Construction.switchOn X₀ k))

/-! ### The rigid part -/

lemma kappa_facts {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) :
    0 < Construction.kappaParam X₀ ∧ Construction.kappaParam X₀ ≤ 1 := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  exact ⟨Construction.kappaParam_pos (by linarith), Construction.kappaParam_le_one hX1.le⟩

/-- `(2u)^{7/12} ≤ κu` for `u ≥ X₀`: the windows `[u, (1+κ)u]` are in the range of (84). -/
lemma window_long {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    (2 * u) ^ (7 / 12 : ℝ) ≤ Construction.kappaParam X₀ * u := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hu0 : 0 < u := by linarith
  have hκ := (kappa_facts hX).1
  have hL : Real.log X₀ ≤ Real.log u := Real.log_le_log (by linarith) hu
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_mul (by norm_num) hu0.ne', Real.log_mul hκ.ne' hu0.ne', Construction.kappaParam,
    Real.log_rpow (by linarith)]
  have := Real.log_two_lt_d9
  nlinarith

/-- **Lemma 3.3, rigid part**: `ρ_det(u) ≤ 1 + 1/(κu) - 0.99/log u` for `u ≥ X₀`, from (84). -/
theorem rhoDet_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀)
    {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    Target.rhoDet X₀ (Construction.kappaParam X₀) u ≤
      1 + 1 / (Construction.kappaParam X₀ * u) - 0.99 / Real.log u := by
  classical
  set κ := Construction.kappaParam X₀ with hκdef
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hX
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hu0 : 0 < u := by linarith
  have hLu : 10 ^ 8 ≤ Real.log u := hX.trans (Real.log_le_log (by linarith) hu)
  set b := (1 + κ) * u with hb
  have hbu : b - u = κ * u := by rw [hb]; ring
  have hκu0 : 0 < κ * u := mul_pos hκ0 hu0
  set I := Finset.Icc ⌈u⌉₊ ⌊b⌋₊ with hI
  set S := (Nat.smoothNumbersUpTo ⌊b⌋₊ X₀).filter (fun n : ℕ => u ≤ (n : ℝ)) with hS
  set P := I.filter Nat.Prime with hP
  have hSI : S ⊆ I := by
    intro n hn
    rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hn.2, hn.1.1⟩
  have hdisj : Disjoint S P := by
    rw [Finset.disjoint_left]
    intro n hnS hnP
    rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hnS
    rw [hP, Finset.mem_filter] at hnP
    have hpn := hnS.1.2
    rw [Nat.mem_smoothNumbers] at hpn
    have hmem : n ∈ n.primeFactorsList := by
      rw [Nat.primeFactorsList_prime hnP.2]; simp
    have h1 := hpn.2 n hmem
    have h2 : (X₀ : ℝ) ≤ n := hu.trans hnS.2
    have : X₀ ≤ n := by exact_mod_cast h2
    omega
  have hcard : S.card + P.card ≤ I.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hSI (Finset.filter_subset _ _))
  have hIcard : (I.card : ℝ) ≤ κ * u + 1 := by
    rw [hI, Nat.card_Icc]
    have hc : ⌈u⌉₊ ≤ ⌊b⌋₊ + 1 := by
      have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0.le
      have h2 : b - 1 < (⌊b⌋₊ : ℝ) := Nat.sub_one_lt_floor b
      have : (⌈u⌉₊ : ℝ) < ⌊b⌋₊ + 1 + 1 := by nlinarith
      exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
    rw [Nat.cast_sub hc]
    push_cast
    have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by positivity)
    linarith
  have hPset : {p : ℕ | p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ b} = ↑P := by
    ext p
    simp only [mem_setOf_eq, hP, hI, Finset.coe_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, h1, h2⟩
      exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨hp, Nat.ceil_le.mp h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))⟩
  have hHBu := hHB u u b hu le_rfl (by rw [hb]; nlinarith) (by rw [hbu]; exact window_long hX hu)
  rw [hPset, Set.ncard_coe_finset, hbu] at hHBu
  -- `(1 - L⁻³)/log(2u) ≥ 0.99/log u`
  have hL3 : Real.log u ^ (-3 : ℤ) ≤ 1 / 100 := by
    rw [zpow_neg, zpow_ofNat, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10 ^ 8) hLu 3]
  have hl2 : Real.log (2 * u) = Real.log 2 + Real.log u := Real.log_mul (by norm_num) hu0.ne'
  have hlog2 := Real.log_two_lt_d9
  have hlog2p := Real.log_two_gt_d9
  have hP99 : 0.99 * (κ * u) / Real.log u ≤ (P.card : ℝ) := by
    refine le_trans ?_ hHBu
    rw [hl2, div_le_div_iff₀ (by linarith) (by linarith)]
    have h0 : 0 ≤ Real.log u ^ (-3 : ℤ) := by positivity
    have hpos : 0 ≤ κ * u := hκu0.le
    have : 0.99 * (Real.log 2 + Real.log u) ≤ (1 - Real.log u ^ (-3 : ℤ)) * Real.log u := by
      have hk : Real.log u ^ (-3 : ℤ) * Real.log u ≤ 1 := by
        rw [zpow_neg, zpow_ofNat]
        rw [inv_mul_le_iff₀ (by positivity), mul_one]
        have h1 : (1 : ℝ) ≤ Real.log u := by linarith
        nlinarith [mul_le_mul h1 h1 zero_le_one (by linarith)]
      nlinarith
    nlinarith
  have hS' : (S.card : ℝ) ≤ κ * u + 1 - 0.99 * (κ * u) / Real.log u := by
    have : (S.card : ℝ) + P.card ≤ I.card := by exact_mod_cast hcard
    linarith
  unfold Target.rhoDet Target.rigidCount
  rw [← hb, div_le_iff₀ hκu0]
  have e : (1 + 1 / (κ * u) - 0.99 / Real.log u) * (κ * u) =
      κ * u + 1 - 0.99 * (κ * u) / Real.log u := by
    have hκne : κ ≠ 0 := hκ0.ne'
    have hune : u ≠ 0 := hu0.ne'
    have hlne : Real.log u ≠ 0 := by linarith
    field_simp
  rw [e]
  exact hS'

lemma rhoDet_nonneg (X₀ : ℕ) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 ≤ u) : 0 ≤ Target.rhoDet X₀ κ u :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hu)

/-- `ρ_det` is interval integrable on `[X₀, x]` (a finite sum of ramps there). -/
lemma intervalIntegrable_rhoDet (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) : IntervalIntegrable (Target.rhoDet X₀ κ) volume (X₀ : ℝ) x := by
  classical
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  set Sb := Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀ with hSb
  have hX01 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX0
  set F : ℝ → ℝ := fun u => ∑ n ∈ Sb, (Icc ((n : ℝ) / (1 + κ)) n).indicator
    (fun u => 1 / (κ * u)) u with hF
  have hFeq : ∀ u ∈ Ioc (X₀ : ℝ) x, Target.rhoDet X₀ κ u = F u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hset : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)) =
        Sb.filter (fun n : ℕ => u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u) := by
      ext n
      simp only [Finset.mem_filter, hSb, Nat.mem_smoothNumbersUpTo]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h4 : (n : ℝ) ≤ (1 + κ) * u :=
          (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
        refine ⟨⟨Nat.le_floor ?_, h2⟩, h3, h4⟩
        nlinarith [hu.2]
      · rintro ⟨⟨-, h2⟩, h3, h4⟩
        exact ⟨⟨Nat.le_floor h4, h2⟩, h3⟩
    unfold Target.rhoDet Target.rigidCount
    rw [hset, hF]
    simp only
    rw [div_eq_mul_one_div, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u
    · have hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n :=
        ⟨by rw [div_le_iff₀ (by linarith)]; linarith [h.2], h.1⟩
      rw [if_pos h, Set.indicator_of_mem hmem]; simp
    · have hmem : u ∉ Icc ((n : ℝ) / (1 + κ)) n := by
        rintro ⟨h1, h2⟩
        apply h
        refine ⟨h2, ?_⟩
        rw [div_le_iff₀ (by linarith)] at h1; linarith
      rw [if_neg h, Set.indicator_of_notMem hmem]; simp
  have hcont : ContinuousOn (fun u : ℝ => 1 / (κ * u)) (Icc (X₀ : ℝ) x) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
    intro u hu
    have : (0 : ℝ) < u := by linarith [hu.1]
    exact (mul_pos hκ this).ne'
  have hFint : IntegrableOn F (Ioc (X₀ : ℝ) x) := by
    simp only [hF]
    refine integrable_finset_sum _ fun n _ => ?_
    have h1 : IntegrableOn (fun u : ℝ => 1 / (κ * u)) (Ioc (X₀ : ℝ) x) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    exact h1.indicator measurableSet_Icc
  exact hFint.congr_fun (fun u hu => (hFeq u hu).symm) measurableSet_Ioc

/-! ### The absorbed part -/

section Absorbed

variable {b : ℝ} (A : Set ℝ)

lemma measurable_absorbedBump (b : ℝ) (u : ℝ → ℝ) (a : ℝ) :
    Measurable (Absorbed.absorbedBump b A u a) := by
  unfold Absorbed.absorbedBump
  split_ifs
  · exact (measurable_id.pow_const _).indicator measurableSet_Icc
  · exact measurable_const

/-- On `[0, x]` only the `a ≤ x + x^b` contribute to `ρ_A` (as `u_a + u_a^b = a`). -/
lemma absorbedDensity_eq_sum (hA : Absorbed.LocFin A) (hb : 0 < b) {x v : ℝ} (hv0 : 0 ≤ v)
    (hvx : v ≤ x) :
    Absorbed.absorbedDensity b A (fun n => Construction.solveU b n) v =
      ∑ a ∈ Absorbed.below hA (x + x ^ b),
        Absorbed.absorbedBump b A (fun n => Construction.solveU b n) a v := by
  unfold Absorbed.absorbedDensity
  apply tsum_eq_sum
  intro a ha
  unfold Absorbed.absorbedBump
  split_ifs with hA'
  · apply Set.indicator_of_notMem
    intro hmem
    apply ha
    rw [Absorbed.mem_below]
    refine ⟨hA', ?_⟩
    have ha0 : 0 ≤ a := le_trans hv0 hmem.2
    obtain ⟨h0, heq⟩ := Construction.solveU_spec hb ha0
    have h1 : Construction.solveU b a ^ b ≤ v ^ b := Real.rpow_le_rpow h0 hmem.1 hb.le
    have h2 : v ^ b ≤ x ^ b := Real.rpow_le_rpow hv0 hvx hb.le
    linarith [hmem.1]
  · rfl

lemma absorbedDensity_nonneg {v : ℝ} (hv : 0 ≤ v) (u : ℝ → ℝ) :
    0 ≤ Absorbed.absorbedDensity b A u v := by
  unfold Absorbed.absorbedDensity
  refine tsum_nonneg fun a => ?_
  unfold Absorbed.absorbedBump
  split_ifs
  · exact Set.indicator_apply_nonneg (fun _ => Real.rpow_nonneg hv _)
  · exact le_rfl

/-- `0 ≤ ρ̄_A(v) ≤ 0.1/log v` for `v ≥ 1`. -/
lemma absorbedDensityCap_mem {v : ℝ} (hv : 1 ≤ v) (u : ℝ → ℝ) :
    0 ≤ Absorbed.absorbedDensityCap b A u v ∧
      Absorbed.absorbedDensityCap b A u v ≤ 0.1 / Real.log v := by
  unfold Absorbed.absorbedDensityCap
  exact ⟨le_min (absorbedDensity_nonneg A (by linarith) u)
    (div_nonneg (by norm_num) (Real.log_nonneg hv)), min_le_right _ _⟩

/-- `ρ̄_A` is interval integrable on `[X, x]`, `X > 1`, for every locally finite `A`. -/
lemma intervalIntegrable_absorbedDensityCap (hA : Absorbed.LocFin A) (hb : 0 < b) {X x : ℝ}
    (hX : 1 < X) (hXx : X ≤ x) :
    IntervalIntegrable (Absorbed.absorbedDensityCap b A (fun n => Construction.solveU b n))
      volume X x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXx]
  set g : ℝ → ℝ := fun v => min (∑ a ∈ Absorbed.below hA (x + x ^ b),
    Absorbed.absorbedBump b A (fun n => Construction.solveU b n) a v) (0.1 / Real.log v) with hg
  have hgm : Measurable g :=
    (Finset.measurable_sum _ fun a _ => measurable_absorbedBump A b _ a).min
      (measurable_const.div Real.measurable_log)
  have heq : EqOn (Absorbed.absorbedDensityCap b A (fun n => Construction.solveU b n)) g
      (Ioc X x) := by
    intro v hv
    simp only [hg, Absorbed.absorbedDensityCap]
    rw [absorbedDensity_eq_sum A hA hb (by linarith [hv.1]) hv.2]
  refine IntegrableOn.congr_fun ?_ heq.symm measurableSet_Ioc
  refine ⟨hgm.aestronglyMeasurable, HasFiniteIntegral.restrict_of_bounded (C := 0.1 / Real.log X)
    measure_Ioc_lt_top ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => ?_)
  have hv1 : 1 ≤ v := by linarith [hv.1]
  rw [← heq hv]
  obtain ⟨h0, h1⟩ := absorbedDensityCap_mem A hv1 (b := b) (fun n => Construction.solveU b n)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine h1.trans ?_
  have hlX : 0 < Real.log X := Real.log_pos hX
  exact div_le_div_of_nonneg_left (by norm_num) hlX (Real.log_le_log (by linarith) hv.1.le)

end Absorbed

/-! ### The oscillation slope -/

/-- `2y ≤ e^y`. -/
lemma two_mul_le_exp (y : ℝ) : 2 * y ≤ Real.exp y := by
  rcases le_or_gt y 0 with h | h
  · linarith [Real.exp_pos y]
  · have := Real.quadratic_le_exp_of_nonneg h.le
    nlinarith [sq_nonneg (y - 1)]

/-- `ϕ'(t) = 0` for `t ≤ 0`: there `ϕ = 0` is a minimum of `ϕ ≥ 0`. -/
lemma deriv_smoothTransition_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.smoothTransition.zero_of_nonpos ht]
  exact Real.smoothTransition.nonneg s

/-- `R_k' = 0` on `(0, x⁺_k]`. -/
lemma deriv_oscTerm_of_le {θ α γ xk x : ℝ} (hx : 0 < x) (hxk : x ≤ xk) :
    deriv (Oscillation.oscTerm θ α γ xk) x = 0 := by
  have hxk0 : 0 < xk := lt_of_lt_of_le hx hxk
  have ht : Real.log (x / xk) ≤ 0 :=
    Real.log_nonpos (div_pos hx hxk0).le ((div_le_one hxk0).mpr hxk)
  rw [(Oscillation.hasDerivAt_oscTerm hx hxk0).deriv, Real.smoothTransition.zero_of_nonpos ht,
    deriv_smoothTransition_of_nonpos ht]
  ring

/-- **The slope of one oscillation** (proof of Lemma 3.3): for `x ≥ x⁺ = x_k`, with `L = log x⁺ ≥
384`, `κ₀ = 1/4`, `γ ∈ [Γ, 2Γ]` and `α = κ₀ (x⁺)^{1-θ}/(L³ γ)`,
`|R_k'(x)| ≤ 11/(L² log x)`. -/
lemma abs_deriv_oscTerm_le_of_ge {θ γ xk x : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hxk : 0 < xk) (hL : 384 ≤ Real.log xk)
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ Construction.kappa0Param xk)
      (2 * DesignedZero.heightScale θ Construction.kappa0Param xk)) (hx : xk ≤ x) :
    |deriv (Oscillation.oscTerm θ (DesignedZero.amplitudeOf θ Construction.kappa0Param γ xk) γ xk)
      x| ≤ 11 / (Real.log xk ^ 2 * Real.log x) := by
  set L := Real.log xk with hLdef
  have hx0 : 0 < x := lt_of_lt_of_le hxk hx
  set ℓ := Real.log x with hℓdef
  have hLℓ : L ≤ ℓ := Real.log_le_log hxk hx
  have hL0 : 0 < L := by linarith
  set Γ := DesignedZero.heightScale θ Construction.kappa0Param xk with hΓ
  have hxkθ : 0 < xk ^ (1 - θ) := Real.rpow_pos_of_pos hxk _
  have hΓ0 : 0 < Γ := by
    rw [hΓ]; unfold DesignedZero.heightScale Construction.kappa0Param; positivity
  have hγ0 : 0 < γ := lt_of_lt_of_le hΓ0 hγ.1
  set α := DesignedZero.amplitudeOf θ Construction.kappa0Param γ xk with hα
  have hαγ : α * γ = 2 * Γ := by
    rw [hα, hΓ]; unfold DesignedZero.amplitudeOf DesignedZero.heightScale
    field_simp
  have hα0 : 0 < α := by
    rw [hα]; unfold DesignedZero.amplitudeOf Construction.kappa0Param; positivity
  have hα2 : α ≤ 2 := by
    have : α * γ ≤ 2 * γ := by rw [hαγ]; nlinarith [hγ.1]
    nlinarith
  have hb := Oscillation.abs_deriv_oscTerm_le (θ := θ) (α := α) (γ := γ) hx0 hxk
  rw [abs_of_pos hα0, abs_of_nonneg (show (0 : ℝ) ≤ θ by linarith), abs_of_pos hγ0] at hb
  -- exponential forms
  have hxe : x = Real.exp ℓ := (Real.exp_log hx0).symm
  have hxke : xk = Real.exp L := (Real.exp_log hxk).symm
  have hxθ : x ^ (θ - 1) = Real.exp ((θ - 1) * ℓ) := by
    rw [Real.rpow_def_of_pos hx0, ← hℓdef]; ring_nf
  have hxkθ' : xk ^ (1 - θ) = Real.exp ((1 - θ) * L) := by
    rw [Real.rpow_def_of_pos hxk, ← hLdef]; ring_nf
  set E := Real.exp ((L - ℓ) / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- `x^{θ-1} ≤ E e^{-L/2}` and `x^{θ-1} (x⁺)^{1-θ} ≤ E`
  have h1 : x ^ (θ - 1) ≤ E * Real.exp (-L / 2) := by
    rw [hxθ, hE, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have h2 : x ^ (θ - 1) * xk ^ (1 - θ) ≤ E := by
    rw [hxθ, hxkθ', ← Real.exp_add, hE]; apply Real.exp_le_exp.mpr; nlinarith
  -- `E ℓ ≤ 2 L`
  have h3 : E * ℓ ≤ 2 * L := by
    set t := ℓ - L with ht
    have ht0 : 0 ≤ t := by linarith
    have hEt : E = Real.exp (-(t / 2)) := by rw [hE]; congr 1; ring
    have hE1 : E ≤ 1 := by rw [hEt]; exact Real.exp_le_one_iff.mpr (by linarith)
    have htE : t * E ≤ 1 := by
      have h := two_mul_le_exp (t / 2)
      rw [hEt, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have : E * ℓ = E * L + t * E := by rw [ht]; ring
    nlinarith
  -- `e^{-L/2} ≤ 1/L³`
  have h4 : Real.exp (-L / 2) * L ^ 3 ≤ 1 := by
    have h := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 4
    have e4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [e4] at h
    have h5 : L ^ 3 ≤ Real.exp (L / 2) := by nlinarith [pow_pos hL0 3]
    rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  -- assemble
  have h2Γ : 2 * Γ = Construction.kappa0Param * xk ^ (1 - θ) / L ^ 3 := by
    rw [hΓ]; unfold DesignedZero.heightScale; rw [← hLdef]; field_simp
  have hk : Construction.kappa0Param = 1 / 4 := rfl
  have hxθ0 : 0 ≤ x ^ (θ - 1) := Real.rpow_nonneg hx0.le _
  have hℓ0 : 0 < ℓ := by linarith
  have key : α * x ^ (θ - 1) * (θ + γ + 2) ≤ E * (5 * Real.exp (-L / 2) + 1 / (4 * L ^ 3)) := by
    have e : α * x ^ (θ - 1) * (θ + γ + 2) =
        α * (θ + 2) * x ^ (θ - 1) + (x ^ (θ - 1) * xk ^ (1 - θ)) / (4 * L ^ 3) := by
      have : α * γ = xk ^ (1 - θ) / (4 * L ^ 3) := by rw [hαγ, h2Γ, hk]; field_simp
      calc α * x ^ (θ - 1) * (θ + γ + 2) = α * (θ + 2) * x ^ (θ - 1) +
            (α * γ) * x ^ (θ - 1) := by ring
        _ = _ := by rw [this]; field_simp
    rw [e]
    have hα5 : α * (θ + 2) ≤ 5 := by nlinarith
    have hp1 : α * (θ + 2) * x ^ (θ - 1) ≤ 5 * (E * Real.exp (-L / 2)) :=
      mul_le_mul hα5 h1 hxθ0 (by norm_num)
    have hp2 : (x ^ (θ - 1) * xk ^ (1 - θ)) / (4 * L ^ 3) ≤ E / (4 * L ^ 3) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have : E * (5 * Real.exp (-L / 2) + 1 / (4 * L ^ 3)) =
        5 * (E * Real.exp (-L / 2)) + E / (4 * L ^ 3) := by ring
    linarith
  refine hb.trans (key.trans ?_)
  rw [le_div_iff₀ (by positivity)]
  have hL3 : 0 < L ^ 3 := by positivity
  have h5 : 5 * Real.exp (-L / 2) + 1 / (4 * L ^ 3) ≤ 5.25 / L ^ 3 := by
    have : Real.exp (-L / 2) ≤ 1 / L ^ 3 := by rw [le_div_iff₀ hL3]; exact h4
    have e : 5.25 / L ^ 3 = 5 * (1 / L ^ 3) + 1 / (4 * L ^ 3) := by field_simp; norm_num
    linarith
  calc E * (5 * Real.exp (-L / 2) + 1 / (4 * L ^ 3)) * (L ^ 2 * ℓ)
      ≤ E * (5.25 / L ^ 3) * (L ^ 2 * ℓ) := by gcongr
    _ = (E * ℓ) * 5.25 / L := by field_simp
    _ ≤ (2 * L) * 5.25 / L := by gcongr
    _ ≤ 11 := by
        rw [show 2 * L * 5.25 / L = 10.5 by field_simp; norm_num]; norm_num

/-- `log x⁺_k ≥ 2^k X₀²` for the switch-on points `x⁺_0 = e^{X₀²}`, `x⁺_{k+1} = e^{x⁺_k}`. -/
lemma log_switchOn_ge (X : ℝ) (k : ℕ) :
    2 ^ k * X ^ 2 ≤ Real.log (Construction.switchOn X k) := by
  induction k with
  | zero => rw [Construction.log_switchOn_zero]; simp
  | succ k ih =>
    have e : Real.log (Construction.switchOn X (k + 1)) = Construction.switchOn X k :=
      Real.log_exp _
    rw [e]
    have h := two_mul_le_exp (Real.log (Construction.switchOn X k))
    rw [Real.exp_log (Construction.switchOn_pos X k)] at h
    rw [pow_succ]
    linarith

lemma nat_lt_switchOn {X : ℝ} (hX : 1 ≤ X) (k : ℕ) : (k : ℝ) < Construction.switchOn X k := by
  have h1 := log_switchOn_ge X k
  have h2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have h3 := Real.add_one_le_exp (Real.log (Construction.switchOn X k))
  rw [Real.exp_log (Construction.switchOn_pos X k)] at h3
  have : (2 : ℝ) ^ k ≤ 2 ^ k * X ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
  linarith

/-- On `(0, x⁺_K]` the oscillation is the finite sum of its first `K` terms. -/
lemma osc_eq_finsum {θ : ℝ} (α γ : ℕ → ℝ) (X : ℝ) {K : ℕ} {y : ℝ} (hy : 0 < y)
    (hyK : y ≤ Construction.switchOn X K) :
    Oscillation.osc θ α γ (Construction.switchOn X) y =
      ∑ k ∈ Finset.range K, Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k) y := by
  unfold Oscillation.osc
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  exact Oscillation.oscTerm_eq_zero_of_le hy (hyK.trans (Construction.switchOn_mono X hk))

/-- The oscillation is differentiable on `(0, ∞)`, its derivative being the (locally finite) sum
of the derivatives of the `R_k`. -/
lemma hasDerivAt_osc {θ : ℝ} (α γ : ℕ → ℝ) {X : ℝ} (hX : 1 ≤ X) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Oscillation.osc θ α γ (Construction.switchOn X))
      (∑ k ∈ Finset.range (⌈x⌉₊ + 1),
        deriv (Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k)) x) x := by
  set K := ⌈x⌉₊ + 1
  have hxK : x < Construction.switchOn X K := by
    have := nat_lt_switchOn hX K
    have : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    push_cast [K] at *
    linarith
  have hsum : HasDerivAt (fun y => ∑ k ∈ Finset.range K,
      Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k) y)
      (∑ k ∈ Finset.range K,
        deriv (Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k)) x) x :=
    HasDerivAt.fun_sum fun k _ =>
      (Oscillation.hasDerivAt_oscTerm hx (Construction.switchOn_pos X k)).differentiableAt
        |>.hasDerivAt
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx hxK] with y hy
  exact osc_eq_finsum α γ X hy.1 hy.2.le

/-- **The oscillation slope bound** (proof of Lemma 3.3): `|R'(x)| ≤ 0.02/log x` for `x ≥ X₀`,
for heights in the designed range and the designed amplitudes. -/
theorem abs_deriv_osc_le {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) :
    |deriv (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) x| ≤ 0.02 / Real.log x := by
  set X : ℝ := (X₀ : ℝ) with hXdef
  have hX1 : 1 < X := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hx0 : 0 < x := by linarith
  have hℓ : 10 ^ 8 ≤ Real.log x := hX.trans (Real.log_le_log (by linarith) hx)
  have hℓ0 : 0 < Real.log x := by linarith
  have hX2 : (10 : ℝ) ^ 8 ≤ X := by
    have := Real.add_one_le_exp (Real.log X); rw [Real.exp_log (by linarith)] at this; linarith
  rw [(hasDerivAt_osc _ γ hX1.le hx0).deriv]
  set α := Construction.amplitudes θ Construction.kappa0Param (Construction.switchOn X) γ
  have hterm : ∀ k, |deriv (Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k)) x| ≤
      11 / (X ^ 4 * Real.log x) * (1 / 4) ^ k := by
    intro k
    have hxk := Construction.switchOn_pos X k
    have hLk := log_switchOn_ge X k
    have hX4 : (0 : ℝ) < X ^ 4 := by positivity
    rcases le_or_gt x (Construction.switchOn X k) with h | h
    · rw [deriv_oscTerm_of_le hx0 h, abs_zero]; positivity
    · have hL384 : 384 ≤ Real.log (Construction.switchOn X k) := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      refine (abs_deriv_oscTerm_le_of_ge hθ.1 (by linarith [hθ.2]) hxk hL384 (hγ k) h.le).trans ?_
      have hsq : 4 ^ k * X ^ 4 ≤ Real.log (Construction.switchOn X k) ^ 2 := by
        have h0 : (0 : ℝ) ≤ 2 ^ k * X ^ 2 := by positivity
        have := pow_le_pow_left₀ h0 hLk 2
        calc (4 : ℝ) ^ k * X ^ 4 = (2 ^ k * X ^ 2) ^ 2 := by
              rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
                mul_comm 2 k]
          _ ≤ _ := this
      rw [div_le_iff₀ (by positivity)]
      have e : 11 / (X ^ 4 * Real.log x) * (1 / 4) ^ k *
          (Real.log (Construction.switchOn X k) ^ 2 * Real.log x) =
          11 * (Real.log (Construction.switchOn X k) ^ 2 / (4 ^ k * X ^ 4)) := by
        rw [one_div_pow]; field_simp
      rw [e]
      have : 1 ≤ Real.log (Construction.switchOn X k) ^ 2 / (4 ^ k * X ^ 4) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
  calc |∑ k ∈ Finset.range (⌈x⌉₊ + 1),
        deriv (Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k)) x|
      ≤ ∑ k ∈ Finset.range (⌈x⌉₊ + 1),
        |deriv (Oscillation.oscTerm θ (α k) (γ k) (Construction.switchOn X k)) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (⌈x⌉₊ + 1), 11 / (X ^ 4 * Real.log x) * (1 / 4) ^ k :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 11 / (X ^ 4 * Real.log x) * ∑ k ∈ Finset.range (⌈x⌉₊ + 1), (1 / 4 : ℝ) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ 11 / (X ^ 4 * Real.log x) * (4 / 3) :=
        mul_le_mul_of_nonneg_left (Construction.sum_inv_four_pow_le _) (by positivity)
    _ ≤ 0.02 / Real.log x := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hℓ0]
        have : (10 : ℝ) ^ 8 ≤ X ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hX2 4]
        nlinarith

/-- The oscillation is `0.01`-Lipschitz on `[X₀, ∞)`. -/
theorem osc_lipschitz {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) {x x' : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hx' : (X₀ : ℝ) ≤ x') :
    |Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀) x' -
      Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀) x| ≤ 0.01 * |x' - x| := by
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Ici (X₀ : ℝ))
    (f := Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
        (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) (C := 0.01)
    (fun y hy => (hasDerivAt_osc _ γ hX1.le (by linarith [mem_Ici.mp hy])).differentiableAt)
    (fun y hy => by
      have hy' : (X₀ : ℝ) ≤ y := hy
      have hl : 10 ^ 8 ≤ Real.log y := hX.trans (Real.log_le_log (by linarith) hy')
      rw [Real.norm_eq_abs]
      refine (abs_deriv_osc_le hθ hX hγ hy').trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith)
    (convex_Ici _) hx hx'
  simpa [Real.norm_eq_abs] using h

/-! ### Assembly: the slope of the continuous part -/

/-- The increment of `C` over `[x, x']`. -/
lemma contPart_sub {X₀ : ℕ} {κ : ℝ} {rhoA R : ℝ → ℝ} {x x' : ℝ}
    (hd : ∀ y, (X₀ : ℝ) ≤ y → IntervalIntegrable (Target.rhoDet X₀ κ) volume X₀ y)
    (ha : ∀ y, (X₀ : ℝ) ≤ y → IntervalIntegrable rhoA volume X₀ y)
    (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    contPart X₀ κ rhoA R x' - contPart X₀ κ rhoA R x =
      (x' - x) - (∫ u in x..x', Target.rhoDet X₀ κ u) - (∫ u in x..x', rhoA u) +
        (R x' - R x) := by
  have h1 := intervalIntegral.integral_interval_sub_left (hd x' (hx.trans hxx)) (hd x hx)
  have h2 := intervalIntegral.integral_interval_sub_left (ha x' (hx.trans hxx)) (ha x hx)
  unfold contPart
  linarith

/-- **Upper slope bound**: `C(x') - C(x) ≤ 1.01 (x' - x)` (`ρ_det, ρ̄_A ≥ 0`, `|R'| ≤ 0.01`). -/
theorem contPart_upper {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) (A : Set ℝ)
    (hA : Absorbed.LocFin A) {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    contPart X₀ (Construction.kappaParam X₀)
        (Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n))
        (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
          (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) x' -
      contPart X₀ (Construction.kappaParam X₀)
        (Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n))
        (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
          (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) x ≤ 1.01 * (x' - x) := by
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  rw [contPart_sub (fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy)
    (fun y hy => intervalIntegrable_absorbedDensityCap A hA hb hX1 hy) hx hxx]
  have h1 : 0 ≤ ∫ u in x..x', Target.rhoDet X₀ (Construction.kappaParam X₀) u :=
    intervalIntegral.integral_nonneg hxx fun u hu => rhoDet_nonneg X₀ hκ0 (by linarith [hu.1])
  have h2 : 0 ≤ ∫ u in x..x',
      Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n) u :=
    intervalIntegral.integral_nonneg hxx fun u hu =>
      (absorbedDensityCap_mem A (by linarith [hu.1]) _).1
  have h3 := osc_lipschitz hθ hX hγ hx (hx.trans hxx)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x' - x)] at h3
  have h4 := (abs_le.mp h3).2
  linarith

/-- A function continuous on every `[X, y]` is continuous on `[X, ∞)`. -/
lemma continuousOn_Ici_of_Icc {f : ℝ → ℝ} {X : ℝ} (h : ∀ y, X ≤ y → ContinuousOn f (Icc X y)) :
    ContinuousOn f (Ici X) := by
  intro z hz
  have hz' : X ≤ z := hz
  refine ((h (z + 1) (by linarith)) z ⟨hz', by linarith⟩).mono_of_mem_nhdsWithin ?_
  rw [show Icc X (z + 1) = Ici X ∩ Iic (z + 1) by ext; simp]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- `x ↦ ∫_X^x f` is continuous on `[X, ∞)` if `f` is interval integrable on every `[X, y]`. -/
lemma continuousOn_primitive_Ici {f : ℝ → ℝ} {X : ℝ}
    (h : ∀ y, X ≤ y → IntervalIntegrable f volume X y) :
    ContinuousOn (fun x => ∫ u in X..x, f u) (Ici X) := by
  refine continuousOn_Ici_of_Icc fun y hy => ?_
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff' (by simp)).mp (h y hy))
  rwa [uIcc_of_le hy] at this

/-- **`C` is continuous on `[X₀, ∞)`.** -/
theorem contPart_continuousOn {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (γ : ℕ → ℝ) (A : Set ℝ) (hA : Absorbed.LocFin A) :
    ContinuousOn (contPart X₀ (Construction.kappaParam X₀)
        (Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n))
        (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
          (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀))) (Ici (X₀ : ℝ)) := by
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  have hR : ContinuousOn (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
      (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) (Ici (X₀ : ℝ)) := fun y hy =>
    (hasDerivAt_osc _ γ hX1.le (by linarith [mem_Ici.mp hy])).continuousAt.continuousWithinAt
  unfold contPart
  refine (((continuousOn_id.sub continuousOn_const).sub
    (continuousOn_primitive_Ici fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy)).sub
    (continuousOn_primitive_Ici fun y hy =>
      intervalIntegrable_absorbedDensityCap A hA hb hX1 hy)).add (hR.sub continuousOn_const)

/-- The comparison function `c(u) = 1/log(max(u, X))`, continuous for `X > 1`. -/
lemma continuous_invLogMax {X : ℝ} (hX : 1 < X) :
    Continuous fun u : ℝ => 1 / Real.log (max u X) := by
  have hm : Continuous fun u : ℝ => max u X := continuous_id.max continuous_const
  have hpos : ∀ u : ℝ, 0 < Real.log (max u X) := fun u =>
    Real.log_pos (lt_of_lt_of_le hX (le_max_right _ _))
  refine continuous_const.div ?_ fun u => (hpos u).ne'
  exact (Real.continuousOn_log.comp_continuous hm fun u => by
    have := lt_of_lt_of_le (by linarith : (0 : ℝ) < X) (le_max_right u X); exact this.ne')

/-- **Lower slope bound (Lemma 3.3)**: `C(x') - C(x) ≥ 0.08 (x' - x)/log x'`, from (84). -/
theorem contPart_lower {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) {γ : ℕ → ℝ} (hγ : DesignedRange θ X₀ γ) (A : Set ℝ)
    (hA : Absorbed.LocFin A) (hHB : ShortIntervalPNTFrom X₀) {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hxx : x ≤ x') :
    0.08 * (x' - x) / Real.log x' ≤
      contPart X₀ (Construction.kappaParam X₀)
        (Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n))
        (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
          (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) x' -
      contPart X₀ (Construction.kappaParam X₀)
        (Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n))
        (Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
          (Construction.switchOn X₀) γ) γ (Construction.switchOn X₀)) x := by
  have hX1 : (1 : ℝ) < (X₀ : ℝ) := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  set κ := Construction.kappaParam (X₀ : ℝ) with hκ
  set ρA := Absorbed.absorbedDensityCap (θ / 2) A (fun n => Construction.solveU (θ / 2) n)
  set R := Oscillation.osc θ (Construction.amplitudes θ Construction.kappa0Param
    (Construction.switchOn (X₀ : ℝ)) γ) γ (Construction.switchOn (X₀ : ℝ)) with hRdef
  set c : ℝ → ℝ := fun u => 1 / Real.log (max u (X₀ : ℝ)) with hc
  have hcc : Continuous c := continuous_invLogMax hX1
  have hcu : ∀ u, (X₀ : ℝ) ≤ u → c u = 1 / Real.log u := fun u hu => by
    simp only [hc, max_eq_left hu]
  have hd : ∀ y, (X₀ : ℝ) ≤ y → IntervalIntegrable (Target.rhoDet X₀ κ) volume (X₀ : ℝ) y :=
    fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy
  have ha : ∀ y, (X₀ : ℝ) ≤ y → IntervalIntegrable ρA volume (X₀ : ℝ) y :=
    fun y hy => intervalIntegrable_absorbedDensityCap A hA hb hX1 hy
  rw [contPart_sub hd ha hx hxx]
  have hx'X : (X₀ : ℝ) ≤ x' := hx.trans hxx
  -- integrability on `[x, x']`
  have hdx : IntervalIntegrable (Target.rhoDet X₀ κ) volume x x' :=
    ((hd x hx).symm.trans (hd x' hx'X))
  have hax : IntervalIntegrable ρA volume x x' := ((ha x hx).symm.trans (ha x' hx'X))
  have hcx : IntervalIntegrable c volume x x' := hcc.intervalIntegrable _ _
  -- the pointwise margin: `ρ_det + ρ̄_A ≤ 1 - 0.88 c`
  have hpt : ∀ u ∈ Icc x x', Target.rhoDet X₀ κ u + ρA u ≤ 1 - 0.88 * c u := by
    intro u hu
    have hXu : (X₀ : ℝ) ≤ u := hx.trans hu.1
    have hl : 10 ^ 8 ≤ Real.log u := hX.trans (Real.log_le_log (by linarith) hXu)
    have h1 := rhoDet_le hX hHB hXu
    have h2 := (absorbedDensityCap_mem A (b := θ / 2) (v := u) (by linarith)
      (fun n => Construction.solveU (θ / 2) n)).2
    have h3 := Positivity.inv_kappa_mul_le (by linarith) hX hXu
    have e : ((X₀ : ℝ) : ℝ) ^ (-(5 / 12 - 1 / 50 : ℝ)) = κ := by
      rw [hκ, Construction.kappaParam]; norm_num
    rw [e] at h3
    rw [hcu u hXu]
    have e2 : 1 - 0.88 * (1 / Real.log u) =
        1 + 0.01 / Real.log u - 0.99 / Real.log u + 0.1 / Real.log u := by ring
    rw [e2]
    linarith
  have hI1 : (∫ u in x..x', Target.rhoDet X₀ κ u) + (∫ u in x..x', ρA u) ≤
      (x' - x) - 0.88 * ∫ u in x..x', c u := by
    rw [← intervalIntegral.integral_add hdx hax]
    have := intervalIntegral.integral_mono_on hxx (hdx.add hax)
      ((intervalIntegrable_const (c := (1 : ℝ))).sub (hcx.const_mul 0.88)) hpt
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcx.const_mul 0.88),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
      mul_one] at this
    exact this
  -- the oscillation: `R(x') - R(x) ≥ -0.02 ∫_x^{x'} c`
  have hRmono : MonotoneOn (fun u => R u + 0.02 * ∫ t in (X₀ : ℝ)..u, c t) (Ici (X₀ : ℝ)) := by
    have hder : ∀ u, (X₀ : ℝ) < u → HasDerivAt (fun u => R u + 0.02 * ∫ t in (X₀ : ℝ)..u, c t)
        (deriv R u + 0.02 * c u) u := by
      intro u hu
      exact (hasDerivAt_osc _ γ hX1.le (by linarith)).differentiableAt.hasDerivAt.add
        ((hcc.integral_hasStrictDerivAt (X₀ : ℝ) u).hasDerivAt.const_mul 0.02)
    refine monotoneOn_of_deriv_nonneg (convex_Ici (X₀ : ℝ)) ?_ ?_ ?_
    · intro u hu
      refine ContinuousAt.continuousWithinAt ?_
      exact ((hasDerivAt_osc _ γ hX1.le (by linarith [mem_Ici.mp hu])).continuousAt).add
        ((hcc.integral_hasStrictDerivAt (X₀ : ℝ) u).hasDerivAt.continuousAt.const_mul 0.02)
    · rw [interior_Ici]
      exact fun u hu => (hder u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro u hu
      have hu' : (X₀ : ℝ) < u := hu
      rw [(hder u hu').deriv, hcu u hu'.le]
      have := abs_deriv_osc_le hθ hX hγ hu'.le
      have := (abs_le.mp this).1
      rw [hRdef]
      have e : (0.02 : ℝ) * (1 / Real.log u) = 0.02 / Real.log u := by ring
      linarith
  have hRx := hRmono hx hx'X hxx
  simp only at hRx
  have hsplit := intervalIntegral.integral_interval_sub_left
    (hcc.intervalIntegrable (μ := volume) (X₀ : ℝ) x') (hcc.intervalIntegrable (X₀ : ℝ) x)
  have hRlow : -(0.02 * ∫ u in x..x', c u) ≤ R x' - R x := by
    rw [← hsplit]; linarith
  -- `∫_x^{x'} c ≥ (x' - x)/log x'`
  have hl' : 0 < Real.log x' := by
    have := hX.trans (Real.log_le_log (by linarith) hx'X); linarith
  have hcI : (x' - x) / Real.log x' ≤ ∫ u in x..x', c u := by
    have := intervalIntegral.integral_mono_on hxx intervalIntegrable_const hcx
      (fun u hu => show 1 / Real.log x' ≤ c u by
        rw [hcu u (hx.trans hu.1)]
        have hl : 10 ^ 8 ≤ Real.log u := hX.trans (Real.log_le_log (by linarith) (hx.trans hu.1))
        exact one_div_le_one_div_of_le (by linarith)
          (Real.log_le_log (by linarith [hx.trans hu.1]) hu.2))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div]; linarith
  have hfin : 0.08 * (x' - x) / Real.log x' ≤ 0.86 * ((x' - x) / Real.log x') := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by norm_num)
      (div_nonneg (by linarith) hl'.le)
  nlinarith

end BModel

end
