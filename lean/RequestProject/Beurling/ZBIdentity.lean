module

public import RequestProject.Beurling.ZBConcrete
public import RequestProject.Beurling.TargetError

/-!
# Identity (15): the paper's `Z_B` equals `ZBcont` for `σ > 1`

The paper defines, for `σ > 1`,
`Z_B(s) = ∑_{n<X₀} n^{-s} + ∑_{d∈D, d≥X₀} d^{-s} + ∫_{X₀}^∞ x^{-s}(1 - ρ_det(x)) dx`
(`ZBpaper`), where `D` is the set of `X₀`-smooth integers and
`ρ_det(u) = Ψ([u,(1+κ)u], X₀)/(κu)` is the rigid density (4) (`Target.rhoDet`).

`ZBpaper_eq_ZBcont` proves that this equals `ZBcont` (formula (15) with its boundary terms), so
`ZBcont` is the analytic continuation of the paper's `Z_B` to `σ > 0`, `s ≠ 1`.

The proof writes `x^{-s} ρ_det(x) = ∑_{d∈D} 1_{[d/(1+κ), d]}(x) x^{-s-1}/κ` (each rigid `d`
contributes a ramp) and integrates term by term.
-/

@[expose] public section

open Complex Metric Set Finset MeasureTheory

namespace BaseFactor

/-- The paper's definition of the base factor (meaningful for `σ > 1`):
`Z_B(s) = ∑_{n<X₀} n^{-s} + ∑_{d∈D, d≥X₀} d^{-s} + ∫_{X₀}^∞ x^{-s}(1 - ρ_det(x)) dx`. -/
noncomputable def ZBpaper (X₀ : ℕ) (κ : ℝ) (s : ℂ) : ℂ :=
  open Classical in
  headSum X₀ s + (∑' d : ℕ, if d ∈ X₀.smoothNumbers ∧ X₀ ≤ d then ((d : ℝ) : ℂ) ^ (-s) else 0) +
    ∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s) * (1 - (Target.rhoDet X₀ κ x : ℂ))

/-- The ramp of the rigid element `d`: `1_{[d/(1+κ), d]}(x) x^{-s-1}/κ`. -/
noncomputable def ramp (X₀ : ℕ) (κ : ℝ) (s : ℂ) (d : ℕ) (x : ℝ) : ℂ :=
  open Classical in
  if d ∈ X₀.smoothNumbers then
    Set.indicator (Icc ((d : ℝ) / (1 + κ)) d) (fun y : ℝ => (y : ℂ) ^ (-s - 1) / κ) x
  else 0

/-- The integral of a ramp over `(X₀, ∞)`. -/
noncomputable def rampVal (X₀ : ℕ) (κ : ℝ) (s : ℂ) (d : ℕ) : ℂ :=
  open Classical in
  (if d ∈ X₀.smoothNumbers ∧ X₀ ≤ d then Wfac κ s * ((d : ℝ) : ℂ) ^ (-s) else 0) -
    (if d ∈ boundarySet X₀ κ then
      ((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ) else 0)

lemma hasSum_smooth_cpow (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) :
    HasSum (fun d : ℕ => if d ∈ X₀.smoothNumbers then ((d : ℝ) : ℂ) ^ (-s) else 0)
      (Zinf X₀ s) := by
  classical
  set f : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-s) with hf
  have h1 : f 1 = 1 := by simp [hf]
  have hmul' : ∀ m n : ℕ, f (m * n) = f m * f n := by
    intro m n
    simp only [hf, Nat.cast_mul, Complex.ofReal_natCast]
    exact Complex.natCast_mul_natCast_cpow m n _
  have hpow : ∀ p n : ℕ, f (p ^ n) = f p ^ n := by
    intro p n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ, hmul', ih, pow_succ]
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    simp only [hf]
    rw [norm_cpow_neg hp]
    exact rpow_neg_lt_one hp hσ
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simp only [hpow, norm_pow]
    exact summable_geometric_of_lt_one (norm_nonneg _) (hnorm hp)
  obtain ⟨-, hh⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {m n} _ => hmul' m n) hsum X₀
  have hprod : (∏ p ∈ X₀.primesBelow, ∑' n : ℕ, f (p ^ n)) = Zinf X₀ s := by
    unfold Zinf
    apply Finset.prod_congr rfl
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    simp only [hpow]
    rw [tsum_geometric_of_norm_lt_one (hnorm hp')]
  rw [hprod] at hh
  have := (hasSum_subtype_iff_indicator (s := (X₀.smoothNumbers : Set ℕ)) (f := f)).mp hh
  convert this using 1
  funext d
  simp only [Set.indicator_apply, hf]

lemma hasSum_smooth_ge (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) :
    HasSum (fun d : ℕ => if d ∈ X₀.smoothNumbers ∧ X₀ ≤ d then ((d : ℝ) : ℂ) ^ (-s) else 0)
      (Zinf X₀ s - headSum X₀ s) := by
  classical
  have hlt : HasSum (fun d : ℕ => if d ∈ Finset.Ico 1 X₀ then ((d : ℝ) : ℂ) ^ (-s) else 0)
      (headSum X₀ s) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := Finset.Ico 1 X₀)
      (f := fun d : ℕ => if d ∈ Finset.Ico 1 X₀ then ((d : ℝ) : ℂ) ^ (-s) else 0)
      (fun d hd => if_neg hd)
    convert this using 1
    unfold headSum
    exact Finset.sum_congr rfl fun d hd => (if_pos hd).symm
  convert (hasSum_smooth_cpow X₀ hσ).sub hlt using 1
  funext d
  by_cases hd : d ∈ X₀.smoothNumbers
  · have h0 : d ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hd
    by_cases hX : X₀ ≤ d
    · have : d ∉ Finset.Ico 1 X₀ := by simp [Finset.mem_Ico]; omega
      simp [hd, hX, this]
    · have : d ∈ Finset.Ico 1 X₀ := by simp [Finset.mem_Ico]; omega
      simp [hd, hX, this]
  · have : d ∉ Finset.Ico 1 X₀ := by
      intro h
      have h' := Finset.mem_Ico.mp h
      exact hd (Nat.mem_smoothNumbers_of_lt (by omega) h'.2)
    simp [hd, this]

lemma hasSum_ramp (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun d => ramp X₀ κ s d x) ((x : ℂ) ^ (-s) * (Target.rhoDet X₀ κ x : ℂ)) := by
  classical
  set S := (Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀).filter fun n : ℕ => x ≤ (n : ℝ) with hS
  have hmem : ∀ d : ℕ, d ∈ S ↔ d ∈ X₀.smoothNumbers ∧ x ∈ Icc ((d : ℝ) / (1 + κ)) d := by
    intro d
    rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo, Set.mem_Icc,
      Nat.le_floor_iff (by positivity), div_le_iff₀ (by linarith)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by linarith, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
  have hramp : ∀ d, ramp X₀ κ s d x = if d ∈ S then (x : ℂ) ^ (-s - 1) / κ else 0 := by
    intro d
    unfold ramp
    by_cases hd : d ∈ X₀.smoothNumbers
    · by_cases hx' : x ∈ Icc ((d : ℝ) / (1 + κ)) d
      · rw [if_pos hd, Set.indicator_of_mem hx', if_pos ((hmem d).mpr ⟨hd, hx'⟩)]
      · rw [if_pos hd, Set.indicator_of_notMem hx', if_neg (fun h => hx' ((hmem d).mp h).2)]
    · rw [if_neg hd, if_neg (fun h => hd ((hmem d).mp h).1)]
  have hsum := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := S)
    (f := fun d => ramp X₀ κ s d x) (fun d hd => by simp only [hramp, if_neg hd])
  have hval : ∑ d ∈ S, ramp X₀ κ s d x = (S.card : ℂ) * ((x : ℂ) ^ (-s - 1) / κ) := by
    rw [Finset.sum_congr rfl (fun d hd => by rw [hramp, if_pos hd]), Finset.sum_const,
      nsmul_eq_mul]
  convert hsum using 1
  rw [hval]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hcp : (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) / x := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  have hcard : Target.rigidCount X₀ x ((1 + κ) * x) = S.card := by
    unfold Target.rigidCount; rw [hS]
  unfold Target.rhoDet
  rw [hcp, hcard]
  push_cast
  field_simp

lemma continuousOn_cpow_div (κ : ℝ) (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-s - 1) / κ) (Icc a b) := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha hy.1))

lemma ramp_eq_of_smooth (X₀ : ℕ) (κ : ℝ) (s : ℂ) {d : ℕ} (hd : d ∈ X₀.smoothNumbers) :
    ramp X₀ κ s d =
      Set.indicator (Icc ((d : ℝ) / (1 + κ)) d) (fun y : ℝ => (y : ℂ) ^ (-s - 1) / κ) := by
  funext x; unfold ramp; rw [if_pos hd]

lemma ramp_eq_of_not_smooth (X₀ : ℕ) (κ : ℝ) (s : ℂ) {d : ℕ} (hd : d ∉ X₀.smoothNumbers) :
    ramp X₀ κ s d = 0 := by
  funext x; unfold ramp; rw [if_neg hd]; rfl

lemma rampStart_pos {X₀ : ℕ} {κ : ℝ} (hκ : 0 < κ) {d : ℕ} (hd : d ∈ X₀.smoothNumbers) :
    0 < (d : ℝ) / (1 + κ) := by
  have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hd)
  positivity

lemma integrable_ramp (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) (s : ℂ) (d : ℕ) :
    Integrable (ramp X₀ κ s d) (volume.restrict (Ioi (X₀ : ℝ))) := by
  by_cases hd : d ∈ X₀.smoothNumbers
  · rw [ramp_eq_of_smooth X₀ κ s hd]
    exact ((integrable_indicator_iff measurableSet_Icc).2
      (continuousOn_cpow_div κ s (rampStart_pos hκ hd)).integrableOn_Icc).integrableOn
  · rw [ramp_eq_of_not_smooth X₀ κ s hd]
    exact integrable_zero _ _ _

lemma integral_norm_ramp_le (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re) (d : ℕ) :
    ∫ x in Ioi (X₀ : ℝ), ‖ramp X₀ κ s d x‖ ≤
      (if d ∈ X₀.smoothNumbers then (1 + κ) ^ s.re * (d : ℝ) ^ (-s.re) else 0) := by
  by_cases hd : d ∈ X₀.smoothNumbers
  · rw [if_pos hd, ramp_eq_of_smooth X₀ κ s hd]
    set a := (d : ℝ) / (1 + κ) with ha_def
    have ha := rampStart_pos hκ hd
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hd)
    have hda : (d : ℝ) - a = κ * a := by rw [ha_def]; field_simp; ring
    set C := a ^ (-s.re - 1) / κ with hC
    have hbound : ∀ y ∈ Ioi (X₀ : ℝ) ∩ Icc a d, ‖‖(y : ℂ) ^ (-s - 1) / κ‖‖ ≤ C := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.2.1
      rw [norm_norm, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hκ, hC]
      apply div_le_div_of_nonneg_right _ hκ.le
      have : (-s - 1).re = -s.re - 1 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos ha hy.2.1 (by linarith)
    have hmeas : volume.real (Ioi (X₀ : ℝ) ∩ Icc a d) ≤ d - a := by
      calc volume.real (Ioi (X₀ : ℝ) ∩ Icc a d) ≤ volume.real (Icc a d) :=
            measureReal_mono Set.inter_subset_right (by simp)
        _ = d - a := by rw [Real.volume_real_Icc]; exact max_eq_left (by rw [hda]; positivity)
    have hfin : volume (Ioi (X₀ : ℝ) ∩ Icc a d) < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp)
    have e1 : ∫ x in Ioi (X₀ : ℝ), ‖(Icc a d).indicator
        (fun y : ℝ => (y : ℂ) ^ (-s - 1) / κ) x‖ =
        ∫ x in Ioi (X₀ : ℝ) ∩ Icc a d, ‖(x : ℂ) ^ (-s - 1) / κ‖ := by
      rw [← setIntegral_indicator measurableSet_Icc]
      congr 1; funext x
      rw [norm_indicator_eq_indicator_norm]
    rw [e1]
    have h2 := norm_setIntegral_le_of_norm_le_const hfin hbound
    have hC0 : 0 ≤ C := by positivity
    calc ∫ x in Ioi (X₀ : ℝ) ∩ Icc a d, ‖(x : ℂ) ^ (-s - 1) / κ‖
        ≤ ‖∫ x in Ioi (X₀ : ℝ) ∩ Icc a d, ‖(x : ℂ) ^ (-s - 1) / κ‖‖ :=
          (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
      _ ≤ C * volume.real (Ioi (X₀ : ℝ) ∩ Icc a d) := h2
      _ ≤ C * (d - a) := mul_le_mul_of_nonneg_left hmeas hC0
      _ = a ^ (-s.re) := by
          have ha' : 0 < a := ha
          have e : a ^ (-s.re - 1) = a ^ (-s.re) / a := by
            rw [Real.rpow_sub ha', Real.rpow_one]
          rw [hda, hC, e]; field_simp
      _ = (1 + κ) ^ s.re * (d : ℝ) ^ (-s.re) := by
          rw [ha_def, Real.div_rpow hd0.le (by linarith), Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + κ),
            div_eq_mul_inv, inv_inv, mul_comm]
  · rw [if_neg hd, ramp_eq_of_not_smooth X₀ κ s hd]
    simp

lemma summable_integral_norm_ramp (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re) :
    Summable (fun d => ∫ x in Ioi (X₀ : ℝ), ‖ramp X₀ κ s d x‖) := by
  classical
  have hs := (Rankin.hasSum_smooth_rpow X₀ hσ).1
  have hs' : Summable ((X₀.smoothNumbers : Set ℕ).indicator fun d : ℕ => (d : ℝ) ^ (-s.re)) :=
    (summable_subtype_iff_indicator).mp hs
  refine Summable.of_nonneg_of_le (fun d => integral_nonneg fun x => norm_nonneg _)
    (fun d => integral_norm_ramp_le X₀ hκ hσ d) ?_
  convert hs'.mul_left ((1 + κ) ^ s.re) using 1
  funext d
  by_cases hd : d ∈ X₀.smoothNumbers
  · rw [if_pos hd, Set.indicator_of_mem hd]
  · rw [if_neg hd, Set.indicator_of_notMem hd, mul_zero]

lemma mem_boundarySet {X₀ : ℕ} {κ : ℝ} (hκ : 0 < κ) {d : ℕ} :
    d ∈ boundarySet X₀ κ ↔ d ∈ X₀.smoothNumbers ∧ X₀ ≤ d ∧ (d : ℝ) < (1 + κ) * X₀ := by
  unfold boundarySet
  rw [Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, h4⟩; exact ⟨h2, h3, h4⟩
  · rintro ⟨h2, h3, h4⟩
    refine ⟨⟨?_, h2⟩, h3, h4⟩
    rw [Nat.le_floor_iff (by positivity)]; exact h4.le

/-- `∫_{lo}^{d} x^{-s-1}/κ dx = (lo^{-s} - d^{-s})/(sκ)`. -/
lemma integral_Ioc_cpow_div {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re) {lo d : ℝ}
    (hlo : 0 < lo) (hd : lo ≤ d) :
    ∫ x in Ioc lo d, (x : ℂ) ^ (-s - 1) / κ =
      (((lo : ℂ)) ^ (-s) - ((d : ℂ)) ^ (-s)) / (s * κ) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [← intervalIntegral.integral_of_le hd, intervalIntegral.integral_div]
  have h0 : (0 : ℝ) ∉ Set.uIcc lo d := by
    rw [Set.uIcc_of_le hd]; intro h; linarith [h.1]
  rw [integral_cpow (Or.inr ⟨by intro h; apply hs0; linear_combination -h, h0⟩)]
  rw [show -s - 1 + 1 = -s by ring]
  field_simp
  ring

/-- `W(s) d^{-s} = ((d/(1+κ))^{-s} - d^{-s})/(sκ)`. -/
lemma Wfac_mul_cpow {κ : ℝ} (hκ : 0 < κ) (s : ℂ) {d : ℝ} (hd : 0 < d) :
    Wfac κ s * ((d : ℂ)) ^ (-s) =
      ((((d / (1 + κ) : ℝ)) : ℂ) ^ (-s) - ((d : ℂ)) ^ (-s)) / (s * κ) := by
  have h1 : ((((d / (1 + κ) : ℝ)) : ℂ) ^ (-s)) = ((d : ℂ)) ^ (-s) * (((1 + κ : ℝ) : ℂ)) ^ s := by
    rw [div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hd.le (inv_nonneg.mpr (by linarith)), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by linarith)]; exact Real.pi_pos.ne),
      Complex.cpow_neg (((1 + κ : ℝ)) : ℂ) s, inv_inv]
  rw [h1]; unfold Wfac; ring

lemma integral_ramp (X₀ : ℕ) (hX : 1 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re)
    (d : ℕ) : ∫ x in Ioi (X₀ : ℝ), ramp X₀ κ s d x = rampVal X₀ κ s d := by
  classical
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  by_cases hd : d ∈ X₀.smoothNumbers
  swap
  · rw [ramp_eq_of_not_smooth X₀ κ s hd]
    have : d ∉ boundarySet X₀ κ := fun h => hd ((mem_boundarySet hκ).mp h).1
    simp [rampVal, hd, this]
  rw [ramp_eq_of_smooth X₀ κ s hd, setIntegral_indicator measurableSet_Icc]
  set a := (d : ℝ) / (1 + κ) with ha_def
  have ha := rampStart_pos hκ hd
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hd)
  have had : a ≤ d := by
    rw [ha_def, div_le_iff₀ (by linarith)]; nlinarith
  have hiff : ∀ {c : ℝ}, a ≤ c ↔ (d : ℝ) ≤ (1 + κ) * c := by
    intro c; rw [ha_def, div_le_iff₀ (by linarith), mul_comm]
  rcases lt_or_ge d X₀ with hdX | hdX
  · -- `d < X₀`: the ramp lies below `X₀`
    have hdX' : (d : ℝ) < X₀ := by exact_mod_cast hdX
    have hempty : Ioi (X₀ : ℝ) ∩ Icc a d = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, -, h3⟩; linarith
    have : d ∉ boundarySet X₀ κ := fun h => by
      have := ((mem_boundarySet hκ).mp h).2.1; omega
    rw [hempty, Measure.restrict_empty, integral_zero_measure]
    simp [rampVal, this, show ¬ X₀ ≤ d by omega]
  have hdX' : (X₀ : ℝ) ≤ d := by exact_mod_cast hdX
  have hW := Wfac_mul_cpow hκ s hd0
  rcases le_or_gt a X₀ with haX | haX
  · -- the ramp is truncated at `X₀`
    have hset : Ioi (X₀ : ℝ) ∩ Icc a d = Ioc (X₀ : ℝ) d := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
    rw [hset, integral_Ioc_cpow_div hκ hσ (by linarith) hdX']
    unfold rampVal
    rw [if_pos ⟨hd, hdX⟩]
    by_cases hb : d ∈ boundarySet X₀ κ
    · rw [if_pos hb, hW]; ring
    · rw [if_neg hb, hW]
      have hdeq : (d : ℝ) = (1 + κ) * X₀ := by
        have h1 : (d : ℝ) ≤ (1 + κ) * X₀ := hiff.mp haX
        by_contra hne
        exact hb ((mem_boundarySet hκ).mpr ⟨hd, hdX, lt_of_le_of_ne h1 hne⟩)
      have haeq : (d : ℝ) / (1 + κ) = X₀ := by rw [hdeq]; field_simp
      rw [haeq]; ring
  · -- the full ramp lies above `X₀`
    have hset : Ioi (X₀ : ℝ) ∩ Icc a d = Icc a d := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc]
      constructor
      · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [hset, integral_Icc_eq_integral_Ioc, integral_Ioc_cpow_div hκ hσ ha had]
    have hb : d ∉ boundarySet X₀ κ := by
      intro h
      have h1 := ((mem_boundarySet hκ).mp h).2.2
      have h2 : (1 + κ) * (X₀ : ℝ) < d := by
        by_contra hc; push_neg at hc; exact absurd (hiff.mpr hc) (not_le.mpr haX)
      linarith
    unfold rampVal
    rw [if_pos ⟨hd, hdX⟩, if_neg hb, hW]
    ring

lemma hasSum_rampVal (X₀ : ℕ) {κ : ℝ} {s : ℂ} (hσ : 0 < s.re) :
    HasSum (rampVal X₀ κ s) (Wfac κ s * (Zinf X₀ s - headSum X₀ s) - boundary X₀ κ s) := by
  classical
  have hA := (hasSum_smooth_ge X₀ hσ).mul_left (Wfac κ s)
  have hB := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := boundarySet X₀ κ) (f := fun d : ℕ => if d ∈ boundarySet X₀ κ then
      ((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ) else 0)
    (fun d hd => if_neg hd)
  have hBv : (∑ d ∈ boundarySet X₀ κ, (if d ∈ boundarySet X₀ κ then
      ((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ) else 0)) =
      boundary X₀ κ s := by
    unfold boundary
    exact Finset.sum_congr rfl fun d hd => if_pos hd
  rw [hBv] at hB
  convert hA.sub hB using 1
  funext d
  unfold rampVal
  rw [mul_ite, mul_zero]

lemma integrable_tsum_ramp (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 < s.re) :
    Integrable (fun x => ∑' d, ramp X₀ κ s d x) (volume.restrict (Ioi (X₀ : ℝ))) := by
  set μ := volume.restrict (Ioi (X₀ : ℝ)) with hμ
  have hint := integrable_ramp X₀ hκ s
  have hmeas : AEStronglyMeasurable (fun x => ∑' d, ramp X₀ κ s d x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun n x => ∑ d ∈ Finset.range n, ramp X₀ κ s d x)
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun d _ => (hint d).1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg X₀) hx
    have h := hasSum_ramp X₀ hκ s hx0
    rw [h.tsum_eq]
    exact h.tendsto_sum_nat
  refine ⟨hmeas, ?_⟩
  have hsum := summable_integral_norm_ramp X₀ hκ hσ
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖∑' d, ramp X₀ κ s d x‖ₑ ∂μ ≤ ∫⁻ x, ∑' d, ‖ramp X₀ κ s d x‖ₑ ∂μ :=
        lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' d, ∫⁻ x, ‖ramp X₀ κ s d x‖ₑ ∂μ :=
        lintegral_tsum fun d => (hint d).1.enorm
    _ = ∑' d, ENNReal.ofReal (∫ x, ‖ramp X₀ κ s d x‖ ∂μ) := by
        congr 1; funext d; exact (ofReal_integral_norm_eq_lintegral_enorm (hint d)).symm
    _ = ENNReal.ofReal (∑' d, ∫ x, ‖ramp X₀ κ s d x‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun d => integral_nonneg fun x => norm_nonneg _)
          hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **Identity (15)**: for `σ > 1` the paper's `Z_B` equals `ZBcont`, i.e.
`Z_B = Z_∞ - W S_{≥X₀} + X₀^{1-s}/(s-1) + (boundary terms)`. -/
theorem ZBpaper_eq_ZBcont (X₀ : ℕ) (hX : 1 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) {s : ℂ}
    (hσ : 1 < s.re) : ZBpaper X₀ κ s = ZBcont X₀ κ s := by
  have hσ0 : 0 < s.re := by linarith
  have hX' : (0 : ℝ) < X₀ := by exact_mod_cast hX
  have heq : EqOn (fun x : ℝ => (x : ℂ) ^ (-s) * (Target.rhoDet X₀ κ x : ℂ))
      (fun x => ∑' d, ramp X₀ κ s d x) (Ioi (X₀ : ℝ)) := fun x hx =>
    (hasSum_ramp X₀ hκ s (lt_trans hX' hx)).tsum_eq.symm
  have hintρ : Integrable (fun x : ℝ => (x : ℂ) ^ (-s) * (Target.rhoDet X₀ κ x : ℂ))
      (volume.restrict (Ioi (X₀ : ℝ))) := by
    refine (integrable_tsum_ramp X₀ hκ hσ0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (heq hx).symm
  have hintc : Integrable (fun x : ℝ => (x : ℂ) ^ (-s)) (volume.restrict (Ioi (X₀ : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hX'
  have hIρ : ∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s) * (Target.rhoDet X₀ κ x : ℂ) =
      Wfac κ s * (Zinf X₀ s - headSum X₀ s) - boundary X₀ κ s := by
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      ← integral_tsum_of_summable_integral_norm (integrable_ramp X₀ hκ s)
        (summable_integral_norm_ramp X₀ hκ hσ0)]
    simp_rw [integral_ramp X₀ hX hκ hσ0]
    exact (hasSum_rampVal X₀ hσ0).tsum_eq
  have hIc : ∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s) = ((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) hX']
    have : (1 : ℂ) - s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2 : s - 1 ≠ 0 := by intro h; apply this; linear_combination -h
    rw [show -s + 1 = 1 - s by ring]
    field_simp
    ring
  have hsplit : ∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s) * (1 - (Target.rhoDet X₀ κ x : ℂ)) =
      (∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s)) -
        ∫ x in Ioi (X₀ : ℝ), (x : ℂ) ^ (-s) * (Target.rhoDet X₀ κ x : ℂ) := by
    rw [← integral_sub hintc hintρ]
    congr 1; funext x; ring
  unfold ZBpaper ZBcont
  rw [(hasSum_smooth_ge X₀ hσ0).tsum_eq, hsplit, hIρ, hIc]
  ring

end BaseFactor

end
