module

public import RequestProject.Beurling.Decomp.Mellin
public import RequestProject.Beurling.AbsorbedPart
public import RequestProject.Beurling.AbsorbedTargetError

/-!
# The transform of the absorbed part of the target

The absorbed part of the target (6) is `E_A(x) = #(A ∩ [X₀, x]) - ∫_{X₀}^x ρ̄_A` for `x ≥ X₀`
(and `0` below). When the cap is inactive (`ρ_A ≤ 0.1/log` on `[X₀, ∞)`, which is the case on
`G`), its transform is the absorbed part of (14):

  `s ∫_1^∞ E_A(x) x^{-s-1} dx = Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))`    (`mellin_absE`)

for `σ > b = θ/2`. The proof splits `E_A = ∑_a e_a` with `e_a(x) = 1[a ≤ x] - ∫_{X₀}^x 1[u_a ≤ v ≤ a]
v^{-b} dv`, computes each transform, and integrates term by term: `∫ |e_a(x)| x^{-σ-1} dx ≪ a^{b-σ-1}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Remark12 Absorbed
open scoped Classical

namespace Decomp

variable {b X₀ : ℝ} {A : Set ℕ} {u : ℕ → ℝ}

/-- The absorbed part of the target, `#(A ∩ [1,x]) - ∫_{X₀}^x ρ̄_A` from `X₀` on, `0` below. -/
noncomputable def absE (X₀ : ℝ) (cntA rhoA : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < X₀ then 0 else cntA x - ∫ v in X₀..x, rhoA v

/-- The contribution of one element `a`: `e_a(x) = 1[a ∈ A, a ≤ x] - ∫_{X₀}^x 1[u_a ≤ v ≤ a] v^{-b}`
from `X₀` on, `0` below. -/
noncomputable def absTerm (b X₀ : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  if x < X₀ then 0 else
    (if a ∈ A ∧ (a : ℝ) ≤ x then (1 : ℝ) else 0) - ∫ v in X₀..x, absorbedBump b A u a v

/-- `E_A = ∑_a e_a` when the cap is inactive. -/
lemma absE_eq_tsum (h : AbsorbedWindowHyp b X₀ A u)
    (hcap : ∀ v ≥ X₀, absorbedDensity b A u v ≤ 0.1 / Real.log v) (x : ℝ) :
    absE X₀ (countA A) (absorbedDensityCap b A u) x = ∑' a, absTerm b X₀ A u a x := by
  by_cases hx : x < X₀
  · simp [absE, absTerm, hx]
  push_neg at hx
  have hx1 : 1 ≤ x := le_trans h.X₀_ge hx
  set N := ⌊2 * x⌋₊ + 1
  have hcapI : ∫ v in X₀..x, absorbedDensityCap b A u v =
      ∑ a ∈ Finset.range N, ∫ v in X₀..x, absorbedBump b A u a v := by
    rw [← intervalIntegral.integral_finset_sum fun a _ => intervalIntegrable_absorbedBump h a hx]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hx] at hv
    simp only [absorbedDensityCap]
    rw [min_eq_left (hcap v hv.1), absorbedDensity_eq_sum h hv.1 hv.2]
  have hzero : ∀ a ∉ Finset.range N, absTerm b X₀ A u a x = 0 := by
    intro a ha
    have ha' : 2 * x < a := Nat.lt_of_floor_lt (by simpa [N, Nat.lt_succ_iff] using ha)
    have hI : ∫ v in X₀..x, absorbedBump b A u a v = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
      intro v hv
      rw [uIcc_of_le hx] at hv
      simp only [absorbedBump]
      split_ifs with hA
      · apply Set.indicator_of_notMem
        rintro ⟨h1, h2⟩
        have hU : 0 ≤ u a := by linarith [h.u_ge a hA, h.X₀_ge]
        have e1 : u a ^ b ≤ x ^ b := Real.rpow_le_rpow hU (h1.trans hv.2) h.b_pos.le
        have e2 : x ^ b ≤ x := by
          simpa using Real.rpow_le_rpow_of_exponent_le hx1 h.b_le
        linarith [h.u_eq a hA, hv.2]
      · rfl
    have hnot : ¬ (a ∈ A ∧ (a : ℝ) ≤ x) := fun hc => by linarith [hc.2]
    simp [absTerm, not_lt.mpr hx, hnot, hI]
  rw [tsum_eq_sum hzero]
  simp only [absE, absTerm, if_neg (not_lt.mpr hx)]
  rw [Finset.sum_sub_distrib, countA_eq_sum h hx, hcapI]

lemma absTerm_of_notMem {a : ℕ} (hA : a ∉ A) (x : ℝ) : absTerm b X₀ A u a x = 0 := by
  have hb : absorbedBump b A u a = fun _ => 0 := by ext v; simp [absorbedBump, hA]
  simp [absTerm, hb, hA]

lemma absTerm_of_le (h : AbsorbedWindowHyp b X₀ A u) (a : ℕ) {x : ℝ} (hx : x ≤ X₀) :
    absTerm b X₀ A u a x = 0 := by
  by_cases hA : a ∈ A
  · rcases hx.lt_or_eq with hx | hx
    · simp [absTerm, hx]
    · have hXa : X₀ < a := lt_of_le_of_lt (h.u_ge a hA) (u_lt h hA)
      simp [absTerm, hx, hXa]
  · exact absTerm_of_notMem hA x

lemma bump_eq_indicator {a : ℕ} (hA : a ∈ A) :
    absorbedBump b A u a = (Icc (u a) (a : ℝ)).indicator (fun w => w ^ (-b)) := by
  ext v; simp [absorbedBump, hA]

/-- `∫_{X₀}^∞ 1[u_a ≤ v ≤ a] v^{-b} v^{-s} dv = a^{-s} w_a(s)`. -/
lemma integral_bump_cpow (h : AbsorbedWindowHyp b X₀ A u) {a : ℕ} (hA : a ∈ A) (s : ℂ) :
    ∫ v in Ioi X₀, (absorbedBump b A u a v : ℂ) * (v : ℂ) ^ (-s) =
      ((a : ℝ) : ℂ) ^ (-s) * Weights.weight b a (u a) s := by
  have hUX := h.u_ge a hA
  have hUa := u_lt h hA
  have hU : 0 < u a := by linarith [h.X₀_ge]
  have ha : (0 : ℝ) < a := by linarith
  have e : (fun v : ℝ => (absorbedBump b A u a v : ℂ) * (v : ℂ) ^ (-s)) =
      (Icc (u a) (a : ℝ)).indicator (fun v : ℝ => ((v ^ (-b) : ℝ) : ℂ) * (v : ℂ) ^ (-s)) := by
    funext v
    rw [bump_eq_indicator hA]
    by_cases hv : v ∈ Icc (u a) (a : ℝ)
    · simp [indicator_of_mem hv]
    · simp [indicator_of_notMem hv]
  have hset : ∫ v in Ioi X₀ ∩ Icc (u a) (a : ℝ), ((v ^ (-b) : ℝ) : ℂ) * (v : ℂ) ^ (-s) =
      ∫ v in Ioc (u a) (a : ℝ), ((v ^ (-b) : ℝ) : ℂ) * (v : ℂ) ^ (-s) := by
    rcases hUX.lt_or_eq with hlt | heq
    · rw [inter_eq_right.mpr (Icc_subset_Ioi_iff hUa.le |>.mpr hlt), integral_Icc_eq_integral_Ioc]
    · have hs : Ioi X₀ ∩ Icc (u a) (a : ℝ) = Ioc (u a) (a : ℝ) := by
        rw [heq]
        ext v; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, h1.le, h3⟩
      rw [hs]
  rw [e, setIntegral_indicator measurableSet_Icc, hset]
  unfold Weights.weight
  rw [intervalIntegral.integral_of_le hUa.le, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  have hv0 : 0 < v := lt_trans hU hv.1
  have key : ((a : ℝ) : ℂ) ^ (-s) * ((a / v : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) := by
    rw [div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hv0.le), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hv0.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, Complex.cpow_neg, ← mul_assoc,
      inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast ha.ne'))),
      one_mul]
  rw [← key]
  ring

/-- The transform of one element: `s ∫_1^∞ e_a(x) x^{-s-1} dx = a^{-s}(1 - w_a(s))` (and `0` for
`a ∉ A`). -/
lemma mellin_absTerm (h : AbsorbedWindowHyp b X₀ A u) (a : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (absTerm b X₀ A u a) s = absorbedTerm b A u s a := by
  by_cases hA : a ∉ A
  · have hz : (fun x : ℝ => (absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun _ => 0 := by
      funext x; simp [absTerm_of_notMem hA x]
    refine ⟨by rw [hz]; exact integrableOn_zero, ?_⟩
    unfold tailMellin absorbedTerm
    rw [hz, if_neg hA]; simp
  push_neg at hA
  have hX1 := h.X₀_ge
  have hX0 : 0 < X₀ := by linarith
  have hUX := h.u_ge a hA
  have hUa := u_lt h hA
  have hU : 0 < u a := by linarith
  have haX : X₀ < a := lt_of_le_of_lt hUX hUa
  -- integrability of the bump against `v^{-σ}`
  have hg : IntegrableOn (fun v => absorbedBump b A u a v * v ^ (-s.re)) (Ioi X₀) := by
    have e : (fun v => absorbedBump b A u a v * v ^ (-s.re)) =
        (Icc (u a) (a : ℝ)).indicator (fun v => v ^ (-b) * v ^ (-s.re)) := by
      rw [bump_eq_indicator hA]; ext v; rw [Set.indicator_mul_left]
    rw [e]
    refine Integrable.integrableOn ((integrable_indicator_iff measurableSet_Icc).mpr ?_)
    refine ContinuousOn.integrableOn_Icc fun v hv => ?_
    have hv0 : 0 < v := lt_of_lt_of_le hU hv.1
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hv0.ne')).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl hv0.ne'))).continuousWithinAt
  obtain ⟨hPint, hPval⟩ := mellin_primitive hX0 hs hg
  set F : ℝ → ℂ := fun x => (if (a : ℝ) ≤ x then (x : ℂ) ^ (-s - 1) else 0) -
    ((∫ v in X₀..x, absorbedBump b A u a v : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) with hF
  have hFint : IntegrableOn F (Ioi X₀) := (integrableOn_Ioi_ite_cpow hX0 hs).sub hPint
  have heq : ∀ x ∈ Ioi (1 : ℝ), (absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (Ioi X₀).indicator F x := by
    intro x _
    by_cases hx : x ≤ X₀
    · rw [absTerm_of_le h a hx, indicator_of_notMem (show x ∉ Ioi X₀ from not_lt.mpr hx)]; simp
    · push_neg at hx
      rw [indicator_of_mem (show x ∈ Ioi X₀ from hx)]
      simp only [absTerm, if_neg (not_lt.mpr hx.le), hF]
      by_cases hax : (a : ℝ) ≤ x
      · simp [hax, hA]; ring
      · simp [hax]
  have hint : IntegrableOn (fun x : ℝ => (absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := by
    refine IntegrableOn.congr_fun ?_ (fun x hx => (heq x hx).symm) measurableSet_Ioi
    exact ((integrable_indicator_iff measurableSet_Ioi).mpr hFint).integrableOn
  refine ⟨hint, ?_⟩
  unfold tailMellin absorbedTerm
  rw [if_pos hA, setIntegral_congr_fun measurableSet_Ioi heq,
    setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hX1,
    integral_sub (integrableOn_Ioi_ite_cpow hX0 hs) hPint, mul_sub, hPval,
    integral_Ioi_ite_cpow hX0 haX hs, integral_bump_cpow h hA]
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  field_simp

/-- The integral of the norm of one term: `∫_1^∞ |e_a(x)| x^{-σ-1} dx ≤ K a^{b-σ-1}` with
`K = 2^{σ+1-b} (1 + 1/σ)`. -/
lemma lintegral_absTerm_le (h : AbsorbedWindowHyp b X₀ A u) (a : ℕ) {s : ℂ} (hs : b < s.re) :
    ∫⁻ x in Ioi (1 : ℝ), ‖(absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)‖ₑ ≤
      ENNReal.ofReal (2 ^ (s.re + 1 - b) * (1 + 1 / s.re) * (a : ℝ) ^ (b - s.re - 1)) := by
  by_cases hA : a ∉ A
  · have hz : ∀ x, ‖(absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)‖ₑ = 0 := fun x => by
      simp [absTerm_of_notMem hA x]
    simp only [hz, lintegral_zero, zero_le]
  push_neg at hA
  set σ := s.re with hσdef
  have hb := h.b_pos
  have hb1 := h.b_le
  have hσ : 0 < σ := lt_trans hb hs
  have hX1 := h.X₀_ge
  have hUX := h.u_ge a hA
  have hUa := u_lt h hA
  set U := u a with hUdef
  have hU : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have ha : (0 : ℝ) < a := by linarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have hdiff : (a : ℝ) - U = U ^ b := by linarith [h.u_eq a hA]
  obtain ⟨hM1, hM2⟩ := mass_bounds h hA
  set M := ∫ v in U..(a : ℝ), v ^ (-b) with hM
  set ε := 1 - U ^ b * (a : ℝ) ^ (-b) with hε
  have hε0 : 0 ≤ ε := by linarith
  have hM0 : 0 ≤ M := by
    refine intervalIntegral.integral_nonneg hUa.le fun v hv => Real.rpow_nonneg ?_ _
    linarith [hv.1]
  -- the pointwise bound
  set G : ℝ → ℝ := fun x => (Ico U (a : ℝ)).indicator (fun _ => U ^ (-σ - 1)) x +
    (if (a : ℝ) ≤ x then ε else 0) * x ^ (-σ - 1) with hG
  have hpt : ∀ x ∈ Ioi (1 : ℝ), ‖(absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ G x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hxs : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have hG1 : 0 ≤ (Ico U (a : ℝ)).indicator (fun _ => U ^ (-σ - 1)) x :=
      Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg hU.le _) _
    have hG2 : 0 ≤ (if (a : ℝ) ≤ x then ε else 0) * x ^ (-σ - 1) :=
      mul_nonneg (by split_ifs <;> linarith) hxs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -σ - 1 := by simp [hσdef]
    rw [hre]
    by_cases hxX : x ≤ X₀
    · rw [absTerm_of_le h a hxX]; simp only [abs_zero, zero_mul]; exact add_nonneg hG1 hG2
    push_neg at hxX
    have hval : absTerm b X₀ A u a x = (if (a : ℝ) ≤ x then (1 : ℝ) else 0) -
        ∫ v in X₀..x, absorbedBump b A u a v := by
      simp [absTerm, not_lt.mpr hxX.le, hA]
    rw [hval, bump_eq_indicator hA]
    by_cases hxU : x < U
    · have hI : ∫ v in X₀..x, (Icc U (a : ℝ)).indicator (fun w => w ^ (-b)) v = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_,
          intervalIntegral.integral_zero]
        intro v hv
        rw [uIcc_of_le hxX.le] at hv
        exact Set.indicator_of_notMem (fun hc => by linarith [hc.1, hv.2]) _
      have hax : ¬ (a : ℝ) ≤ x := by linarith
      rw [hI, if_neg hax]; simp only [sub_zero, abs_zero, zero_mul]; exact add_nonneg hG1 hG2
    push_neg at hxU
    rw [integral_indicator_Icc hUX hUa.le hxU]
    by_cases hax : (a : ℝ) ≤ x
    · rw [if_pos hax, min_eq_left hax, ← hM, abs_of_nonneg (by linarith)]
      have : (Ico U (a : ℝ)).indicator (fun _ => U ^ (-σ - 1)) x = 0 :=
        Set.indicator_of_notMem (fun hc => by linarith [hc.2]) _
      simp only [hG]
      rw [this, zero_add, if_pos hax]
      exact mul_le_mul_of_nonneg_right (by linarith) hxs
    · push_neg at hax
      rw [if_neg (not_le.mpr hax), min_eq_right hax.le, zero_sub, abs_neg]
      have hI0 : 0 ≤ ∫ v in U..x, v ^ (-b) :=
        intervalIntegral.integral_nonneg hxU fun v hv => Real.rpow_nonneg (by linarith [hv.1]) _
      have hI1 : ∫ v in U..x, v ^ (-b) ≤ M := by
        rw [hM]
        refine intervalIntegral.integral_mono_interval le_rfl hxU hax.le ?_ ?_
        · refine (ae_restrict_mem measurableSet_Ioc).mono fun v hv => ?_
          exact Real.rpow_nonneg (by linarith [hv.1]) _
        · refine ContinuousOn.intervalIntegrable fun v hv => ?_
          rw [uIcc_of_le hUa.le] at hv
          exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
      rw [abs_of_nonneg hI0]
      have hind : (Ico U (a : ℝ)).indicator (fun _ => U ^ (-σ - 1)) x = U ^ (-σ - 1) :=
        Set.indicator_of_mem (show x ∈ Ico U (a : ℝ) from ⟨hxU, hax⟩) _
      have h2 : (if (a : ℝ) ≤ x then ε else 0) * x ^ (-σ - 1) = 0 := by
        rw [if_neg (not_le.mpr hax), zero_mul]
      simp only [hG]
      rw [hind, h2, add_zero]
      calc (∫ v in U..x, v ^ (-b)) * x ^ (-σ - 1) ≤ 1 * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hxs
        _ ≤ U ^ (-σ - 1) := by
            rw [one_mul]; exact Real.rpow_le_rpow_of_nonpos hU hxU (by linarith)
  -- the integral of the bound
  have hlin : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (G x) ≤
      ENNReal.ofReal (U ^ (-σ - 1) * ((a : ℝ) - U) + ε * (a : ℝ) ^ (-σ) / σ) := by
    have e : ∀ x, ENNReal.ofReal (G x) =
        (Ico U (a : ℝ)).indicator (fun _ => ENNReal.ofReal (U ^ (-σ - 1))) x +
          ENNReal.ofReal ((if (a : ℝ) ≤ x then ε else 0) * x ^ (-σ - 1)) := by
      intro x
      rw [hG]
      simp only
      rw [ENNReal.ofReal_add (Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg hU.le _) _)]
      · congr 1
        by_cases hx : x ∈ Ico U (a : ℝ)
        · simp [indicator_of_mem hx]
        · simp [indicator_of_notMem hx]
      · rcases le_or_gt x 0 with hx | hx
        · split_ifs with h1
          · linarith
          · simp
        · exact mul_nonneg (by split_ifs <;> linarith) (Real.rpow_nonneg hx.le _)
    simp_rw [e]
    rw [lintegral_add_left ((measurable_const.indicator measurableSet_Ico)),
      lintegral_indicator_const measurableSet_Ico,
      AbelMellin.lintegral_ite_rpow ha1 hε0 hσ,
      ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hU.le _) (by linarith))
        (div_nonneg (mul_nonneg hε0 (Real.rpow_nonneg ha.le _)) hσ.le),
      ENNReal.ofReal_mul (Real.rpow_nonneg hU.le _)]
    gcongr
    calc (volume.restrict (Ioi (1 : ℝ))) (Ico U (a : ℝ)) ≤ volume (Ico U (a : ℝ)) :=
          Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal ((a : ℝ) - U) := Real.volume_Ico
  -- the numerical bound
  have hnum : U ^ (-σ - 1) * ((a : ℝ) - U) + ε * (a : ℝ) ^ (-σ) / σ ≤
      2 ^ (σ + 1 - b) * (1 + 1 / σ) * (a : ℝ) ^ (b - σ - 1) := by
    have hUb : U ^ b ≤ U := by
      simpa using Real.rpow_le_rpow_of_exponent_le hU1 hb1
    have ha2 : (a : ℝ) / 2 ≤ U := by linarith
    have hε' : ε ≤ U ^ b / a := by
      have hr0 : 0 < U / a := div_pos hU ha
      have hr1 : U / a ≤ 1 := (div_le_one ha).mpr hUa.le
      have h1 : U / a ≤ (U / a) ^ b := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hb1
      have h2 : (U / a) ^ b = U ^ b * (a : ℝ) ^ (-b) := by
        rw [Real.div_rpow hU.le ha.le, Real.rpow_neg ha.le, div_eq_mul_inv]
      rw [hε, ← h2]
      have h3 : U ^ b / a = 1 - U / a := by
        rw [← hdiff]; field_simp
      rw [h3]; linarith
    have hT1 : U ^ (-σ - 1) * ((a : ℝ) - U) = U ^ (b - σ - 1) := by
      rw [hdiff, ← Real.rpow_add hU]; ring_nf
    have hT2 : ε * (a : ℝ) ^ (-σ) / σ ≤ U ^ (b - σ - 1) / σ := by
      have h1 : ε * (a : ℝ) ^ (-σ) ≤ U ^ b * (a : ℝ) ^ (-σ - 1) := by
        calc ε * (a : ℝ) ^ (-σ) ≤ U ^ b / a * (a : ℝ) ^ (-σ) :=
              mul_le_mul_of_nonneg_right hε' (Real.rpow_nonneg ha.le _)
          _ = U ^ b * (a : ℝ) ^ (-σ - 1) := by
              rw [Real.rpow_sub ha, Real.rpow_one]; ring
      have h2 : U ^ b * (a : ℝ) ^ (-σ - 1) ≤ U ^ b * U ^ (-σ - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hU hUa.le (by linarith))
          (Real.rpow_nonneg hU.le _)
      have h3 : U ^ b * U ^ (-σ - 1) = U ^ (b - σ - 1) := by
        rw [← Real.rpow_add hU]; ring_nf
      exact div_le_div_of_nonneg_right (h1.trans (h2.trans h3.le)) hσ.le
    have hT3 : U ^ (b - σ - 1) ≤ 2 ^ (σ + 1 - b) * (a : ℝ) ^ (b - σ - 1) := by
      have h1 : U ^ (b - σ - 1) ≤ ((a : ℝ) / 2) ^ (b - σ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) ha2 (by linarith)
      have h2 : ((a : ℝ) / 2) ^ (b - σ - 1) = 2 ^ (σ + 1 - b) * (a : ℝ) ^ (b - σ - 1) := by
        rw [Real.div_rpow ha.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
        ring_nf
      linarith
    have hpos : 0 ≤ U ^ (b - σ - 1) := Real.rpow_nonneg hU.le _
    calc U ^ (-σ - 1) * ((a : ℝ) - U) + ε * (a : ℝ) ^ (-σ) / σ
        ≤ U ^ (b - σ - 1) + U ^ (b - σ - 1) / σ := by rw [hT1]; linarith
      _ = (1 + 1 / σ) * U ^ (b - σ - 1) := by ring
      _ ≤ (1 + 1 / σ) * (2 ^ (σ + 1 - b) * (a : ℝ) ^ (b - σ - 1)) := by
          gcongr
      _ = 2 ^ (σ + 1 - b) * (1 + 1 / σ) * (a : ℝ) ^ (b - σ - 1) := by ring
  calc ∫⁻ x in Ioi (1 : ℝ), ‖(absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1)‖ₑ
      ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (G x) := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hpt x hx)
    _ ≤ _ := hlin
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnum

/-- **The absorbed part of the decomposition (14)**: when the cap is inactive, for `σ > b`,
`s ∫_1^∞ E_A(x) x^{-s-1} dx = Ê_A(s)` (with the integrand integrable). -/
theorem mellin_absE (h : AbsorbedWindowHyp b X₀ A u)
    (hcap : ∀ v ≥ X₀, absorbedDensity b A u v ≤ 0.1 / Real.log v) {s : ℂ} (hs : b < s.re) :
    IntegrableOn (fun x : ℝ => (absE X₀ (countA A) (absorbedDensityCap b A u) x : ℂ) *
        (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (absE X₀ (countA A) (absorbedDensityCap b A u)) s = absorbedHat b A u s := by
  have hs0 : 0 < s.re := lt_trans h.b_pos hs
  set f : ℕ → ℝ → ℂ := fun a x => (absTerm b X₀ A u a x : ℂ) * (x : ℂ) ^ (-s - 1) with hf
  have hfm : ∀ a, AEStronglyMeasurable (f a) (volume.restrict (Ioi 1)) := fun a =>
    (mellin_absTerm h a hs0).1.1
  have hsumm : Summable fun a : ℕ =>
      2 ^ (s.re + 1 - b) * (1 + 1 / s.re) * (a : ℝ) ^ (b - s.re - 1) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hfin : ∑' a, ∫⁻ x in Ioi (1 : ℝ), ‖f a x‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun a => lintegral_absTerm_le h a hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => ?_) hsumm]
    · exact ENNReal.ofReal_ne_top
    · have : 0 ≤ 1 / s.re := by positivity
      positivity
  have heq : (fun x : ℝ => (absE X₀ (countA A) (absorbedDensityCap b A u) x : ℂ) *
      (x : ℂ) ^ (-s - 1)) = fun x => ∑' a, f a x := by
    funext x
    simp only [hf]
    rw [absE_eq_tsum h hcap x, Complex.ofReal_tsum, tsum_mul_right]
  refine ⟨heq ▸ integrable_tsum_of_lintegral f hfm hfin, ?_⟩
  unfold tailMellin
  rw [heq, integral_tsum hfm hfin, ← tsum_mul_left]
  unfold absorbedHat
  congr 1
  funext a
  exact (mellin_absTerm h a hs0).2

end Decomp

end
