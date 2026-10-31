module

public import RequestProject.Beurling.Decomp.MellinBase
public import RequestProject.Beurling.Decomp.MellinOsc
public import RequestProject.Beurling.Decomp.MellinAbsorbed
public import RequestProject.Beurling.Zeros
public import RequestProject.Beurling.TargetError

/-!
# The decomposition (14) of the zeta function

For a Beurling system `P` and the target `T` of (6) (built from `X₀`, `κ`, the absorbed set `A`
with windows `[u_a, a]`, and the oscillation `R = ∑ R_k`), put `D := N_P - T`. Then

  `ζ_P(s) = Z_B(s) + ∑_k R̂_k(s) + D̂(s) + Ê_A(s)`,     `D̂ = D̂_{<a} + D̂_{≥a}`,

where `ζ_P` is the continuation `s/(s-1) + s ∫_1^∞ (N_P(x) - x) x^{-s-1} dx` (`zetaCont P 1`).
This is (14), proved here (`decomposition_14`) on the whole half-plane `σ > max(θ, η)`, `s ≠ 1`,
from:

* `X₀` is `X₀`-smooth (e.g. even, `≥ 4`), `κ > 0`, `0 < θ ≤ 2`;
* the windows `u_a + u_a^{θ/2} = a`, `u_a ≥ X₀` of the elements of `A`, and the cap in (6) being
  inactive (`ρ_A ≤ 0.1/log` on `[X₀, ∞)`);
* the switch-on points satisfy `x⁺_{k+1} ≥ exp(x⁺_k)`, `x⁺_0 ≥ X₀`, and the amplitudes are bounded;
* `|D(x)| ≤ K x^η` for `x ≥ X₀`, with `η ≥ 0` (the lag bound (13)).

`D̂_{<a}` is `earlyNoise D a`, `D̂_{≥a}` is `lateNoise D a`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Remark12 Oscillation Absorbed Target BaseFactor
  DesignedZero

namespace Decomp

/-- The target (6) with the concrete absorbed count and capped density. -/
noncomputable def targetOf (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) :
    ℝ → ℝ :=
  target X₀ κ (countA A) (absorbedDensityCap (thetaB θ) A u) (osc θ α γ xp)

/-- The lag `D = N_P - T`. -/
noncomputable def lagOf (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (α γ xp : ℕ → ℝ) (x : ℝ) : ℝ :=
  P.N x - targetOf θ X₀ κ A u α γ xp x

/-- The target splits as base part + absorbed part + oscillation. -/
lemma targetOf_eq {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ} {u : ℝ → ℝ} {α γ xp : ℕ → ℝ}
    (hsp : Spacing xp) (hX1 : 1 ≤ X₀) (hxp : (X₀ : ℝ) ≤ xp 0) {x : ℝ} (hx : 0 < x) :
    targetOf θ X₀ κ A u α γ xp x = baseErr X₀ κ x + x +
      absE X₀ (countA A) (absorbedDensityCap (thetaB θ) A u) x + osc θ α γ xp x := by
  have hR0 : osc θ α γ xp X₀ = 0 :=
    osc_eq_zero_of_le hsp (by exact_mod_cast hX1) hxp
  unfold targetOf target baseErr absE
  by_cases h : x < X₀
  · rw [if_pos h, if_pos h, if_pos h, osc_eq_zero_of_le hsp hx (h.le.trans hxp)]
    ring
  · rw [if_neg h, if_neg h, if_neg h, hR0]
    unfold rigidErr
    ring

/-- The transform integrand of the lag is integrable on `(1, ∞)`. -/
lemma lag_integrableOn (P : BeurlingSystem) {X₀ : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers)
    {κ θ : ℝ} (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2) {A : Set ℝ} {u : ℝ → ℝ}
    (hAu : ∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (thetaB θ) = a) (hAfin : LocFin A)
    (hcap : ∀ v ≥ (X₀ : ℝ), absorbedDensity (thetaB θ) A u v ≤ 0.1 / Real.log v)
    {α γ xp : ℕ → ℝ} (hsp : Spacing xp) {C : ℝ} (hα : ∀ k, |α k| ≤ C) (hxp : (X₀ : ℝ) ≤ xp 0)
    {η K : ℝ} (hη : 0 ≤ η)
    (hD : ∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ K * x ^ η)
    {s : ℂ} (hsθ : θ < s.re) (hsη : η < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (lagOf P θ X₀ κ A u α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  have hX1 : 1 ≤ X₀ := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hXs)
  have hX1' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX1
  have hs0 : 0 < s.re := by linarith
  set D := lagOf P θ X₀ κ A u α γ xp with hDdef
  set E := absE (X₀ : ℝ) (countA A) (absorbedDensityCap (thetaB θ) A u) with hEdef
  have hW : AbsorbedWindowHyp (thetaB θ) X₀ A u :=
    ⟨thetaB_pos (by linarith), thetaB_le_one (by linarith), hX1', fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2, hAfin⟩
  obtain ⟨hiB, -⟩ := mellin_baseErr hXs hκ hs0 hs1
  obtain ⟨hiA, -⟩ := mellin_absE hW hcap (s := s) (by linarith [thetaB_le_self θ])
  obtain ⟨hiR, -⟩ := mellin_osc (θ := θ) (γ := γ) hsp hα hsθ
  -- the pointwise split `N - x = (T_base - x) + E_A + R + D`
  have hsplit : ∀ x : ℝ, 0 < x → P.N x - 1 * x =
      baseErr X₀ κ x + E x + osc θ α γ xp x + D x := by
    intro x hx
    simp only [hDdef, hEdef, lagOf]
    rw [targetOf_eq hsp hX1 hxp hx]
    ring
  -- integrability of the lag part
  set c : ℝ := P.N X₀ + X₀ with hc
  have hDb : ∀ x ∈ Ioi (1 : ℝ), |D x| ≤ max K c * x ^ η := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx1.le hη
    rcases le_or_gt (X₀ : ℝ) x with hxX | hxX
    · exact (hD x hxX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith) _))
    · have hT : targetOf θ X₀ κ A u α γ xp x = ⌊x⌋₊ := by
        simp only [targetOf, target, if_pos hxX]
      have hN0 : 0 ≤ P.N x := Nat.cast_nonneg _
      have hNX : P.N x ≤ P.N X₀ := BeurlingSystem.N_mono P hxX.le
      have hfl : (⌊x⌋₊ : ℝ) ≤ X₀ := (Nat.floor_le (by linarith)).trans hxX.le
      have hfl0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
      have h1 : |D x| ≤ c := by
        simp only [hDdef, lagOf, hT, hc]
        rw [abs_le]; constructor <;> linarith
      have hc0 : 0 ≤ c := by rw [hc]; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc |D x| ≤ c := h1
        _ ≤ max K c := le_max_right _ _
        _ = max K c * 1 := by ring
        _ ≤ max K c * x ^ η :=
            mul_le_mul_of_nonneg_left hxη (le_trans hc0 (le_max_right _ _))
  have hNm : AEStronglyMeasurable (fun x : ℝ => ((P.N x - 1 * x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi 1)) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (Complex.measurable_ofReal.comp ((BeurlingSystem.N_mono P).measurable.sub
      (measurable_const.mul measurable_id))).mul ?_
    exact Complex.measurable_ofReal.pow_const _
  have hiD : IntegrableOn (fun x : ℝ => (D x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => (D x : ℂ) * (x : ℂ) ^ (-s - 1))
        (volume.restrict (Ioi 1)) := by
      refine (((hNm.sub hiB.1).sub hiA.1).sub hiR.1).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      simp only [Pi.sub_apply]
      rw [hsplit x hx0]
      push_cast; ring
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := η - s.re - 1) (by linarith)
      one_pos).const_mul (max K c)) hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc |D x| * x ^ (-s.re - 1) ≤ max K c * x ^ η * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hDb x hx) (Real.rpow_nonneg hx0.le _)
      _ = max K c * x ^ (η - s.re - 1) := by
          rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf
  exact hiD

/-- **The decomposition (14).** -/
theorem decomposition_14 (P : BeurlingSystem) {X₀ : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers)
    {κ θ : ℝ} (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ2 : θ ≤ 2) {A : Set ℝ} {u : ℝ → ℝ}
    (hAu : ∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (thetaB θ) = a) (hAfin : LocFin A)
    (hcap : ∀ v ≥ (X₀ : ℝ), absorbedDensity (thetaB θ) A u v ≤ 0.1 / Real.log v)
    {α γ xp : ℕ → ℝ} (hsp : Spacing xp) {C : ℝ} (hα : ∀ k, |α k| ≤ C) (hxp : (X₀ : ℝ) ≤ xp 0)
    {η K : ℝ} (hη : 0 ≤ η)
    (hD : ∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ K * x ^ η)
    {s : ℂ} (hsθ : θ < s.re) (hsη : η < s.re) (hs1 : s ≠ 1) {a : ℝ} (ha : 1 ≤ a) :
    P.zetaCont 1 s = ZBcont X₀ κ s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) +
      (earlyNoise (lagOf P θ X₀ κ A u α γ xp) a s + lateNoise (lagOf P θ X₀ κ A u α γ xp) a s) +
      absorbedHat (thetaB θ) A u s := by
  have hX1 : 1 ≤ X₀ := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hXs)
  have hX1' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX1
  have hs0 : 0 < s.re := by linarith
  set D := lagOf P θ X₀ κ A u α γ xp with hDdef
  set E := absE (X₀ : ℝ) (countA A) (absorbedDensityCap (thetaB θ) A u) with hEdef
  have hW : AbsorbedWindowHyp (thetaB θ) X₀ A u :=
    ⟨thetaB_pos (by linarith), thetaB_le_one (by linarith), hX1', fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2, hAfin⟩
  obtain ⟨hiB, heB⟩ := mellin_baseErr hXs hκ hs0 hs1
  obtain ⟨hiA, heA⟩ := mellin_absE hW hcap (s := s) (by linarith [thetaB_le_self θ])
  obtain ⟨hiR, heR⟩ := mellin_osc (θ := θ) (γ := γ) hsp hα hsθ
  -- the pointwise split `N - x = (T_base - x) + E_A + R + D`
  have hsplit : ∀ x : ℝ, 0 < x → P.N x - 1 * x =
      baseErr X₀ κ x + E x + osc θ α γ xp x + D x := by
    intro x hx
    simp only [hDdef, hEdef, lagOf]
    rw [targetOf_eq hsp hX1 hxp hx]
    ring
  have hiD := lag_integrableOn P hXs hκ hθ0 hθ2 hAu hAfin hcap hsp hα hxp hη hD hsθ hsη hs1
  have heD := mellin_split (s := s) ha hiD
  -- assemble
  have hint_eq : tailMellin (fun x => P.N x - 1 * x) s =
      tailMellin (baseErr X₀ κ) s + tailMellin E s + tailMellin (osc θ α γ xp) s +
        tailMellin D s := by
    unfold tailMellin
    have e : ∫ x in Ioi (1 : ℝ), (((fun x => P.N x - 1 * x) x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
        ∫ x in Ioi (1 : ℝ), ((baseErr X₀ κ x : ℂ) * (x : ℂ) ^ (-s - 1) +
          (E x : ℂ) * (x : ℂ) ^ (-s - 1) + (osc θ α γ xp x : ℂ) * (x : ℂ) ^ (-s - 1) +
          (D x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      simp only
      rw [hsplit x hx0]
      push_cast; ring
    rw [e, integral_add ?_ hiD, integral_add ?_ hiR, integral_add hiB hiA]
    · exact hiB.add hiA
    · exact (hiB.add hiA).add hiR
  unfold BeurlingSystem.zetaCont
  rw [hint_eq, mul_add, mul_add, mul_add, heB, heA, heR, heD]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  push_cast
  ring

end Decomp

end
