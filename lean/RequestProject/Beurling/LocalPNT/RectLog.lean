module

public import Mathlib

/-!
# Primitives and logarithms of holomorphic functions on open rectangles

Mathlib provides primitives of holomorphic functions on disks
(`DifferentiableOn.isExactOn_ball`). Here we extend this to open axis-parallel rectangles
`Ioo a b ×ℂ Ioo c d`: the wedge path (horizontal, then vertical) between two points of such a
rectangle stays inside it, so the wedge integral from a fixed base point is a primitive.

## Main results

* `LocalPNT.DifferentiableOn.exists_primitive_rect`: holomorphic functions on an open rectangle
  have primitives.
* `LocalPNT.exists_log_rect`: a holomorphic nowhere-zero function on an open rectangle has a
  holomorphic logarithm.
* `LocalPNT.exists_log_ball`: the same on a disk.
* `LocalPNT.log_eq_of_exp_eq`: two continuous logarithms of the same function on a preconnected
  set agree everywhere once they agree at one point.
-/

@[expose] public section

open Complex Set
open scoped Real

namespace LocalPNT

section Rect

variable {a b c d : ℝ}

lemma add_mul_I_mem_rect {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d) :
    (x : ℂ) + y * I ∈ Ioo a b ×ℂ Ioo c d := by
  simpa [mem_reProdIm] using ⟨hx, hy⟩

lemma rectangle_subset_rect {z w : ℂ} (hz : z ∈ Ioo a b ×ℂ Ioo c d)
    (hw : w ∈ Ioo a b ×ℂ Ioo c d) : Rectangle z w ⊆ Ioo a b ×ℂ Ioo c d := by
  rw [mem_reProdIm] at hz hw
  intro p hp
  rw [Rectangle, mem_reProdIm] at hp
  exact ⟨ordConnected_Ioo.uIcc_subset hz.1 hw.1 hp.1, ordConnected_Ioo.uIcc_subset hz.2 hw.2 hp.2⟩

lemma intervalIntegrable_horiz_rect {f : ℂ → ℂ} (hf : ContinuousOn f (Ioo a b ×ℂ Ioo c d))
    {x₁ x₂ y : ℝ} (hx₁ : x₁ ∈ Ioo a b) (hx₂ : x₂ ∈ Ioo a b) (hy : y ∈ Ioo c d) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + y * I)) MeasureTheory.volume x₁ x₂ := by
  refine ContinuousOn.intervalIntegrable (hf.comp (by fun_prop) fun x hx ↦ ?_)
  exact add_mul_I_mem_rect (ordConnected_Ioo.uIcc_subset hx₁ hx₂ hx) hy

lemma intervalIntegrable_vert_rect {f : ℂ → ℂ} (hf : ContinuousOn f (Ioo a b ×ℂ Ioo c d))
    {x y₁ y₂ : ℝ} (hx : x ∈ Ioo a b) (hy₁ : y₁ ∈ Ioo c d) (hy₂ : y₂ ∈ Ioo c d) :
    IntervalIntegrable (fun y : ℝ ↦ f (x + y * I)) MeasureTheory.volume y₁ y₂ := by
  refine ContinuousOn.intervalIntegrable (hf.comp (by fun_prop) fun y hy ↦ ?_)
  exact add_mul_I_mem_rect hx (ordConnected_Ioo.uIcc_subset hy₁ hy₂ hy)

/-- On an open rectangle, the wedge integral of a holomorphic function from a base point `p` is
additive: a detour through any other point `z` of the rectangle does not change it. -/
lemma wedgeIntegral_sub_wedgeIntegral_rect {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Ioo a b ×ℂ Ioo c d)) {p z w : ℂ}
    (hp : p ∈ Ioo a b ×ℂ Ioo c d) (hz : z ∈ Ioo a b ×ℂ Ioo c d)
    (hw : w ∈ Ioo a b ×ℂ Ioo c d) :
    wedgeIntegral p w f - wedgeIntegral p z f = wedgeIntegral z w f := by
  have hfc := hf.continuousOn
  rw [mem_reProdIm] at hp hz hw
  set I₁ :=     ∫ x in p.re..w.re, f (x + p.im * I)
  set I₂ := I • ∫ y in p.im..w.im, f (w.re + y * I)
  set I₃ :=     ∫ x in p.re..z.re, f (x + p.im * I)
  set I₄ := I • ∫ y in p.im..z.im, f (z.re + y * I)
  set I₅ :=     ∫ x in z.re..w.re, f (x + z.im * I)
  set I₆ := I • ∫ y in z.im..w.im, f (w.re + y * I)
  set I₇ :=     ∫ x in z.re..w.re, f (x + p.im * I)
  set I₈ := I • ∫ y in p.im..z.im, f (w.re + y * I)
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact intervalIntegrable_horiz_rect hfc hp.1 hz.1 hp.2
    · exact intervalIntegrable_horiz_rect hfc hz.1 hw.1 hp.2
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals]
    · exact intervalIntegrable_vert_rect hfc hw.1 hp.2 hz.2
    · exact intervalIntegrable_vert_rect hfc hw.1 hz.2 hw.2
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have hU : Rectangle (z.re + p.im * I) (w.re + z.im * I) ⊆ Ioo a b ×ℂ Ioo c d :=
      rectangle_subset_rect (add_mul_I_mem_rect hz.1 hp.2) (add_mul_I_mem_rect hw.1 hz.2)
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf.isConservativeOn (z.re + p.im * I) (w.re + z.im * I) hU
  grind [wedgeIntegral]

/-- Holomorphic functions on an open rectangle have primitives. -/
theorem DifferentiableOn.exists_primitive_rect {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (Ioo a b ×ℂ Ioo c d)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Ioo a b ×ℂ Ioo c d, HasDerivAt F (f z) z := by
  rcases (Ioo a b ×ℂ Ioo c d).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · exact ⟨0, by simp [h]⟩
  have hR : IsOpen (Ioo a b ×ℂ Ioo c d) := isOpen_Ioo.reProdIm isOpen_Ioo
  refine ⟨fun w ↦ wedgeIntegral p w f, fun z hz ↦ ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hR z hz
  have hfb := hf.mono hball
  have hd := (hfb.isConservativeOn.hasDerivAt_wedgeIntegral hfb.continuousOn
    (Metric.mem_ball_self hρ)).const_add (wedgeIntegral p z f)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hR.mem_nhds hz] with w hw
  rw [← wedgeIntegral_sub_wedgeIntegral_rect hf hp hz hw]
  ring

end Rect

/-- Two continuous logarithms of the same function on a preconnected set agree once they agree
at one point. -/
theorem log_eq_of_exp_eq {U : Set ℂ} (hU : IsPreconnected U) {L₁ L₂ : ℂ → ℂ}
    (h1 : ContinuousOn L₁ U) (h2 : ContinuousOn L₂ U)
    (he : ∀ z ∈ U, Complex.exp (L₁ z) = Complex.exp (L₂ z)) {z₁ : ℂ} (hz₁ : z₁ ∈ U)
    (h₁ : L₁ z₁ = L₂ z₁) : ∀ z ∈ U, L₁ z = L₂ z := by
  have hT : IsDiscrete (range (Int.cast : ℤ → ℂ)) := by
    have h : Topology.IsEmbedding (Int.cast : ℤ → ℂ) :=
      Complex.isometry_ofReal.isEmbedding.comp Int.isClosedEmbedding_coe_real.isEmbedding
    simpa using (IsDiscrete.univ (X := ℤ)).image h
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hmaps : MapsTo (fun z ↦ (L₁ z - L₂ z) / (2 * π * I)) U (range (Int.cast : ℤ → ℂ)) := by
    intro z hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he z hz)
    exact ⟨n, by simp only [hn]; field_simp; ring⟩
  intro z hz
  have := hU.constant_of_mapsTo hT ((h1.sub h2).div_const _) hmaps hz hz₁
  simp only [h₁, sub_self, zero_div, div_eq_zero_iff, hπ, or_false] at this
  exact sub_eq_zero.mp this

/-- A holomorphic nowhere-zero function on an open convex set, whose logarithmic derivative has
a primitive there, has a holomorphic logarithm. -/
lemma exists_log_of_primitive {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hU' : Convex ℝ U)
    (hg : DifferentiableOn ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) {F : ℂ → ℂ}
    (hF : ∀ z ∈ U, HasDerivAt F (deriv g z / g z) z) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ z ∈ U, Complex.exp (L z) = g z := by
  rcases U.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · exact ⟨0, by simp [h]⟩
  have hgd : ∀ z ∈ U, HasDerivAt g (deriv g z) z := fun z hz ↦
    ((hg z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ U, HasDerivAt (fun w ↦ g w * Complex.exp (-F w)) 0 z := by
    intro z hz
    convert (hgd z hz).mul ((hF z hz).neg.cexp) using 1
    field_simp [hg0 z hz]
    ring
  have hconst : ∀ z ∈ U, g z * Complex.exp (-F z) = g p * Complex.exp (-F p) := fun z hz ↦
    hU.is_const_of_deriv_eq_zero hU'.isPreconnected
      (fun w hw ↦ (hh w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hh w hw).deriv) hz hp
  set C := g p * Complex.exp (-F p)
  have hC : C ≠ 0 := mul_ne_zero (hg0 p hp) (Complex.exp_ne_zero _)
  refine ⟨fun z ↦ F z + Complex.log C, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · exact ((hF z hz).differentiableAt.add_const _).differentiableWithinAt
  · rw [Complex.exp_add, Complex.exp_log hC, ← hconst z hz, mul_comm, mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- A holomorphic nowhere-zero function on an open rectangle has a holomorphic logarithm. -/
theorem exists_log_rect {g : ℂ → ℂ} {a b c d : ℝ}
    (hg : DifferentiableOn ℂ g (Ioo a b ×ℂ Ioo c d))
    (hg0 : ∀ z ∈ Ioo a b ×ℂ Ioo c d, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Ioo a b ×ℂ Ioo c d) ∧
      ∀ z ∈ Ioo a b ×ℂ Ioo c d, Complex.exp (L z) = g z := by
  have hR : IsOpen (Ioo a b ×ℂ Ioo c d) := isOpen_Ioo.reProdIm isOpen_Ioo
  obtain ⟨F, hF⟩ := DifferentiableOn.exists_primitive_rect ((hg.deriv hR).div hg hg0)
  exact exists_log_of_primitive hR
    (((convex_Ioo a b).linear_preimage reLm).inter ((convex_Ioo c d).linear_preimage imLm))
    hg hg0 hF

/-- A holomorphic nowhere-zero function on a disk has a holomorphic logarithm. -/
theorem exists_log_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball c r))
    (hg0 : ∀ z ∈ Metric.ball c r, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, Complex.exp (L z) = g z := by
  obtain ⟨F, hF⟩ := ((hg.deriv Metric.isOpen_ball).div hg hg0).isExactOn_ball
  exact exists_log_of_primitive Metric.isOpen_ball (convex_ball c r) hg hg0 hF

end LocalPNT

end
