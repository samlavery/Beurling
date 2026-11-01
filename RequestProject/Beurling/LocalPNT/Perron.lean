module

public import RequestProject.Beurling.LocalPNT.Inversion

/-!
# §5.7: Perron's formula with a smooth weight

* `laplace_inversion_of_hasCompactSupport`: for `ψ` continuous with compact support and
  `Ψ(s) = ∫ ψ(y) e^{sy} dy` integrable on `Re s = c`, `(1/2π) ∫ Ψ(c + it) e^{-(c+it)x} dt = ψ(x)`.
* `perron_smoothed`: for `h` continuous with compact support and `ĥ(s) = ∫ h(τ) e^{sτ} dτ`,
  `(1/2π) ∫ ĥ(c + it) x^{c+it}/(c + it) dt = ∫_{τ ≥ -log x} h(τ) dτ` for `c > 0`, `x > 0`.
-/

@[expose] public section

open Set Real MeasureTheory Complex Filter Topology

namespace LocalPNT

section Perron

/-- **Laplace inversion for compactly supported functions**, in the form
`ψ(x) = (1/2π) ∫ Ψ(c + it) e^{-(c+it)x} dt` with `Ψ(s) = ∫ ψ(y) e^{sy} dy`. -/
theorem laplace_inversion_of_hasCompactSupport {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hsupp : HasCompactSupport ψ) {c : ℝ}
    (hint : Integrable (fun t : ℝ => ∫ y : ℝ, (ψ y : ℂ) * cexp (((c : ℂ) + t * I) * y)))
    (x : ℝ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ y : ℝ, (ψ y : ℂ) * cexp (((c : ℂ) + t * I) * y)) *
        cexp (-((c : ℂ) + t * I) * x) = ψ x := by
  have hrefl : ∀ t : ℝ, ∫ ξ : ℝ, (ψ (-ξ) : ℂ) * cexp (-((c : ℂ) + t * I) * ξ) =
      ∫ y : ℝ, (ψ y : ℂ) * cexp (((c : ℂ) + t * I) * y) := fun t => by
    rw [← integral_neg_eq_self (fun y : ℝ => (ψ y : ℂ) * cexp (((c : ℂ) + t * I) * y))]
    congr 1
    ext ξ
    push_cast
    ring_nf
  have hcs : HasCompactSupport fun y : ℝ => (ψ (-y) : ℂ) * (Real.exp (-c * y) : ℂ) := by
    have h1 : HasCompactSupport fun y : ℝ => ψ (-y) := hsupp.comp_homeomorph (Homeomorph.neg ℝ)
    exact (h1.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).mul_right
  have key := laplace_inversion (f := fun y : ℝ => (ψ (-y) : ℂ)) (c := c) (by fun_prop)
    ((by fun_prop : Continuous _).integrable_of_hasCompactSupport hcs)
    (by simpa only [hrefl] using hint) (-x)
  simp only [neg_neg, hrefl] at key
  rw [key]
  congr 2
  ext t
  push_cast
  ring_nf

/-- **Smoothed Perron formula.** For `h` continuous with compact support,
`ĥ(s) = ∫ h(τ) e^{sτ} dτ`, `c > 0` and `x > 0`,
`(1/2π) ∫ ĥ(c + it) x^{c+it}/(c + it) dt = ∫_{τ ≥ -log x} h(τ) dτ`. This is Laplace inversion
applied to `ξ ↦ ∫_{τ ≥ -ξ} h(τ) dτ`, whose Laplace transform is `ĥ(s)/s` by Fubini. -/
theorem perron_smoothed {h : ℝ → ℝ} (hc0 : Continuous h) (hsupp : HasCompactSupport h)
    {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x)
    (hint : Integrable (fun t : ℝ => (∫ τ : ℝ, (h τ : ℂ) * cexp (((c : ℂ) + t * I) * τ)) /
      ((c : ℂ) + t * I))) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ τ : ℝ, (h τ : ℂ) * cexp (((c : ℂ) + t * I) * τ)) *
        (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      ∫ τ in Ici (-Real.log x), (h τ : ℂ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ τ, R < τ → h τ = 0 := by
    obtain ⟨R, hR⟩ := hsupp.isCompact.bddAbove
    exact ⟨R, fun τ hτ => image_eq_zero_of_notMem_tsupport fun hm => (hR hm).not_gt hτ⟩
  have hhi : Integrable (fun τ : ℝ => (h τ : ℂ)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (hsupp.comp_left ofReal_zero)
  set F : ℝ → ℂ := fun ξ => ∫ τ in Ici (-ξ), (h τ : ℂ)
  have hFint : ∀ ξ, F ξ = ∫ τ in (-ξ)..R, (h τ : ℂ) := fun ξ => by
    have h0 : ∫ τ in Ioi R, (h τ : ℂ) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => by simp [hR τ hτ]
    show ∫ τ in Ici (-ξ), (h τ : ℂ) = _
    rw [integral_Ici_eq_integral_Ioi, ← intervalIntegral.integral_interval_add_Ioi
      hhi.integrableOn hhi.integrableOn, h0, add_zero]
  have hFc : Continuous F := by
    have hp := intervalIntegral.continuous_primitive (fun a b => hhi.intervalIntegrable) R
    have e : F = fun ξ => -∫ τ in R..(-ξ), (h τ : ℂ) := by
      ext ξ
      rw [hFint, intervalIntegral.integral_symm]
    rw [e]
    exact (hp.comp continuous_neg).neg
  set k : ℝ → ℝ × ℝ → ℂ := fun t => indicator {p : ℝ × ℝ | -p.1 ≤ p.2}
    (fun p => (h p.2 : ℂ) * cexp (-((c : ℂ) + t * I) * p.1)) with hk_def
  have hS : MeasurableSet {p : ℝ × ℝ | -p.1 ≤ p.2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hexpi : Integrable (indicator (Ici (-R)) fun ξ : ℝ => Real.exp (-c * ξ)) := by
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) _
  have hk : ∀ t, Integrable (k t) (volume.prod volume) := fun t => by
    refine Integrable.mono' (hexpi.mul_prod hhi.norm) ?_ (Eventually.of_forall fun p => ?_)
    · exact ((by fun_prop : Continuous _).aestronglyMeasurable).indicator hS
    · have hnn : 0 ≤ indicator (Ici (-R)) (fun ξ : ℝ => Real.exp (-c * ξ)) p.1 * ‖(h p.2 : ℂ)‖ :=
        mul_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _) (norm_nonneg _)
      by_cases hp : p ∈ {p : ℝ × ℝ | -p.1 ≤ p.2}
      · by_cases hz : h p.2 = 0
        · simp [hk_def, hz]
        · have : p.1 ∈ Ici (-R) := by
            have := not_lt.1 (mt (hR p.2) hz)
            have hp' : -p.1 ≤ p.2 := hp
            simp only [mem_Ici]
            linarith
          rw [hk_def]
          simp only [indicator_of_mem hp, indicator_of_mem this, norm_mul, Complex.norm_exp]
          simp [mul_comm]
      · simp only [hk_def, indicator_of_notMem hp, norm_zero]
        exact hnn
  have hkτ : ∀ t ξ, ∫ τ, k t (ξ, τ) = F ξ * cexp (-((c : ℂ) + t * I) * ξ) := fun t ξ => by
    have : (fun τ => k t (ξ, τ)) =
        indicator (Ici (-ξ)) (fun τ => (h τ : ℂ) * cexp (-((c : ℂ) + t * I) * ξ)) := by
      ext τ
      simp [hk_def, indicator]
    rw [this, integral_indicator measurableSet_Ici, integral_mul_const]
  have hkξ : ∀ t τ, ∫ ξ, k t (ξ, τ) =
      (h τ : ℂ) * cexp (((c : ℂ) + t * I) * τ) / ((c : ℂ) + t * I) := fun t τ => by
    have hs : ((c : ℂ) + t * I) ≠ 0 := fun h0 => by
      have := congrArg re h0
      simp at this
      linarith
    have : (fun ξ => k t (ξ, τ)) =
        indicator (Ici (-τ)) (fun ξ => (h τ : ℂ) * cexp (-((c : ℂ) + t * I) * ξ)) := by
      ext ξ
      simp [hk_def, indicator, neg_le]
    rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hc)]
    push_cast
    field_simp
  have hL : ∀ t : ℝ, ∫ ξ : ℝ, F ξ * cexp (-((c : ℂ) + t * I) * ξ) =
      (∫ τ : ℝ, (h τ : ℂ) * cexp (((c : ℂ) + t * I) * τ)) / ((c : ℂ) + t * I) := fun t => by
    calc ∫ ξ : ℝ, F ξ * cexp (-((c : ℂ) + t * I) * ξ) = ∫ ξ : ℝ, ∫ τ : ℝ, k t (ξ, τ) := by
          simp only [hkτ]
      _ = ∫ τ : ℝ, ∫ ξ : ℝ, k t (ξ, τ) := integral_integral_swap (hk t)
      _ = _ := by simp only [hkξ, integral_div]
  have hFi : Integrable (fun ξ : ℝ => F ξ * Real.exp (-c * ξ)) := by
    refine (hk 0).integral_prod_left.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hkτ]
    push_cast
    ring_nf
  have key := laplace_inversion hFc hFi (by simpa only [hL] using hint) (Real.log x)
  rw [show (∫ τ in Ici (-Real.log x), (h τ : ℂ)) = F (Real.log x) from rfl, key]
  congr 2
  ext t
  rw [hL, cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← ofReal_log hx.le]
  ring_nf

end Perron

end LocalPNT

end
