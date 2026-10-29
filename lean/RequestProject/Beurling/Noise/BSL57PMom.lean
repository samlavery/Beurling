module

public import RequestProject.Beurling.Noise.BSL57Dec

/-!
# Lemma 5.7: moments against `π`

* `tailMom_integrable`, `tailMom_eq` : `∫_u^∞ (w-u)^k e^{-r(w-u)} dw = k!/r^{k+1}` (`r > 0`);
* `master` : for `u ≥ 2`, `r₀ = r(u-1)`, `0 ≤ γ < r₀`, a non-negative `f` on `S ⊆ (u-1, ∞)` with
  `f ≤ A` on `(u-1, u]` and `f(w) ≤ (∑_k c_k (w-u)^k) e^{γ(w-u)}` for `w > u` satisfies
  `∫_S f ρ(w-1)/w ≤ ρ(u-1) (A + u⁻¹ ∑_k c_k k!/(r₀-γ)^{k+1})` (the moment bounds of the proof
  of Lemma 5.7, 04c-saias.tex lines 358-364).
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias.Large

lemma tailMom0_integrable (k : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := r)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) le_rfl hr
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

lemma tailMom0_eq (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(r * t)) = (k.factorial : ℝ) / r ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := r)
    (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have e2 : ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(r * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.rpow_natCast]
  rw [e2, h, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    one_div, inv_pow]
  field_simp

lemma indicator_shift (g : ℝ → ℝ) (u w : ℝ) :
    (Ioi u).indicator (fun w => g (w - u)) w = (Ioi (0 : ℝ)).indicator g (w - u) := by
  by_cases h : u < w
  · rw [Set.indicator_of_mem (show w ∈ Ioi u from h),
      Set.indicator_of_mem (show w - u ∈ Ioi (0 : ℝ) by simp [h])]
  · rw [Set.indicator_of_notMem (show w ∉ Ioi u from h),
      Set.indicator_of_notMem (show w - u ∉ Ioi (0 : ℝ) by simpa using h)]

lemma integrableOn_shift {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (u : ℝ) :
    IntegrableOn (fun w => g (w - u)) (Ioi u) := by
  rw [← integrable_indicator_iff measurableSet_Ioi]
  have h := ((integrable_indicator_iff measurableSet_Ioi).mpr hg).comp_sub_right u
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  exact (indicator_shift g u w).symm

lemma integral_shift (g : ℝ → ℝ) (u : ℝ) :
    ∫ w in Ioi u, g (w - u) = ∫ t in Ioi (0 : ℝ), g t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  simp_rw [indicator_shift g u]
  exact integral_sub_right_eq_self _ u

lemma tailMom_integrable (k : ℕ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    IntegrableOn (fun w => (w - u) ^ k * Real.exp (-(r * (w - u)))) (Ioi u) :=
  integrableOn_shift (tailMom0_integrable k hr) u

lemma tailMom_eq (k : ℕ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    ∫ w in Ioi u, (w - u) ^ k * Real.exp (-(r * (w - u))) = (k.factorial : ℝ) / r ^ (k + 1) := by
  rw [integral_shift (fun t => t ^ k * Real.exp (-(r * t))) u, tailMom0_eq k hr]

/-- The tail majorant `∑_k c_k (w-u)^k e^{-r(w-u)}` is integrable with the explicit integral. -/
lemma tailPoly (N : ℕ) (c : ℕ → ℝ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    IntegrableOn (fun w => ∑ k ∈ Finset.range N, c k * ((w - u) ^ k * Real.exp (-(r * (w - u)))))
      (Ioi u) ∧
    ∫ w in Ioi u, ∑ k ∈ Finset.range N, c k * ((w - u) ^ k * Real.exp (-(r * (w - u)))) =
      ∑ k ∈ Finset.range N, c k * ((k.factorial : ℝ) / r ^ (k + 1)) := by
  have hi : ∀ k ∈ Finset.range N, Integrable
      (fun w => c k * ((w - u) ^ k * Real.exp (-(r * (w - u))))) (volume.restrict (Ioi u)) :=
    fun k _ => (tailMom_integrable k hr u).const_mul (c k)
  refine ⟨integrable_finset_sum _ hi, ?_⟩
  rw [integral_finset_sum _ hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, tailMom_eq k hr u]

/-- The mass of `π` on `(u-1, u]` is at most `1`: `∫_{(u-1,u]} ρ(w-1)/w ≤ ρ(u-1)`. -/
lemma head_mass {u : ℝ} (hu : 2 ≤ u) :
    IntegrableOn (fun w => Dickman.rho (w - 1) / w) (Ioc (u - 1) u) ∧
    ∫ w in Ioc (u - 1) u, Dickman.rho (w - 1) / w ≤ Dickman.rho (u - 1) := by
  have hc := continuousOn_rho_div (a := u - 1) (by linarith)
  have hint : IntegrableOn (fun w => Dickman.rho (w - 1) / w) (Ioc (u - 1) u) :=
    ((hc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine ⟨hint, ?_⟩
  rw [← intervalIntegral.integral_of_le (by linarith),
    Dickman.integral_shift_div (by linarith) (by linarith)]
  linarith [Dickman.rho_pos u]

/-- **The moment bound** (lines 358-364): `E_π`-type integrals of a non-negative function with a
constant bound on `(u-1, u]` and a polynomial-exponential bound beyond `u`. -/
lemma master {u γ A : ℝ} (hu : 2 ≤ u) (hγr : γ < Dickman.ratio (u - 1))
    (hA : 0 ≤ A) (N : ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) {S : Set ℝ} (hS : S ⊆ Ioi (u - 1))
    (hSm : MeasurableSet S) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun w => f w * Dickman.rho (w - 1) / w) S) (hf0 : ∀ w ∈ S, 0 ≤ f w)
    (hhead : ∀ w ∈ S, w ≤ u → f w ≤ A)
    (htail : ∀ w ∈ S, u < w →
      f w ≤ (∑ k ∈ Finset.range N, c k * (w - u) ^ k) * Real.exp (γ * (w - u))) :
    ∫ w in S, f w * Dickman.rho (w - 1) / w ≤
      Dickman.rho (u - 1) * (A + (∑ k ∈ Finset.range N,
        c k * ((k.factorial : ℝ) / (Dickman.ratio (u - 1) - γ) ^ (k + 1))) / u) := by
  set r0 := Dickman.ratio (u - 1) with hr0
  have hr : 0 < r0 - γ := by linarith
  have hu0 : 0 < u := by linarith
  have hρ := Dickman.rho_pos (u - 1)
  have hsplit : S = (S ∩ Iic u) ∪ (S ∩ Ioi u) := by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ioi, Set.inter_univ]
  have hdisj : Disjoint (S ∩ Iic u) (S ∩ Ioi u) :=
    Set.disjoint_left.mpr fun x h1 h2 => absurd (mem_Ioi.mp h2.2) (not_lt.mpr (mem_Iic.mp h1.2))
  rw [hsplit, setIntegral_union hdisj (hSm.inter measurableSet_Ioi)
    (hf.mono_set Set.inter_subset_left) (hf.mono_set Set.inter_subset_left)]
  obtain ⟨hmI, hm⟩ := head_mass hu
  have hsub1 : S ∩ Iic u ⊆ Ioc (u - 1) u := fun w hw => ⟨hS hw.1, hw.2⟩
  -- the head
  have h1 : ∫ w in S ∩ Iic u, f w * Dickman.rho (w - 1) / w ≤ A * Dickman.rho (u - 1) := by
    calc ∫ w in S ∩ Iic u, f w * Dickman.rho (w - 1) / w
        ≤ ∫ w in S ∩ Iic u, A * (Dickman.rho (w - 1) / w) := by
          apply setIntegral_mono_on (hf.mono_set Set.inter_subset_left)
            ((hmI.mono_set hsub1).const_mul A) (hSm.inter measurableSet_Iic)
          intro w hw
          have hw0 : 0 < w := by have := hS hw.1; simp only [mem_Ioi] at this; linarith
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (hhead w hw.1 hw.2)
            (div_nonneg (Dickman.rho_pos _).le hw0.le)
      _ ≤ ∫ w in Ioc (u - 1) u, A * (Dickman.rho (w - 1) / w) := by
          apply setIntegral_mono_set (hmI.const_mul A)
          · refine ae_restrict_of_forall_mem measurableSet_Ioc fun w hw => ?_
            have hw0 : 0 < w := by linarith [hw.1]
            exact mul_nonneg hA (div_nonneg (Dickman.rho_pos _).le hw0.le)
          · exact Filter.Eventually.of_forall hsub1
      _ = A * ∫ w in Ioc (u - 1) u, Dickman.rho (w - 1) / w := integral_const_mul _ _
      _ ≤ A * Dickman.rho (u - 1) := mul_le_mul_of_nonneg_left hm hA
  -- the tail
  obtain ⟨hTi, hTv⟩ := tailPoly N c hr u
  set G := fun w => ∑ k ∈ Finset.range N, c k * ((w - u) ^ k * Real.exp (-((r0 - γ) * (w - u))))
  have hsub2 : S ∩ Ioi u ⊆ Ioi u := Set.inter_subset_right
  have h2 : ∫ w in S ∩ Ioi u, f w * Dickman.rho (w - 1) / w ≤
      Dickman.rho (u - 1) / u * ∑ k ∈ Finset.range N,
        c k * ((k.factorial : ℝ) / (r0 - γ) ^ (k + 1)) := by
    calc ∫ w in S ∩ Ioi u, f w * Dickman.rho (w - 1) / w
        ≤ ∫ w in S ∩ Ioi u, Dickman.rho (u - 1) / u * G w := by
          apply setIntegral_mono_on (hf.mono_set Set.inter_subset_left)
            ((hTi.mono_set hsub2).const_mul _) (hSm.inter measurableSet_Ioi)
          intro w hw
          have hwu : u < w := hw.2
          have hw0 : 0 < w := by linarith
          have ht := rho_tail hu hwu.le
          rw [← hr0] at ht
          have hP0 : 0 ≤ ∑ k ∈ Finset.range N, c k * (w - u) ^ k :=
            Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (pow_nonneg (by linarith) k)
          have hfw := htail w hw.1 hwu
          have hf0' := hf0 w hw.1
          calc f w * Dickman.rho (w - 1) / w = f w * (Dickman.rho (w - 1) / w) := by ring
            _ ≤ ((∑ k ∈ Finset.range N, c k * (w - u) ^ k) * Real.exp (γ * (w - u))) *
                (Dickman.rho (u - 1) * Real.exp (-(r0 * (w - u))) / u) :=
                mul_le_mul hfw ht (div_nonneg (Dickman.rho_pos _).le hw0.le)
                  (mul_nonneg hP0 (Real.exp_pos _).le)
            _ = Dickman.rho (u - 1) / u * G w := by
                simp only [G]
                rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                have : Real.exp (γ * (w - u)) * Real.exp (-(r0 * (w - u))) =
                    Real.exp (-((r0 - γ) * (w - u))) := by rw [← Real.exp_add]; ring_nf
                rw [← this]; ring
      _ ≤ ∫ w in Ioi u, Dickman.rho (u - 1) / u * G w := by
          apply setIntegral_mono_set (hTi.const_mul _)
          · refine ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_
            have : 0 ≤ w - u := by linarith [mem_Ioi.mp hw]
            exact mul_nonneg (div_nonneg hρ.le hu0.le) (Finset.sum_nonneg fun k _ =>
              mul_nonneg (hc k) (mul_nonneg (pow_nonneg this k) (Real.exp_pos _).le))
          · exact Filter.Eventually.of_forall hsub2
      _ = Dickman.rho (u - 1) / u * ∑ k ∈ Finset.range N,
            c k * ((k.factorial : ℝ) / (r0 - γ) ^ (k + 1)) := by
          rw [integral_const_mul, hTv]
  calc _ ≤ A * Dickman.rho (u - 1) + Dickman.rho (u - 1) / u * ∑ k ∈ Finset.range N,
        c k * ((k.factorial : ℝ) / (r0 - γ) ^ (k + 1)) := add_le_add h1 h2
    _ = _ := by field_simp

lemma fact_div_pow_le {r rmin : ℝ} (hmin : 0 < rmin) (hr : rmin ≤ r) (k : ℕ) :
    (k.factorial : ℝ) / r ^ (k + 1) ≤ (k.factorial : ℝ) / rmin ^ (k + 1) :=
  div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hmin.le hr _)

lemma momSum_le {r rmin : ℝ} (hmin : 0 < rmin) (hr : rmin ≤ r) (N : ℕ) (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    ∑ k ∈ Finset.range N, c k * ((k.factorial : ℝ) / r ^ (k + 1)) ≤
      ∑ k ∈ Finset.range N, c k * ((k.factorial : ℝ) / rmin ^ (k + 1)) :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (fact_div_pow_le hmin hr k) (hc k)

/-- Nine polynomial coefficients. -/
noncomputable def c9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else if k = 3 then a3 else
  if k = 4 then a4 else if k = 5 then a5 else if k = 6 then a6 else if k = 7 then a7 else
  if k = 8 then a8 else 0

lemma c9_nonneg {a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) (h7 : 0 ≤ a7) (h8 : 0 ≤ a8)
    (k : ℕ) : 0 ≤ c9 a0 a1 a2 a3 a4 a5 a6 a7 a8 k := by
  unfold c9; split_ifs <;> first | assumption | exact le_rfl

lemma c9_poly (a0 a1 a2 a3 a4 a5 a6 a7 a8 t : ℝ) :
    ∑ k ∈ Finset.range 9, c9 a0 a1 a2 a3 a4 a5 a6 a7 a8 k * t ^ k =
      a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 + a4 * t ^ 4 + a5 * t ^ 5 + a6 * t ^ 6 +
        a7 * t ^ 7 + a8 * t ^ 8 := by
  simp [Finset.sum_range_succ, c9]

lemma c9_mom (a0 a1 a2 a3 a4 a5 a6 a7 a8 r : ℝ) :
    ∑ k ∈ Finset.range 9, c9 a0 a1 a2 a3 a4 a5 a6 a7 a8 k * ((k.factorial : ℝ) / r ^ (k + 1)) =
      a0 / r + a1 / r ^ 2 + 2 * a2 / r ^ 3 + 6 * a3 / r ^ 4 + 24 * a4 / r ^ 5 +
        120 * a5 / r ^ 6 + 720 * a6 / r ^ 7 + 5040 * a7 / r ^ 8 + 40320 * a8 / r ^ 9 := by
  simp [Finset.sum_range_succ, c9, Nat.factorial]; ring

/-- **The moment bound with nine coefficients and `r(u-1) - γ ≥ rmin`.** -/
lemma master9 {u γ A rmin : ℝ} (hu : 2 ≤ u) (hmin : 0 < rmin)
    (hr : rmin ≤ Dickman.ratio (u - 1) - γ) (hA : 0 ≤ A)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) (h7 : 0 ≤ a7) (h8 : 0 ≤ a8)
    {S : Set ℝ} (hS : S ⊆ Ioi (u - 1)) (hSm : MeasurableSet S) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun w => f w * Dickman.rho (w - 1) / w) S) (hf0 : ∀ w ∈ S, 0 ≤ f w)
    (hhead : ∀ w ∈ S, w ≤ u → f w ≤ A)
    (htail : ∀ w ∈ S, u < w → f w ≤ (a0 + a1 * (w - u) + a2 * (w - u) ^ 2 + a3 * (w - u) ^ 3 +
      a4 * (w - u) ^ 4 + a5 * (w - u) ^ 5 + a6 * (w - u) ^ 6 + a7 * (w - u) ^ 7 +
        a8 * (w - u) ^ 8) * Real.exp (γ * (w - u))) :
    (∫ w in S, f w * Dickman.rho (w - 1) / w) / Dickman.rho (u - 1) ≤
      A + (a0 / rmin + a1 / rmin ^ 2 + 2 * a2 / rmin ^ 3 + 6 * a3 / rmin ^ 4 +
        24 * a4 / rmin ^ 5 + 120 * a5 / rmin ^ 6 + 720 * a6 / rmin ^ 7 + 5040 * a7 / rmin ^ 8 +
          40320 * a8 / rmin ^ 9) / u := by
  have hc := c9_nonneg h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hm := master (u := u) (γ := γ) (A := A) hu (by linarith) hA 9
    (c9 a0 a1 a2 a3 a4 a5 a6 a7 a8) hc hS hSm hf hf0 hhead
    (fun w hw huw => by rw [c9_poly]; exact htail w hw huw)
  have hs := momSum_le hmin hr 9 _ hc
  rw [c9_mom _ _ _ _ _ _ _ _ _ rmin] at hs
  have hρ := Dickman.rho_pos (u - 1)
  rw [div_le_iff₀ hρ]
  have hu0 : 0 < u := by linarith
  calc _ ≤ _ := hm
    _ ≤ Dickman.rho (u - 1) * (A + (a0 / rmin + a1 / rmin ^ 2 + 2 * a2 / rmin ^ 3 +
        6 * a3 / rmin ^ 4 + 24 * a4 / rmin ^ 5 + 120 * a5 / rmin ^ 6 + 720 * a6 / rmin ^ 7 +
          5040 * a7 / rmin ^ 8 + 40320 * a8 / rmin ^ 9) / u) := by
        gcongr
    _ = _ := by ring

end BSaias.Large

end
