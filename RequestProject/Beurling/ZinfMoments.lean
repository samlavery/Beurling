module

public import RequestProject.Beurling.ZBIdentity
public import RequestProject.Beurling.TauEuler
public import RequestProject.Beurling.MeanValueWeighted

/-!
# Lemma 4.8(i): `|Z_B(1+iγ)| ≥ 0.6` on a positive proportion of `[Γ, 2Γ]`

Following the proof of Lemma 4.8(i): the mean value theorem (19) applied to the Dirichlet series
`Z_∞(1+it) = ∑_{n∈D} n^{-1-it}` and to its square gives
`∫_Γ^{2Γ} |Z_∞(1+it)|² ≥ 1.4 Γ` and `∫_Γ^{2Γ} |Z_∞(1+it)|⁴ ≤ 13.1 Γ` (for `Γ` huge);
a Paley–Zygmund argument then shows `|Z_∞(1+it)|² ≥ 0.375` on a set of measure `≥ 0.036 Γ`,
and Lemma 4.2 (`|Z_B - Z_∞| ≤ e^{-X₀²/4}`) transfers this to `Z_B`.

The infinite Dirichlet series is approximated uniformly in `t` by the Dirichlet polynomials
`P_N(t) = ∑_{n∈D, n≤N} n^{-1-it}` (`Pol`), to which the (finite) mean value theorem applies.
-/

@[expose] public section

open Complex MeasureTheory Set Finset Filter Topology BaseFactor

namespace ZMoments

/-- The Dirichlet polynomial `∑_{n∈S} n^{-1} n^{-it}`. -/
noncomputable def Pol (S : Finset ℕ) (t : ℝ) : ℂ := ∑ n ∈ S, (n : ℂ)⁻¹ * (n : ℂ) ^ (-(t * I))

/-- The tail `∑_{n∈D, n>N} 1/n`. -/
noncomputable def tailSum (X₀ N : ℕ) : ℝ :=
  open Classical in
  ∑' k : ℕ, (if k + (N + 1) ∈ X₀.smoothNumbers then (((k + (N + 1) : ℕ) : ℝ))⁻¹ else 0)

/-- The number of factorisations `m = ab` with `a, b ∈ S`. -/
def cnt (S : Finset ℕ) (m : ℕ) : ℕ := ((S ×ˢ S).filter (fun p => p.1 * p.2 = m)).card

/-- `n ↦ 1/n` on the smooth numbers. -/
noncomputable def invSmooth (X₀ : ℕ) (n : ℕ) : ℝ :=
  open Classical in
  if n ∈ X₀.smoothNumbers then (n : ℝ)⁻¹ else 0

lemma hasSum_invSmooth (X₀ : ℕ) : HasSum (invSmooth X₀) (ZinfR X₀ 1) := by
  classical
  have h := (Rankin.hasSum_smooth_rpow X₀ (θ := 1) one_pos).2
  have h' := (hasSum_subtype_iff_indicator (s := (X₀.smoothNumbers : Set ℕ))
    (f := fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)))).mp h
  convert! h' using 1
  funext n
  unfold invSmooth
  simp only [Set.indicator_apply, Real.rpow_neg_one]

lemma tendsto_tailSum (X₀ : ℕ) : Tendsto (tailSum X₀) atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add (invSmooth X₀)).comp (tendsto_add_atTop_nat 1)
  convert! h using 1

lemma cpow_one_add (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(1 + t * I)) = (n : ℂ)⁻¹ * (n : ℂ) ^ (-(t * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.ofReal_natCast, show -(1 + (t : ℂ) * I) = -1 + -(t * I) by ring,
    Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]

lemma norm_cpow_neg_tI (n : ℕ) (hn : n ≠ 0) (t : ℝ) : ‖(n : ℂ) ^ (-(t * I))‖ = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp

lemma norm_Zinf_sub_Pol_le (X₀ N : ℕ) (t : ℝ) :
    ‖Zinf X₀ (1 + t * I) - Pol (Nat.smoothNumbersUpTo N X₀) t‖ ≤ tailSum X₀ N := by
  classical
  set F : ℕ → ℂ := fun n => if n ∈ X₀.smoothNumbers then ((n : ℝ) : ℂ) ^ (-(1 + t * I)) else 0
    with hF
  have hre : (1 + (t : ℂ) * I).re = 1 := by simp
  have hZ : HasSum F (Zinf X₀ (1 + t * I)) := hasSum_smooth_cpow X₀ (by rw [hre]; norm_num)
  have htail := (hasSum_nat_add_iff' (N + 1)).mpr hZ
  have hhead : ∑ i ∈ Finset.range (N + 1), F i = Pol (Nat.smoothNumbersUpTo N X₀) t := by
    rw [hF, ← Finset.sum_filter]
    unfold Pol Nat.smoothNumbersUpTo
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    exact cpow_one_add n (Nat.ne_zero_of_mem_smoothNumbers hn') t
  rw [hhead] at htail
  have hg : HasSum (fun k => invSmooth X₀ (k + (N + 1))) (tailSum X₀ N) := by
    have hs := ((summable_nat_add_iff (N + 1)).mpr (hasSum_invSmooth X₀).summable).hasSum
    convert! hs using 1
  rw [← htail.tsum_eq]
  refine tsum_of_norm_bounded hg fun k => ?_
  simp only [hF, invSmooth]
  split_ifs with h
  · have hn := Nat.ne_zero_of_mem_smoothNumbers h
    have hpos : (0 : ℝ) < ((k + (N + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp [Real.rpow_neg_one]
  · simp

lemma sum_inv_le (X₀ N : ℕ) : ∑ n ∈ Nat.smoothNumbersUpTo N X₀, (n : ℝ)⁻¹ ≤ ZinfR X₀ 1 := by
  classical
  rw [← (hasSum_invSmooth X₀).tsum_eq]
  calc ∑ n ∈ Nat.smoothNumbersUpTo N X₀, (n : ℝ)⁻¹
      = ∑ n ∈ Nat.smoothNumbersUpTo N X₀, invSmooth X₀ n := by
        apply Finset.sum_congr rfl
        intro n hn
        unfold invSmooth
        rw [if_pos (Nat.mem_smoothNumbersUpTo.mp hn).2]
    _ ≤ ∑' n, invSmooth X₀ n :=
        (hasSum_invSmooth X₀).summable.sum_le_tsum _ (fun n _ => by
          unfold invSmooth; split_ifs <;> positivity)

lemma norm_Pol_le (X₀ N : ℕ) (t : ℝ) : ‖Pol (Nat.smoothNumbersUpTo N X₀) t‖ ≤ ZinfR X₀ 1 := by
  unfold Pol
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans (sum_inv_le X₀ N))
  have hn0 := Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hn).2
  rw [norm_mul, norm_cpow_neg_tI n hn0, mul_one, norm_inv, Complex.norm_natCast]

lemma sum_inv_sq_ge {X₀ N : ℕ} (hX : 5 ≤ X₀) (hN : 4 ≤ N) :
    1.42 ≤ ∑ n ∈ Nat.smoothNumbersUpTo N X₀, ((n : ℝ) ^ 2)⁻¹ := by
  have hsub : ({1, 2, 3, 4} : Finset ℕ) ⊆ Nat.smoothNumbersUpTo N X₀ := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨by omega, Nat.mem_smoothNumbers_of_lt (by omega) (by omega)⟩
  calc (1.42 : ℝ) ≤ ∑ n ∈ ({1, 2, 3, 4} : Finset ℕ), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
        norm_num
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

lemma Pol_sq (S : Finset ℕ) (t : ℝ) :
    Pol S t ^ 2 = ∑ m ∈ (S ×ˢ S).image (fun p => p.1 * p.2),
      ((cnt S m : ℂ) / m) * (m : ℂ) ^ (-(t * I)) := by
  classical
  set h : ℕ → ℂ := fun m => (m : ℂ)⁻¹ * (m : ℂ) ^ (-(t * I)) with hh
  have hprod : ∀ a b : ℕ, ((a : ℂ)⁻¹ * (a : ℂ) ^ (-(t * I))) * ((b : ℂ)⁻¹ * (b : ℂ) ^ (-(t * I)))
      = h (a * b) := by
    intro a b
    simp only [hh, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_inv]
    ring
  rw [sq, Pol, Finset.sum_mul_sum, ← Finset.sum_product']
  simp only [hprod]
  rw [Finset.sum_comp h (fun p : ℕ × ℕ => p.1 * p.2)]
  apply Finset.sum_congr rfl
  intro m _
  simp only [hh, nsmul_eq_mul, cnt]
  ring

lemma interval_eq_Icc {F : ℝ → ℝ} {Γ : ℝ} (hΓ : 0 < Γ) :
    ∫ t in Γ..Γ + Γ, F t = ∫ t in Icc Γ (2 * Γ), F t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc, two_mul]

lemma second_moment_Pol {X₀ N : ℕ} (hX : 5 ≤ X₀) (hN : 4 ≤ N) {Γ : ℝ} (hΓ : 0 < Γ) :
    1.42 * Γ - 2 * Real.sqrt 26 * ZinfR X₀ 1 ≤
      ∫ t in Icc Γ (2 * Γ), ‖Pol (Nat.smoothNumbersUpTo N X₀) t‖ ^ 2 := by
  set S := Nat.smoothNumbersUpTo N X₀
  have hS : ∀ n ∈ S, 1 ≤ n := fun n hn =>
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hn).2)
  have hMV := MeanValue.mean_value_weighted S hS (fun n => (n : ℂ)⁻¹) Γ Γ
  rw [interval_eq_Icc hΓ] at hMV
  have h1 : ∑ n ∈ S, ‖(n : ℂ)⁻¹‖ ^ 2 = ∑ n ∈ S, ((n : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl; intro n _; rw [norm_inv, Complex.norm_natCast, inv_pow]
  have h2 : ∑ n ∈ S, (n : ℝ) * ‖(n : ℂ)⁻¹‖ ^ 2 = ∑ n ∈ S, (n : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl; intro n hn
    have : (n : ℝ) ≠ 0 := by have := hS n hn; positivity
    rw [norm_inv, Complex.norm_natCast]; field_simp
  rw [h1, h2] at hMV
  have h3 := sum_inv_sq_ge hX hN
  have h4 := sum_inv_le X₀ N
  have h5 := (abs_le.mp hMV).1
  have h6 : 1.42 * Γ ≤ Γ * ∑ n ∈ S, ((n : ℝ) ^ 2)⁻¹ := by nlinarith
  have h7 : 2 * Real.sqrt 26 * ∑ n ∈ S, (n : ℝ)⁻¹ ≤ 2 * Real.sqrt 26 * ZinfR X₀ 1 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  unfold Pol at *
  linarith

lemma cnt_le_card_divisors (S : Finset ℕ) (hS0 : ∀ n ∈ S, n ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    cnt S m ≤ m.divisors.card := by
  unfold cnt
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨⟨p.2, hp.2.symm⟩, hm⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    have h1 : p.1 ≠ 0 := hS0 _ hp.1.1
    have h2 : p.2 = q.2 := by
      have : p.1 * p.2 = p.1 * q.2 := by rw [hp.2, ← hq.2, ← hpq]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) this
    exact Prod.ext hpq h2

lemma hasSum_tau_sq_smooth' (X₀ : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => if n ∈ X₀.smoothNumbers then
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-σ)) else 0) :=
  (TauSum.hasSum_tau_sq_smooth X₀ hσ).summable

lemma sum_le_tsum_smooth {X₀ : ℕ} (M : Finset ℕ) (hM : ∀ m ∈ M, m ∈ X₀.smoothNumbers)
    (F G : ℕ → ℝ) (hFG : ∀ m ∈ M, F m ≤ G m) (hG0 : ∀ m, 0 ≤ G m)
    (hsum : Summable (fun m => if m ∈ X₀.smoothNumbers then G m else 0)) :
    ∑ m ∈ M, F m ≤ ∑' m, (if m ∈ X₀.smoothNumbers then G m else 0) := by
  calc ∑ m ∈ M, F m ≤ ∑ m ∈ M, (if m ∈ X₀.smoothNumbers then G m else 0) :=
        Finset.sum_le_sum fun m hm => by rw [if_pos (hM m hm)]; exact hFG m hm
    _ ≤ _ := hsum.sum_le_tsum _ (fun m _ => by split_ifs <;> simp [hG0])

lemma fourth_moment_Pol (X₀ N : ℕ) {Γ : ℝ} (hΓ : 0 < Γ) :
    ∫ t in Icc Γ (2 * Γ), ‖Pol (Nat.smoothNumbersUpTo N X₀) t‖ ^ 4 ≤
      13 * Γ + 2 * Real.sqrt 26 * 16 ^ X₀ := by
  classical
  set S := Nat.smoothNumbersUpTo N X₀ with hSdef
  have hSs : ∀ n ∈ S, n ∈ X₀.smoothNumbers := fun n hn => (Nat.mem_smoothNumbersUpTo.mp hn).2
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn => Nat.ne_zero_of_mem_smoothNumbers (hSs n hn)
  set M := (S ×ˢ S).image (fun p => p.1 * p.2) with hMdef
  have hMs : ∀ m ∈ M, m ∈ X₀.smoothNumbers := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_product] at hp
    exact Nat.mul_mem_smoothNumbers (hSs _ hp.1) (hSs _ hp.2)
  have hM0 : ∀ m ∈ M, m ≠ 0 := fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hMs m hm)
  have hM : ∀ m ∈ M, 1 ≤ m := fun m hm => Nat.one_le_iff_ne_zero.mpr (hM0 m hm)
  set b : ℕ → ℂ := fun m => (cnt S m : ℂ) / m with hb
  have hMV := MeanValue.mean_value_weighted M hM b Γ Γ
  rw [interval_eq_Icc hΓ] at hMV
  have hP4 : ∀ t, ‖Pol S t‖ ^ 4 = ‖∑ m ∈ M, b m * (m : ℂ) ^ (-(t * I))‖ ^ 2 := by
    intro t
    rw [← Pol_sq, norm_pow]; ring
  simp_rw [hP4]
  have hcnt : ∀ m ∈ M, (cnt S m : ℝ) ≤ m.divisors.card := by
    intro m hm
    exact_mod_cast cnt_le_card_divisors S hS0 (hM0 m hm)
  have hb2 : ∀ m ∈ M, ‖b m‖ ^ 2 ≤ (m.divisors.card : ℝ) ^ 2 * (m : ℝ) ^ (-(2 : ℝ)) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (hM0 m hm)
    simp only [hb, norm_div, Complex.norm_natCast]
    rw [Real.rpow_neg hm0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hcnt m hm) 2)
      (by positivity)
  have hb1 : ∀ m ∈ M, (m : ℝ) * ‖b m‖ ^ 2 ≤
      (m.divisors.card : ℝ) ^ 2 * (m : ℝ) ^ (-(1 : ℝ)) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (hM0 m hm)
    simp only [hb, norm_div, Complex.norm_natCast]
    rw [Real.rpow_neg_one]
    have : (m : ℝ) * ((cnt S m : ℝ) / m) ^ 2 = (cnt S m : ℝ) ^ 2 * (m : ℝ)⁻¹ := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hcnt m hm) 2)
      (by positivity)
  have hs2 := sum_le_tsum_smooth M hMs _ _ hb2 (fun m => by positivity)
    (hasSum_tau_sq_smooth' X₀ (by norm_num : (0 : ℝ) < 2))
  have hs1 := sum_le_tsum_smooth M hMs _ _ hb1 (fun m => by positivity)
    (hasSum_tau_sq_smooth' X₀ (by norm_num : (0 : ℝ) < 1))
  have h13 := TauSum.tsum_tau_sq_two_le X₀
  have h16 := TauSum.tsum_tau_sq_one_le X₀
  have h5 := (abs_le.mp hMV).2
  have h6 : Γ * ∑ m ∈ M, ‖b m‖ ^ 2 ≤ 13 * Γ := by nlinarith
  have h7 : 2 * Real.sqrt 26 * ∑ m ∈ M, (m : ℝ) * ‖b m‖ ^ 2 ≤ 2 * Real.sqrt 26 * 16 ^ X₀ :=
    mul_le_mul_of_nonneg_left (hs1.trans h16) (by positivity)
  linarith

/-- **Paley–Zygmund on an interval**: for continuous `f` and `G = {t ∈ [a,b] : f t ≥ c}`,
`(∫_{[a,b]} f - c(b-a))² ≤ |G| ∫_{[a,b]} f²` whenever `∫_{[a,b]} f ≥ c(b-a)`. -/
lemma paley_zygmund {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c) (hA : c * (b - a) ≤ ∫ t in Icc a b, f t) :
    ((∫ t in Icc a b, f t) - c * (b - a)) ^ 2 ≤
      volume.real {t ∈ Icc a b | c ≤ f t} * ∫ t in Icc a b, f t ^ 2 := by
  set I := Icc a b with hI
  set T := {t : ℝ | c ≤ f t} with hT
  have hGeq : {t ∈ Icc a b | c ≤ f t} = I ∩ T := rfl
  rw [hGeq]
  set G := I ∩ T with hG
  have hTm : MeasurableSet T := measurableSet_le measurable_const hf.measurable
  have hGm : MeasurableSet G := measurableSet_Icc.inter hTm
  have hfI : IntegrableOn f I := hf.continuousOn.integrableOn_Icc
  have hf2I : IntegrableOn (fun t => f t ^ 2) I := (hf.pow 2).continuousOn.integrableOn_Icc
  have hGI : G ⊆ I := Set.inter_subset_left
  have hfG : IntegrableOn f G := hfI.mono_set hGI
  have hf2G : IntegrableOn (fun t => f t ^ 2) G := hf2I.mono_set hGI
  have hIvol : volume.real I = b - a := by rw [hI, Real.volume_real_Icc, max_eq_left (by linarith)]
  have hvolG : volume G < ⊤ := lt_of_le_of_lt (measure_mono hGI) measure_Icc_lt_top
  set A := ∫ t in G, f t with hA
  set B := ∫ t in G, f t ^ 2 with hB
  -- `∫_I f = A + ∫_{I \ T} f` and `∫_{I \ T} f ≤ c (b - a)`
  have hsplit := integral_inter_add_diff (μ := volume) hTm hfI
  have hrest : ∫ t in I \ T, f t ≤ c * (b - a) := by
    have h1 : ∫ t in I \ T, f t ≤ ∫ t in I \ T, c :=
      setIntegral_mono_on (hfI.mono_set Set.diff_subset) (integrableOn_const
        (lt_of_le_of_lt (measure_mono Set.diff_subset) measure_Icc_lt_top).ne)
        (measurableSet_Icc.diff hTm) (fun t ht => le_of_lt (not_le.mp ht.2))
    rw [setIntegral_const, smul_eq_mul] at h1
    have h2 : volume.real (I \ T) ≤ b - a := by
      rw [← hIvol]; exact measureReal_mono Set.diff_subset measure_Icc_lt_top.ne
    nlinarith [measureReal_nonneg (μ := volume) (s := I \ T)]
  have hAge : (∫ t in I, f t) - c * (b - a) ≤ A := by
    rw [← hsplit]; linarith
  have hBC : B ≤ ∫ t in I, f t ^ 2 :=
    setIntegral_mono_set hf2I (Filter.Eventually.of_forall fun t => by positivity)
      (Filter.Eventually.of_forall hGI)
  -- AM-GM: `A ≤ (λ B + |G|/λ)/2` for every `λ > 0`
  have hamgm : ∀ l : ℝ, 0 < l → A ≤ (l * B + volume.real G / l) / 2 := by
    intro l hl
    have h1 : A ≤ ∫ t in G, (l * f t ^ 2 + 1 / l) / 2 := by
      apply setIntegral_mono_on hfG (((hf2G.const_mul l).add (integrableOn_const
        hvolG.ne)).div_const 2) hGm
      intro t _
      have : 0 ≤ (l * f t - 1) ^ 2 / l := by positivity
      have e : (l * f t - 1) ^ 2 / l = l * f t ^ 2 - 2 * f t + 1 / l := by
        field_simp; ring
      simp only [Pi.add_apply]
      linarith
    rw [integral_div, integral_add (hf2G.const_mul l) (integrableOn_const hvolG.ne),
      integral_const_mul, setIntegral_const, smul_eq_mul] at h1
    rw [hB]; convert! h1 using 2; ring
  have hA0 : 0 ≤ A := by linarith
  have hAB : A ^ 2 ≤ volume.real G * B := by
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg measureReal_nonneg (integral_nonneg fun t => by positivity)
    · have hB0 : 0 ≤ B := integral_nonneg fun t => by positivity
      rcases hB0.eq_or_lt with hB' | hB'
      · exfalso
        have hv := measureReal_nonneg (μ := volume) (s := G)
        have h1 := hamgm ((volume.real G + 1) / A) (by positivity)
        rw [← hB', mul_zero, zero_add] at h1
        have e : volume.real G / ((volume.real G + 1) / A) / 2 =
            A * (volume.real G / (volume.real G + 1)) / 2 := by field_simp
        rw [e] at h1
        have h2 : volume.real G / (volume.real G + 1) < 1 := by
          rw [div_lt_one (by linarith)]; linarith
        nlinarith
      · have h1 := hamgm (A / B) (by positivity)
        have e : (A / B * B + volume.real G / (A / B)) / 2 = A / 2 + volume.real G * B / A / 2 := by
          field_simp
        rw [e] at h1
        have h2 : A ≤ volume.real G * B / A := by linarith
        rwa [le_div_iff₀ h, ← sq] at h2
  calc ((∫ t in I, f t) - c * (b - a)) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by linarith) hAge 2
    _ ≤ volume.real G * B := hAB
    _ ≤ volume.real G * ∫ t in I, f t ^ 2 := mul_le_mul_of_nonneg_left hBC measureReal_nonneg

set_option maxHeartbeats 1600000 in
/-- **Lemma 4.8(i)**: if `X₀ ≥ 24`, `0 < κ ≤ 1` and `κΓ ≥ e^{X₀²/3}`, then
`|Z_B(1+iγ)| < 0.6` on a subset of `[Γ, 2Γ]` of measure at most `0.964 Γ`. -/
theorem lemma_4_8_i {X₀ : ℕ} (hX : 24 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) :
    volume {γ ∈ Icc Γ (2 * Γ) | ‖ZBcont X₀ κ (1 + γ * I)‖ < 0.6} ≤
      ENNReal.ofReal (0.964 * Γ) := by
  have hX' : (24 : ℝ) ≤ X₀ := by exact_mod_cast hX
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  have hΓbig : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ Γ :=
    hΓ.trans (by nlinarith)
  set Z1 := ZinfR X₀ 1 with hZ1def
  have hZ1 : Z1 ≤ 4 ^ X₀ := ZinfR_le_four_pow X₀ (by norm_num)
  have hZ10 : 0 < Z1 := ZinfR_pos X₀ one_pos
  set δ := 1 / (1000 * (Z1 + 1) ^ 3) with hδdef
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N, hN4, hNt⟩ : ∃ N, 4 ≤ N ∧ tailSum X₀ N ≤ δ := by
    have h1 := (tendsto_tailSum X₀).eventually (gt_mem_nhds hδ0)
    obtain ⟨N, hN⟩ := (h1.and (eventually_ge_atTop 4)).exists
    exact ⟨N, hN.2, hN.1.le⟩
  set S := Nat.smoothNumbersUpTo N X₀ with hS
  set f : ℝ → ℝ := fun t => ‖Zinf X₀ (1 + t * I)‖ ^ 2 with hf
  set g : ℝ → ℝ := fun t => ‖Pol S t‖ ^ 2 with hg
  have hre : ∀ t : ℝ, (1 + (t : ℂ) * I).re = 1 := fun t => by simp
  have hfZ : ∀ t : ℝ, ‖Zinf X₀ (1 + t * I)‖ ≤ Z1 := fun t =>
    (norm_Zinf_le X₀ (by rw [hre]; norm_num)).trans (by rw [hre])
  have hgZ : ∀ t, ‖Pol S t‖ ≤ Z1 := norm_Pol_le X₀ N
  have hdiff : ∀ t : ℝ, ‖Zinf X₀ (1 + t * I) - Pol S t‖ ≤ δ := fun t =>
    (norm_Zinf_sub_Pol_le X₀ N t).trans hNt
  have hdn : ∀ t : ℝ, |‖Zinf X₀ (1 + t * I)‖ - ‖Pol S t‖| ≤ δ := fun t =>
    (abs_norm_sub_norm_le _ _).trans (hdiff t)
  have hfg : ∀ t, |f t - g t| ≤ 2 * Z1 * δ := by
    intro t
    simp only [hf, hg]
    rw [sq_sub_sq, abs_mul]
    have h1 := hdn t
    have h2 : |‖Zinf X₀ (1 + t * I)‖ + ‖Pol S t‖| ≤ 2 * Z1 := by
      rw [abs_of_nonneg (by positivity)]; linarith [hfZ t, hgZ t]
    calc |‖Zinf X₀ (1 + t * I)‖ + ‖Pol S t‖| * |‖Zinf X₀ (1 + t * I)‖ - ‖Pol S t‖|
        ≤ (2 * Z1) * δ := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = 2 * Z1 * δ := by ring
  have hfg2 : ∀ t, |f t ^ 2 - g t ^ 2| ≤ 4 * Z1 ^ 3 * δ := by
    intro t
    rw [sq_sub_sq, abs_mul]
    have hf0 : 0 ≤ f t := by positivity
    have hg0 : 0 ≤ g t := by positivity
    have hfle : f t ≤ Z1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hfZ t) 2
    have hgle : g t ≤ Z1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgZ t) 2
    have h2 : |f t + g t| ≤ 2 * Z1 ^ 2 := by rw [abs_of_nonneg (by positivity)]; linarith
    calc |f t + g t| * |f t - g t| ≤ (2 * Z1 ^ 2) * (2 * Z1 * δ) :=
          mul_le_mul h2 (hfg t) (abs_nonneg _) (by positivity)
      _ = 4 * Z1 ^ 3 * δ := by ring
  -- continuity
  have hZcont : Continuous fun t : ℝ => Zinf X₀ (1 + t * I) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd := (differentiableAt_Zinf X₀ (s := 1 + t * I) (by rw [hre]; norm_num)).continuousAt
    exact ContinuousAt.comp (g := Zinf X₀) hd
      (by fun_prop : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * I) t)
  have hPcont : Continuous (Pol S) := by
    unfold Pol
    refine continuous_finset_sum _ fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hn).2
      exact_mod_cast this
    exact continuous_const.mul
      ((by fun_prop : Continuous fun t : ℝ => -((t : ℂ) * I)).const_cpow (Or.inl hn0))
  have hfc : Continuous f := (continuous_norm.comp hZcont).pow 2
  have hgc : Continuous g := (continuous_norm.comp hPcont).pow 2
  have hIvol : volume.real (Icc Γ (2 * Γ)) = Γ := by
    rw [Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring
  have hint : ∀ {h : ℝ → ℝ}, Continuous h → IntegrableOn h (Icc Γ (2 * Γ)) :=
    fun hc => hc.continuousOn.integrableOn_Icc
  -- numerics
  have hsq : 2 * Real.sqrt 26 ≤ 11 := by
    have : Real.sqrt 26 ≤ 5.1 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have h16 : 11000 * (16 : ℝ) ^ X₀ ≤ Γ := by
    have he := Real.exp_one_gt_d9
    have h3 : (16 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
      norm_num at this ⊢; linarith
    have h10 : (11000 : ℝ) ≤ Real.exp 10 := by
      have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : (2.7 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith) 10
      norm_num at this ⊢; linarith
    have hp : (16 : ℝ) ^ X₀ ≤ Real.exp (3 * X₀) := by
      rw [show (3 * (X₀ : ℝ)) = X₀ * 3 by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) h3 _
    calc 11000 * (16 : ℝ) ^ X₀ ≤ Real.exp 10 * Real.exp (3 * X₀) :=
          mul_le_mul h10 hp (by positivity) (Real.exp_pos _).le
      _ = Real.exp (10 + 3 * X₀) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((X₀ : ℝ) ^ 2 / 3) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ Γ := hΓbig
  have h4le : (4 : ℝ) ^ X₀ ≤ 16 ^ X₀ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hZ1δ : 2 * Z1 * δ ≤ 1 / 500 := by
    rw [hδdef]
    rw [show 2 * Z1 * (1 / (1000 * (Z1 + 1) ^ 3)) = Z1 / (500 * (Z1 + 1) ^ 3) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ Z1 + 1) 2]
  have hZ3δ : 4 * Z1 ^ 3 * δ ≤ 1 / 250 := by
    rw [hδdef]
    rw [show 4 * Z1 ^ 3 * (1 / (1000 * (Z1 + 1) ^ 3)) = Z1 ^ 3 / (250 * (Z1 + 1) ^ 3) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : Z1 ^ 3 ≤ (Z1 + 1) ^ 3 := pow_le_pow_left₀ hZ10.le (by linarith) 3
    nlinarith
  -- the second moment of `Z_∞`
  have hM2g := second_moment_Pol (X₀ := X₀) (N := N) (by omega) hN4 hΓ0
  have hM2 : 1.417 * Γ ≤ ∫ t in Icc Γ (2 * Γ), f t := by
    have h1 : ∫ t in Icc Γ (2 * Γ), (g t - f t) ≤ ∫ t in Icc Γ (2 * Γ), (2 * Z1 * δ) :=
      setIntegral_mono_on ((hint hgc).sub (hint hfc)) (integrableOn_const (by simp))
        measurableSet_Icc (fun t _ => by linarith [(abs_le.mp (hfg t)).1])
    rw [integral_sub (hint hgc) (hint hfc), setIntegral_const, hIvol, smul_eq_mul] at h1
    have h2 : (2 * Z1 * δ) * Γ ≤ Γ / 500 := by nlinarith
    have h3 : 2 * Real.sqrt 26 * Z1 ≤ Γ / 1000 := by
      have : 2 * Real.sqrt 26 * Z1 ≤ 11 * 16 ^ X₀ := by
        have := mul_le_mul hsq (hZ1.trans h4le) hZ10.le (by norm_num); linarith
      linarith
    show 1.417 * Γ ≤ ∫ t in Icc Γ (2 * Γ), f t
    have : ∫ t in Icc Γ (2 * Γ), g t = ∫ t in Icc Γ (2 * Γ), ‖Pol S t‖ ^ 2 := rfl
    linarith
  -- the fourth moment of `Z_∞`
  have hM4g := fourth_moment_Pol X₀ N hΓ0
  have hM4 : ∫ t in Icc Γ (2 * Γ), f t ^ 2 ≤ 13.006 * Γ := by
    have hfc2 : Continuous fun t => f t ^ 2 := hfc.pow 2
    have hgc2 : Continuous fun t => g t ^ 2 := hgc.pow 2
    have h1 : ∫ t in Icc Γ (2 * Γ), (f t ^ 2 - g t ^ 2) ≤
        ∫ t in Icc Γ (2 * Γ), (4 * Z1 ^ 3 * δ) :=
      setIntegral_mono_on ((hint hfc2).sub (hint hgc2)) (integrableOn_const (by simp))
        measurableSet_Icc (fun t _ => by linarith [(abs_le.mp (hfg2 t)).2])
    rw [integral_sub (hint hfc2) (hint hgc2), setIntegral_const, hIvol, smul_eq_mul] at h1
    have hg4 : ∫ t in Icc Γ (2 * Γ), g t ^ 2 = ∫ t in Icc Γ (2 * Γ), ‖Pol S t‖ ^ 4 := by
      congr 1; funext t; simp only [hg]; ring
    have h2 : (4 * Z1 ^ 3 * δ) * Γ ≤ Γ / 250 := by nlinarith
    have h3 : 2 * Real.sqrt 26 * 16 ^ X₀ ≤ Γ / 1000 := by
      have := mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ 16 ^ X₀); linarith
    linarith
  -- Paley–Zygmund
  set G := {t ∈ Icc Γ (2 * Γ) | (0.375 : ℝ) ≤ f t} with hGdef
  have hPZ := paley_zygmund hfc (a := Γ) (b := 2 * Γ) (c := 0.375)
    (by linarith) (by norm_num) (by nlinarith)
  rw [show 2 * Γ - Γ = Γ by ring] at hPZ
  have hGvol : 0.036 * Γ ≤ volume.real G := by
    have hM4pos : 0 < ∫ t in Icc Γ (2 * Γ), f t ^ 2 := by
      by_contra hneg; push_neg at hneg
      have h0 : ((∫ t in Icc Γ (2 * Γ), f t) - 0.375 * Γ) ^ 2 ≤ 0 :=
        hPZ.trans (mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg hneg)
      have hp : 0 < ((∫ t in Icc Γ (2 * Γ), f t) - 0.375 * Γ) ^ 2 :=
        pow_pos (by linarith) 2
      linarith
    have h1 : (1.042 * Γ) ^ 2 ≤ volume.real G * ∫ t in Icc Γ (2 * Γ), f t ^ 2 := by
      refine le_trans ?_ hPZ
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    by_contra hlt; push_neg at hlt
    have h2 : volume.real G * ∫ t in Icc Γ (2 * Γ), f t ^ 2 ≤ (0.036 * Γ) * (13.006 * Γ) :=
      mul_le_mul hlt.le hM4 hM4pos.le (by positivity)
    have e1 : (1.042 * Γ) ^ 2 = 1.085764 * Γ ^ 2 := by ring
    have e2 : (0.036 * Γ) * (13.006 * Γ) = 0.468216 * Γ ^ 2 := by ring
    have : 0 < Γ ^ 2 := by positivity
    linarith
  -- the bad set avoids `G`
  have hsub : {γ ∈ Icc Γ (2 * Γ) | ‖ZBcont X₀ κ (1 + γ * I)‖ < 0.6} ⊆ Icc Γ (2 * Γ) \ G := by
    rintro γ ⟨hγI, hγ⟩
    refine ⟨hγI, fun hG => ?_⟩
    have hfz : (0.375 : ℝ) ≤ ‖Zinf X₀ (1 + γ * I)‖ ^ 2 := hG.2
    have hz : (0.61 : ℝ) ≤ ‖Zinf X₀ (1 + γ * I)‖ := by
      by_contra hc; push_neg at hc
      have := pow_lt_pow_left₀ hc (norm_nonneg _) (two_ne_zero)
      norm_num at this; linarith
    have hclose := norm_ZBcont_sub_Zinf_le hX hκ hκ1 (s := 1 + γ * I) (by rw [hre]; norm_num)
      (by rw [hre]; norm_num) (by
        simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
        rw [abs_of_pos (by linarith [hγI.1])]
        exact hΓ.trans (mul_le_mul_of_nonneg_left hγI.1 hκ.le))
    have hsmall : Real.exp (-((X₀ : ℝ) ^ 2 / 4)) ≤ 0.01 := by
      have : Real.exp (-((X₀ : ℝ) ^ 2 / 4)) ≤ Real.exp (-5) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h5 : Real.exp (-5) ≤ 0.01 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        have he := Real.exp_one_gt_d9
        have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        have : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
        norm_num at this ⊢; linarith
      linarith
    have := norm_sub_norm_le (Zinf X₀ (1 + γ * I)) (ZBcont X₀ κ (1 + γ * I))
    rw [norm_sub_rev] at this
    linarith
  have hGmeas : MeasurableSet G :=
    measurableSet_Icc.inter (measurableSet_le measurable_const hfc.measurable)
  have hGsub : G ⊆ Icc Γ (2 * Γ) := fun t ht => ht.1
  calc volume {γ ∈ Icc Γ (2 * Γ) | ‖ZBcont X₀ κ (1 + γ * I)‖ < 0.6}
      ≤ volume (Icc Γ (2 * Γ) \ G) := measure_mono hsub
    _ = ENNReal.ofReal (volume.real (Icc Γ (2 * Γ) \ G)) := by
        rw [ofReal_measureReal (measure_ne_top_of_subset diff_subset (by simp))]
    _ ≤ ENNReal.ofReal (0.964 * Γ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [measureReal_diff hGsub hGmeas measure_Icc_lt_top.ne, hIvol]
        linarith

end ZMoments

end
