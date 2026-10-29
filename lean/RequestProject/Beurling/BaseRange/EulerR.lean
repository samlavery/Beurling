module

public import RequestProject.Beurling.BaseRange.AbelFin
public import RequestProject.Beurling.BaseRange.EulerQ
public import RequestProject.Beurling.GenLemma51Final
public import RequestProject.Beurling.Noise.Saias59
public import RequestProject.Beurling.Construction.RealisedPrimes

/-!
# The Rankin–Euler product for a Beurling system satisfying (HBS)

For the realised system the second bullet of the proof of Lemma 7.3(c) needs, for the primes
`p_j ≤ Y` (`Y` the largest value of a prime that can occur, here `Y ≤ 2y`) and `σ = 2/log y`,

  `∑_{e : supp e ⊆ {p_j ≤ Y}} val(e)^{-(1-σ)} ≤ ∏_{p_j ≤ Y} (1 - p_j^{σ-1})^{-1}`  (Rankin), and
  `∏_{p_j ≤ Y} (1 - p_j^{σ-1})^{-1} ≤ 2 e^γ e^{Ein(2)} log y`.

* `hasSum_label_smooth`, `rankin_elems` : Rankin's bound over the elements (through the labels
  `iota e` and Mathlib's Euler product for completely multiplicative functions);
* `HBS.zinf_le` : Mertens' product for the realised primes,
  `∏_{p_j ≤ Y}(1 - 1/p_j)^{-1} ≤ 1.8 log(X₀⁻ + 1) · (log Y/log(X₀⁻/2)) e^{2.21/log(X₀⁻/2)}`
  (the rational primes below `X₀⁻`, `Mertens.ZinfR_one_le`, and Lemma 5.1(iv) above);
* `HBS.sum_rpow_sub_one_le` : `∑_{p_j ≤ Y}(p_j^σ - 1)/p_j ≤ Ein(σ log Y) + 2.2 σ φ(σ log Y)`
  by `abel_fin` against Lemma 5.1(iii) (`Sp_sub_log_mem`);
* `HBS.sum_log_div_sq_le` : `∑_{p_j ≤ Y} log p_j/p_j² ≤ 3` (Abel against Lemma 5.1(iii));
* `HBS.realProd_le` : the product bound.
-/

@[expose] public section

open Real Finset BSCert.EiFn MeasureTheory intervalIntegral Set BeurlingSystem

namespace BaseRange

/-! ### Rankin over the elements -/

/-- The Euler product over the labels below `X`. -/
theorem hasSum_label_smooth (P : BeurlingSystem) (X : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    HasSum (fun m : X.smoothNumbers => (LemmaM.valN P.labelVal m) ^ (-θ))
      (∏ p ∈ X.primesBelow, (1 - P.labelVal p ^ (-θ))⁻¹) := by
  set f : ℕ → ℝ := fun n => (LemmaM.valN P.labelVal n) ^ (-θ) with hf
  have hV1 : ∀ p, 1 ≤ P.labelVal p := P.one_le_labelVal
  have hVpow : ∀ p n : ℕ, p.Prime → LemmaM.valN P.labelVal (p ^ n) = P.labelVal p ^ n := by
    intro p n hp
    unfold LemmaM.valN
    rw [hp.factorization_pow, Finsupp.prod_single_index (by simp)]
  have hpow : ∀ p n : ℕ, p.Prime → f (p ^ n) = (P.labelVal p ^ (-θ)) ^ n := by
    intro p n hp
    simp only [hf, hVpow p n hp]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hV1 p]),
      ← Real.rpow_mul (by linarith [hV1 p]), mul_comm]
  have hlt : ∀ {p : ℕ}, p.Prime → P.labelVal p ^ (-θ) < 1 := by
    intro p _
    exact Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt _) (by linarith)
  have hnn : ∀ p : ℕ, 0 ≤ P.labelVal p ^ (-θ) := fun p => Real.rpow_nonneg (by linarith [hV1 p]) _
  have h1 : f 1 = 1 := by simp [hf, LemmaM.valN_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp [hf, LemmaM.valN_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp [hf, LemmaM.valN_one]
    simp only [hf]
    rw [LemmaM.valN_mul _ hm.ne' hn.ne']
    exact Real.mul_rpow (LemmaM.valN_pos _ (fun r _ => hV1 r)).le
      (LemmaM.valN_pos _ (fun r _ => hV1 r)).le
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simp only [hpow p _ hp, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hnn p)]
    exact summable_geometric_of_lt_one (hnn p) (hlt hp)
  obtain ⟨-, hh⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 hmul hsum X
  convert hh using 1
  apply prod_congr rfl
  intro p hp
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  simp only [hpow p _ hp']
  rw [tsum_geometric_of_lt_one (hnn p) (hlt hp')]

/-- The primes below the `J`-th prime are the `qp j`, `j < J`. -/
lemma primesBelow_qp (J : ℕ) : Nat.primesBelow (qp J) = (range J).image qp := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    refine ⟨Nat.count Nat.Prime p, ?_, exists_qp_eq hp⟩
    by_contra h
    push_neg at h
    have := qp_strictMono.monotone h
    rw [exists_qp_eq hp] at this
    omega
  · rintro ⟨j, hj, rfl⟩
    exact ⟨qp_strictMono hj, qp_prime j⟩

/-- **Rankin's bound over the elements**: if every element of `F` is supported on the first
`J` primes, `∑_{e ∈ F} val(e)^{-θ} ≤ ∏_{j < J}(1 - p_j^{-θ})^{-1}`. -/
theorem rankin_elems (P : BeurlingSystem) {J : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (F : Finset (ℕ →₀ ℕ)) (hF : ∀ e ∈ F, ∀ j ∈ e.support, j < J) :
    ∑ e ∈ F, P.val e ^ (-θ) ≤ ∏ j ∈ range J, (1 - P.p j ^ (-θ))⁻¹ := by
  classical
  have hprod : ∏ j ∈ range J, (1 - P.p j ^ (-θ))⁻¹ =
      ∏ p ∈ (qp J).primesBelow, (1 - P.labelVal p ^ (-θ))⁻¹ := by
    rw [primesBelow_qp, Finset.prod_image (fun a _ b _ h => qp_injective h)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [P.labelVal_qp]
  rw [hprod]
  have hsm : ∀ e ∈ F, iota e ∈ (qp J).smoothNumbers := by
    intro e he
    rw [Nat.mem_smoothNumbers]
    refine ⟨(iota_pos e).ne', fun r hr => ?_⟩
    have hr' : r ∈ (iota e).primeFactors := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hr
    rw [primeFactors_iota, Finset.mem_image] at hr'
    obtain ⟨j, hj, rfl⟩ := hr'
    exact qp_strictMono (hF e he j hj)
  have e1 : ∑ e ∈ F, P.val e ^ (-θ) =
      ∑ m ∈ (F.image iota).subtype (fun m => m ∈ (qp J).smoothNumbers),
        (LemmaM.valN P.labelVal (m : ℕ)) ^ (-θ) := by
    rw [Finset.sum_subtype_of_mem (fun n : ℕ => (LemmaM.valN P.labelVal n) ^ (-θ)) (by
      intro m hm
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
      exact hsm e he)]
    rw [Finset.sum_image (fun a _ b _ h => iota_injective h)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [P.valN_iota]
  rw [e1]
  exact sum_le_hasSum _ (fun _ _ => Real.rpow_nonneg
    (LemmaM.valN_pos _ (fun r _ => P.one_le_labelVal r)).le _) (hasSum_label_smooth P _ hθ)

/-! ### Elementary real bounds -/

/-- `V - V^σ ≥ V/3` for a real `V ≥ 2` when `0 < σ ≤ 1/100` and `σ log V ≤ 2.01`. -/
lemma sub_rpow_ge_real {σ V : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100) (hV : 2 ≤ V)
    (hσV : σ * Real.log V ≤ 2.01) : V / 3 ≤ V - V ^ σ := by
  rw [rpow_eq_exp_mul_log (by linarith)]
  rcases le_or_gt 12 V with h12 | h12
  · have he : Real.exp (σ * Real.log V) ≤ Real.exp 2.01 := Real.exp_le_exp.mpr hσV
    have he2 : Real.exp 2.01 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 2.01 = Real.exp 1 * Real.exp 1 * Real.exp 0.01 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      have h3 : Real.exp 0.01 ≤ 1.0102 := by
        have := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.01)
          (by norm_num)
        norm_num at this ⊢; linarith
      rw [e]
      have h1 : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
      nlinarith [Real.exp_pos 1, Real.exp_pos 0.01]
    linarith
  · have hl : Real.log V ≤ 11 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < V); linarith
    have hu : σ * Real.log V ≤ 0.11 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ V); nlinarith
    have hu0 : 0 ≤ σ * Real.log V := mul_nonneg hσ.le (Real.log_nonneg (by linarith))
    have he : Real.exp (σ * Real.log V) ≤ 4 / 3 := by
      rcases eq_or_lt_of_le hu0 with h0 | h0
      · rw [← h0, Real.exp_zero]; norm_num
      · have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
        have : 1 / (1 - σ * Real.log V) ≤ 4 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
    linarith

/-- The upper Riemann bound for the increasing integrand of `Ein`:
`Ein(B) - Ein(A) ≤ (B - A) φ(B)` for `0 < A ≤ B`. -/
lemma ein_upper {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) : Ein B - Ein A ≤ (B - A) * ph B := by
  set c := ph B
  set G : ℝ → ℝ := fun t => t * c - Ein t
  have hd : ∀ t, 0 < t → HasDerivAt G (c - (Real.exp t - 1) / t) t := by
    intro t ht
    exact ((hasDerivAt_id t).mul_const c |>.congr_deriv (by simp)).sub (hasDerivAt_Ein ht)
  have hmono : MonotoneOn G (Set.Icc A B) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc A B)
    · exact fun v hv => (hd v (by linarith [hv.1])).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      exact (hd v (by linarith [hv.1])).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v (by linarith [hv.1])).deriv]
      have := ph_mono (by linarith [hv.1]) hv.2.le
      have hc : c = (Real.exp B - 1) / B := rfl
      simp only [ph] at this
      linarith
  have := hmono (Set.left_mem_Icc.mpr hAB) (Set.right_mem_Icc.mpr hAB) hAB
  simp only [G] at this
  linarith

end BaseRange

namespace BeurlingSystem

namespace HBS

variable {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma two_le_p (h : P.HBS X0m Z η1 η2 ε1) (hZ : 3 ≤ Z) (j : ℕ) : 2 ≤ P.p j := by
  rw [← h.p_zero_eq_two hZ]; exact P.mono (Nat.zero_le j)

lemma primesLe_filter (P : BeurlingSystem) {Y s : ℝ} (hs : s ≤ Y) :
    (P.primesLe Y).filter (fun j => P.p j ≤ s) = P.primesLe s := by
  ext j; simp only [Finset.mem_filter, mem_primesLe]
  exact ⟨fun h => h.2, fun h => ⟨h.trans hs, h⟩⟩

/-- **`∑_{p_j ≤ Y} (p_j^σ - 1)/p_j ≤ Ein(σ log Y) + 2.2 (Y^σ - 1)/log Y`** under (HBS), for
`2 ≤ Y ≤ Z`, `σ > 0`. -/
theorem sum_rpow_sub_one_le (h : P.HBS X0m Z η1 η2 ε1) (hZ3 : 3 ≤ Z) {Y σ : ℝ} (hY : 2 ≤ Y)
    (hYZ : Y ≤ Z) (hσ : 0 < σ) :
    ∑ j ∈ P.primesLe Y, (P.p j ^ σ - 1) / P.p j ≤
      Ein (σ * Real.log Y) + 2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) := by
  classical
  set a : ℝ := 3 / 2 with ha
  have haY : a ≤ Y := by rw [ha]; linarith
  have hla : 0 < Real.log a := Real.log_pos (by norm_num)
  have hla2 : Real.log a ≤ 1.77 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < a); rw [ha] at this ⊢; linarith
  have hlogpos : ∀ s ∈ Icc a Y, 0 < Real.log s := fun s hs =>
    Real.log_pos (by linarith [hs.1, show (1 : ℝ) < a by norm_num])
  have hspos : ∀ s ∈ Icc a Y, 0 < s := fun s hs => by linarith [hs.1, show (0 : ℝ) < a by norm_num]
  set g : ℝ → ℝ := fun s => (Real.exp (σ * Real.log s) - 1) / Real.log s with hg
  set g' : ℝ → ℝ := fun s => (Real.exp (σ * Real.log s) * σ * Real.log s -
      (Real.exp (σ * Real.log s) - 1)) / (s * Real.log s ^ 2) with hg'
  have hder : ∀ s ∈ Icc a Y, HasDerivAt g (g' s) s := by
    intro s hs
    have hs0 := hspos s hs
    have hl := hlogpos s hs
    have h1 := ((Real.hasDerivAt_log hs0.ne').const_mul σ).exp.sub_const 1
    have h2 := h1.div (Real.hasDerivAt_log hs0.ne') hl.ne'
    convert h2 using 1
    simp only [hg']
    field_simp
  have hcont : ContinuousOn g' (Icc a Y) := by
    have hlog : ContinuousOn Real.log (Icc a Y) := Real.continuousOn_log.mono fun s hs => by
      simp only [mem_compl_iff, mem_singleton_iff]; exact (hspos s hs).ne'
    apply ContinuousOn.div
    · exact (((hlog.const_smul σ).rexp).mul continuousOn_const).mul hlog |>.sub
        ((hlog.const_smul σ).rexp.sub continuousOn_const)
    · exact continuousOn_id.mul (hlog.pow 2)
    · intro s hs; exact mul_ne_zero (hspos s hs).ne' (pow_ne_zero 2 (hlogpos s hs).ne')
  have hg'0 : ∀ s ∈ Icc a Y, 0 ≤ g' s := by
    intro s hs
    have hs0 := hspos s hs
    have hl := hlogpos s hs
    simp only [hg']
    apply div_nonneg _ (by positivity)
    set u := σ * Real.log s
    have hu : 0 ≤ u := mul_nonneg hσ.le hl.le
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have e : Real.exp u * σ * Real.log s = Real.exp u * u := by ring
    rw [e]
    nlinarith [Real.exp_pos u]
  set I := P.primesLe Y
  have hI : ∀ j ∈ I, a < P.p j ∧ P.p j ≤ Y := by
    intro j hj
    exact ⟨by rw [ha]; linarith [h.two_le_p hZ3 j], P.mem_primesLe.mp hj⟩
  have habel := BaseRange.abel_fin I P.p (fun j => Real.log (P.p j) / P.p j) haY hI g g' hder hcont
  have e1 : ∑ j ∈ I, (P.p j ^ σ - 1) / P.p j =
      ∑ j ∈ I, Real.log (P.p j) / P.p j * g (P.p j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hp2 := h.two_le_p hZ3 j
    have hl : 0 < Real.log (P.p j) := Real.log_pos (by linarith)
    simp only [hg]
    rw [BaseRange.rpow_eq_exp_mul_log (by linarith)]
    field_simp
  rw [e1, habel]
  have hC : ∀ s ∈ Icc a Y,
      (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) = P.Sp s := by
    intro s hs
    rw [← Finset.sum_filter, primesLe_filter P hs.2]
    rfl
  have hSpY : ∑ j ∈ I, Real.log (P.p j) / P.p j = P.Sp Y := rfl
  rw [hSpY]
  have hup := (h.Sp_sub_log_mem (by linarith) hYZ).2
  have hlow : ∀ s ∈ Icc a Y, Real.log s - 1.77 ≤ P.Sp s := fun s hs =>
    by linarith [(h.Sp_sub_log_mem (by linarith [hs.1, show (1 : ℝ) ≤ a by norm_num])
      (hs.2.trans hYZ)).1]
  have hint1 : IntervalIntegrable (fun s => (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j
      else 0) * g' s) volume a Y := by
    have hsum : IntervalIntegrable (fun s => ∑ j ∈ I, if P.p j ≤ s then
        Real.log (P.p j) / P.p j else 0) volume a Y := by
      apply Monotone.intervalIntegrable
      intro s1 s2 hs
      apply Finset.sum_le_sum
      intro j _
      have hp2 := h.two_le_p hZ3 j
      have : 0 ≤ Real.log (P.p j) / P.p j :=
        div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (h1.trans hs) h2
      · exact this
      · exact le_rfl
    exact hsum.mul_continuousOn (by rw [Set.uIcc_of_le haY]; exact hcont)
  have hint2 : IntervalIntegrable (fun s => (Real.log s - 1.77) * g' s) volume a Y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haY]
    apply ContinuousOn.mul _ hcont
    exact (Real.continuousOn_log.mono fun s hs => by
      simp only [mem_compl_iff, mem_singleton_iff]; exact (hspos s hs).ne').sub continuousOn_const
  have hmono : ∫ s in a..Y, (Real.log s - 1.77) * g' s ≤
      ∫ s in a..Y, (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) * g' s := by
    apply integral_mono_on haY hint2 hint1
    intro s hs
    rw [hC s hs]
    exact mul_le_mul_of_nonneg_right (hlow s hs) (hg'0 s hs)
  have hF : ∫ s in a..Y, (Real.log s - 1.77) * g' s =
      ((Real.log Y - 1.77) * g Y - Ein (σ * Real.log Y)) -
        ((Real.log a - 1.77) * g a - Ein (σ * Real.log a)) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro s hs
      rw [Set.uIcc_of_le haY] at hs
      have hs0 := hspos s hs
      have hl := hlogpos s hs
      have hu : 0 < σ * Real.log s := mul_pos hσ hl
      have hE := (hasDerivAt_Ein hu).comp s ((Real.hasDerivAt_log hs0.ne').const_mul σ)
      have hlog := (Real.hasDerivAt_log hs0.ne').sub_const 1.77
      have hprod := hlog.mul (hder s hs)
      convert hprod.sub hE using 1
      simp only [hg, hg']
      field_simp
      ring
    · exact hint2
  rw [hF] at hmono
  have hgY : 0 ≤ g Y := by
    have := hlogpos Y ⟨haY, le_rfl⟩
    simp only [hg]
    apply div_nonneg _ this.le
    have := Real.one_le_exp (mul_nonneg hσ.le this.le); linarith
  have hga : 0 ≤ g a := by
    simp only [hg]
    apply div_nonneg _ hla.le
    have := Real.one_le_exp (mul_nonneg hσ.le hla.le); linarith
  have hEa : 0 ≤ Ein (σ * Real.log a) := SmoothTails.Ein_nonneg (mul_nonneg hσ.le hla.le)
  have h1 : P.Sp Y * g Y ≤ (Real.log Y + 0.43) * g Y :=
    mul_le_mul_of_nonneg_right (by linarith) hgY
  have h2 : (Real.log a - 1.77) * g a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hga
  have hgYe : g Y = (Real.exp (σ * Real.log Y) - 1) / Real.log Y := rfl
  rw [← hgYe]
  nlinarith

/-- **`∑_{p_j ≤ Y, p_j > b} log p_j/p_j² ≤ 6.4/b`** under (HBS), for `1 ≤ b`, `2 ≤ Y ≤ Z`. -/
theorem sum_log_div_sq_le (h : P.HBS X0m Z η1 η2 ε1) {Y b : ℝ} (hb : 1 ≤ b)
    (hbY : b ≤ Y) (hYZ : Y ≤ Z) :
    ∑ j ∈ (P.primesLe Y).filter (fun j => b < P.p j), Real.log (P.p j) / P.p j ^ 2 ≤
      6.4 / b := by
  classical
  have hb0 : 0 < b := by linarith
  set I := (P.primesLe Y).filter (fun j => b < P.p j)
  have hI : ∀ j ∈ I, b < P.p j ∧ P.p j ≤ Y := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj
    exact ⟨h2, P.mem_primesLe.mp h1⟩
  set g : ℝ → ℝ := fun s => 1 / s
  set g' : ℝ → ℝ := fun s => -(1 / s ^ 2)
  have hder : ∀ s ∈ Icc b Y, HasDerivAt g (g' s) s := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have := hasDerivAt_inv hs0.ne'
    simp only [g, g', one_div]
    convert this using 1
  have hcont : ContinuousOn g' (Icc b Y) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro s hs; exact pow_ne_zero 2 (by linarith [hs.1])
  have habel := BaseRange.abel_fin I P.p (fun j => Real.log (P.p j) / P.p j) hbY hI g g' hder hcont
  have e1 : ∑ j ∈ I, Real.log (P.p j) / P.p j ^ 2 =
      ∑ j ∈ I, Real.log (P.p j) / P.p j * g (P.p j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := (hI j hj).1
    simp only [g]; field_simp
  rw [e1, habel]
  -- `C(s) = Sp s - Sp b ≤ log(s/b) + 2.2`
  have hSb := (h.Sp_sub_log_mem hb (hbY.trans hYZ)).1
  have hC : ∀ s ∈ Icc b Y,
      (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) ≤ Real.log s - Real.log b + 2.2
      := by
    intro s hs
    have hsub : (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) =
        P.Sp s - P.Sp b := by
      rw [← Finset.sum_filter]
      have : (I.filter fun j => P.p j ≤ s) = (P.primesLe s) \ (P.primesLe b) := by
        ext j; simp only [I, Finset.mem_filter, Finset.mem_sdiff, mem_primesLe, not_le]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨h3.trans hs.2, h2⟩, h3⟩
      rw [this, Finset.sum_sdiff_eq_sub]
      · rfl
      · intro j hj; rw [mem_primesLe] at hj ⊢; linarith [hs.1]
    rw [hsub]
    have := (h.Sp_sub_log_mem (by linarith [hs.1]) (hs.2.trans hYZ)).2
    linarith
  have hCnn : ∀ s, 0 ≤ (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) := by
    intro s
    apply Finset.sum_nonneg
    intro j hj
    have := (hI j hj).1
    split_ifs
    · exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    · exact le_rfl
  have hCY : ∑ j ∈ I, Real.log (P.p j) / P.p j ≤ Real.log Y - Real.log b + 2.2 := by
    have := hC Y ⟨hbY, le_rfl⟩
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (hI j hj).2]
  -- `-∫ C g' = ∫ C/s² ≤ ∫ (log(s/b) + 2.2)/s² ≤ 3.2/b`
  have hint1 : IntervalIntegrable (fun s => (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j
      else 0) * g' s) volume b Y := by
    have hsum : IntervalIntegrable (fun s => ∑ j ∈ I, if P.p j ≤ s then
        Real.log (P.p j) / P.p j else 0) volume b Y := by
      apply Monotone.intervalIntegrable
      intro s1 s2 hs
      apply Finset.sum_le_sum
      intro j hj
      have := (hI j hj).1
      have : 0 ≤ Real.log (P.p j) / P.p j :=
        div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (h1.trans hs) h2
      · exact this
      · exact le_rfl
    exact hsum.mul_continuousOn (by rw [Set.uIcc_of_le hbY]; exact hcont)
  set G : ℝ → ℝ := fun s => (Real.log s - Real.log b + 3.2) / s
  have hint2 : IntervalIntegrable (fun s => (Real.log s - Real.log b + 2.2) * g' s) volume b Y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbY]
    apply ContinuousOn.mul _ hcont
    exact ((Real.continuousOn_log.mono fun s hs => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hs.1]).sub
        continuousOn_const).add continuousOn_const
  have hmono : ∫ s in b..Y, (Real.log s - Real.log b + 2.2) * g' s ≤
      ∫ s in b..Y, (∑ j ∈ I, if P.p j ≤ s then Real.log (P.p j) / P.p j else 0) * g' s := by
    apply integral_mono_on hbY hint2 hint1
    intro s hs
    have hg'n : g' s ≤ 0 := by simp only [g']; have : 0 < s ^ 2 := by nlinarith [hs.1]
                               linarith [div_pos one_pos this]
    exact mul_le_mul_of_nonpos_right (hC s hs) hg'n
  have hF : ∫ s in b..Y, (Real.log s - Real.log b + 2.2) * g' s = G Y - G b := by
    apply integral_eq_sub_of_hasDerivAt
    · intro s hs
      rw [Set.uIcc_of_le hbY] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h1 := (((Real.hasDerivAt_log hs0.ne').sub_const (Real.log b)).add_const 3.2).div
        (hasDerivAt_id s) hs0.ne'
      convert h1 using 1
      simp only [g', id]
      field_simp
      ring
    · exact hint2
  rw [hF] at hmono
  have hY0 : 0 < Y := by linarith
  have hgY : g Y = 1 / Y := rfl
  have h1 : (∑ j ∈ I, Real.log (P.p j) / P.p j) * g Y ≤ (Real.log Y - Real.log b + 2.2) / Y := by
    rw [hgY, mul_one_div]; exact div_le_div_of_nonneg_right hCY hY0.le
  have hGY : G Y = (Real.log Y - Real.log b + 3.2) / Y := rfl
  have hGb : G b = 3.2 / b := by simp only [G]; ring_nf
  have h2 : (Real.log Y - Real.log b + 2.2) / Y ≤ (Real.log Y - Real.log b + 3.2) / Y :=
    div_le_div_of_nonneg_right (by linarith) hY0.le
  have hb6 : 3.2 / b ≤ 6.4 / b := div_le_div_of_nonneg_right (by norm_num) hb0.le
  linarith

/-- **Mertens' product for the realised primes**: for `X₀⁻ ≤ Y ≤ Z` and `log X₀⁻ ≥ 10⁴`,
`∏_{p_j ≤ Y} (1 - 1/p_j)^{-1} ≤ 1.8 log⌈X₀⁻⌉ · (log Y/log(X₀⁻/2)) · e^{2.2/log(X₀⁻/2) + 25.6/X₀⁻}`.
-/
theorem zinf_le (h : P.HBS X0m Z η1 η2 ε1) (hZ3 : 3 ≤ Z) (hXm : 10 ^ 4 ≤ Real.log X0m)
    {Y : ℝ} (hXY : X0m ≤ Y) (hYZ : Y ≤ Z) :
    ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 : ℝ)))⁻¹ ≤
      1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2)) *
        Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) := by
  classical
  have hX7 := h.X0m_ge
  have hX0 : 0 < X0m := by linarith
  set I := P.primesLe Y
  set N := ⌈X0m⌉₊ with hN
  have hNX : X0m ≤ (N : ℝ) := Nat.le_ceil X0m
  rw [← Finset.prod_filter_mul_prod_filter_not I (fun j => P.p j < X0m)]
  -- the rational part
  have hrat : ∏ j ∈ I.filter (fun j => P.p j < X0m), (1 - P.p j ^ (-(1 : ℝ)))⁻¹ =
      BaseFactor.ZinfR N 1 := by
    unfold BaseFactor.ZinfR
    apply Finset.prod_nbij' (fun j => qp j) (fun p => Nat.count Nat.Prime p)
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hid := h.ident (x := P.p j) hj2 ((P.mem_primesLe.mp hj1).trans hYZ) j (Or.inl le_rfl)
      simp only [Nat.mem_primesBelow]
      refine ⟨?_, qp_prime j⟩
      have : ((qp j : ℕ) : ℝ) < X0m := by rw [← hid]; exact hj2
      exact Nat.lt_ceil.mpr this
    · intro p hp
      simp only [Nat.mem_primesBelow] at hp
      have hpX : (p : ℝ) < X0m := Nat.lt_ceil.mp hp.1
      have hq := exists_qp_eq hp.2
      have hid := h.ident (x := (p : ℝ)) hpX (by linarith) (Nat.count Nat.Prime p)
        (Or.inr (by rw [hq]))
      simp only [Finset.mem_filter, I, mem_primesLe]
      rw [hid, hq]
      exact ⟨by linarith, hpX⟩
    · intro j _; exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime j
    · intro p hp
      simp only [Nat.mem_primesBelow] at hp
      exact exists_qp_eq hp.2
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hid := h.ident (x := P.p j) hj2 ((P.mem_primesLe.mp hj1).trans hYZ) j (Or.inl le_rfl)
      rw [hid]
  rw [hrat]
  have hlogN : 10 ^ 4 ≤ Real.log N := hXm.trans (Real.log_le_log hX0 hNX)
  have hZ1 := Mertens.ZinfR_one_le hlogN
  -- the realised part
  set I2 := I.filter (fun j => ¬ P.p j < X0m)
  have hI2 : ∀ j ∈ I2, X0m ≤ P.p j ∧ P.p j ≤ Y := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj
    exact ⟨not_lt.mp h2, P.mem_primesLe.mp h1⟩
  have hfac : ∀ j ∈ I2, (1 - P.p j ^ (-(1 : ℝ)))⁻¹ ≤
      Real.exp (1 / P.p j + 2 * (Real.log (P.p j) / P.p j ^ 2)) := by
    intro j hj
    have hp := (hI2 j hj).1
    have hp3 : 3 ≤ P.p j := by linarith
    have hp0 : 0 < P.p j := by linarith
    rw [Real.rpow_neg_one]
    have hp1 : P.p j - 1 ≠ 0 := by linarith
    have e : (1 - (P.p j)⁻¹)⁻¹ = 1 + 1 / (P.p j - 1) := by
      rw [show 1 - (P.p j)⁻¹ = (P.p j - 1) / P.p j by field_simp, inv_div]
      field_simp; ring
    rw [e]
    have hx := Real.add_one_le_exp (1 / P.p j + 2 * (Real.log (P.p j) / P.p j ^ 2))
    refine le_trans ?_ hx
    have hl : 1 ≤ Real.log (P.p j) := by
      rw [Real.le_log_iff_exp_le hp0]; linarith [Real.exp_one_lt_d9]
    have h1 : 1 / (P.p j - 1) ≤ 1 / P.p j + 2 * (1 / P.p j ^ 2) := by
      have hp0' : 0 < P.p j - 1 := by linarith
      rw [div_le_iff₀ hp0']
      have e2 : (1 / P.p j + 2 * (1 / P.p j ^ 2)) * (P.p j - 1) =
          1 + 1 / P.p j - 2 / P.p j ^ 2 := by field_simp; ring
      rw [e2]
      have : 2 / P.p j ^ 2 ≤ 1 / P.p j := by
        rw [div_le_div_iff₀ (by positivity) hp0]; nlinarith
      linarith
    have h2 : 1 / P.p j ^ 2 ≤ Real.log (P.p j) / P.p j ^ 2 :=
      div_le_div_of_nonneg_right hl (by positivity)
    linarith
  have hprod2 : ∏ j ∈ I2, (1 - P.p j ^ (-(1 : ℝ)))⁻¹ ≤
      Real.exp (∑ j ∈ I2, (1 / P.p j + 2 * (Real.log (P.p j) / P.p j ^ 2))) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod _ hfac
    intro j hj
    have hp := (hI2 j hj).1
    apply inv_nonneg.mpr
    have : P.p j ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    linarith
  -- `∑ 1/p ≤ log(log Y/log(X₀⁻/2)) + 2.2/log(X₀⁻/2)`, `∑ log p/p² ≤ 12.8/X₀⁻`
  have hy2 : 2 ≤ X0m / 2 := by linarith
  have hsub : I2 ⊆ I.filter (fun j => X0m / 2 < P.p j) := by
    intro j hj
    have := hI2 j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, by linarith⟩
  have hnn1 : ∀ j ∈ I.filter (fun j => X0m / 2 < P.p j), 0 ≤ 1 / P.p j := by
    intro j _; have := h.two_le_p hZ3 j; positivity
  have hnn2 : ∀ j ∈ I.filter (fun j => X0m / 2 < P.p j), 0 ≤ Real.log (P.p j) / P.p j ^ 2 := by
    intro j _; have := h.two_le_p hZ3 j
    exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hM4 := h.mertens_iv hy2 (by linarith) hYZ
  have hS1 : ∑ j ∈ I2, 1 / P.p j ≤
      Real.log (Real.log Y / Real.log (X0m / 2)) + 2.2 / Real.log (X0m / 2) := by
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn1 j hj)
    have h2 := (abs_le.mp hM4).2
    linarith
  have hS2 : ∑ j ∈ I2, Real.log (P.p j) / P.p j ^ 2 ≤ 12.8 / X0m := by
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn2 j hj)
    have h2 := h.sum_log_div_sq_le (Y := Y) (b := X0m / 2) (by linarith) (by linarith) hYZ
    have e : 6.4 / (X0m / 2) = 12.8 / X0m := by field_simp; ring
    linarith
  have hlY : 0 < Real.log Y / Real.log (X0m / 2) := by
    apply div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
  have hexp : Real.exp (∑ j ∈ I2, (1 / P.p j + 2 * (Real.log (P.p j) / P.p j ^ 2))) ≤
      (Real.log Y / Real.log (X0m / 2)) * Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← Real.exp_log hlY, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : 25.6 / X0m = 2 * (12.8 / X0m) := by ring
    linarith
  have hZ0 : 0 ≤ BaseFactor.ZinfR N 1 := by
    unfold BaseFactor.ZinfR
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    apply inv_nonneg.mpr
    have : (p : ℝ) ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    linarith
  calc BaseFactor.ZinfR N 1 * ∏ j ∈ I2, (1 - P.p j ^ (-(1 : ℝ)))⁻¹
      ≤ (1.8 * Real.log N) * ((Real.log Y / Real.log (X0m / 2)) *
          Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m)) :=
        mul_le_mul hZ1 (hprod2.trans hexp) (Finset.prod_nonneg fun j hj => by
          have hp := (hI2 j hj).1
          apply inv_nonneg.mpr
          have : P.p j ^ (-(1 : ℝ)) < 1 :=
            Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
          linarith) (by positivity)
    _ = _ := by ring

/-- **The realised Rankin–Euler product**: for `0 < σ ≤ 1/100`, `X₀⁻ ≤ Y ≤ Z`,
`σ log Y ≤ 2.01`,
`∏_{p_j ≤ Y}(1 - p_j^{σ-1})^{-1} ≤ ∏_{p_j ≤ Y}(1 - 1/p_j)^{-1} ·
  e^{Ein(σ log Y) + 2.2 (Y^σ - 1)/log Y + 1076 σ}`. -/
theorem realProd_le (h : P.HBS X0m Z η1 η2 ε1) (hZ3 : 3 ≤ Z) {Y σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (hY : 2 ≤ Y) (hYZ : Y ≤ Z) (hσY : σ * Real.log Y ≤ 2.01) :
    ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹ ≤
      (∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 : ℝ)))⁻¹) *
        Real.exp (Ein (σ * Real.log Y) +
          2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) + 1076 * σ) := by
  classical
  set I := P.primesLe Y
  have hp2 : ∀ j, 2 ≤ P.p j := h.two_le_p hZ3
  have hσV : ∀ j ∈ I, σ * Real.log (P.p j) ≤ 2.01 := by
    intro j hj
    have := P.mem_primesLe.mp hj
    exact le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hp2 j]) this)
      hσ.le) hσY
  have hprod : ∏ j ∈ I, (1 - P.p j ^ (-(1 - σ)))⁻¹ ≤ (∏ j ∈ I, (1 - P.p j ^ (-(1 : ℝ)))⁻¹) *
      Real.exp (∑ j ∈ I, ((P.p j ^ σ - 1) / (P.p j - P.p j ^ σ))) := by
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro j _
      apply inv_nonneg.mpr
      have : P.p j ^ (-(1 - σ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hp2 j]) (by linarith)
      linarith
    · intro j hj
      exact BaseRange.factor_le (hp2 j) (BaseRange.sub_rpow_ge_real hσ hσ1 (hp2 j) (hσV j hj))
  refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j _ => by
    apply inv_nonneg.mpr
    have : P.p j ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hp2 j]) (by norm_num)
    linarith))
  apply Real.exp_le_exp.mpr
  have he4 : Real.exp 2.01 * Real.exp 2.01 ≤ 56 := by
    rw [← Real.exp_add]
    have h := Real.exp_one_lt_d9
    have e : Real.exp (2.01 + 2.01) = (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) *
        Real.exp 0.02 := by
      simp only [← Real.exp_add]; norm_num
    have h3 : Real.exp 0.02 ≤ 1.0205 := by
      have := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.02)
        (by norm_num)
      norm_num at this ⊢; linarith
    rw [e]
    have h1 : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
    have h2 : 0 ≤ Real.exp 1 * Real.exp 1 := by positivity
    nlinarith [Real.exp_pos 0.02]
  have hsplit : ∀ j ∈ I, (P.p j ^ σ - 1) / (P.p j - P.p j ^ σ) ≤
      (P.p j ^ σ - 1) / P.p j + 168 * σ * (Real.log (P.p j) / P.p j ^ 2) := by
    intro j hj
    have hpj := hp2 j
    have hpp := BaseRange.sub_rpow_ge_real hσ hσ1 hpj (hσV j hj)
    have hlp0 : 0 ≤ Real.log (P.p j) := Real.log_nonneg (by linarith)
    set r := P.p j ^ σ with hr
    have hre : r = Real.exp (σ * Real.log (P.p j)) := BaseRange.rpow_eq_exp_mul_log (by linarith)
    have hr2 : r ≤ Real.exp 2.01 := by rw [hre]; exact Real.exp_le_exp.mpr (hσV j hj)
    have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) hσ.le
    have hr3 : r - 1 ≤ σ * Real.log (P.p j) * r := by
      rw [hre]
      have := Real.add_one_le_exp (-(σ * Real.log (P.p j)))
      have h2 : Real.exp (-(σ * Real.log (P.p j))) * Real.exp (σ * Real.log (P.p j)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (σ * Real.log (P.p j))]
    have hd : 0 < P.p j - r := by linarith
    have e : (r - 1) / (P.p j - r) = (r - 1) / P.p j + (r - 1) * r / (P.p j * (P.p j - r)) := by
      field_simp; ring
    rw [e]
    have h4 : (r - 1) * r / (P.p j * (P.p j - r)) ≤ 168 * σ * (Real.log (P.p j) / P.p j ^ 2) := by
      have hnum : (r - 1) * r ≤ σ * Real.log (P.p j) * 56 := by
        have h5 : (r - 1) * r ≤ σ * Real.log (P.p j) * r * r :=
          mul_le_mul_of_nonneg_right hr3 (by linarith)
        have h6 : r * r ≤ 56 := by nlinarith
        have h7 : 0 ≤ σ * Real.log (P.p j) := mul_nonneg hσ.le hlp0
        nlinarith
      have hden : P.p j ^ 2 / 3 ≤ P.p j * (P.p j - r) := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc (r - 1) * r ≤ σ * Real.log (P.p j) * 56 := hnum
        _ = 168 * σ * (Real.log (P.p j) / P.p j ^ 2) * (P.p j ^ 2 / 3) := by
            have : P.p j ≠ 0 := by linarith
            field_simp; ring
        _ ≤ 168 * σ * (Real.log (P.p j) / P.p j ^ 2) * (P.p j * (P.p j - r)) := by
            apply mul_le_mul_of_nonneg_left hden
            have : 0 ≤ Real.log (P.p j) / P.p j ^ 2 := div_nonneg hlp0 (by positivity)
            positivity
    linarith
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := h.sum_rpow_sub_one_le hZ3 hY hYZ hσ
  have hfil : I.filter (fun j => 1 < P.p j) = I :=
    Finset.filter_true_of_mem fun j _ => by linarith [hp2 j]
  have h2 := h.sum_log_div_sq_le (Y := Y) (b := 1) le_rfl (by linarith) hYZ
  rw [hfil] at h2
  have : 168 * σ * ∑ j ∈ I, Real.log (P.p j) / P.p j ^ 2 ≤ 168 * σ * 6.4 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

end HBS

end BeurlingSystem
