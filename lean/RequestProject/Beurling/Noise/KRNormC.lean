module

public import RequestProject.Beurling.Noise.KRTransMain
public import RequestProject.Beurling.Noise.KRNormHarm

/-!
# Corollary 5.17(c) for the shifted kernels, and with the harmonic bound

* `cor_5_17_c_sh` : for the kernels `C^{v,y}_n` started at `v ≥ 0.85 y` with the nominal filters
  of the start `y` (`kS`; for `v = y = x` these are the nominal kernels `kN`),
  `∑_n TV(C^{v,y}_n)/n ≤ (1 + ½λ₀A₀) ∑_e |c_e(y)|/e`, the sums over the levels `y/n ≥ X₀⁻`,
  with the `H_ord` sums only up to `y/X₀⁻` (`HordSumsB`, as in `KRHord.lean`);
* `sum_kS_le` : under (HBS), `λ₀ ≤ 1.001` and `2y/X₀⁻ ≤ Z`, the right side is
  `≤ 2.04 (log y + B₁)`, `B₁ = 1` (Lemma 5.5: `|c_e| ≤ 1`; the harmonic bound `harm_le`).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem}

/-- **Corollary 5.17(c) for the shifted kernels.** -/
theorem cor_5_17_c_sh {H : ℝ → ℝ} {X0m ε θ lam0 A0 A1 : ℝ} {tw : ℕ → ℝ} {v y : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) (hv : 0.85 * y ≤ v)
    (hA : HordSumsB P ε A0 A1 (y / X0m)) :
    ∑ n ∈ NAll P y X0m, (eVariationOn (kS P H tw X0m v y n) univ).toReal /
        LemmaM.valN P.labelVal n ≤
      (1 + 1 / 2 * lam0 * A0) * ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| /
        LemmaM.valN P.labelVal n := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  set G : ℕ → ℕ → ℝ := fun f m => |cN P tw X0m y f| / V f *
    ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2))
  have hG : ∀ f m, 0 ≤ G f m := fun f m => by
    have := hV f; have := hV m; positivity
  have hmem : ∀ n ∈ NAll P y X0m, n ≠ 0 ∧ V n ≤ y / X0m := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
    refine ⟨(iota_pos e).ne', ?_⟩
    simp only [V]; rw [P.valN_iota]; exact P.mem_elems.mp he
  set M := ((P.elems (y / X0m)).image iota).filter (2 ≤ ·)
  have hlev : ∀ n ∈ NAll P y X0m, (eVariationOn (kS P H tw X0m v y n) univ).toReal / V n ≤
      |cN P tw X0m y n| / V n + 1 / 2 * lam0 *
        ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
    intro n hn
    obtain ⟨hn0, -⟩ := hmem n hn
    have hb := level_bound_sh hP hp2 ht hlam hy hv hn0
    rw [div_le_iff₀ (hV n)]
    refine hb.trans (le_of_eq ?_)
    have hs : ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m y f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * V (n / f) ^ ε * (V f / V n) =
        (∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) * V n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfn : f ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
      have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
      have hf0 := hV f
      have hm0 := hV (n / f)
      simp only [G]
      rw [Real.rpow_sub hm0, Real.rpow_two, hVn]
      field_simp
    rw [hs, add_mul, div_mul_cancel₀ _ (hV n).ne']
    ring
  have hre : ∑ n ∈ NAll P y X0m, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
      G f (n / f) ≤ ∑ m ∈ M, ∑ f ∈ NAll P y X0m, G f m := by
    refine sum_divisors_le G hG fun n hn f hf => ?_
    obtain ⟨hn0, hVn1⟩ := hmem n hn
    obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
    have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
    have hm2 : 2 ≤ n / f := by
      obtain ⟨k, hk⟩ := hfn
      have hf0 : 0 < f := by omega
      rw [hk, Nat.mul_div_cancel_left k hf0]
      by_contra hc; push_neg at hc
      interval_cases k <;> simp_all
    constructor
    · refine Finset.mem_filter.mpr ⟨KR.mem_image_iota P (by omega) ?_, hm2⟩
      have : V (n / f) ≤ V n := LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0
      linarith
    · refine KR.mem_image_iota P (by omega) ?_
      have : V f ≤ V n := LemmaM.valN_le_of_dvd _ hval hfn hn0
      linarith
  have hM2 : ∀ m ∈ M, 2 ≤ m ∧ V m ≤ y / X0m := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    refine ⟨hm2, ?_⟩
    simp only [V]; rw [P.valN_iota]; exact P.mem_elems.mp he
  obtain ⟨hA0, -⟩ := hA M hM2
  have hcs0 : 0 ≤ ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / V n :=
    Finset.sum_nonneg fun n _ => by have := hV n; positivity
  have hfin : ∑ m ∈ M, ∑ f ∈ NAll P y X0m, G f m =
      (∑ m ∈ M, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) *
        ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / V n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [G]; ring
  calc ∑ n ∈ NAll P y X0m, (eVariationOn (kS P H tw X0m v y n) univ).toReal / V n
      ≤ ∑ n ∈ NAll P y X0m, (|cN P tw X0m y n| / V n + 1 / 2 * lam0 *
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) :=
        Finset.sum_le_sum hlev
    _ = ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / V n + 1 / 2 * lam0 *
          ∑ n ∈ NAll P y X0m, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
            G f (n / f) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / V n + 1 / 2 * lam0 *
          (A0 * ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / V n) := by
        gcongr
        exact hre.trans ((le_of_eq hfin).trans (mul_le_mul_of_nonneg_right hA0 hcs0))
    _ = _ := by ring

/-- `∑_{y/e ≥ X₀⁻} 1/e ≤ log y + 1` under (HBS) (the harmonic bound with `B₁ = 1`). -/
lemma sum_NAll_inv_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {y : ℝ}
    (hy : X0m ≤ y) (hyZ : y / X0m ≤ Z) :
    ∑ n ∈ NAll P y X0m, 1 / LemmaM.valN P.labelVal n ≤ Real.log y + 1 := by
  have hX := h.X0m_pos
  have hX1 : 1 ≤ X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hy1 : 1 ≤ y / X0m := by rw [le_div_iff₀ hX]; linarith
  have e : ∑ n ∈ NAll P y X0m, 1 / LemmaM.valN P.labelVal n =
      ∑ e ∈ P.elems (y / X0m), 1 / P.val e := by
    unfold NAll
    rw [Finset.sum_image (fun a _ b _ hab => iota_injective hab)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [P.valN_iota]
  rw [e]
  refine (h.harm_le hy1 hyZ).trans ?_
  have : Real.log (y / X0m) ≤ Real.log y := by
    apply Real.log_le_log (by positivity)
    exact div_le_self (by linarith) hX1
  linarith

/-- **Corollary 5.17(c) with the harmonic bound**, for the shifted kernels:
`∑_n TV(C^{v,y}_n)/n ≤ 2.04 (log y + B₁)` (`B₁ = 1`). -/
theorem sum_kS_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {H : ℝ → ℝ} {ε θ lam0 : ℝ} {tw : ℕ → ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) {v y : ℝ} (hy : X0m ≤ y)
    (hv : 0.85 * y ≤ v) (hyZ : y / X0m ≤ Z) :
    ∑ n ∈ NAll P y X0m, (eVariationOn (kS P H tw X0m v y n) univ).toReal /
        LemmaM.valN P.labelVal n ≤ 2.04 * (Real.log y + 1) := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hε : ε ≤ 0.03 := by have := hP.eps_le; linarith
  have hc := cor_5_17_c_sh (A1 := 9.4091) hP hp2 ht hlam hy hv (hordSumsB P h hXm hε hyZ)
  have hle : ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / LemmaM.valN P.labelVal n ≤
      ∑ n ∈ NAll P y X0m, 1 / LemmaM.valN P.labelVal n := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hn
    apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P _).le
    rw [show cN P tw X0m y (iota e) = (LemmaM.coeff tw P.labelVal X0m y (iota e) : ℝ)
      from mass_eq_coeff _ _ _ _ _]
    exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht hval hX.le hy (iota_pos e)
  have hnn : 0 ≤ ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / LemmaM.valN P.labelVal n :=
    Finset.sum_nonneg fun n _ => by have := KR.valN_labelVal_pos P n; positivity
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have h0 : 1 + 1 / 2 * lam0 * 2.0674 ≤ 2.04 := by nlinarith
  have hH := sum_NAll_inv_le h hy hyZ
  calc _ ≤ (1 + 1 / 2 * lam0 * 2.0674) * ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| /
        LemmaM.valN P.labelVal n := hc
    _ ≤ 2.04 * ∑ n ∈ NAll P y X0m, |cN P tw X0m y n| / LemmaM.valN P.labelVal n :=
        mul_le_mul_of_nonneg_right h0 hnn
    _ ≤ 2.04 * (Real.log y + 1) := by linarith

end KR

end
