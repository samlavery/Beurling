module

public import RequestProject.Beurling.Defs

/-!
# Basic analytic facts about discrete Beurling systems

* `finite_le`: only finitely many elements have value `≤ x`, so `N_P(x)` is a genuine count.
* `differentiableAt_zetaCont`: if `|N_P(x) - x| ≤ C x^θ` then the partial-summation
  continuation `zetaCont` is holomorphic on `Re s > θ`, `s ≠ 1`.
* `zeta_eq_zetaCont`: for `θ ≤ 1` and `Re s > 1` it agrees with the Dirichlet series `zeta`.

Together these justify using `zetaCont` as "the" zeta function of the system on `Re s > θ`
(first half of the direction (b) ⇒ (a) of Remark 1.2 of the paper).
-/

@[expose] public section

open Filter Topology MeasureTheory Set Asymptotics

lemma tsum_indicator_const_of_finite {α M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] {A : Set α} (hA : A.Finite) (c : M) :
    ∑' a, A.indicator (fun _ => c) a = A.ncard • c := by
  rw [tsum_eq_sum (s := hA.toFinset) (fun a ha => by
    rw [Set.indicator_of_notMem (by simpa using ha)])]
  rw [Finset.sum_congr rfl (fun a ha => Set.indicator_of_mem (by simpa using ha) _),
    Finset.sum_const, Set.ncard_eq_toFinset_card A hA]

namespace BeurlingSystem

variable (P : BeurlingSystem)

lemma one_le_prod_pow (s : Finset ℕ) (e : ℕ →₀ ℕ) : 1 ≤ ∏ i ∈ s, P.p i ^ e i := by
  have := Finset.prod_le_prod (s := s) (f := fun _ => (1:ℝ)) (g := fun i => P.p i ^ e i)
    (fun _ _ => zero_le_one) (fun i _ => one_le_pow₀ (P.one_lt i).le)
  simpa using this

lemma pow_le_val (e : ℕ →₀ ℕ) (j : ℕ) : P.p j ^ e j ≤ P.val e := by
  unfold val Finsupp.prod
  by_cases hj : j ∈ e.support
  · rw [← Finset.mul_prod_erase _ _ hj]
    have h1 : 1 ≤ P.p j ^ e j := one_le_pow₀ (P.one_lt j).le
    have := P.one_le_prod_pow (e.support.erase j) e
    nlinarith
  · rw [Finsupp.notMem_support_iff.mp hj, pow_zero]
    exact P.one_le_prod_pow _ e

lemma one_le_val (e : ℕ →₀ ℕ) : 1 ≤ P.val e := P.one_le_prod_pow _ e

/-- Only finitely many elements have value `≤ x`. -/
theorem finite_le (x : ℝ) : {e : ℕ →₀ ℕ | P.val e ≤ x}.Finite := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt x (P.one_lt 0)
  obtain ⟨M, hM⟩ := (P.tendsto.eventually_gt_atTop x).exists_forall_of_atTop
  let f : ℕ →₀ ℕ := ∑ j ∈ Finset.range M, Finsupp.single j K
  apply (Set.finite_Iic f).subset
  intro e he
  simp only [Set.mem_setOf_eq] at he
  simp only [Set.mem_Iic]
  intro j
  have hf : f j = if j < M then K else 0 := by
    simp [f, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [hf]
  split_ifs with h
  · by_contra hc
    push_neg at hc
    have : P.p 0 ^ K ≤ P.val e :=
      ((pow_le_pow_right₀ (P.one_lt 0).le hc.le).trans
        (pow_le_pow_left₀ (by linarith [P.one_lt 0]) (P.mono (Nat.zero_le j)) _)).trans
        (P.pow_le_val e j)
    linarith
  · by_contra hc
    have : P.p j ≤ P.val e := by
      calc P.p j = P.p j ^ 1 := (pow_one _).symm
        _ ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le (by omega)
        _ ≤ _ := P.pow_le_val e j
    linarith [hM j (by omega)]

lemma N_mono : Monotone P.N := by
  intro x y hxy
  exact Set.ncard_le_ncard (fun e he => le_trans (show P.val e ≤ x from he) hxy) (P.finite_le y)

lemma locallyIntegrable_err :
    LocallyIntegrable (fun t : ℝ => (Ioi (1:ℝ)).indicator
      (fun x => (((P.N x : ℝ) : ℂ) - x)) t) := by
  have h1 : LocallyIntegrable (fun t : ℝ => (P.N t : ℝ)) volume :=
    (Monotone.locallyIntegrable (fun x y h => by exact_mod_cast P.N_mono h))
  have h2 : LocallyIntegrable (fun t : ℝ => ((P.N t : ℝ) : ℂ)) volume := by
    rw [locallyIntegrable_iff] at h1 ⊢
    intro K hK
    exact (h1 K hK).ofReal
  have h3 : LocallyIntegrable (fun t : ℝ => (((P.N t : ℝ) : ℂ) - t)) volume :=
    h2.sub (Complex.continuous_ofReal.locallyIntegrable)
  exact h3.indicator measurableSet_Ioi

lemma integral_eq_mellin (s : ℂ) :
    (∫ x in Ioi (1 : ℝ), (((P.N x : ℝ) : ℂ) - x) * (x : ℂ) ^ (-s - 1)) =
      mellin (fun t : ℝ => (Ioi (1:ℝ)).indicator (fun x => (((P.N x : ℝ) : ℂ) - x)) t) (-s) := by
  unfold mellin
  have : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • (Ioi (1:ℝ)).indicator
      (fun x => (((P.N x : ℝ) : ℂ) - x)) t) =
      (Ioi (1:ℝ)).indicator (fun x : ℝ => (((P.N x : ℝ) : ℂ) - x) * (x : ℂ) ^ (-s - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1:ℝ)
    · simp [Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
    · simp [Set.indicator_of_notMem ht]
  rw [this, setIntegral_indicator measurableSet_Ioi]
  congr 1
  rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]

/-- If `|N_P(x) - x| ≤ C x^θ` for `x ≥ 1`, then `zetaCont` is holomorphic at every `s`
with `Re s > θ`, `s ≠ 1`. -/
theorem differentiableAt_zetaCont {θ C : ℝ} (hN : ∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ)
    {s : ℂ} (hs : θ < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ P.zetaCont s := by
  have hfun : P.zetaCont = fun s => s / (s - 1) + s *
      mellin (fun t : ℝ => (Ioi (1:ℝ)).indicator (fun x => (((P.N x : ℝ) : ℂ) - x)) t) (-s) := by
    funext s
    rw [zetaCont, integral_eq_mellin]
  rw [hfun]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hm : DifferentiableAt ℂ (mellin (fun t : ℝ => (Ioi (1:ℝ)).indicator
      (fun x => (((P.N x : ℝ) : ℂ) - x)) t)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -θ) (b := -s.re - 1)
      (P.locallyIntegrable_err.locallyIntegrableOn _) ?_ (by simp; linarith) ?_ (by simp)
    · refine IsBigO.of_bound C ?_
      filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
      rw [Set.indicator_of_mem (show t ∈ Ioi (1:ℝ) from ht), neg_neg]
      have h := hN t ht.le
      rw [Real.norm_eq_abs (t ^ θ), abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
      have : (((P.N t : ℝ) : ℂ) - (t : ℂ)) = (((P.N t : ℝ) - t : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      exact h
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [Set.indicator_of_notMem (show t ∉ Ioi (1:ℝ) from fun h => by simp at h; linarith [ht.2])]
      simp
  have h1 : DifferentiableAt ℂ (fun s : ℂ => s / (s - 1)) s :=
    DifferentiableAt.div differentiableAt_id (differentiableAt_id.sub_const (1:ℂ)) hsub
  have h2 : DifferentiableAt ℂ (fun s : ℂ => mellin (fun t : ℝ => (Ioi (1:ℝ)).indicator
      (fun x => (((P.N x : ℝ) : ℂ) - x)) t) (-s)) s := hm.comp s differentiableAt_id.neg
  exact h1.add (differentiableAt_id.mul h2)

lemma integral_indicator_Ici_cpow {s : ℂ} (hs : 0 < s.re) {v : ℝ} (hv : 1 ≤ v) :
    ∫ x in Ioi (1:ℝ), (Ici v).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1)) x =
      (v : ℂ) ^ (-s) / s := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hae : (Ioi (1:ℝ) ∩ Ici v : Set ℝ) =ᵐ[volume] Ioi v := by
    rcases eq_or_lt_of_le hv with h | h
    · subst h
      have : (Ioi (1:ℝ) ∩ Ici 1 : Set ℝ) = Ioi 1 := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, h.le⟩
      rw [this]
    · have : (Ioi (1:ℝ) ∩ Ici v : Set ℝ) = Ici v := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
        · exact fun h => h.2
        · exact fun h' => ⟨lt_of_lt_of_le h h', h'⟩
      rw [this]; exact Ioi_ae_eq_Ici.symm
  rw [setIntegral_congr_set hae, integral_Ioi_cpow_of_lt (by simp; linarith) (by linarith)]
  rw [show -s - 1 + 1 = -s by ring, neg_div_neg_eq]

lemma integral_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), (x : ℂ) ^ (-s) = 1 / (s - 1) := by
  rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have : -s + 1 = -(s - 1) := by ring
  rw [this, neg_div_neg_eq]

/-- Partial summation: if `|N_P(x) - x| ≤ C x^θ` with `θ ≤ 1`, then for `Re s > 1` the
Dirichlet series `ζ_P(s)` equals `zetaCont s`. -/
theorem zeta_eq_zetaCont {θ C : ℝ} (hθ : θ ≤ 1) (hN : ∀ x ≥ 1, |(P.N x : ℝ) - x| ≤ C * x ^ θ)
    {s : ℂ} (hs : 1 < s.re) : P.zeta s = P.zetaCont s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; simp [h] at hs
  have hNle : ∀ x ≥ 1, (P.N x : ℝ) ≤ (1 + |C|) * x := by
    intro x hx
    have h1 := hN x hx
    have h2 : x ^ θ ≤ x := by
      calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ
        _ = x := Real.rpow_one x
    have h3 : C * x ^ θ ≤ |C| * x := by
      calc C * x ^ θ ≤ |C| * x ^ θ :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C| * x := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have := (abs_le.mp h1).2
    nlinarith
  set F : (ℕ →₀ ℕ) → ℝ → ℂ := fun e => (Ici (P.val e)).indicator (fun x => (x:ℂ) ^ (-s-1))
    with hFdef
  have hcpow_meas : Measurable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) := by fun_prop
  have hF_meas : ∀ e, Measurable (F e) := fun e => hcpow_meas.indicator measurableSet_Ici
  have hFset : ∀ x e, F e x = {e | P.val e ≤ x}.indicator (fun _ => (x:ℂ) ^ (-s-1)) e := by
    intro x e; simp only [F, Set.indicator, Set.mem_Ici, Set.mem_setOf_eq]
  have hpt : ∀ x : ℝ, ∑' e, F e x = ((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1) := by
    intro x
    simp_rw [hFset x]
    rw [tsum_indicator_const_of_finite (P.finite_le x), nsmul_eq_mul]
    simp [N]
  have hptE : ∀ x : ℝ, ∑' e, ‖F e x‖ₑ = ‖((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1)‖ₑ := by
    intro x
    have : ∀ e, ‖F e x‖ₑ = {e | P.val e ≤ x}.indicator (fun _ => ‖(x:ℂ) ^ (-s-1)‖ₑ) e := by
      intro e; rw [hFset x e, enorm_indicator_eq_indicator_enorm]
    simp_rw [this]
    rw [tsum_indicator_const_of_finite (P.finite_le x), nsmul_eq_mul, enorm_mul,
      ← ofReal_norm_eq_enorm (((P.N x : ℝ) : ℂ)), Complex.norm_real, Real.norm_natCast,
      ENNReal.ofReal_natCast]
    rfl
  have hNmeas : Measurable (fun x : ℝ => ((P.N x : ℝ) : ℂ)) := by
    have : Measurable (fun x : ℝ => (P.N x : ℝ)) :=
      Monotone.measurable (fun x y h => by exact_mod_cast P.N_mono h)
    exact Complex.measurable_ofReal.comp this
  have hbound : ∀ x ∈ Ioi (1:ℝ), ‖((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1)‖ ≤
      (1 + |C|) * x ^ (-s.re) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have : x ^ (-s - 1).re = x ^ (-s.re) * x⁻¹ := by
      rw [show (-s - 1).re = -s.re + (-1) by simp; ring, Real.rpow_add hx0, Real.rpow_neg_one]
    rw [this]
    have hN' := hNle x (le_of_lt hx)
    have hp : 0 < x ^ (-s.re) := Real.rpow_pos_of_pos hx0 _
    calc (P.N x : ℝ) * (x ^ (-s.re) * x⁻¹) ≤ ((1 + |C|) * x) * (x ^ (-s.re) * x⁻¹) :=
          mul_le_mul_of_nonneg_right hN' (by positivity)
      _ = (1 + |C|) * x ^ (-s.re) := by field_simp
  have hIbound : IntegrableOn (fun x : ℝ => (1 + |C|) * x ^ (-s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hGint : IntegrableOn (fun x : ℝ => ((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1)) (Ioi 1) :=
    Integrable.mono' hIbound ((hNmeas.mul hcpow_meas).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  have hfin : ∑' e, ∫⁻ x in Ioi 1, ‖F e x‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun e => (hF_meas e).enorm.aemeasurable)]
    simp_rw [hptE]
    exact hGint.hasFiniteIntegral.ne
  have hGeq : ∫ x in Ioi (1:ℝ), ((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1) =
      ∑' e, ((P.val e : ℝ) : ℂ) ^ (-s) / s := by
    have := integral_tsum (μ := volume.restrict (Ioi (1:ℝ)))
      (fun e => (hF_meas e).aestronglyMeasurable) hfin
    simp_rw [hpt] at this
    rw [this]
    congr 1; funext e
    exact integral_indicator_Ici_cpow (by linarith) (P.one_le_val e)
  have hxint : IntegrableOn (fun x : ℝ => (x:ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hsplit : ∫ x in Ioi (1 : ℝ), (((P.N x : ℝ) : ℂ) - x) * (x : ℂ) ^ (-s - 1) =
      (∫ x in Ioi (1:ℝ), ((P.N x : ℝ) : ℂ) * (x:ℂ) ^ (-s-1)) -
        ∫ x in Ioi (1:ℝ), (x:ℂ) ^ (-s) := by
    rw [← integral_sub hGint hxint]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans one_pos (show (1:ℝ) < x from hx)))
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      have := Complex.cpow_add (-s - 1) 1 hx0
      rw [Complex.cpow_one, show -s - 1 + 1 = -s by ring] at this
      exact this
    rw [sub_mul, hpow, mul_comm (x : ℂ)]
  rw [zetaCont, hsplit, hGeq, integral_cpow_neg hs, tsum_div_const, zeta]
  field_simp
  ring

end BeurlingSystem

end
