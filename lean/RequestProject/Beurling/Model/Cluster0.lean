module

public import RequestProject.Beurling.Queue6.Family
public import RequestProject.Beurling.Model.SlotHypCap

/-!
# Proposition 6.11 at the lowest height `z = X₀/2` (the QueueInputs field `cluster0`)

At `z = X₀/2` the windows lie in `(-∞, 2z + 1] = (-∞, X₀ + 1]`, while every decided jittered
prime is `≥ X₀⁻ > √(X₀ + 1)`. So every element of `N ∩ J` has at most one jittered prime, with
exponent `1`, and the window set `S(J)` consists of distinct unit vectors: `rank S(J) = |S(J)|`
(capacity `0`). This is the low-height case of the proof of Proposition 6.11 (§6, the case
`2z + 1 < (X₀⁻)²`): the case `rank < r₀` of Theorem 6.23(a) is vacuous, and only the case
`r ≥ r₀` (Theorem R, stated for `z ≥ X₀/2`) remains.

* `low_vec_unit` : every `v ∈ S(J)` is a unit vector `e_n`;
* `low_rank_eq_card` : `rank S(J) = |S(J)|`;
* `eclW_fail_zero` : **Proposition 6.11 at `z_0 = X₀/2`** for the cluster event `E_cl(z_0)` on a
  good event `G`, from the window model (`prop_6_11_model`) with the skeleton bound
  `skeletonBound_construction`. The inputs are (S3)(d) (`S3dHyp`) and the multi-run skeleton
  bound (`MultiRunSkeletonBound`) at `z_0`, as in `Queue6.eclW_fail`; no Cover Bound is needed,
  and `SlotHyp` is `slotHyp_capH`;
* `cluster0_of` : the field `cluster0` of `QueueInputs`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono RankFull RankFull.Config

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

section Low

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc in
lemma z0_facts : zH X₀ 0 = (X₀ : ℝ) / 2 ∧ 1 < zH X₀ 0 ∧ 10 ^ 8 - 1 ≤ Real.log (zH X₀ 0) ∧
    18 ≤ Real.log (Real.log (zH X₀ 0)) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hz : zH X₀ 0 = (X₀ : ℝ) / 2 := by simp [zH]
  have hbig := X0_ge_big (hc := hc)
  have hL : 10 ^ 8 - 1 ≤ Real.log (zH X₀ 0) := by
    rw [hz, Real.log_div (by linarith) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  refine ⟨hz, by rw [hz]; linarith, hL, ?_⟩
  have hL0 : 0 < Real.log (zH X₀ 0) := by linarith
  rw [Real.le_log_iff_exp_le hL0]
  have he := Real.exp_one_lt_d9
  have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 18
  rw [e]; nlinarith

include hc in
/-- **The window vectors at `z_0 = X₀/2` are unit vectors**: an element of `N ∩ J`,
`J ⊆ (-∞, X₀ + 1]`, has at most one jittered prime factor, since `(X₀⁻)² > X₀ + 1`. -/
theorem low_vec_unit {N D Dmax : ℕ} (ω : JitterΩ) {J : Set ℝ}
    (hJ : J ⊆ Iic ((X₀ : ℝ) + 1)) {v : Fin N → ℕ}
    (hv : v ∈ windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax J) :
    ∃ n, v = Pi.single n 1 := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp1, hp0⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprod, hsupp, -, hval⟩ := Finset.mem_filter.mp hp1
  have hd : 1 ≤ p.2 := by
    have := (Finset.mem_product.mp hprod).2
    rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers] at this
    exact Nat.one_le_iff_ne_zero.mpr this.2.1
  set Xm' := Xm X₀
  have hXm1 := Xm_pos hc
  have hq : ∀ n, p.1 n ≠ 0 → Xm' ≤ qOf (constructionLaw2 hc hev) ω n := by
    intro n hn
    exact valF_ge_Xm hc n ω
  -- the product is at least `X₀⁻^{deg}`
  have hP : Xm' ^ (∑ n, p.1 n) ≤ ∏ n, qOf (constructionLaw2 hc hev) ω n ^ p.1 n := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun n _ => ?_
    by_cases hn : p.1 n = 0
    · simp [hn]
    · exact pow_le_pow_left₀ (by linarith) (hq n hn) _
  have hdeg : ∑ n, p.1 n ≤ 1 := by
    by_contra hc'
    push_neg at hc'
    have h2 : Xm' ^ 2 ≤ Xm' ^ (∑ n, p.1 n) := pow_le_pow_right₀ hXm1.le hc'
    have hv' := hJ hval
    simp only [elemVal, mem_Iic] at hv'
    have hd' : (1 : ℝ) ≤ p.2 := by exact_mod_cast hd
    have hprod0 : 0 ≤ ∏ n, qOf (constructionLaw2 hc hev) ω n ^ p.1 n := le_trans
      (by positivity) hP
    have h3 : Xm' ^ 2 ≤ (p.2 : ℝ) * ∏ n, qOf (constructionLaw2 hc hev) ω n ^ p.1 n := by
      nlinarith
    -- `X₀⁻ ≥ X₀/2`, so `X₀⁻² > X₀ + 1`
    have hbig := X0_ge_big (hc := hc)
    have hXm2 : (X₀ : ℝ) / 2 ≤ Xm' := by
      have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
      have h4 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
      simp only [Xm', Xm]; linarith
    nlinarith
  -- a non-zero vector of degree `≤ 1` is a unit vector
  obtain ⟨n, hn⟩ : ∃ n, p.1 n ≠ 0 := by
    by_contra h; push_neg at h; exact hp0 (funext h)
  have hle : ∀ m, p.1 m ≤ ∑ k, p.1 k := fun m =>
    Finset.single_le_sum (f := p.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have hn1 : p.1 n = 1 := by have := hle n; omega
  refine ⟨n, funext fun m => ?_⟩
  by_cases hmn : m = n
  · subst hmn; simp [hn1]
  · rw [Pi.single_eq_of_ne hmn]
    have h2 : p.1 m + p.1 n ≤ ∑ k, p.1 k := by
      rw [← Finset.sum_pair hmn]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

/-- Distinct unit vectors are linearly independent: `rank S = |S|`. -/
lemma rank_eq_card_of_unit {N : ℕ} (S : Finset (Fin N → ℕ))
    (hS : ∀ v ∈ S, ∃ n, v = Pi.single n 1) : Covers.rank S = S.card := by
  classical
  set f : Fin N → (Fin N → ℕ) := fun n => Pi.single n 1 with hf
  have hfi : Function.Injective f := by
    intro n n' h
    have := congrFun h n
    simp only [hf, Pi.single_apply] at this
    by_contra hne
    rw [if_pos trivial, if_neg hne] at this
    exact one_ne_zero this
  have hli : LinearIndepOn ℚ Covers.vq (range f) := by
    rw [linearIndepOn_range_iff hfi]
    have e : Covers.vq ∘ f = ⇑(Pi.basisFun ℚ (Fin N)) := by
      funext n i
      simp only [Function.comp_apply, hf, Covers.vq, Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    exact (Pi.basisFun ℚ (Fin N)).linearIndependent
  have hsub : (S : Set (Fin N → ℕ)) ⊆ range f := by
    intro v hv
    obtain ⟨n, rfl⟩ := hS v hv
    exact ⟨n, rfl⟩
  have hB : Covers.IsBasisOf S S := ⟨subset_rfl, hli.mono hsub, le_rfl⟩
  exact Covers.rank_eq_card hB

include hc in
lemma low_rank_eq_card {N D Dmax : ℕ} (ω : JitterΩ) {J : Set ℝ}
    (hJ : J ⊆ Iic ((X₀ : ℝ) + 1)) :
    Covers.rank (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax J) =
    (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax J).card :=
  rank_eq_card_of_unit _ fun _ hv => low_vec_unit hc hev ω hJ hv

/-- **Proposition 6.11 at the lowest height `z_0 = X₀/2`** for the cluster event `E_cl(z_0)`, on
a good event `G` (§6, proof of Proposition 6.11, the case `2z + 1 < (X₀⁻)²`): the window sets
have capacity `0`, so Theorem 6.23(a) is not needed, and Theorem R (`prop_6_11_model`, with the
skeleton bound `skeletonBound_construction`) gives the bound. The residual inputs are the named
hypotheses of Appendix A at `z_0`: (S3)(d) (`S3dHyp`) and the multi-run skeleton bound
(`MultiRunSkeletonBound`), exactly as in `eclW_fail`. -/
theorem eclW_fail_zero (G : Set JitterΩ)
    (hS3 : S3dHyp hc hev (NpZ (zH X₀ 0)) (DmaxZ (zH X₀ 0)) (smaxZ (zH X₀ 0))
      (AtopZ X₀ (zH X₀ 0)))
    (hmulti : ∀ k ∈ gridW X₀ 0, MultiRunSkeletonBound jitterMeasure
      (G ∩ goodLt θ X₀ (smaxZ (zH X₀ 0))) (r0At (zH X₀ 0)) (1 + 1 / Real.log X₀)
      (2 * gridDelta (zH X₀ 0)) (AtopZ X₀ (zH X₀ 0)) (EuZ X₀ (zH X₀ 0))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ 0)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ 0)) (DmaxZ (zH X₀ 0))
        (gwin (zH X₀ 0) k)) E l)) :
    jitterMeasure ((EclW hc hev 0)ᶜ ∩ G) ≤
      ENNReal.ofReal (Real.log (zH X₀ 0) ^ (-2 : ℝ)) := by
  classical
  obtain ⟨hz, hz1, hL, hℓ⟩ := z0_facts hc
  set z := zH X₀ 0 with hzdef
  set L := Real.log z with hLdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hz2 : 2 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hδ : 0 < gridDelta z := gridDelta_pos hz1
  set smax := smaxZ z
  set B := goodLt θ X₀ smax
  have hBm : MeasurableSet B := jitterFiltration.le smax _ (good_meas hc smax)
  set GoodM := toMeasurable jitterMeasure (G ∩ B) ∩ B
  have hGM : MeasurableSet GoodM := (measurableSet_toMeasurable _ _).inter hBm
  have hres : jitterMeasure.restrict GoodM = jitterMeasure.restrict (G ∩ B) :=
    restrict_hull_inter jitterMeasure G hBm
  -- `Eu ≤ A_top`, from (S3)(d) at `u = 0`
  have hEuA : EuZ X₀ z ≤ AtopZ X₀ z := by
    have h := hS3 (fun _ => 0) 0 (Nat.zero_le _) (by simp [goodLt])
    simpa [EuZ] using h
  have hE1 : 1 ≤ EuZ X₀ z := by
    unfold EuZ tailSum
    have hX1' : 1 ≤ DmaxZ z := by
      unfold DmaxZ; exact Nat.one_le_iff_ne_zero.mpr (by
        rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
    have hmem : 1 ∈ Nat.smoothNumbersUpTo (DmaxZ z) X₀ := by
      rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨hX1', ?_⟩
      rw [Nat.mem_smoothNumbers]; simp
    have := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ))⁻¹)
      (fun d _ => by positivity) hmem
    simpa using this
  have hA0 : 0 ≤ AtopZ X₀ z := by linarith
  -- `r₀`
  have hr0lo : L / (3 * Real.log L) + 3 ≤ (r0At z : ℝ) := by
    unfold r0At; push_cast
    have := Nat.le_ceil (L / (3 * Real.log L))
    linarith
  have hr0hi : (r0At z : ℝ) ≤ L / (3 * Real.log L) + 4 := by
    unfold r0At; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ L / (3 * Real.log L) by positivity)
    linarith
  have hr1 : 1 ≤ r0At z := by
    have h0 : 0 ≤ L / (3 * Real.log L) := by positivity
    exact_mod_cast (show (1 : ℝ) ≤ r0At z by linarith)
  have hu : 1 + (r0At z : ℝ) / X₀ ≤ 2 * L := by
    have h1 : (r0At z : ℝ) / X₀ ≤ r0At z := div_le_self (Nat.cast_nonneg _) hX1.le
    have h2 : L / (3 * Real.log L) ≤ L / 54 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
    linarith
  -- `#W`
  have hW : ((gridW X₀ 0).card : ℝ) ≤ 2 * z / (4 * L ^ (-6 : ℝ)) + 1 := by
    unfold gridW
    rw [← hzdef, Int.card_Icc]
    set c1 := ⌈z / gridDelta z⌉
    set c2 := ⌈2 * z / gridDelta z⌉
    have h1 : z / gridDelta z ≤ c1 := Int.le_ceil _
    have h2 : (c2 : ℝ) < 2 * z / gridDelta z + 1 := Int.ceil_lt_add_one _
    have e : 2 * z / (4 * L ^ (-6 : ℝ)) = z / gridDelta z := by
      unfold gridDelta
      rw [Real.rpow_neg hL0.le]
      have : L ^ (6 : ℝ) = L ^ (6 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
      rw [this]; field_simp; ring
    rw [e]
    rcases le_or_gt c1 (c2 - 1 + 1) with h | h
    · have : (((c2 - 1 + 1 - c1).toNat : ℕ) : ℝ) = ((c2 - 1 + 1 - c1 : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [this]; push_cast
      have : 2 * z / gridDelta z = 2 * (z / gridDelta z) := by ring
      linarith
    · rw [Int.toNat_of_nonpos (by omega)]; simp; positivity
  -- `A_top ≤ A_R e^{2.2/Λ}`
  have hsmall := capH_X0_small (hc := hc)
  have hH2z : capH X₀ (2 * z) ≤ 0.0001 * (2 * z) := by
    rw [hz, show 2 * ((X₀ : ℝ) / 2) = X₀ by ring]
    rw [div_le_iff₀ (by linarith)] at hsmall
    linarith
  have hlt := RankFull.log_top_le (by linarith) (capH_nonneg _ _) hH2z
  have hlt0 : 0 ≤ Real.log (2 * z + capH X₀ (2 * z)) :=
    Real.log_nonneg (by linarith [capH_nonneg X₀ (2 * z)])
  have hAtop : AtopZ X₀ z ≤ 1.8 * (L + 4) * Real.exp (2.2 / Real.log X₀) :=
    RankFull.A_top_le hc.hX hL0.le hlt0 hlt (by linarith)
  -- `2δ₁ = 4 L^{-6}`
  have h2δ : 2 * gridDelta z = 4 * L ^ (-6 : ℝ) := by
    unfold gridDelta
    rw [Real.rpow_neg hL0.le]
    have : L ^ (6 : ℝ) = L ^ (6 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
    rw [this]; ring
  -- the windows lie in `(-∞, X₀ + 1]`
  have hwin : ∀ k ∈ gridW X₀ 0, gwin z k ⊆ Iic ((X₀ : ℝ) + 1) := by
    intro k hk
    have h := gridWin_le hz2 ((mem_gridW hδ).mp hk).2
    exact h.trans (Iic_subset_Iic.mpr (by rw [hz]; linarith))
  have hmain := prop_6_11_model jitterMeasure hGM (gridW X₀ 0)
    (fun ω => decOf (N := NpZ z) (constructionLaw2 hc hev) ω) (qOf (constructionLaw2 hc hev))
    (hq1_dec hc hev) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z) (fun k => k * gridDelta z)
    (δ := 2 * gridDelta z) (fun k => gridWin_sub z k) (gridDelta_two_lt hz2) (r0At z)
    (c := cAt X₀ z) (Q := Real.sqrt (cAt X₀ z)) (M₁ := M1cl X₀ z) (L := L) (z := z)
    (θ := 1 + 1 / Real.log X₀) (A := AtopZ X₀ z) (Eu := EuZ X₀ z) (A_R := 1.8 * (L + 4))
    (b := Real.exp (2.2 / Real.log X₀)) (X₀ := (X₀ : ℝ)) (H := capH X₀)
    (slotHyp_capH hX0 hc.hX) rfl (by linarith) (by linarith)
    (by rw [hLdef, Real.exp_log (by linarith)]) (by positivity) (Real.exp_pos _)
    (theta_ab (hc := hc) (z := (X₀ : ℝ)) le_rfl) (by positivity) le_rfl hu hr0lo hW
    (by linarith) hEuA hAtop
    (fun k E l => meas_skelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k E l)
    (fun k _ => meas_rankFullCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k)
    (fun k hk => by
      rw [← h2δ]
      have h := skeletonBound_construction hc hev hGM smax Set.inter_subset_right
        (r₀ := r0At z) hr1 (Jw := gwin z k) measurableSet_Ico (gridWin_sub z k)
        (by linarith) (V := 2 * z + 1)
        (gridWin_le hz2 ((mem_gridW hδ).mp hk).2) le_rfl (DpZ X₀ z) (DmaxZ z)
        hA0 hEuA hS3 (by
          have := hmulti k hk
          unfold MultiRunSkeletonBound at this ⊢
          intro E hE' l hl hl'
          rw [hres]; exact this E hE' l hl hl')
      exact h)
    (by
      -- the capacity-`0` case: `rank S(J) = |S(J)|`, so the event is empty
      refine le_of_eq_of_le ?_ (zero_le _)
      refine measure_mono_null (fun ω hω => ?_) measure_empty
      obtain ⟨⟨k, hk, hlt, hle⟩, -⟩ := hω
      have hr := low_rank_eq_card hc hev (N := NpZ z) (D := DpZ X₀ z) (Dmax := DmaxZ z) ω
        (hwin k hk)
      rw [hr] at hlt
      have hφ : 0 ≤ Covers.phi (cAt X₀ z) (Real.sqrt (cAt X₀ z)) (r0At z) := by
        unfold Covers.phi cAt; positivity
      have : ((windowVecs (decOf (N := NpZ z) (constructionLaw2 hc hev) ω)
          (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z k)).card : ℝ) <
          r0At z := by exact_mod_cast hlt
      linarith)
  have hcompl : (EclW hc hev 0)ᶜ = {ω | ∃ k ∈ gridW X₀ 0, M1cl X₀ z <
      ((windowElems (decOf (N := NpZ z) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z k)).card : ℝ)} := by
    ext ω
    simp only [EclW, mem_compl_iff, mem_setOf_eq, not_forall, not_le, exists_prop]
    exact Iff.rfl
  have hnull : jitterMeasure Bᶜ = 0 := good_compl_null hc smax
  calc jitterMeasure ((EclW hc hev 0)ᶜ ∩ G)
      ≤ jitterMeasure ((EclW hc hev 0)ᶜ ∩ (G ∩ B)) + jitterMeasure Bᶜ := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        intro ω ⟨h1, h2⟩
        by_cases hb : ω ∈ B
        · left; exact ⟨h1, h2, hb⟩
        · right; exact hb
    _ = jitterMeasure ((EclW hc hev 0)ᶜ ∩ (G ∩ B)) := by rw [hnull, add_zero]
    _ ≤ jitterMeasure ((EclW hc hev 0)ᶜ ∩ GoodM) :=
        measure_mono (Set.inter_subset_inter_right _ fun ω hω =>
          ⟨subset_toMeasurable _ _ hω, hω.2⟩)
    _ ≤ _ := by
        rw [hcompl]
        exact hmain

/-- **The field `cluster0` of `QueueInputs`** (Proposition 6.11 at `z = X₀/2` on the good event
`Good(< t(E1(z_0)))`), from (S3)(d) and the multi-run skeleton bound at `z_0`. -/
theorem cluster0_of (D : Sec5Family)
    (hS3 : S3dHyp hc hev (NpZ (zH X₀ 0)) (DmaxZ (zH X₀ 0)) (smaxZ (zH X₀ 0))
      (AtopZ X₀ (zH X₀ 0)))
    (hmulti : ∀ k ∈ gridW X₀ 0, MultiRunSkeletonBound jitterMeasure
      (G0 θ X₀ D (tE1 X₀ 0) ∩ goodLt θ X₀ (smaxZ (zH X₀ 0))) (r0At (zH X₀ 0))
      (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ 0)) (AtopZ X₀ (zH X₀ 0)) (EuZ X₀ (zH X₀ 0))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ 0)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ 0)) (DmaxZ (zH X₀ 0))
        (gwin (zH X₀ 0) k)) E l)) :
    jitterMeasure ((E1ev θ X₀ 0)ᶜ ∩ G0 θ X₀ D (tE1 X₀ 0)) ≤
      ENNReal.ofReal (Real.log (zH X₀ 0) ^ (-2 : ℝ)) := by
  have e : E1ev θ X₀ 0 = EclW hc hev 0 := by
    unfold E1ev; rw [dif_pos ⟨hc, hev⟩]
  rw [e]
  exact eclW_fail_zero hc hev _ hS3 hmulti

end Low

end Queue6
