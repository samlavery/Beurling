module

public import RequestProject.Beurling.Zeros48.Pieces

/-!
# Lemma 4.8(ii) for the realised system: `Lemma48PiecesCount` at every scale
-/

@[expose] public section

open Set MeasureTheory Complex Construction Target Rankin Absorbed Decomp Oscillation CaplLink
  GoodHeights DesignedZero QueueMono

namespace Zeros48

variable {θ : ℝ} {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

set_option maxHeartbeats 400000 in
/-- **Lemma 4.8(ii), the pieces of `D̂_{<a_k}`, for the realised system.** From the target
formula (6), the lag bound (13) on `[X₀, ∞)`, `X₀` even (so `X₀`-smooth), jitters in `[0, 1]` and
the realised primes forming a Beurling system: `Lemma48PiecesCount` holds at every scale `k`. -/
theorem lemma48PiecesCount_realised (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hXs : X₀ ∈ X₀.smoothNumbers) (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    (h : RealisedOK M (capH X₀) U)
    (hT : ∀ x, M.T x = target X₀ (kappaParam X₀) (countA (realisedA M (capH X₀) U))
      (absorbedDensityCap (θ / 2) (realisedA M (capH X₀) U) (fun n => solveU (θ / 2) n))
      (osc θ (designedAlpha (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (designedGamma (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (switchOn X₀)) x)
    (hlag : ∀ x ≥ (X₀ : ℝ),
      |(realisedSystem M (capH X₀) U).N x - M.T x| ≤ x ^ lagExponent θ)
    (k : ℕ) :
    Lemma48PiecesCount X₀ (heightScale θ kappa0Param (switchOn X₀ k))
      (earlyOf (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀) (realisedA M (capH X₀) U)
        (fun n => solveU (θ / 2) n)
        (designedAlpha (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (designedGamma (realisedSystem M (capH X₀) U) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) U) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (switchOn X₀) (constructionScale X₀) k) := by
  classical
  set P := realisedSystem M (capH X₀) U with hP
  set A := realisedA M (capH X₀) U with hA
  set u : ℝ → ℝ := fun n => solveU (θ / 2) n with hu
  set κ := kappaParam (X₀ : ℝ) with hκdef
  set xp := switchOn (X₀ : ℝ) with hxpdef
  set αd := designedAlpha P θ X₀ κ A u kappa0Param xp (constructionScale X₀) with hαd
  set γd := designedGamma P θ X₀ κ A u kappa0Param xp (constructionScale X₀) with hγd
  set R := osc θ αd γd xp with hR
  set rhoA := absorbedDensityCap (θ / 2) A u with hrhoA
  set ak := constructionScale (X₀ : ℝ) k with hak
  set xk := xp k with hxk
  set η := lagExponent θ with hη
  set D := lagOf P θ X₀ κ A u αd γd xp with hD
  -- numerical facts
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) < X₀ := one_lt_of_logX hX0 hX
  have h16 := two_pow_le_of_logX hX0 hX
  have hX10 : (10 : ℝ) ≤ X₀ := le_trans (by norm_num) h16
  obtain ⟨hXa, ha0, haxk, hxka⟩ := constructionScale_spec hX0 hX k
  have hκ0 : 0 < κ := kappaParam_pos (by linarith)
  have hκ1 : κ ≤ 1 := kappaParam_le_one hX1.le
  have hκge : 1 / (X₀ : ℝ) ≤ κ := by
    have := kappaParam_ge hX1.le
    rwa [Real.exp_neg, Real.exp_log (by linarith), inv_eq_one_div] at this
  have hsp : Spacing xp := switchOn_spacing _
  have hxp0 : ∀ j, 0 < xp j := fun j => by linarith [hsp.one_le_all j]
  have hx0k : xp 0 ≤ xk := switchOn_mono _ (Nat.zero_le k)
  have hxk0 : (X₀ : ℝ) ^ 2 ≤ Real.log xk := by
    rw [← log_switchOn_zero (X₀ : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hx0k
  have hX1a : (X₀ : ℝ) + 1 ≤ ak := by
    have h1 : 1 + (X₀ : ℝ) ^ 2 ≤ xk := by
      have := Real.add_one_le_exp ((X₀ : ℝ) ^ 2)
      have : xp 0 = Real.exp ((X₀ : ℝ) ^ 2) := rfl
      linarith
    nlinarith
  have hη0 : 0 ≤ η := by
    simp only [hη, lagExponent]
    exact div_nonneg (le_min (by linarith) (by linarith)) (by norm_num)
  have hη8 : η ≤ 1 / 8 := by
    simp only [hη, lagExponent]
    have := min_le_right θ (1 / 2 - θ)
    linarith
  -- the target below `X₀`, the absorbed set lies above `X₀`
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hAlarge : ∀ n ∈ A, (X₀ : ℝ) < n := fun n hn => by
    have := (realisedA_large h hU hX hTlow hn).2
    linarith
  -- the lag bound (13) and the lag as residual count minus continuous part
  have hDT : ∀ x, D x = P.N x - M.T x := fun x => by rw [hT x]; rfl
  have hDlag : ∀ x ≥ (X₀ : ℝ), |D x| ≤ x ^ η := fun x hx => by rw [hDT x]; exact hlag x hx
  have hDeq : ∀ x, 0 ≤ x → D x = ((residualLe h x).card : ℝ) - contPart X₀ κ rhoA R x :=
    fun x hx => lag_eq_residual_sub_cont h hXs hAlarge rhoA R hx
  have hcnt : ∀ x, 0 ≤ x → ((residualLe h x).card : ℝ) = D x + contPart X₀ κ rhoA R x :=
    fun x hx => by rw [hDeq x hx]; ring
  -- the oscillation
  have hΓpos : ∀ j, 0 < heightScale θ kappa0Param (xp j) := fun j =>
    heightScale_pos (by norm_num [kappa0Param]) (by
      have := hsp.one_le_all j
      have h2 : xp 0 ≤ xp j := switchOn_mono _ (Nat.zero_le j)
      have h3 : (1 : ℝ) < xp 0 := by
        show 1 < Real.exp ((X₀ : ℝ) ^ 2)
        exact Real.one_lt_exp_iff.mpr (by positivity)
      linarith)
  have hαb : ∀ j, |αd j| ≤ 2 := fun j => by
    have := designedAlpha_mem P θ X₀ κ A u kappa0Param xp (constructionScale X₀) hΓpos j
    rw [abs_of_nonneg (by linarith [this.1])]; exact this.2
  have hγb : ∀ j, |γd j| ≤ 2 * heightScale θ kappa0Param (xp j) := fun j => by
    have := designedGamma_mem P θ X₀ κ A u kappa0Param xp (constructionScale X₀)
      (fun j => (hΓpos j).le) j
    rw [abs_of_nonneg (by linarith [this.1, hΓpos j])]; exact this.2
  set L := ∑ j ∈ Finset.range k, oscLip θ (αd j) (γd j) (xp j) with hLdef
  have hL : L ≤ 1 / 100 :=
    sum_oscLip_switchOn_le (by linarith) (by linarith) hX10 hαb hγb k
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => oscLip_nonneg (hxp0 j)
  -- the hypotheses on `ρ̄_A` and `R` on `[X₀, a_k]`
  have hAfin : LocFin A := realisedA_locFin M (capH X₀) U
  set ρAF := rhoAF (θ / 2) A hAfin u ak with hρAF
  have hc : ContHyp X₀ ak rhoA R ρAF (oscPart θ αd γd xp k) (oscDeriv θ αd γd xp k) L := by
    refine ⟨fun v hv => ?_, measurable_rhoAF _ _ _ _ _, fun v hv => ?_, fun v hv => ?_,
      fun x hx => ?_, measurable_oscDeriv _ _ _ _ _, fun x hx => ?_,
      fun u' hu' v hv huv => ?_, fun u' hu' v hv huv => ?_⟩
    · exact absorbedDensityCap_eq_rhoAF (by linarith) (by linarith) hAfin
        (fun n hn => solveU_spec (by linarith) (by linarith [hAlarge n hn])) (by linarith [hv.1])
        hv.2
    · exact absorbedDensityCap_nonneg (by linarith [hv.1])
    · refine (absorbedDensityCap_le v).trans ?_
      have : (10 : ℝ) ^ 8 ≤ Real.log v :=
        hX.trans (Real.log_le_log (by linarith) hv.1)
      rw [div_le_one (by linarith)]; linarith
    · exact osc_eq_oscPart hsp (by linarith [hx.1]) (hx.2.trans haxk)
    · exact abs_oscDeriv_le (by linarith) hxp0 k (by linarith [hx.1])
    · exact oscPart_sub_eq_integral (by linarith) hxp0 k (by linarith [hu'.1]) huv
    · exact (le_abs_self _).trans (abs_oscPart_sub_le (by linarith) hxp0 k
        (by linarith [hu'.1]) huv)
  -- the residual elements lie above `X₀/2`
  have hres : ∀ e ∈ residual h, (X₀ : ℝ) / 2 ≤ P.val e := fun e he => by
    have h1 := residual_val_ge h hU hX hTlow hXs he
    have h2 := four_capH_le hX0 hX (le_refl (X₀ : ℝ))
    linarith
  have hcont0 : contPart X₀ κ rhoA R X₀ = 0 := contPart_self rhoA R
  -- the short-interval count of `ℬ`
  have hshort : ∀ y₁ y₂ : ℝ, (X₀ : ℝ) + 1 ≤ y₁ → y₁ ≤ y₂ → y₂ ≤ ak →
      (((residualLe h y₂).filter (fun e => y₁ ≤ P.val e)).card : ℝ) ≤
        y₂ ^ η + y₁ ^ η + 1.01 * (y₂ - y₁) + 1 := by
    intro y₁ y₂ hy₁ hy12 hy₂
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ = y₁ - 1 / 2 := ⟨_, rfl⟩
    have hy₀X : (X₀ : ℝ) ≤ y₀ := by linarith
    have hsub : (residualLe h y₂).filter (fun e => y₁ ≤ P.val e) ⊆
        residualLe h y₂ \ residualLe h y₀ := by
      intro e he
      simp only [Finset.mem_filter] at he
      rw [Finset.mem_sdiff]
      refine ⟨he.1, fun he' => ?_⟩
      simp only [residualLe, Finset.mem_filter, BeurlingSystem.mem_elems] at he'
      linarith [he'.1, he.2]
    have hmono := residualLe_mono h (show y₀ ≤ y₂ by linarith)
    have hc1 : (((residualLe h y₂).filter (fun e => y₁ ≤ P.val e)).card : ℝ) ≤
        ((residualLe h y₂).card : ℝ) - ((residualLe h y₀).card : ℝ) := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset hmono] at h1
      have h2 := Finset.card_le_card hmono
      have h3 : (((residualLe h y₂).filter (fun e => y₁ ≤ P.val e)).card : ℝ) ≤
          (((residualLe h y₂).card - (residualLe h y₀).card : ℕ) : ℝ) := by exact_mod_cast h1
      rwa [Nat.cast_sub h2] at h3
    rw [hcnt y₂ (by linarith), hcnt y₀ (by linarith)] at hc1
    have hdv := (abs_le.mp (hDlag y₂ (by linarith))).2
    have hdu := (abs_le.mp (hDlag y₀ hy₀X)).1
    have hcp := hc.contPart_sub_le (κ := κ) hX1.le hκ0 hκ1 hy₀X (by linarith) hy₂
    have hy₀η : y₀ ^ η ≤ y₁ ^ η := Real.rpow_le_rpow (by linarith) (by linarith) hη0
    have hL' : (1 + L) * (y₂ - y₀) ≤ 1.01 * (y₂ - y₁) + 0.51 := by
      rw [hy₀]; nlinarith
    linarith
  -- the residual elements in `[X, a_k]`, listed in order, and those below `X`
  set X : ℝ := (X₀ : ℝ) + 1 with hXdef
  set E' := (residualLe h ak).filter (fun e => X ≤ P.val e) with hE'
  set El := (residualLe h ak).filter (fun e => ¬ X ≤ P.val e) with hEl
  obtain ⟨m, n, hmono, hnE, hsum⟩ := exists_sorted_enum E' P.val
  obtain ⟨J, hJ1, hJ2⟩ := exists_dyadic (X := X) (a := ak) (by positivity) hX1a
  -- the density `T'_cont = 1 - ρ_det - ρ̄_A + R'` on `[X₀, a_k]`
  set gF : ℝ → ℝ := fun t => 1 - rhoDetF X₀ κ ak t - ρAF t + oscDeriv θ αd γd xp k t
    with hgF
  set c : ℝ := 3 / κ + 3 with hcdef
  have hgFm : Measurable gF :=
    ((measurable_const.sub (measurable_rhoDetF _ _ _)).sub (measurable_rhoAF _ _ _ _ _)).add
      (measurable_oscDeriv _ _ _ _ _)
  have hgFb : ∀ t ∈ Icc (X₀ : ℝ) ak, |gF t| ≤ c := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have e1 := rhoDet_eq_rhoDetF X₀ hκ0 ht0 ht.2
    have b1 := rhoDet_nonneg X₀ hκ0 ht0
    have b2 := rhoDet_le X₀ hκ0 hκ1 (by linarith [ht.1] : 1 ≤ t)
    have e2 := hc.rhoA_eq t ht
    have b3 := hc.rhoA_nonneg t ht
    have b4 := hc.rhoA_le t ht
    have b5 := abs_le.mp (hc.Rd_le t ht)
    have b6 : 0 ≤ 3 / κ := by positivity
    simp only [hgF]
    rw [← e1, ← e2, abs_le]
    constructor <;> linarith [b5.1, b5.2]
  have hc0 : 0 < c := by positivity
  have hc4 : c ≤ 4 * X₀ := by
    have h1 : 1 / κ ≤ X₀ := by
      rw [div_le_iff₀ hκ0]
      rw [div_le_iff₀ (by linarith)] at hκge
      linarith
    have h2 : 3 / κ = 3 * (1 / κ) := by ring
    linarith
  have hgFint : IntegrableOn gF (Ioc (X₀ : ℝ) ak) :=
    Measure.integrableOn_of_bounded (M := c) (by simp) hgFm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
        rw [Real.norm_eq_abs]; exact hgFb t ⟨ht.1.le, ht.2⟩)
  set Mb : ℝ := (X ^ η + 2) * ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) with hMb
  obtain ⟨-, hβα, hnum⟩ := lemma48_numerics hθ (X₀ := (X₀ : ℝ)) (a := ak) (xk := xk)
    (by linarith) hX hXa haxk hxka hxk0 hc0 hc4 hJ2
  have hcP : ∀ x : ℝ, 1 < x → x < X₀ → contPart X₀ κ rhoA R x = 0 := fun x _ hx => by
    simp only [contPart, if_pos hx]
  unfold Lemma48PiecesCount
  refine ⟨fun z => ∑ e ∈ El, ((P.val e : ℝ) : ℂ) ^ (-z), fun t => -gF (Real.exp t), m, J, X, η,
    Mb, c, Real.log X₀, Real.log ak, n, ?_, ?_, ?_, hη0, hη8, hmono, ?_, ?_, ?_, ?_, ?_, ?_,
    hc0, ?_, ?_, ?_, ?_⟩
  · -- `p` is measurable
    refine Finset.measurable_sum _ fun e _ => ?_
    exact (continuous_const.cpow continuous_neg (fun _ => Or.inl (by
      simp only [Complex.ofReal_re]; exact P.val_pos e))).measurable
  · exact (hgFm.comp Real.measurable_exp).neg
  · show (10 : ℝ) ^ 4 ≤ (X₀ : ℝ) + 1
    have : (10 : ℝ) ^ 4 ≤ 2 ^ 16 := by norm_num
    linarith only [h16, this]
  · -- the range of the residual elements
    intro i
    obtain ⟨e, he, hne⟩ := hnE i
    simp only [hE', Finset.mem_filter, residualLe, BeurlingSystem.mem_elems] at he
    rw [hne]
    exact ⟨he.2, he.1.1.trans hJ1⟩
  · -- the short-interval count
    intro y₁ y₂ hy₁ hy12
    have hcard : ((Finset.univ.filter (fun i => y₁ ≤ n i ∧ n i ≤ y₂)).card : ℝ) =
        ((E'.filter (fun e => y₁ ≤ P.val e ∧ P.val e ≤ y₂)).card : ℝ) := by
      rw [Finset.card_filter, Finset.card_filter]
      exact_mod_cast hsum (fun x => if y₁ ≤ x ∧ x ≤ y₂ then 1 else 0)
    rw [hcard]
    by_cases hya : y₁ ≤ ak
    · have hsub : E'.filter (fun e => y₁ ≤ P.val e ∧ P.val e ≤ y₂) ⊆
          (residualLe h (min y₂ ak)).filter (fun e => y₁ ≤ P.val e) := by
        intro e he
        simp only [hE', Finset.mem_filter, residualLe, BeurlingSystem.mem_elems] at he ⊢
        exact ⟨⟨le_min he.2.2 he.1.1.1, he.1.1.2⟩, he.2.1⟩
      have h1 := hshort y₁ (min y₂ ak) hy₁ (le_min hy12 hya) (min_le_right _ _)
      have h2 : ((E'.filter (fun e => y₁ ≤ P.val e ∧ P.val e ≤ y₂)).card : ℝ) ≤
          (((residualLe h (min y₂ ak)).filter (fun e => y₁ ≤ P.val e)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h3 : (min y₂ ak) ^ η ≤ y₂ ^ η :=
        Real.rpow_le_rpow (by linarith [le_min hy12 hya]) (min_le_left _ _) hη0
      have h4 : min y₂ ak ≤ y₂ := min_le_left _ _
      linarith
    · have hemp : E'.filter (fun e => y₁ ≤ P.val e ∧ P.val e ≤ y₂) = ∅ := by
        refine Finset.filter_false_of_mem fun e he => ?_
        simp only [hE', Finset.mem_filter, residualLe, BeurlingSystem.mem_elems] at he
        intro h'
        linarith [he.1.1, h'.1]
      rw [hemp, Finset.card_empty, Nat.cast_zero]
      have : 0 ≤ y₂ ^ η := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ y₁ ^ η := Real.rpow_nonneg (by linarith) _
      linarith
  · positivity
  · -- the bound for `p`
    intro z hz
    have hzr : 3 / 4 ≤ z.re := hz.1
    have hq : 0 < ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) := by positivity
    have hterm : ∀ e ∈ El, ‖((P.val e : ℝ) : ℂ) ^ (-z)‖ ≤ ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) := by
      intro e he
      simp only [hEl, Finset.mem_filter, residualLe, BeurlingSystem.mem_elems] at he
      have hv := hres e he.1.2
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (P.val_pos e), Complex.neg_re]
      calc P.val e ^ (-z.re) ≤ P.val e ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hv (by norm_num)
    have hsubX : El ⊆ residualLe h X := by
      intro e he
      simp only [hEl, Finset.mem_filter, residualLe, BeurlingSystem.mem_elems] at he ⊢
      exact ⟨by linarith [he.2], he.1.2⟩
    have hcardX : (El.card : ℝ) ≤ X ^ η + 2 := by
      have h1 : (El.card : ℝ) ≤ ((residualLe h X).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubX
      rw [hcnt X (by positivity)] at h1
      have h2 := (abs_le.mp (hDlag X (by simp only [hXdef]; linarith))).2
      have h3 := hc.contPart_sub_le (κ := κ) hX1.le hκ0 hκ1 le_rfl
        (by simp only [hXdef]; linarith) hX1a
      rw [hcont0] at h3
      have h4 : (1 + L) * (X - X₀) ≤ 2 := by simp only [hXdef]; nlinarith
      linarith
    calc ‖∑ e ∈ El, ((P.val e : ℝ) : ℂ) ^ (-z)‖
        ≤ ∑ e ∈ El, ‖((P.val e : ℝ) : ℂ) ^ (-z)‖ := norm_sum_le _ _
      _ ≤ ∑ _e ∈ El, ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) := Finset.sum_le_sum hterm
      _ = (El.card : ℝ) * ((X₀ : ℝ) / 2) ^ (-(3 / 4 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Mb := by simp only [hMb]; exact mul_le_mul_of_nonneg_right hcardX hq.le
  · exact Real.log_nonneg hX1.le
  · exact Real.log_le_log (by linarith) hXa
  · -- the bound for `w`
    intro t ht
    have h1 : (X₀ : ℝ) ≤ Real.exp t := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr ht.1
    have h2 : Real.exp t ≤ ak :=
      (Real.exp_le_exp.mpr ht.2).trans (Real.exp_log ha0).le
    rw [abs_neg]
    exact hgFb _ ⟨h1, h2⟩
  · exact hβα
  · -- the decomposition
    intro z hz
    have hz0 : 0 < z.re := by linarith [hz.1]
    have hprim := earlyNoise_primitive (g := gF) (C := contPart X₀ κ rhoA R) (c := X₀)
      hX1.le hXa hgFint hcP (fun x hx => hc.contPart_eq hX1.le hκ0 hκ1 hx) hz0
    set D' : ℝ → ℝ := fun x =>
      ∑ e ∈ residualLe h ak, (if P.val e ≤ x then (1 : ℝ) else 0) - contPart X₀ κ rhoA R x
      with hD'
    have hDD' : earlyNoise D ak = earlyNoise D' ak := by
      refine earlyNoise_congr ha0 fun x hx hxa => ?_
      rw [hDeq x hx.le, residualLe_eq_filter h hxa, Finset.card_filter]
      simp only [hD']
      push_cast
      rfl
    show earlyNoise D ak z = _
    rw [hDD', show D' = fun x => ∑ e ∈ residualLe h ak, (fun e x =>
        if P.val e ≤ x then (1 : ℝ) else 0) e x - contPart X₀ κ rhoA R x from rfl,
      earlyNoise_sum_sub _ _ _ ak z
        (fun e _ => (earlyNoise_step (P.one_le_val e) z).1) hprim.1, hprim.2,
      integral_cpow_eq_exp gF (by linarith) hXa z]
    have hsteps : ∑ e ∈ residualLe h ak,
        earlyNoise (fun x => if P.val e ≤ x then (1 : ℝ) else 0) ak z =
        ∑ e ∈ residualLe h ak, ((P.val e : ℝ) : ℂ) ^ (-z) := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [(earlyNoise_step (P.one_le_val e) z).2]
      simp only [residualLe, Finset.mem_filter, BeurlingSystem.mem_elems] at he
      rw [if_pos he.1]
    rw [hsteps, ← Finset.sum_filter_add_sum_filter_not (residualLe h ak)
      (fun e => X ≤ P.val e), ← hsum (fun x : ℝ => (x : ℂ) ^ (-z))]
    have hint : ∫ t in Icc (Real.log X₀) (Real.log ak),
        (((-gF (Real.exp t) : ℝ)) : ℂ) * cexp ((1 - z) * t) =
        -∫ t in Icc (Real.log X₀) (Real.log ak), ((gF (Real.exp t) : ℝ) : ℂ) *
          cexp ((1 - z) * t) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      push_cast; ring
    rw [hint]
    ring
  · exact hnum

end Zeros48

end
