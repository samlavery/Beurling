module

public import RequestProject.Beurling.Noise.KRWidthReal
public import RequestProject.BSCert.CaplMono

/-!
# `H` is piecewise smooth (§5.1): `CapHDiff`

The jitter width `H = max(H_std, M̄₁²)` of Theorem 6.23 is differentiable at every `y > X₀` off a
countable set (`KR.WidthReal.CapHDiff`, §5.1 "`H` is piecewise smooth").

* `countable_isolated_zeros` : the zeros of `h` that are isolated are countably many;
* `max_diffAt`, `max_diff_off` : `max f g` is differentiable wherever `f, g` are, except at the
  points where `f = g` with `f' ≠ g'`; these are isolated zeros of `f - g`, so countably many;
* `G_comp_diff` : `s ↦ G(Λ(s), s)` is differentiable where `2 log Λ + s > 0`, `A > 0`,
  `Λ - A - 1 > 0` (the ranges of `Λ ≥ 10⁸`, `-log Λ ≤ s ≤ 6`, `CaplMono`);
* `gam_diff` : `γ(s)` is differentiable off `{s_H, s_H + 1, -log 10⁸}`;
* `capHDiff` : `CapHDiff X₀` for `log X₀ ≥ 10⁸`.
-/

@[expose] public section

open Real Set Filter Topology BSCert.Capl CaplLink

namespace CapHDiffProof

/-! ### Maxima of differentiable functions -/

/-- The isolated zeros of a real function are countably many. -/
lemma countable_isolated_zeros {h : ℝ → ℝ} {T : Set ℝ} (hT0 : ∀ z ∈ T, h z = 0)
    (hiso : ∀ z ∈ T, ∀ᶠ t in 𝓝[≠] z, h t ≠ 0) : T.Countable := by
  have key : ∀ z ∈ T, ∃ p : ℚ × ℚ, (p.1 : ℝ) < z ∧ z < p.2 ∧
      ∀ t ∈ T, (p.1 : ℝ) < t → t < p.2 → t = z := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hiso z hz)
    obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show z - ε < z by linarith)
    obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show z < z + ε by linarith)
    refine ⟨(q1, q2), hq1', hq2, fun t ht h1 h2 => ?_⟩
    by_contra hne
    have hmem : t ∈ Metric.ball z ε ∩ {z}ᶜ :=
      ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hne⟩
    exact hball hmem (hT0 t ht)
  choose! p hp using key
  refine MapsTo.countable_of_injOn (f := p) (t := univ) (mapsTo_univ _ _) ?_
    Set.countable_univ
  intro z1 h1 z2 h2 h12
  obtain ⟨a1, b1, c1⟩ := hp z1 h1
  obtain ⟨a2, b2, -⟩ := hp z2 h2
  rw [← h12] at a2 b2
  exact (c1 z2 h2 a2 b2).symm

/-- `max f g` is differentiable at `y` if `f, g` are, unless `f y = g y` and `f' y ≠ g' y`. -/
lemma max_diffAt {f g : ℝ → ℝ} {y : ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (h : ¬ (f y = g y ∧ deriv f y ≠ deriv g y)) :
    DifferentiableAt ℝ (fun t => max (f t) (g t)) y := by
  rcases lt_trichotomy (f y) (g y) with hlt | heq | hgt
  · refine hg.congr_of_eventuallyEq ?_
    filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt hlt] with t ht
    exact max_eq_right ht.le
  · have hd : deriv f y = deriv g y := by
      by_contra hne; exact h ⟨heq, hne⟩
    set k : ℝ → ℝ := fun t => g t - f t with hk
    have hk' : HasDerivAt k 0 y := by
      have := hg.hasDerivAt.sub hf.hasDerivAt
      rw [hd, sub_self] at this
      exact this
    have hk0 : k y = 0 := by simp [hk, heq]
    have hm : HasDerivAt (fun t => max 0 (k t)) 0 y := by
      rw [hasDerivAt_iff_isLittleO] at hk' ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hk'
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simp only [hk0, smul_zero, sub_zero, max_self, one_mul, Real.norm_eq_abs]
      rcases le_total 0 (k t) with h0 | h0
      · rw [max_eq_right h0]
      · rw [max_eq_left h0, abs_zero]; exact abs_nonneg _
    refine (hf.add hm.differentiableAt).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show max (f t) (g t) = f t + max 0 (k t)
    rw [hk]
    simp only
    rw [← max_add_add_left]
    simp
  · refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt hgt] with t ht
    exact max_eq_left ht.le

/-- **`max f g` is differentiable off a countable set** on `U` if `f`, `g` are. -/
lemma max_diff_off {f g : ℝ → ℝ} {U Sf Sg : Set ℝ} (hSf : Sf.Countable) (hSg : Sg.Countable)
    (hf : ∀ y ∈ U, y ∉ Sf → DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ U, y ∉ Sg → DifferentiableAt ℝ g y) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ y ∈ U, y ∉ S →
      DifferentiableAt ℝ (fun t => max (f t) (g t)) y := by
  classical
  set T := {z | z ∈ U ∧ z ∉ Sf ∧ z ∉ Sg ∧ f z = g z ∧ deriv f z ≠ deriv g z} with hT
  have hTc : T.Countable := by
    refine countable_isolated_zeros (h := fun t => f t - g t) (fun z hz => by
      simp [hz.2.2.2.1]) (fun z hz => ?_)
    obtain ⟨hzU, hzf, hzg, heq, hne⟩ := hz
    have hd := (hf z hzU hzf).hasDerivAt.sub (hg z hzU hzg).hasDerivAt
    have := hd.eventually_ne (c := 0) (sub_ne_zero.mpr hne)
    filter_upwards [this] with t ht
    simpa [heq] using ht
  refine ⟨Sf ∪ Sg ∪ T, (hSf.union hSg).union hTc, fun y hy hyS => ?_⟩
  simp only [mem_union, not_or] at hyS
  obtain ⟨⟨hyf, hyg⟩, hyT⟩ := hyS
  exact max_diffAt (hf y hy hyf) (hg y hy hyg) fun h => hyT ⟨hy, hyf, hyg, h.1, h.2⟩

/-! ### `γ` -/

/-- `s ↦ G(Λ(s), s)` is differentiable at `s` in the range of `G`. -/
lemma G_comp_diff {L : ℝ → ℝ} {s : ℝ} (hL : DifferentiableAt ℝ L s) (hL0 : 0 < L s)
    (hd : 0 < 2 * Real.log (L s) + s) (hA : 0 < A (L s) s) (hB : 0 < L s - A (L s) s - 1) :
    DifferentiableAt ℝ (fun s => G (L s) s) s := by
  have hlogL : DifferentiableAt ℝ (fun s => Real.log (L s)) s := hL.log hL0.ne'
  have hden : DifferentiableAt ℝ (fun s => 2 * Real.log (L s) + s) s :=
    (hlogL.const_mul 2).add differentiableAt_id
  have hnum : DifferentiableAt ℝ (fun s => 2 * L s ^ 3 * Real.exp (2 * s)) s :=
    ((hL.pow 3).const_mul 2).mul ((differentiableAt_id.const_mul 2).exp)
  have harg0 : 0 < 2 * L s ^ 3 * Real.exp (2 * s) / (2 * Real.log (L s) + s) := by positivity
  have hAd : DifferentiableAt ℝ (fun s => A (L s) s) s := by
    unfold A
    exact (hnum.div hden hd.ne').log harg0.ne'
  have h1 : DifferentiableAt ℝ (fun s => Real.sqrt (A (L s) s * (A (L s) s + 1))) s :=
    (hAd.mul (hAd.add_const 1)).sqrt (mul_pos hA (by linarith)).ne'
  have h2 : DifferentiableAt ℝ (fun s => Real.sqrt (L s - A (L s) s - 1)) s :=
    ((hL.sub hAd).sub_const 1).sqrt hB.ne'
  unfold G
  exact ((h1.const_mul 2).mul ((differentiableAt_id.div_const 2).exp)).div h2
    (Real.sqrt_ne_zero'.mpr hB)

/-- The range facts of `G` for `Λ ≥ 10⁸`, `-log Λ ≤ s ≤ 6` (`CaplMono`). -/
lemma G_range {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs6 : s ≤ 6) :
    0 < Λ ∧ 0 < 2 * Real.log Λ + s ∧ 0 < A Λ s ∧ 0 < Λ - A Λ s - 1 := by
  have hL := log_ge_18 hΛ
  have h6 := A_ge_six hΛ hs
  have hlin := A_le_lin hΛ hs hs6
  have hll := lin_log_lt hΛ
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma log_e8_pos : 0 < Real.log (100000000 : ℝ) := Real.log_pos (by norm_num)

/-- `γ* = 1.3 G(Λ_s, s)` is differentiable at `s ≤ 6`, `s ≠ -log 10⁸`. -/
lemma gstar_diff {s : ℝ} (hs6 : s ≤ 6) (hs : s ≠ -Real.log 100000000) :
    DifferentiableAt ℝ gstar s := by
  have hlog := log_e8_pos
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · -- `Λ_s = e^{-s}`
    have hev : ∀ᶠ t in 𝓝 s, gstar t = 1.3 * G (Real.exp (-t)) t := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      unfold gstar LamS
      rw [max_eq_right]
      have : Real.log 100000000 < -t := by simp only [mem_Iio] at ht; linarith
      have := Real.exp_lt_exp.mpr this
      rw [Real.exp_log (by norm_num)] at this
      exact this.le
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hE : 100000000 ≤ Real.exp (-s) := by
      have := Real.exp_le_exp.mpr (show Real.log 100000000 ≤ -s by linarith)
      rwa [Real.exp_log (by norm_num)] at this
    obtain ⟨h0, hd, hA, hB⟩ := G_range hE (by rw [Real.log_exp, neg_neg]) hs6
    exact (G_comp_diff (L := fun t => Real.exp (-t)) (differentiableAt_id.neg.exp) h0 hd hA
      hB).const_mul 1.3
  · -- `Λ_s = 10⁸`
    have hev : ∀ᶠ t in 𝓝 s, gstar t = 1.3 * G 100000000 t := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      unfold gstar LamS
      rw [max_eq_left]
      have : -t < Real.log 100000000 := by simp only [mem_Ioi] at ht; linarith
      have := Real.exp_lt_exp.mpr this
      rw [Real.exp_log (by norm_num)] at this
      exact this.le
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    obtain ⟨h0, hd, hA, hB⟩ := G_range (Λ := 100000000) le_rfl hgt.le hs6
    exact (G_comp_diff (L := fun _ => (100000000 : ℝ)) (differentiableAt_const _) h0 hd hA
      hB).const_mul 1.3

/-- **`γ` is differentiable off `{s_H, s_H + 1, -log 10⁸}`** (for `s_H < 6`). -/
lemma gam_diff {sH s : ℝ} (hsH : sH < 6) (h1 : s ≠ sH) (h2 : s ≠ sH + 1)
    (h3 : s ≠ -Real.log 100000000) : DifferentiableAt ℝ (gam sH) s := by
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · have hev : ∀ᶠ t in 𝓝 s, gam sH t = gstar t := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      unfold gam; rw [if_pos (le_of_lt ht)]
    exact (gstar_diff (by linarith) h3).congr_of_eventuallyEq hev
  · rcases lt_or_gt_of_ne h2 with hlt2 | hgt2
    · have hev : ∀ᶠ t in 𝓝 s, gam sH t = gstar sH + (7.5 - gstar sH) * (t - sH) := by
        filter_upwards [Ioo_mem_nhds hgt hlt2] with t ht
        unfold gam; rw [if_neg (not_le.mpr ht.1), if_pos ht.2.le]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact (differentiableAt_const _).add ((differentiableAt_id.sub_const _).const_mul _)
    · have hev : ∀ᶠ t in 𝓝 s, gam sH t = 7.5 := by
        filter_upwards [Ioi_mem_nhds hgt2] with t ht
        have ht' : sH + 1 < t := ht
        unfold gam; rw [if_neg (by linarith), if_neg (not_le.mpr ht')]
      exact (differentiableAt_const _).congr_of_eventuallyEq hev

/-! ### `log c`, `M̄₁`, `H` -/

/-- `log c` is differentiable off a countable set of `s`. -/
lemma logc_diff_off (Λ : ℝ) : ∃ C : Set ℝ, C.Countable ∧ ∀ s, s ∉ C →
    DifferentiableAt ℝ (logc sHroot Λ) s := by
  have hsH := sHroot_mem
  obtain ⟨S, hS, hdiff⟩ := max_diff_off (U := univ) (Sf := ∅)
    (Sg := {sHroot, sHroot + 1, -Real.log 100000000})
    (f := fun s => 4 * (2 * Real.log Λ + s) ^ 2 - Real.log 4) (g := fun s => gam sHroot s * Λ)
    countable_empty (Set.toFinite _).countable
    (fun y _ _ => (((differentiableAt_const _).add differentiableAt_id).pow 2 |>.const_mul 4)
      |>.sub_const _)
    (fun y _ hy => by
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy
      exact (gam_diff (by linarith [hsH.2]) hy.1 hy.2.1 hy.2.2).mul_const _)
  exact ⟨S, hS, fun s hs => hdiff s (mem_univ _) hs⟩

/-- `M̄₁` is differentiable in `s` where `log c` is and `2 log Λ + s ≠ 0`. -/
lemma Mbar1_diff {Λ s : ℝ} (hc : DifferentiableAt ℝ (logc sHroot Λ) s)
    (hl : 2 * Real.log Λ + s ≠ 0) : DifferentiableAt ℝ (Mbar1 sHroot Λ) s := by
  have hr : DifferentiableAt ℝ (rbar0 Λ) s := by
    unfold rbar0
    have hd : DifferentiableAt ℝ (fun s => 2 * Real.log Λ + s) s :=
      (differentiableAt_const _).add differentiableAt_id
    exact ((hd.exp).div (hd.const_mul 3) (mul_ne_zero (by norm_num) hl)).add_const 4
  have hce : DifferentiableAt ℝ (fun s => Real.exp (logc sHroot Λ s)) s := hc.exp
  have hsq : DifferentiableAt ℝ (fun s => Real.sqrt (Real.exp (logc sHroot Λ s))) s :=
    hce.sqrt (Real.exp_pos _).ne'
  unfold Mbar1
  exact ((hr.add ((hce.add (hr.mul hsq)).add ((hr.mul (hr.add_const 1)).div_const 2))).add_const
    1)

/-- **`H` is piecewise smooth** (§5.1; `H = max(H_std, M̄₁²)` of Theorem 6.23): for
`log X₀ ≥ 10⁸`, `H` is differentiable at every `y > X₀` off a countable set. -/
theorem capHDiff {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : KR.WidthReal.CapHDiff X₀ := by
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra h; push_neg at h
    have : (X₀ : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hX; norm_num at hX
  have hlogpos : ∀ y : ℝ, (X₀ : ℝ) < y → 1 < Real.log y := fun y hy => by
    have := Real.log_le_log hX0 hy.le; linarith
  obtain ⟨C, hC, hlogc⟩ := logc_diff_off (Real.log X₀)
  set Λ₀ := Real.log (Real.log (X₀ : ℝ)) with hΛ₀
  set S2 := {x : ℝ | (X₀ : ℝ) < x ∧ capS X₀ x ∈ C} with hS2
  have hS2c : S2.Countable := by
    refine (hC.image fun s => Real.exp (Real.exp (s + 2 * Λ₀))).mono fun x hx => ?_
    obtain ⟨hx1, hxC⟩ := hx
    refine ⟨capS X₀ x, hxC, ?_⟩
    have hl := hlogpos x hx1
    have e := ell_eq (X₀ : ℝ) x
    show Real.exp (Real.exp (capS X₀ x + 2 * Λ₀)) = x
    rw [show capS (X₀ : ℝ) x + 2 * Λ₀ = Real.log (Real.log x) by rw [hΛ₀]; linarith,
      Real.exp_log (by linarith), Real.exp_log (by linarith)]
  have hcapS : ∀ y : ℝ, (X₀ : ℝ) < y →
      DifferentiableAt ℝ (fun x => capS (X₀ : ℝ) x) y := fun y hy => by
    unfold capS
    have hy0 : 0 < y := by linarith
    exact ((Real.differentiableAt_log hy0.ne').log (by linarith [hlogpos y hy])).sub_const _
  obtain ⟨S, hS, hdiff⟩ := max_diff_off (U := Ioi (X₀ : ℝ)) (Sf := ∅) (Sg := S2)
    (f := fun x => Real.exp (8 * Real.log (Real.log x) ^ 2))
    (g := fun x => capM1 (X₀ : ℝ) x ^ 2) countable_empty hS2c
    (fun y hy _ => by
      have hy' : (X₀ : ℝ) < y := hy
      have hy0 : 0 < y := by linarith
      exact ((((Real.differentiableAt_log hy0.ne').log
        (by linarith [hlogpos y hy'])).pow 2).const_mul 8).exp)
    (fun y hy hyS => by
      have hy' : (X₀ : ℝ) < y := hy
      have hyC : capS (X₀ : ℝ) y ∉ C := fun h => hyS ⟨hy', h⟩
      have hl : 2 * Real.log (Real.log (X₀ : ℝ)) + capS (X₀ : ℝ) y ≠ 0 := by
        rw [ell_eq]
        exact (Real.log_pos (hlogpos y hy')).ne'
      have hM := (Mbar1_diff (hlogc _ hyC) hl).comp y (hcapS y hy')
      exact hM.pow 2)
  exact ⟨S, hS, fun y hy hyS => hdiff y hy hyS⟩

end CapHDiffProof
