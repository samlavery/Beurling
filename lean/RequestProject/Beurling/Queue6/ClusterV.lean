module

public import RequestProject.Beurling.Queue6.S3dV
public import RequestProject.Beurling.Model.Cluster0

/-!
# Proposition 6.11 with (S3)(d) and the skeleton bound proved (the cluster events E1)

The cluster event `E1(z_n) = E_cl(z_n)` fails on `Good(< t(E1(z_n)))` with probability at most
`(log z_n)^{-2}` (Proposition 6.11), with the parameters of Lemma A.6 and Theorem A.12:

* `A_top = AtopV X₀ z = 1.8 log(2z + 2) exp(2.21/Λ + 10⁻⁶)` (Lemma A.6 (S3)(d), the constant
  `1.8` of the Mertens product estimate), `A_top ≤ A_R b` with `A_R = 1.8 (log z + 0.7)
  ≤ 1.8 (log z + 4)` and `b = exp(2.21/Λ + 10⁻⁶)`, `θ e^{(3H(X₀)+2)/X₀} b ≤ 1.01`;
* the skeleton bound (Lemma A.5 + Theorem A.10, `skeletonBound_all`) for the position-cut law
  `truncLaw (constructionLaw2) (2z + 1)`, on the good event `Good(< t) ∩ G_{<s_max} ∩ S(z)`, where
  `S(z)` is the (S3)(d) event (`SV`); the window sets are those of the full law
  (`windowVecs_trunc`); on `Good(< t)` the event `S(z)` holds off `NiceEvᶜ` (`s3dV_sure`).

* `eclV_fail` : `n ≥ 1`, from `prop_6_11_window`; the only input is the Cover Bound
  (`CoverSkeletonBound`, Lemmas 6.17–6.19), with `A = A_top`;
* `eclV_fail_zero` : `n = 0` (`z = X₀/2`), from `prop_6_11_model` (capacity `0`); no input.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono RankFull RankFull.Config

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The numerics of `A_top` -/

section NumV

variable {hc : Cond θ X₀}
include hc

variable {z : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z)
include hz

lemma logV_le : Real.log (2 * z + 2) ≤ Real.log z + 0.7 := by
  have hXb := X0_ge_1e8 hc
  exact RankFull.log_top_le (by linarith) (by norm_num) (by linarith)

lemma logV_nonneg : 0 ≤ Real.log (2 * z + 2) := by
  have hXb := X0_ge_1e8 hc
  exact Real.log_nonneg (by linarith)

lemma logz_ge : 10 ^ 8 - 1 ≤ Real.log z := by
  have hX := hc.hX
  have hXb := X0_ge_1e8 hc
  have h1 : Real.log ((X₀ : ℝ) / 2) ≤ Real.log z := Real.log_le_log (by linarith) hz
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  linarith [Real.log_two_lt_d9]

omit hz in
lemma expV_le : Real.exp (2.21 / Real.log X₀ + 1e-6) ≤ 1.0002 := by
  have hX := hc.hX
  have hsmall : 2.21 / Real.log X₀ + 1e-6 ≤ 0.0001 := by
    have : 2.21 / Real.log X₀ ≤ 2.21 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hX
    norm_num at this ⊢; linarith
  have h1 := Real.exp_le_exp.mpr hsmall
  have hb := Real.exp_bound (x := (0.0001 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
    (by norm_num)
  have := (abs_le.mp hb).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

/-- `Eu_rat ≤ A_top` (Lemma A.6 (S3)(d), the case `u = X₀`). -/
lemma tail_le_AtopV (Dmax : ℕ) : tailSum Dmax X₀ ≤ AtopV X₀ z := by
  have hX := hc.hX
  have hXb := X0_ge_1e8 hc
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hΛ : 0 < Real.log X₀ := by linarith
  have h := tailSum_le_rat hX Dmax
  refine h.trans ?_
  unfold AtopV
  have hl : Real.log X₀ ≤ Real.log (2 * z + 2) := Real.log_le_log hX0 (by linarith)
  have he : 1 / ((X₀ : ℝ) * Real.log X₀) ≤ 2.21 / Real.log X₀ + 1e-6 := by
    have : 1 / ((X₀ : ℝ) * Real.log X₀) ≤ 2.21 / Real.log X₀ := by
      rw [div_le_div_iff₀ (by positivity) hΛ]; nlinarith
    linarith
  have hE := Real.exp_le_exp.mpr he
  have hp := Real.exp_pos (1 / ((X₀ : ℝ) * Real.log X₀))
  have := logV_nonneg (hc := hc) hz
  gcongr

lemma EuZ_le_AtopV : EuZ X₀ z ≤ AtopV X₀ z := tail_le_AtopV (hc := hc) hz _

/-- `A_top ≤ A_R b`, `A_R = 1.8 (log z + 0.7)`, `b = exp(2.21/Λ + 10⁻⁶)`. -/
lemma AtopV_le_AR : AtopV X₀ z ≤ 1.8 * (Real.log z + 0.7) *
    Real.exp (2.21 / Real.log X₀ + 1e-6) := by
  unfold AtopV
  have := logV_le (hc := hc) hz
  gcongr

/-- `A_top ≤ 2 log z` (`hCh` with `Ch = A_top`). -/
lemma AtopV_le_two : AtopV X₀ z ≤ 2 * Real.log z := by
  have h1 := AtopV_le_AR (hc := hc) hz
  have h2 := expV_le (hc := hc)
  have hL := logz_ge (hc := hc) hz
  have hp := Real.exp_pos (2.21 / Real.log X₀ + 1e-6)
  calc AtopV X₀ z ≤ 1.8 * (Real.log z + 0.7) * Real.exp (2.21 / Real.log X₀ + 1e-6) := h1
    _ ≤ 1.8 * (Real.log z + 0.7) * 1.0002 := by gcongr
    _ ≤ 2 * Real.log z := by nlinarith

lemma AtopV_nonneg : 0 ≤ AtopV X₀ z := by
  unfold AtopV
  have := logV_nonneg (hc := hc) hz
  positivity

omit hz in
/-- `θ e^{(3H(X₀)+2)/X₀} b ≤ 1.01`, `θ = 1 + 1/Λ`, `b = exp(2.21/Λ + 10⁻⁶)`. -/
lemma theta_abV : (1 + 1 / Real.log X₀) * Real.exp ((3 * capH X₀ X₀ + 2) / X₀) *
    Real.exp (2.21 / Real.log X₀ + 1e-6) ≤ 1.01 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hs := capH_X0_small (hc := hc)
  have hX16 := X0_ge_big (hc := hc)
  have h1 : (3 * capH X₀ X₀ + 2) / X₀ ≤ 1e-9 := by
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (by linarith)] at hs
    nlinarith
  have h2 : 2.21 / Real.log X₀ ≤ 1e-7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 1 / Real.log X₀ ≤ 1e-8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [mul_assoc, ← Real.exp_add]
  have he : Real.exp ((3 * capH X₀ X₀ + 2) / X₀ + (2.21 / Real.log X₀ + 1e-6)) ≤ 1.001 := by
    have : (3 * capH X₀ X₀ + 2) / X₀ + (2.21 / Real.log X₀ + 1e-6) ≤ 0.0001 := by linarith
    have h1' := Real.exp_le_exp.mpr this
    have hb := Real.exp_bound (x := (0.0001 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
      (by norm_num)
    have := (abs_le.mp hb).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hpos := Real.exp_pos ((3 * capH X₀ X₀ + 2) / X₀ + (2.21 / Real.log X₀ + 1e-6))
  nlinarith

end NumV

section NumV2

variable {hc : Cond θ X₀}
include hc

variable {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
include hz

/-- `1 + r₀ log(A_top/Eu) ≤ L` (`hrlam`). -/
lemma rlam_leV : 1 + (r0At z : ℝ) * Real.log (AtopV X₀ z / EuZ X₀ z) ≤ Real.log z := by
  have hz' : (X₀ : ℝ) / 2 ≤ z := by linarith [Nat.cast_nonneg (α := ℝ) X₀]
  obtain ⟨hz1, hL, -, hℓ⟩ := z_facts (hc := hc) hz
  have hE1 := tailSum_ge_one (hc := hc) hz
  have hEuA := EuZ_le_AtopV (hc := hc) hz'
  have hA := AtopV_le_two (hc := hc) hz'
  have hr := r0_hi (hc := hc) hz
  set L := Real.log z
  set ℓ := Real.log L
  have hlam : Real.log (AtopV X₀ z / EuZ X₀ z) ≤ ℓ + 0.7 := by
    have h1 : AtopV X₀ z / EuZ X₀ z ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h0 : 0 < AtopV X₀ z / EuZ X₀ z := div_pos (by linarith) (by linarith)
    have := Real.log_le_log h0 h1
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith [Real.log_two_lt_d9]
  have hlam0 : 0 ≤ Real.log (AtopV X₀ z / EuZ X₀ z) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hℓL : ℓ ≤ L / 1000 := by
    have := sq_log_le (show (1 : ℝ) ≤ L by linarith)
    by_contra hc'; push_neg at hc'
    have : L ^ 2 < (1000 * ℓ) ^ 2 := by nlinarith
    nlinarith
  have hr0 : (0 : ℝ) ≤ r0At z := Nat.cast_nonneg _
  calc 1 + (r0At z : ℝ) * Real.log (AtopV X₀ z / EuZ X₀ z)
      ≤ 1 + (L / (3 * ℓ) + 4) * (ℓ + 0.7) := by
        gcongr
    _ = 1 + L / 3 + 0.7 * L / (3 * ℓ) + 4 * ℓ + 2.8 := by
        have hℓ0 : ℓ ≠ 0 := by linarith
        field_simp; ring
    _ ≤ L := by
        have : 0.7 * L / (3 * ℓ) ≤ 0.7 * L / 54 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num); linarith
        nlinarith

end NumV2

/-! ### The skeleton bound for the position-cut law -/

section BoundV

variable (hc : Cond θ X₀) (hev : Even X₀)

/-- **The (S3)(d) event at the height `z_n`**: the Euler-product bound `≤ A_top` for the
position-cut law at every stage `u ≤ s_max`. -/
def SV (n : ℕ) : Set JitterΩ :=
  s3dEv (truncLaw (constructionLaw2 hc hev) (bCut (zH X₀ n))) (NpZ (zH X₀ n))
    (DmaxZ (zH X₀ n)) X₀ (smaxZ (zH X₀ n)) (AtopV X₀ (zH X₀ n)) (smaxZ (zH X₀ n))

lemma SV_meas (n : ℕ) : MeasurableSet (SV hc hev n) :=
  (truncLaw (constructionLaw2 hc hev) (bCut (zH X₀ n))).F_le _ _ (s3dEv_meas _ _ _ _ _ _ _)

/-- **(S3)(d) holds on `Good(< t(E1(z_n)))`**, off the null set `NiceEvᶜ` (`s3dV_sure`). -/
theorem mem_SV (D : Sec5Family) {n : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D (tE1 X₀ n))
    (hN : ω ∈ NiceEv θ X₀) : ω ∈ SV hc hev n := by
  classical
  intro u' _ _
  unfold eulerLt
  exact s3dV_sure D hc hev hω hN (DmaxZ (zH X₀ n)) _
    (fun k hk => (Finset.mem_filter.mp hk).2.1)

/-- **The skeleton bound (Lemma A.5 + Theorem A.10) at the height `z_n`, with (S3)(d) proved**:
on a measurable `Good ⊆ G_{<s_max} ∩ S(z_n)`, for every grid window, from `skeletonBound_all`
for the position-cut law; the window sets are those of the full law. -/
theorem hboundV {n : ℕ} (hz2 : 2 ≤ Real.log (zH X₀ n)) {Good : Set JitterΩ}
    (hGood : MeasurableSet Good) (hGoodB : Good ⊆ goodLt θ X₀ (smaxZ (zH X₀ n)))
    (hGoodS : Good ⊆ SV hc hev n) :
    ∀ k ∈ gridW X₀ n, SkeletonBound jitterMeasure Good (r0At (zH X₀ n)) (1 + 1 / Real.log X₀)
      (2 * gridDelta (zH X₀ n)) (AtopV X₀ (zH X₀ n)) (EuZ X₀ (zH X₀ n))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
        (gwin (zH X₀ n) k)) E l) := by
  classical
  intro k hk
  set z := zH X₀ n with hzdef
  have hz1 : 1 < z := zH_gt_one hc n
  have hδ : 0 < gridDelta z := gridDelta_pos hz1
  have hk' := ((mem_gridW hδ).mp hk).2
  have hJb : gwin z k ⊆ Iic (bCut z) := gridWin_le hz2 hk'
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hΛ : 0 < Real.log X₀ := by linarith [hc.hX]
  set J := constructionLaw2 hc hev with hJdef
  set J' := truncLaw J (bCut z) with hJ'def
  set N := NpZ z
  set smax := smaxZ z
  set A := AtopV X₀ z
  set Dmax := DmaxZ z
  set G : ℕ → Set JitterΩ := fun u => goodLt θ X₀ u ∩ s3dEv J' N Dmax X₀ smax A u with hGdef
  have hGm : ∀ u, MeasurableSet[J'.F u] (G u) := fun u =>
    (good_meas hc u).inter (s3dEv_meas J' N Dmax X₀ smax A u)
  have hGa : ∀ u u', u ≤ u' → G u' ⊆ G u := fun u u' h =>
    Set.inter_subset_inter (good_anti h) (s3dEv_anti J' N Dmax X₀ smax A h)
  have hGoodG : Good ⊆ G smax := fun ω hω => ⟨hGoodB hω, hGoodS hω⟩
  have hr0 : 1 ≤ r0At z := by unfold r0At; omega
  have hτ1 : ∀ j : Fin (r0At z), 1 ≤ tauSlot (capH X₀) X₀ j :=
    fun j => (one_lt_tauSlot (hc := hc) j).le
  have hEu : 0 < EuZ X₀ z := by
    have := tailSum_ge_one (hc := hc) (z := (X₀ : ℝ)) le_rfl
    unfold EuZ at this ⊢
    have h1 : 1 ≤ tailSum Dmax X₀ := by
      unfold tailSum
      have hX1' : 1 ≤ Dmax := by
        simp only [Dmax, DmaxZ]
        exact Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
      have hmem : 1 ∈ Nat.smoothNumbersUpTo Dmax X₀ := by
        rw [Nat.mem_smoothNumbersUpTo]
        refine ⟨hX1', ?_⟩
        rw [Nat.mem_smoothNumbers]; simp
      have := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ))⁻¹)
        (fun d _ => by positivity) hmem
      simpa using this
    linarith
  have hq : ∀ ω, ∀ m : Fin N, ω ∈ J'.A m → 1 < J'.q m ω :=
    fun ω m hm => law2_hq hc hev ω m hm.1
  have hsmax : ∀ ω, ∀ m : Fin N, ω ∈ J'.A m → ∀ y ∈ gwin z k, J'.q m ω ≤ y →
      (m : ℕ) ≤ smax :=
    fun ω m hm y hy hqy => law2_hsmax hc hev (gridWin_le hz2 hk') ω m hm.1 y hy hqy
  have hτ : ∀ ω, ∀ m : Fin N, ω ∈ J'.A m → ∀ j : Fin (r0At z),
      (j : ℕ) ≤ ((decOf (N := N) J' ω).filter (· < m)).card →
        tauSlot (capH X₀) X₀ j ≤ J'.q m ω :=
    fun ω m hm j hj => law2_hτSlot hc hev ω m hm.1 j (hj.trans (card_dec_trunc_le J _ ω m))
  have hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J' (EuZ X₀ z) ω u ≤ A :=
    fun ω u hu hω => hω.2 u le_rfl hu
  have h := skeletonBound_all J' (θ := 1 + 1 / Real.log X₀) (by positivity) le_rfl hGood G hGm
    hGa smax hGoodG hr0 (fun j => tauSlot (capH X₀) X₀ j) hτ1 (Jw := gwin z k)
    (measurableSet_Ico : MeasurableSet (gwin z k)) (gridWin_sub z k) (by linarith) X₀
    (DpZ X₀ z) Dmax hEu le_rfl hq hsmax hτ hS3
  intro E hE l hl
  refine le_trans (le_of_eq ?_) (h E hE l hl)
  refine lintegral_congr fun ω => ?_
  dsimp only
  rw [windowVecs_trunc J (bCut z) ω (fun m hm => (law2_hq hc hev ω m hm).le)
    (fun m _ => valF_ge_slot hc m ω) X₀ (DpZ X₀ z) Dmax hJb]

/-- The good event of the window model at `z_n`: the measurable hull of `G ∩ G_{<s_max}`,
intersected with `G_{<s_max}` and the (S3)(d) event `S(z_n)`. -/
noncomputable def goodV (G : Set JitterΩ) (n : ℕ) : Set JitterΩ :=
  (toMeasurable jitterMeasure (G ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) ∩
    goodLt θ X₀ (smaxZ (zH X₀ n))) ∩ SV hc hev n

lemma goodV_meas (G : Set JitterΩ) (n : ℕ) : MeasurableSet (goodV hc hev G n) :=
  ((measurableSet_toMeasurable _ _).inter
    (jitterFiltration.le _ _ (good_meas hc _))).inter (SV_meas hc hev n)

/-- The `∫⁻` over `goodV` is at most the `∫⁻` over `G ∩ G_{<s_max}`. -/
lemma lintegral_goodV_le (G : Set JitterΩ) (n : ℕ) (f : JitterΩ → ENNReal) :
    ∫⁻ ω in goodV hc hev G n, f ω ∂jitterMeasure ≤
      ∫⁻ ω in G ∩ goodLt θ X₀ (smaxZ (zH X₀ n)), f ω ∂jitterMeasure := by
  have hB : MeasurableSet (goodLt θ X₀ (smaxZ (zH X₀ n))) :=
    jitterFiltration.le _ _ (good_meas hc _)
  have hres := restrict_hull_inter jitterMeasure G hB
  calc ∫⁻ ω in goodV hc hev G n, f ω ∂jitterMeasure
      ≤ ∫⁻ ω in toMeasurable jitterMeasure (G ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) ∩
          goodLt θ X₀ (smaxZ (zH X₀ n)), f ω ∂jitterMeasure :=
        lintegral_mono_set Set.inter_subset_left
    _ = _ := by rw [hres]

/-- **The failure split**: `P(Eᶜ ∩ Good(< t)) ≤ P(Eᶜ ∩ goodV)`, since `G_{<s_max}ᶜ` and `NiceEvᶜ`
are null and (S3)(d) holds on `Good(< t) ∩ NiceEv`. -/
lemma fail_le_goodV (D : Sec5Family) (n : ℕ) (E : Set JitterΩ) :
    jitterMeasure (Eᶜ ∩ G0 θ X₀ D (tE1 X₀ n)) ≤
      jitterMeasure (Eᶜ ∩ goodV hc hev (G0 θ X₀ D (tE1 X₀ n)) n) := by
  set G := G0 θ X₀ D (tE1 X₀ n)
  set B := goodLt θ X₀ (smaxZ (zH X₀ n))
  have hnull : jitterMeasure Bᶜ = 0 := good_compl_null hc _
  have hnice : jitterMeasure (NiceEv θ X₀)ᶜ = 0 := niceEv_compl_null hc hev
  have hsub : Eᶜ ∩ G ⊆ (Eᶜ ∩ goodV hc hev G n) ∪ (Bᶜ ∪ (NiceEv θ X₀)ᶜ) := by
    intro ω ⟨h1, h2⟩
    by_cases hb : ω ∈ B
    · by_cases hN : ω ∈ NiceEv θ X₀
      · left
        exact ⟨h1, ⟨subset_toMeasurable _ _ ⟨h2, hb⟩, hb⟩, mem_SV hc hev D h2 hN⟩
      · right; right; exact hN
    · right; left; exact hb
  calc jitterMeasure (Eᶜ ∩ G)
      ≤ jitterMeasure (Eᶜ ∩ goodV hc hev G n) + jitterMeasure (Bᶜ ∪ (NiceEv θ X₀)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = jitterMeasure (Eᶜ ∩ goodV hc hev G n) := by
        rw [measure_union_null hnull hnice, add_zero]

end BoundV

/-! ### Proposition 6.11 for the cluster events -/

section Prop611V

variable (hc : Cond θ X₀) (hev : Even X₀)

/-- **The Cover Bound input at the height `z_n`** (Lemmas 6.17–6.19, `CoverSkeletonBound`) with
`A = A_top(z_n)` (named hypothesis of Proposition 6.11). -/
def CoverV (G : Set JitterΩ) (n : ℕ) : Prop :=
  ∀ j, ∀ k ∈ gridW X₀ n, ∀ r < r0At (zH X₀ n), ∀ C ∈ CSet r j, ∀ lab ex s4,
    ExOK C ex → ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
      CoverSkeletonBound jitterMeasure (G ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) r
        (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopV X₀ (zH X₀ n))
        (EuZ X₀ (zH X₀ n)) (zH X₀ n) (fun i => tauSlot (capH X₀) X₀ i) (exExcess ex)
        (r - C.card) l (fun ω => cfgSkelCount (DpZ X₀ (zH X₀ n)) (r0At (zH X₀ n)) 0 0
          (tailOf (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
            (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
            (gwin (zH X₀ n) k))
          (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
            (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
            (gwin (zH X₀ n) k)) r C lab ex s4)

/-- **Proposition 6.11 at the dyadic height `z_n ≥ X₀`** on `Good(< t(E1(z_n)))`, from the
window model (`prop_6_11_window`) with the skeleton bound `hboundV` ((S3)(d) and the multi-run
skeleton bound proved). The only input is the Cover Bound `CoverV`. -/
theorem eclV_fail (D : Sec5Family) {n : ℕ} (hn : 1 ≤ n)
    (hcov : CoverV hc hev (G0 θ X₀ D (tE1 X₀ n)) n) :
    jitterMeasure ((EclW hc hev n)ᶜ ∩ G0 θ X₀ D (tE1 X₀ n)) ≤
      ENNReal.ofReal (Real.log (zH X₀ n) ^ (-2 : ℝ)) := by
  classical
  set z := zH X₀ n with hzdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hz : (X₀ : ℝ) ≤ z := by
    simp only [hzdef, zH]
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith
  have hz' : (X₀ : ℝ) / 2 ≤ z := by linarith
  obtain ⟨hz1, hL, hll, hℓ⟩ := z_facts (hc := hc) hz
  have hz2 : 2 ≤ Real.log z := by linarith
  have hE := exp_ell_eq (hc := hc) hz1
  have hzz : Real.exp (Real.exp (2 * Real.log (Real.log X₀) + capS X₀ z)) = z := by
    rw [hE, Real.exp_log (by linarith)]
  set G := G0 θ X₀ D (tE1 X₀ n)
  set Good := goodV hc hev G n
  have hGM : MeasurableSet Good := goodV_meas hc hev G n
  have hEuA := EuZ_le_AtopV (hc := hc) hz'
  have hE1 := tailSum_ge_one (hc := hc) hz
  have hA0 := AtopV_nonneg (hc := hc) hz'
  have hM : M1cl X₀ z = (r0At z : ℝ) + Covers.phi
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z)))
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z) / 2)) (r0At z) + 1 := by
    unfold M1cl cAt logcAt; rw [sqrt_exp]
  have hmain := prop_6_11_window jitterMeasure hGM (gridW X₀ n)
    (fun ω => decOf (N := NpZ z) (constructionLaw2 hc hev) ω) (qOf (constructionLaw2 hc hev))
    (DmaxZ z) (gwin z) (fun k => k * gridDelta z) (δ := 2 * gridDelta z)
    (fun k => gridWin_sub z k) (gridDelta_two_lt hz2) hc.hX sHroot_mem gstar_sHroot
    (hs_of (hc := hc) hz) (r₀ := r0At z) (D := DpZ X₀ z) (DpZ_ge_one (hc := hc) hz)
    (by rw [hE]; exact r0_lo (hc := hc) hz)
    (by rw [hE, ell_eq]; exact r0_hi (hc := hc) hz)
    (by rw [hE]; exact DpZ_le (hc := hc) hz) (Xm := Xm X₀) (by linarith [Xm_pos hc])
    (log_Xm_ge (hc := hc)) (by
      have h1 := Xm_pos hc
      unfold Xm at h1 ⊢
      exact Real.log_le_log (by linarith) (by linarith [capH_nonneg X₀ X₀]))
    (tauL X₀) (fun i => le_max_left _ _) (fun i => le_max_right _ _) (hq1_dec hc hev)
    (fun k hk => by
      rw [hzz]
      have hδ : 0 < gridDelta z := gridDelta_pos hz1
      exact gridWin_le hz2 ((mem_gridW hδ).mp hk).2) (hτq_dec hc hev)
    (fun r i => tauSlot (capH X₀) X₀ i) (fun r i => one_lt_tauSlot (hc := hc) i)
    (lam := Real.log (AtopV X₀ z / EuZ X₀ z))
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (by rw [hE]; exact rlam_leV (hc := hc) hz) (Ch := AtopV X₀ z)
    (by rw [hE]; exact AtopV_le_two (hc := hc) hz') (B := 2.1 * Real.log z ^ (1.02 : ℝ))
    (fun r hr => prod_tau_le (hc := hc) hz (slotHyp_capH hX0 hc.hX) hr) (by rw [hE])
    (by linarith) hEuA le_rfl le_rfl
    (by rw [hE, Real.exp_log (by linarith)]; exact gridW_card (hc := hc) hz rfl)
    (θ := 1 + 1 / Real.log X₀) (A := AtopV X₀ z) (Eu' := EuZ X₀ z)
    (A_R := 1.8 * (Real.log z + 0.7)) (b := Real.exp (2.21 / Real.log X₀ + 1e-6))
    (slotHyp_capH hX0 hc.hX) (by positivity)
    (Real.exp_pos _) (theta_abV (hc := hc)) (by nlinarith) (by rw [hE]; nlinarith)
    (by rw [hE]; exact hu_le (hc := hc) hz) (by linarith) hEuA (AtopV_le_AR (hc := hc) hz')
    (fun k E l => meas_skelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k E l)
    (fun k _ => meas_rankFullCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k)
    (fun j k' k _ => meas_configCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) j k' k)
    (fun k r C lab ex s4 =>
      meas_cfgSkelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k r C lab ex s4)
    (fun k hk => by
      rw [← two_gridDelta (hc := hc) hz]
      exact hboundV hc hev hz2 hGM (fun ω hω => hω.1.2) (fun ω hω => hω.2) k hk)
    (fun j k hk r hr C hC lab ex s4 hex => by
      obtain ⟨l, h1, h2, h3⟩ := hcov j k hk r hr C hC lab ex s4 hex
      refine ⟨l, h1, h2, ?_⟩
      rw [← two_gridDelta (hc := hc) hz, hzz]
      unfold CoverSkeletonBound at h3 ⊢
      exact (lintegral_goodV_le hc hev G n _).trans h3)
  have hcompl : (EclW hc hev n)ᶜ = {ω | ∃ k ∈ gridW X₀ n, (r0At z : ℝ) + Covers.phi
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z)))
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z) / 2)) (r0At z) + 1 <
        ((windowElems (decOf (N := NpZ z) (constructionLaw2 hc hev) ω)
          (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z k)).card : ℝ)} := by
    ext ω
    simp only [EclW, mem_compl_iff, mem_setOf_eq, not_forall, not_le, exists_prop]
    rw [← hM]
  calc jitterMeasure ((EclW hc hev n)ᶜ ∩ G)
      ≤ jitterMeasure ((EclW hc hev n)ᶜ ∩ Good) := fail_le_goodV hc hev D n _
    _ ≤ _ := by
        rw [hcompl]
        refine hmain.trans (le_of_eq ?_)
        rw [hE]

/-- **Proposition 6.11 at the lowest height `z_0 = X₀/2`** on `Good(< t(E1(z_0)))` (capacity `0`,
`prop_6_11_model`), with the skeleton bound `hboundV`: no named input. -/
theorem eclV_fail_zero (D : Sec5Family) :
    jitterMeasure ((EclW hc hev 0)ᶜ ∩ G0 θ X₀ D (tE1 X₀ 0)) ≤
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
  have hz' : (X₀ : ℝ) / 2 ≤ z := by rw [hz]
  set G := G0 θ X₀ D (tE1 X₀ 0)
  set Good := goodV hc hev G 0
  have hGM : MeasurableSet Good := goodV_meas hc hev G 0
  have hEuA := EuZ_le_AtopV (hc := hc) hz'
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
  -- `r₀`
  have hr0lo : L / (3 * Real.log L) + 3 ≤ (r0At z : ℝ) := by
    unfold r0At; push_cast
    have := Nat.le_ceil (L / (3 * Real.log L))
    linarith
  have hu : 1 + (r0At z : ℝ) / X₀ ≤ 2 * L := by
    have hr0hi : (r0At z : ℝ) ≤ L / (3 * Real.log L) + 4 := by
      unfold r0At; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ L / (3 * Real.log L) by positivity)
      linarith
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
  have hL' := logz_ge (hc := hc) hz'
  have hmain := prop_6_11_model jitterMeasure hGM (gridW X₀ 0)
    (fun ω => decOf (N := NpZ z) (constructionLaw2 hc hev) ω) (qOf (constructionLaw2 hc hev))
    (hq1_dec hc hev) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z) (fun k => k * gridDelta z)
    (δ := 2 * gridDelta z) (fun k => gridWin_sub z k) (gridDelta_two_lt hz2) (r0At z)
    (c := cAt X₀ z) (Q := Real.sqrt (cAt X₀ z)) (M₁ := M1cl X₀ z) (L := L) (z := z)
    (θ := 1 + 1 / Real.log X₀) (A := AtopV X₀ z) (Eu := EuZ X₀ z)
    (A_R := 1.8 * (L + 0.7)) (b := Real.exp (2.21 / Real.log X₀ + 1e-6)) (X₀ := (X₀ : ℝ))
    (H := capH X₀) (slotHyp_capH hX0 hc.hX) rfl (by linarith) (by linarith)
    (by rw [hLdef, Real.exp_log (by linarith)]) (by positivity) (Real.exp_pos _)
    (theta_abV (hc := hc)) (by nlinarith) (by nlinarith) hu hr0lo hW
    (by linarith) hEuA (AtopV_le_AR (hc := hc) hz')
    (fun k E l => meas_skelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k E l)
    (fun k _ => meas_rankFullCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k)
    (fun k hk => by
      rw [← h2δ]
      exact hboundV hc hev (n := 0) hz2 hGM (fun ω hω => hω.1.2) (fun ω hω => hω.2) k hk)
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
  calc jitterMeasure ((EclW hc hev 0)ᶜ ∩ G)
      ≤ jitterMeasure ((EclW hc hev 0)ᶜ ∩ Good) := fail_le_goodV hc hev D 0 _
    _ ≤ _ := by
        rw [hcompl]
        exact hmain

/-- **The E1 bound of Table 1 at every height** (Proposition 6.11 on `Good(< t(E1(z_n)))`), with
the Cover Bound at the heights `z_n ≥ X₀` as the only input. -/
theorem e1V (D : Sec5Family) (hcov : ∀ n, 1 ≤ n → CoverV hc hev (G0 θ X₀ D (tE1 X₀ n)) n)
    (n : ℕ) :
    jitterMeasure ((E1ev θ X₀ n)ᶜ ∩ G0 θ X₀ D (tE1 X₀ n)) ≤
      ENNReal.ofReal (Real.log (zH X₀ n) ^ (-2 : ℝ)) := by
  have e : E1ev θ X₀ n = EclW hc hev n := by
    unfold E1ev; rw [dif_pos ⟨hc, hev⟩]
  rw [e]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; exact eclV_fail_zero hc hev D
  · exact eclV_fail hc hev D hn (hcov n hn)

end Prop611V

end Queue6

end
