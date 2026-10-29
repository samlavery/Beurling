module

public import RequestProject.Beurling.Queue6.ClusterV
public import RequestProject.Beurling.RankFull.CoverCount

/-!
# Proposition 6.11 with the Cover Bound proved

The Cover Bound (Lemmas 6.17–6.19, Proposition 6.19: `CoverSkeletonBound` for every window,
`r < r₀` and skeleton) is `RankFull.Config.hcov_window`. Applied to the position-cut law
`truncLaw (constructionLaw2) (2z + 1)` on the good event `goodV` (where (S3)(d) holds, as in
`hboundV`), with the caps `τ = tauSlot` and windows in `[z, ∞)`, and transported to the full
law (the window sets and their tails are unchanged by the cut-off), it gives the input `hcov` of
`eclV_fail`:

* `tailOf_trunc` : the tails of the window elements are unchanged by the cut-off;
* `coverOn_goodV` : the Cover Bound on `goodV` at every height `z_n`;
* `e1X` : **the E1 bound of Table 1 at every height, with no input**.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono RankFull RankFull.Config
open scoped ENNReal

namespace RankFull.Config

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞} {N : ℕ}

/-- **The tails are unchanged by the cut-off** for a window `J ⊆ (-∞, b]`. -/
theorem tailOf_trunc (J : JitterLaw Ω P θE) (b : ℝ) (ω : Ω)
    (hq1 : ∀ n : Fin N, ω ∈ J.A n → 1 ≤ J.q n ω)
    (hbox : ∀ n : Fin N, ω ∈ J.A n → J.c n ω - J.H n ω / 2 ≤ J.q n ω)
    (X₀ D Dmax : ℕ) {Jw : Set ℝ} (hJw : Jw ⊆ Iic b) :
    tailOf (decOf (N := N) (truncLaw J b) ω) (qOf (truncLaw J b) ω) X₀ D Dmax Jw =
      tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw := by
  have e := windowElems_trunc J b ω hq1 hbox X₀ D Dmax hJw
  unfold tailOf
  generalize windowElems (decOf (N := N) (truncLaw J b) ω) (qOf (truncLaw J b) ω) X₀ D Dmax Jw
    = S at e ⊢
  subst e; rfl

end RankFull.Config

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

section CoverX

variable (hc : Cond θ X₀) (hev : Even X₀)

/-- **The Cover Bound at the height `z_n`** on a measurable `Good ⊆ G_{<s_max} ∩ S(z_n)`
(Proposition 6.19, `hcov_window`, for the position-cut law). -/
theorem coverOn_of_good {n : ℕ} (hz2 : 2 ≤ Real.log (zH X₀ n)) {Good : Set JitterΩ}
    (hGood : MeasurableSet Good) (hGoodB : Good ⊆ goodLt θ X₀ (smaxZ (zH X₀ n)))
    (hGoodS : Good ⊆ SV hc hev n) : CoverOn hc hev Good n := by
  classical
  set z := zH X₀ n with hzdef
  have hz1 : 1 < z := zH_gt_one hc n
  have hδ : 0 < gridDelta z := gridDelta_pos hz1
  have hΛ : 0 < Real.log X₀ := by linarith [hc.hX]
  set J := constructionLaw2 hc hev with hJdef
  set J' := truncLaw J (bCut z) with hJ'def
  set Nn := NpZ z
  set smax := smaxZ z
  set A := AtopV X₀ z
  set Dmax := DmaxZ z
  set G : ℕ → Set JitterΩ := fun u => goodLt θ X₀ u ∩ s3dEv J' Nn Dmax X₀ smax A u
  have hGm : ∀ u, MeasurableSet[J'.F u] (G u) := fun u =>
    (good_meas hc u).inter (s3dEv_meas J' Nn Dmax X₀ smax A u)
  have hGa : ∀ u u', u ≤ u' → G u' ⊆ G u := fun u u' h =>
    Set.inter_subset_inter (good_anti h) (s3dEv_anti J' Nn Dmax X₀ smax A h)
  have hGoodG : Good ⊆ G smax := fun ω hω => ⟨hGoodB hω, hGoodS hω⟩
  have hEu : 0 < EuZ X₀ z := by
    have hE := tailSum_ge_one (hc := hc) (z := (X₀ : ℝ)) le_rfl
    unfold EuZ at hE ⊢
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
  have hq : ∀ ω, ∀ m : Fin Nn, ω ∈ J'.A m → 1 < J'.q m ω :=
    fun ω m hm => law2_hq hc hev ω m hm.1
  have hsmax : ∀ k ∈ gridW X₀ n, ∀ ω, ∀ m : Fin Nn, ω ∈ J'.A m → ∀ y ∈ gwin z k,
      J'.q m ω ≤ y → (m : ℕ) ≤ smax :=
    fun k hk ω m hm y hy hqy =>
      law2_hsmax hc hev (gridWin_le hz2 ((mem_gridW hδ).mp hk).2) ω m hm.1 y hy hqy
  have hτ : ∀ r < r0At z, ∀ ω, ∀ m : Fin Nn, ω ∈ J'.A m → ∀ j : Fin r,
      (j : ℕ) ≤ ((decOf (N := Nn) J' ω).filter (· < m)).card →
        tauSlot (capH X₀) X₀ j ≤ J'.q m ω :=
    fun r _ ω m hm j hj => law2_hτSlot hc hev ω m hm.1 j (hj.trans (card_dec_trunc_le J _ ω m))
  have hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := Nn) J' (EuZ X₀ z) ω u ≤ A :=
    fun ω u hu hω => hω.2 u le_rfl hu
  have hJz : ∀ k ∈ gridW X₀ n, gwin z k ⊆ Set.Ici z := by
    intro k hk x hx
    have := ((mem_gridW hδ).mp hk).1
    exact le_trans this hx.1
  have h := hcov_window J' (θ := 1 + 1 / Real.log X₀) (by positivity) le_rfl hGood G hGm hGa
    smax hGoodG (r0At z) (gridW X₀ n) (gwin z) (fun _ _ => measurableSet_Ico)
    (fun k => k * gridDelta z) (δ := 2 * gridDelta z) (fun k _ => gridWin_sub z k)
    (by linarith) (z := z) (by linarith) hJz X₀ (DpZ X₀ z) Dmax hEu le_rfl hq hsmax hS3
    (fun _ i => tauSlot (capH X₀) X₀ i) (fun _ i => (one_lt_tauSlot (hc := hc) i).le) hτ
  intro j k hk r hr C hC lab ex s4 hex
  obtain ⟨l, h1, h2, h3⟩ := h j k hk r hr C hC lab ex s4 hex
  refine ⟨l, h1, h2, ?_⟩
  unfold CoverSkeletonBound at h3 ⊢
  refine le_trans (le_of_eq ?_) h3
  refine lintegral_congr fun ω => ?_
  have hJb : gwin z k ⊆ Iic (bCut z) := gridWin_le hz2 ((mem_gridW hδ).mp hk).2
  have hq1 : ∀ m : Fin Nn, ω ∈ J.A m → 1 ≤ J.q m ω := fun m hm => (law2_hq hc hev ω m hm).le
  have hbox : ∀ m : Fin Nn, ω ∈ J.A m → J.c m ω - J.H m ω / 2 ≤ J.q m ω :=
    fun m _ => valF_ge_slot hc m ω
  rw [windowVecs_trunc J (bCut z) ω hq1 hbox X₀ (DpZ X₀ z) Dmax hJb,
    tailOf_trunc J (bCut z) ω hq1 hbox X₀ (DpZ X₀ z) Dmax hJb]

/-- **The Cover Bound on `goodV`** at every height `z_n`, `n ≥ 1`. -/
theorem coverOn_goodV (G : Set JitterΩ) {n : ℕ} (hn : 1 ≤ n) :
    CoverOn hc hev (goodV hc hev G n) n := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hz : (X₀ : ℝ) ≤ zH X₀ n := by
    simp only [zH]
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith
  obtain ⟨-, hL, -, -⟩ := z_facts (hc := hc) hz
  exact coverOn_of_good hc hev (by linarith) (goodV_meas hc hev G n)
    (fun ω hω => hω.1.2) (fun ω hω => hω.2)

include hc hev in
/-- **The E1 bound of Table 1 at every height** (Proposition 6.11 on `Good(< t(E1(z_n)))`), with
no named input. -/
theorem e1X (D : Sec5Family) (n : ℕ) :
    jitterMeasure ((E1ev θ X₀ n)ᶜ ∩ G0 θ X₀ D (tE1 X₀ n)) ≤
      ENNReal.ofReal (Real.log (zH X₀ n) ^ (-2 : ℝ)) := by
  have e : E1ev θ X₀ n = EclW hc hev n := by
    unfold E1ev; rw [dif_pos ⟨hc, hev⟩]
  rw [e]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; exact eclV_fail_zero hc hev D
  · exact eclV_fail hc hev D hn (coverOn_goodV hc hev _ hn)

end CoverX

end Queue6

end
