module

public import RequestProject.Beurling.Model.Wire2
public import RequestProject.Beurling.Noise.KRNormFix

/-!
# Eq. (NT): `|NT_pt| ≤ 2 η` for the realised system

`NT_pt := c - K_pt ρ̃ + K_𝒜 ρ̃` (§5.3, 04b-identity.tex): "`NT` replaces the slot filter
`s_q > τ_w` by the landing filter `y/w > τ_w` on the non-absorbed part. It is supported on
`τ`-near-threshold cofactors, i.e. those with `|τ_w - y/w| ≤ 2H(y/w)`, and
`|NT(y)| ≤ 2η(y) · sup ρ̃`, `η(y) := ∑_{w τ-near at y} 1/w`" (eq. (NT)).

Here the compensator density `c` (`compDen`) is a sum over the slots `k` and the cofactor
exponent vectors `e ∈ cofP k` (jittered primes decided at earlier slots), while `K_pt` sums over
the `ℕ`-labels `w` of the realised system with the landing filter `τ_w < y/w`. Transporting the
exponent vectors to labels (`Model/Identify.lean`, `mapE`), the two filters agree on every slot
`k` with `y/w ∈ box_k` unless `w` is `τ`-near at `y` (`filters_agree`), and on the `τ`-near
cofactors both sides lie in `[0, ρ̃(y/w)/w]`. With `ρ̃ ≤ 2` this gives
`|NT_pt(y)| ≤ ∑_{w τ-near} ρ̃(y/w)/w ≤ 2 η(y)` (`NTpt_abs_le_eta`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem SlotModel
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section Transport

variable (hc : Cond θ X₀) (ω : JitterΩ)
include hc

/-- The realised system of the constructed model is a Beurling system. -/
lemma realisedOK_Mcl : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω) := by
  rw [Mcl_eq hc ω]; exact limModel_realisedOK (hc.std ω)

variable {hc ω}

/-- The transport `f ↦ e` of an exponent vector over the realised primes (indexed by `ℕ`) to the
fixed index set `PIdx X₀`. -/
noncomputable def EF (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) (f : ℕ →₀ ℕ) :
    PIdx X₀ →₀ ℕ :=
  mapE (Mcl θ X₀ ω) (Finsupp.equivMapDomain h.equiv f)

omit hc in
lemma EF_eval (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) (f : ℕ →₀ ℕ) :
    eval (DD θ X₀ ω) (EF h f) = (PR θ X₀ ω).val f := by
  unfold EF
  rw [show DD θ X₀ ω = DM (Mcl θ X₀ ω) (Ucl ω) from rfl, eval_mapE, PR, val_eq_idxVal h]

omit hc in
lemma EF_injective (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) :
    Function.Injective (EF h) :=
  (mapE_injective _).comp (equivMapDomain_inj _)

omit hc in
lemma EF_live (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) (f : ℕ →₀ ℕ) :
    Live (DD θ X₀ ω) (EF h f) :=
  live_mapE _ _ _

omit hc in
lemma EF_zero (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) : EF h 0 = 0 := by
  unfold EF mapE; simp

omit hc in
lemma EF_ne_zero (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) {f : ℕ →₀ ℕ} (hf : f ≠ 0) :
    EF h f ≠ 0 := by
  intro h0; apply hf; apply EF_injective h; rw [h0, EF_zero]

omit hc in
lemma EF_surj (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) {e : PIdx X₀ →₀ ℕ}
    (he : Live (DD θ X₀ ω) e) : ∃ f, EF h f = e := by
  obtain ⟨g, hg⟩ := exists_mapE (M := Mcl θ X₀ ω) (U := Ucl ω) he
  refine ⟨Finsupp.equivMapDomain h.equiv.symm g, ?_⟩
  unfold EF
  rw [← hg]; congr 1; ext i; simp [Finsupp.equivMapDomain_apply]

omit hc in
lemma EF_inr (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) (f : ℕ →₀ ℕ) (j : ℕ) :
    EF h f (Sum.inr j) ≠ 0 ↔ ∃ i ∈ f.support, ∃ hk, h.equiv i = Sum.inr ⟨j, hk⟩ := by
  classical
  unfold EF
  rw [mapE_apply_inr]
  constructor
  · intro hne
    split_ifs at hne with hk
    · refine ⟨h.equiv.symm (Sum.inr ⟨j, hk⟩), ?_, hk, by simp⟩
      rw [Finsupp.mem_support_iff]
      simpa [Finsupp.equivMapDomain_apply] using hne
    · exact absurd rfl hne
  · rintro ⟨i, hi, hk, he⟩
    rw [dif_pos hk, Finsupp.equivMapDomain_apply, ← he, Equiv.symm_apply_apply]
    exact Finsupp.mem_support_iff.mp hi

omit hc in
lemma count_qp (i : ℕ) : Nat.count Nat.Prime (qp i) = i :=
  Nat.count_nth_of_infinite Nat.infinite_setOf_prime i

omit hc in
lemma twR_qp_inl (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) {i : ℕ}
    {p : {p : ℕ // p.Prime ∧ p < X₀}} (hi : h.equiv i = Sum.inl p) :
    twR θ X₀ ω (qp i) = (p.1 : ℝ) := by
  unfold twR
  rw [if_pos (qp_prime i), count_qp, realisedSrc_eq h, hi]
  show (PR θ X₀ ω).p i = _
  rw [PR, realisedSystem_p h, hi]; rfl

omit hc in
lemma twR_qp_inr (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) {i : ℕ}
    {k : {k : ℕ // placedAt (Mcl θ X₀ ω) k}} (hi : h.equiv i = Sum.inr k) :
    twR θ X₀ ω (qp i) = slotF θ X₀ k.1 ω := by
  unfold twR
  rw [if_pos (qp_prime i), count_qp, realisedSrc_eq h, hi]
  rfl

end Transport

/-! ### The two filters on a box -/

section Filters

variable (hc : Cond θ X₀)
include hc

/-- **Width regularity at a box**: if `z ≥ s - H(s)/2` with `s ≥ X₀`, then `H(s)/2 ≤ 2 H(z)`
(`H = Hc X₀`; `capH_lip`). -/
lemma half_capH_le {s z : ℝ} (hs : (X₀ : ℝ) ≤ s) (hz : s - capH X₀ s / 2 ≤ z) :
    capH X₀ s / 2 ≤ 2 * Queue6.Hc X₀ z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  set x := max z (X₀ : ℝ) with hxdef
  have hxX : (X₀ : ℝ) ≤ x := le_max_right _ _
  have hHx : 1 ≤ capH X₀ x := capH_ge_one hX0 hX hxX
  have e : Queue6.Hc X₀ z = capH X₀ x := rfl
  rw [e]
  rcases le_total s x with hsx | hxs
  · have := capH_monotoneOn hX0 hX (mem_Ici.mpr hs) (mem_Ici.mpr hxX) hsx
    linarith
  · have hl := capH_lip hX0 hX hxX hxs
    have : s - x ≤ capH X₀ s / 2 := by
      have : z ≤ x := le_max_left _ _
      linarith
    linarith

/-- `H(X₀)/2 ≤ 2 H(z)` for every `z`. -/
lemma half_capH_X0_le (z : ℝ) : capH X₀ X₀ / 2 ≤ 2 * Queue6.Hc X₀ z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  have hxX : (X₀ : ℝ) ≤ max z X₀ := le_max_right _ _
  have h1 := capH_monotoneOn hX0 hX (mem_Ici.mpr le_rfl) (mem_Ici.mpr hxX) hxX
  have h2 := capH_ge_one hX0 hX (le_refl (X₀ : ℝ))
  show capH X₀ X₀ / 2 ≤ 2 * capH X₀ (max z X₀)
  linarith

variable {ω : JitterΩ} (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω))

omit hc in
lemma tauW_iota_eq {f : ℕ →₀ ℕ} (hf : f ≠ 0) :
    ∃ hne : (f.support.image qp).Nonempty,
      tauW (twR θ X₀ ω) (iota f) = (f.support.image qp).sup' hne (twR θ X₀ ω) := by
  have hne : (f.support.image qp).Nonempty :=
    (Finsupp.support_nonempty_iff.mpr hf).image _
  refine ⟨hne, ?_⟩
  unfold tauW
  have hne' : (iota f).primeFactors.Nonempty := by rw [primeFactors_iota]; exact hne
  rw [dif_pos hne']
  simp only [primeFactors_iota]

set_option maxHeartbeats 1000000 in
/-- **The filters agree off the `τ`-near cofactors** (proof of eq. (NT)): at a slot `k` whose
box contains the landing point `z = y/w`, the slot filter (`τ_w` before `s_k`: every jittered
prime of `w` decided at an earlier slot) and the landing filter `τ_w < z` agree unless
`|τ_w - z| ≤ 2H(z)`. -/
theorem filters_agree {f : ℕ →₀ ℕ} (hf : f ≠ 0) {y : ℝ} {k : ℕ}
    (hz : Xm X₀ ≤ y / (PR θ X₀ ω).val f)
    (hbox : y / (PR θ X₀ ω).val f ∈ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω))
    (hnear : ¬ TauNearAt (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y (iota f)) :
    (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ↔
      ∀ i ∈ f.support, twR θ X₀ ω (qp i) < y / (PR θ X₀ ω).val f := by
  classical
  set P := PR θ X₀ ω with hP
  set z := y / P.val f with hzdef
  have hVl : Vl P (iota f) = P.val f := P.valN_iota f
  have hsk := slotF_ge hc k ω
  obtain ⟨hb1, hb2⟩ := hbox
  have hW := half_capH_le hc hsk (show slotF θ X₀ k ω - capH X₀ (slotF θ X₀ k ω) / 2 ≤ z from
    hb1)
  have hW0 := half_capH_X0_le hc z
  obtain ⟨hne, hτ⟩ := tauW_iota_eq (ω := ω) hf
  have hnear' : ¬ |tauW (twR θ X₀ ω) (iota f) - z| ≤ 2 * Queue6.Hc X₀ z := by
    intro hn; apply hnear
    unfold TauNearAt
    rw [hVl]; exact ⟨hn, hz⟩
  have hXm : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
  have hHk : HF θ X₀ k ω = capH X₀ (slotF θ X₀ k ω) := rfl
  constructor
  · intro hC
    by_contra hL
    push_neg at hL
    obtain ⟨i0, hi0, hi0z⟩ := hL
    apply hnear'
    rw [hτ, abs_le]
    constructor
    · have := Finset.le_sup' (twR θ X₀ ω) (Finset.mem_image_of_mem qp hi0)
      linarith
    · have : (f.support.image qp).sup' hne (twR θ X₀ ω) ≤ z + 2 * Queue6.Hc X₀ z := by
        refine Finset.sup'_le _ _ fun r hr => ?_
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        rcases he : h.equiv i with p | kk
        · rw [twR_qp_inl h he]
          have hp : ((p.1 : ℕ) : ℝ) < X₀ := by exact_mod_cast p.2.2
          linarith
        · rw [twR_qp_inr h he]
          have hjk : kk.1 < k := hC kk.1 ((EF_inr h f kk.1).mpr ⟨i, hi, kk.2, by rw [he]⟩)
          have := (Mcl θ X₀ ω).slot_mono (show kk.1 + 1 ≤ k + 1 by omega)
          have e1 : slotF θ X₀ kk.1 ω = (Mcl θ X₀ ω).slot (kk.1 + 1) := rfl
          have e2 : slotF θ X₀ k ω = (Mcl θ X₀ ω).slot (k + 1) := rfl
          rw [hHk] at hb2
          linarith
      linarith
  · intro hL j hj
    by_contra hjk
    push_neg at hjk
    obtain ⟨i, hi, hk, he⟩ := (EF_inr h f j).mp hj
    apply hnear'
    rw [hτ, abs_le]
    have hti := twR_qp_inr h he
    have hsl := (Mcl θ X₀ ω).slot_mono (show k + 1 ≤ j + 1 by omega)
    have e1 : slotF θ X₀ j ω = (Mcl θ X₀ ω).slot (j + 1) := rfl
    have e2 : slotF θ X₀ k ω = (Mcl θ X₀ ω).slot (k + 1) := rfl
    have hle := Finset.le_sup' (twR θ X₀ ω) (Finset.mem_image_of_mem qp hi)
    have hlt : (f.support.image qp).sup' hne (twR θ X₀ ω) < z := by
      rw [Finset.sup'_lt_iff]
      intro r hr
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hr
      exact hL i' hi'
    rw [hHk] at hb2
    simp only at hti
    constructor <;> linarith

end Filters

/-! ### The sums -/

section Sums

variable (θ X₀) in
/-- The box weight `1_{A_k} H_k⁻¹ 1[z ∈ box_k]` of the slot `k` at `z`. -/
noncomputable def bw (ω : JitterΩ) (k : ℕ) (z : ℝ) : ℝ≥0∞ :=
  (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
    (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 z) ω

lemma rhoT_eq_bw (ω : JitterΩ) (z : ℝ) : rhoT θ X₀ ω z = (∑' k, bw θ X₀ ω k z).toReal := rfl

lemma mem_box_of_bw {ω : JitterΩ} {k : ℕ} {z : ℝ} (hb : bw θ X₀ ω k z ≠ 0) :
    z ∈ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω) := by
  by_contra hz
  apply hb
  unfold bw
  by_cases hA : ω ∈ lawA θ X₀ k
  · rw [Set.indicator_of_mem hA]; simp [Set.indicator_of_notMem hz]
  · rw [Set.indicator_of_notMem hA]

/-- Sums over the labels `w ≥ 2` of `X₀⁻`-cut cofactors are sums over their exponent vectors. -/
lemma sum_labels (P : BeurlingSystem) (x : ℝ) (φ : ℕ → ℝ) [DecidablePred fun w : ℕ => 2 ≤ w] :
    ∑ w ∈ ((P.elems x).image iota).filter (2 ≤ ·), φ w =
      ∑ f ∈ (P.elems x).filter (fun f => 2 ≤ iota f), φ (iota f) := by
  rw [Finset.filter_image, Finset.sum_image fun a _ b _ hab => iota_injective hab]

lemma iota_zero : iota 0 = 1 := by unfold iota; simp

lemma ne_zero_of_two_le {f : ℕ →₀ ℕ} (hf : 2 ≤ iota f) : f ≠ 0 := by
  rintro rfl; rw [iota_zero] at hf; omega

lemma two_le_iota {f : ℕ →₀ ℕ} (hf : f ≠ 0) : 2 ≤ iota f := by
  have h0 := iota_pos f
  have h1 : iota f ≠ 1 := fun h1 => hf (iota_injective (h1.trans iota_zero.symm))
  omega

end Sums

section Comp

variable (hc : Cond θ X₀) {ω : JitterΩ} (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω))
include hc

open Classical in
set_option maxHeartbeats 2000000 in
/-- **The compensator density as a sum over the labelled cofactors** (§5.3): `c(y) = ∑_w
(∑_k 1[τ_w before s_k, y ∉ 𝒜 via y/w] 1_{A_k} H_k⁻¹ 1[y/w ∈ box_k]) / w`, over the exponent
vectors `f` of the realised system with `w = iota f ≥ 2`, `y/w ≥ X₀⁻`. -/
theorem compDen_eq (y : ℝ) :
    compDen θ X₀ ω y = ∑ f ∈ ((PR θ X₀ ω).elems (y / Xm X₀)).filter (fun f => 2 ≤ iota f),
      (∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
          y / (PR θ X₀ ω).val f < absorbY X₀ y) then bw θ X₀ ω k (y / (PR θ X₀ ω).val f)
        else 0) * ENNReal.ofReal ((PR θ X₀ ω).val f)⁻¹ := by
  set P := PR θ X₀ ω with hP
  set F := (P.elems (y / Xm X₀)).filter (fun f => 2 ≤ iota f) with hF
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hk : ∀ k, compTerm θ X₀ k ω y = ∑ f ∈ F,
      (if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
          y / P.val f < absorbY X₀ y) then bw θ X₀ ω k (y / P.val f) else 0) *
        ENNReal.ofReal (P.val f)⁻¹ := by
    intro k
    unfold compTerm
    set G : (PIdx X₀ →₀ ℕ) → ℝ≥0∞ := fun w => if w ∈ cofP θ X₀ k ω ∧
      Xm X₀ ≤ y / eval (DD θ X₀ ω) w ∧
      ¬ (10 ^ 7 ≤ Real.log y ∧ y / eval (DD θ X₀ ω) w < absorbY X₀ y) then
      (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (y / eval (DD θ X₀ ω) w) *
        ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0 with hG
    have hsupp : ∀ e ∉ F.image (EF h), G e = 0 := by
      intro e he
      simp only [hG]
      rw [if_neg]
      rintro ⟨⟨hlive, hne, -⟩, hcut, -⟩
      apply he
      obtain ⟨f, rfl⟩ := EF_surj h hlive
      refine Finset.mem_image.mpr ⟨f, ?_, rfl⟩
      rw [hF, Finset.mem_filter, mem_elems]
      have hpos := eval_pos hc hlive
      rw [EF_eval] at hcut hpos
      refine ⟨?_, two_le_iota fun h0 => hne (by rw [h0, EF_zero])⟩
      rw [le_div_iff₀ hXm0]
      rw [le_div_iff₀ hpos] at hcut
      linarith
    have hsum : ∑' e, G e = ∑ f ∈ F, G (EF h f) := by
      rw [tsum_eq_sum hsupp, Finset.sum_image fun a _ b _ hab => EF_injective h hab]
    have hGf : ∀ f ∈ F, G (EF h f) = (if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧
        ¬ (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y) then
        (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (y / P.val f) else 0) *
          ENNReal.ofReal (P.val f)⁻¹ := by
      intro f hf
      have hf' := Finset.mem_filter.mp hf
      have hf0 := ne_zero_of_two_le hf'.2
      have hval := (mem_elems (P := P)).mp hf'.1
      have hvp := P.val_pos f
      have hcut : Xm X₀ ≤ y / P.val f := by
        rw [le_div_iff₀ hvp]; rw [le_div_iff₀ hXm0] at hval; linarith
      simp only [hG, EF_eval]
      have hcof : EF h f ∈ cofP θ X₀ k ω ↔ ∀ j, EF h f (Sum.inr j) ≠ 0 → j < k :=
        ⟨fun h' => h'.2.2, fun h' => ⟨EF_live h f, EF_ne_zero h hf0, h'⟩⟩
      by_cases hC : (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧
          ¬ (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y)
      · rw [if_pos ⟨hcof.mpr hC.1, hcut, hC.2⟩, if_pos hC]
      · rw [if_neg (fun h' => hC ⟨hcof.mp h'.1, h'.2.2⟩), if_neg hC, zero_mul]
    by_cases hA : ω ∈ lawA θ X₀ k
    · rw [Set.indicator_of_mem hA]
      rw [← hG, hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [hGf f hf]
      unfold bw
      rw [Set.indicator_of_mem hA]
      split_ifs <;> simp [mul_assoc]
    · rw [Set.indicator_of_notMem hA]
      symm
      refine Finset.sum_eq_zero fun f _ => ?_
      unfold bw
      rw [Set.indicator_of_notMem hA]
      simp
  unfold compDen
  rw [tsum_congr hk, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [ENNReal.tsum_mul_right]

end Comp

section Main

variable (hc : Cond θ X₀) {ω : JitterΩ} (h : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω))
include hc

open Classical in
omit hc in
lemma r_le (f : ℕ →₀ ℕ) (y : ℝ) :
    (∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
        y / (PR θ X₀ ω).val f < absorbY X₀ y) then bw θ X₀ ω k (y / (PR θ X₀ ω).val f)
      else 0) ≤ ∑' k, bw θ X₀ ω k (y / (PR θ X₀ ω).val f) :=
  ENNReal.tsum_le_tsum fun k => by split_ifs <;> simp

open Classical in
/-- Off the `τ`-near cofactors, the slot-filtered box weight is the landing-filtered one. -/
lemma r_eq {f : ℕ →₀ ℕ} (hf : f ≠ 0) {y : ℝ} (hz : Xm X₀ ≤ y / (PR θ X₀ ω).val f)
    (hnear : ¬ TauNearAt (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y (iota f)) :
    (∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
        y / (PR θ X₀ ω).val f < absorbY X₀ y) then bw θ X₀ ω k (y / (PR θ X₀ ω).val f)
      else 0) =
      if (∀ i ∈ f.support, twR θ X₀ ω (qp i) < y / (PR θ X₀ ω).val f) ∧ ¬ (10 ^ 7 ≤
        Real.log y ∧ y / (PR θ X₀ ω).val f < absorbY X₀ y) then
        ∑' k, bw θ X₀ ω k (y / (PR θ X₀ ω).val f) else 0 := by
  have hterm : ∀ k, (if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
        y / (PR θ X₀ ω).val f < absorbY X₀ y) then bw θ X₀ ω k (y / (PR θ X₀ ω).val f)
      else 0) =
      if (∀ i ∈ f.support, twR θ X₀ ω (qp i) < y / (PR θ X₀ ω).val f) ∧ ¬ (10 ^ 7 ≤
        Real.log y ∧ y / (PR θ X₀ ω).val f < absorbY X₀ y) then
        bw θ X₀ ω k (y / (PR θ X₀ ω).val f) else 0 := by
    intro k
    by_cases hb : bw θ X₀ ω k (y / (PR θ X₀ ω).val f) = 0
    · simp [hb]
    · have hag := filters_agree hc h hf hz (mem_box_of_bw hb) hnear (k := k)
      simp only [hag]
  rw [tsum_congr hterm]
  split_ifs <;> simp

end Main

section Final

variable (hc : Cond θ X₀)
include hc

omit hc in
lemma land_iff (ω : JitterΩ) {f : ℕ →₀ ℕ} {y : ℝ} :
    (∀ p ∈ (iota f).primeFactors, twR θ X₀ ω p * (PR θ X₀ ω).val f < y) ↔
      ∀ i ∈ f.support, twR θ X₀ ω (qp i) < y / (PR θ X₀ ω).val f := by
  rw [primeFactors_iota, Finset.forall_mem_image]
  have hv := (PR θ X₀ ω).val_pos f
  exact forall₂_congr fun i _ => (lt_div_iff₀ hv).symm

lemma bw_sum_le (hev : Even X₀) (ω : JitterΩ) (z : ℝ) : ∑' k, bw θ X₀ ω k z ≤ 2 :=
  law_slots hc hev ω z

set_option maxHeartbeats 4000000 in
/-- **Eq. (NT)** (§5.3, 04b-identity.tex): `|NT_pt(y)| ≤ 2 η(y)`, `η(y) = ∑_{w τ-near at y} 1/w`.
`NT_pt = c - K_pt ρ̃ + K_𝒜 ρ̃` replaces the slot filter by the landing filter on the
non-absorbed part; the two agree off the `τ`-near cofactors (`filters_agree`), and on those both
sides lie in `[0, ρ̃(y/w)/w]` with `ρ̃ ≤ 2` ((F1), `law_slots`). -/
theorem NTpt_abs_le_eta (hev : Even X₀) (ω : JitterΩ) (y : ℝ) :
    |NTpt θ X₀ ω y| ≤
      2 * KR.etaG (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (fun _ => 1) y := by
  classical
  have h := realisedOK_Mcl hc ω
  set P := PR θ X₀ ω with hP
  set F := (P.elems (y / Xm X₀)).filter (fun f => 2 ≤ iota f) with hF
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hVl : ∀ f, Vl P (iota f) = P.val f := fun f => P.valN_iota f
  -- the four sums over `F`
  have hc1 : (compDen θ X₀ ω y).toReal = ∑ f ∈ F, (∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 →
      j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y) then
        bw θ X₀ ω k (y / P.val f) else 0).toReal * (P.val f)⁻¹ := by
    rw [compDen_eq hc h y, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun f _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (P.val_pos f).le)]
    · intro f _
      refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ ((r_le h f y).trans
        (bw_sum_le hc hev ω _))) ENNReal.ofReal_ne_top
      exact ENNReal.ofNat_ne_top
  have hK : KptR θ X₀ ω (rhoT θ X₀ ω) y = ∑ f ∈ F,
      if (∀ p ∈ (iota f).primeFactors, twR θ X₀ ω p * P.val f < y) then
        rhoT θ X₀ ω (y / P.val f) / P.val f else 0 := by
    unfold KptR KR.Sharp.Kpt KR.NAll
    rw [sum_labels]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hVl]
  have hA : KAbsR θ X₀ ω (rhoT θ X₀ ω) y = ∑ f ∈ F,
      if (∀ p ∈ (iota f).primeFactors, twR θ X₀ ω p * P.val f < y) ∧
        (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y) then
        rhoT θ X₀ ω (y / P.val f) / P.val f else 0 := by
    unfold KAbsR KR.NAll
    rw [sum_labels]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hVl]
  have hη : KR.etaG P (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (fun _ => 1) y = ∑ f ∈ F,
      if TauNearAt P (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y (iota f) then 1 / P.val f
        else 0 := by
    unfold KR.etaG KR.Cof
    rw [Finset.sum_filter, sum_labels]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hVl]
  have hN : NTpt θ X₀ ω y = ∑ f ∈ F, ((∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 →
      j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y) then
        bw θ X₀ ω k (y / P.val f) else 0).toReal * (P.val f)⁻¹ -
      (if (∀ p ∈ (iota f).primeFactors, twR θ X₀ ω p * P.val f < y) then
        rhoT θ X₀ ω (y / P.val f) / P.val f else 0) +
      (if (∀ p ∈ (iota f).primeFactors, twR θ X₀ ω p * P.val f < y) ∧
        (10 ^ 7 ≤ Real.log y ∧ y / P.val f < absorbY X₀ y) then
        rhoT θ X₀ ω (y / P.val f) / P.val f else 0)) := by
    unfold NTpt
    rw [hc1, hK, hA, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hN, hη, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f hf => ?_)
  -- one cofactor
  have hf' := Finset.mem_filter.mp hf
  have hf0 := ne_zero_of_two_le hf'.2
  have hval := (mem_elems (P := P)).mp hf'.1
  have hvp := P.val_pos f
  have hcut : Xm X₀ ≤ y / P.val f := by
    rw [le_div_iff₀ hvp]; rw [le_div_iff₀ hXm0] at hval; linarith
  set z := y / P.val f with hz
  set R := ∑' k, bw θ X₀ ω k z with hR
  have hR2 : R ≤ 2 := bw_sum_le hc hev ω z
  have hRt : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hR2
  have hρ : rhoT θ X₀ ω z = R.toReal := rhoT_eq_bw ω z
  have hρ2 : R.toReal ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by rw [ENNReal.ofReal_ofNat]; exact hR2)
  have hρ0 : 0 ≤ R.toReal := ENNReal.toReal_nonneg
  have hiv : 0 < (P.val f)⁻¹ := inv_pos.mpr hvp
  have hl := land_iff (θ := θ) (X₀ := X₀) ω (f := f) (y := y)
  rw [← hP, ← hz] at hl
  simp only [hl]
  have hdiv : R.toReal / P.val f = R.toReal * (P.val f)⁻¹ := div_eq_mul_inv _ _
  rw [hρ, hdiv]
  by_cases hn : TauNearAt P (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y (iota f)
  · rw [if_pos hn]
    set r := (∑' k, if (∀ j, EF h f (Sum.inr j) ≠ 0 → j < k) ∧ ¬ (10 ^ 7 ≤ Real.log y ∧
      z < absorbY X₀ y) then bw θ X₀ ω k z else 0) with hr
    have hr1 : r.toReal ≤ R.toReal := ENNReal.toReal_mono hRt (r_le h f y)
    have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    have e : 2 * (1 / P.val f) = 2 * (P.val f)⁻¹ := by rw [one_div]
    rw [e, abs_le]
    have a1 : r.toReal * (P.val f)⁻¹ ≤ R.toReal * (P.val f)⁻¹ :=
      mul_le_mul_of_nonneg_right hr1 hiv.le
    have a2 : R.toReal * (P.val f)⁻¹ ≤ 2 * (P.val f)⁻¹ := mul_le_mul_of_nonneg_right hρ2 hiv.le
    have a0 : 0 ≤ r.toReal * (P.val f)⁻¹ := mul_nonneg hr0 hiv.le
    split_ifs <;> first | (constructor <;> linarith) | (exfalso; tauto)
  · rw [if_neg hn, r_eq hc h hf0 hcut hn, mul_zero]
    by_cases hL : ∀ i ∈ f.support, twR θ X₀ ω (qp i) < z
    · by_cases hab : 10 ^ 7 ≤ Real.log y ∧ z < absorbY X₀ y
      · rw [if_neg (fun h' => h'.2 hab), if_pos hL, if_pos ⟨hL, hab⟩]; simp
      · rw [if_pos ⟨hL, hab⟩, if_pos hL, if_neg (fun h' => hab h'.2), add_zero, sub_self,
          abs_zero]
    · rw [if_neg (fun h' => hL h'.1), if_neg hL, if_neg (fun h' => hL h'.1)]; simp

end Final

end BModel

end
