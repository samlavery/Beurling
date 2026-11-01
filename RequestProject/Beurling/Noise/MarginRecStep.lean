module

public import RequestProject.Beurling.Noise.MarginRecSuper

/-!
# Proposition 5.38, Steps 1–3: the recursion for the variation of the margin

The pointwise margin density is `m = T' - K_pt ρ̃ - NT_pt` (`K_pt` is the realised operator
`KR.Sharp.Kpt`, applied to the jitter-smoothed slot density `ρ̃`, which vanishes below `X₀⁻`),
and its variation `v(t) = sup_{|h| ≤ 1.01 H(t)} |m(t+h) - m(t)|` (we only use that `v` is an
upper envelope: `|m(x + h) - m(x)| ≤ v(x)` for `|h| ≤ 1.01 H(x)`).

* `step2_assembly` : **Step 2** (04g-margin.tex lines 77–123) from its bullets: the exact form
  with the weights, `|H(z)(ρ̃(z+s) - ρ̃(z)) - (σ(A₊) - σ(A₋))| ≤ 3.3 δ_z H(z)`; Step 1 (Lemma 5.22),
  `σ(A±) = ∫_{A±} m + E(A±)`, `|E(A±)| ≤ ε`; the strip comparison
  `|∫_{A±} m - ∫_{I±} m| ≤ 1.05 δ_z H m*`; and the shift bound `|m(x + H(z)) - m(x)| ≤ b` on the
  lower strip. Conclusion: `|Δ_s ρ̃(z)| ≤ (s/H(z)) b + 2ε/H(z) + (3.3 + 2.1 m*) δ_z`;
* `abs_m_le` : `|m(y)| ≤ 3.03 log y + 4.02` from `|T'| ≤ 2`, `0 ≤ K_pt ρ̃ ≤ 1.01 log y` and
  `|NT_pt| ≤ 2.02 (log y + 1)`; `rem_le_delta` : `(3.3 + 2.1 m*) δ_z ≤ δ(z) = 6.6 ε_H (H/z) log z`;
* `Step2At` : the Step-2 conclusion at `z` (the form used by Step 3);
* `Kpt_diff` : the exact difference of `K_pt g` between two points for `g` vanishing below
  `X₀⁻` (the cut-off switches nothing on): the shifted terms plus the filter switching;
* `step3_pointwise`, `recIneq_of` : **Step 3**: the recursion `Margin.Var.RecIneq` with
  `c_w = 1.0101 κ_w w^{ε-2}` and `S(t) = o_t + 2η(t) + ∑_w e_w/w`, from Step 2 at `t/w` and at
  `z' = t/w - |h|/w`, the oscillation of `T'`, the filter-switching / `NT` cost `≤ 2η(t)`, and
  the regularity of `H`.

The construction facts enter as hypotheses, each the paper's statement: the exact form and
the weights of Step 2 (slot structure of §3.4, centred half-open boxes), Step 1 (Lemma 5.22 on
`Good(< max I + H(u))`), the strip comparison (position and length of `A±`), the bounds
`|T'| ≤ 2`, `K_pt ρ̃ ≤ 1.01 log y`, `|NT_pt| ≤ 2.02 η` on `Good(< t)` ((HBS) and Lemma
`lem:rhoA`), the
filter-switching cost `≤ 2η(t)` (τ-near steps), and `H(t/w) ≤ (1 + 10⁻⁹) H(z')` for the negative
shifts.
-/

@[expose] public section

open Finset Real MeasureTheory Set

namespace Margin.Rec

/-! ## Step 2 -/

/-- **Step 2, assembled from its bullets.** -/
theorem step2_assembly {H m ρ : ℝ → ℝ} {z s b ε δz mst σp σm Ep Em JAp JAm : ℝ}
    (hH : 0 < H z) (hs0 : 0 ≤ s)
    (hex : |H z * (ρ (z + s) - ρ z) - (σp - σm)| ≤ 3.3 * δz * H z)
    (hσp : σp = JAp + Ep) (hσm : σm = JAm + Em) (hEp : |Ep| ≤ ε) (hEm : |Em| ≤ ε)
    (hJp : |JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst)
    (hJm : |JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst)
    (hmi : IntervalIntegrable m volume (z - H z / 2) (z + H z / 2 + s))
    (hshift : ∀ x ∈ Icc (z - H z / 2) (z - H z / 2 + s), |m (x + H z) - m x| ≤ b) :
    |ρ (z + s) - ρ z| ≤ s / H z * b + 2 * ε / H z + (3.3 + 2.1 * mst) * δz := by
  set a := z - H z / 2 with ha
  have hHa : a + H z = z + H z / 2 := by rw [ha]; ring
  -- the strip difference is an integral of increments
  have hi1 : IntervalIntegrable (fun x => m (x + H z)) volume a (a + s) := by
    have : IntervalIntegrable m volume (a + H z) (a + s + H z) :=
      hmi.mono_set (by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc (by linarith) (by linarith))
    simpa using this.comp_add_right (H z)
  have hi2 : IntervalIntegrable m volume a (a + s) :=
    hmi.mono_set (by
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hD : (∫ r in (z + H z / 2)..(z + H z / 2 + s), m r) -
      ∫ r in a..(a + s), m r = ∫ x in a..(a + s), (m (x + H z) - m x) := by
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_comp_add_right m,
      hHa, show a + s + H z = z + H z / 2 + s by rw [ha]; ring]
  have hDb : |∫ x in a..(a + s), (m (x + H z) - m x)| ≤ b * s := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + s)
      (C := b) (f := fun x => m (x + H z) - m x) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs]; exact hshift x ⟨hx.1.le, hx.2⟩)
    rw [Real.norm_eq_abs, show |a + s - a| = s by rw [add_sub_cancel_left, abs_of_nonneg hs0]]
      at this
    exact this
  -- assemble
  have hmain : |H z * (ρ (z + s) - ρ z)| ≤ b * s + 2 * ε + 3.3 * δz * H z +
      2.1 * δz * H z * mst := by
    have e : H z * (ρ (z + s) - ρ z) =
        (H z * (ρ (z + s) - ρ z) - (σp - σm)) + (Ep - Em) +
          ((JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r) -
            (JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r)) +
          ∫ x in a..(a + s), (m (x + H z) - m x) := by
      rw [← hD, hσp, hσm, ← ha]; ring
    rw [e]
    have t1 := abs_add_le (H z * (ρ (z + s) - ρ z) - (σp - σm) + (Ep - Em) +
      ((JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r) -
        (JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r)))
      (∫ x in a..(a + s), (m (x + H z) - m x))
    have t2 := abs_add_le (H z * (ρ (z + s) - ρ z) - (σp - σm) + (Ep - Em))
      ((JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r) -
        (JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r))
    have t3 := abs_add_le (H z * (ρ (z + s) - ρ z) - (σp - σm)) (Ep - Em)
    have t4 := abs_sub (JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r)
      (JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r)
    have t5 := abs_sub Ep Em
    linarith
  rw [abs_mul, abs_of_pos hH] at hmain
  rw [← mul_le_mul_iff_of_pos_left hH]
  have e2 : H z * (s / H z * b + 2 * ε / H z + (3.3 + 2.1 * mst) * δz) =
      b * s + 2 * ε + 3.3 * δz * H z + 2.1 * δz * H z * mst := by
    field_simp; ring
  rw [e2]; exact hmain

/-- `|m(y)| ≤ 3.03 log y + 4.02` from `|T'(y)| ≤ 2`, `0 ≤ (K_pt ρ̃)(y) ≤ 1.01 log y` and
`|NT_pt(y)| ≤ 2.02 (log y + 1)`. -/
lemma abs_m_le {Tp K NT L : ℝ} (hT : |Tp| ≤ 2) (hK0 : 0 ≤ K) (hK : K ≤ 1.01 * L)
    (hNT : |NT| ≤ 2.02 * (L + 1)) : |Tp - K - NT| ≤ 3.03 * L + 4.02 := by
  have h1 : |Tp - K - NT| ≤ |Tp| + |K| + |NT| := by
    have := abs_sub (Tp - K) NT
    have := abs_sub Tp K
    linarith
  rw [abs_of_nonneg hK0] at h1
  linarith

/-- The Step-2 remainder: `(3.3 + 2.1 m*) δ_z ≤ δ(z) = 6.6 ε_H (H(z)/z) log z` for
`m* ≤ 3.1 log z + 4.2` and `log z ≥ 10⁸`, with `δ_z = ε_H H(z)/z`. -/
lemma rem_le_delta {εH Hz z mst : ℝ} (hεH : 0 ≤ εH) (hHz : 0 ≤ Hz) (hz : 0 < z)
    (hm : mst ≤ 3.1 * Real.log z + 4.2) (hlog : 100000000 ≤ Real.log z) :
    (3.3 + 2.1 * mst) * (εH * Hz / z) ≤ 6.6 * εH * (Hz / z) * Real.log z := by
  have hq : 0 ≤ εH * Hz / z := by positivity
  have h1 : 3.3 + 2.1 * mst ≤ 6.6 * Real.log z := by nlinarith
  calc (3.3 + 2.1 * mst) * (εH * Hz / z) ≤ 6.6 * Real.log z * (εH * Hz / z) :=
        mul_le_mul_of_nonneg_right h1 hq
    _ = 6.6 * εH * (Hz / z) * Real.log z := by ring

/-- **The conclusion of Step 2 at `z`**, in the form used by Step 3: for `0 ≤ s ≤ 1.01 H(z)` and
any bound `b ≥ v` on `[z - H(z), z + 0.6 H(z)]`,
`|ρ̃(z+s) - ρ̃(z)| ≤ (s/H(z)) b + err(z)` (`err(z) = 2ε_{1.0001s}(z)/H(z) + δ(z)`). -/
def Step2At (H ρ v err : ℝ → ℝ) (z : ℝ) : Prop :=
  ∀ s, 0 ≤ s → s ≤ 1.01 * H z → ∀ b : ℝ, (∀ x ∈ Icc (z - H z) (z + 0.6 * H z), v x ≤ b) →
    |ρ (z + s) - ρ z| ≤ s / H z * b + err z

/-- Step 2's bullets give `Step2At`: the shift bound comes from the envelope `v`, since the
strip shift `H(z)` is at most `1.01 H(x)` on the lower strip (`hHx`). -/
theorem step2At_of {H m ρ v err : ℝ → ℝ} {z : ℝ} (hH : 0 < H z)
    (hv : ∀ x hh, |hh| ≤ 1.01 * H x → |m (x + hh) - m x| ≤ v x)
    (hHx : ∀ x ∈ Icc (z - H z / 2) (z + 0.51 * H z), H z ≤ 1.01 * H x)
    (hmi : ∀ s, 0 ≤ s → s ≤ 1.01 * H z →
      IntervalIntegrable m volume (z - H z / 2) (z + H z / 2 + s))
    (hbul : ∀ s, 0 ≤ s → s ≤ 1.01 * H z → ∃ ε δz mst σp σm Ep Em JAp JAm : ℝ,
      |H z * (ρ (z + s) - ρ z) - (σp - σm)| ≤ 3.3 * δz * H z ∧
      σp = JAp + Ep ∧ σm = JAm + Em ∧ |Ep| ≤ ε ∧ |Em| ≤ ε ∧
      |JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst ∧
      |JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst ∧
      2 * ε / H z + (3.3 + 2.1 * mst) * δz ≤ err z) :
    Step2At H ρ v err z := by
  intro s hs0 hs b hb
  obtain ⟨ε, δz, mst, σp, σm, Ep, Em, JAp, JAm, hex, hσp, hσm, hEp, hEm, hJp, hJm, herr⟩ :=
    hbul s hs0 hs
  have hshift : ∀ x ∈ Icc (z - H z / 2) (z - H z / 2 + s), |m (x + H z) - m x| ≤ b := by
    intro x hx
    have hx' : x ∈ Icc (z - H z / 2) (z + 0.51 * H z) := ⟨hx.1, by linarith [hx.2]⟩
    have h1 := hv x (H z) (by rw [abs_of_pos hH]; exact hHx x hx')
    exact h1.trans (hb x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have := step2_assembly hH hs0 hex hσp hσm hEp hEm hJp hJm (hmi s hs0 hs) hshift
  linarith

/-! ## The difference of `K_pt` -/

open scoped Classical in
/-- `K_pt g` for `g` vanishing below `X₀⁻`, at a point `y ≤ 2t`, summed over the levels with
`t/w ≥ X₀⁻/2` (the extra terms have `y/w < X₀⁻`). -/
lemma Kpt_eq_big (P : BeurlingSystem) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {g : ℝ → ℝ}
    (hg : ∀ z, z < X0m → g z = 0) {y t : ℝ} (hyt : y ≤ 2 * t) :
    KR.Sharp.Kpt P tw X0m g y = ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
      (if ∀ p ∈ w.primeFactors, tw p * KR.Vl P w < y then g (y / KR.Vl P w) / KR.Vl P w
        else 0) := by
  unfold KR.Sharp.Kpt
  have hX2 : 0 < X0m / 2 := by linarith
  apply Finset.sum_subset
  · intro w hw
    obtain ⟨hwA, hw2⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨?_, hw2⟩
    obtain ⟨hw0, hwc⟩ := (mem_NAll_iff' hX).mp hwA
    refine (mem_NAll_iff' hX2).mpr ⟨hw0, ?_⟩
    have hV := Vv_pos (P := P) w
    have : y / KR.Vl P w ≤ 2 * t / KR.Vl P w := div_le_div_of_nonneg_right hyt hV.le
    have e : X0m / 2 ≤ t / KR.Vl P w ↔ X0m ≤ 2 * t / KR.Vl P w := by
      rw [mul_div_assoc]; constructor <;> intro h <;> linarith
    exact e.mpr (hwc.trans this)
  · intro w hw hnot
    obtain ⟨hwA, hw2⟩ := Finset.mem_filter.mp hw
    have hw0 := ((mem_NAll_iff' hX2).mp hwA).1
    have hlt : y / KR.Vl P w < X0m := by
      by_contra hc; push_neg at hc
      exact hnot (Finset.mem_filter.mpr ⟨(mem_NAll_iff' hX).mpr ⟨hw0, hc⟩, hw2⟩)
    split_ifs
    · rw [hg _ hlt, zero_div]
    · rfl

open scoped Classical in
/-- **The difference of `K_pt g`** (Step 3): for `g` vanishing below `X₀⁻` and `t' ≤ 2t`,
`K_pt g(t') - K_pt g(t) = ∑_w κ_w(t) (g(t'/w) - g(t/w))/w + ∑_w (κ_w(t') - κ_w(t)) g(t'/w)/w`,
`κ_w(y) = 1[τ_w < y/w]`, over the levels `w ≥ 2` with `t/w ≥ X₀⁻/2`. The second sum is the
filter switching. -/
lemma Kpt_diff (P : BeurlingSystem) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {g : ℝ → ℝ}
    (hg : ∀ z, z < X0m → g z = 0) {t t' : ℝ} (ht : 0 ≤ t) (ht' : t' ≤ 2 * t) :
    KR.Sharp.Kpt P tw X0m g t' - KR.Sharp.Kpt P tw X0m g t =
      ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
        (if ∀ p ∈ w.primeFactors, tw p * KR.Vl P w < t then (1 : ℝ) else 0) *
          ((g (t' / KR.Vl P w) - g (t / KR.Vl P w)) / KR.Vl P w) +
      ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
        ((if ∀ p ∈ w.primeFactors, tw p * KR.Vl P w < t' then (1 : ℝ) else 0) -
          (if ∀ p ∈ w.primeFactors, tw p * KR.Vl P w < t then (1 : ℝ) else 0)) *
          (g (t' / KR.Vl P w) / KR.Vl P w) := by
  rw [Kpt_eq_big P tw hX hg (y := t) (t := t) (by linarith), Kpt_eq_big P tw hX hg ht',
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

/-! ## Step 3 -/

open scoped Classical in
/-- The filter `κ_w(y) = 1[τ_w < y/w]` as a real number. -/
noncomputable def kap (P : BeurlingSystem) (tw : ℕ → ℝ) (y : ℝ) (w : ℕ) : ℝ :=
  if ∀ p ∈ w.primeFactors, tw p * KR.Vl P w < y then 1 else 0

lemma kap_mem (P : BeurlingSystem) (tw : ℕ → ℝ) (y : ℝ) (w : ℕ) :
    0 ≤ kap P tw y w ∧ kap P tw y w ≤ 1 := by
  unfold kap; split_ifs <;> norm_num

/-- The regularity of `H` used in Step 3 at one cofactor (from (RH) and `H(y)/y ≤ 10⁻¹⁰`
above `X₀⁻/2`): the shift `|h| ≤ 1.01 H(t)` compresses to `|h|/w ≤ 1.01 w^{ε-1} H(t/w)`; for
the negative shifts, the points `z' ∈ [t/w - 0.52 H(t/w), t/w]` have
`H(z') ≤ H(t/w) ≤ (1 + 10⁻⁹) H(z')`. -/
structure HStep (H : ℝ → ℝ) (ε t y w : ℝ) : Prop where
  compress : ∀ hh, |hh| ≤ 1.01 * H t → |hh| / w ≤ 1.01 * w ^ (ε - 1) * H y
  neg_ratio : ∀ z', y - 0.52 * H y ≤ z' → z' ≤ y → H y ≤ (1 + 1 / 10 ^ 9) * H z'
  neg_le : ∀ z', y - 0.52 * H y ≤ z' → z' ≤ y → H z' ≤ H y
  pos : 0 < H y

/-- `w^{ε-1} ≤ 0.505` for `w ≥ 2`, `ε ≤ 0.01`. -/
lemma rpow_le_0505 {ε W : ℝ} (hε : ε ≤ 0.01) (hW : 2 ≤ W) : W ^ (ε - 1) ≤ 0.505 := by
  have hr1 : W ^ (ε - 1) ≤ 2 ^ (ε - 1) :=
    Real.rpow_le_rpow_of_nonpos two_pos hW (by linarith)
  have hr2 : (2 : ℝ) ^ (ε - 1) ≤ 2 ^ ((0.01 : ℝ) + (-1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hb := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num)
    (p := (0.01 : ℝ)) (by norm_num) (by norm_num)
  have hr3 : (2 : ℝ) ^ ((0.01 : ℝ) + (-1)) ≤ 0.505 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_neg_one]
    norm_num at hb ⊢
    linarith
  linarith

/-- One cofactor of Step 3: `κ_w |ρ̃(t'/w) - ρ̃(t/w)|/w ≤ 1.0101 κ_w w^{ε-2} b_w + e_w/w`. -/
lemma step3_term {H ρ v err : ℝ → ℝ} {ε t hh y W b e κ : ℝ} (hε : ε ≤ 0.01) (hW : 2 ≤ W)
    (hy : y = t / W) (hg : HStep H ε t y W) (hh1 : |hh| ≤ 1.01 * H t)
    (hS2 : ∀ z', y - 0.52 * H y ≤ z' → z' ≤ y → Step2At H ρ v err z' ∧ err z' ≤ e)
    (hb : ∀ x ∈ Icc (y - 2.1 * H y) (y + 2.1 * H y), v x ≤ b) (hb0 : 0 ≤ b)
    (hκ : 0 ≤ κ ∧ κ ≤ 1) (he0 : 0 ≤ e) :
    κ * (|ρ ((t + hh) / W) - ρ (t / W)| / W) ≤
      1.0101 * κ * W ^ (ε - 2) * b + e / W := by
  have hW0 : 0 < W := by linarith
  have hHy := hg.pos
  have hcomp := hg.compress hh hh1
  set s := |hh| / W with hs
  have hs0 : 0 ≤ s := div_nonneg (abs_nonneg _) hW0.le
  have hWr : W ^ (ε - 1) ≤ 0.505 := rpow_le_0505 hε hW
  have hWr0 : 0 ≤ W ^ (ε - 1) := Real.rpow_nonneg hW0.le _
  have hWb : 0 ≤ W ^ (ε - 1) * b := mul_nonneg hWr0 hb0
  have hsH : s ≤ 0.51005 * H y := by
    have : 1.01 * W ^ (ε - 1) * H y ≤ 1.01 * 0.505 * H y :=
      mul_le_mul_of_nonneg_right (by linarith) hHy.le
    linarith
  have hpowW : W ^ (ε - 2) = W ^ (ε - 1) / W := by
    rw [show ε - 2 = (ε - 1) - 1 by ring, Real.rpow_sub_one hW0.ne']
  have hΔ : |ρ ((t + hh) / W) - ρ (t / W)| ≤ 1.0101 * (W ^ (ε - 1) * b) + e := by
    rcases le_or_gt 0 hh with hpos | hneg
    · have hsdef : s = hh / W := by rw [hs, abs_of_nonneg hpos]
      have e1 : (t + hh) / W = y + s := by rw [hsdef, hy, add_div]
      obtain ⟨h2, herr⟩ := hS2 y (by linarith) le_rfl
      have hsy : s ≤ 1.01 * H y := by linarith
      have hbound := h2 s hs0 hsy b (fun x hx => hb x ⟨by linarith [hx.1],
        by linarith [hx.2]⟩)
      rw [e1, ← hy]
      have hq : s / H y * b ≤ 1.01 * (W ^ (ε - 1) * b) := by
        have h1 : s / H y ≤ 1.01 * W ^ (ε - 1) := by
          rw [div_le_iff₀ hHy]; linarith
        have := mul_le_mul_of_nonneg_right h1 hb0
        linarith
      linarith
    · have hsdef : s = -hh / W := by rw [hs, abs_of_neg hneg]
      set z' := y - s with hz'
      have hz1 : y - 0.52 * H y ≤ z' := by rw [hz']; linarith
      have hz2 : z' ≤ y := by rw [hz']; linarith
      have e1 : (t + hh) / W = z' := by rw [hz', hsdef, hy]; ring
      have e2 : t / W = z' + s := by rw [hz', hy]; ring
      obtain ⟨h2, herr⟩ := hS2 z' hz1 hz2
      have hrat := hg.neg_ratio z' hz1 hz2
      have hle := hg.neg_le z' hz1 hz2
      have hHz' : 0 < H z' := by
        by_contra hc; push_neg at hc
        have : (1 + 1 / 10 ^ 9 : ℝ) * H z' ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by norm_num) hc
        linarith
      have hsz : s ≤ 1.01 * H z' := by
        have : (0.51005 : ℝ) * H y ≤ 0.51005 * ((1 + 1 / 10 ^ 9) * H z') :=
          mul_le_mul_of_nonneg_left hrat (by norm_num)
        nlinarith
      have hbound := h2 s hs0 hsz b (fun x hx => hb x ⟨by linarith [hx.1],
        by linarith [hx.2]⟩)
      rw [e1, e2, abs_sub_comm]
      have hq : s / H z' * b ≤ 1.0101 * (W ^ (ε - 1) * b) := by
        have h1 : s / H z' ≤ 1.0101 * W ^ (ε - 1) := by
          rw [div_le_iff₀ hHz']
          have : 1.01 * W ^ (ε - 1) * H y ≤
              1.01 * W ^ (ε - 1) * ((1 + 1 / 10 ^ 9) * H z') :=
            mul_le_mul_of_nonneg_left hrat (by positivity)
          have h3 : 1.01 * W ^ (ε - 1) * ((1 + 1 / 10 ^ 9) * H z') ≤
              1.0101 * W ^ (ε - 1) * H z' := by
            have := mul_nonneg hWr0 hHz'.le
            nlinarith
          linarith
        have := mul_le_mul_of_nonneg_right h1 hb0
        linarith
      linarith
  calc κ * (|ρ ((t + hh) / W) - ρ (t / W)| / W)
      ≤ κ * ((1.0101 * (W ^ (ε - 1) * b) + e) / W) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hΔ hW0.le) hκ.1
    _ = κ * (1.0101 * W ^ (ε - 2) * b) + κ * (e / W) := by rw [hpowW]; ring
    _ ≤ 1.0101 * κ * W ^ (ε - 2) * b + e / W := by
        have : κ * (e / W) ≤ 1 * (e / W) :=
          mul_le_mul_of_nonneg_right hκ.2 (div_nonneg he0 hW0.le)
        linarith

/-- **Step 3, pointwise.** Let `m = T' - K_pt ρ̃ - NT_pt` with `ρ̃ = 0` below `X₀⁻`, and let
`F` be the cofactors `w ≥ 2` with `t/w ≥ X₀⁻/2`. Fix `|h| ≤ 1.01 H(t)` with `0 ≤ t + h ≤ 2t`.
Assume, for every `w ∈ F`: the shift geometry `HStep`; Step 2 at the points
`z' ∈ [t/w - 0.52 H(t/w), t/w]` with error at most `e_w ≥ 0`; and `v ≤ b_w` on
`|t' - t/w| ≤ 2.1 H(t/w)`. Assume `|T'(t+h) - T'(t)| ≤ o_t`, and that the filter switching plus
`|NT(t+h) - NT(t)|` is at most `2η(t)`. Then
`|m(t+h) - m(t)| ≤ o_t + 2η(t) + ∑_w e_w/w + ∑_w 1.0101 κ_w(t) w^{ε-2} b_w`. -/
theorem step3_pointwise (P : BeurlingSystem) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m)
    {H Tp NT ρ v err : ℝ → ℝ} {ε o η : ℝ} (hε : ε ≤ 0.01) (hp2 : ∀ i, 2 ≤ P.p i)
    (hρ : ∀ z, z < X0m → ρ z = 0) {t hh : ℝ} (ht0 : 0 ≤ t) (hth : t + hh ≤ 2 * t)
    (hh1 : |hh| ≤ 1.01 * H t) (e b : ℕ → ℝ)
    (hgeom : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
      HStep H ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ v err z' ∧ err z' ≤ e w)
    (he0 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), 0 ≤ e w)
    (hb : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), ∀ x ∈
      Icc (t / KR.Vl P w - 2.1 * H (t / KR.Vl P w)) (t / KR.Vl P w + 2.1 * H (t / KR.Vl P w)),
        v x ≤ b w)
    (hb0 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), 0 ≤ b w)
    (hosc : |Tp (t + hh) - Tp t| ≤ o)
    (hsw : |∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
        (kap P tw (t + hh) w - kap P tw t w) * (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| +
      |NT (t + hh) - NT t| ≤ 2 * η) :
    |(Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
        (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t)| ≤
      o + 2 * η + ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), e w / KR.Vl P w +
        ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
          1.0101 * kap P tw t w * KR.Vl P w ^ (ε - 2) * b w := by
  classical
  set F := (KR.NAll P t (X0m / 2)).filter (2 ≤ ·)
  have hK := Kpt_diff P tw hX hρ ht0 hth
  set A := ∑ w ∈ F, kap P tw t w * ((ρ ((t + hh) / KR.Vl P w) - ρ (t / KR.Vl P w)) /
    KR.Vl P w)
  set SW := ∑ w ∈ F, (kap P tw (t + hh) w - kap P tw t w) *
    (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)
  have hK' : KR.Sharp.Kpt P tw X0m ρ (t + hh) - KR.Sharp.Kpt P tw X0m ρ t = A + SW := by
    rw [hK]; rfl
  have hA : |A| ≤ ∑ w ∈ F, (1.0101 * kap P tw t w * KR.Vl P w ^ (ε - 2) * b w +
      e w / KR.Vl P w) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w hw => ?_)
    have hw2 := (Finset.mem_filter.mp hw).2
    have hV2 := two_le_Vv hp2 hw2
    have hk := kap_mem P tw t w
    rw [abs_mul, abs_of_nonneg hk.1, abs_div, abs_of_pos (Vv_pos (P := P) w)]
    exact step3_term hε hV2 rfl (hgeom w hw) hh1 (hS2 w hw) (hb w hw) (hb0 w hw) hk
      (he0 w hw)
  have e1 : (Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
      (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t) =
      (Tp (t + hh) - Tp t) - A - (SW + (NT (t + hh) - NT t)) := by
    rw [show (Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
      (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t) = (Tp (t + hh) - Tp t) -
        (KR.Sharp.Kpt P tw X0m ρ (t + hh) - KR.Sharp.Kpt P tw X0m ρ t) -
        (NT (t + hh) - NT t) by ring, hK']
    ring
  rw [e1]
  have t1 := abs_sub (Tp (t + hh) - Tp t - A) (SW + (NT (t + hh) - NT t))
  have t2 := abs_sub (Tp (t + hh) - Tp t) A
  have t3 := abs_add_le SW (NT (t + hh) - NT t)
  rw [Finset.sum_add_distrib] at hA
  linarith

/-- The variation as a supremum: `v(t) = sup_{|h| ≤ 1.01 H(t)} |m(t+h) - m(t)|`. -/
noncomputable def vSup (H m : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup ((fun hh => |m (t + hh) - m t|) '' Icc (-(1.01 * H t)) (1.01 * H t))

lemma vSup_le {H m : ℝ → ℝ} {t B : ℝ} (hH : 0 ≤ H t)
    (hB : ∀ hh, |hh| ≤ 1.01 * H t → |m (t + hh) - m t| ≤ B) : vSup H m t ≤ B := by
  apply csSup_le (Set.Nonempty.image _ ⟨0, by constructor <;> linarith⟩)
  rintro _ ⟨hh, hhI, rfl⟩
  exact hB hh (abs_le.mpr hhI)

lemma le_vSup {H m : ℝ → ℝ} {x hh : ℝ} (hbdd : ∃ C, ∀ y, |m y| ≤ C)
    (hh1 : |hh| ≤ 1.01 * H x) : |m (x + hh) - m x| ≤ vSup H m x := by
  obtain ⟨C, hC⟩ := hbdd
  refine le_csSup (show BddAbove _ from ⟨2 * C, ?_⟩) ⟨hh, abs_le.mp hh1, rfl⟩
  rintro _ ⟨k, -, rfl⟩
  have := abs_sub (m (x + k)) (m x)
  linarith [hC (x + k), hC x]

/-- **Step 3: the recursion** `Margin.Var.RecIneq` for `v = vSup H m`, `m = T' - K_pt ρ̃ - NT`,
with the cofactors `Fset` (`t/w ≥ X₀⁻/2`), the neighbourhoods `Nbhd`, the weights
`c_w(t) = 1.0101 κ_w(t) w^{ε-2}` and `S(t) = o_t + 2η(t) + ∑_w e_w(t)/w`, from the pointwise
hypotheses of `step3_pointwise` at every `t ≥ T₀` and `|h| ≤ 1.01 H(t)`. -/
theorem recIneq_of (P : BeurlingSystem) (p : CP) (tw : ℕ → ℝ) {H Tp NT ρ err : ℝ → ℝ}
    {o η : ℝ → ℝ} {e : ℝ → ℕ → ℝ} {T0 : ℝ} (hXm : 0 < p.Xm) (hε : p.ε ≤ 0.01)
    (hp2 : ∀ i, 2 ≤ P.p i) (hρ : ∀ z, z < p.Xm → ρ z = 0) (hH0 : ∀ y, 0 ≤ H y)
    (hT0 : ∀ t, T0 ≤ t → 0 ≤ t ∧ 1.01 * H t ≤ t)
    (hgeom : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ (vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y)) err z' ∧
          err z' ≤ e t w)
    (he0 : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ e t w)
    (hosc : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t → |Tp (t + hh) - Tp t| ≤ o t)
    (hsw : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t →
      |∑ w ∈ Fset P p t, (kap P tw (t + hh) w - kap P tw t w) *
          (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NT (t + hh) - NT t| ≤ 2 * η t) :
    Var.RecIneq T0 (vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y))
      (fun t => o t + 2 * η t + ∑ w ∈ Fset P p t, e t w / KR.Vl P w) (Fset P p)
      (fun t w => 1.0101 * kap P tw t w * KR.Vl P w ^ (p.ε - 2)) (Nbhd P H) := by
  intro t ht b hb
  obtain ⟨ht0, hHt⟩ := hT0 t ht
  set m := fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y
  have hv0 : ∀ x, 0 ≤ vSup H m x := fun x =>
    Real.sSup_nonneg (fun _ ⟨_, _, hk⟩ => hk ▸ abs_nonneg _)
  have hb0 : ∀ w ∈ Fset P p t, 0 ≤ b w := by
    intro w hw
    refine (hv0 _).trans (hb w hw (t / KR.Vl P w) ⟨?_, ?_⟩) <;>
      linarith [hH0 (t / KR.Vl P w)]
  apply vSup_le (hH0 t)
  intro hh hh1
  have hth : t + hh ≤ 2 * t := by
    have := (abs_le.mp hh1).2; linarith
  exact step3_pointwise P tw hXm hε hp2 hρ ht0 hth hh1 (e t) b (hgeom t ht) (hS2 t ht)
    (he0 t ht) (fun w hw x hx => hb w hw x hx) hb0 (hosc t ht hh hh1) (hsw t ht hh hh1)

/-- **Proposition 5.38, Steps 1–5**: the variation `v = vSup H m` of the margin
`m = T' - K_pt ρ̃ - NT_pt` is bounded by the ordered-factorisation chain sum,
`v(t) ≤ ∑_M H_ord(M) M^{ε'-2} E_S/log(t/M) + j ∑_{|t/M - X₀| ≤ R₀} H_ord(M) M^{ε'-2}`,
from the Step-3 recursion (`recIneq_of`, with Steps 1–2 entering through `Step2At`), Step 4
(`log t · S(t) ≤ E_S`, hypothesis `hS4`; `Margin.Var.step4` proves it from Lemma 5.21), the
base case below `T₀` (`hbase`), and the super-solution `Vsup` (`v_le_chain`). -/
theorem variation_le_chain (P : BeurlingSystem) (p : CP) (tw : ℕ → ℝ)
    {H Tp NT ρ err : ℝ → ℝ} {o η : ℝ → ℝ} {e : ℝ → ℕ → ℝ} {T0 : ℝ}
    (h : ChainHyp P p H) (hε : p.ε ≤ 0.01) (hT0 : p.cinf + p.Kc ≤ T0)
    (hT0wf : 2 ≤ T0 * (1 - p.θ0)) (hρ : ∀ z, z < p.Xm → ρ z = 0)
    (hT0' : ∀ t, T0 ≤ t → 0 ≤ t ∧ 1.01 * H t ≤ t)
    (hgeom : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ (vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y)) err z' ∧
          err z' ≤ e t w)
    (he0 : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ e t w)
    (hosc : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t → |Tp (t + hh) - Tp t| ≤ o t)
    (hsw : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t →
      |∑ w ∈ Fset P p t, (kap P tw (t + hh) w - kap P tw t w) *
          (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NT (t + hh) - NT t| ≤ 2 * η t)
    (hS4 : ∀ t, T0 ≤ t →
      o t + 2 * η t + ∑ w ∈ Fset P p t, e t w / KR.Vl P w ≤ p.ES / Real.log t)
    (hbase : ∀ t, t < T0 →
      vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤ PhiC P p t 1)
    (t : ℝ) :
    vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤
      ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => cutL P p M ≤ t / Vv P M),
          Aw P p M * (p.ES / Real.log (t / Vv P M)) +
        p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter
          (fun M => |t / Vv P M - p.X0| ≤ p.R0), Aw P p M := by
  have hXm : 0 < p.Xm := by linarith [h.hXm]
  have hrec := recIneq_of P p tw hXm hε h.hp2 hρ h.hH0 hT0' hgeom hS2 he0 hosc hsw
  refine v_le_chain h hT0 hT0wf hS4 ?_ hrec hbase t
  intro t' _ w _
  have hk := kap_mem P tw t' w
  have hV := Real.rpow_nonneg (Vv_pos (P := P) w).le (p.ε - 2)
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hk.1) hV
  · have := mul_le_mul_of_nonneg_right hk.2 hV
    nlinarith

end Margin.Rec

end
