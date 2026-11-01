module

public import RequestProject.Beurling.Noise.MarginExact

/-!
# Step 2 of Proposition 5.38: the strip comparison

For a width `H` that is monotone, `≥ 1`, with `H(y)² ≤ max(y, X₀)` and the ratio bound
`H(t) - H(s) ≤ ε (t - s)/max(s, X₀) · H(s)` (`s ≤ t`, `ε ≤ 1/10`), the sets
`A₊ = {x : z < x - H(x)/2 ≤ z + s}` and `A₋ = {x : z < x + H(x)/2 ≤ z + s}` differ from the
strips `I₊ = (z + H(z)/2, z + H(z)/2 + s]`, `I₋ = (z - H(z)/2, z - H(z)/2 + s]` by sets of
measure at most `2` (`0 ≤ s ≤ 1.01 H(z)`), so for `|m| ≤ M` on `[z - 3H(z), z + 3H(z)]`,
`|∫_{A±} m - ∫_{I±} m| ≤ 2 M` (`strip_cmp_plus`, `strip_cmp_minus`).
-/

@[expose] public section

open MeasureTheory Set

namespace Margin.Strip

/-- The hypotheses on the width. -/
structure WidthH (H : ℝ → ℝ) (X0 ε : ℝ) : Prop where
  mono : Monotone H
  ge_one : ∀ y, 1 ≤ H y
  sq_le : ∀ y, H y ^ 2 ≤ max y X0
  X0_ge : 1 ≤ X0
  ε0 : 0 ≤ ε
  ε1 : ε ≤ 1 / 10
  ratio : ∀ s t, s ≤ t → H t - H s ≤ ε * (t - s) / max s X0 * H s

variable {H : ℝ → ℝ} {X0 ε : ℝ}

namespace WidthH

variable (hW : WidthH H X0 ε)
include hW

lemma max_ge_one (y : ℝ) : 1 ≤ max y X0 := le_trans hW.X0_ge (le_max_right _ _)

lemma le_max (y : ℝ) : H y ≤ max y X0 := by
  have h1 := hW.ge_one y
  have h2 := hW.sq_le y
  nlinarith

/-- `H(x) - H(z) ≤ ε(x - z)` for `z ≤ x`. -/
lemma incr_le {z x : ℝ} (hzx : z ≤ x) : H x - H z ≤ ε * (x - z) := by
  have h := hW.ratio z x hzx
  have hm := hW.max_ge_one z
  have hle := hW.le_max z
  have hε := hW.ε0
  have : ε * (x - z) / max z X0 * H z ≤ ε * (x - z) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have : 0 ≤ ε * (x - z) := mul_nonneg hε (by linarith)
    nlinarith
  linarith

/-- On `[z, z + 3H(z)]`, `|H(x) - H(z)| ≤ 1`. -/
lemma var_plus {z x : ℝ} (hzx : z ≤ x) (hx : x ≤ z + 3 * H z) : |H x - H z| ≤ 1 := by
  have h := hW.ratio z x hzx
  have hm := hW.max_ge_one z
  have hsq := hW.sq_le z
  have hε := hW.ε0
  have hε1 := hW.ε1
  have hmono := hW.mono hzx
  have hH1 := hW.ge_one z
  rw [abs_le]; refine ⟨by linarith, ?_⟩
  have : ε * (x - z) / max z X0 * H z ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h3 : ε * (x - z) * H z ≤ ε * (3 * H z) * H z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hε) (by linarith)
    nlinarith
  linarith

/-- On `[z - H(z)/2, z]`, `|H(x) - H(z)| ≤ 1`. -/
lemma var_minus {z x : ℝ} (hxz : x ≤ z) (hx : z - H z / 2 ≤ x) : |H x - H z| ≤ 1 := by
  have h := hW.ratio x z hxz
  have hmono := hW.mono hxz
  have hHx1 := hW.ge_one x
  have hsq := hW.sq_le z
  have hlez := hW.le_max z
  have hε := hW.ε0
  have hε1 := hW.ε1
  have hmz := hW.max_ge_one z
  -- `max x X0 ≥ max z X0 / 2`
  have hmx : max z X0 / 2 ≤ max x X0 := by
    rcases le_total z X0 with h1 | h1
    · rw [max_eq_right h1]; linarith [le_max_right x X0, hW.X0_ge]
    · rw [max_eq_left h1]
      have : z - max z X0 / 2 ≤ x := by
        rw [max_eq_left h1] at hlez ⊢; linarith
      rw [max_eq_left h1] at this
      linarith [le_max_left x X0]
  have hmx0 : 0 < max x X0 := by linarith
  rw [abs_le]; refine ⟨?_, by linarith⟩
  have : ε * (z - x) / max x X0 * H x ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hmx0]
    have h3 : ε * (z - x) * H x ≤ ε * (H z / 2) * H z :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hε) hmono (by linarith)
        (mul_nonneg hε (by linarith))
    nlinarith
  linarith

end WidthH

/-- `|∫_A m - ∫_I m| ≤ M (vol(A \ I) + vol(I \ A))` for `A, I ⊆ K`, `m` integrable and
bounded by `M` on `K`. -/
lemma integral_sub_le {m : ℝ → ℝ} {A I K : Set ℝ} {M : ℝ} (hAK : A ⊆ K) (hIK : I ⊆ K)
    (hA : MeasurableSet A) (hI : MeasurableSet I) (hK : volume K < ⊤)
    (hm : IntegrableOn m K) (hb : ∀ x ∈ K, |m x| ≤ M) :
    |(∫ x in A, m x) - ∫ x in I, m x| ≤ M * (volume.real (A \ I) + volume.real (I \ A)) := by
  have e1 := integral_inter_add_diff hI (hm.mono_set hAK)
  have e2 := integral_inter_add_diff hA (hm.mono_set hIK)
  rw [inter_comm] at e2
  have h1 := norm_setIntegral_le_of_norm_le_const (f := m) (s := A \ I) (C := M)
    (lt_of_le_of_lt (measure_mono (diff_subset.trans hAK)) hK)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hb x (hAK hx.1))
  have h2 := norm_setIntegral_le_of_norm_le_const (f := m) (s := I \ A) (C := M)
    (lt_of_le_of_lt (measure_mono (diff_subset.trans hIK)) hK)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hb x (hIK hx.1))
  rw [Real.norm_eq_abs] at h1 h2
  rw [← e1, ← e2]
  calc |(∫ x in A ∩ I, m x) + (∫ x in A \ I, m x) - ((∫ x in A ∩ I, m x) + ∫ x in I \ A, m x)|
      = |(∫ x in A \ I, m x) - ∫ x in I \ A, m x| := by ring_nf
    _ ≤ |∫ x in A \ I, m x| + |∫ x in I \ A, m x| := abs_sub _ _
    _ ≤ M * volume.real (A \ I) + M * volume.real (I \ A) := add_le_add h1 h2
    _ = _ := by ring

lemma real_union_Ioc_le (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    volume.real (Ioc a b ∪ Ioc c d) ≤ (b - a) + (d - c) := by
  calc volume.real (Ioc a b ∪ Ioc c d) ≤ volume.real (Ioc a b) + volume.real (Ioc c d) :=
        measureReal_union_le _ _
    _ = (b - a) + (d - c) := by
        rw [Real.volume_real_Ioc_of_le hab, Real.volume_real_Ioc_of_le hcd]

lemma real_mono_of_sub {S T : Set ℝ} (hST : S ⊆ T) (hT : volume T < ⊤) :
    volume.real S ≤ volume.real T :=
  measureReal_mono hST hT.ne

namespace WidthH

variable (hW : WidthH H X0 ε)
include hW

lemma measurable_H : Measurable H := hW.mono.measurable

lemma meas_Aplus (z s : ℝ) : MeasurableSet (Margin.Exact.Aplus H z s) := by
  have hm := hW.measurable_H
  have hf : Measurable fun x : ℝ => x - H x / 2 := measurable_id.sub (hm.div_const 2)
  exact (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)

lemma meas_Aminus (z s : ℝ) : MeasurableSet (Margin.Exact.Aminus H z s) := by
  have hm := hW.measurable_H
  have hf : Measurable fun x : ℝ => x + H x / 2 := measurable_id.add (hm.div_const 2)
  exact (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)

lemma Aplus_sub {z s : ℝ} (hs : s ≤ 1.01 * H z) :
    Margin.Exact.Aplus H z s ⊆ Icc z (z + 3 * H z) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hH1 := hW.ge_one x
  have hzx : z ≤ x := by linarith
  have hinc := hW.incr_le hzx
  have hε1 := hW.ε1
  have hε0 := hW.ε0
  refine ⟨hzx, ?_⟩
  have : ε * (x - z) ≤ (x - z) / 10 :=
    by nlinarith
  nlinarith [hW.ge_one z]

lemma Aminus_sub {z s : ℝ} (hs : s ≤ 1.01 * H z) :
    Margin.Exact.Aminus H z s ⊆ Icc (z - H z / 2) (z + 1.01 * H z) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hH1 := hW.ge_one x
  refine ⟨?_, by linarith⟩
  rcases le_total z x with hzx | hxz
  · linarith [hW.ge_one z]
  · have := hW.mono hxz; linarith

/-- **The strip comparison on `A₊`**: `|∫_{A₊} m - ∫_{I₊} m| ≤ 2M`. -/
theorem strip_cmp_plus {m : ℝ → ℝ} {M z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * H z)
    (hm : IntegrableOn m (Icc (z - 3 * H z) (z + 3 * H z)))
    (hb : ∀ x ∈ Icc (z - 3 * H z) (z + 3 * H z), |m x| ≤ M) :
    |(∫ x in Margin.Exact.Aplus H z s, m x) -
      ∫ x in (z + H z / 2)..(z + H z / 2 + s), m x| ≤ 2 * M := by
  have hH := hW.ge_one z
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hb z ⟨by linarith, by linarith⟩)
  set a := z + H z / 2 with ha
  rw [intervalIntegral.integral_of_le (by linarith)]
  set A := Margin.Exact.Aplus H z s
  set I := Ioc a (a + s)
  set K := Icc (z - 3 * H z) (z + 3 * H z)
  have hAK : A ⊆ K := fun x hx => by
    have := hW.Aplus_sub hs hx; exact ⟨by linarith [this.1], this.2⟩
  have hIK : I ⊆ K := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hK : volume K < ⊤ := measure_Icc_lt_top
  have hmain := integral_sub_le hAK hIK (hW.meas_Aplus z s) measurableSet_Ioc hK hm hb
  have hvar : ∀ x ∈ A, |H x - H z| ≤ 1 := fun x hx => by
    have := hW.Aplus_sub hs hx; exact hW.var_plus this.1 this.2
  have hvarI : ∀ x ∈ I, |H x - H z| ≤ 1 := fun x hx =>
    hW.var_plus (by linarith [hx.1]) (by linarith [hx.2])
  have hAI : A \ I ⊆ Ioc (a - 1 / 2) a ∪ Ioc (a + s) (a + s + 1 / 2) := by
    intro x ⟨hxA, hxI⟩
    have hv := abs_le.mp (hvar x hxA)
    obtain ⟨h1, h2⟩ := hxA
    simp only [I, mem_Ioc, not_and_or, not_lt, not_le] at hxI
    rcases hxI with h | h
    · left; exact ⟨by linarith, h⟩
    · right; exact ⟨h, by linarith⟩
  have hIA : I \ A ⊆ Ioc a (a + 1 / 2) ∪ Ioc (a + s - 1 / 2) (a + s) := by
    intro x ⟨hxI, hxA⟩
    have hv := abs_le.mp (hvarI x hxI)
    obtain ⟨h1, h2⟩ := hxI
    simp only [A, Margin.Exact.Aplus, mem_setOf_eq, not_and_or, not_lt, not_le] at hxA
    rcases hxA with h | h
    · left; exact ⟨h1, by linarith⟩
    · right; exact ⟨by linarith, h2⟩
  have hfin : ∀ a b c d : ℝ, volume (Ioc a b ∪ Ioc c d) < ⊤ := fun a b c d =>
    measure_union_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  have v1 := (real_mono_of_sub hAI (hfin _ _ _ _)).trans
    (real_union_Ioc_le _ _ _ _ (by linarith) (by linarith))
  have v2 := (real_mono_of_sub hIA (hfin _ _ _ _)).trans
    (real_union_Ioc_le _ _ _ _ (by linarith) (by linarith))
  have hv : volume.real (A \ I) + volume.real (I \ A) ≤ 2 := by linarith
  calc _ ≤ M * (volume.real (A \ I) + volume.real (I \ A)) := hmain
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left hv hM
    _ = 2 * M := by ring

/-- **The strip comparison on `A₋`**: `|∫_{A₋} m - ∫_{I₋} m| ≤ 2M`. -/
theorem strip_cmp_minus {m : ℝ → ℝ} {M z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * H z)
    (hm : IntegrableOn m (Icc (z - 3 * H z) (z + 3 * H z)))
    (hb : ∀ x ∈ Icc (z - 3 * H z) (z + 3 * H z), |m x| ≤ M) :
    |(∫ x in Margin.Exact.Aminus H z s, m x) -
      ∫ x in (z - H z / 2)..(z - H z / 2 + s), m x| ≤ 2 * M := by
  have hH := hW.ge_one z
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hb z ⟨by linarith, by linarith⟩)
  set c := z - H z / 2 with hc
  rw [intervalIntegral.integral_of_le (by linarith)]
  set A := Margin.Exact.Aminus H z s
  set I := Ioc c (c + s)
  set K := Icc (z - 3 * H z) (z + 3 * H z)
  have hvar0 : ∀ x, z - H z / 2 ≤ x → x ≤ z + 3 * H z → |H x - H z| ≤ 1 := by
    intro x h1 h2
    rcases le_total z x with hzx | hxz
    · exact hW.var_plus hzx h2
    · exact hW.var_minus hxz h1
  have hAK : A ⊆ K := fun x hx => by
    have := hW.Aminus_sub hs hx; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hIK : I ⊆ K := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hK : volume K < ⊤ := measure_Icc_lt_top
  have hmain := integral_sub_le hAK hIK (hW.meas_Aminus z s) measurableSet_Ioc hK hm hb
  have hvar : ∀ x ∈ A, |H x - H z| ≤ 1 := fun x hx => by
    have := hW.Aminus_sub hs hx; exact hvar0 x this.1 (by linarith [this.2])
  have hvarI : ∀ x ∈ I, |H x - H z| ≤ 1 := fun x hx =>
    hvar0 x (by linarith [hx.1]) (by linarith [hx.2])
  have hAI : A \ I ⊆ Ioc (c - 1 / 2) c ∪ Ioc (c + s) (c + s + 1 / 2) := by
    intro x ⟨hxA, hxI⟩
    have hv := abs_le.mp (hvar x hxA)
    obtain ⟨h1, h2⟩ := hxA
    simp only [I, mem_Ioc, not_and_or, not_lt, not_le] at hxI
    rcases hxI with h | h
    · left; exact ⟨by linarith, h⟩
    · right; exact ⟨h, by linarith⟩
  have hIA : I \ A ⊆ Ioc c (c + 1 / 2) ∪ Ioc (c + s - 1 / 2) (c + s) := by
    intro x ⟨hxI, hxA⟩
    have hv := abs_le.mp (hvarI x hxI)
    obtain ⟨h1, h2⟩ := hxI
    simp only [A, Margin.Exact.Aminus, mem_setOf_eq, not_and_or, not_lt, not_le] at hxA
    rcases hxA with h | h
    · left; exact ⟨h1, by linarith⟩
    · right; exact ⟨by linarith, h2⟩
  have hfin : ∀ a b c d : ℝ, volume (Ioc a b ∪ Ioc c d) < ⊤ := fun a b c d =>
    measure_union_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  have v1 := (real_mono_of_sub hAI (hfin _ _ _ _)).trans
    (real_union_Ioc_le _ _ _ _ (by linarith) (by linarith))
  have v2 := (real_mono_of_sub hIA (hfin _ _ _ _)).trans
    (real_union_Ioc_le _ _ _ _ (by linarith) (by linarith))
  have hv : volume.real (A \ I) + volume.real (I \ A) ≤ 2 := by linarith
  calc _ ≤ M * (volume.real (A \ I) + volume.real (I \ A)) := hmain
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left hv hM
    _ = 2 * M := by ring

end WidthH

end Margin.Strip

end
