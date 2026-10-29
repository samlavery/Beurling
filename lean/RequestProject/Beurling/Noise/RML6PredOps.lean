module

public import RequestProject.Beurling.Noise.MarginPoint
public import RequestProject.Beurling.Noise.KptDefs
public import RequestProject.Beurling.Noise.KRVarWidth

/-!
# The operators of §5.3 on locally integrable functions: `B`, `K_pt`, and `R_res = (1 + K_pt B)⁻¹`

The window average `B g(x) = H(x)⁻¹ ∫_{W_x} g` is additive only on functions integrable on the
windows (`RML6PredBug.lean`). So the operators of Lemma 5.34 are taken on the additive subgroup
`LocInt` of locally integrable functions `ℝ → ℝ`:

* `Bop H : LocInt →+ LocInt`, `Bop H g x = Bavg (H x) g x` (for `H` continuous and positive the
  average is continuous in `x`);
* `Kop P tw X0m : LocInt →+ LocInt`, the realised `K_pt` (`KR.Sharp.Kpt`); on `(-∞, c]` it is a
  finite sum of indicator-weighted rescalings (`Kpt_eq_on`);
* `Nop : LocInt →+ LocInt`, the Neumann series `∑_k (-K_pt B)^k g`, which terminates at every
  point: `K_pt B` reads its argument at heights `≤ 0.525 y` and vanishes below `2X₀⁻`
  (`T_iter_zero`), so at `y` only the terms `k ≤ ⌈y⌉₊` are non-zero.

Main results (with `PaperWidth`, `H` non-decreasing, prime values `≥ 2`, `X₀⁻ ≥ 1`):

* `Nop_spec` : `R g + K_pt B R g = g` for every `g ∈ LocInt` (the field `hR`, §5.3);
* `inj_spec` : `f + B K_pt f = f' + B K_pt f' → f = f'` on `LocInt` (the field `hinj`: the
  Neumann series of `1 + B K_pt` terminate, §5.3);
* `Bop_apply` : `B g x = Bavg (H x) g x` (the field `hBx`, now for `g ∈ LocInt`).
-/

@[expose] public section

open MeasureTheory Set Finset BeurlingSystem

namespace KR.Ops

/-! ## Locally integrable functions -/

/-- The functions integrable on every bounded interval. -/
def LocInt : AddSubgroup (ℝ → ℝ) where
  carrier := {f | ∀ a b, IntervalIntegrable f volume a b}
  add_mem' := fun ha hb a b => (ha a b).add (hb a b)
  zero_mem' := fun _ _ => intervalIntegrable_const
  neg_mem' := fun ha a b => (ha a b).neg

lemma mem_LocInt {f : ℝ → ℝ} : f ∈ LocInt ↔ ∀ a b, IntervalIntegrable f volume a b := Iff.rfl

lemma LocInt_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : f ∈ LocInt :=
  fun a b => hf.intervalIntegrable a b

/-! ## The window average -/

variable {H : ℝ → ℝ}

lemma continuous_Bavg (hHc : Continuous H) (hHp : ∀ y, 0 < H y) {f : ℝ → ℝ}
    (hf : f ∈ LocInt) : Continuous fun x => Margin.Bavg (H x) f x := by
  unfold Margin.Bavg
  have hP : Continuous fun b => ∫ t in (0 : ℝ)..b, f t :=
    intervalIntegral.continuous_primitive (fun a b => hf a b) 0
  have e : (fun x => (H x)⁻¹ * ∫ t in (x - H x / 2)..(x + H x / 2), f t) =
      fun x => (H x)⁻¹ * ((∫ t in (0 : ℝ)..(x + H x / 2), f t) -
        ∫ t in (0 : ℝ)..(x - H x / 2), f t) := by
    funext x
    rw [intervalIntegral.integral_interval_sub_left (hf _ _) (hf _ _)]
  rw [e]
  refine (hHc.inv₀ fun y => (hHp y).ne').mul ((hP.comp ?_).sub (hP.comp ?_))
  · exact continuous_id.add (hHc.div_const 2)
  · exact continuous_id.sub (hHc.div_const 2)

/-- `B` on `LocInt`. -/
noncomputable def Bop (hHc : Continuous H) (hHp : ∀ y, 0 < H y) : LocInt →+ LocInt where
  toFun f := ⟨fun x => Margin.Bavg (H x) f x,
    LocInt_of_continuous (continuous_Bavg hHc hHp f.2)⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    simp [Margin.Bavg]
  map_add' f g := by
    apply Subtype.ext
    funext x
    show Margin.Bavg (H x) (fun t => f.1 t + g.1 t) x =
      Margin.Bavg (H x) f.1 x + Margin.Bavg (H x) g.1 x
    unfold Margin.Bavg
    rw [intervalIntegral.integral_add (f.2 _ _) (g.2 _ _)]
    ring

lemma Bop_apply (hHc : Continuous H) (hHp : ∀ y, 0 < H y) (g : LocInt) (x : ℝ) :
    (Bop hHc hHp g : ℝ → ℝ) x = Margin.Bavg (H x) g x := rfl

/-- `B g x` depends only on `g` on the window `[x - H(x)/2, x + H(x)/2]`. -/
lemma Bavg_congr {h x : ℝ} (hh : 0 ≤ h) {f g : ℝ → ℝ}
    (hfg : ∀ t, x - h / 2 ≤ t → t ≤ x + h / 2 → f t = g t) :
    Margin.Bavg h f x = Margin.Bavg h g x := by
  unfold Margin.Bavg
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by linarith)] at ht
  exact hfg t ht.1 ht.2

/-! ## The realised latest-prime operator -/

variable (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ)

open KR.Sharp

lemma valN_prime {p : ℕ} (hp : p.Prime) : Vl P p = P.labelVal p := by
  unfold Vl LemmaM.valN
  rw [hp.factorization, Finsupp.prod_single_index (by simp), pow_one]

variable {P} in
/-- With prime values `≥ 2`, every `w ≥ 2` has value `≥ 2`. -/
lemma Vl_ge_two (hp2 : ∀ j, 2 ≤ P.p j) {w : ℕ} (hw : 2 ≤ w) : 2 ≤ Vl P w := by
  obtain ⟨p, hp, hpw⟩ := Nat.exists_prime_and_dvd (show w ≠ 1 by omega)
  have h1 : Vl P p ≤ Vl P w :=
    LemmaM.valN_le_of_dvd _ (fun r _ => P.one_le_labelVal r) hpw (by omega)
  rw [valN_prime P hp] at h1
  have : 2 ≤ P.labelVal p := hp2 _
  linarith

variable {P tw X0m}

lemma Kpt_congr (hX : 0 < X0m) (hp2 : ∀ j, 2 ≤ P.p j) {f g : ℝ → ℝ} {y : ℝ}
    (hfg : ∀ t, X0m ≤ t → t ≤ y / 2 → f t = g t) : Kpt P tw X0m f y = Kpt P tw X0m g y := by
  unfold Kpt
  refine Finset.sum_congr rfl fun w hw => ?_
  obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
  have hV2 := Vl_ge_two hp2 hw2
  have hcut : X0m ≤ y / Vl P w := (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hwN).2
  have hy0 : 0 ≤ y := by
    have := Vl_pos P w
    by_contra hc; push_neg at hc
    have : y / Vl P w < 0 := div_neg_of_neg_of_pos hc (Vl_pos P w)
    linarith
  have hle : y / Vl P w ≤ y / 2 := div_le_div_of_nonneg_left hy0 (by norm_num) hV2
  split_ifs
  · rw [hfg _ hcut hle]
  · rfl

lemma Kpt_zero_low (hX : 0 < X0m) (hp2 : ∀ j, 2 ≤ P.p j) (f : ℝ → ℝ) {y : ℝ}
    (hy : y < 2 * X0m) : Kpt P tw X0m f y = 0 := by
  unfold Kpt
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
  have hV2 := Vl_ge_two hp2 hw2
  have h := ((mem_NAll_iff P hX).mp hwN).2
  rw [le_div_iff₀ hX] at h
  nlinarith

lemma Kpt_add (f g : ℝ → ℝ) (y : ℝ) :
    Kpt P tw X0m (fun t => f t + g t) y = Kpt P tw X0m f y + Kpt P tw X0m g y := by
  unfold Kpt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

lemma Kpt_zero (y : ℝ) : Kpt P tw X0m (fun _ => 0) y = 0 := by
  unfold Kpt
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs <;> simp

/-- The landing set of the cofactor `w`: `w ∈ NAll P y X₀⁻` and the filter `τ_w < y/w`. -/
def Sw (w : ℕ) : Set ℝ := {t | Vl P w ≤ t / X0m ∧ ∀ p ∈ w.primeFactors, tw p * Vl P w < t}

lemma measurableSet_Sw (w : ℕ) : MeasurableSet (Sw (P := P) (tw := tw) (X0m := X0m) w) := by
  unfold Sw
  rw [Set.setOf_and]
  refine MeasurableSet.inter (measurableSet_le measurable_const (measurable_id.div_const _)) ?_
  have : {t : ℝ | ∀ p ∈ w.primeFactors, tw p * Vl P w < t} =
      ⋂ p ∈ w.primeFactors, {t : ℝ | tw p * Vl P w < t} := by
    ext t; simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun p _ => measurableSet_lt measurable_const measurable_id

/-- On `(-∞, c]`, `K_pt f` is a fixed finite sum of indicator-weighted rescalings of `f`. -/
lemma Kpt_eq_on (hX : 0 < X0m) (f : ℝ → ℝ) {c y : ℝ} (hy : y ≤ c) :
    Kpt P tw X0m f y = ∑ w ∈ (NAll P c X0m).filter (2 ≤ ·),
      (Sw (P := P) (tw := tw) (X0m := X0m) w).indicator (fun t => f (t / Vl P w) / Vl P w) y := by
  classical
  unfold Kpt
  have hsub : (NAll P y X0m).filter (2 ≤ ·) ⊆ (NAll P c X0m).filter (2 ≤ ·) := by
    intro w hw
    obtain ⟨hwN, hw2⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨?_, hw2⟩
    obtain ⟨h0, h1⟩ := (mem_NAll_iff P hX).mp hwN
    exact (mem_NAll_iff P hX).mpr ⟨h0, h1.trans (div_le_div_of_nonneg_right hy hX.le)⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hwN, -⟩ := Finset.mem_filter.mp hw
    have hV := ((mem_NAll_iff P hX).mp hwN).2
    unfold Set.indicator Sw
    simp only [Set.mem_setOf_eq]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hV, h1⟩ h2
    · exact absurd h2.2 h1
    · rfl
  · intro w hw hnot
    obtain ⟨hwc, hw2⟩ := Finset.mem_filter.mp hw
    have hV : ¬ Vl P w ≤ y / X0m := by
      intro hV
      exact hnot (Finset.mem_filter.mpr ⟨(mem_NAll_iff P hX).mpr
        ⟨((mem_NAll_iff P hX).mp hwc).1, hV⟩, hw2⟩)
    unfold Set.indicator Sw
    simp only [Set.mem_setOf_eq]
    rw [if_neg (fun h => hV h.1)]

lemma Kpt_mem (hX : 0 < X0m) {f : ℝ → ℝ} (hf : f ∈ LocInt) :
    (fun y => Kpt P tw X0m f y) ∈ LocInt := by
  intro a b
  set c := max a b
  set S := ∑ w ∈ (NAll P c X0m).filter (2 ≤ ·),
      (Sw (P := P) (tw := tw) (X0m := X0m) w).indicator (fun t => f (t / Vl P w) / Vl P w)
  have hS : IntervalIntegrable S volume a b := by
    refine IntervalIntegrable.sum _ fun w _ => ?_
    have hV := Vl_pos P w
    have hc : IntervalIntegrable (fun t => f (t / Vl P w) / Vl P w) volume a b := by
      have h1 := (hf (a * (Vl P w)⁻¹) (b * (Vl P w)⁻¹)).comp_mul_left (c := (Vl P w)⁻¹)
      have e1 : a * (Vl P w)⁻¹ / (Vl P w)⁻¹ = a := by field_simp
      have e2 : b * (Vl P w)⁻¹ / (Vl P w)⁻¹ = b := by field_simp
      rw [e1, e2] at h1
      have h2 := h1.div_const (Vl P w)
      refine h2.congr (fun t _ => ?_)
      simp only [div_eq_inv_mul]
    rw [intervalIntegrable_iff] at hc ⊢
    exact hc.indicator (measurableSet_Sw w)
  refine hS.congr (fun y hy => ?_)
  have hyc : y ≤ c := by
    rcases le_total a b with h | h
    · rw [Set.uIoc_of_le h] at hy; exact hy.2.trans (le_max_right _ _)
    · rw [Set.uIoc_of_ge h] at hy; exact hy.2.trans (le_max_left _ _)
  simp only [S, Finset.sum_apply]
  exact (Kpt_eq_on hX f hyc).symm

/-- `K_pt` on `LocInt`. -/
noncomputable def Kop (hX : 0 < X0m) : LocInt →+ LocInt where
  toFun f := ⟨fun y => Kpt P tw X0m f y, Kpt_mem hX f.2⟩
  map_zero' := by
    apply Subtype.ext; funext y
    exact Kpt_zero y
  map_add' f g := by
    apply Subtype.ext; funext y
    exact Kpt_add f.1 g.1 y

lemma Kop_apply (hX : 0 < X0m) (g : LocInt) (y : ℝ) :
    (Kop (P := P) (tw := tw) hX g : ℝ → ℝ) y = Kpt P tw X0m g y := rfl

/-! ## The Neumann series -/

/-- The hypotheses on the width used by the termination argument: `H` continuous and positive,
`H(y) ≤ y/10` for `y ≥ X₀⁻/2` (`PaperWidth`), `H(y) ≤ X₀⁻/20` below `X₀⁻/2` (`H` non-decreasing),
prime values `≥ 2`, `X₀⁻ ≥ 1`. -/
structure OpHyp (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) : Prop where
  cont : Continuous H
  pos : ∀ y, 0 < H y
  small : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10
  low : ∀ y, y < X0m / 2 → H y ≤ X0m / 20
  p2 : ∀ j, 2 ≤ P.p j
  one_le : 1 ≤ X0m

variable (hO : OpHyp P H X0m)
include hO

lemma OpHyp.X0m_pos : 0 < X0m := by linarith [hO.one_le]

/-- `T = -K_pt B` on `LocInt`. -/
noncomputable def Top : LocInt →+ LocInt :=
  -((Kop (P := P) (tw := tw) hO.X0m_pos).comp (Bop hO.cont hO.pos))

lemma Top_apply (g : LocInt) (y : ℝ) :
    (Top (tw := tw) hO g : ℝ → ℝ) y = -Kpt P tw X0m (fun t => Margin.Bavg (H t) g t) y := rfl

omit hO in
lemma window_sub {t s : ℝ} (_hH0 : 0 ≤ H t) (hH : H t ≤ t / 10) (h1 : t - H t / 2 ≤ s)
    (h2 : s ≤ t + H t / 2) : 0.95 * t ≤ s ∧ s ≤ 1.05 * t := by
  constructor <;> linarith

/-- `T g (y)` reads `g` only on `[0.95 X₀⁻, 0.525 y]`. -/
lemma Top_local {g h : LocInt} {y : ℝ}
    (hgh : ∀ t, 0.95 * X0m ≤ t → t ≤ 0.525 * y → (g : ℝ → ℝ) t = (h : ℝ → ℝ) t) :
    (Top (tw := tw) hO g : ℝ → ℝ) y = (Top (tw := tw) hO h : ℝ → ℝ) y := by
  rw [Top_apply, Top_apply]
  congr 1
  refine Kpt_congr hO.X0m_pos hO.p2 fun t ht1 ht2 => ?_
  have hHt := hO.small t (by linarith [hO.X0m_pos])
  refine Bavg_congr (hO.pos t).le fun s hs1 hs2 => hgh s ?_ ?_
  · have := (window_sub (hO.pos t).le hHt hs1 hs2).1; nlinarith
  · have := (window_sub (hO.pos t).le hHt hs1 hs2).2; nlinarith

lemma Top_zero_low (g : LocInt) {y : ℝ} (hy : y < 2 * X0m) :
    (Top (tw := tw) hO g : ℝ → ℝ) y = 0 := by
  rw [Top_apply, Kpt_zero_low hO.X0m_pos hO.p2 _ hy, neg_zero]

/-- **Termination**: `T^{k+1} g` vanishes below `2 X₀⁻ 1.9^k`. -/
lemma Top_iter_zero (k : ℕ) : ∀ (g : LocInt) (y : ℝ), y < 2 * X0m * 1.9 ^ k →
    (((Top (tw := tw) hO)^[k + 1] g : LocInt) : ℝ → ℝ) y = 0 := by
  induction k with
  | zero =>
    intro g y hy
    simp only [zero_add, Function.iterate_one]
    exact Top_zero_low hO g (by simpa using hy)
  | succ k ih =>
    intro g y hy
    rw [Function.iterate_succ_apply']
    have h0 : (Top (tw := tw) hO 0 : ℝ → ℝ) y = 0 := by rw [map_zero]; rfl
    rw [← h0]
    refine Top_local hO fun t _ ht2 => ?_
    refine ih g t ?_
    have hX := hO.X0m_pos
    have hp : (0 : ℝ) < 1.9 ^ k := by positivity
    rw [pow_succ] at hy
    nlinarith

omit hO in
lemma ceil_bound {X0m : ℝ} (h1 : 1 ≤ X0m) {y : ℝ} {j : ℕ} (hj : ⌈y⌉₊ ≤ j) :
    y < 2 * X0m * 1.9 ^ j := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 0.9 by norm_num) j
  have hjy : y ≤ j := (Nat.le_ceil y).trans (by exact_mod_cast hj)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  norm_num at hb
  nlinarith

lemma Top_iter_vanish (g : LocInt) {y : ℝ} {k : ℕ} (hk : ⌈y⌉₊ + 1 ≤ k) :
    (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) y = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Top_iter_zero hO j g y (ceil_bound hO.one_le (by omega))

/-- The Neumann series `∑_k T^k g`, truncated at `⌈y⌉₊` (all later terms vanish at `y`). -/
noncomputable def Nfun (g : LocInt) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (⌈y⌉₊ + 1), (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) y

lemma Nfun_eq_sum (g : LocInt) {c t : ℝ} (htc : t ≤ c) :
    Nfun (tw := tw) hO g t =
      ∑ k ∈ Finset.range (⌈c⌉₊ + 1), (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) t := by
  unfold Nfun
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    have := Nat.ceil_mono htc
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    exact Top_iter_vanish hO g hk

lemma Nfun_mem (g : LocInt) : Nfun (tw := tw) hO g ∈ LocInt := by
  intro a b
  set c := max a b
  have hS : IntervalIntegrable (∑ k ∈ Finset.range (⌈c⌉₊ + 1),
      (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ)) volume a b :=
    IntervalIntegrable.sum _ fun k _ => ((Top (tw := tw) hO)^[k] g).2 a b
  refine hS.congr (fun y hy => ?_)
  have hyc : y ≤ c := by
    rcases le_total a b with h | h
    · rw [Set.uIoc_of_le h] at hy; exact hy.2.trans (le_max_right _ _)
    · rw [Set.uIoc_of_ge h] at hy; exact hy.2.trans (le_max_left _ _)
  simp only [Finset.sum_apply]
  exact (Nfun_eq_sum hO g hyc).symm

/-- **`R_res = (1 + K_pt B)⁻¹`** on `LocInt`, as the terminating Neumann series. -/
noncomputable def Nop : LocInt →+ LocInt where
  toFun g := ⟨Nfun (tw := tw) hO g, Nfun_mem hO g⟩
  map_zero' := by
    apply Subtype.ext; funext y
    simp only [Nfun, iterate_map_zero]
    exact Finset.sum_eq_zero fun _ _ => rfl
  map_add' f g := by
    apply Subtype.ext; funext y
    show Nfun hO (f + g) y = Nfun hO f y + Nfun hO g y
    simp only [Nfun, iterate_map_add, AddSubgroup.coe_add, Pi.add_apply,
      Finset.sum_add_distrib]

/-- **The field `hR`**: `R g + K_pt B R g = g` for `g ∈ LocInt` (§5.3). -/
theorem Nop_spec (g : LocInt) :
    Nop (tw := tw) hO g + Kop (P := P) (tw := tw) hO.X0m_pos
      (Bop hO.cont hO.pos (Nop (tw := tw) hO g)) = g := by
  apply Subtype.ext; funext y
  set c := max y 0
  set M := ⌈c⌉₊ + 1
  set S : LocInt := ∑ k ∈ Finset.range M, (Top (tw := tw) hO)^[k] g
  have hKB : ∀ u : LocInt, ((Kop (P := P) (tw := tw) hO.X0m_pos (Bop hO.cont hO.pos u) :
      LocInt) : ℝ → ℝ) y = -((Top (tw := tw) hO u : LocInt) : ℝ → ℝ) y := by
    intro u; rw [Top_apply, neg_neg]; rfl
  have hloc : ((Top (tw := tw) hO (Nop (tw := tw) hO g) : LocInt) : ℝ → ℝ) y =
      ((Top (tw := tw) hO S : LocInt) : ℝ → ℝ) y := by
    refine Top_local hO fun t ht1 ht2 => ?_
    have htc : t ≤ c := by
      have hX := hO.X0m_pos
      have : 0 ≤ y := by nlinarith
      simp only [c]; rw [max_eq_left this]; nlinarith
    show Nfun hO g t = _
    rw [Nfun_eq_sum hO g htc]
    simp only [S, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    rfl
  have hS : ((Top (tw := tw) hO S : LocInt) : ℝ → ℝ) y =
      ∑ k ∈ Finset.range M, (((Top (tw := tw) hO)^[k + 1] g : LocInt) : ℝ → ℝ) y := by
    simp only [S, map_sum, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply,
      Function.iterate_succ_apply']
  have hN : Nfun (tw := tw) hO g y =
      ∑ k ∈ Finset.range M, (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) y :=
    Nfun_eq_sum hO g (le_max_left y 0)
  have hvan : (((Top (tw := tw) hO)^[M] g : LocInt) : ℝ → ℝ) y = 0 :=
    Top_iter_vanish hO g (by have := Nat.ceil_mono (show y ≤ c from le_max_left y 0); omega)
  have htel := Finset.sum_range_sub
    (fun k => (((Top (tw := tw) hO)^[k] g : LocInt) : ℝ → ℝ) y) M
  simp only [Function.iterate_zero, id] at htel
  show Nfun hO g y + ((Kop (P := P) (tw := tw) hO.X0m_pos (Bop hO.cont hO.pos
    (Nop (tw := tw) hO g)) : LocInt) : ℝ → ℝ) y = (g : ℝ → ℝ) y
  rw [hKB, hloc, hS, hN]
  rw [Finset.sum_sub_distrib] at htel
  linarith

/-! ## Injectivity of `1 + B K_pt` -/

/-- `S' = -B K_pt` on `LocInt`. -/
noncomputable def Sop : LocInt →+ LocInt :=
  -((Bop hO.cont hO.pos).comp (Kop (P := P) (tw := tw) hO.X0m_pos))

lemma Sop_apply (g : LocInt) (y : ℝ) :
    (Sop (tw := tw) hO g : ℝ → ℝ) y = -Margin.Bavg (H y) (fun t => Kpt P tw X0m g t) y := rfl

/-- The window of `y` lies below `max(1.05 y, X₀⁻/2 + X₀⁻/40)`. -/
lemma window_top (y : ℝ) {c : ℝ} (hc : X0m ≤ c) (hy : 1.05 * y < c) {s : ℝ}
    (hs : s ≤ y + H y / 2) : s < c := by
  rcases le_or_gt (X0m / 2) y with h | h
  · have := hO.small y h; linarith
  · have := hO.low y h; have := hO.X0m_pos; linarith

lemma Sop_iter_zero (k : ℕ) : ∀ (g : LocInt) (y : ℝ), y < X0m * 1.9 ^ (k + 1) →
    (((Sop (tw := tw) hO)^[k + 1] g : LocInt) : ℝ → ℝ) y = 0 := by
  have hX := hO.X0m_pos
  induction k with
  | zero =>
    intro g y hy
    simp only [zero_add, Function.iterate_one, Sop_apply]
    rw [neg_eq_zero]
    have h0 : Margin.Bavg (H y) (fun _ => (0 : ℝ)) y = 0 := by simp [Margin.Bavg]
    rw [← h0]
    refine Bavg_congr (hO.pos y).le fun s _ hs2 => ?_
    refine Kpt_zero_low hX hO.p2 _ ?_
    exact window_top hO y (c := 2 * X0m) (by linarith) (by nlinarith) hs2
  | succ k ih =>
    intro g y hy
    rw [Function.iterate_succ_apply', Sop_apply, neg_eq_zero]
    have h0 : Margin.Bavg (H y) (fun _ => (0 : ℝ)) y = 0 := by simp [Margin.Bavg]
    rw [← h0]
    have hp : (0 : ℝ) < 1.9 ^ (k + 1) := by positivity
    refine Bavg_congr (hO.pos y).le fun s _ hs2 => ?_
    have hs : s < 2 * (X0m * 1.9 ^ (k + 1)) := by
      have h19 : (1 : ℝ) ≤ 1.9 ^ (k + 1) := one_le_pow₀ (by norm_num)
      refine window_top hO y (by nlinarith) ?_ hs2
      rw [pow_succ] at hy; nlinarith
    rw [← Kpt_zero (P := P) (tw := tw) (X0m := X0m) s]
    refine Kpt_congr hX hO.p2 fun t _ ht2 => ih g t (by linarith)

/-- **The field `hinj`**: `1 + B K_pt` is injective on `LocInt` (its Neumann series terminate). -/
theorem inj_spec (f f' : LocInt)
    (h : f + Bop hO.cont hO.pos (Kop (P := P) (tw := tw) hO.X0m_pos f) =
      f' + Bop hO.cont hO.pos (Kop (P := P) (tw := tw) hO.X0m_pos f')) : f = f' := by
  set d := f - f'
  have hfix : Sop (tw := tw) hO d = d := by
    have : d + Bop hO.cont hO.pos (Kop (P := P) (tw := tw) hO.X0m_pos d) = 0 := by
      simp only [d, map_sub]
      rw [sub_add_sub_comm, h, sub_self]
    simp only [Sop, AddMonoidHom.neg_apply, AddMonoidHom.comp_apply]
    exact (eq_neg_of_add_eq_zero_left this).symm
  have hit : ∀ k, (Sop (tw := tw) hO)^[k] d = d := fun k =>
    Function.iterate_fixed hfix k
  have hd : d = 0 := by
    apply Subtype.ext; funext y
    have := Sop_iter_zero (tw := tw) hO (2 * ⌈y⌉₊ + 1) d y (by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 0.9 by norm_num) (2 * ⌈y⌉₊ + 1 + 1)
      have hjy : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
      have h0 : (0 : ℝ) ≤ ⌈y⌉₊ := Nat.cast_nonneg _
      have h1 := hO.one_le
      push_cast at hb
      norm_num at hb
      have hp : (0 : ℝ) < 1.9 ^ (2 * ⌈y⌉₊ + 1 + 1) := by positivity
      nlinarith)
    rw [hit] at this
    exact this
  exact sub_eq_zero.mp hd

end KR.Ops

end
