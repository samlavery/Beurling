module

public import RequestProject.Beurling.Noise.LemSMain
public import RequestProject.Beurling.Noise.TNPScales

/-!
# Lemma 5.34, second bullet (correction #110): the scale sum with `C'_S = 10` applied once

At a start `y`, the levels of the scale `u` (`y/n ∈ [u, 2u)`) read the source at points
`t ∈ [0.89u, 2.21u]` (their kernels are supported within `1.02 H(y/n) ≤ 0.102 y/n` of `y/n`).
On that window, `ω_t(v) ≤ OmB(log 3v, log(t/2v)) ≤ OmB(log 3v, log(0.89u/2v))` (the decreasing
majorant of Lemma 5.21, `HBS.omega_le_OmB`, `LemS.OmB_anti`), and `ω_t(v) = 0` for `t < v`. So
the scale weight is

  `Om8 v u = 0` if `2.21u < v`, and `OmB(log 3v, log(0.89u/2v))` otherwise,

and the outer-scale sum of Lemma 5.21(iii) is taken **once**, with the shifted levels:

* `scale_sum_tight` : `∑_{u ∈ dyScales X₀ y N} log(2u) Om8 v u ≤ 10 (log 3v)²`.

This is the paper's "taking the suprema of Lemma S over `[Y - 1.02H, 2Y + 1.02H]` costs a
factor `1 + o(1)`, covered by `C'_S = 10`": the scales `u = X₀2^k/4` are mapped injectively to
the dyadic levels `m = k + d` of `LemS.partA_le`/`partB_le` (`d = ⌊log(0.89X₀/4)/log 2⌋`), which
shifts the level by less than `log 2` (absorbed by the monotonicity of `OmB`) and the weight by
a factor `1 + 10⁻⁷`; the at most seven levels just below `v` cost `7 log 3v`.
-/

@[expose] public section

open Finset Real KR.TNP

namespace KR.RML8G

/-- The scale weight of `ω(v)` at the scale `u` (window `[0.89u, 2.21u]`). -/
noncomputable def Om8 (v u : ℝ) : ℝ :=
  if 2.21 * u < v then 0 else LemS.OmB (Real.log (3 * v)) (Real.log (0.89 * u / (2 * v)))

lemma Om8_nonneg (v u : ℝ) : 0 ≤ Om8 v u := by
  unfold Om8; split_ifs
  · exact le_rfl
  · exact LemS.OmB_nonneg _ _

lemma OmB_le_one_of_lt {L ℓ : ℝ} (h : ℓ < L) : LemS.OmB L ℓ = 1 := by
  unfold LemS.OmB; rw [if_pos h]

set_option maxHeartbeats 2000000 in
/-- **The outer-scale sum** (Lemma 5.21(iii) applied once at the shifted levels):
`∑_{u ∈ dyScales X₀ y N} log(2u) Om8 v u ≤ 10 (log 3v)²`. -/
theorem scale_sum_tight {X0 v y : ℝ} {N : ℕ} (hX0 : 12 ≤ X0) (hv : 0 < v)
    (hL : 100000000 ≤ Real.log (3 * v)) :
    ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Om8 v u ≤ 10 * Real.log (3 * v) ^ 2 := by
  classical
  set L := Real.log (3 * v) with hLdef
  obtain ⟨hl2a, hl2b⟩ := LemS.log2_bounds
  have hl2 : 0 < Real.log 2 := by linarith
  set f : ℕ → ℝ := fun k => X0 * 2 ^ k / 4 with hf
  have hfpos : ∀ k, 0 < f k := fun k => by simp only [hf]; positivity
  have hfinj : Set.InjOn f (range N : Set ℕ) := by
    intro a _ b _ hab
    simp only [hf] at hab
    have h1 : (2 : ℝ) ^ a = 2 ^ b := by
      have hX : X0 ≠ 0 := by linarith
      field_simp at hab; nlinarith [hab]
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h1)
  -- the terms are nonnegative
  have hterm0 : ∀ u, 3 ≤ u → 0 ≤ Real.log (2 * u) * Om8 v u := fun u hu =>
    mul_nonneg (Real.log_nonneg (by linarith)) (Om8_nonneg v u)
  have hf3 : ∀ k, 3 ≤ f k := fun k => by
    simp only [hf]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  -- the shift `d`
  set c0 := Real.log (0.89 * X0 / 4) with hc0
  have hc0pos : 0 ≤ c0 := Real.log_nonneg (by linarith)
  set d := ⌊c0 / Real.log 2⌋₊ with hd
  have hd1 : (d : ℝ) * Real.log 2 ≤ c0 := by
    have := Nat.floor_le (div_nonneg hc0pos hl2.le)
    rw [← hd] at this
    rwa [le_div_iff₀ hl2] at this
  have hd2 : c0 < ((d : ℝ) + 1) * Real.log 2 := by
    have := Nat.lt_floor_add_one (c0 / Real.log 2)
    rw [← hd] at this
    rwa [div_lt_iff₀ hl2] at this
  -- `T m = (m+1) log 2 · OmB(L, g_m)`, `g_m = log(2^m/2v)`
  set T : ℕ → ℝ := fun m => ((m : ℝ) + 1) * Real.log 2 *
    LemS.OmB L (Real.log ((2 : ℝ) ^ m / (2 * v))) with hT
  have hT0 : ∀ m, 0 ≤ T m := fun m => by
    simp only [hT]; exact mul_nonneg (by positivity) (LemS.OmB_nonneg _ _)
  have hlog2v : Real.log (2 * v) ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hlog2v' : L - 1 ≤ Real.log (2 * v) := by
    have e : L = Real.log (2 * v) + Real.log (3 / 2) := by
      rw [hLdef, ← Real.log_mul (by positivity) (by norm_num)]; ring_nf
    have : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  -- the level and weight of the scale `k`
  have hlev : ∀ k, Real.log (0.89 * f k / (2 * v)) =
      (k : ℝ) * Real.log 2 + c0 - Real.log (2 * v) := by
    intro k
    simp only [hf]
    rw [show 0.89 * (X0 * 2 ^ k / 4) / (2 * v) = 2 ^ k * (0.89 * X0 / 4) / (2 * v) by ring,
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hgm : ∀ m : ℕ, Real.log ((2 : ℝ) ^ m / (2 * v)) = m * Real.log 2 - Real.log (2 * v) :=
    fun m => LemS.log_pow_div hv m
  have hw : ∀ k, Real.log (2 * f k) = (k : ℝ) * Real.log 2 + Real.log (X0 / 2) := by
    intro k
    simp only [hf]
    rw [show 2 * (X0 * 2 ^ k / 4) = 2 ^ k * (X0 / 2) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hwc : Real.log (X0 / 2) - c0 ≤ 1.25 := by
    rw [hc0, ← Real.log_div (by positivity) (by positivity)]
    have e : X0 / 2 / (0.89 * X0 / 4) = 2 / 0.89 := by field_simp; ring
    rw [e]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 0.89 by norm_num)
    norm_num at this ⊢; linarith
  -- each relevant term is at most `(1 + 10⁻⁷) T (k + d)`
  set K := (range N).filter (fun k => ¬ 2.21 * f k < v) with hK
  have hstep : ∀ k ∈ K, Real.log (2 * f k) * Om8 v (f k) ≤ (1 + 1 / 10 ^ 7) * T (k + d) := by
    intro k hk
    have hkv := (Finset.mem_filter.mp hk).2
    push_neg at hkv
    unfold Om8
    rw [if_neg (not_lt.mpr hkv)]
    -- monotone shift of the level
    have hsh : LemS.OmB L (Real.log (0.89 * f k / (2 * v))) ≤
        LemS.OmB L (Real.log ((2 : ℝ) ^ (k + d) / (2 * v))) := by
      apply LemS.OmB_anti hL
      rw [hlev k, hgm (k + d)]; push_cast; nlinarith
    -- the weight
    have hwlow : L - 3 ≤ Real.log (2 * f k) := by
      have h1 : 2 * v / 2.21 ≤ 2 * f k := by
        rw [div_le_iff₀ (by norm_num)]; linarith
      have h2 : Real.log (2 * v / 2.21) ≤ Real.log (2 * f k) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_div (by positivity) (by norm_num)] at h2
      have : Real.log 2.21 ≤ 2.21 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have hwup : Real.log (2 * f k) ≤ (((k + d : ℕ) : ℝ) + 1) * Real.log 2 + 1.25 := by
      rw [hw k]; push_cast; nlinarith
    have hbig : 100000000 - 5 ≤ (((k + d : ℕ) : ℝ) + 1) * Real.log 2 := by linarith
    have hwle : Real.log (2 * f k) ≤ (1 + 1 / 10 ^ 7) * ((((k + d : ℕ) : ℝ) + 1) *
        Real.log 2) := by
      nlinarith
    have hO0 := LemS.OmB_nonneg L (Real.log (0.89 * f k / (2 * v)))
    have hw0 : 0 ≤ Real.log (2 * f k) := Real.log_nonneg (by linarith [hf3 k])
    calc Real.log (2 * f k) * LemS.OmB L (Real.log (0.89 * f k / (2 * v)))
        ≤ Real.log (2 * f k) * LemS.OmB L (Real.log ((2 : ℝ) ^ (k + d) / (2 * v))) :=
          mul_le_mul_of_nonneg_left hsh hw0
      _ ≤ (1 + 1 / 10 ^ 7) * ((((k + d : ℕ) : ℝ) + 1) * Real.log 2) *
          LemS.OmB L (Real.log ((2 : ℝ) ^ (k + d) / (2 * v))) :=
          mul_le_mul_of_nonneg_right hwle (LemS.OmB_nonneg _ _)
      _ = (1 + 1 / 10 ^ 7) * T (k + d) := by simp only [hT]; push_cast; ring
  -- the image levels satisfy `g_m > -4.7`
  have himg : ∀ k ∈ K, -(4.7 : ℝ) < Real.log ((2 : ℝ) ^ (k + d) / (2 * v)) := by
    intro k hk
    have hkv := (Finset.mem_filter.mp hk).2
    push_neg at hkv
    have h1 : 0.89 / 4.42 ≤ 0.89 * f k / (2 * v) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have h2 : Real.log (0.89 / 4.42) ≤ Real.log (0.89 * f k / (2 * v)) :=
      Real.log_le_log (by norm_num) h1
    have h3 : 1 - 1 / (0.89 / 4.42) ≤ Real.log (0.89 / 4.42) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.89 / 4.42 by norm_num)
      simpa [one_div] using this
    rw [hlev k] at h2
    rw [hgm (k + d)]; push_cast
    norm_num at h3
    nlinarith
  set I := K.image (· + d) with hI
  have hinjd : Set.InjOn (· + d) (K : Set ℕ) := fun a _ b _ h => by simpa using h
  -- reduce to the image levels
  have hred : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Om8 v u ≤
      (1 + 1 / 10 ^ 7) * ∑ m ∈ I, T m := by
    calc ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Om8 v u
        ≤ ∑ u ∈ (range N).image f, Real.log (2 * u) * Om8 v u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu; exact (Finset.mem_filter.mp hu).1
          · intro u hu _
            obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
            exact hterm0 _ (hf3 k)
      _ = ∑ k ∈ range N, Real.log (2 * f k) * Om8 v (f k) := Finset.sum_image hfinj
      _ = ∑ k ∈ K, Real.log (2 * f k) * Om8 v (f k) := by
          rw [hK, Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h : 2.21 * f k < v
          · rw [if_neg (not_not.mpr h)]; unfold Om8; rw [if_pos h, mul_zero]
          · rw [if_pos h]
      _ ≤ ∑ k ∈ K, (1 + 1 / 10 ^ 7) * T (k + d) := Finset.sum_le_sum hstep
      _ = (1 + 1 / 10 ^ 7) * ∑ m ∈ I, T m := by
          rw [← Finset.mul_sum, hI, Finset.sum_image hinjd]
  -- split the image levels
  have hmemI : ∀ m ∈ I, -(4.7 : ℝ) < Real.log ((2 : ℝ) ^ m / (2 * v)) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    exact himg k hk
  rw [← Finset.sum_filter_add_sum_filter_not I
    (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v)))] at hred
  have hB := LemS.partB_le hv hL (I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))))
    (fun m hm => (Finset.mem_filter.mp hm).2)
  have hBe : ∑ m ∈ I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))), T m =
      ∑ m ∈ I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))),
        ((m : ℝ) + 1) * Real.log 2 *
        (0.71 * Real.exp (-(0.99 * (Real.log ((2 : ℝ) ^ m / (2 * v)) / L - 1)))
          + 2 * Real.exp (-(√(Real.log ((2 : ℝ) ^ m / (2 * v))) / 2))) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have := (Finset.mem_filter.mp hm).2
    simp only [hT]; unfold LemS.OmB; rw [if_neg (not_lt.mpr this)]
  set I' := I.filter (fun m => ¬ L ≤ Real.log ((2 : ℝ) ^ m / (2 * v)))
  have hI'e : ∑ m ∈ I', T m = ∑ m ∈ I', ((m : ℝ) + 1) * Real.log 2 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have := (Finset.mem_filter.mp hm).2
    push_neg at this
    simp only [hT]; rw [OmB_le_one_of_lt this, mul_one]
  have hA := LemS.partA_le hv hL (I'.filter (fun m => v ≤ (2 : ℝ) ^ m)) (fun m hm => by
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    exact ⟨hm2, lt_of_not_ge (Finset.mem_filter.mp hm1).2⟩)
  -- the levels just below `v`: at most seven, each of weight `≤ L`
  set I3 := I'.filter (fun m => ¬ v ≤ (2 : ℝ) ^ m)
  set A0 := (Real.log (2 * v) - 4.7) / Real.log 2
  have hA0 : 0 ≤ A0 := div_nonneg (by linarith) hl2.le
  have hsub3 : I3 ⊆ Finset.Icc ⌊A0⌋₊ (⌊A0⌋₊ + 6) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    push_neg at hm2
    have hmI := (Finset.mem_filter.mp hm1).1
    have hg := hmemI m hmI
    rw [hgm m] at hg
    have hm2' : (m : ℝ) * Real.log 2 < Real.log v := by
      rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hm2
    have hlv : Real.log v = Real.log (2 * v) - Real.log 2 := by
      rw [Real.log_mul (by norm_num) hv.ne']; ring
    have hlo : A0 < m := by
      show (Real.log (2 * v) - 4.7) / Real.log 2 < m
      rw [div_lt_iff₀ hl2]; linarith
    have hhi : (m : ℝ) < A0 + 6 := by
      have : (m : ℝ) * Real.log 2 < (A0 + 6) * Real.log 2 := by
        show (m : ℝ) * Real.log 2 < ((Real.log (2 * v) - 4.7) / Real.log 2 + 6) * Real.log 2
        rw [add_mul, div_mul_cancel₀ _ hl2.ne']; linarith
      exact lt_of_mul_lt_mul_right this hl2.le
    have hf1 := Nat.floor_le hA0
    have hf2 := Nat.lt_floor_add_one A0
    rw [Finset.mem_Icc]
    constructor
    · have : (⌊A0⌋₊ : ℝ) < m := lt_of_le_of_lt hf1 hlo
      exact_mod_cast this.le
    · have : (m : ℝ) < ⌊A0⌋₊ + 7 := by linarith
      have : m < ⌊A0⌋₊ + 7 := by exact_mod_cast this
      omega
  have hcard3 : (I3.card : ℝ) ≤ 7 := by
    have h1 := Finset.card_le_card hsub3
    rw [Nat.card_Icc] at h1
    exact_mod_cast (show I3.card ≤ 7 by omega)
  have hterm3 : ∀ m ∈ I3, ((m : ℝ) + 1) * Real.log 2 ≤ L := by
    intro m hm
    have hm2 := (Finset.mem_filter.mp hm).2
    push_neg at hm2
    have : ((m : ℝ) + 1) * Real.log 2 = Real.log (2 * 2 ^ m) := by
      rw [← pow_succ', Real.log_pow]; push_cast; ring
    rw [this]
    exact (Real.log_le_log (by positivity) (by linarith)).trans hlog2v
  have hS3 : ∑ m ∈ I3, ((m : ℝ) + 1) * Real.log 2 ≤ 7 * L :=
    calc ∑ m ∈ I3, ((m : ℝ) + 1) * Real.log 2 ≤ ∑ _m ∈ I3, L := Finset.sum_le_sum hterm3
      _ = I3.card * L := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 * L := mul_le_mul_of_nonneg_right hcard3 (by linarith)
  have hL2 : 7 * L + 1 ≤ L ^ 2 := by nlinarith
  have hI'b : ∑ m ∈ I', ((m : ℝ) + 1) * Real.log 2 ≤ 3 * L ^ 2 + 7 * L := by
    rw [← Finset.sum_filter_add_sum_filter_not I' (fun m => v ≤ (2 : ℝ) ^ m)]
    exact add_le_add hA hS3
  have htot : ∑ m ∈ I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))), T m +
      ∑ m ∈ I', T m ≤ 3.2 * L ^ 2 + 1 + (3 * L ^ 2 + 7 * L) := by
    rw [hBe, hI'e]; linarith [hB, hI'b]
  have hpos : 0 ≤ ∑ m ∈ I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))), T m +
      ∑ m ∈ I', T m :=
    add_nonneg (Finset.sum_nonneg fun m _ => hT0 m) (Finset.sum_nonneg fun m _ => hT0 m)
  calc ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Om8 v u
      ≤ (1 + 1 / 10 ^ 7) * (∑ m ∈ I.filter (fun m => L ≤ Real.log ((2 : ℝ) ^ m / (2 * v))),
          T m + ∑ m ∈ I', T m) := hred
    _ ≤ (1 + 1 / 10 ^ 7) * (3.2 * L ^ 2 + 1 + (3 * L ^ 2 + 7 * L)) :=
        mul_le_mul_of_nonneg_left htot (by norm_num)
    _ ≤ 10 * L ^ 2 := by nlinarith

end KR.RML8G

end
