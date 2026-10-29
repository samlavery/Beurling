module

public import RequestProject.Beurling.Noise.RML12SzRank
public import RequestProject.Beurling.Noise.RML12SzBsc
public import RequestProject.Beurling.Noise.RML6BridgeNum
public import RequestProject.Beurling.Noise.KRWidthReal
public import RequestProject.Beurling.Model.G1BSec5
public import RequestProject.Beurling.Model.Wire3
public import RequestProject.Beurling.Queue6.NuBlock

/-!
# The sizes of Lemma 5.34 (round 12): `SK ≤ 10⁻²⁰` and `Gsum ≤ e^{-41} + 2·10⁻²²`

The Model's `G`-term `Gsum θ X₀ ω nb z = ∑_{i ≤ Jc z} (log 3v_i)² (o_i + F̄_r(i))` and the
`K`-term `SK θ X₀ ω nb x = ∑_{k < Jc x + 3} log(2u_k) GK(u_k)` (`v_i = X₀⁻2ⁱ`, `u_k = X₀2ᵏ/4`),
with `F̄_r(i) = o_i + 6/H(v_i) + ν̄_i + 2(s_η(i-1) + s_η(i) + s_η(i+1))` (`FrBv`), at `ν̄ = nbQ`.

* `sum_etaS_le` : `∑_{i < M} (log 3v_i)² s_η(i) ≤ 7·10⁷ Φ₃(X₀⁻/2)` (Lemma 5.20, `RML12SzRank`);
* `sum_FrBv_le` : `∑_{i ≤ N} (log 3v_i)² F̄_r(i) ≤ 7.4·10⁻¹⁹ + 1.6·10⁻²²` (with the sharp
  `sum_oscG_sharp`, `sum_sixH_le`, `Queue6.sum_nbQ_le`, `Phi_tiny`);
* `Gsum_le`, `SK_le` : the two size bounds, given the horizon at the last block read.

**Horizon.** Both sums run over the blocks `i ≤ Jc z (+ 4)`. `Jc` (Model, `RestWire.lean`) is a
`Classical.choose` of `pow_unbounded_of_one_lt`, i.e. *some* `n` with `z + H(z)/2 < X₀⁻2ⁿ`, not the
least one; so `X₀⁻2^{Jc z}` is not bounded in terms of `z`, and the blocks beyond the (H_BS)
horizon cannot be controlled (`s_η(i)` reads `𝒩` up to `3√(2v_i)`). The theorems therefore take
the horizon at the last block as a hypothesis (`hJ`); with the least `n` (`Nat.find`),
`X₀⁻2^{Jc z} ≤ 2(z + H(z)/2)` and `hJ` follows from `Zc` (`JcBound`, `hor_of_JcBound`).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction CaplLink Queue6 KR KR.TNP

namespace BModel.RML12

variable {θ : ℝ} {X₀ : ℕ}

/-- `log(3 v_i)`, `v_i = X₀⁻2ⁱ`. -/
noncomputable abbrev Lb (X₀ : ℕ) (i : ℕ) : ℝ := Real.log (3 * (Xm X₀ * 2 ^ i))

section

variable (hc : Cond θ X₀)
include hc

lemma Lb_ge (i : ℕ) : 100000000 ≤ Lb X₀ i := by
  have hX := hc.hX
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hX0 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have : Real.log X₀ ≤ Lb X₀ i := Real.log_le_log (by linarith) (by nlinarith)
  linarith

lemma Lb_succ (i : ℕ) : Lb X₀ (i + 1) = Lb X₀ i + Real.log 2 := by
  have hXm := Queue6.Xm_pos hc
  unfold Lb
  rw [pow_succ, show 3 * (Xm X₀ * (2 ^ i * 2)) = 3 * (Xm X₀ * 2 ^ i) * 2 by ring,
    Real.log_mul (by positivity) (by norm_num)]

lemma Lb_mono (i : ℕ) : Lb X₀ i ≤ Lb X₀ (i + 1) := by
  rw [Lb_succ hc]; have := Real.log_two_gt_d9; linarith

lemma Lb_succ_sq_le (i : ℕ) : Lb X₀ (i + 1) ^ 2 ≤ 4 * Lb X₀ i ^ 2 := by
  rw [Lb_succ hc]
  have := Lb_ge hc i
  have := Real.log_two_lt_d9
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

omit hc in
/-- `blk` is monotone in the number of levels. -/
lemma blk_mono {P : BeurlingSystem} {H : ℝ → ℝ} {X0m ε' θ' : ℝ}
    (hP : PaperWidth H X0m ε' θ') {K K' : ℕ} (hKK : K ≤ K') (v : ℝ) :
    TNP.blk P H X0m K (fun _ => 1) v ≤ TNP.blk P H X0m K' (fun _ => 1) v := by
  have hX := hP.X0m_pos
  unfold TNP.blk
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr hKK) fun k _ _ => ?_
  refine mul_nonneg ?_ (Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le)
  have := hP.reg.pos (Pk X0m k); have := Pk_pos hX k
  positivity

omit hc in
lemma sep_image {X : ℝ} (hX : 0 < X) (M : ℕ) :
    Sep ((Finset.range M).image fun i => X * 2 ^ i) := by
  intro v hv w hw hvw
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
  have hkl : k < l := by
    by_contra h; push_neg at h
    have : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) h
    nlinarith
  have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hkl
  rw [pow_succ] at this
  nlinarith

/-- **Lemma 5.20's blocks at the dyadic scales**: `∑_{i < M} (log 3v_i)² s_η(i) ≤ 7·10⁷ Φ₃`. -/
theorem sum_etaS_le {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    (hZ0 : 2500 ≤ Z) (M : ℕ) (hZ : 18 * (Xm X₀ * 2 ^ M) ≤ Z ^ 2) :
    ∑ i ∈ range M, Lb X₀ i ^ 2 * etaS θ X₀ ω i ≤
      70000000 * TNP.Phi (Queue6.Hc X₀) 3 (Xm X₀ / 2) := by
  have hXm := Queue6.Xm_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  set K := (range M).sup (Keta X₀)
  set Sc := (range M).image fun i => Xm X₀ * 2 ^ i
  have hinj : Set.InjOn (fun i : ℕ => Xm X₀ * 2 ^ i) (Finset.range M : Set ℕ) := by
    intro a _ c _ hac
    simp only at hac
    have : (2 : ℝ) ^ a = 2 ^ c := mul_left_cancel₀ hXm0.ne' hac
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)
  have hS : Sep Sc := sep_image hXm0 M
  have hSc : ∀ v ∈ Sc, 1 ≤ v := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    nlinarith
  have hSZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2 := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have : (2 : ℝ) ^ i ≤ 2 ^ M :=
      pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hi).le
    nlinarith
  have hmain := KR.RML12.sum_blk_logsq_le hT hS hSc hZ0 hSZ K
  rw [Finset.sum_image hinj] at hmain
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) hmain
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact blk_mono hT.width (Finset.le_sup (f := Keta X₀) hi) _

omit hc in
lemma exp_neg41_ge' : (148 : ℝ) / 10 ^ 20 ≤ Real.exp (-41) := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 41 = Real.exp 1 ^ 41 := by rw [← Real.exp_nat_mul]; norm_num
  have h41 : Real.exp 41 ≤ 10 ^ 20 / 148 := by
    rw [e]
    calc Real.exp 1 ^ 41 ≤ 2.7182818286 ^ 41 := by gcongr
      _ ≤ 10 ^ 20 / 148 := by norm_num
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  calc (148 : ℝ) / 10 ^ 20 * Real.exp 41 ≤ 148 / 10 ^ 20 * (10 ^ 20 / 148) := by gcongr
    _ = 1 := by norm_num

omit hc in
lemma exp_neg200_le : Real.exp (-200) ≤ 1 / 10 ^ 80 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (10 : ℝ) ^ 80 ≤ Real.exp 200 := by
    rw [e]
    calc (10 : ℝ) ^ 80 ≤ 2.7 ^ 200 := by norm_num
      _ ≤ Real.exp 1 ^ 200 := by gcongr; linarith [h]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h2

set_option maxHeartbeats 4000000 in
/-- **The block sum of `F̄_r`**: `∑_{i ≤ N} (log 3v_i)² F̄_r(i) ≤ 7.4·10⁻¹⁹ + 1.6·10⁻²²` at
`ν̄ = nbQ`, given the horizon `18 v_{N+2} ≤ Z²`. -/
theorem sum_FrBv_le {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    (hZ0 : 2500 ≤ Z) (N : ℕ) (hZ : 18 * (Xm X₀ * 2 ^ (N + 2)) ≤ Z ^ 2) :
    ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * FrBv θ X₀ ω (nbQ X₀) i ≤
      74 / 10 ^ 20 + 16 / 10 ^ 23 := by
  have hX := hc.hX
  have hE := sum_etaS_le hc hT hZ0 (N + 2) hZ
  have hPhi := KR.WidthReal.Phi_tiny hT (KR.WidthReal.Hc_Xm_half_le hX) (a := 3) (by norm_num)
  have he200 := exp_neg200_le
  have hE' : ∑ i ∈ range (N + 2), Lb X₀ i ^ 2 * etaS θ X₀ ω i ≤ 1 / 10 ^ 70 := by
    have : 70000000 * TNP.Phi (Queue6.Hc X₀) 3 (Xm X₀ / 2) ≤ 70000000 * (1 / 10 ^ 80) := by
      gcongr; linarith
    linarith [this, show (70000000 : ℝ) * (1 / 10 ^ 80) ≤ 1 / 10 ^ 70 by norm_num]
  have he0 : ∀ i, 0 ≤ etaS θ X₀ ω i := fun i => etaS_nonneg hc hT i
  -- the three shifted `s_η`-sums
  have hE1 : ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * etaS θ X₀ ω i ≤ 1 / 10 ^ 70 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr
      (by omega)) fun i _ _ => mul_nonneg (sq_nonneg _) (he0 i)) hE'
  have hE2 : ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * etaS θ X₀ ω (i + 1) ≤ 1 / 10 ^ 70 := by
    have h1 : ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * etaS θ X₀ ω (i + 1) ≤
        ∑ i ∈ range (N + 1), Lb X₀ (i + 1) ^ 2 * etaS θ X₀ ω (i + 1) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (he0 _)
      have hm := Lb_mono hc i; have := Lb_ge hc i
      exact pow_le_pow_left₀ (by linarith) hm 2
    have h2 := Finset.sum_range_succ' (fun i => Lb X₀ i ^ 2 * etaS θ X₀ ω i) (N + 1)
    have h3 : 0 ≤ Lb X₀ 0 ^ 2 * etaS θ X₀ ω 0 := mul_nonneg (sq_nonneg _) (he0 0)
    linarith
  have hE3 : ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 *
      (if i = 0 then 0 else etaS θ X₀ ω (i - 1)) ≤ 4 / 10 ^ 70 := by
    rw [Finset.sum_range_succ']
    simp only [if_true, mul_zero, add_zero, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    calc ∑ i ∈ range N, Lb X₀ (i + 1) ^ 2 * etaS θ X₀ ω i
        ≤ ∑ i ∈ range N, 4 * (Lb X₀ i ^ 2 * etaS θ X₀ ω i) :=
          Finset.sum_le_sum fun i _ => by
            have := Lb_succ_sq_le hc i; have := he0 i; nlinarith
      _ = 4 * ∑ i ∈ range N, Lb X₀ i ^ 2 * etaS θ X₀ ω i := by rw [Finset.mul_sum]
      _ ≤ 4 * (1 / 10 ^ 70) := by
          gcongr
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr
            (by omega)) fun i _ _ => mul_nonneg (sq_nonneg _) (he0 i)) hE'
      _ = 4 / 10 ^ 70 := by ring
  have hB := sum_oscG_sharp hX N
  have hH := sum_sixH_le hX N
  have hn := Queue6.sum_nbQ_le hc (N + 1)
  have e : ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * FrBv θ X₀ ω (nbQ X₀) i =
      ∑ i ∈ range (N + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i +
      ∑ i ∈ range (N + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 *
        (6 / Queue6.Hc X₀ (Xm X₀ * 2 ^ i)) +
      ∑ i ∈ range (N + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * nbQ X₀ i +
      2 * (∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * (if i = 0 then 0 else etaS θ X₀ ω (i - 1)) +
        ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * etaS θ X₀ ω i +
        ∑ i ∈ range (N + 1), Lb X₀ i ^ 2 * etaS θ X₀ ω (i + 1)) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold FrBv obG Lb
    ring
  rw [e]
  have h74 : (34 : ℝ) * (1 / 10 ^ 43) ≤ 1 / 10 ^ 40 := by norm_num
  linarith


/-- `G(z) ≤ e^{-41} + 2·10⁻²²` given the horizon at the block `Jc z + 2`. -/
theorem Gsum_le {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    (hZ0 : 2500 ≤ Z) (z : ℝ) (hZ : 18 * (Xm X₀ * 2 ^ (Jc X₀ z + 2)) ≤ Z ^ 2) :
    Gsum θ X₀ ω (nbQ X₀) z ≤ Real.exp (-41) + 2 / 10 ^ 22 := by
  have hF := sum_FrBv_le hc hT hZ0 (Jc X₀ z) hZ
  have hB := sum_oscG_sharp hc.hX (Jc X₀ z)
  have he := exp_neg41_ge'
  unfold Gsum
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [Lb] at hF
  linarith

lemma two_u_le {u : ℝ} (hu : 0 < u) (i : ℕ) (h : 0.79 * u < 2 * (Xm X₀ * 2 ^ i)) :
    Real.log (2 * u) * 1 ≤ 2 / 10 ^ 8 * Lb X₀ i ^ 2 := by
  have hL := Lb_ge hc i
  have hXm := Queue6.Xm_pos hc
  have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hv : 1 ≤ Xm X₀ * 2 ^ i := by nlinarith
  have h2 : Real.log (2 * u) ≤ 2 * Lb X₀ i := by
    unfold Lb
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [show (3 * (Xm X₀ * 2 ^ i)) ^ (2 : ℝ) = (3 * (Xm X₀ * 2 ^ i)) ^ (2 : ℕ) by norm_cast]
    nlinarith
  have : 2 * Lb X₀ i ≤ 2 / 10 ^ 8 * Lb X₀ i ^ 2 := by nlinarith
  linarith

/-- The blocks read by `GK(u_k)`: `i ≤ k ≤ i + 3`. -/
lemma GK_index {i k : ℕ}
    (h : (i = 0 ∨ Xm X₀ * 2 ^ i ≤ 2.21 * ((X₀ : ℝ) * 2 ^ k / 4)) ∧
      0.79 * ((X₀ : ℝ) * 2 ^ k / 4) < 2 * (Xm X₀ * 2 ^ i)) : i ≤ k ∧ k ≤ i + 3 := by
  have hXm := Queue6.Xm_pos hc
  have hXg := KR.WidthReal.Xm_ge hc.hX (X₀ := X₀)
  have hXl := Xm_le_X0 hc
  have p2 : ∀ a b : ℕ, (2 : ℝ) ^ a < 2 ^ b → a < b := fun a b hab =>
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hab
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · omega
    · have : (2 : ℝ) ^ i < 2 ^ (k + 1) := by
        rw [pow_succ]
        have : (0 : ℝ) < 2 ^ k := by positivity
        nlinarith
      have := p2 _ _ this; omega
  · have : (2 : ℝ) ^ k < 2 ^ (i + 4) := by
      rw [pow_add]
      have : (0 : ℝ) < 2 ^ i := by positivity
      have : (0 : ℝ) < 2 ^ k := by positivity
      nlinarith
    have := p2 _ _ this; omega

set_option maxHeartbeats 2000000 in
/-- `S(x) ≤ 10⁻²⁰` given the horizon at the block `Jc x + 4`. -/
theorem SK_le (hev : Even X₀) {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    (hZ0 : 2500 ≤ Z) (x : ℝ) (hZ : 18 * (Xm X₀ * 2 ^ (Jc X₀ x + 4)) ≤ Z ^ 2) :
    SK θ X₀ ω (nbQ X₀) x ≤ 1 / 10 ^ 20 := by
  set J := Jc X₀ x
  set F := fun i => 2 / 10 ^ 8 * Lb X₀ i ^ 2 * FrBv θ X₀ ω (nbQ X₀) i
  have hF0 : ∀ i, 0 ≤ F i := fun i =>
    mul_nonneg (by positivity) (FrBv_nonneg hc hev hT (nbQ_nonneg hc) i)
  have hX0 := KR.WidthReal.X0_ge hc.hX (X₀ := X₀)
  -- each scale reads the blocks `i ≤ k ≤ i + 3`
  have hk : ∀ k ∈ range (J + 3), Real.log (2 * ((X₀ : ℝ) * 2 ^ k / 4)) *
      GK θ X₀ ω (nbQ X₀) ((X₀ : ℝ) * 2 ^ k / 4) ≤
      ∑ i ∈ range (J + 3), if i ≤ k ∧ k ≤ i + 3 then F i else 0 := by
    intro k hk
    have hu : (0 : ℝ) < (X₀ : ℝ) * 2 ^ k / 4 := by positivity
    unfold GK
    rw [Finset.mul_sum]; simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    calc _ ≤ ∑ i ∈ (range (⌈2.21 * ((X₀ : ℝ) * 2 ^ k / 4) / Xm X₀⌉₊ + 1)).filter
          (fun i => (i = 0 ∨ Xm X₀ * 2 ^ i ≤ 2.21 * ((X₀ : ℝ) * 2 ^ k / 4)) ∧
            0.79 * ((X₀ : ℝ) * 2 ^ k / 4) < 2 * (Xm X₀ * 2 ^ i)), F i := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hc' := (Finset.mem_filter.mp hi).2
          have := two_u_le hc hu i hc'.2
          have := FrBv_nonneg hc hev hT (nbQ_nonneg hc) i
          simp only [F]; nlinarith
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => hF0 i
          have hc' := (Finset.mem_filter.mp hi).2
          have hik := GK_index hc hc'
          have := Finset.mem_range.mp hk
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hik⟩
  have hcnt : ∀ i, ∑ k ∈ range (J + 3), (if i ≤ k ∧ k ≤ i + 3 then F i else 0) ≤ 4 * F i := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (range (J + 3)).filter (fun k => i ≤ k ∧ k ≤ i + 3) ⊆ Finset.Icc i (i + 3) :=
      fun k hk => Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
    have hc4 : (((range (J + 3)).filter (fun k => i ≤ k ∧ k ≤ i + 3)).card : ℝ) ≤ 4 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : _ ≤ 4)
    exact mul_le_mul_of_nonneg_right hc4 (hF0 i)
  have hFs := sum_FrBv_le hc hT hZ0 (J + 2) hZ
  unfold SK
  calc _ ≤ ∑ k ∈ range (J + 3), ∑ i ∈ range (J + 3), (if i ≤ k ∧ k ≤ i + 3 then F i else 0) :=
        Finset.sum_le_sum hk
    _ = ∑ i ∈ range (J + 3), ∑ k ∈ range (J + 3), (if i ≤ k ∧ k ≤ i + 3 then F i else 0) :=
        Finset.sum_comm
    _ ≤ ∑ i ∈ range (J + 3), 4 * F i := Finset.sum_le_sum fun i _ => hcnt i
    _ = 8 / 10 ^ 8 * ∑ i ∈ range (J + 2 + 1), Lb X₀ i ^ 2 * FrBv θ X₀ ω (nbQ X₀) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp only [F]; ring
    _ ≤ 8 / 10 ^ 8 * (74 / 10 ^ 20 + 16 / 10 ^ 23) := by gcongr
    _ ≤ 1 / 10 ^ 20 := by norm_num

end

variable (X₀) in
/-- **`Jc` is the least dyadic count** (Model, `RestWire.Jc`; open — see the module doc): at the
centres `X₀^{1.01} ≤ t ≤ b`, `X₀⁻2^{Jc t} ≤ 2(t + H(t)/2)`. True for `Jc := Nat.find`. -/
def JcBound (b : ℝ) : Prop :=
  ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → Xm X₀ * 2 ^ Jc X₀ t ≤ 2 * (t + Queue6.Hc X₀ t / 2)

section Fields

variable (hc : Cond θ X₀)
include hc

/-- The horizon at the last block read: `18 X₀⁻2^{Jc t + 4} ≤ Z_c(b)²`. -/
lemma hor_of_JcBound {b : ℝ} (hb : (X₀ : ℝ) ≤ b) (hJ : JcBound X₀ b) {t : ℝ}
    (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) (htb : t ≤ b) :
    18 * (Xm X₀ * 2 ^ (Jc X₀ t + 4)) ≤ Zc X₀ b ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := KR.WidthReal.X0_ge hc.hX (X₀ := X₀)
  have hXg := KR.WidthReal.Xm_ge hc.hX (X₀ := X₀)
  have hXt : (X₀ : ℝ) ≤ t := by
    refine le_trans ?_ ht
    conv_lhs => rw [← Real.rpow_one (X₀ : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hH : Queue6.Hc X₀ t ≤ t / 4 := by
    unfold Queue6.Hc
    rw [max_eq_left hXt]
    have := four_capH_le hX0 hc.hX hXt
    linarith
  have h1 := hJ t ht htb
  have e : Xm X₀ * 2 ^ (Jc X₀ t + 4) = 16 * (Xm X₀ * 2 ^ Jc X₀ t) := by rw [pow_add]; ring
  rw [e]
  have h2 : 18 * (16 * (Xm X₀ * 2 ^ Jc X₀ t)) ≤ 648 * b := by linarith
  refine h2.trans ?_
  unfold Zc
  split_ifs with hbig
  · nlinarith
  · push_neg at hbig
    nlinarith

variable (hev : Even X₀)
include hev

/-- **`RestMarginH.hSbX` at `ν̄ = nbQ`** (Lemma 5.34, first bullet). -/
theorem hSbX_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) η1 η2 ε1 εH θH)
    (hJ : JcBound X₀ b) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → SK θ X₀ ω (Queue6.nbQ X₀) t ≤ 1 / 10 ^ 20 :=
  fun t ht htb => SK_le hc hev hT (Zc_facts hc hb).2.1 t (hor_of_JcBound hc hb hJ ht htb)

/-- **`RestMarginH.hGX` at `ν̄ = nbQ`** (Lemma 5.34, second bullet). -/
theorem hGX_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) η1 η2 ε1 εH θH)
    (hJ : JcBound X₀ b) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      Gsum θ X₀ ω (Queue6.nbQ X₀) t ≤ Real.exp (-41) + 2 / 10 ^ 22 := by
  intro t ht htb
  refine Gsum_le hc hT (Zc_facts hc hb).2.1 t ?_
  refine le_trans ?_ (hor_of_JcBound hc hb hJ ht htb)
  have : (2 : ℝ) ^ (Jc X₀ t + 2) ≤ 2 ^ (Jc X₀ t + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have := Queue6.Xm_pos hc
  nlinarith

end Fields

end BModel.RML12

end
