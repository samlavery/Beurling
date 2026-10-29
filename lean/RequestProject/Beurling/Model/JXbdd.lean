module

public import RequestProject.Beurling.Model.JXnn
public import RequestProject.Beurling.Noise.RML7XBKern
public import RequestProject.Beurling.Noise.BridgeG1Resp

/-!
# The eq. (jX0) family is bounded on `W_x` (the field `hbdd`)

`j_{X₀}(x)` (eq. (jX0), Proposition 5.33) is the supremum over the window `W_x` of
`j₀ (𝔹(y) + 4.3 C_N S(y)/log y) log y`. On `W_x ⊂ [X₀, Y]`, `Y = x + H(x)/2`, both parts are
bounded uniformly in `y` (crudely):

* `𝔹(y)` is a sum over the levels `n` of `y`, a subset of the levels of `Y`, of
  `(|c_n|/2 + ∑_{d ∣ n} step_d)/n`, and each step is bounded through the kernel bounds
  (TVD-bounds) (`halfTVD_le`, `KRD_le`) by a quantity depending on `d` and `H(Y)` only;
* `S(y) = ∑_v log(2v) s_θ(v)` runs over the dyadic scales `≤ Y`, and the block sums `s_θ(v)`
  only see the blocks `k` with `P_k² ≤ 2v` (`SmB` is empty beyond), uniformly in `K`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP

namespace BModel

section Generic

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- The crude step bound `B(d) = 1 + (λ₀/4 + λ₀²/4) H_Y ∑_{e ∣ d} H_ord(d/e) e`. -/
noncomputable def stepB (P : BeurlingSystem) (lam0 HY : ℝ) (d : ℕ) : ℝ :=
  1 + (lam0 / 4 + lam0 * (lam0 / 4)) * HY *
    ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e

lemma sumD_nonneg (P : BeurlingSystem) (d : ℕ) :
    0 ≤ ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e :=
  Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _)
    (le_trans zero_le_one (LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)))

lemma one_le_valN' (P : BeurlingSystem) (n : ℕ) : 1 ≤ LemmaM.valN P.labelVal n :=
  LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)

/-- The partial `e`-sums of the kernel bounds are at most `H_Y ∑_{e ∣ d} H_ord(d/e) e`. -/
lemma esum_le {ε θ HY y : ℝ} (ht : ∀ p, p.Prime → 0 < tw p) (hX : 0 ≤ X0m) (hy : X0m ≤ y)
    (hH1 : ∀ z, 1 ≤ H z) (hHY : ∀ z, z ≤ y → H z ≤ HY) (hy0 : 0 ≤ y) (d : ℕ)
    (s : Finset ℕ) (hs : s ⊆ d.divisors.filter (1 < ·)) (w : ℕ → ℝ)
    (hw : ∀ e ∈ s, 0 ≤ w e ∧ w e ≤ Hlev P.labelVal y H e) :
    ∑ e ∈ s, |cN P tw X0m y e| * w e * (BSCert.X0Band.Hord (d / e) : ℝ) *
      (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) ≤
    HY * ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e := by
  have hHY0 : 0 ≤ HY := le_trans zero_le_one ((hH1 0).trans (hHY 0 hy0))
  rw [Finset.mul_sum]
  calc _ ≤ ∑ e ∈ s, HY * ((BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he1 : 1 < e := (Finset.mem_filter.mp (hs he)).2
        have hc := KR.G1.abs_cN_le_one (P := P) ht hX hy e (by omega)
        have hc0 := abs_nonneg (cN P tw X0m y e)
        obtain ⟨hw0, hw1⟩ := hw e he
        have hHl : Hlev P.labelVal y H e ≤ HY := by
          unfold Hlev posn
          refine hHY _ (div_le_self hy0 (one_le_valN' P e))
        have hv1 := one_le_valN' P e
        have hv2 := one_le_valN' P d
        have hq : LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d ≤
            LemmaM.valN P.labelVal e := div_le_self (by linarith) hv2
        have hq0 : 0 ≤ LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d := by positivity
        have hO : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
        have h1 : |cN P tw X0m y e| * w e ≤ HY := by nlinarith
        calc |cN P tw X0m y e| * w e * (BSCert.X0Band.Hord (d / e) : ℝ) *
              (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d)
            ≤ HY * (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hO) hq hq0 (by positivity)
          _ = _ := by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (hs.trans (Finset.filter_subset _ _))
          fun e _ _ => ?_
        exact mul_nonneg hHY0 (mul_nonneg (Nat.cast_nonneg _)
          (le_trans zero_le_one (one_le_valN' P e)))

/-- **The step bound**: every step of `𝔹(y)` is at most `stepB`. -/
lemma xbBstep_le_stepB {ε θ X0 lam0 HY y : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hy : X0m ≤ y) (hH1 : ∀ z, 1 ≤ H z) (hHY : ∀ z, z ≤ y → H z ≤ HY) {n d : ℕ}
    (hd : d ∈ n.properDivisors) :
    xbBstep P H tw X0m y X0 θ lam0 d n ≤ stepB P lam0 HY d := by
  have hX := hP.X0m_pos
  have hy0 : 0 ≤ y := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hHY0 : 0 ≤ HY := le_trans zero_le_one ((hH1 0).trans (hHY 0 hy0))
  have hS := sumD_nonneg P d
  have hB1 : 1 ≤ stepB P lam0 HY d := by
    unfold stepB
    have : 0 ≤ (lam0 / 4 + lam0 * (lam0 / 4)) * HY *
        ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e := by
      positivity
    linarith
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hd
    rw [zero_dvd_iff] at h1; omega
  unfold xbBstep
  split_ifs with h1 h2 h3 h4
  · linarith
  · linarith
  · -- `½ TV(D_d)`
    have hd2 : 2 ≤ d := by omega
    refine (KR.XB7.halfTVD_le hP hp2 ht hlam hy hd2).trans ?_
    have hc := KR.G1.abs_cN_le_one (P := P) ht hX.le hy d (by omega)
    have he := esum_le (H := H) (ε := ε) (θ := θ) ht hX.le hy hH1 hHY hy0 d
      (d.divisors.filter (fun e => 1 < e ∧ e < d))
      (fun e he => by
        simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, he.2.1⟩)
      (fun e => Hlev P.labelVal y H e / Hlev P.labelVal y H d) (fun e _ => by
        have h1 : 1 ≤ Hlev P.labelVal y H d := hH1 _
        have h0 : 0 ≤ Hlev P.labelVal y H e := le_trans zero_le_one (hH1 _)
        exact ⟨div_nonneg h0 (by linarith), div_le_self h0 h1⟩)
    have e1 : ∀ e, |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
        (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) =
        |cN P tw X0m y e| * (fun e => Hlev P.labelVal y H e / Hlev P.labelVal y H d) e *
        (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) := fun e => rfl
    simp only [e1]
    unfold stepB
    have h4' : 0 ≤ lam0 * (lam0 / 4) * HY *
        ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e := by
      positivity
    have h5 := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 1 / 4 * lam0 by positivity)
    nlinarith
  · -- `λ₀ ‖D_d‖_KR / (n/d · H)`
    have hd2 : 2 ≤ d := by omega
    have hK := KR.XB7.KRD_le hP hp2 ht hlam hy hd2 (tw := tw)
    have he := esum_le (H := H) (ε := ε) (θ := θ) ht hX.le hy hH1 hHY hy0 d
      (d.divisors.filter (1 < ·)) (subset_refl _) (fun e => Hlev P.labelVal y H e)
      (fun e _ => ⟨le_trans zero_le_one (hH1 _), le_rfl⟩)
    have hK0 : 0 ≤ KRD P H tw X0m y d := by unfold KRD; positivity
    have hV := KR.Sharp.Vl_pos P (n / d)
    have hV1 : 1 ≤ Vl P (n / d) := one_le_valN' P (n / d)
    have hHn := hH1 (posn P.labelVal y n)
    have hq : lam0 * KRD P H tw X0m y d / (Vl P (n / d) * H (posn P.labelVal y n)) ≤
        lam0 * KRD P H tw X0m y d := by
      apply div_le_self (by positivity)
      nlinarith
    refine hq.trans ?_
    unfold stepB
    have h5 : KRD P H tw X0m y d ≤ 1 / 4 * lam0 * (HY *
        ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e) :=
      hK.trans (mul_le_mul_of_nonneg_left he (by positivity))
    have h6 := mul_le_mul_of_nonneg_left h5 hlam0
    have h7 : 0 ≤ lam0 / 4 * HY *
        ∑ e ∈ d.divisors, (BSCert.X0Band.Hord (d / e) : ℝ) * LemmaM.valN P.labelVal e := by
      positivity
    nlinarith
  · linarith

/-- The crude level-sum bound `𝔹_Y = ∑_{n ∈ levels(Y)} (1/2 + ∑_{d ∣ n} B(d))`. -/
noncomputable def xbBound (P : BeurlingSystem) (X0m lam0 HY Y : ℝ) : ℝ :=
  ∑ n ∈ levels P X0m Y, (1 / 2 + ∑ d ∈ n.properDivisors, stepB P lam0 HY d)

/-- **`𝔹(y) ≤ 𝔹_Y`** for `X₀⁻ ≤ y ≤ Y`, `H ≥ 1`, `H ≤ H_Y` below `y`. -/
lemma xbB_le_bound {ε θ X0 lam0 HY y Y : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hy : X0m ≤ y) (hyY : y ≤ Y) (hH1 : ∀ z, 1 ≤ H z) (hHY : ∀ z, z ≤ y → H z ≤ HY) :
    xbB P H tw X0m y X0 θ lam0 ≤ xbBound P X0m lam0 HY Y := by
  have hX := hP.X0m_pos
  have hy0 : 0 ≤ y := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hHY0 : 0 ≤ HY := le_trans zero_le_one ((hH1 0).trans (hHY 0 hy0))
  have hB0 : ∀ d, 0 ≤ stepB P lam0 HY d := fun d => by
    unfold stepB; have := sumD_nonneg P d; positivity
  have hT0 : ∀ n : ℕ, 0 ≤ 1 / 2 + ∑ d ∈ n.properDivisors, stepB P lam0 HY d := fun n => by
    have := Finset.sum_nonneg fun d (_ : d ∈ n.properDivisors) => hB0 d; linarith
  unfold xbB xbBound
  calc _ ≤ ∑ n ∈ levels P X0m y, (1 / 2 + ∑ d ∈ n.properDivisors, stepB P lam0 HY d) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hV := one_le_valN' P n
        have hnum : ((if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
            then |cN P tw X0m y n| / 2 else 0) +
            ∑ d ∈ n.properDivisors, xbBstep P H tw X0m y X0 θ lam0 d n) ≤
            1 / 2 + ∑ d ∈ n.properDivisors, stepB P lam0 HY d := by
          have h1 : (if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
              then |cN P tw X0m y n| / 2 else 0) ≤ 1 / 2 := by
            have hn2 := (Finset.mem_filter.mp hn).2
            have hc := KR.G1.abs_cN_le_one (P := P) ht hX.le hy n (by omega)
            split_ifs <;> linarith
          have h2 := Finset.sum_le_sum fun d (hd : d ∈ n.properDivisors) =>
            xbBstep_le_stepB (X0 := X0) hP hp2 ht hlam hy hH1 hHY hd
          linarith
        have hnum0 : 0 ≤ ((if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
            then |cN P tw X0m y n| / 2 else 0) +
            ∑ d ∈ n.properDivisors, xbBstep P H tw X0m y X0 θ lam0 d n) := by
          have := xbB_nonneg (P := P) (tw := tw) (X0m := X0m) (X0 := X0) (θ' := θ)
            (fun z => lt_of_lt_of_le one_pos (hH1 z)) hlam0 y
          refine add_nonneg ?_ (Finset.sum_nonneg fun d _ => ?_)
          · split_ifs
            · positivity
            · exact le_rfl
          · unfold xbBstep
            have hT : 0 ≤ TVD P H tw X0m y d := by unfold TVD; positivity
            have hK : 0 ≤ KRD P H tw X0m y d := by unfold KRD; positivity
            have hV' := KR.Sharp.Vl_pos P (n / d)
            have hHn := hH1 (posn P.labelVal y n)
            split_ifs <;> positivity
        calc _ ≤ ((if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
              then |cN P tw X0m y n| / 2 else 0) +
              ∑ d ∈ n.properDivisors, xbBstep P H tw X0m y X0 θ lam0 d n) :=
              div_le_self hnum0 hV
          _ ≤ _ := hnum
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hT0 n
        intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
        refine Finset.mem_filter.mpr ⟨?_, h2⟩
        have h1' := (KR.Sharp.mem_NAll_iff P (by linarith : 0 < X0m / 2)).mp h1
        refine (KR.Sharp.mem_NAll_iff P (by linarith : 0 < X0m / 2)).mpr ⟨h1'.1, ?_⟩
        exact h1'.2.trans (div_le_div_of_nonneg_right hyY (by linarith))

/-- The `k`-th block term of `s_θ(v)`. -/
noncomputable def blkT (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
    ∑ e ∈ SmB P X0m k v, 1 / P.val e

lemma blkT_nonneg (hX : 2 ≤ X0m) (hH : ∀ z, 0 ≤ H z) (k : ℕ) (v : ℝ) :
    0 ≤ blkT P H X0m k v := by
  unfold blkT
  have hP1 : 1 ≤ Pk X0m k := by
    unfold Pk
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have := Real.log_nonneg hP1
  have := hH (Pk X0m k)
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => ?_)
  have := P.one_le_val e
  positivity

/-- `SmB_k(v) = ∅` once `k ≥ ⌈2Y⌉₊ + 1 > 2v`: `s_θ(v)` is bounded uniformly in `K`. -/
lemma sTheta_le (hX : 2 ≤ X0m) (hH : ∀ z, 0 ≤ H z) {v Y : ℝ} (hvY : v ≤ Y) (K : ℕ) :
    sTheta P H X0m K v ≤ ∑ k ∈ range (⌈2 * Y⌉₊ + 1), blkT P H X0m k v := by
  set K0 := ⌈2 * Y⌉₊ + 1
  have hz : ∀ k, K0 ≤ k → blkT P H X0m k v = 0 := by
    intro k hk
    unfold blkT
    rw [Finset.sum_eq_zero, mul_zero]
    intro e he
    exfalso
    simp only [SmB, Finset.mem_filter, BeurlingSystem.mem_elems] at he
    have hv1 := P.one_le_val e
    have hPk : (2 : ℝ) ^ k ≤ Pk X0m k := by unfold Pk; nlinarith [pow_pos (two_pos (α := ℝ)) k]
    have hk2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hK0 : 2 * Y < K0 := by
      have := Nat.le_ceil (2 * Y); simp only [K0]; push_cast; linarith
    have hkK : (K0 : ℝ) ≤ k := by exact_mod_cast hk
    have hP0 : 0 < Pk X0m k := by linarith [pow_pos (two_pos (α := ℝ)) k]
    have h1 : 1 ≤ 2 * v / Pk X0m k ^ 2 := hv1.trans he.1
    rw [le_div_iff₀ (by positivity)] at h1
    have hP1 : 1 ≤ Pk X0m k := le_trans (one_le_pow₀ (by norm_num)) hPk
    have : Pk X0m k ≤ Pk X0m k ^ 2 := by nlinarith
    linarith
  show KR.TNP.blk P H X0m K _ v ≤ _
  unfold KR.TNP.blk
  have e : ∀ k, 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
      ∑ e ∈ SmB P X0m k v, 1 / P.val e = blkT P H X0m k v := fun k => rfl
  simp only [e]
  rcases le_total K K0 with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
      fun k _ _ => blkT_nonneg hX hH k v
  · rw [← Finset.sum_subset (Finset.range_subset_range.mpr h) fun k hk hk' => by
      simp only [Finset.mem_range, not_lt] at hk'
      exact hz k hk']

end Generic

section Real

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **The eq. (jX0) family is bounded on `W_x`** (Proposition 5.33; the field `hbdd`), for the
realised system with (H_BS) on `[1, Zc b]` (through `KR.TNP.Hyp`). -/
theorem hbdd_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10)) :
    ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ x) x y} =>
        jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
          (NKc X₀ y.1).1 (NKc X₀ y.1).2 y.1) := by
  intro x hx _
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm2 : (2 : ℝ) ≤ Xm X₀ := by
    have := KR.WidthReal.Xm_ge hX (X₀ := X₀); linarith
  have hP := hT.width
  have hp2 := KR.Chain.p_ge_two_of hT (Xm_le_Zc' hc b)
  have ht := (KR.Chain.dec_R hT).1
  have hlam : 1 + 2 * (epsH / 10) ≤ lamH := by norm_num [epsH, lamH]
  have hlam0 : (0 : ℝ) ≤ lamH := by norm_num [lamH]
  have hH1 : ∀ z, 1 ≤ Queue6.Hc X₀ z := fun z => by
    unfold Queue6.Hc; exact KR.WidthReal.capH_one_le hX (le_max_right _ _)
  have hH0 : ∀ z, 0 ≤ Queue6.Hc X₀ z := fun z => le_trans zero_le_one (hH1 z)
  have hj0 := jzX_nonneg hc
  -- the window
  have hx2 : 2 * (X₀ : ℝ) ≤ x := by
    refine le_trans ?_ hx
    rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add hXp, Real.rpow_one]
    have : (2 : ℝ) ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := by
      rw [Real.rpow_def_of_pos hXp]
      have := Real.add_one_le_exp (Real.log X₀ * 0.01)
      nlinarith
    nlinarith
  have hxX : (X₀ : ℝ) ≤ x := by linarith
  have hHx : Queue6.Hc X₀ x ≤ x / 40 := by
    unfold Queue6.Hc; rw [max_eq_left hxX]
    exact KR.WidthReal.capH_le_tenth hX hxX
  set Y := x + Queue6.Hc X₀ x / 2 with hYdef
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith [hH0 x])
  set HY := Queue6.Hc X₀ Y
  set M := ⌈Y⌉₊ + 1
  set XB := xbBound (PR θ X₀ ω) (Xm X₀) lamH HY Y
  set SB := ∑ v ∈ dyScales (X₀ : ℝ) Y M, Real.log (2 * v) *
    ∑ k ∈ range (⌈2 * Y⌉₊ + 1), blkT (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) k v
  have hC : 0 ≤ CNc (X₀ : ℝ) := by
    unfold CNc
    have : 0 ≤ 4.71 / Real.log X₀ := div_nonneg (by norm_num) (by linarith)
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_trans (by norm_num) (le_max_right _ _)
    positivity
  refine ⟨jzX X₀ * (XB * Real.log Y + 4.3 * CNc (X₀ : ℝ) * SB), ?_⟩
  rintro _ ⟨⟨y, hW⟩, rfl⟩
  simp only
  have hyX : (X₀ : ℝ) ≤ y := by linarith [hW.1]
  have hyY : y ≤ Y := hW.2
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlyY : Real.log y ≤ Real.log Y := Real.log_le_log hy0 hyY
  have hXmy : Xm X₀ ≤ y := (Xm_le_X0 hc).trans hyX
  -- `𝔹`
  have hB := xbB_le_bound (X0 := (X₀ : ℝ)) hP hp2 ht hlam hXmy hyY hH1
    (HY := HY) (fun z hz => KR.WidthReal.Hc_mono hX (hz.trans hyY))
  have hB0 := xbB_nonneg (P := PR θ X₀ ω) (tw := twR θ X₀ ω) (X0m := Xm X₀) (X0 := (X₀ : ℝ))
    (θ' := epsH / 10) (fun z => lt_of_lt_of_le one_pos (hH1 z)) hlam0 y
  -- `S`
  set N := (NKc X₀ y).1
  set K := (NKc X₀ y).2
  have hS : ∑ v ∈ dyScales (X₀ : ℝ) y N, Real.log (2 * v) *
      TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) K v ≤ SB := by
    have hsub : dyScales (X₀ : ℝ) y N ⊆ dyScales (X₀ : ℝ) Y M := by
      intro v hv
      obtain ⟨k, -, rfl, hv⟩ := mem_dyScales.mp hv
      refine mem_dyScales.mpr ⟨k, ?_, rfl, hv.trans hyY⟩
      have hk2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have h4 : (2 : ℝ) ^ k ≤ (X₀ : ℝ) * 2 ^ k / 4 := by
        have := pow_pos (two_pos (α := ℝ)) k; nlinarith
      have hc' := Nat.le_ceil Y
      have : (k : ℝ) < ⌈Y⌉₊ + 1 := by linarith
      exact_mod_cast this
    have hlog2 : ∀ v ∈ dyScales (X₀ : ℝ) Y M, 0 ≤ Real.log (2 * v) := fun v hv => by
      obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact Real.log_nonneg (by nlinarith)
    calc _ ≤ ∑ v ∈ dyScales (X₀ : ℝ) y N, Real.log (2 * v) *
          ∑ k ∈ range (⌈2 * Y⌉₊ + 1), blkT (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) k v := by
          refine Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (hlog2 v (hsub hv))
          obtain ⟨k, -, rfl, hv'⟩ := mem_dyScales.mp hv
          exact sTheta_le hXm2 hH0 (hv'.trans hyY) K
      _ ≤ SB := Finset.sum_le_sum_of_subset_of_nonneg hsub fun v hv _ =>
          mul_nonneg (hlog2 v hv) (Finset.sum_nonneg fun k _ => blkT_nonneg hXm2 hH0 k v)
  have hS0 : 0 ≤ ∑ v ∈ dyScales (X₀ : ℝ) y N, Real.log (2 * v) *
      TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) K v := by
    refine Finset.sum_nonneg fun v hv => mul_nonneg ?_ ?_
    · obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact Real.log_nonneg (by nlinarith)
    · exact KR.TNP.blk_nonneg hP _ (fun k => by
        have h1 := KR.TNP.Pk_ge_one hP.X0m_pos hT.hXm k
        have h2 := Real.log_nonneg h1; linarith) v
  unfold jXat
  set S := ∑ v ∈ dyScales (X₀ : ℝ) y N, Real.log (2 * v) *
      TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) K v
  set B := xbB (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y (X₀ : ℝ) (epsH / 10) lamH
  have e : jzX X₀ * (B + 4.3 * CNc (X₀ : ℝ) * S / Real.log y) * Real.log y =
      jzX X₀ * (B * Real.log y + 4.3 * CNc (X₀ : ℝ) * S) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hj0
  have h1 : B * Real.log y ≤ XB * Real.log Y :=
    mul_le_mul hB hlyY hly.le (hB0.trans hB)
  have h2 : 4.3 * CNc (X₀ : ℝ) * S ≤ 4.3 * CNc (X₀ : ℝ) * SB :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  linarith

end Real

end BModel

end
