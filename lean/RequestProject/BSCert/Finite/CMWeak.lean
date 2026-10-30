module

public import RequestProject.BSCert.Finite.ChebN
public import RequestProject.BSCert.Finite.KArith

/-!
# Lemma 5.1(ii), (iii) for `ℕ` in the form used by the corollary, checked by the kernel

* `mertensS_sub_log_small`: `-1.01 ≤ S(x) - log x ≤ 0.43` for `1 ≤ x ≤ 1000`
  (`S(x) = ∑_{n ≤ x} Λ(n)/n`); for `x ≥ 1000` this follows from Stirling
  (`Lemma51NatFull.lemma_5_1_ii_nat_mid`).
* `sum_log_div_prime_le_weak`: `∑_p log p/(p(p-1)) ≤ 0.75539`: the partial sum up to `10⁵`
  (kernel-checked, in 40 chunks) plus the tail `∑_{p > N} ≤ 1.42/N + 1.42/(N+1)`, by partial
  summation against `θ(x) ≤ ψ(x) ≤ 1.42 x` (`cm3_tail_weak`).

The paper's sharper `-0.753 ≤ S(x) - log x ≤ 0` on `[1, 10⁷]` and `≤ 0.75537` are in
`CMCertSharp` (still `native_decide`, not used by the corollary).
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction Chebyshev FX

/-! ## Line 2, small `x` -/

/-- Lower bound for `2^128 Λ(n)/n`. -/
def mLoK (n : ℕ) : ℤ := if n = 0 then 0 else FX.fdiv (K.vmLoK n) (n : ℤ)
/-- Upper bound for `2^128 Λ(n)/n`. -/
def mHiK (n : ℕ) : ℤ := if n = 0 then 0 else FX.cdiv (K.vmHiK n) (n : ℤ)

/-- The check at `N`: `B - log N ≤ 0.43` and `A - log (N+1) ≥ -1.01`. -/
def mOkK (N : ℕ) (A B : ℤ) : Bool :=
  decide (100 * (B - K.logLoK N) ≤ 43 * ZI) && decide (-101 * ZI ≤ 100 * (A - K.logHiK (N + 1)))

lemma m_checks : K.encLoop mLoK mHiK mOkK 1000 1 0 0 = true := by decide +kernel

lemma m_hg (i : ℕ) : toR (mLoK i) ≤ Λ i / i ∧ Λ i / i ≤ toR (mHiK i) := by
  unfold mLoK mHiK
  split_ifs with h
  · subst h; simp [toR_zero]
  · have hi : 0 < i := Nat.pos_of_ne_zero h
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    exact ⟨(K.toR_fdivN_le _ hi).trans (div_le_div_of_nonneg_right (K.vmLoK_spec i) hi'.le),
      (div_le_div_of_nonneg_right (K.vmHiK_spec i) hi'.le).trans (K.toR_cdivN_ge _ hi)⟩

lemma toR_const (c : ℤ) : toR (c * ZI) = c := by unfold toR; push_cast; field_simp [ZR_pos.ne']

/-- **Lemma 5.1(ii) for `ℕ`, small `x`**: `-1.01 ≤ S(x) - log x ≤ 0.43` for `1 ≤ x ≤ 1000`. -/
theorem mertensS_sub_log_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 1000) :
    -1.01 ≤ mertensS x - Real.log x ∧ mertensS x - Real.log x ≤ 0.43 := by
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN2 : N ≤ 1000 := Nat.floor_le_of_le (by exact_mod_cast hx2)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  obtain ⟨A, B, hA, hB, hok⟩ := K.encLoop_spec mLoK mHiK mOkK (fun i => Λ i / i) m_hg
    1000 1 0 0 m_checks (by simp [toR_zero]) (by simp [toR_zero]) N hN1 (by omega)
  simp only [mOkK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok1, hok2⟩ := hok
  have hS : mertensS x = ∑ i ∈ range (N + 1), Λ i / (i : ℝ) := rfl
  have hlo := K.logLoK_le hN1
  have hhi := K.log_le_logHiK (n := N + 1) (by omega)
  have hlogx1 : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlogx2 : Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by linarith); push_cast; linarith
  have h1 : toR (100 * (B - K.logLoK N)) ≤ toR (43 * ZI) := toR_le_toR.mpr hok1
  have h2 : toR (-101 * ZI) ≤ toR (100 * (A - K.logHiK (N + 1))) := toR_le_toR.mpr hok2
  rw [toR_const] at h1 h2
  have e1 : toR (100 * (B - K.logLoK N)) = 100 * (toR B - toR (K.logLoK N)) := by
    unfold toR; push_cast; ring
  have e2 : toR (100 * (A - K.logHiK (N + 1))) = 100 * (toR A - toR (K.logHiK (N + 1))) := by
    unfold toR; push_cast; ring
  rw [e1] at h1; rw [e2] at h2
  push_cast at h1 h2 hhi hlogx2
  rw [hS]
  constructor <;> linarith

/-! ## Line 6, in the weak form `≤ 0.75539` -/

lemma cm3HiK_spec (n : ℕ) : cm3g n ≤ toR (K.cm3HiK n) := by
  unfold cm3g K.cm3HiK
  split_ifs with hp h1 h2 h3 h4
  · exact absurd hp (by intro h; have := h.two_le; omega)
  · have hn : 2 ≤ n := hp.two_le
    have hd : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    refine le_trans ?_ (K.toR_cdivN_ge _ hd)
    have e : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
    rw [e]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (K.log_le_logHiK (by omega)) (by nlinarith)
  · exfalso
    push_neg at h2
    have hn : 2 ≤ n := hp.two_le
    have := K.lpf_eq_minFac hn h2.1
    rw [hp.minFac_eq] at this
    exact h2.2 this
  · simp [toR_zero]
  · have hn : 2 ≤ n := by omega
    have hd : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    refine le_trans ?_ (K.toR_cdivN_ge _ hd)
    exact div_nonneg (K.logHiK_nonneg (by omega)) (by positivity)
  · simp [toR_zero]

/-- The running sums `∑_{n < 2500 k} cm3HiK n`, `k ≤ 40`, and the sum up to `10⁵` inclusive. -/
def cm3C (k : ℕ) : ℤ := [0, 256902799382747262156446471907675427210, 256970269404493794394410627127662968635, 256992605050115457122494300232795052682, 257004102905635095309854390239540589936, 257010771908837665888982967037234395723, 257015308109557071152943515492014117283, 257018578257288414860922733836878337342, 257020947893582935668020721827170849834, 257022853775717542885705464012823516789, 257024362682689638350411374112851385315, 257025582328501212432976669413334669871, 257026604881301963839628606502573158031, 257027478314924632489012212872480127783, 257028243310322623779864273623442620128, 257028885235102146327537574373533393250, 257029448235725194602124080871001690600, 257029965625297334968173420585540844384, 257030398625868540515051700455772038682, 257030774641102936432116683188510953480, 257031142732975414385009729194877150551, 257031460614495590654113909417948234254, 257031757318895689355197630758233191023, 257032036046918046152334203585078924034, 257032285277713080669089058586932212549, 257032503351392155792526075086567345045, 257032705540776020593530407045624900043, 257032905306867493997290648304441128641, 257033073921092368605212506660096201226, 257033251568293795636575707937785017852, 257033406531904221728887552082053420236, 257033551330848397368010652297000196482, 257033689940496312919003097161706998049, 257033822778034129185593199838815475579, 257033939391415803577660498727826009759, 257034051231907940400322284701794099211, 257034160019692296787734659766972508272, 257034263660371352311759465398307153940, 257034362123439993155570800703734253088, 257034454112674276614131289797654651294, 257034541180296138082802786870951401502, 257034541180296138082802786870951401502].getD k 0

lemma cm3_chunk0 : K.sumUp K.cm3HiK 2500 (2500 * 0) (cm3C 0) = cm3C 1 := by decide +kernel
lemma cm3_chunk1 : K.sumUp K.cm3HiK 2500 (2500 * 1) (cm3C 1) = cm3C 2 := by decide +kernel
lemma cm3_chunk2 : K.sumUp K.cm3HiK 2500 (2500 * 2) (cm3C 2) = cm3C 3 := by decide +kernel
lemma cm3_chunk3 : K.sumUp K.cm3HiK 2500 (2500 * 3) (cm3C 3) = cm3C 4 := by decide +kernel
lemma cm3_chunk4 : K.sumUp K.cm3HiK 2500 (2500 * 4) (cm3C 4) = cm3C 5 := by decide +kernel
lemma cm3_chunk5 : K.sumUp K.cm3HiK 2500 (2500 * 5) (cm3C 5) = cm3C 6 := by decide +kernel
lemma cm3_chunk6 : K.sumUp K.cm3HiK 2500 (2500 * 6) (cm3C 6) = cm3C 7 := by decide +kernel
lemma cm3_chunk7 : K.sumUp K.cm3HiK 2500 (2500 * 7) (cm3C 7) = cm3C 8 := by decide +kernel
lemma cm3_chunk8 : K.sumUp K.cm3HiK 2500 (2500 * 8) (cm3C 8) = cm3C 9 := by decide +kernel
lemma cm3_chunk9 : K.sumUp K.cm3HiK 2500 (2500 * 9) (cm3C 9) = cm3C 10 := by decide +kernel
lemma cm3_chunk10 : K.sumUp K.cm3HiK 2500 (2500 * 10) (cm3C 10) = cm3C 11 := by decide +kernel
lemma cm3_chunk11 : K.sumUp K.cm3HiK 2500 (2500 * 11) (cm3C 11) = cm3C 12 := by decide +kernel
lemma cm3_chunk12 : K.sumUp K.cm3HiK 2500 (2500 * 12) (cm3C 12) = cm3C 13 := by decide +kernel
lemma cm3_chunk13 : K.sumUp K.cm3HiK 2500 (2500 * 13) (cm3C 13) = cm3C 14 := by decide +kernel
lemma cm3_chunk14 : K.sumUp K.cm3HiK 2500 (2500 * 14) (cm3C 14) = cm3C 15 := by decide +kernel
lemma cm3_chunk15 : K.sumUp K.cm3HiK 2500 (2500 * 15) (cm3C 15) = cm3C 16 := by decide +kernel
lemma cm3_chunk16 : K.sumUp K.cm3HiK 2500 (2500 * 16) (cm3C 16) = cm3C 17 := by decide +kernel
lemma cm3_chunk17 : K.sumUp K.cm3HiK 2500 (2500 * 17) (cm3C 17) = cm3C 18 := by decide +kernel
lemma cm3_chunk18 : K.sumUp K.cm3HiK 2500 (2500 * 18) (cm3C 18) = cm3C 19 := by decide +kernel
lemma cm3_chunk19 : K.sumUp K.cm3HiK 2500 (2500 * 19) (cm3C 19) = cm3C 20 := by decide +kernel
lemma cm3_chunk20 : K.sumUp K.cm3HiK 2500 (2500 * 20) (cm3C 20) = cm3C 21 := by decide +kernel
lemma cm3_chunk21 : K.sumUp K.cm3HiK 2500 (2500 * 21) (cm3C 21) = cm3C 22 := by decide +kernel
lemma cm3_chunk22 : K.sumUp K.cm3HiK 2500 (2500 * 22) (cm3C 22) = cm3C 23 := by decide +kernel
lemma cm3_chunk23 : K.sumUp K.cm3HiK 2500 (2500 * 23) (cm3C 23) = cm3C 24 := by decide +kernel
lemma cm3_chunk24 : K.sumUp K.cm3HiK 2500 (2500 * 24) (cm3C 24) = cm3C 25 := by decide +kernel
lemma cm3_chunk25 : K.sumUp K.cm3HiK 2500 (2500 * 25) (cm3C 25) = cm3C 26 := by decide +kernel
lemma cm3_chunk26 : K.sumUp K.cm3HiK 2500 (2500 * 26) (cm3C 26) = cm3C 27 := by decide +kernel
lemma cm3_chunk27 : K.sumUp K.cm3HiK 2500 (2500 * 27) (cm3C 27) = cm3C 28 := by decide +kernel
lemma cm3_chunk28 : K.sumUp K.cm3HiK 2500 (2500 * 28) (cm3C 28) = cm3C 29 := by decide +kernel
lemma cm3_chunk29 : K.sumUp K.cm3HiK 2500 (2500 * 29) (cm3C 29) = cm3C 30 := by decide +kernel
lemma cm3_chunk30 : K.sumUp K.cm3HiK 2500 (2500 * 30) (cm3C 30) = cm3C 31 := by decide +kernel
lemma cm3_chunk31 : K.sumUp K.cm3HiK 2500 (2500 * 31) (cm3C 31) = cm3C 32 := by decide +kernel
lemma cm3_chunk32 : K.sumUp K.cm3HiK 2500 (2500 * 32) (cm3C 32) = cm3C 33 := by decide +kernel
lemma cm3_chunk33 : K.sumUp K.cm3HiK 2500 (2500 * 33) (cm3C 33) = cm3C 34 := by decide +kernel
lemma cm3_chunk34 : K.sumUp K.cm3HiK 2500 (2500 * 34) (cm3C 34) = cm3C 35 := by decide +kernel
lemma cm3_chunk35 : K.sumUp K.cm3HiK 2500 (2500 * 35) (cm3C 35) = cm3C 36 := by decide +kernel
lemma cm3_chunk36 : K.sumUp K.cm3HiK 2500 (2500 * 36) (cm3C 36) = cm3C 37 := by decide +kernel
lemma cm3_chunk37 : K.sumUp K.cm3HiK 2500 (2500 * 37) (cm3C 37) = cm3C 38 := by decide +kernel
lemma cm3_chunk38 : K.sumUp K.cm3HiK 2500 (2500 * 38) (cm3C 38) = cm3C 39 := by decide +kernel
lemma cm3_chunk39 : K.sumUp K.cm3HiK 2500 (2500 * 39) (cm3C 39) = cm3C 40 := by decide +kernel

lemma cm3_last : K.sumUp K.cm3HiK 1 100000 (cm3C 40) = cm3C 41 := by decide +kernel

lemma cm3_final : 100000000 * cm3C 41 + 2840 * ZI ≤ 75539000 * ZI := by decide +kernel

lemma cm3_chunks : ∀ k < 40, K.sumUp K.cm3HiK 2500 (2500 * k) (cm3C k) = cm3C (k + 1) := by
  intro k hk
  interval_cases k
  exacts [cm3_chunk0, cm3_chunk1, cm3_chunk2, cm3_chunk3, cm3_chunk4, cm3_chunk5, cm3_chunk6, cm3_chunk7, cm3_chunk8, cm3_chunk9, cm3_chunk10, cm3_chunk11, cm3_chunk12, cm3_chunk13, cm3_chunk14, cm3_chunk15, cm3_chunk16, cm3_chunk17, cm3_chunk18, cm3_chunk19, cm3_chunk20, cm3_chunk21, cm3_chunk22, cm3_chunk23, cm3_chunk24, cm3_chunk25, cm3_chunk26, cm3_chunk27, cm3_chunk28, cm3_chunk29, cm3_chunk30, cm3_chunk31, cm3_chunk32, cm3_chunk33, cm3_chunk34, cm3_chunk35, cm3_chunk36, cm3_chunk37, cm3_chunk38, cm3_chunk39]

lemma cm3_prefix : ∀ k ≤ 40, K.sumUp K.cm3HiK (2500 * k) 0 0 = cm3C k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [show 2500 * (k + 1) = 2500 * k + 2500 by ring, K.sumUp_add, ih (by omega), zero_add]
    exact cm3_chunks k (by omega)

lemma cm3_partial : ∑ n ∈ range 100001, cm3g n ≤ toR (cm3C 41) := by
  have h := K.sumUp_spec K.cm3HiK cm3g cm3HiK_spec 100001 0 0
  rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at h
  have e : K.sumUp K.cm3HiK 100001 0 0 = cm3C 41 := by
    rw [show 100001 = 2500 * 40 + 1 by norm_num, K.sumUp_add, cm3_prefix 40 le_rfl, zero_add]
    exact cm3_last
  rwa [e] at h

/-! ### The tail by partial summation -/

private lemma abel_upper' (a w B : ℕ → ℝ) (hA : ∀ N ≥ 2, ∑ k ∈ Icc 2 N, a k ≤ B N)
    (hw : ∀ n ≥ 2, w (n + 1) ≤ w n) (hw0 : ∀ n ≥ 2, 0 ≤ w n) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, a k * w k ≤ B 2 * w 2 + ∑ n ∈ Icc 3 N, (B n - B (n - 1)) * w n := by
  have key : ∀ N ≥ 2, ∑ k ∈ Icc 2 N, a k * w k ≤ B 2 * w 2 +
      ∑ n ∈ Icc 3 N, (B n - B (n - 1)) * w n + (∑ k ∈ Icc 2 N, a k - B N) * w N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp; ring_nf; rfl
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 : (∑ k ∈ Icc 2 M, a k - B M) * (w M - w (M + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith [hA M hM]) (by linarith [hw M hM])
      simp only [Nat.add_sub_cancel]
      nlinarith
  have := key N hN
  have h2 : (∑ k ∈ Icc 2 N, a k - B N) * w N ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hA N hN]) (hw0 N hN)
  linarith

lemma theta_partial_le' (N : ℕ) :
    ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) ≤ 1.42 * N := by
  have h1 := psi_le_one_point_four_two (x := (N : ℝ)) (Nat.cast_nonneg _)
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  have e : Chebyshev.theta (N : ℝ) =
      ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro k hk; simp at hk ⊢; omega
    · intro k hk hk'
      simp at hk hk'
      have : ¬ k.Prime := by intro hp; have := hp.two_le; omega
      simp [this]
  linarith

/-- `∑_{N < p ≤ M} log p/(p(p-1)) ≤ 1.42/N + 1.42/(N+1)` for `N ≥ 2`. -/
lemma cm3_tail_weak {N : ℕ} (hN : 2 ≤ N) (M : ℕ) :
    ∑ n ∈ Ioc N M, cm3g n ≤ 1.42 / N + 1.42 / (N + 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 ≤ 1.42 / (N : ℝ) + 1.42 / (N + 1) := by positivity
  rcases le_or_gt M N with hM | hM
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; exact hpos
  set a : ℕ → ℝ := fun k => if N < k ∧ k.Prime then Real.log k else 0 with ha
  set w : ℕ → ℝ := fun k => 1 / ((k : ℝ) * ((k : ℝ) - 1)) with hw
  set B : ℕ → ℝ := fun n => if n ≤ N then 0 else 1.42 * n with hB
  have hA : ∀ n ≥ 2, ∑ k ∈ Icc 2 n, a k ≤ B n := by
    intro n hn
    simp only [hB]
    split_ifs with hnN
    · refine le_of_eq (Finset.sum_eq_zero fun k hk => ?_)
      simp only [ha, Finset.mem_Icc] at hk ⊢
      rw [if_neg (by omega)]
    · refine le_trans (Finset.sum_le_sum fun k hk => ?_) (theta_partial_le' n)
      simp only [ha]
      split_ifs with h1 h2 <;> try exact le_rfl
      · exact absurd h1.2 h2
      · exact Real.log_nonneg (by have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (by omega : 1 ≤ k))
  have hwm : ∀ n ≥ 2, w (n + 1) ≤ w n := by
    intro n hn
    simp only [hw]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply one_div_le_one_div_of_le (by nlinarith)
    push_cast; nlinarith
  have hw0 : ∀ n ≥ 2, 0 ≤ w n := by
    intro n hn
    simp only [hw]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_nonneg zero_le_one; nlinarith
  have habel := abel_upper' a w B hA hwm hw0 (N := M) (by omega)
  -- the left side is the tail
  have hL : ∑ k ∈ Icc 2 M, a k * w k = ∑ n ∈ Ioc N M, cm3g n := by
    rw [← Finset.sum_subset (s₁ := Ioc N M) (s₂ := Icc 2 M)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Ioc] at hk
      simp only [ha, hw, cm3g]
      by_cases hp : k.Prime
      · rw [if_pos ⟨hk.1, hp⟩, if_pos hp]; ring
      · rw [if_neg (fun h => hp h.2), if_neg hp]; ring
    · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
    · intro k hk hk'
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk hk'
      simp only [ha]
      rw [if_neg (by omega)]; ring
  -- the right side
  have hR : ∀ m, N + 1 ≤ m → B 2 * w 2 + ∑ n ∈ Icc 3 m, (B n - B (n - 1)) * w n ≤
      1.42 / N + 1.42 / (N + 1) - 1.42 / m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      have h2 : B 2 = 0 := by simp only [hB]; rw [if_pos hN]
      rw [h2, zero_mul, zero_add, Finset.sum_Icc_succ_top (by omega)]
      have hz : ∑ n ∈ Icc 3 N, (B n - B (n - 1)) * w n = 0 :=
        Finset.sum_eq_zero fun n hn => by
          simp only [Finset.mem_Icc] at hn
          simp only [hB]; rw [if_pos (by omega), if_pos (by omega)]; ring
      rw [hz, zero_add]
      simp only [hB, hw]
      rw [if_neg (by omega), Nat.add_sub_cancel, if_pos le_rfl]
      push_cast
      have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
      have hN1 : (N : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
      have e : (1.42 * ((N : ℝ) + 1) - 0) * (1 / (((N : ℝ) + 1) * ((N : ℝ) + 1 - 1))) =
          1.42 / N := by
        rw [show (N : ℝ) + 1 - 1 = N by ring, sub_zero]; field_simp
      rw [e]; linarith
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : (B (m + 1) - B (m + 1 - 1)) * w (m + 1) = 1.42 / m - 1.42 / (m + 1) := by
        simp only [hB, hw, Nat.add_sub_cancel]
        rw [if_neg (by omega), if_neg (by omega)]
        have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
        push_cast
        have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
        have hm1 : (m : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
        rw [show (m : ℝ) + 1 - 1 = m by ring]
        field_simp
      rw [e]
      push_cast
      linarith
  have h3 := hR M hM
  have hM0 : 0 ≤ 1.42 / (M : ℝ) := by positivity
  rw [← hL]
  exact habel.trans (h3.trans (by linarith))

/-- **`finite_checks.py`, line 6, weak form**: `∑_p log p/(p(p-1)) ≤ 0.75539` (the series
converges). -/
theorem sum_log_div_prime_le_weak :
    Summable (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) ∧
    ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75539 := by
  have hfin0 : ∀ M, ∑ n ∈ range (M + 1), cm3g n ≤ 0.75539 := by
    intro M
    have hP := cm3_partial
    have hF : toR (100000000 * cm3C 41 + 2840 * ZI) ≤ toR (75539000 * ZI) :=
      toR_le_toR.mpr cm3_final
    have e1 : toR (100000000 * cm3C 41 + 2840 * ZI) = 100000000 * toR (cm3C 41) + 2840 := by
      unfold toR; push_cast; field_simp [ZR_pos.ne']
    rw [e1, toR_const] at hF
    have ht := cm3_tail_weak (N := 100000) (by norm_num) M
    rcases le_or_gt M 100000 with hM | hM
    · have : ∑ n ∈ range (M + 1), cm3g n ≤ ∑ n ∈ range 100001, cm3g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun i _ _ => cm3g_nonneg i)
      push_cast at hF
      linarith
    · have hsplit : ∑ n ∈ range (M + 1), cm3g n =
          ∑ n ∈ range 100001, cm3g n + ∑ n ∈ Ioc 100000 M, cm3g n := by
        have hI : Ico 100001 (M + 1) = Ioc 100000 M := by ext; simp; omega
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le 100001) (by omega : 100001 ≤ M + 1),
          hI]
      rw [hsplit]
      push_cast at ht hF
      norm_num at ht
      linarith
  have hnn : 0 ≤ (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p
    have := cm3g_nonneg p
    simpa [cm3g, p.2] using this
  have hfin : ∀ u : Finset Nat.Primes,
      ∑ p ∈ u, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75539 := by
    intro u
    obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ u, (p : ℕ) ≤ M :=
      ⟨u.sup (fun p => (p : ℕ)), fun p hp => Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp⟩
    have e : ∑ p ∈ u, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) =
        ∑ n ∈ u.map ⟨fun p : Nat.Primes => (p : ℕ), Subtype.val_injective⟩, cm3g n := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p _
      simp [cm3g, p.2]
    rw [e]
    refine le_trans ?_ (hfin0 M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hM p hp))
    · intro i _ _; exact cm3g_nonneg i
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

end BSCert.FiniteN
