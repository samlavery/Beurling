module

public import RequestProject.BSCert.Transc

/-!
# Fixed-point enclosures of `log n` and of the von Mangoldt function

Used by the finite computations of Section 5 (`finite_checks.py`).

* Fixed-point numbers are integers `a` standing for `a / 2^KS`.
* `logTab` holds certified enclosures of `log (i / 2^TB)` for `2^TB ≤ i ≤ 2^(TB+1)`, computed
  with the certified `logLoPt` / `logHiPt` of `Transc.lean`.
* `logLoN n`, `logHiN n` enclose `log n` for `n ≥ 1`: write `n = 2^e · x` with `x ∈ [1, 2)`
  and bound `log x` by the two neighbouring table entries. For `n < 2^(TB+1)` the table entry
  is exact (up to the `2^-46` accuracy of `logLoPt`).
* `ppBase n` is the prime `p` if `n = p^k` (`k ≥ 1`), and `0` otherwise, so that
  `Λ n = log (ppBase n)` or `0` (`vonMangoldt_eq_ppBase`).
-/

@[expose] public section

namespace BSCert.FiniteN

open Real

/-- Fixed-point scale: `a : ℤ` stands for `a / 2^KS`. -/
def KS : ℕ := 50

/-- Table resolution: `log (i / 2^TB)` for `2^TB ≤ i ≤ 2^(TB+1)`. -/
def TB : ℕ := 12

/-- A certified fixed-point lower bound for `log q`. -/
def logLoQ (q : ℚ) : ℤ := ⌊logLoPt q * 2 ^ KS⌋

/-- A certified fixed-point upper bound for `log q`. -/
def logHiQ (q : ℚ) : ℤ := ⌈logHiPt q * 2 ^ KS⌉

lemma logLoQ_le {q : ℚ} (hq : 0 < q) : ((logLoQ q : ℤ) : ℝ) ≤ 2 ^ KS * Real.log q := by
  have h1 := logLoPt_le hq
  have h2 : ((logLoQ q : ℤ) : ℚ) ≤ logLoPt q * 2 ^ KS := Int.floor_le _
  have h3 : ((logLoQ q : ℤ) : ℝ) ≤ ((logLoPt q : ℚ) : ℝ) * 2 ^ KS := by exact_mod_cast h2
  have : (0 : ℝ) < 2 ^ KS := by positivity
  nlinarith

lemma le_logHiQ {q : ℚ} (hq : 0 < q) : 2 ^ KS * Real.log q ≤ ((logHiQ q : ℤ) : ℝ) := by
  have h1 := le_logHiPt hq
  have h2 : logHiPt q * 2 ^ KS ≤ ((logHiQ q : ℤ) : ℚ) := Int.le_ceil _
  have h3 : ((logHiPt q : ℚ) : ℝ) * 2 ^ KS ≤ ((logHiQ q : ℤ) : ℝ) := by exact_mod_cast h2
  have : (0 : ℝ) < 2 ^ KS := by positivity
  nlinarith

/-- The table entry for `i`: enclosure of `log ((2^TB + i) / 2^TB)`. -/
def tabEntry (i : ℕ) : ℤ × ℤ :=
  let q : ℚ := ((2 ^ TB + i : ℕ) : ℚ) / ((2 ^ TB : ℕ) : ℚ)
  (logLoQ q, logHiQ q)

/-- The table, `0 ≤ i ≤ 2^TB`. -/
def logTab : Array (ℤ × ℤ) := Array.ofFn (n := 2 ^ TB + 1) fun i => tabEntry i

/-- Table lookup. -/
def tab (i : ℕ) : ℤ × ℤ := logTab.getD i (0, 0)

lemma tab_eq {i : ℕ} (hi : i ≤ 2 ^ TB) : tab i = tabEntry i := by
  unfold tab logTab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [show i < 2 ^ TB + 1 by omega]

lemma tab_spec {i : ℕ} (hi : i ≤ 2 ^ TB) :
    ((tab i).1 : ℝ) ≤ 2 ^ KS * Real.log (((2 ^ TB + i : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ)) ∧
    2 ^ KS * Real.log (((2 ^ TB + i : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ)) ≤ ((tab i).2 : ℝ) := by
  rw [tab_eq hi]
  have hq : (0 : ℚ) < ((2 ^ TB + i : ℕ) : ℚ) / ((2 ^ TB : ℕ) : ℚ) := by positivity
  have e : (((((2 ^ TB + i : ℕ) : ℚ) / ((2 ^ TB : ℕ) : ℚ) : ℚ)) : ℝ) =
      ((2 ^ TB + i : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have := logLoQ_le hq; rw [e] at this; exact this
  · have := le_logHiQ hq; rw [e] at this; exact this

/-- Lower fixed-point bound for `log 2`. -/
def lo2 : ℤ := (tabEntry (2 ^ TB)).1
/-- Upper fixed-point bound for `log 2`. -/
def hi2 : ℤ := (tabEntry (2 ^ TB)).2

lemma log2_spec : (lo2 : ℝ) ≤ 2 ^ KS * Real.log 2 ∧ 2 ^ KS * Real.log 2 ≤ (hi2 : ℝ) := by
  have h := tab_spec (i := 2 ^ TB) le_rfl
  rw [tab_eq le_rfl] at h
  have e : ((2 ^ TB + 2 ^ TB : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ) = 2 := by
    push_cast; field_simp; ring
  rw [e] at h
  exact h

/-- Fixed-point lower bound for `log n` (`n ≥ 1`). -/
def logLoN (n : ℕ) : ℤ :=
  let e := Nat.log2 n
  if e ≤ TB then (tab (n * 2 ^ (TB - e) - 2 ^ TB)).1 + e * lo2
  else (tab (n / 2 ^ (e - TB) - 2 ^ TB)).1 + e * lo2

/-- Fixed-point upper bound for `log n` (`n ≥ 1`). -/
def logHiN (n : ℕ) : ℤ :=
  let e := Nat.log2 n
  if e ≤ TB then (tab (n * 2 ^ (TB - e) - 2 ^ TB)).2 + e * hi2
  else (tab (n / 2 ^ (e - TB) - 2 ^ TB + 1)).2 + e * hi2

lemma log2_bounds {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) := by
  rw [Nat.log2_eq_log_two]
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) n⟩

lemma log_split (n e : ℕ) (hn : 1 ≤ n) :
    Real.log n = Real.log ((n : ℝ) / 2 ^ e) + e * Real.log 2 := by
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div h1.ne' (by positivity), Real.log_pow]
  ring

theorem logLoN_spec {n : ℕ} (hn : 1 ≤ n) : (logLoN n : ℝ) ≤ 2 ^ KS * Real.log n := by
  obtain ⟨hlo, hhi⟩ := log2_bounds hn
  set e := Nat.log2 n with he
  have hl2 := log2_spec.1
  have hlog := log_split n e hn
  have he0 : (0 : ℝ) ≤ e := by positivity
  unfold logLoN
  rw [← he]
  dsimp only
  split_ifs with h
  · -- exact table point
    have hT : 2 ^ TB ≤ n * 2 ^ (TB - e) ∧ n * 2 ^ (TB - e) < 2 ^ (TB + 1) := by
      have h1 : 2 ^ TB = 2 ^ e * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      have h2 : 2 ^ (TB + 1) = 2 ^ (e + 1) * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      constructor
      · rw [h1]; exact Nat.mul_le_mul_right _ hlo
      · rw [h2]; exact Nat.mul_lt_mul_of_pos_right hhi (by positivity)
    have hi : n * 2 ^ (TB - e) - 2 ^ TB ≤ 2 ^ TB := by
      have : 2 ^ (TB + 1) = 2 * 2 ^ TB := by ring
      omega
    have hs := (tab_spec hi).1
    have hq : ((2 ^ TB + (n * 2 ^ (TB - e) - 2 ^ TB) : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ) =
        (n : ℝ) / 2 ^ e := by
      rw [show 2 ^ TB + (n * 2 ^ (TB - e) - 2 ^ TB) = n * 2 ^ (TB - e) by omega]
      have h1 : (2 : ℝ) ^ TB = 2 ^ e * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      push_cast
      rw [h1]
      field_simp
    rw [hq] at hs
    have hm := mul_le_mul_of_nonneg_left hl2 he0
    rw [hlog]
    push_cast
    linarith
  · push_neg at h
    set s := e - TB
    set mm := n / 2 ^ s
    have hs2 : 2 ^ e = 2 ^ TB * 2 ^ s := by rw [← pow_add]; congr 1; omega
    have hm1 : mm * 2 ^ s ≤ n := Nat.div_mul_le_self n _
    have hm2 : 2 ^ TB ≤ mm := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      rw [hs2] at hlo; exact hlo
    have hm3 : mm < 2 ^ (TB + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have : 2 ^ (e + 1) = 2 ^ (TB + 1) * 2 ^ s := by rw [← pow_add]; congr 1; omega
      rw [this] at hhi; exact hhi
    have hi : mm - 2 ^ TB ≤ 2 ^ TB := by
      have : 2 ^ (TB + 1) = 2 * 2 ^ TB := by ring
      omega
    have hsp := (tab_spec hi).1
    rw [show 2 ^ TB + (mm - 2 ^ TB) = mm by omega] at hsp
    have hmm1 : (1 : ℝ) ≤ mm := by exact_mod_cast (le_trans Nat.one_le_two_pow hm2)
    have hmono : Real.log ((mm : ℝ) / ((2 ^ TB : ℕ) : ℝ)) ≤ Real.log ((n : ℝ) / 2 ^ e) := by
      apply Real.log_le_log (by positivity)
      have hc : (mm : ℝ) * 2 ^ s ≤ n := by exact_mod_cast hm1
      have hs2' : (2 : ℝ) ^ e = 2 ^ TB * 2 ^ s := by exact_mod_cast hs2
      rw [hs2', div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 ^ TB)
      calc (mm : ℝ) * (2 ^ TB * 2 ^ s) = 2 ^ TB * (mm * 2 ^ s) := by ring
        _ ≤ 2 ^ TB * n := this
        _ = n * 2 ^ TB := by ring
    have hm := mul_le_mul_of_nonneg_left hl2 he0
    have hm2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 2 ^ KS)
    rw [hlog]
    push_cast
    linarith

theorem logHiN_spec {n : ℕ} (hn : 1 ≤ n) : 2 ^ KS * Real.log n ≤ (logHiN n : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log2_bounds hn
  set e := Nat.log2 n with he
  have hl2 := log2_spec.2
  have hlog := log_split n e hn
  have he0 : (0 : ℝ) ≤ e := by positivity
  unfold logHiN
  rw [← he]
  dsimp only
  split_ifs with h
  · have hT : 2 ^ TB ≤ n * 2 ^ (TB - e) ∧ n * 2 ^ (TB - e) < 2 ^ (TB + 1) := by
      have h1 : 2 ^ TB = 2 ^ e * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      have h2 : 2 ^ (TB + 1) = 2 ^ (e + 1) * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      constructor
      · rw [h1]; exact Nat.mul_le_mul_right _ hlo
      · rw [h2]; exact Nat.mul_lt_mul_of_pos_right hhi (by positivity)
    have hi : n * 2 ^ (TB - e) - 2 ^ TB ≤ 2 ^ TB := by
      have : 2 ^ (TB + 1) = 2 * 2 ^ TB := by ring
      omega
    have hs := (tab_spec hi).2
    have hq : ((2 ^ TB + (n * 2 ^ (TB - e) - 2 ^ TB) : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ) =
        (n : ℝ) / 2 ^ e := by
      rw [show 2 ^ TB + (n * 2 ^ (TB - e) - 2 ^ TB) = n * 2 ^ (TB - e) by omega]
      have h1 : (2 : ℝ) ^ TB = 2 ^ e * 2 ^ (TB - e) := by rw [← pow_add]; congr 1; omega
      push_cast
      rw [h1]
      field_simp
    rw [hq] at hs
    have hm := mul_le_mul_of_nonneg_left hl2 he0
    rw [hlog]
    push_cast
    linarith
  · push_neg at h
    set s := e - TB
    set mm := n / 2 ^ s
    have hs2 : 2 ^ e = 2 ^ TB * 2 ^ s := by rw [← pow_add]; congr 1; omega
    have hm1 : n < (mm + 1) * 2 ^ s := by
      have := Nat.lt_div_mul_add (a := n) (b := 2 ^ s) (by positivity)
      rw [add_mul, one_mul]; exact this
    have hm2 : 2 ^ TB ≤ mm := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      rw [hs2] at hlo; exact hlo
    have hm3 : mm < 2 ^ (TB + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have : 2 ^ (e + 1) = 2 ^ (TB + 1) * 2 ^ s := by rw [← pow_add]; congr 1; omega
      rw [this] at hhi; exact hhi
    have hi : mm - 2 ^ TB + 1 ≤ 2 ^ TB := by
      have : 2 ^ (TB + 1) = 2 * 2 ^ TB := by ring
      omega
    have hsp := (tab_spec hi).2
    rw [show 2 ^ TB + (mm - 2 ^ TB + 1) = mm + 1 by omega] at hsp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hmono : Real.log ((n : ℝ) / 2 ^ e) ≤
        Real.log (((mm + 1 : ℕ) : ℝ) / ((2 ^ TB : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      have hc : (n : ℝ) < (mm + 1) * 2 ^ s := by exact_mod_cast hm1
      have hs2' : (2 : ℝ) ^ e = 2 ^ TB * 2 ^ s := by exact_mod_cast hs2
      rw [hs2', div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      have := mul_le_mul_of_nonneg_left hc.le (by positivity : (0 : ℝ) ≤ 2 ^ TB)
      calc (n : ℝ) * 2 ^ TB = 2 ^ TB * n := by ring
        _ ≤ 2 ^ TB * ((mm + 1) * 2 ^ s) := this
        _ = (mm + 1) * (2 ^ TB * 2 ^ s) := by ring
    have hm := mul_le_mul_of_nonneg_left hl2 he0
    have hm2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 2 ^ KS)
    rw [hlog]
    push_cast
    linarith

/-! ## The von Mangoldt function -/

/-- `ppBase n = p` if `n = p^k` with `p` prime and `k ≥ 1`, and `0` otherwise. -/
def ppBase (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    let p := n.minFac
    if p ^ Nat.log p n = n then p else 0

lemma isPrimePow_iff_ppBase {n : ℕ} : IsPrimePow n ↔ ppBase n ≠ 0 := by
  unfold ppBase
  constructor
  · intro h
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp h
    have h1 : ¬ q ^ k ≤ 1 := by
      have := Nat.one_lt_pow hk.ne' hq.one_lt; omega
    rw [if_neg h1]
    simp only
    rw [Nat.Prime.pow_minFac hq hk.ne', Nat.log_pow hq.one_lt, if_pos rfl]
    exact hq.ne_zero
  · intro h
    dsimp only at h
    split_ifs at h with h1 h2
    · exact absurd rfl h
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      refine (isPrimePow_nat_iff _).mpr ⟨n.minFac, Nat.log n.minFac n, hp, ?_, h2⟩
      rcases Nat.eq_zero_or_pos (Nat.log n.minFac n) with h0 | h0
      · rw [h0, pow_zero] at h2; omega
      · exact h0
    · exact absurd rfl h

lemma ppBase_eq_minFac {n : ℕ} (h : ppBase n ≠ 0) : ppBase n = n.minFac := by
  unfold ppBase at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with h1 h2 <;> first | rfl | exact absurd rfl h

theorem vonMangoldt_eq_ppBase (n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      if ppBase n = 0 then 0 else Real.log (ppBase n) := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  by_cases h : ppBase n = 0
  · rw [if_pos h, if_neg]
    rw [isPrimePow_iff_ppBase]; exact fun h' => h' h
  · rw [if_neg h, if_pos (isPrimePow_iff_ppBase.mpr h), ppBase_eq_minFac h]

lemma ppBase_ge_two {n : ℕ} (h : ppBase n ≠ 0) : 2 ≤ ppBase n := by
  rw [ppBase_eq_minFac h]
  unfold ppBase at h
  dsimp only at h
  split_ifs at h with h1
  · exact absurd rfl h
  · exact (Nat.minFac_prime (by omega)).two_le
  · exact absurd rfl h

/-- Floor division (for a positive divisor). -/
def fdiv (a : ℤ) (n : ℕ) : ℤ := a / (n : ℤ)
/-- Ceiling division (for a positive divisor). -/
def cdiv (a : ℤ) (n : ℕ) : ℤ := -((-a) / (n : ℤ))

lemma fdiv_le {a : ℤ} {n : ℕ} (hn : 0 < n) : ((fdiv a n : ℤ) : ℝ) ≤ (a : ℝ) / n := by
  unfold fdiv
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have := Int.ediv_mul_le a (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne')
  exact_mod_cast this

lemma le_cdiv {a : ℤ} {n : ℕ} (hn : 0 < n) : (a : ℝ) / n ≤ ((cdiv a n : ℤ) : ℝ) := by
  unfold cdiv
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  have := Int.ediv_mul_le (-a) (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne')
  have h2 : (a : ℤ) ≤ -(-a / (n : ℤ)) * n := by linarith
  exact_mod_cast h2

end BSCert.FiniteN
