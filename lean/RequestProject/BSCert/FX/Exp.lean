module

public import RequestProject.BSCert.FX.Core

/-!
# Fixed-point enclosures of `exp`

For `x = X / 2^128 ≥ 0`: halve, `y = X / 2^k ≤ 1/32`; sum the first 18 Taylor terms of
`exp y` with every term rounded down (resp. up); square `k` times with outward rounding.
The rounded-down partial sum is a lower bound because all terms are non-negative
(`Real.sum_le_exp_of_nonneg`); the rounded-up one plus one unit bounds the remainder
(`Real.exp_bound'`). For `x < 0`, `exp x = 1 / exp (-x)`; for `x ≤ -90`, `[0, 2^-128]`.

The halving count `k` is chosen from the bit length `blen` of `X`; its choice only affects
sharpness (the bound `y ≤ 1/32` is checked).
-/

@[expose] public section

namespace BSCert.FX

open Finset

/-- Bit length by binary search over the shifts in the list. -/
def blenAux : List ℕ → ℕ → ℕ → ℕ
  | [], n, acc => acc + n
  | s :: ss, n, acc =>
    let m := n >>> s
    if m = 0 then blenAux ss n acc else blenAux ss m (acc + s)

/-- The bit length of `n` (for `n < 2^2048`; only used to choose scales). -/
def blen (n : ℕ) : ℕ := blenAux [1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1] n 0

/-! ## Rounded Taylor sums -/

/-- `s + ∑_{j=m}^{m+n-1} t_j` with `t_{j+1} = ⌊t_j y / ((j+1) 2^128)⌋`. -/
def serLo (y : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, _, s => s
  | n + 1, m, t, s =>
    forceI (s + t) fun s' => forceI (fdiv (t * y) (((m + 1 : ℕ) : ℤ) * ZI)) fun t' =>
      serLo y n (m + 1) t' s'

/-- As `serLo`, with every term rounded up. -/
def serHi (y : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, _, s => s
  | n + 1, m, t, s =>
    forceI (s + t) fun s' => forceI (cdiv (t * y) (((m + 1 : ℕ) : ℤ) * ZI)) fun t' =>
      serHi y n (m + 1) t' s'

lemma toR_fdiv_le (a : ℤ) {d : ℕ} (hd : 0 < d) :
    toR (fdiv a ((d : ℤ) * ZI)) ≤ (a : ℝ) / ((d : ℝ) * ZI * ZI) := by
  have hd' : (0 : ℤ) < (d : ℤ) * ZI := mul_pos (by exact_mod_cast hd) ZI_pos
  have := fdiv_le (a := a) hd'
  unfold toR
  rw [show (a : ℝ) / ((d : ℝ) * ZI * ZI) = (a : ℝ) / (((d : ℤ) * ZI : ℤ) : ℝ) / ZI by
    push_cast; rw [div_div]]
  exact div_le_div_of_nonneg_right this ZR_pos.le

lemma le_toR_cdiv (a : ℤ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / ((d : ℝ) * ZI * ZI) ≤ toR (cdiv a ((d : ℤ) * ZI)) := by
  have hd' : (0 : ℤ) < (d : ℤ) * ZI := mul_pos (by exact_mod_cast hd) ZI_pos
  have := le_cdiv (a := a) hd'
  unfold toR
  rw [show (a : ℝ) / ((d : ℝ) * ZI * ZI) = (a : ℝ) / (((d : ℤ) * ZI : ℤ) : ℝ) / ZI by
    push_cast; rw [div_div]]
  exact div_le_div_of_nonneg_right this ZR_pos.le

/-- The term recursion `T^m/m! · T/(m+1) = T^(m+1)/(m+1)!`. -/
lemma term_succ (T : ℝ) (m : ℕ) :
    T ^ m / (m.factorial : ℝ) * T / ((m + 1 : ℕ) : ℝ) = T ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rw [Nat.factorial_succ]; push_cast; field_simp; ring

lemma serLo_spec {y : ℤ} (hy : 0 ≤ y) : ∀ n m t s, 0 ≤ t → 0 ≤ s →
    toR t ≤ toR y ^ m / (m.factorial : ℝ) →
    0 ≤ serLo y n m t s ∧
      toR (serLo y n m t s) ≤ toR s + ∑ j ∈ Ico m (m + n), toR y ^ j / (j.factorial : ℝ) := by
  intro n
  induction n with
  | zero => intro m t s _ hs _; simp [serLo, hs]
  | succ n ih =>
    intro m t s ht hs htT
    simp only [serLo, forceI_eq]
    have hT : 0 ≤ toR y := toR_nonneg.mpr hy
    have ht' : 0 ≤ fdiv (t * y) (((m + 1 : ℕ) : ℤ) * ZI) :=
      fdiv_nonneg (mul_nonneg ht hy) (mul_pos (by positivity) ZI_pos)
    have htT' : toR (fdiv (t * y) (((m + 1 : ℕ) : ℤ) * ZI)) ≤
        toR y ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      refine (toR_fdiv_le _ (by omega)).trans ?_
      rw [← term_succ]
      have e : ((t * y : ℤ) : ℝ) / (((m + 1 : ℕ) : ℝ) * ZI * ZI) =
          toR t * toR y / ((m + 1 : ℕ) : ℝ) := by
        unfold toR; push_cast; field_simp
      rw [e]
      gcongr
    obtain ⟨h1, h2⟩ := ih (m + 1) _ (s + t) ht' (by linarith) htT'
    refine ⟨h1, h2.trans ?_⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot (show m < m + (n + 1) by omega), toR_add,
      show m + (n + 1) = m + 1 + n by omega]
    linarith

lemma serHi_spec {y : ℤ} (hy : 0 ≤ y) : ∀ n m t s, toR y ^ m / (m.factorial : ℝ) ≤ toR t →
    toR s + ∑ j ∈ Ico m (m + n), toR y ^ j / (j.factorial : ℝ) ≤ toR (serHi y n m t s) := by
  intro n
  induction n with
  | zero => intro m t s _; simp [serHi]
  | succ n ih =>
    intro m t s htT
    simp only [serHi, forceI_eq]
    have hT : 0 ≤ toR y := toR_nonneg.mpr hy
    have htT' : toR y ^ (m + 1) / ((m + 1).factorial : ℝ) ≤
        toR (cdiv (t * y) (((m + 1 : ℕ) : ℤ) * ZI)) := by
      refine le_trans ?_ (le_toR_cdiv _ (by omega))
      rw [← term_succ]
      have e : ((t * y : ℤ) : ℝ) / (((m + 1 : ℕ) : ℝ) * ZI * ZI) =
          toR t * toR y / ((m + 1 : ℕ) : ℝ) := by
        unfold toR; push_cast; field_simp
      rw [e]
      gcongr
    have h2 := ih (m + 1) _ (s + t) htT'
    refine le_trans ?_ h2
    rw [Finset.sum_eq_sum_Ico_succ_bot (show m < m + (n + 1) by omega), toR_add,
      show m + (n + 1) = m + 1 + n by omega]
    linarith

/-! ## Squarings -/

/-- `k` squarings, rounded down (of a non-negative number). -/
def sqLo : ℕ → ℤ → ℤ
  | 0, a => a
  | k + 1, a => forceI (fl (a * a)) (sqLo k)

/-- `k` squarings, rounded up. -/
def sqHi : ℕ → ℤ → ℤ
  | 0, a => a
  | k + 1, a => forceI (cl (a * a)) (sqHi k)

lemma sqLo_spec : ∀ (k : ℕ) (a : ℤ) (E : ℝ), 0 ≤ a → toR a ≤ Real.exp E →
    toR (sqLo k a) ≤ Real.exp (E * 2 ^ k) := by
  intro k
  induction k with
  | zero => intro a E _ h; simpa [sqLo] using h
  | succ k ih =>
    intro a E ha h
    simp only [sqLo, forceI_eq]
    have ha' : 0 ≤ toR a := toR_nonneg.mpr ha
    have h2 : toR (fl (a * a)) ≤ Real.exp (E * 2) := by
      refine fl_mul_le.trans ?_
      rw [show E * 2 = E + E by ring, Real.exp_add]
      exact mul_le_mul h h ha' (Real.exp_pos _).le
    have := ih _ (E * 2) (fdiv_nonneg (mul_self_nonneg a) ZI_pos) h2
    rwa [show E * 2 * 2 ^ k = E * 2 ^ (k + 1) by ring] at this

lemma sqHi_spec : ∀ (k : ℕ) (a : ℤ) (E : ℝ), Real.exp E ≤ toR a →
    Real.exp (E * 2 ^ k) ≤ toR (sqHi k a) := by
  intro k
  induction k with
  | zero => intro a E h; simpa [sqHi] using h
  | succ k ih =>
    intro a E h
    simp only [sqHi, forceI_eq]
    have h2 : Real.exp (E * 2) ≤ toR (cl (a * a)) := by
      refine le_trans ?_ le_cl_mul
      rw [show E * 2 = E + E by ring, Real.exp_add]
      exact mul_le_mul h h (Real.exp_pos _).le ((Real.exp_pos _).le.trans h)
    have := ih _ (E * 2) h2
    rwa [show E * 2 * 2 ^ k = E * 2 ^ (k + 1) by ring] at this

/-! ## `exp` of a non-negative fixed-point number -/

/-- The number of halvings for `X`: `X / 2^k ≤ 2^123` (if `blen` is right). -/
def expK (X : ℤ) : ℕ := blen X.toNat + 5 - 128

/-- Lower bound for `2^128 exp (X / 2^128)`, `X ≥ 0`. -/
def expPosLo (X : ℤ) : ℤ :=
  let k := expK X
  sqLo k (serLo (X / ((2 ^ k : ℕ) : ℤ)) 18 0 ZI 0)

/-- Upper bound for `2^128 exp (X / 2^128)`, `X ≥ 0` (`none` if the reduced argument is not
`≤ 1/32`). -/
def expPosHi (X : ℤ) : Option ℤ :=
  let k := expK X
  let y := cdiv X ((2 ^ k : ℕ) : ℤ)
  if 32 * y ≤ ZI then some (sqHi k (serHi y 18 0 ZI 0 + 1)) else none

lemma toR_div_pow_le {X : ℤ} (k : ℕ) :
    toR (X / ((2 ^ k : ℕ) : ℤ)) * 2 ^ k ≤ toR X := by
  have hd : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have h := fdiv_le (a := X) hd
  unfold fdiv at h
  unfold toR
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  push_cast at h
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ZR_pos]
  rwa [le_div_iff₀ h2k] at h

lemma le_toR_cdiv_pow {X : ℤ} (k : ℕ) :
    toR X ≤ toR (cdiv X ((2 ^ k : ℕ) : ℤ)) * 2 ^ k := by
  have hd : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have h := le_cdiv (a := X) hd
  unfold toR
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  push_cast at h
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ZR_pos]
  rwa [div_le_iff₀ h2k] at h

lemma expPosLo_le {X : ℤ} (hX : 0 ≤ X) : toR (expPosLo X) ≤ Real.exp (toR X) := by
  unfold expPosLo
  set k := expK X
  set y := X / ((2 ^ k : ℕ) : ℤ)
  have hy : 0 ≤ y := Int.ediv_nonneg hX (by positivity)
  obtain ⟨h0, h1⟩ := serLo_spec hy 18 0 ZI 0 ZI_pos.le le_rfl (by rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, toR_ZI])
  have hS : toR (serLo y 18 0 ZI 0) ≤ Real.exp (toR y) := by
    refine h1.trans ?_
    rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico]
    exact Real.sum_le_exp_of_nonneg (toR_nonneg.mpr hy) 18
  refine (sqLo_spec k _ _ h0 hS).trans (Real.exp_le_exp.mpr ?_)
  exact toR_div_pow_le k

/-- The Taylor remainder after 18 terms at `|y| ≤ 1/32` is below `2^-128`. -/
lemma rem18 {T : ℝ} (h0 : 0 ≤ T) (h1 : T ≤ 1 / 32) :
    T ^ 18 * (18 + 1) / ((Nat.factorial 18 : ℕ) * 18) ≤ 1 / (ZI : ℝ) := by
  have : T ^ 18 ≤ (1 / 32) ^ 18 := pow_le_pow_left₀ h0 h1 18
  have hf : ((Nat.factorial 18 : ℕ) : ℝ) = 6402373705728000 := by
    norm_num [Nat.factorial]
  rw [hf, ZI]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

lemma le_expPosHi {X : ℤ} (hX : 0 ≤ X) {h : ℤ} (hh : expPosHi X = some h) :
    Real.exp (toR X) ≤ toR h := by
  unfold expPosHi at hh
  simp only at hh
  split_ifs at hh with hy32
  simp only [Option.some.injEq] at hh
  subst hh
  set k := expK X
  set y := cdiv X ((2 ^ k : ℕ) : ℤ)
  have hyR : toR X ≤ toR y * 2 ^ k := le_toR_cdiv_pow k
  have hy : 0 ≤ y := by
    have : 0 ≤ toR y * 2 ^ k := (toR_nonneg.mpr hX).trans hyR
    exact toR_nonneg.mp (nonneg_of_mul_nonneg_left this (by positivity))
  have hT0 : 0 ≤ toR y := toR_nonneg.mpr hy
  have hT1 : toR y ≤ 1 / 32 := by
    have : toR (32 * y) ≤ toR ZI := toR_le_toR.mpr hy32
    rw [toR_ZI] at this
    unfold toR at this ⊢
    push_cast at this
    rw [mul_div_assoc] at this
    linarith
  have hS := serHi_spec hy 18 0 ZI 0 (by rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, toR_ZI])
  rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hS
  have hb := Real.exp_bound' hT0 (by linarith) (n := 18) (by norm_num)
  have hr := rem18 hT0 hT1
  have hE : Real.exp (toR y) ≤ toR (serHi y 18 0 ZI 0 + 1) := by
    rw [toR_add]
    have : toR 1 = 1 / (ZI : ℝ) := by simp [toR]
    rw [this]
    push_cast at hb hr ⊢
    linarith
  exact (Real.exp_le_exp.mpr hyR).trans (sqHi_spec k _ _ hE)

lemma sqLo_nonneg : ∀ (k : ℕ) (a : ℤ), 0 ≤ a → 0 ≤ sqLo k a := by
  intro k
  induction k with
  | zero => intro a h; simpa [sqLo] using h
  | succ k ih =>
    intro a _
    simp only [sqLo, forceI_eq]
    exact ih _ (fdiv_nonneg (mul_self_nonneg a) ZI_pos)

lemma expPosLo_nonneg {X : ℤ} (hX : 0 ≤ X) : 0 ≤ expPosLo X := by
  unfold expPosLo
  have hy : 0 ≤ X / ((2 ^ expK X : ℕ) : ℤ) := Int.ediv_nonneg hX (by positivity)
  exact sqLo_nonneg _ _ (serLo_spec hy 18 0 ZI 0 ZI_pos.le le_rfl
    (by rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, toR_ZI])).1

/-! ## `exp` of any fixed-point number -/

/-- `2^128 ≤ e^90`. -/
lemma two_pow_le_exp90 : (ZI : ℝ) ≤ Real.exp 90 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 90 = Real.exp 1 ^ 90 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e, ZI]
  push_cast
  calc (340282366920938463463374607431768211456 : ℝ) ≤ 2.7182818283 ^ 90 := by norm_num
    _ ≤ Real.exp 1 ^ 90 := by gcongr

/-- Lower bound for `2^128 exp (X / 2^128)`. -/
def expLo (X : ℤ) : ℤ :=
  if 0 ≤ X then expPosLo X
  else if X ≤ -90 * ZI then 0
  else match expPosHi (-X) with
    | some h => if 0 < h then fdiv (ZI * ZI) h else 0
    | none => 0

/-- Upper bound for `2^128 exp (X / 2^128)`. -/
def expHi (X : ℤ) : Option ℤ :=
  if 0 ≤ X then expPosHi X
  else if X ≤ -90 * ZI then some 1
  else if 0 < expPosLo (-X) then some (cdiv (ZI * ZI) (expPosLo (-X))) else none

/-- `toR (⌊2^256 / h⌋) ≤ 1 / toR h` for `h > 0`. -/
lemma toR_fdiv_sq_le {h : ℤ} (hh : 0 < h) : toR (fdiv (ZI * ZI) h) ≤ 1 / toR h := by
  have := fdiv_le (a := ZI * ZI) hh
  have e : (1 : ℝ) / toR h = ((ZI * ZI : ℤ) : ℝ) / (h : ℝ) / ZI := by
    unfold toR; push_cast; field_simp
  rw [e]
  exact div_le_div_of_nonneg_right this ZR_pos.le

lemma le_toR_cdiv_sq {h : ℤ} (hh : 0 < h) : 1 / toR h ≤ toR (cdiv (ZI * ZI) h) := by
  have := le_cdiv (a := ZI * ZI) hh
  have e : (1 : ℝ) / toR h = ((ZI * ZI : ℤ) : ℝ) / (h : ℝ) / ZI := by
    unfold toR; push_cast; field_simp
  rw [e]
  exact div_le_div_of_nonneg_right this ZR_pos.le

lemma expLo_le (X : ℤ) : toR (expLo X) ≤ Real.exp (toR X) := by
  unfold expLo
  have hz : toR 0 ≤ Real.exp (toR X) := by rw [toR_zero]; exact (Real.exp_pos _).le
  split_ifs with h1 h2
  · exact expPosLo_le h1
  · exact hz
  · split
    · rename_i h hh
      split_ifs with h3
      · have hE := le_expPosHi (by omega) hh
        rw [toR_neg] at hE
        refine (toR_fdiv_sq_le h3).trans ?_
        rw [Real.exp_neg] at hE
        have hp : 0 < Real.exp (toR X) := Real.exp_pos _
        have hpos : 0 < toR h := toR_pos.mpr h3
        rw [div_le_iff₀ hpos]
        have := mul_le_mul_of_nonneg_left hE hp.le
        rwa [mul_inv_cancel₀ hp.ne'] at this
      · exact hz
    · exact hz

lemma le_expHi {X : ℤ} {h : ℤ} (hh : expHi X = some h) : Real.exp (toR X) ≤ toR h := by
  unfold expHi at hh
  split_ifs at hh with h1 h2 h3
  · exact le_expPosHi h1 hh
  · simp only [Option.some.injEq] at hh
    subst hh
    have hX : toR X ≤ -90 := by
      have := toR_le_toR.mpr h2
      unfold toR at this ⊢
      push_cast at this
      rwa [mul_div_assoc, div_self ZR_pos.ne', mul_one] at this
    have : toR 1 = 1 / (ZI : ℝ) := by simp [toR]
    rw [this]
    refine (Real.exp_le_exp.mpr hX).trans ?_
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le ZR_pos two_pow_le_exp90
  · simp only [Option.some.injEq] at hh
    subst hh
    have hL := expPosLo_le (X := -X) (by omega)
    rw [toR_neg] at hL
    refine le_trans ?_ (le_toR_cdiv_sq h3)
    have hpos : 0 < toR (expPosLo (-X)) := toR_pos.mpr h3
    rw [le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hL (Real.exp_pos (toR X)).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this

namespace FI

/-- Interval `exp`. -/
def exp (a : FI) : Option FI :=
  match expHi a.hi with
  | some h => some ⟨expLo a.lo, h⟩
  | none => none

lemma mem_exp {x : ℝ} {a I : FI} (hx : Mem x a) (h : exp a = some I) : Mem (Real.exp x) I := by
  unfold exp at h
  split at h
  · rename_i hh hhe
    cases h
    exact ⟨(expLo_le _).trans (Real.exp_le_exp.mpr hx.1),
      (Real.exp_le_exp.mpr hx.2).trans (le_expHi hhe)⟩
  · cases h

end FI

end BSCert.FX
