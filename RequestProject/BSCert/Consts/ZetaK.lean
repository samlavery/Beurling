module

public import RequestProject.BSCert.Consts.ZetaSeries
public import RequestProject.BSCert.Finite.KArith

/-!
# Fixed-point enclosures of `ζ(s)` and `-ζ'(s)` for rational `s = a/b > 1` (kernel-checked)

The analogue of `ZetaItv` in the fixed-point arithmetic `BSCert.FX`: the terms `n^{-s}` are
enclosed by `e^{-s log n}` with `FX.logLo`/`FX.logHi` and `FX.expLo`/`FX.expHi`, the partial
sums `∑_{n ≤ N}` are running sums (`K.sumUp`, checked in chunks by the kernel), and the tails
are the integral bounds of `ZetaSeries`.
-/

@[expose] public section

namespace BSCert.Consts

open FX Finset BSCert.FiniteN

/-- `expHi Y`, or `2^128` if it fails. -/
def expHiOr1 (Y : ℤ) : ℤ :=
  match expHi Y with
  | some X => X
  | none => ZI

lemma le_expHiOr1 (Y : ℤ) {z : ℝ} (h1 : z ≤ Real.exp (toR Y)) (h2 : z ≤ 1) :
    z ≤ toR (expHiOr1 Y) := by
  unfold expHiOr1
  split
  · rename_i X hX; exact h1.trans (le_expHi hX)
  · rw [toR_ZI]; exact h2

/-- Upper bound for `2^128 m^{-a/b}` (`m ≥ 1`). -/
def rpowNegHi (a b m : ℕ) : ℤ := expHiOr1 (cdiv (-((a : ℤ) * K.logLoK m)) (b : ℤ))

/-- Lower bound for `2^128 m^{-a/b}` (`m ≥ 1`). -/
def rpowNegLo (a b m : ℕ) : ℤ := expLo (fdiv (-((a : ℤ) * K.logHiK m)) (b : ℤ))

lemma rpow_neg_eq {m : ℕ} (hm : 1 ≤ m) (s : ℝ) :
    (m : ℝ) ^ (-s) = Real.exp (-s * Real.log m) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hm)]; ring_nf

lemma le_rpowNegHi {a b m : ℕ} (hb : 0 < b) (hm : 1 ≤ m) :
    (m : ℝ) ^ (-((a : ℝ) / b)) ≤ toR (rpowNegHi a b m) := by
  have hL := K.logLoK_le hm
  have hY : -((a : ℝ) / b) * Real.log m ≤ toR (cdiv (-((a : ℤ) * K.logLoK m)) (b : ℤ)) := by
    have h1 := le_toR_cdivN (-((a : ℤ) * K.logLoK m)) hb
    have e : toR (-((a : ℤ) * K.logLoK m)) / b = -((a : ℝ) / b) * toR (K.logLoK m) := by
      unfold toR; push_cast; ring
    rw [e] at h1
    have ha : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
    nlinarith
  have hle1 : (m : ℝ) ^ (-((a : ℝ) / b)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm)
      (by have : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
          linarith)
  refine le_expHiOr1 _ ?_ hle1
  rw [rpow_neg_eq hm]
  exact Real.exp_le_exp.mpr hY

lemma rpowNegLo_le {a b m : ℕ} (hb : 0 < b) (hm : 1 ≤ m) :
    toR (rpowNegLo a b m) ≤ (m : ℝ) ^ (-((a : ℝ) / b)) := by
  have hL := K.log_le_logHiK hm
  have hY : toR (fdiv (-((a : ℤ) * K.logHiK m)) (b : ℤ)) ≤ -((a : ℝ) / b) * Real.log m := by
    have h1 := toR_fdivN (-((a : ℤ) * K.logHiK m)) hb
    have e : toR (-((a : ℤ) * K.logHiK m)) / b = -((a : ℝ) / b) * toR (K.logHiK m) := by
      unfold toR; push_cast; ring
    rw [e] at h1
    have ha : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
    nlinarith
  rw [rpow_neg_eq hm]
  exact (expLo_le _).trans (Real.exp_le_exp.mpr hY)

/-- The term `(k+1)^{-a/b}`, upper bound. -/
def zTermHi (a b : ℕ) (k : ℕ) : ℤ := rpowNegHi a b (k + 1)
/-- The term `(k+1)^{-a/b}`, lower bound. -/
def zTermLo (a b : ℕ) (k : ℕ) : ℤ := rpowNegLo a b (k + 1)
/-- The term `log (k+1) · (k+1)^{-a/b}`, upper bound. -/
def zdTermHi (a b : ℕ) (k : ℕ) : ℤ := cl (K.logHiK (k + 1) * rpowNegHi a b (k + 1))

lemma zTermHi_spec {a b : ℕ} (hb : 0 < b) (k : ℕ) :
    ((k : ℝ) + 1) ^ (-((a : ℝ) / b)) ≤ toR (zTermHi a b k) := by
  have := le_rpowNegHi (a := a) hb (m := k + 1) (by omega)
  push_cast at this; exact this

lemma zTermLo_spec {a b : ℕ} (hb : 0 < b) (k : ℕ) :
    toR (zTermLo a b k) ≤ ((k : ℝ) + 1) ^ (-((a : ℝ) / b)) := by
  have := rpowNegLo_le (a := a) hb (m := k + 1) (by omega)
  push_cast at this; exact this

lemma zdTermHi_spec {a b : ℕ} (hb : 0 < b) (k : ℕ) :
    Real.log ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ (-((a : ℝ) / b)) ≤ toR (zdTermHi a b k) := by
  have h1 := K.log_le_logHiK (n := k + 1) (by omega)
  have h2 := zTermHi_spec (a := a) hb k
  push_cast at h1
  have hl : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
  have hp : 0 ≤ ((k : ℝ) + 1) ^ (-((a : ℝ) / b)) := Real.rpow_nonneg (by positivity) _
  exact (mul_le_mul h1 h2 hp (hl.trans h1)).trans le_cl_mul

/-- Running lower sums. -/
def sumDown (h : ℕ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, _, A => A
  | f + 1, n, A => forceI (A + h n) (sumDown h f (n + 1))

lemma sumDown_spec (h : ℕ → ℤ) (g : ℕ → ℝ) (hg : ∀ i, toR (h i) ≤ g i) :
    ∀ f n A, toR (sumDown h f n A) ≤ toR A + ∑ i ∈ Ico n (n + f), g i := by
  intro f
  induction f with
  | zero => intro n A; simp [sumDown]
  | succ f ih =>
    intro n A
    simp only [sumDown, forceI_eq]
    refine (ih (n + 1) (A + h n)).trans ?_
    rw [Finset.sum_eq_sum_Ico_succ_bot (show n < n + (f + 1) by omega), toR_add,
      show n + (f + 1) = n + 1 + f by omega]
    linarith [hg n]

lemma sumDown_add (h : ℕ → ℤ) : ∀ a b n A, sumDown h (a + b) n A = sumDown h b (n + a) (sumDown h a n A) := by
  intro a
  induction a with
  | zero => intro b n A; simp [sumDown]
  | succ a ih =>
    intro b n A
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [sumDown, forceI_eq]
    rw [ih, show n + 1 + a = n + (a + 1) by omega]

/-- `ζ(a/b) ≤ toR S + N^{1-a/b}/(a/b - 1)` from the partial sum `S`. -/
theorem zetaR_le_K {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hN : 1 ≤ N) {S : ℤ}
    (hS : K.sumUp (zTermHi a b) N 0 0 = S) :
    zetaR ((a : ℝ) / b) ≤ toR S + toR (rpowNegHi (a - b) b N) / (((a : ℝ) - b) / b) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : (1 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hb', one_mul]; exact_mod_cast hab
  have hsum := K.sumUp_spec (zTermHi a b) _ (zTermHi_spec (a := a) hb) N 0 0
  rw [hS, toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hsum
  have htail := zetaR_tail_le hs hN
  have hT := le_rpowNegHi (a := a - b) hb hN
  have e1 : ((a - b : ℕ) : ℝ) / b = (a : ℝ) / b - 1 := by
    rw [Nat.cast_sub hab.le]; field_simp
  rw [e1, show -((a : ℝ) / b - 1) = 1 - (a : ℝ) / b by ring] at hT
  have hs1 : (0 : ℝ) < (a : ℝ) / b - 1 := by linarith
  have e2 : ((a : ℝ) - b) / b = (a : ℝ) / b - 1 := by field_simp
  rw [e2, zetaR_split hs N]
  have : (N : ℝ) ^ (1 - (a : ℝ) / b) / ((a : ℝ) / b - 1) ≤
      toR (rpowNegHi (a - b) b N) / ((a : ℝ) / b - 1) := div_le_div_of_nonneg_right hT hs1.le
  linarith

/-- `toR S + (N+1)^{1-a/b}/(a/b - 1) ≤ ζ(a/b)` from the lower partial sum `S`. -/
theorem zetaR_ge_K {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hN : 1 ≤ N) {S : ℤ}
    (hS : sumDown (zTermLo a b) N 0 0 = S) :
    toR S + toR (rpowNegLo (a - b) b (N + 1)) / (((a : ℝ) - b) / b) ≤ zetaR ((a : ℝ) / b) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : (1 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hb', one_mul]; exact_mod_cast hab
  have hsum := sumDown_spec (zTermLo a b) _ (zTermLo_spec (a := a) hb) N 0 0
  rw [hS, toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hsum
  have htail := zetaR_tail_ge hs hN
  have hT := rpowNegLo_le (a := a - b) hb (m := N + 1) (by omega)
  have e1 : ((a - b : ℕ) : ℝ) / b = (a : ℝ) / b - 1 := by
    rw [Nat.cast_sub hab.le]; field_simp
  rw [e1, show -((a : ℝ) / b - 1) = 1 - (a : ℝ) / b by ring] at hT
  push_cast at hT
  have hs1 : (0 : ℝ) < (a : ℝ) / b - 1 := by linarith
  have e2 : ((a : ℝ) - b) / b = (a : ℝ) / b - 1 := by field_simp
  rw [e2, zetaR_split hs N]
  have : toR (rpowNegLo (a - b) b (N + 1)) / ((a : ℝ) / b - 1) ≤
      ((N : ℝ) + 1) ^ (1 - (a : ℝ) / b) / ((a : ℝ) / b - 1) := div_le_div_of_nonneg_right hT hs1.le
  linarith

/-- `-ζ'(a/b) ≤ toR S + N^{1-a/b} (log N/(a/b-1) + 1/(a/b-1)²)` from the partial sum `S`. -/
theorem zetaDR_le_K {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hs2 : 1 / Real.log 2 ≤ (a : ℝ) / b)
    (hN : 2 ≤ N) {S : ℤ} (hS : K.sumUp (zdTermHi a b) N 0 0 = S) :
    zetaDR ((a : ℝ) / b) ≤ toR S + toR (rpowNegHi (a - b) b N) *
      (toR (K.logHiK N) / (((a : ℝ) - b) / b) + 1 / (((a : ℝ) - b) / b) ^ 2) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : (1 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hb', one_mul]; exact_mod_cast hab
  have hsum := K.sumUp_spec (zdTermHi a b) _ (zdTermHi_spec (a := a) hb) N 0 0
  rw [hS, toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hsum
  have htail := zetaDR_tail_le hs hs2 hN
  have hT := le_rpowNegHi (a := a - b) hb (m := N) (by omega)
  have e1 : ((a - b : ℕ) : ℝ) / b = (a : ℝ) / b - 1 := by
    rw [Nat.cast_sub hab.le]; field_simp
  rw [e1, show -((a : ℝ) / b - 1) = 1 - (a : ℝ) / b by ring] at hT
  have hs1 : (0 : ℝ) < (a : ℝ) / b - 1 := by linarith
  have e2 : ((a : ℝ) - b) / b = (a : ℝ) / b - 1 := by field_simp
  rw [e2, zetaDR_split hs N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN := K.log_le_logHiK (n := N) (by omega)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hpow0 : 0 ≤ (N : ℝ) ^ (1 - (a : ℝ) / b) := Real.rpow_nonneg hN0.le _
  have hfac : Real.log N / ((a : ℝ) / b - 1) + 1 / ((a : ℝ) / b - 1) ^ 2
      ≤ toR (K.logHiK N) / ((a : ℝ) / b - 1) + 1 / ((a : ℝ) / b - 1) ^ 2 := by
    gcongr
  have hfac0 : 0 ≤ Real.log N / ((a : ℝ) / b - 1) + 1 / ((a : ℝ) / b - 1) ^ 2 := by positivity
  have : zetaDF ((a : ℝ) / b) N ≤ toR (rpowNegHi (a - b) b N) *
      (toR (K.logHiK N) / ((a : ℝ) / b - 1) + 1 / ((a : ℝ) / b - 1) ^ 2) := by
    unfold zetaDF
    exact mul_le_mul hT hfac hfac0 (le_trans hpow0 hT)
  linarith

end BSCert.Consts
