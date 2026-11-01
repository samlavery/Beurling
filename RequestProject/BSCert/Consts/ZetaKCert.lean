module

public import RequestProject.BSCert.Consts.ZetaKChunks.zH17287
public import RequestProject.BSCert.Consts.ZetaKChunks.zL17286
public import RequestProject.BSCert.Consts.ZetaKChunks.zH197
public import RequestProject.BSCert.Consts.ZetaKChunks.zD197
public import RequestProject.BSCert.Consts.ZetaKChunks.zH18
public import RequestProject.BSCert.Consts.ZetaKChunks.zH1799997
public import RequestProject.BSCert.Consts.ZetaKChunks.zH177
public import RequestProject.BSCert.Consts.ZetaKChunks.zH1955

/-!
# `consts.py`: kernel-checked enclosures of `ζ(s)`, `-ζ'(s)` at the points used

The partial sums (3000 terms) of `ZetaKChunks/*`, assembled (`*_total`), and the resulting
rational enclosures `zUpQ`, `zLoQ`, `zdUpQ` of `ζ(a/b)` and `-ζ'(a/b)` (with the integral tails).
-/

@[expose] public section

namespace BSCert.Consts

open FX BSCert.FiniteN

/-- `2^128` as a rational. -/
def zqZ : ℚ := 340282366920938463463374607431768211456

lemma toR_eq_q (X : ℤ) : toR X = (((X : ℚ) / zqZ : ℚ) : ℝ) := by
  unfold toR ZI zqZ; push_cast; rfl

/-- Upper bound for `ζ(a/b)` from the partial sum `S` of `N` terms. -/
def zUpQ (a b N : ℕ) (S : ℤ) : ℚ :=
  (S : ℚ) / zqZ + (rpowNegHi (a - b) b N : ℚ) / zqZ / (((a : ℚ) - b) / b)

/-- Lower bound for `ζ(a/b)` from the lower partial sum `S` of `N` terms. -/
def zLoQ (a b N : ℕ) (S : ℤ) : ℚ :=
  (S : ℚ) / zqZ + (rpowNegLo (a - b) b (N + 1) : ℚ) / zqZ / (((a : ℚ) - b) / b)

/-- Upper bound for `-ζ'(a/b)` from the partial sum `S` of `N` terms. -/
def zdUpQ (a b N : ℕ) (S : ℤ) : ℚ :=
  (S : ℚ) / zqZ + (rpowNegHi (a - b) b N : ℚ) / zqZ *
    ((K.logHiK N : ℚ) / zqZ / (((a : ℚ) - b) / b) + 1 / (((a : ℚ) - b) / b) ^ 2)

theorem zetaR_le_zUpQ {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hN : 1 ≤ N) {S : ℤ}
    (hS : K.sumUp (zTermHi a b) N 0 0 = S) : zetaR ((a : ℝ) / b) ≤ (zUpQ a b N S : ℝ) := by
  have h := zetaR_le_K hb hab hN hS
  rw [toR_eq_q, toR_eq_q] at h
  unfold zUpQ; push_cast at h ⊢; exact h

theorem zLoQ_le_zetaR {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hN : 1 ≤ N) {S : ℤ}
    (hS : sumDown (zTermLo a b) N 0 0 = S) : (zLoQ a b N S : ℝ) ≤ zetaR ((a : ℝ) / b) := by
  have h := zetaR_ge_K hb hab hN hS
  rw [toR_eq_q, toR_eq_q] at h
  unfold zLoQ; push_cast at h ⊢; exact h

theorem zetaDR_le_zdUpQ {a b N : ℕ} (hb : 0 < b) (hab : b < a) (hs2 : 1 / Real.log 2 ≤ (a : ℝ) / b)
    (hN : 2 ≤ N) {S : ℤ} (hS : K.sumUp (zdTermHi a b) N 0 0 = S) :
    zetaDR ((a : ℝ) / b) ≤ (zdUpQ a b N S : ℝ) := by
  have h := zetaDR_le_K hb hab hs2 hN hS
  rw [toR_eq_q, toR_eq_q, toR_eq_q] at h
  unfold zdUpQ; push_cast at h ⊢; exact h

lemma zH17287_chunks : ∀ i < 6, K.sumUp (zTermHi 17287 10000) 500 (500 * i) (zH17287C i) = zH17287C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH17287_0, zH17287_1, zH17287_2, zH17287_3, zH17287_4, zH17287_5]

lemma zH17287_total : K.sumUp (zTermHi 17287 10000) 3000 0 0 = zH17287C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 17287 10000) (500 * k) 0 0 = zH17287C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH17287_chunks k (by omega)
  exact key 6 le_rfl

lemma zL17286_chunks : ∀ i < 6, sumDown (zTermLo 17286 10000) 500 (500 * i) (zL17286C i) = zL17286C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zL17286_0, zL17286_1, zL17286_2, zL17286_3, zL17286_4, zL17286_5]

lemma zL17286_total : sumDown (zTermLo 17286 10000) 3000 0 0 = zL17286C 6 := by
  have key : ∀ k ≤ 6, sumDown (zTermLo 17286 10000) (500 * k) 0 0 = zL17286C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, sumDown_add, ih (by omega), zero_add]
      exact zL17286_chunks k (by omega)
  exact key 6 le_rfl

lemma zH197_chunks : ∀ i < 6, K.sumUp (zTermHi 197 100) 500 (500 * i) (zH197C i) = zH197C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH197_0, zH197_1, zH197_2, zH197_3, zH197_4, zH197_5]

lemma zH197_total : K.sumUp (zTermHi 197 100) 3000 0 0 = zH197C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 197 100) (500 * k) 0 0 = zH197C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH197_chunks k (by omega)
  exact key 6 le_rfl

lemma zD197_chunks : ∀ i < 6, K.sumUp (zdTermHi 197 100) 500 (500 * i) (zD197C i) = zD197C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zD197_0, zD197_1, zD197_2, zD197_3, zD197_4, zD197_5]

lemma zD197_total : K.sumUp (zdTermHi 197 100) 3000 0 0 = zD197C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zdTermHi 197 100) (500 * k) 0 0 = zD197C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zD197_chunks k (by omega)
  exact key 6 le_rfl

lemma zH18_chunks : ∀ i < 6, K.sumUp (zTermHi 18 10) 500 (500 * i) (zH18C i) = zH18C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH18_0, zH18_1, zH18_2, zH18_3, zH18_4, zH18_5]

lemma zH18_total : K.sumUp (zTermHi 18 10) 3000 0 0 = zH18C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 18 10) (500 * k) 0 0 = zH18C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH18_chunks k (by omega)
  exact key 6 le_rfl

lemma zH1799997_chunks : ∀ i < 6, K.sumUp (zTermHi 1799997 1000000) 500 (500 * i) (zH1799997C i) = zH1799997C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH1799997_0, zH1799997_1, zH1799997_2, zH1799997_3, zH1799997_4, zH1799997_5]

lemma zH1799997_total : K.sumUp (zTermHi 1799997 1000000) 3000 0 0 = zH1799997C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 1799997 1000000) (500 * k) 0 0 = zH1799997C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH1799997_chunks k (by omega)
  exact key 6 le_rfl

lemma zH177_chunks : ∀ i < 6, K.sumUp (zTermHi 177 100) 500 (500 * i) (zH177C i) = zH177C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH177_0, zH177_1, zH177_2, zH177_3, zH177_4, zH177_5]

lemma zH177_total : K.sumUp (zTermHi 177 100) 3000 0 0 = zH177C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 177 100) (500 * k) 0 0 = zH177C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH177_chunks k (by omega)
  exact key 6 le_rfl

lemma zH1955_chunks : ∀ i < 6, K.sumUp (zTermHi 1955 1000) 500 (500 * i) (zH1955C i) = zH1955C (i + 1) := by
  intro i hi
  interval_cases i
  exacts [zH1955_0, zH1955_1, zH1955_2, zH1955_3, zH1955_4, zH1955_5]

lemma zH1955_total : K.sumUp (zTermHi 1955 1000) 3000 0 0 = zH1955C 6 := by
  have key : ∀ k ≤ 6, K.sumUp (zTermHi 1955 1000) (500 * k) 0 0 = zH1955C k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [show 500 * (k + 1) = 500 * k + 500 by ring, K.sumUp_add, ih (by omega), zero_add]
      exact zH1955_chunks k (by omega)
  exact key 6 le_rfl

end BSCert.Consts
