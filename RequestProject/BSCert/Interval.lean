module

public import Mathlib

/-!
# Verified rational interval arithmetic

A small interval arithmetic over `ℚ` with outward rounding, used to re-check the
computer-assisted parts of Appendix B.1 of the paper inside Lean.

* Every endpoint is a rational number; after each operation the endpoints are rounded
  outward to about `prec` significant bits (`rdn`, `rup`).
* `Itv.Mem x I` means `I.lo ≤ x ≤ I.hi` (as real numbers).
-/

@[expose] public section

namespace BSCert

/-- Working precision (in bits) of the outward rounding. -/
def prec : ℕ := 64

/-- A cheap approximation of `log₂ |q|` (exact up to `±1`); only used to choose scales. -/
def qlog2 (q : ℚ) : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)

/-- Round down to about `prec` bits. -/
def rdn (q : ℚ) : ℚ :=
  let s : ℤ := (prec : ℤ) - qlog2 q
  if 0 ≤ s then
    mkRat (q.num * ((2 ^ s.toNat : ℕ) : ℤ) / (q.den : ℤ)) (2 ^ s.toNat)
  else
    (((q.num / ((q.den * 2 ^ (-s).toNat : ℕ) : ℤ)) * ((2 ^ (-s).toNat : ℕ) : ℤ) : ℤ) : ℚ)

/-- Round up to about `prec` bits. -/
def rup (q : ℚ) : ℚ := - rdn (-q)

lemma rdn_le (q : ℚ) : rdn q ≤ q := by
  unfold rdn
  simp only
  split_ifs with hs
  · rw [Rat.mkRat_eq_div]
    set k := ((prec : ℤ) - qlog2 q).toNat
    have hd : (0 : ℤ) < q.den := by exact_mod_cast q.pos
    have h2 : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) := by positivity
    have key := Int.ediv_mul_le (q.num * ((2 ^ k : ℕ) : ℤ)) (b := (q.den : ℤ)) hd.ne'
    have key' : ((q.num * ((2 ^ k : ℕ) : ℤ) / (q.den : ℤ) : ℤ) : ℚ) * (q.den : ℚ)
        ≤ (q.num : ℚ) * ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast key
    rw [div_le_iff₀ h2]
    conv_rhs => rw [← Rat.num_div_den q]
    have hdq : (0 : ℚ) < q.den := by exact_mod_cast q.pos
    rw [div_mul_eq_mul_div, le_div_iff₀ hdq]
    push_cast at key' ⊢
    linarith
  · set k := (-((prec : ℤ) - qlog2 q)).toNat
    have hM : (0 : ℤ) < ((q.den * 2 ^ k : ℕ) : ℤ) := by
      have := q.pos; positivity
    have key := Int.ediv_mul_le q.num hM.ne'
    have key' : ((q.num / ((q.den * 2 ^ k : ℕ) : ℤ) : ℤ) : ℚ) * ((q.den : ℚ) * ((2 ^ k : ℕ) : ℚ))
        ≤ (q.num : ℚ) := by exact_mod_cast key
    conv_rhs => rw [← Rat.num_div_den q]
    have hdq : (0 : ℚ) < q.den := by exact_mod_cast q.pos
    rw [le_div_iff₀ hdq]
    push_cast at key' ⊢
    linarith

lemma le_rup (q : ℚ) : q ≤ rup q := by
  unfold rup
  have := rdn_le (-q)
  linarith

lemma rdn_le_real {q : ℚ} {x : ℝ} (h : (q : ℝ) ≤ x) : ((rdn q : ℚ) : ℝ) ≤ x :=
  le_trans (by exact_mod_cast rdn_le q) h

lemma le_rup_real {q : ℚ} {x : ℝ} (h : x ≤ (q : ℝ)) : x ≤ ((rup q : ℚ) : ℝ) :=
  le_trans h (by exact_mod_cast le_rup q)

/-! ## Intervals -/

/-- A closed interval with rational endpoints. -/
structure Itv where
  lo : ℚ
  hi : ℚ
deriving Inhabited, Repr

/-- `x ∈ [I.lo, I.hi]`. -/
def Itv.Mem (x : ℝ) (I : Itv) : Prop := ((I.lo : ℚ) : ℝ) ≤ x ∧ x ≤ ((I.hi : ℚ) : ℝ)

namespace Itv

/-- The degenerate interval `[q, q]`. -/
def pt (q : ℚ) : Itv := ⟨q, q⟩

lemma mem_pt (q : ℚ) : Mem (q : ℝ) (pt q) := ⟨le_rfl, le_rfl⟩

def add (a b : Itv) : Itv := ⟨rdn (a.lo + b.lo), rup (a.hi + b.hi)⟩
def neg (a : Itv) : Itv := ⟨-a.hi, -a.lo⟩
def sub (a b : Itv) : Itv := ⟨rdn (a.lo - b.hi), rup (a.hi - b.lo)⟩

def mul (a b : Itv) : Itv :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨rdn (min (min p1 p2) (min p3 p4)), rup (max (max p1 p2) (max p3 p4))⟩

/-- Reciprocal; `none` if the interval may contain `0`. -/
def inv (a : Itv) : Option Itv :=
  if 0 < a.lo ∨ a.hi < 0 then some ⟨rdn (1 / a.hi), rup (1 / a.lo)⟩ else none

def sq (a : Itv) : Itv :=
  if 0 ≤ a.lo then ⟨rdn (a.lo * a.lo), rup (a.hi * a.hi)⟩
  else if a.hi ≤ 0 then ⟨rdn (a.hi * a.hi), rup (a.lo * a.lo)⟩
  else ⟨0, rup (max (a.lo * a.lo) (a.hi * a.hi))⟩

def pos (a : Itv) : Itv := ⟨max a.lo 0, max a.hi 0⟩

def max (a b : Itv) : Itv := ⟨Max.max a.lo b.lo, Max.max a.hi b.hi⟩

def hull (a b : Itv) : Itv := ⟨min a.lo b.lo, Max.max a.hi b.hi⟩

lemma mem_add {x y : ℝ} {a b : Itv} (hx : Mem x a) (hy : Mem y b) : Mem (x + y) (add a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor
  · apply rdn_le_real; push_cast; linarith
  · apply le_rup_real; push_cast; linarith

lemma mem_neg {x : ℝ} {a : Itv} (hx : Mem x a) : Mem (-x) (neg a) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp [neg] <;> linarith

lemma mem_sub {x y : ℝ} {a b : Itv} (hx : Mem x a) (hy : Mem y b) : Mem (x - y) (sub a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor
  · apply rdn_le_real; push_cast; linarith
  · apply le_rup_real; push_cast; linarith

lemma min_mul_le {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (min_le_left _ _) (by nlinarith)
  · exact le_trans (min_le_right _ _) (by nlinarith)

lemma le_max_mul {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    x * y ≤ Max.max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

lemma mem_mul {x y : ℝ} {a b : Itv} (hx : Mem x a) (hy : Mem y b) : Mem (x * y) (mul a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have l1 := min_mul_le (y := y) h1 h2
  have u1 := le_max_mul (y := y) h1 h2
  have la := min_mul_le (y := (a.lo : ℝ)) h3 h4
  have lb := min_mul_le (y := (a.hi : ℝ)) h3 h4
  have ua := le_max_mul (y := (a.lo : ℝ)) h3 h4
  have ub := le_max_mul (y := (a.hi : ℝ)) h3 h4
  rw [mul_comm (b.lo : ℝ), mul_comm (b.hi : ℝ), mul_comm y] at la ua
  rw [mul_comm (b.lo : ℝ), mul_comm (b.hi : ℝ), mul_comm y] at lb ub
  constructor
  · apply rdn_le_real
    push_cast
    refine le_trans ?_ l1
    apply le_min
    · exact le_trans (min_le_left _ _) la
    · exact le_trans (min_le_right _ _) lb
  · apply le_rup_real
    push_cast
    refine le_trans u1 ?_
    apply max_le
    · exact le_trans ua (le_max_left _ _)
    · exact le_trans ub (le_max_right _ _)

lemma mem_inv {x : ℝ} {a I : Itv} (hx : Mem x a) (h : inv a = some I) :
    Mem x⁻¹ I ∧ x ≠ 0 := by
  unfold inv at h
  split_ifs at h with hc
  cases h
  obtain ⟨h1, h2⟩ := hx
  rcases hc with hc | hc
  · have hc' : (0 : ℝ) < a.lo := by exact_mod_cast hc
    have hx0 : 0 < x := lt_of_lt_of_le hc' h1
    refine ⟨⟨?_, ?_⟩, hx0.ne'⟩
    · apply rdn_le_real; push_cast
      rw [one_div]; exact inv_anti₀ hx0 h2
    · apply le_rup_real; push_cast
      rw [one_div]; exact inv_anti₀ hc' h1
  · have hc' : (a.hi : ℝ) < 0 := by exact_mod_cast hc
    have hx0 : x < 0 := lt_of_le_of_lt h2 hc'
    refine ⟨⟨?_, ?_⟩, hx0.ne⟩
    · apply rdn_le_real; push_cast
      rw [one_div]
      have := inv_anti₀ (neg_pos.mpr hc') (neg_le_neg h2)
      simp only [inv_neg] at this
      linarith
    · apply le_rup_real; push_cast
      rw [one_div]
      have := inv_anti₀ (neg_pos.mpr hx0) (neg_le_neg h1)
      simp only [inv_neg] at this
      linarith

lemma mem_sq {x : ℝ} {a : Itv} (hx : Mem x a) : Mem (x ^ 2) (sq a) := by
  obtain ⟨h1, h2⟩ := hx
  unfold sq
  split_ifs with ha hb
  · have ha' : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
    constructor
    · apply rdn_le_real; push_cast; nlinarith
    · apply le_rup_real; push_cast; nlinarith
  · have hb' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hb
    constructor
    · apply rdn_le_real; push_cast; nlinarith
    · apply le_rup_real; push_cast; nlinarith
  · constructor
    · simp; positivity
    · apply le_rup_real; push_cast
      rcases le_total 0 x with hx0 | hx0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

lemma mem_pos {x : ℝ} {a : Itv} (hx : Mem x a) : Mem (Max.max x 0) (pos a) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [pos] <;> push_cast
  · exact max_le_max h1 le_rfl
  · exact max_le_max h2 le_rfl

lemma mem_max {x y : ℝ} {a b : Itv} (hx : Mem x a) (hy : Mem y b) :
    Mem (Max.max x y) (max a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [max] <;> push_cast
  · exact max_le_max h1 h3
  · exact max_le_max h2 h4

lemma mem_hull_left {x : ℝ} {a b : Itv} (hx : Mem x a) : Mem x (hull a b) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [hull] <;> push_cast
  · exact le_trans (min_le_left _ _) h1
  · exact le_trans h2 (le_max_left _ _)

lemma mem_hull_right {x : ℝ} {a b : Itv} (hx : Mem x b) : Mem x (hull a b) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [hull] <;> push_cast
  · exact le_trans (min_le_right _ _) h1
  · exact le_trans h2 (le_max_right _ _)

end Itv

end BSCert
