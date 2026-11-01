module

public import Mathlib

/-!
# Fixed-point interval arithmetic for kernel evaluation

The rational interval arithmetic of `BSCert.Interval` is exact but slow to evaluate in the
kernel (every operation on `ℚ` normalises by a `gcd`), and its transcendental functions take
floating-point hints that the kernel cannot evaluate. This file sets up a replacement whose
operations reduce to a few `Int`/`Nat` operations on literals, so that certificates can be
checked by `decide +kernel` (no `native_decide`).

* A fixed-point number is an integer `a : ℤ`, standing for `toR a = a / 2^128`.
* `FX.FI` is an interval `[lo, hi]` of fixed-point numbers; `FI.Mem x I` means
  `toR I.lo ≤ x ≤ toR I.hi`.
* `forceN`, `forceI` make the kernel evaluate a number to a literal before passing it on
  (they are the identity, `forceN_eq`, `forceI_eq`): otherwise an accumulator in a loop is
  passed on as an ever deeper unevaluated term.
-/

@[expose] public section

namespace BSCert.FX

/-! ## Forcing -/

/-- `forceN n k = k n`, with `n` evaluated to a literal first. -/
def forceN {α : Sort*} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- `forceI x k = k x`, with `x` evaluated to `ofNat lit` / `negSucc lit` first. -/
def forceI {α : Sort*} (x : ℤ) (k : ℤ → α) : α :=
  match x with
  | .ofNat n => forceN n fun m => k (.ofNat m)
  | .negSucc n => forceN n fun m => k (.negSucc m)

@[simp] lemma forceN_eq {α : Sort*} (n : ℕ) (k : ℕ → α) : forceN n k = k n := by
  cases n <;> rfl

@[simp] lemma forceI_eq {α : Sort*} (x : ℤ) (k : ℤ → α) : forceI x k = k x := by
  cases x <;> simp [forceI]

/-! ## Scale and rounding -/

/-- The scale `2^128`. -/
def ZN : ℕ := 340282366920938463463374607431768211456
/-- The scale `2^128`, as an integer. -/
def ZI : ℤ := 340282366920938463463374607431768211456

lemma ZN_eq : ZN = 2 ^ 128 := by norm_num [ZN]
lemma ZI_eq : ZI = 2 ^ 128 := by norm_num [ZI]
lemma ZI_natCast : ((ZN : ℕ) : ℤ) = ZI := by norm_num [ZN, ZI]
lemma ZI_pos : (0 : ℤ) < ZI := by norm_num [ZI]

/-- The real value of a fixed-point number. -/
noncomputable def toR (a : ℤ) : ℝ := (a : ℝ) / (ZI : ℝ)

lemma ZR_pos : (0 : ℝ) < (ZI : ℝ) := by exact_mod_cast ZI_pos

lemma toR_add (a b : ℤ) : toR (a + b) = toR a + toR b := by
  unfold toR; push_cast; ring
lemma toR_sub (a b : ℤ) : toR (a - b) = toR a - toR b := by
  unfold toR; push_cast; ring
lemma toR_neg (a : ℤ) : toR (-a) = - toR a := by
  unfold toR; push_cast; ring
lemma toR_zero : toR 0 = 0 := by simp [toR]
lemma toR_ZI : toR ZI = 1 := by unfold toR; exact div_self ZR_pos.ne'
lemma toR_mul_ZI (a : ℤ) : toR a * ZI = a := by unfold toR; rw [div_mul_cancel₀ _ ZR_pos.ne']
lemma toR_le_toR {a b : ℤ} : toR a ≤ toR b ↔ a ≤ b := by
  unfold toR; rw [div_le_div_iff_of_pos_right ZR_pos]; exact Int.cast_le
lemma toR_lt_toR {a b : ℤ} : toR a < toR b ↔ a < b := by
  unfold toR; rw [div_lt_div_iff_of_pos_right ZR_pos]; exact Int.cast_lt
lemma toR_nonneg {a : ℤ} : 0 ≤ toR a ↔ 0 ≤ a := by
  rw [← toR_zero, toR_le_toR]
lemma toR_pos {a : ℤ} : 0 < toR a ↔ 0 < a := by
  rw [← toR_zero, toR_lt_toR]

/-- Floor division `⌊a / d⌋` (for `d > 0`). -/
def fdiv (a d : ℤ) : ℤ := a / d
/-- Ceiling division `⌈a / d⌉` (for `d > 0`). -/
def cdiv (a d : ℤ) : ℤ := -((-a) / d)

lemma fdiv_le {a d : ℤ} (hd : 0 < d) : ((fdiv a d : ℤ) : ℝ) ≤ (a : ℝ) / d := by
  unfold fdiv
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast Int.ediv_mul_le a hd.ne'

lemma le_cdiv {a d : ℤ} (hd : 0 < d) : (a : ℝ) / d ≤ ((cdiv a d : ℤ) : ℝ) := by
  unfold cdiv
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have := Int.ediv_mul_le (-a) hd.ne'
  have h2 : a ≤ -(-a / d) * d := by linarith
  exact_mod_cast h2

lemma fdiv_nonneg {a d : ℤ} (ha : 0 ≤ a) (hd : 0 < d) : 0 ≤ fdiv a d := Int.ediv_nonneg ha hd.le

/-- `⌊a / 2^128⌋`: the fixed-point value of a product `a` of two fixed-point numbers, rounded
down. -/
def fl (a : ℤ) : ℤ := fdiv a ZI
/-- `⌈a / 2^128⌉`. -/
def cl (a : ℤ) : ℤ := cdiv a ZI

lemma toR_fl (a : ℤ) : toR (fl a) ≤ (a : ℝ) / ((ZI : ℝ) * ZI) := by
  unfold toR fl
  rw [← div_div]
  exact div_le_div_of_nonneg_right (fdiv_le ZI_pos) ZR_pos.le

lemma toR_cl (a : ℤ) : (a : ℝ) / ((ZI : ℝ) * ZI) ≤ toR (cl a) := by
  unfold toR cl
  rw [← div_div]
  exact div_le_div_of_nonneg_right (le_cdiv ZI_pos) ZR_pos.le

/-- `toR a * toR b = a b / 2^256`. -/
lemma toR_mul_toR (a b : ℤ) : toR a * toR b = ((a * b : ℤ) : ℝ) / ((ZI : ℝ) * ZI) := by
  unfold toR; push_cast; field_simp

lemma fl_mul_le {a b : ℤ} : toR (fl (a * b)) ≤ toR a * toR b := by
  rw [toR_mul_toR]; exact toR_fl _

lemma le_cl_mul {a b : ℤ} : toR a * toR b ≤ toR (cl (a * b)) := by
  rw [toR_mul_toR]; exact toR_cl _

/-- The fixed-point lower bound `⌊2^128 q⌋` of a rational number. -/
def qLo (q : ℚ) : ℤ := fdiv (q.num * ZI) q.den
/-- The fixed-point upper bound `⌈2^128 q⌉` of a rational number. -/
def qHi (q : ℚ) : ℤ := cdiv (q.num * ZI) q.den

lemma qLo_le (q : ℚ) : toR (qLo q) ≤ (q : ℝ) := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.pos
  have h := fdiv_le (a := q.num * ZI) hd
  unfold toR qLo
  rw [div_le_iff₀ ZR_pos]
  refine h.trans (le_of_eq ?_)
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
    rw [← Rat.num_div_den q]; push_cast; rw [Rat.num_div_den]
  rw [hq]; push_cast; ring

lemma le_qHi (q : ℚ) : (q : ℝ) ≤ toR (qHi q) := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.pos
  have h := le_cdiv (a := q.num * ZI) hd
  unfold toR qHi
  rw [le_div_iff₀ ZR_pos]
  refine le_trans (le_of_eq ?_) h
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
    rw [← Rat.num_div_den q]; push_cast; rw [Rat.num_div_den]
  rw [hq]; push_cast; ring

/-! ## Intervals -/

/-- An interval of fixed-point numbers. -/
structure FI where
  lo : ℤ
  hi : ℤ
deriving Inhabited, Repr

/-- `x ∈ [toR lo, toR hi]`. -/
def FI.Mem (x : ℝ) (I : FI) : Prop := toR I.lo ≤ x ∧ x ≤ toR I.hi

namespace FI

/-- Evaluate both endpoints to literals before continuing. -/
def forceK {α : Sort*} (I : FI) (k : FI → α) : α :=
  forceI I.lo fun a => forceI I.hi fun b => k ⟨a, b⟩

@[simp] lemma forceK_eq {α : Sort*} (I : FI) (k : FI → α) : I.forceK k = k I := by
  simp [forceK]

/-- The enclosure `[⌊2^128 q⌋, ⌈2^128 q⌉]` of a rational constant. -/
def ofQ (q : ℚ) : FI := ⟨qLo q, qHi q⟩

lemma mem_ofQ (q : ℚ) : Mem (q : ℝ) (ofQ q) := ⟨qLo_le q, le_qHi q⟩

def add (a b : FI) : FI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : FI) : FI := ⟨-a.hi, -a.lo⟩
def sub (a b : FI) : FI := ⟨a.lo - b.hi, a.hi - b.lo⟩

def mul (a b : FI) : FI :=
  if 0 ≤ a.lo ∧ 0 ≤ b.lo then ⟨fl (a.lo * b.lo), cl (a.hi * b.hi)⟩ else
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨fl (min (min p1 p2) (min p3 p4)), cl (max (max p1 p2) (max p3 p4))⟩

/-- Reciprocal of a positive interval: `[⌊2^256 / hi⌋, ⌈2^256 / lo⌉]`. -/
def invPos (a : FI) : FI := ⟨fdiv (ZI * ZI) a.hi, cdiv (ZI * ZI) a.lo⟩

/-- Reciprocal; `none` if the interval may contain `0`. -/
def inv (a : FI) : Option FI :=
  if 0 < a.lo then some (invPos a)
  else if a.hi < 0 then some (neg (invPos (neg a)))
  else none

def sq (a : FI) : FI :=
  if 0 ≤ a.lo then ⟨fl (a.lo * a.lo), cl (a.hi * a.hi)⟩
  else if a.hi ≤ 0 then ⟨fl (a.hi * a.hi), cl (a.lo * a.lo)⟩
  else ⟨0, cl (Max.max (a.lo * a.lo) (a.hi * a.hi))⟩

def pos (a : FI) : FI := ⟨Max.max a.lo 0, Max.max a.hi 0⟩
def max (a b : FI) : FI := ⟨Max.max a.lo b.lo, Max.max a.hi b.hi⟩
def hull (a b : FI) : FI := ⟨min a.lo b.lo, Max.max a.hi b.hi⟩

lemma mem_add {x y : ℝ} {a b : FI} (hx : Mem x a) (hy : Mem y b) : Mem (x + y) (add a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [add, toR_add] <;> linarith

lemma mem_neg {x : ℝ} {a : FI} (hx : Mem x a) : Mem (-x) (neg a) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [neg, toR_neg] <;> linarith

lemma mem_sub {x y : ℝ} {a b : FI} (hx : Mem x a) (hy : Mem y b) : Mem (x - y) (sub a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [sub, toR_sub] <;> linarith

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

/-- The four corner products enclose the product (real version). -/
lemma mul_mem_corners {x y al ah bl bh : ℝ} (h1 : al ≤ x) (h2 : x ≤ ah) (h3 : bl ≤ y)
    (h4 : y ≤ bh) :
    min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh)) ≤ x * y ∧
      x * y ≤ Max.max (Max.max (al * bl) (al * bh)) (Max.max (ah * bl) (ah * bh)) := by
  have l1 := min_mul_le (y := y) h1 h2
  have u1 := le_max_mul (y := y) h1 h2
  have la := min_mul_le (y := al) h3 h4
  have lb := min_mul_le (y := ah) h3 h4
  have ua := le_max_mul (y := al) h3 h4
  have ub := le_max_mul (y := ah) h3 h4
  rw [mul_comm bl, mul_comm bh, mul_comm y] at la ua
  rw [mul_comm bl, mul_comm bh, mul_comm y] at lb ub
  constructor
  · refine le_trans ?_ l1
    apply le_min
    · exact le_trans (min_le_left _ _) la
    · exact le_trans (min_le_right _ _) lb
  · refine le_trans u1 ?_
    apply max_le
    · exact le_trans ua (le_max_left _ _)
    · exact le_trans ub (le_max_right _ _)

lemma toR_min (a b : ℤ) : toR (min a b) = min (toR a) (toR b) :=
  (Monotone.map_min (fun _ _ h => toR_le_toR.mpr h))
lemma toR_max (a b : ℤ) : toR (Max.max a b) = Max.max (toR a) (toR b) :=
  (Monotone.map_max (fun _ _ h => toR_le_toR.mpr h))

lemma mem_mul {x y : ℝ} {a b : FI} (hx : Mem x a) (hy : Mem y b) : Mem (x * y) (mul a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  unfold mul
  split_ifs with hp
  · obtain ⟨ha, hb⟩ := hp
    have ha' : 0 ≤ toR a.lo := toR_nonneg.mpr ha
    have hb' : 0 ≤ toR b.lo := toR_nonneg.mpr hb
    constructor
    · exact fl_mul_le.trans (mul_le_mul h1 h3 hb' (ha'.trans h1))
    · exact (mul_le_mul h2 h4 (hb'.trans h3) ((ha'.trans h1).trans h2)).trans le_cl_mul
  · obtain ⟨c1, c2⟩ := mul_mem_corners h1 h2 h3 h4
    have hD : (0 : ℝ) ≤ (ZI : ℝ) * ZI := (mul_pos ZR_pos ZR_pos).le
    constructor
    · refine le_trans (toR_fl _) (le_trans (le_of_eq ?_) c1)
      simp only [toR_mul_toR, Int.cast_min, min_div_div_right hD]
    · refine le_trans c2 (le_trans (le_of_eq ?_) (toR_cl _))
      simp only [toR_mul_toR, Int.cast_max, max_div_div_right hD]

lemma mem_invPos {x : ℝ} {a : FI} (hx : Mem x a) (h0 : 0 < a.lo) :
    Mem x⁻¹ (invPos a) ∧ 0 < x := by
  obtain ⟨h1, h2⟩ := hx
  have hl : 0 < toR a.lo := toR_pos.mpr h0
  have hx0 : 0 < x := lt_of_lt_of_le hl h1
  have hhi : 0 < a.hi := toR_pos.mp (lt_of_lt_of_le hx0 h2)
  have hh : 0 < toR a.hi := toR_pos.mpr hhi
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · -- `⌊Z² / hi⌋ / Z ≤ Z / hi = 1 / toR hi ≤ 1 / x`
    have e : (1 : ℝ) / toR a.hi = ((ZI * ZI : ℤ) : ℝ) / (a.hi : ℝ) / ZI := by
      unfold toR; push_cast; field_simp
    have := fdiv_le (a := ZI * ZI) hhi
    calc toR (fdiv (ZI * ZI) a.hi) = ((fdiv (ZI * ZI) a.hi : ℤ) : ℝ) / ZI := rfl
      _ ≤ ((ZI * ZI : ℤ) : ℝ) / (a.hi : ℝ) / ZI := div_le_div_of_nonneg_right this ZR_pos.le
      _ = 1 / toR a.hi := e.symm
      _ ≤ x⁻¹ := by rw [one_div]; exact inv_anti₀ hx0 h2
  · have e : (1 : ℝ) / toR a.lo = ((ZI * ZI : ℤ) : ℝ) / (a.lo : ℝ) / ZI := by
      unfold toR; push_cast; field_simp
    have := le_cdiv (a := ZI * ZI) h0
    calc x⁻¹ ≤ 1 / toR a.lo := by rw [one_div]; exact inv_anti₀ hl h1
      _ = ((ZI * ZI : ℤ) : ℝ) / (a.lo : ℝ) / ZI := e
      _ ≤ ((cdiv (ZI * ZI) a.lo : ℤ) : ℝ) / ZI := div_le_div_of_nonneg_right this ZR_pos.le
      _ = toR (cdiv (ZI * ZI) a.lo) := rfl

lemma mem_inv {x : ℝ} {a I : FI} (hx : Mem x a) (h : inv a = some I) : Mem x⁻¹ I ∧ x ≠ 0 := by
  unfold inv at h
  split_ifs at h with h1 h2
  · cases h; exact ⟨(mem_invPos hx h1).1, (mem_invPos hx h1).2.ne'⟩
  · cases h
    have hn := mem_neg hx
    have h0 : 0 < (neg a).lo := by simp [neg]; exact h2
    obtain ⟨hm, hpos⟩ := mem_invPos hn h0
    have := mem_neg hm
    rw [inv_neg, neg_neg] at this
    exact ⟨this, by linarith⟩

lemma mem_sq {x : ℝ} {a : FI} (hx : Mem x a) : Mem (x ^ 2) (sq a) := by
  obtain ⟨h1, h2⟩ := hx
  rw [pow_two]
  unfold FI.sq
  split_ifs with ha hb
  · have ha' : 0 ≤ toR a.lo := toR_nonneg.mpr ha
    exact ⟨fl_mul_le.trans (mul_le_mul h1 h1 ha' (ha'.trans h1)),
      (mul_le_mul h2 h2 (ha'.trans h1) ((ha'.trans h1).trans h2)).trans le_cl_mul⟩
  · have hb' : toR a.hi ≤ 0 := by rw [← toR_zero]; exact toR_le_toR.mpr hb
    constructor
    · refine fl_mul_le.trans ?_; nlinarith
    · refine le_trans ?_ le_cl_mul; nlinarith
  · constructor
    · rw [toR_zero]; exact mul_self_nonneg x
    · refine le_trans ?_ (toR_cl _)
      rw [Int.cast_max, ← max_div_div_right (le_of_lt (mul_pos ZR_pos ZR_pos)),
        ← toR_mul_toR, ← toR_mul_toR]
      have : toR a.lo ≤ 0 := by rw [← toR_zero]; exact toR_le_toR.mpr (le_of_lt (not_le.mp ha))
      have : 0 ≤ toR a.hi := by rw [← toR_zero]; exact toR_le_toR.mpr (le_of_lt (not_le.mp hb))
      rcases le_total 0 x with hx0 | hx0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

lemma mem_pos {x : ℝ} {a : FI} (hx : Mem x a) : Mem (Max.max x 0) (pos a) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [pos, toR_max, toR_zero]
  · exact max_le_max h1 le_rfl
  · exact max_le_max h2 le_rfl

lemma mem_max {x y : ℝ} {a b : FI} (hx : Mem x a) (hy : Mem y b) :
    Mem (Max.max x y) (max a b) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [FI.max, toR_max]
  · exact max_le_max h1 h3
  · exact max_le_max h2 h4

lemma mem_hull_left {x : ℝ} {a b : FI} (hx : Mem x a) : Mem x (hull a b) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [hull, toR_max, toR_min]
  · exact le_trans (min_le_left _ _) h1
  · exact le_trans h2 (le_max_left _ _)

lemma mem_hull_right {x : ℝ} {a b : FI} (hx : Mem x b) : Mem x (hull a b) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [hull, toR_max, toR_min]
  · exact le_trans (min_le_right _ _) h1
  · exact le_trans h2 (le_max_right _ _)

end FI

end BSCert.FX
