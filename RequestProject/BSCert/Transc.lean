module

public import RequestProject.BSCert.Interval

/-!
# Rigorous enclosures of `exp`, `log` and `sqrt`

* `exp`: argument halving `x = 2ᵏ y` with `|y|` small, Taylor polynomial of degree `< expN`
  with the remainder bound `Real.exp_bound` from Mathlib, then `k` squarings with outward
  rounding.
* `log`: a floating-point guess `g ≈ log a`, shifted down (up) by a small margin, is accepted
  as a lower (upper) bound only after the `exp` enclosure *proves* `exp g ≤ a` (`a ≤ exp g`);
  otherwise the elementary bounds `1 - 1/a ≤ log a ≤ a - 1` are used.
* `sqrt`: a floating-point guess, checked exactly by squaring, with elementary fallbacks.

Floating point only proposes candidates; every returned bound is justified by an exact
rational check.
-/

@[expose] public section

namespace BSCert

/-- `(∑_{m<n} y^m/m!, y^n/n!)`, computed incrementally. -/
def expSeries (y : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | n + 1 => let p := expSeries y n; (p.1 + p.2, p.2 * y / (n + 1))

lemma expSeries_spec (y : ℚ) (n : ℕ) :
    expSeries y n = (∑ m ∈ Finset.range n, y ^ m / m.factorial, y ^ n / n.factorial) := by
  induction n with
  | zero => simp [expSeries]
  | succ n ih =>
    simp only [expSeries, ih, Finset.sum_range_succ, Prod.mk.injEq, true_and]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Number of Taylor terms. -/
def expN : ℕ := 12

/-- Number of halvings used for the argument `x`. -/
def expRed (x : ℚ) : ℕ := (qlog2 x + 10).toNat

/-- `k` outward-rounded squarings of a bracket. -/
def sqIter : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | k + 1, p => sqIter k (rdn (max p.1 0 * max p.1 0), rup (p.2 * p.2))

lemma sqIter_spec (k : ℕ) : ∀ (p : ℚ × ℚ) (z : ℝ), ((p.1 : ℚ) : ℝ) ≤ Real.exp z →
    Real.exp z ≤ ((p.2 : ℚ) : ℝ) →
    (((sqIter k p).1 : ℚ) : ℝ) ≤ Real.exp (z * 2 ^ k) ∧
      Real.exp (z * 2 ^ k) ≤ (((sqIter k p).2 : ℚ) : ℝ) := by
  induction k with
  | zero => intro p z h1 h2; simpa [sqIter] using ⟨h1, h2⟩
  | succ k ih =>
    intro p z h1 h2
    have he : Real.exp (z * 2) = Real.exp z * Real.exp z := by
      rw [← Real.exp_add]; ring_nf
    have hpos := Real.exp_pos z
    have key := ih (rdn (max p.1 0 * max p.1 0), rup (p.2 * p.2)) (z * 2) ?_ ?_
    · have : z * 2 * 2 ^ k = z * 2 ^ (k + 1) := by ring
      rw [this] at key
      simpa [sqIter] using key
    · apply rdn_le_real
      rw [he]; push_cast
      have h0 : (0 : ℝ) ≤ max (p.1 : ℝ) 0 := le_max_right _ _
      have h1' : max (p.1 : ℝ) 0 ≤ Real.exp z := max_le h1 hpos.le
      exact mul_le_mul h1' h1' h0 hpos.le
    · apply le_rup_real
      rw [he]; push_cast
      exact mul_le_mul h2 h2 hpos.le (le_trans hpos.le h2)

/-- A rigorous bracket `(lo, hi)` of `exp x`, or `none`. -/
def expPt (x : ℚ) : Option (ℚ × ℚ) :=
  let k := expRed x
  let y := x / ((2 ^ k : ℕ) : ℚ)
  if |y| ≤ 1 then
    let s := (expSeries y expN).1
    let err := |y| ^ expN * (((expN + 1 : ℕ) : ℚ) / ((expN.factorial : ℚ) * expN))
    some (sqIter k (rdn (s - err), rup (s + err)))
  else none

lemma expPt_spec {x : ℚ} {p : ℚ × ℚ} (h : expPt x = some p) :
    ((p.1 : ℚ) : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ ((p.2 : ℚ) : ℝ) := by
  unfold expPt at h
  simp only at h
  split_ifs at h with hy
  cases h
  set k := expRed x
  set y : ℚ := x / ((2 ^ k : ℕ) : ℚ) with hydef
  have hxy : (x : ℝ) = (y : ℝ) * 2 ^ k := by
    rw [hydef]; push_cast; field_simp
  rw [hxy]
  apply sqIter_spec
  · have hb := Real.exp_bound (x := (y : ℝ)) (by exact_mod_cast hy) (n := expN) (by decide)
    rw [expSeries_spec]
    apply rdn_le_real
    push_cast
    have := (abs_le.mp hb).1
    simp only [Nat.succ_eq_add_one] at this
    push_cast at this ⊢
    linarith
  · have hb := Real.exp_bound (x := (y : ℝ)) (by exact_mod_cast hy) (n := expN) (by decide)
    rw [expSeries_spec]
    apply le_rup_real
    push_cast
    have := (abs_le.mp hb).2
    simp only [Nat.succ_eq_add_one] at this
    push_cast at this ⊢
    linarith

/-- Convert a float to an exact rational (`none` for `NaN`/`∞`). -/
def ratOfFloat (f : Float) : Option ℚ :=
  match f.toRatParts with
  | some (m, e) =>
      some (if 0 ≤ e then (m : ℚ) * ((2 ^ e.toNat : ℕ) : ℚ) else (m : ℚ) / ((2 ^ (-e).toNat : ℕ) : ℚ))
  | none => none

/-- Relative margin applied to floating-point guesses. -/
def guessMargin : ℚ := 1 / 2 ^ 46

/-- A certified lower bound for `log a` (for `a > 0`). -/
def logLoPt (a : ℚ) : ℚ :=
  let fb := rdn (1 - 1 / a)
  match ratOfFloat (Float.log a.toFloat) with
  | some g =>
    let g' := rdn (g - (|g| + 1) * guessMargin)
    match expPt g' with
    | some p => if p.2 ≤ a then max g' fb else fb
    | none => fb
  | none => fb

/-- A certified upper bound for `log a` (for `a > 0`). -/
def logHiPt (a : ℚ) : ℚ :=
  let fb := rup (a - 1)
  match ratOfFloat (Float.log a.toFloat) with
  | some g =>
    let g' := rup (g + (|g| + 1) * guessMargin)
    match expPt g' with
    | some p => if a ≤ p.1 then min g' fb else fb
    | none => fb
  | none => fb

lemma logLoPt_le {a : ℚ} (ha : 0 < a) : ((logLoPt a : ℚ) : ℝ) ≤ Real.log a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hfb : ((rdn (1 - 1 / a) : ℚ) : ℝ) ≤ Real.log a := by
    apply rdn_le_real
    have := Real.one_sub_inv_le_log_of_pos ha'
    push_cast; simpa [one_div] using this
  unfold logLoPt
  dsimp only
  split
  · rename_i g _
    split
    · rename_i p hp
      split_ifs with hle
      · push_cast
        refine max_le ?_ hfb
        rw [Real.le_log_iff_exp_le ha']
        exact le_trans (expPt_spec hp).2 (by exact_mod_cast hle)
      · exact hfb
    · exact hfb
  · exact hfb

lemma le_logHiPt {a : ℚ} (ha : 0 < a) : Real.log a ≤ ((logHiPt a : ℚ) : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hfb : Real.log a ≤ ((rup (a - 1) : ℚ) : ℝ) := by
    apply le_rup_real
    have := Real.log_le_sub_one_of_pos ha'
    push_cast; exact this
  unfold logHiPt
  dsimp only
  split
  · rename_i g _
    split
    · rename_i p hp
      split_ifs with hle
      · push_cast
        refine le_min ?_ hfb
        rw [Real.log_le_iff_le_exp ha']
        exact le_trans (by exact_mod_cast hle) (expPt_spec hp).1
      · exact hfb
    · exact hfb
  · exact hfb

/-- A certified lower bound for `√a`. -/
def sqrtLoPt (a : ℚ) : ℚ :=
  match ratOfFloat (Float.sqrt a.toFloat) with
  | some g =>
    let g' := rdn (g * (1 - guessMargin))
    if 0 ≤ g' ∧ g' * g' ≤ a then g' else 0
  | none => 0

/-- A certified upper bound for `√a`. -/
def sqrtHiPt (a : ℚ) : ℚ :=
  let fb := max a 1
  match ratOfFloat (Float.sqrt a.toFloat) with
  | some g =>
    let g' := rup (g * (1 + guessMargin))
    if 0 ≤ g' ∧ a ≤ g' * g' then g' else fb
  | none => fb

lemma sqrtLoPt_le (a : ℚ) : ((sqrtLoPt a : ℚ) : ℝ) ≤ Real.sqrt a := by
  unfold sqrtLoPt
  dsimp only
  split
  · split_ifs with h
    · obtain ⟨h0, h1⟩ := h
      generalize rdn (_ * (1 - guessMargin)) = t at h0 h1 ⊢
      have h0' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h0
      have h1' : (t : ℝ) * (t : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
      rw [Real.le_sqrt h0' (le_trans (mul_self_nonneg _) h1')]
      nlinarith
    · simp [Real.sqrt_nonneg]
  · simp [Real.sqrt_nonneg]

lemma le_sqrtHiPt (a : ℚ) : Real.sqrt a ≤ ((sqrtHiPt a : ℚ) : ℝ) := by
  have hfb : Real.sqrt a ≤ ((max a 1 : ℚ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((max a 1 : ℚ) : ℝ) := by
      push_cast; exact le_trans zero_le_one (le_max_right _ _)
    rw [Real.sqrt_le_left h0]
    push_cast
    rcases le_total (a : ℝ) 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; nlinarith
  unfold sqrtHiPt
  dsimp only
  split
  · split_ifs with h
    · obtain ⟨h0, h1⟩ := h
      generalize rup (_ * (1 + guessMargin)) = t at h0 h1 ⊢
      have h0' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h0
      have h1' : (a : ℝ) ≤ (t : ℝ) * (t : ℝ) := by exact_mod_cast h1
      rw [Real.sqrt_le_left h0']
      nlinarith
    · exact hfb
  · exact hfb

namespace Itv

/-- Interval `exp`. -/
def exp (a : Itv) : Option Itv :=
  match expPt a.lo, expPt a.hi with
  | some p, some q => some ⟨p.1, q.2⟩
  | _, _ => none

/-- Interval `log`; `none` unless the interval is positive. -/
def log (a : Itv) : Option Itv :=
  if 0 < a.lo then some ⟨logLoPt a.lo, logHiPt a.hi⟩ else none

/-- Interval `sqrt` (`Real.sqrt` is monotone on all of `ℝ`). -/
def sqrt (a : Itv) : Itv := ⟨sqrtLoPt a.lo, sqrtHiPt a.hi⟩

lemma mem_exp {x : ℝ} {a I : Itv} (hx : Mem x a) (h : exp a = some I) : Mem (Real.exp x) I := by
  unfold exp at h
  split at h
  · rename_i p q hp hq
    cases h
    obtain ⟨h1, h2⟩ := hx
    exact ⟨le_trans (expPt_spec hp).1 (Real.exp_le_exp.mpr h1),
      le_trans (Real.exp_le_exp.mpr h2) (expPt_spec hq).2⟩
  · cases h

lemma mem_log {x : ℝ} {a I : Itv} (hx : Mem x a) (h : log a = some I) :
    Mem (Real.log x) I ∧ 0 < x := by
  unfold log at h
  split_ifs at h with h0
  cases h
  obtain ⟨h1, h2⟩ := hx
  have h0' : (0 : ℝ) < a.lo := by exact_mod_cast h0
  have hx0 : 0 < x := lt_of_lt_of_le h0' h1
  have hhi : (0 : ℚ) < a.hi := by
    have : (0 : ℝ) < a.hi := lt_of_lt_of_le hx0 h2
    exact_mod_cast this
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · exact le_trans (logLoPt_le h0) (Real.log_le_log h0' h1)
  · exact le_trans (Real.log_le_log hx0 h2) (le_logHiPt hhi)

lemma mem_sqrt {x : ℝ} {a : Itv} (hx : Mem x a) : Mem (Real.sqrt x) (sqrt a) := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨le_trans (sqrtLoPt_le _) (Real.sqrt_le_sqrt h1),
    le_trans (Real.sqrt_le_sqrt h2) (le_sqrtHiPt _)⟩

end Itv

end BSCert
