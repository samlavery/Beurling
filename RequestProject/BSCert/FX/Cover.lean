module

public import RequestProject.BSCert.FX.Core

/-!
# Covering an interval by checked cells (fixed-point endpoints)

The analogue of `BSCert.Cover` with endpoints in `ℤ` (standing for `toR x = x / 2^128`):
`coverF f d step n x b` walks from `x` to `b` in cells `[x, step x]`, …, the last one ending at
`b`; each cell is accepted by `f`, possibly after bisecting it up to depth `d`.
-/

@[expose] public section

namespace BSCert.FX

/-- Accept `[a, b]` if `f a b`, or (up to depth `d`) if both halves are accepted. -/
def bisectF (f : ℤ → ℤ → Bool) : ℕ → ℤ → ℤ → Bool
  | 0, a, b => f a b
  | d + 1, a, b => f a b || (bisectF f d a ((a + b) / 2) && bisectF f d ((a + b) / 2) b)

lemma bisectF_sound (P : ℝ → Prop) (f : ℤ → ℤ → Bool)
    (hf : ∀ a b : ℤ, f a b = true → ∀ u : ℝ, toR a ≤ u → u ≤ toR b → P u) :
    ∀ (d : ℕ) (a b : ℤ), bisectF f d a b = true → ∀ u : ℝ, toR a ≤ u → u ≤ toR b → P u := by
  intro d
  induction d with
  | zero => intro a b h; exact hf a b h
  | succ d ih =>
    intro a b h u hu1 hu2
    simp only [bisectF, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact hf a b h u hu1 hu2
    · rcases le_total u (toR ((a + b) / 2)) with hm | hm
      · exact ih _ _ h1 u hu1 hm
      · exact ih _ _ h2 u hm hu2

/-- Walk from `x` to `b` with steps `step`, checking each cell with `bisectF f d`. -/
def coverF (f : ℤ → ℤ → Bool) (d : ℕ) (step : ℤ → ℤ) : ℕ → ℤ → ℤ → Bool
  | 0, _, _ => false
  | n + 1, x, b =>
    forceI (step x) fun y =>
    if b ≤ y then bisectF f d x b
    else decide (x < y) && bisectF f d x y && coverF f d step n y b

lemma coverF_sound (P : ℝ → Prop) (f : ℤ → ℤ → Bool)
    (hf : ∀ a b : ℤ, f a b = true → ∀ u : ℝ, toR a ≤ u → u ≤ toR b → P u)
    (d : ℕ) (step : ℤ → ℤ) :
    ∀ (n : ℕ) (x b : ℤ), coverF f d step n x b = true →
      ∀ u : ℝ, toR x ≤ u → u ≤ toR b → P u := by
  intro n
  induction n with
  | zero => intro x b h; simp [coverF] at h
  | succ n ih =>
    intro x b h u hu1 hu2
    simp only [coverF, forceI_eq] at h
    split_ifs at h with hb
    · exact bisectF_sound P f hf d x b h u hu1 hu2
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨-, h1⟩, h2⟩ := h
      rcases le_total u (toR (step x)) with hm | hm
      · exact bisectF_sound P f hf d x _ h1 u hu1 hm
      · exact ih _ b h2 u hm hu2

/-- Check `f` on the consecutive cells `[x, m₁], [m₁, m₂], …, [m_k, y]` of an explicit list of
break points. -/
def coverL (f : ℤ → ℤ → Bool) : ℤ → List ℤ → ℤ → Bool
  | x, [], y => f x y
  | x, m :: l, y => f x m && coverL f m l y

lemma coverL_sound (P : ℝ → Prop) (f : ℤ → ℤ → Bool)
    (hf : ∀ a b : ℤ, f a b = true → ∀ u : ℝ, toR a ≤ u → u ≤ toR b → P u) :
    ∀ (l : List ℤ) (x y : ℤ), coverL f x l y = true → ∀ u : ℝ, toR x ≤ u → u ≤ toR y → P u := by
  intro l
  induction l with
  | nil => intro x y h; exact hf x y h
  | cons m l ih =>
    intro x y h u hu1 hu2
    simp only [coverL, Bool.and_eq_true] at h
    rcases le_total u (toR m) with hm | hm
    · exact hf x m h.1 u hu1 hm
    · exact ih m y h.2 u hm hu2

end BSCert.FX
