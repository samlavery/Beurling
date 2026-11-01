module

public import RequestProject.BSCert.Dickman

/-!
# Covering an interval by checked cells

`cover f d step n x b` walks from `x` to `b` in cells `[x, step x]`, `[step x, step (step x)]`,
…, the last one ending exactly at `b`. Each cell is accepted by the cell test `f`, possibly
after bisecting it up to depth `d` (`bisect`). If the walk succeeds, every point of `[x, b]`
lies in an accepted cell (`cover_sound`).
-/

@[expose] public section

namespace BSCert

/-- Accept `[a, b]` if `f a b`, or (up to depth `d`) if both halves are accepted. -/
def bisect (f : ℚ → ℚ → Bool) : ℕ → ℚ → ℚ → Bool
  | 0, a, b => f a b
  | d + 1, a, b => f a b || (bisect f d a ((a + b) / 2) && bisect f d ((a + b) / 2) b)

lemma bisect_sound (P : ℝ → Prop) (f : ℚ → ℚ → Bool)
    (hf : ∀ a b : ℚ, f a b = true → ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (b : ℝ) → P u) :
    ∀ (d : ℕ) (a b : ℚ), bisect f d a b = true → ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (b : ℝ) → P u := by
  intro d
  induction d with
  | zero => intro a b h; exact hf a b h
  | succ d ih =>
    intro a b h u hu1 hu2
    simp only [bisect, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact hf a b h u hu1 hu2
    · rcases le_total u (((a + b) / 2 : ℚ) : ℝ) with hm | hm
      · exact ih _ _ h1 u hu1 hm
      · exact ih _ _ h2 u hm hu2

/-- Walk from `x` to `b` with steps `step`, checking each cell with `bisect f d`. -/
def cover (f : ℚ → ℚ → Bool) (d : ℕ) (step : ℚ → ℚ) : ℕ → ℚ → ℚ → Bool
  | 0, _, _ => false
  | n + 1, x, b =>
    let y := step x
    if b ≤ y then bisect f d x b
    else decide (x < y) && bisect f d x y && cover f d step n y b

lemma cover_sound (P : ℝ → Prop) (f : ℚ → ℚ → Bool)
    (hf : ∀ a b : ℚ, f a b = true → ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (b : ℝ) → P u)
    (d : ℕ) (step : ℚ → ℚ) :
    ∀ (n : ℕ) (x b : ℚ), cover f d step n x b = true →
      ∀ u : ℝ, (x : ℝ) ≤ u → u ≤ (b : ℝ) → P u := by
  intro n
  induction n with
  | zero => intro x b h; simp [cover] at h
  | succ n ih =>
    intro x b h u hu1 hu2
    simp only [cover] at h
    split_ifs at h with hb
    · exact bisect_sound P f hf d x b h u hu1 hu2
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨-, h1⟩, h2⟩ := h
      rcases le_total u ((step x : ℚ) : ℝ) with hm | hm
      · exact bisect_sound P f hf d x _ h1 u hu1 hm
      · exact ih _ b h2 u hm hu2

/-- Geometric step `x ↦ x · q`, rounded (only its progress matters, which is checked). -/
def gstep (q : ℚ) (x : ℚ) : ℚ := rup (x * q)

/-- Arithmetic step `x ↦ x + h`. -/
def astep (h : ℚ) (x : ℚ) : ℚ := x + h

end BSCert
