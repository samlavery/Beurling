module

public import Mathlib

/-!
# Auxiliary facts for step (iii) of Proposition 5.18

* `r8 x = x^{1/8}` (as `√√√x`) and its algebra: `r8_pow8`, `le_r8_of_pow8`, `r8_mono`,
  `r8_mul`, `log_le_r8` (`log x ≤ 8 x^{1/8}`), `log_le_two_sqrt` (`log x ≤ 2√x`);
* `sum_sep_le` : a geometric bound for sums over a `2`-separated finite set of reals:
  if `g ≥ 0` is antitone on `[V₀, ∞)` and `g(2v) ≤ r g(v)` there (`0 ≤ r < 1`), then
  `∑_{v ∈ S} g(v) ≤ g(V₀)/(1 - r)` for every finite `S ⊆ [V₀, ∞)` with `v < w ⇒ 2v ≤ w`;
* the dyadic scales `v = X₀ 2^k` (`k ∈ ℤ`): `dyadic_sep`, `dyadic_lt`, `dyadic_eq`.
-/

@[expose] public section

open Finset Real

namespace KR.X0S

/-! ## `x^{1/8}` -/

/-- `x^{1/8} = √√√x`. -/
noncomputable def r8 (x : ℝ) : ℝ := √(√(√x))

lemma r8_nonneg (x : ℝ) : 0 ≤ r8 x := Real.sqrt_nonneg _

lemma r8_pow8 {x : ℝ} (hx : 0 ≤ x) : r8 x ^ 8 = x := by
  unfold r8
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg (√x))
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h3 := Real.sq_sqrt hx
  calc (√(√(√x))) ^ 8 = ((√(√(√x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma r8_mono {a b : ℝ} (h : a ≤ b) : r8 a ≤ r8 b := by
  unfold r8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h))

lemma r8_of_pow8 {h : ℝ} (h0 : 0 ≤ h) : r8 (h ^ 8) = h := by
  unfold r8
  have e1 : h ^ 8 = (h ^ 4) ^ 2 := by ring
  have e2 : h ^ 4 = (h ^ 2) ^ 2 := by ring
  rw [e1, Real.sqrt_sq (by positivity), e2, Real.sqrt_sq (by positivity), Real.sqrt_sq h0]

lemma le_r8_of_pow8 {h B : ℝ} (h0 : 0 ≤ h) (hb : h ^ 8 ≤ B) : h ≤ r8 B := by
  rw [← r8_of_pow8 h0]; exact r8_mono hb

lemma r8_mul {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) : r8 (a * b) = r8 a * r8 b := by
  unfold r8
  rw [Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_mul (Real.sqrt_nonneg _)]

lemma one_le_r8 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ r8 x := by
  have := r8_mono hx
  unfold r8 at this ⊢
  simpa using this

lemma r8_pos {x : ℝ} (hx : 0 < x) : 0 < r8 x := by
  unfold r8; positivity

/-- `log x ≤ 8 x^{1/8}`. -/
lemma log_le_r8 {x : ℝ} (hx : 0 < x) : Real.log x ≤ 8 * r8 x := by
  have hr := r8_pos hx
  have e : Real.log x = 8 * Real.log (r8 x) := by
    conv_lhs => rw [← r8_pow8 hx.le]
    rw [Real.log_pow]; push_cast; ring
  rw [e]
  have := Real.log_le_sub_one_of_pos hr
  linarith

/-- `log x ≤ 2√x`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.mpr hx
  have e : Real.log x = 2 * Real.log √x := by
    conv_lhs => rw [← Real.sq_sqrt hx.le]
    rw [Real.log_pow]; push_cast; ring
  rw [e]
  have := Real.log_le_sub_one_of_pos hs
  linarith

/-! ## Sums over separated families -/

/-- `v < w ⇒ 2v ≤ w` on `S`. -/
def Sep2 (S : Finset ℝ) : Prop := ∀ v ∈ S, ∀ w ∈ S, v < w → 2 * v ≤ w

/-- **Geometric bound** over a `2`-separated family. -/
theorem sum_sep_le {g : ℝ → ℝ} {V0 r : ℝ} (_hV0 : 0 < V0) (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg0 : ∀ v, V0 ≤ v → 0 ≤ g v) (hanti : ∀ v w, V0 ≤ v → v ≤ w → g w ≤ g v)
    (h2 : ∀ v, V0 ≤ v → g (2 * v) ≤ r * g v) (S : Finset ℝ) (hS : Sep2 S)
    (hSV : ∀ v ∈ S, V0 ≤ v) : ∑ v ∈ S, g v ≤ g V0 / (1 - r) := by
  classical
  have h1r : 0 < 1 - r := by linarith
  have key : ∀ S : Finset ℝ, Sep2 S → ∀ m, V0 ≤ m → (∀ v ∈ S, m ≤ v) →
      ∑ v ∈ S, g v ≤ g m / (1 - r) := by
    intro S
    induction S using Finset.induction_on_min with
    | empty =>
      intro _ m hm _
      simp only [Finset.sum_empty]
      exact div_nonneg (hg0 m hm) h1r.le
    | insert a s hlt ih =>
      intro hS m hm hmS
      have ha : m ≤ a := hmS a (Finset.mem_insert_self a s)
      have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
      rw [Finset.sum_insert has]
      have hS' : Sep2 s := fun v hv w hw hvw =>
        hS v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw) hvw
      have h2a : ∀ v ∈ s, 2 * a ≤ v := fun v hv =>
        hS a (Finset.mem_insert_self a s) v (Finset.mem_insert_of_mem hv) (hlt v hv)
      have hVa : V0 ≤ a := hm.trans ha
      have hrec := ih hS' (2 * a) (by linarith) h2a
      have hga := h2 a hVa
      have hga0 := hg0 a hVa
      have hmono := hanti m a hm ha
      calc g a + ∑ v ∈ s, g v ≤ g a + g (2 * a) / (1 - r) := by linarith
        _ ≤ g a + r * g a / (1 - r) := by
          gcongr
        _ = g a / (1 - r) := by field_simp; ring
        _ ≤ g m / (1 - r) := div_le_div_of_nonneg_right hmono h1r.le
  exact key S hS V0 le_rfl hSV

/-! ## Dyadic scales -/

/-- The dyadic scales `v = X₀ 2^k`, `k ∈ ℤ`. -/
def Dyadic (X0 : ℝ) (S : Finset ℝ) : Prop := ∀ v ∈ S, ∃ k : ℤ, v = X0 * 2 ^ k

lemma dyadic_sep {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Dyadic X0 S) : Sep2 S := by
  intro v hv w hw hvw
  obtain ⟨k, rfl⟩ := hS v hv
  obtain ⟨j, rfl⟩ := hS w hw
  have hkj : k < j := by
    by_contra h
    push_neg at h
    have : (2 : ℝ) ^ j ≤ 2 ^ k := zpow_le_zpow_right₀ (by norm_num) h
    nlinarith
  have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_add₀ (by norm_num), zpow_one] at this
  nlinarith

lemma dyadic_lt {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Dyadic X0 S) {v : ℝ} (hv : v ∈ S)
    (hlt : v < X0) : 2 * v ≤ X0 := by
  obtain ⟨k, rfl⟩ := hS v hv
  have hk : k < 0 := by
    by_contra h
    push_neg at h
    have : (1 : ℝ) ≤ 2 ^ k := one_le_zpow₀ (by norm_num) h
    nlinarith
  have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_add₀ (by norm_num), zpow_one, zpow_zero] at this
  nlinarith

lemma dyadic_eq {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Dyadic X0 S) {v : ℝ} (hv : v ∈ S)
    (h1 : X0 ≤ v) (h2 : v < 2 * X0) : v = X0 := by
  obtain ⟨k, rfl⟩ := hS v hv
  have hk0 : 0 ≤ k := by
    by_contra h
    push_neg at h
    have : (2 : ℝ) ^ k < 1 := zpow_lt_one_of_neg₀ (by norm_num) h
    nlinarith
  have hk1 : k < 1 := by
    by_contra h
    push_neg at h
    have : (2 : ℝ) ^ (1 : ℤ) ≤ 2 ^ k := zpow_le_zpow_right₀ (by norm_num) h
    rw [zpow_one] at this
    nlinarith
  have : k = 0 := by omega
  subst this; simp

end KR.X0S

end
