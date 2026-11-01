module

public import RequestProject.Beurling.Noise.LemSDefs

/-!
# Lemma 5.21 (i) and the Dickman form of (ii)

* `omegaW_le_harmBlock`, `HBS.lemS_i` : (i) `ω_y(v) ≤ 1` (the paper states `≤ 1.2`);
* `omegaW_le_vSmooth` : the filter forces `P⁺(w) ≤ 3v` (`DecidedSmall`), so `ω_y(v)` is at most
  the smooth dyadic sum `v(log(y/2v), 3v)`;
* `HBS.lemS_ii_dickman` : (ii), first bound: for `1 ≤ u_y ≤ log 3v`,
  `ω_y(v) ≤ C₀ ρ(u_y) e^{a_V}` (Lemma 5.3 with `z = 3v`; the paper has `2C₀`), and
  `a_V ≤ 13 u_y log(u_y + 2)/log 3v`.
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable {P : BeurlingSystem}

lemma omegaW_nonneg (t : ℕ → ℝ) (y v : ℝ) : 0 ≤ P.omegaW t y v :=
  Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le

lemma window_iff' {y v : ℝ} (hv : 0 < v) (e : ℕ →₀ ℕ) :
    (v ≤ y / P.val e ∧ y / P.val e < 2 * v) ↔ (y / (2 * v) < P.val e ∧ P.val e ≤ y / v) := by
  have he := P.val_pos e
  rw [le_div_iff₀ he, div_lt_iff₀ he, div_lt_iff₀ (by positivity), le_div_iff₀ hv]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma two_mul_div_two_mul {y v : ℝ} (hv : 0 < v) : 2 * (y / (2 * v)) = y / v := by
  field_simp

/-- Dropping the filter: `ω_y(v) ≤ ∑_{𝒩 ∩ (y/2v, y/v]} 1/w`. -/
lemma omegaW_le_harmBlock (t : ℕ → ℝ) {y v : ℝ} (hv : 0 < v) :
    P.omegaW t y v ≤ P.harmBlock (y / (2 * v)) := by
  unfold omegaW harmBlock
  rw [two_mul_div_two_mul hv]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter, mem_elems] at he ⊢
    exact ⟨he.1, ((window_iff' hv e).mp ⟨he.2.1, he.2.2.1⟩).1⟩
  · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

/-- The filter forces `P⁺(w) ≤ 3v`: `ω_y(v) ≤ v(log(y/2v), 3v)`. -/
lemma omegaW_le_vSmooth {t : ℕ → ℝ} {v : ℝ} (hd : P.DecidedSmall t v) (y : ℝ) (hv : 0 < v) :
    P.omegaW t y v ≤ P.vSmooth (y / (2 * v)) (3 * v) := by
  unfold omegaW vSmooth
  rw [two_mul_div_two_mul hv]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter, mem_elems] at he ⊢
    obtain ⟨h0, h1, h2, h3⟩ := he
    exact ⟨h0, ((window_iff' hv e).mp ⟨h1, h2⟩).1, fun j hj => hd j ((h3 j hj).trans h2)⟩
  · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

/-- `v(ℓ, z)` is non-decreasing in `z`. -/
lemma vSmooth_mono {Y z z' : ℝ} (hz : z ≤ z') : P.vSmooth Y z ≤ P.vSmooth Y z' := by
  unfold vSmooth
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.1, fun j hj => (he.2.2 j hj).trans hz⟩
  · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- **Lemma 5.21(i)**: `ω_y(v) ≤ 1` (`≤ 1.2` in the paper), for `v > 0` and `y/v ≤ Z`. -/
theorem lemS_i (h : P.HBS X0m Z η1 η2 ε1) (t : ℕ → ℝ) {y v : ℝ} (hv : 0 < v)
    (hZ : y / v ≤ Z) : P.omegaW t y v ≤ 1 := by
  refine (omegaW_le_harmBlock t hv).trans (h.harmBlock_le_one ?_)
  rw [two_mul_div_two_mul hv]; exact hZ

/-- `u_y = log(y/2v)/log 3v`. -/
noncomputable abbrev uY (y v : ℝ) : ℝ := Real.log (y / (2 * v)) / Real.log (3 * v)

lemma exp_uY {y v : ℝ} (hy : 0 < y) (hv : 0 < v) (hL : 0 < Real.log (3 * v)) :
    Real.exp (uY y v * Real.log (3 * v)) = y / (2 * v) := by
  rw [uY, div_mul_cancel₀ _ hL.ne', Real.exp_log (by positivity)]

/-- **Lemma 5.21(ii)**, Dickman form: for `log 3v ≥ 100` and `1 ≤ u_y ≤ log 3v`,
`ω_y(v) ≤ C₀ ρ(u_y) e^{a_V}`, `a_V = a_V(log(y/2v), u_y)` of Lemma 5.3. -/
theorem lemS_ii_dickman (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100 ≤ Real.log (3 * v)) {y : ℝ} (hy : 0 < y)
    (hu1 : 1 ≤ uY y v) (hu2 : uY y v ≤ Real.log (3 * v)) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤
      BSaias.C0 * Dickman.rho (uY y v) *
        Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v)) := by
  have hL0 : 0 < Real.log (3 * v) := by linarith
  have h53 := h.lemma53 (3 * v) (uY y v) hL hu1 hu2 (by
    rw [exp_uY hy hv hL0, two_mul_div_two_mul hv]; exact hZ)
  rw [exp_uY hy hv hL0] at h53
  have e : uY y v * Real.log (3 * v) = Real.log (y / (2 * v)) := by
    rw [uY, div_mul_cancel₀ _ hL0.ne']
  rw [e] at h53
  exact (omegaW_le_vSmooth hd y hv).trans h53

/-- The exponent of (ii): `a_V(log(y/2v), u_y) ≤ 13 u_y log(u_y + 2)/log 3v`. -/
lemma aV_uY_le {y v : ℝ} (hL : 0 < Real.log (3 * v))
    (hu1 : 1 ≤ uY y v) :
    BSaias.aV (Real.log (y / (2 * v))) (uY y v) ≤
      13 * uY y v * Real.log (uY y v + 2) / Real.log (3 * v) := by
  have e : Real.log (y / (2 * v)) = uY y v * Real.log (3 * v) := by
    rw [uY, div_mul_cancel₀ _ hL.ne']
  unfold BSaias.aV
  rw [e]
  have hl : 0 ≤ Real.log (uY y v + 2) := Real.log_nonneg (by linarith)
  have hu0 : 0 < uY y v := by linarith
  rw [div_le_div_iff₀ (by positivity) hL]
  have : 4 * 3.2 * uY y v ^ 2 * Real.log (uY y v + 2) * Real.log (3 * v) =
      12.8 * uY y v * Real.log (uY y v + 2) * (uY y v * Real.log (3 * v)) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := mul_nonneg hu0.le hl
  nlinarith

end HBS

end BeurlingSystem

end
