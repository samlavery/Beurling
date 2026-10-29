module

public import RequestProject.Beurling.Noise.MarginRecStep

/-!
# Proposition 5.38, Step 2: the exact form and the weights

The jitter-smoothed slot density (§5.1, "Jitter and slots") is
`ρ̃(y) = ∑_q box_{H(s_q)}(y - s_q)`, `box_h(x) = h⁻¹ 1[-h/2 ≤ x < h/2]`, over the decided primes
`q` with slots `s_q` (`rhoTilde`, for a finite family of slots). The slot measure is
`σ(A) = #{q : s_q ∈ A}` (`sigmaS`).

* `rhoTilde_sub` : **the exact form** (Step 2, first bullet): for `0 ≤ s`,
  `ρ̃(z+s) - ρ̃(z) = ∑_{s_q ∈ A₊} 1/H(s_q) - ∑_{s_q ∈ A₋} 1/H(s_q)`, with
  `A₊ = φ₋⁻¹((z, z+s])`, `A₋ = φ₊⁻¹((z, z+s])`, `φ±(x) = x ± H(x)/2` (the boxes are half-open);
* `exact_form_bound` : **the weights** (third bullet): if `|H(z)/H(s_q) - 1| ≤ c` on `A₊ ∪ A₋`,
  then `|H(z)(ρ̃(z+s) - ρ̃(z)) - (σ(A₊) - σ(A₋))| ≤ c (σ(A₊) + σ(A₋))`;
* `step2_exact_bullet` : with `c = 1.6 δ_z` and `σ(A±) ≤ 1.03 H(z)`, the bound `3.3 δ_z H(z)` in
  the form of the first conjunct of the bullets of `Margin.Rec.step2At_of`.

The inputs `|H(z)/H(x) - 1| ≤ 1.6 δ_z` on `A±` (regularity of `H`, and the position of `A±`
within `[z - 0.51H, z + 1.53H]`) and `σ(A±) ≤ 1.01|A±| + 1 ≤ 1.03H` (each continuous slot decides
at most one prime, slot starts `1 - 10⁻⁸` apart, §5.6) are construction facts and stay hypotheses.
-/

@[expose] public section

open Finset Real

namespace Margin.Exact

variable {ι : Type*} (Q : Finset ι) (sl : ι → ℝ) (H : ℝ → ℝ)

/-- The jitter-smoothed slot density
`ρ̃(y) = ∑_q H(s_q)⁻¹ 1[s_q - H(s_q)/2 ≤ y < s_q + H(s_q)/2]`. -/
noncomputable def rhoTilde (y : ℝ) : ℝ :=
  open scoped Classical in
  ∑ q ∈ Q, if sl q - H (sl q) / 2 ≤ y ∧ y < sl q + H (sl q) / 2 then (H (sl q))⁻¹ else 0

/-- `A₊ = φ₋⁻¹((z, z+s])`, `φ₋(x) = x - H(x)/2`. -/
def Aplus (z s : ℝ) : Set ℝ := {x | z < x - H x / 2 ∧ x - H x / 2 ≤ z + s}

/-- `A₋ = φ₊⁻¹((z, z+s])`, `φ₊(x) = x + H(x)/2`. -/
def Aminus (z s : ℝ) : Set ℝ := {x | z < x + H x / 2 ∧ x + H x / 2 ≤ z + s}

/-- The slot measure `σ(A) = #{q : s_q ∈ A}`. -/
noncomputable def sigmaS (A : Set ℝ) : ℝ :=
  open scoped Classical in
  ((Q.filter fun q => sl q ∈ A).card : ℝ)

/-- One box: `1[z+s ∈ [a,b)] - 1[z ∈ [a,b)] = 1[a ∈ (z, z+s]] - 1[b ∈ (z, z+s]]` for `a ≤ b`,
`0 ≤ s`. -/
lemma box_diff {a b z s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    ((if a ≤ z + s ∧ z + s < b then 1 else 0 : ℝ) - if a ≤ z ∧ z < b then 1 else 0) =
      (if z < a ∧ a ≤ z + s then 1 else 0 : ℝ) - if z < b ∧ b ≤ z + s then 1 else 0 := by
  by_cases h1 : a ≤ z <;> by_cases h2 : z < b <;> by_cases h3 : a ≤ z + s <;>
    by_cases h4 : z + s < b <;> by_cases h5 : z < a <;> by_cases h6 : b ≤ z + s <;>
    simp only [h1, h2, h3, h4, h5, h6, and_self, and_true, and_false,
      if_true, if_false] <;>
    first | (exfalso; push_neg at *; linarith) | norm_num

variable {Q sl H}

/-- **The exact form** of Step 2: `ρ̃(z+s) - ρ̃(z) = ∫_{A₊} dσ/H - ∫_{A₋} dσ/H`. -/
theorem rhoTilde_sub (hH : ∀ q ∈ Q, 0 ≤ H (sl q)) {z s : ℝ} (hs : 0 ≤ s) :
    rhoTilde Q sl H (z + s) - rhoTilde Q sl H z =
      (open scoped Classical in
        ∑ q ∈ Q.filter (fun q => sl q ∈ Aplus H z s), (H (sl q))⁻¹) -
      (open scoped Classical in
        ∑ q ∈ Q.filter (fun q => sl q ∈ Aminus H z s), (H (sl q))⁻¹) := by
  classical
  unfold rhoTilde
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hab : sl q - H (sl q) / 2 ≤ sl q + H (sl q) / 2 := by linarith [hH q hq]
  have h := box_diff (z := z) hab hs
  simp only [Aplus, Aminus, Set.mem_setOf_eq]
  have h' := congrArg (fun r => (H (sl q))⁻¹ * r) h
  simp only [mul_sub, mul_ite, mul_one, mul_zero] at h'
  convert h' using 3

/-- **The weights** of Step 2: with `|H(z)/H(s_q) - 1| ≤ c` on `A₊ ∪ A₋`,
`|H(z)(ρ̃(z+s) - ρ̃(z)) - (σ(A₊) - σ(A₋))| ≤ c (σ(A₊) + σ(A₋))`. -/
theorem exact_form_bound (hH : ∀ q ∈ Q, 0 < H (sl q)) {z s c : ℝ} (hs : 0 ≤ s)
    (hw : ∀ q ∈ Q, (sl q ∈ Aplus H z s ∨ sl q ∈ Aminus H z s) →
      |H z / H (sl q) - 1| ≤ c) :
    |H z * (rhoTilde Q sl H (z + s) - rhoTilde Q sl H z) -
        (sigmaS Q sl (Aplus H z s) - sigmaS Q sl (Aminus H z s))| ≤
      c * (sigmaS Q sl (Aplus H z s) + sigmaS Q sl (Aminus H z s)) := by
  classical
  rw [rhoTilde_sub (fun q hq => (hH q hq).le) hs]
  unfold sigmaS
  set Fp := Q.filter (fun q => sl q ∈ Aplus H z s)
  set Fm := Q.filter (fun q => sl q ∈ Aminus H z s)
  have ep : H z * ∑ q ∈ Fp, (H (sl q))⁻¹ - (Fp.card : ℝ) = ∑ q ∈ Fp, (H z / H (sl q) - 1) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib, Finset.card_eq_sum_ones]
    push_cast
    rfl
  have em : H z * ∑ q ∈ Fm, (H (sl q))⁻¹ - (Fm.card : ℝ) = ∑ q ∈ Fm, (H z / H (sl q) - 1) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib, Finset.card_eq_sum_ones]
    push_cast
    rfl
  have hp : |∑ q ∈ Fp, (H z / H (sl q) - 1)| ≤ c * Fp.card := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.card_eq_sum_ones]; push_cast; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    rw [mul_one]; exact hw q hq1 (Or.inl hq2)
  have hm : |∑ q ∈ Fm, (H z / H (sl q) - 1)| ≤ c * Fm.card := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.card_eq_sum_ones]; push_cast; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    rw [mul_one]; exact hw q hq1 (Or.inr hq2)
  have e : H z * (∑ q ∈ Fp, (H (sl q))⁻¹ - ∑ q ∈ Fm, (H (sl q))⁻¹) -
      ((Fp.card : ℝ) - Fm.card) =
      (H z * ∑ q ∈ Fp, (H (sl q))⁻¹ - Fp.card) - (H z * ∑ q ∈ Fm, (H (sl q))⁻¹ - Fm.card) := by
    ring
  rw [e, ep, em]
  calc |∑ q ∈ Fp, (H z / H (sl q) - 1) - ∑ q ∈ Fm, (H z / H (sl q) - 1)|
      ≤ |∑ q ∈ Fp, (H z / H (sl q) - 1)| + |∑ q ∈ Fm, (H z / H (sl q) - 1)| := abs_sub _ _
    _ ≤ c * Fp.card + c * Fm.card := add_le_add hp hm
    _ = c * ((Fp.card : ℝ) + Fm.card) := by ring

/-- **Step 2, exact form with weights** (the first bullet of `Margin.Rec.step2At_of`):
with `|H(z)/H(x) - 1| ≤ 1.6 δ_z` on `A±` and `σ(A±) ≤ 1.03 H(z)`,
`|H(z)(ρ̃(z+s) - ρ̃(z)) - (σ(A₊) - σ(A₋))| ≤ 3.3 δ_z H(z)`. -/
theorem step2_exact_bullet (hH : ∀ q ∈ Q, 0 < H (sl q)) {z s δz : ℝ} (hs : 0 ≤ s)
    (hδ : 0 ≤ δz)
    (hw : ∀ q ∈ Q, (sl q ∈ Aplus H z s ∨ sl q ∈ Aminus H z s) →
      |H z / H (sl q) - 1| ≤ 1.6 * δz)
    (hcp : sigmaS Q sl (Aplus H z s) ≤ 1.03 * H z)
    (hcm : sigmaS Q sl (Aminus H z s) ≤ 1.03 * H z) :
    |H z * (rhoTilde Q sl H (z + s) - rhoTilde Q sl H z) -
        (sigmaS Q sl (Aplus H z s) - sigmaS Q sl (Aminus H z s))| ≤ 3.3 * δz * H z := by
  refine (exact_form_bound hH hs hw).trans ?_
  have h := add_le_add hcp hcm
  have h2 : 1.6 * δz * (sigmaS Q sl (Aplus H z s) + sigmaS Q sl (Aminus H z s)) ≤
      1.6 * δz * (1.03 * H z + 1.03 * H z) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have hHz : 0 ≤ H z := by
    have := le_trans (by unfold sigmaS; positivity) hcp
    linarith
  nlinarith

end Margin.Exact

end
