module

public import RequestProject.Beurling.AbsorbedTargetError

/-!
# Lemma 6.27(a) from the pointwise sparsity of `A` (Lemma 6.26)

The paper: "(a) is Lemma 6.26". Lemma 6.26 bounds the number of elements of `A` in a window of
length `h(u) = u^{θ/2}`:

  `#(A ∩ [u, u + h(u)]) ≤ h(u) (log u)^{-4}`    (`u ≥ X₀`).

Here `localCountA A v w = #(A ∩ [v, w])`, and `absorbedDensity_le_of_localCount` derives the
density bound: since each `a ∈ A` with `u_a ≤ v ≤ a` has `a = u_a + u_a^b ≤ v + v^b`,
`ρ_A(v) = ∑_{u_a ≤ v ≤ a} v^{-b} ≤ #(A ∩ [v, v + v^b]) v^{-b}`. In particular
`ρ_A(v) ≤ (log v)^{-4}` (Lemma 6.27(a)) follows from Lemma 6.26 (`rhoA_le_of_lemma626`).
-/

@[expose] public section

open Set Finset

namespace Absorbed

open scoped Classical

/-- `#(A ∩ [v, w])`. -/
noncomputable def localCountA (A : Set ℕ) (v w : ℝ) : ℕ :=
  ((Finset.Icc ⌈v⌉₊ ⌊w⌋₊).filter (· ∈ A)).card

/-- **The density is bounded by the local count**: if `#(A ∩ [v, v + v^b]) ≤ v^b ε`, then
`ρ_A(v) ≤ ε`. -/
theorem absorbedDensity_le_of_localCount {b X₀ : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (hb : 0 < b)
    (hX : 0 < X₀) (hAu : ∀ a ∈ A, X₀ ≤ u a ∧ u a + u a ^ b = a) {v ε : ℝ} (hv : X₀ ≤ v)
    (hloc : (localCountA A v (v + v ^ b) : ℝ) ≤ v ^ b * ε) :
    absorbedDensity b A u v ≤ ε := by
  have hv0 : 0 < v := by linarith
  set S := (Finset.Icc ⌈v⌉₊ ⌊v + v ^ b⌋₊).filter (· ∈ A) with hS
  have hsupp : ∀ a ∉ S, absorbedBump b A u a v = 0 := by
    intro a ha
    unfold absorbedBump
    split_ifs with hA
    · apply Set.indicator_of_notMem
      rintro ⟨h1, h2⟩
      apply ha
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.ceil_le.mpr h2, Nat.le_floor ?_⟩, hA⟩
      have hU : 0 ≤ u a := by linarith [(hAu a hA).1]
      have e1 : u a ^ b ≤ v ^ b := Real.rpow_le_rpow hU h1 hb.le
      linarith [(hAu a hA).2]
    · rfl
  unfold absorbedDensity
  rw [tsum_eq_sum (s := S) (fun a ha => hsupp a ha)]
  have hle : ∀ a ∈ S, absorbedBump b A u a v ≤ v ^ (-b) := by
    intro a _
    unfold absorbedBump
    split_ifs
    · unfold Set.indicator
      split_ifs
      · exact le_rfl
      · exact (Real.rpow_pos_of_pos hv0 _).le
    · exact (Real.rpow_pos_of_pos hv0 _).le
  calc ∑ a ∈ S, absorbedBump b A u a v ≤ ∑ _a ∈ S, v ^ (-b) := Finset.sum_le_sum hle
    _ = (S.card : ℝ) * v ^ (-b) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (v ^ b * ε) * v ^ (-b) :=
        mul_le_mul_of_nonneg_right hloc (Real.rpow_pos_of_pos hv0 _).le
    _ = ε := by
        rw [Real.rpow_neg hv0.le]
        field_simp [(Real.rpow_pos_of_pos hv0 b).ne']

/-- **Lemma 6.27(a) from Lemma 6.26**: if `#(A ∩ [v, v + v^b]) ≤ v^b (log v)^{-4}` for every
`v ≥ X₀`, then `ρ_A(v) ≤ (log v)^{-4}` for every `v ≥ X₀`. -/
theorem rhoA_le_of_lemma626 {b X₀ : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (hb : 0 < b) (hX : 0 < X₀)
    (hAu : ∀ a ∈ A, X₀ ≤ u a ∧ u a + u a ^ b = a)
    (h626 : ∀ v ≥ X₀, (localCountA A v (v + v ^ b) : ℝ) ≤ v ^ b * Real.log v ^ (-4 : ℤ)) :
    ∀ v ≥ X₀, absorbedDensity b A u v ≤ Real.log v ^ (-4 : ℤ) := fun v hv =>
  absorbedDensity_le_of_localCount hb hX hAu hv (h626 v hv)

end Absorbed

end
