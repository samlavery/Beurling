module

public import RequestProject.Beurling.AbsorbedTargetError

/-!
# Lemma 6.27(a) from the pointwise sparsity of `A` (Lemma 6.26)

The paper: "(a) is Lemma 6.26". Lemma 6.26 bounds the number of elements of `A` in a window of
length `h(u)` (the absorption window `winH X₀`):

  `#(A ∩ [u, u + h(u)]) ≤ h(u) (log u)^{-4}`    (`u ≥ X₀`).

Here `localCountA A v w = #(A ∩ [v, w])`, and `absorbedDensity_le_of_localCount` derives the
density bound: since each `a ∈ A` with `u_a ≤ v ≤ a` has `a = u_a + h(u_a) ≤ v + h(v)`,
`ρ_A(v) = ∑_{u_a ≤ v ≤ a} 1/h(v) ≤ #(A ∩ [v, v + h(v)])/h(v)`. In particular
`ρ_A(v) ≤ (log v)^{-4}` (Lemma 6.27(a)) follows from Lemma 6.26 (`rhoA_le_of_lemma626`).
-/

@[expose] public section

open Set Finset

namespace Absorbed

open scoped Classical

/-- `#(A ∩ [v, w])`. -/
noncomputable def localCountA (A : Set ℝ) (v w : ℝ) : ℕ :=
  (A ∩ Set.Icc v w).ncard

/-- **The density is bounded by the local count**: if `#(A ∩ [v, v + h(v)]) ≤ h(v) ε`, then
`ρ_A(v) ≤ ε`. -/
theorem absorbedDensity_le_of_localCount {w : ℝ → ℝ} {X₀ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}
    (hw : IsWin w) (hX : 0 < X₀) (hAu : ∀ a ∈ A, X₀ ≤ u a ∧ u a + w (u a) = a)
    (hAfin : LocFin A) {v ε : ℝ} (hv : X₀ ≤ v)
    (hloc : (localCountA A v (v + w v) : ℝ) ≤ w v * ε) :
    absorbedDensity w A u v ≤ ε := by
  have hv0 : 0 < v := by linarith
  have hwv := hw.pos v hv0
  set S := (hAfin.finite_Icc v (v + w v)).toFinset with hS
  have hcard : (S.card : ℝ) = localCountA A v (v + w v) := by
    rw [hS, ← Set.ncard_eq_toFinset_card _ (hAfin.finite_Icc v (v + w v))]; rfl
  have hsupp : ∀ a ∉ S, absorbedBump w A u a v = 0 := by
    intro a ha
    unfold absorbedBump
    split_ifs with hA
    · apply Set.indicator_of_notMem
      rintro ⟨h1, h2⟩
      apply ha
      rw [hS, Set.Finite.mem_toFinset]
      refine ⟨hA, h2, ?_⟩
      have hU : 0 < u a := by linarith [(hAu a hA).1]
      have e1 : w (u a) ≤ w v := hw.mono' hU h1
      linarith [(hAu a hA).2]
    · rfl
  unfold absorbedDensity
  rw [tsum_eq_sum (s := S) (fun a ha => hsupp a ha)]
  have hle : ∀ a ∈ S, absorbedBump w A u a v ≤ (w v)⁻¹ := by
    intro a _
    unfold absorbedBump
    split_ifs
    · unfold Set.indicator
      split_ifs
      · exact le_rfl
      · exact (inv_pos.mpr hwv).le
    · exact (inv_pos.mpr hwv).le
  calc ∑ a ∈ S, absorbedBump w A u a v ≤ ∑ _a ∈ S, (w v)⁻¹ := Finset.sum_le_sum hle
    _ = (S.card : ℝ) * (w v)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (w v * ε) * (w v)⁻¹ :=
        mul_le_mul_of_nonneg_right (hcard ▸ hloc) (inv_pos.mpr hwv).le
    _ = ε := by field_simp

/-- **Lemma 6.27(a) from Lemma 6.26**: if `#(A ∩ [v, v + h(v)]) ≤ h(v) (log v)^{-4}` for every
`v ≥ X₀`, then `ρ_A(v) ≤ (log v)^{-4}` for every `v ≥ X₀`. -/
theorem rhoA_le_of_lemma626 {w : ℝ → ℝ} {X₀ : ℝ} {A : Set ℝ} {u : ℝ → ℝ} (hw : IsWin w)
    (hX : 0 < X₀) (hAu : ∀ a ∈ A, X₀ ≤ u a ∧ u a + w (u a) = a) (hAfin : LocFin A)
    (h626 : ∀ v ≥ X₀, (localCountA A v (v + w v) : ℝ) ≤ w v * Real.log v ^ (-4 : ℤ)) :
    ∀ v ≥ X₀, absorbedDensity w A u v ≤ Real.log v ^ (-4 : ℤ) := fun v hv =>
  absorbedDensity_le_of_localCount hw hX hAu hAfin hv (h626 v hv)

end Absorbed

end
