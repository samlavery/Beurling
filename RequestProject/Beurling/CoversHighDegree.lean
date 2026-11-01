module

public import RequestProject.Beurling.Covers

/-!
# Lemma 6.21(i): the high-degree completion

The last sentence of Lemma 6.21(i): if the elements of `S'` of degree at most `k` number at
most `Q`, the completion of a minimum cover `C` to a basis `B'` can be chosen with every row of
`R = B' \ C` of degree at least `k + 1` (Lemma 6.14(iii) and Steinitz exchange).

* `Covers.exists_basis_extending_within`: Steinitz exchange — an independent `C ⊆ S` extends to
  a basis of `S` using only elements of a set `H ⊆ S` with `span (C ∪ H) ⊇ span S`.
* `Covers.extras_drop_out_high_degree`: Lemma 6.21(i) in full, for an `S` whose elements of
  degree `≥ k + 1` span `S`.
* `Covers.extras_drop_out_heavy`: the same for `S' = S ∩ V`, `V` a heavy subspace of least
  dimension (Lemma 6.14), under the paper's hypothesis that at most `Q` elements of `S ∩ V` have
  degree `≤ k`.
-/

@[expose] public section

open Finset

namespace Covers

variable {m : ℕ}

/-- Steinitz exchange: if `C ⊆ S` is independent and `H ⊆ S` is such that `C ∪ H` spans `S`, then
`C` extends to a basis `B` of `S` with `B \ C ⊆ H`. -/
theorem exists_basis_extending_within {S C H : Finset (Fin m → ℕ)} (hCS : C ⊆ S) (hHS : H ⊆ S)
    (hli : LinearIndepOn ℚ vq (C : Set (Fin m → ℕ)))
    (hspan : Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) ≤
      Submodule.span ℚ (vq '' ((C ∪ H : Finset _) : Set (Fin m → ℕ)))) :
    ∃ B, IsBasisOf S B ∧ C ⊆ B ∧ B \ C ⊆ H := by
  classical
  obtain ⟨b, hbS, hCb, hspanb, hlib⟩ :=
    exists_linearIndepOn_extension hli
      (Finset.coe_subset.mpr (Finset.subset_union_left (s₂ := H)))
  have hcoe : (((C ∪ H).filter (fun v => v ∈ b) : Finset _) : Set (Fin m → ℕ)) = b := by
    ext v
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hbS h, h⟩⟩
  refine ⟨(C ∪ H).filter (fun v => v ∈ b), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v hv
    have := (Finset.mem_filter.mp hv).1
    rcases Finset.mem_union.mp this with h | h
    · exact hCS h
    · exact hHS h
  · rw [hcoe]; exact hlib
  · rw [hcoe]
    refine hspan.trans ?_
    rw [Submodule.span_le]
    exact hspanb
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hv, hCb hv⟩
  · intro v hv
    obtain ⟨hvB, hvC⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hvB).1 with h | h
    · exact absurd h hvC
    · exact h

/-- **Lemma 6.21(i)**, with the high-degree completion. Let `S` have no zero vector, all degrees
`≤ D`, and `Cap(S) ≥ c > e (r(D+1))^{2j+1}`, `r = rank S`. Suppose the elements of `S` of degree
at least `k + 1` span `S`. Then `κ(S) ≤ r - 1 - j`, and a minimum cover `C` extends to a basis
`B ⊆ S` (a cover of `S`, by Lemma 6.15(a)) such that the rows `R = B \ C` number at least `1 + j`
and every row of `R` has degree at least `k + 1`. -/
theorem extras_drop_out_high_degree {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j k : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) {c : ℝ}
    (hc : Real.exp 1 * ((rank S : ℝ) * (D + 1)) ^ (2 * j + 1) < c) (hcap : c ≤ cap S)
    (hhigh : Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) ≤
      Submodule.span ℚ (vq '' ((S.filter (fun y => k + 1 ≤ deg y) : Finset _) :
        Set (Fin m → ℕ)))) :
    kappa S + j + 1 ≤ rank S ∧
      ∃ C B, IsCover S C ∧ C.card = kappa S ∧ IsBasisOf S B ∧ C ⊆ B ∧
        j + 1 ≤ (B \ C).card ∧ ∀ y ∈ B \ C, k + 1 ≤ deg y := by
  classical
  have hκ := (extras_drop_out h0 hD hc hcap).1
  refine ⟨hκ, ?_⟩
  obtain ⟨C, hC, hCcard⟩ := exists_min_cover S
  have hli := minimal_cover_linearIndependent hC (min_cover_minimal hCcard)
  set H := S.filter (fun y => k + 1 ≤ deg y)
  have hsp : Submodule.span ℚ (vq '' (S : Set (Fin m → ℕ))) ≤
      Submodule.span ℚ (vq '' ((C ∪ H : Finset _) : Set (Fin m → ℕ))) :=
    hhigh.trans (Submodule.span_mono (Set.image_mono (by
      intro v hv; exact Finset.mem_coe.mpr (Finset.mem_union_right _ hv))))
  obtain ⟨B, hB, hCB, hBH⟩ :=
    exists_basis_extending_within hC.1 (Finset.filter_subset _ _) hli hsp
  refine ⟨C, B, hC, hCcard, hB, hCB, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hCB, ← rank_eq_card hB, hCcard]
    omega
  · intro y hy
    exact (Finset.mem_filter.mp (hBH hy)).2

open scoped Classical in
/-- **Lemma 6.21(i)** in the paper's setting: `S' = S ∩ V`, where `V` is a heavy subspace of
least dimension (Lemma 6.14, with `Q ≥ 0`, `rank S < r₀` and `|S| ≥ r₀ + φ(r₀)`). Suppose `0 ∉ S`,
every element of `S` has degree `≤ D`, and `c > e (r(D+1))^{2j+1}` with `r = dim V`. If at most `Q`
elements of `S ∩ V` have degree `≤ k`, then `κ(S ∩ V) ≤ r - 1 - j`, and a minimum cover `C` of
`S ∩ V` extends to a basis `B ⊆ S ∩ V` with at least `1 + j` rows outside `C`, every one of degree
at least `k + 1`. -/
theorem extras_drop_out_heavy {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {D j k : ℕ}
    (hD : ∀ v ∈ S, deg v ≤ D) {c Q : ℝ} (hQ : 0 ≤ Q) {r₀ : ℕ}
    (hrank : rank S < r₀) (hcard : (r₀ : ℝ) + phi c Q r₀ ≤ S.card) :
    ∃ V : Submodule ℚ (Fin m → ℚ), ElemSpanned S V ∧ Heavy c Q S V ∧
      (∀ W, ElemSpanned S W → Heavy c Q S W → Module.finrank ℚ V ≤ Module.finrank ℚ W) ∧
      rank (inter S V) = Module.finrank ℚ V ∧
      (Real.exp 1 * ((Module.finrank ℚ V : ℝ) * (D + 1)) ^ (2 * j + 1) < c →
        (((inter S V).filter (fun y => deg y ≤ k)).card : ℝ) ≤ Q →
        kappa (inter S V) + j + 1 ≤ Module.finrank ℚ V ∧
          ∃ C B, IsCover (inter S V) C ∧ C.card = kappa (inter S V) ∧
            IsBasisOf (inter S V) B ∧ C ⊆ B ∧
            j + 1 ≤ (B \ C).card ∧ ∀ y ∈ B \ C, k + 1 ≤ deg y) := by
  obtain ⟨V, hVes, hVh, hmin, ⟨hcapV, hcV⟩, -, hiii⟩ := heavy_subspace hQ hrank hcard
  have hsub : inter S V ⊆ S := Finset.filter_subset _ _
  have hsp : Submodule.span ℚ (vq '' ((inter S V : Finset _) : Set (Fin m → ℕ))) = V := by
    obtain ⟨T, hTS, rfl⟩ := hVes
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact (Finset.mem_filter.mp hy).2
    · apply Submodule.span_mono
      apply Set.image_mono
      intro t ht
      exact Finset.mem_filter.mpr ⟨hTS ht, Submodule.subset_span ⟨t, ht, rfl⟩⟩
  have hrk : rank (inter S V) = Module.finrank ℚ V := by unfold rank; rw [hsp]
  refine ⟨V, hVes, hVh, hmin, hrk, fun hc hlow => ?_⟩
  have hcap' : c ≤ (cap (inter S V) : ℝ) := hcV.trans hcapV
  have hc' : Real.exp 1 * ((rank (inter S V) : ℝ) * (D + 1)) ^ (2 * j + 1) < c := by
    rw [hrk]; exact hc
  have hhigh : Submodule.span ℚ (vq '' ((inter S V : Finset _) : Set (Fin m → ℕ))) ≤
      Submodule.span ℚ (vq '' (((inter S V).filter (fun y => k + 1 ≤ deg y) : Finset _) :
        Set (Fin m → ℕ))) := by
    rw [hsp, hiii k hlow]
  have := extras_drop_out_high_degree (fun h => h0 (hsub h)) (fun v hv => hD v (hsub hv))
    hc' hcap' hhigh
  rw [hrk] at this
  exact this

end Covers
