module

public import RequestProject.BSCert.Z2Cells

/-!
# Region Z2: covering a range of `ℓ` by bands

`z2_range_sound` turns a successful walk over bands of ratio `1.05` (each band checked by
`bandOK`) into the real statement on the whole range of `ℓ`. The walks themselves are run, in
32 pieces, in the files `RequestProject/BSCert/Z2Chunks/*.lean`.
-/

@[expose] public section

namespace BSCert

namespace Z2

/-- The `r_low` table for region Z2 (`u ≤ Ū(10¹⁸) < 2.6·10⁵`). -/
def z2Table : Array ℚ := rlowTable 300000

/-- The property certified for a given `ℓ`: for every `2 ≤ u ≤ Ū(ℓ)`,
`r(u-1) > γ₁`, `r(u-1) > γ_max` and `S(ℓ, u) > 0`. -/
def Z2Prop (r : ℝ → ℝ) (ℓ : ℝ) : Prop := ∀ u : ℝ, 2 ≤ u → u ≤ Ubar ℓ → 0 < Z2Claim r ℓ u

theorem z2_range_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {a b : ℚ}
    (h : cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 a b = true) :
    ∀ ℓ : ℝ, (a : ℝ) ≤ ℓ → ℓ ≤ (b : ℝ) → Z2Prop r ℓ :=
  cover_sound (Z2Prop r) _ (fun _ _ hab _ h1 h2 u hu1 hu2 =>
    bandOK_sound hr (rlowTable_ok hr 300000) hab h1 h2 u hu1 hu2) 0 _ 1000 a b h

lemma glue {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ x, a ≤ x → x ≤ b → P x)
    (h2 : ∀ x, b ≤ x → x ≤ c → P x) : ∀ x, a ≤ x → x ≤ c → P x := by
  intro x hx1 hx2
  rcases le_total x b with h | h
  · exact h1 x hx1 h
  · exact h2 x h hx2

end Z2

end BSCert
