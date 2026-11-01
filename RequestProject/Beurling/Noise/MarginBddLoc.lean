module

public import RequestProject.Beurling.Noise.MarginRecStep

/-!
# Local boundedness suffices for the variation envelope

`Margin.Rec.le_vSup` asks for a global bound on `m`. The envelope `vSup H m x` only reads `m` on
the window `[x - 1.01 H(x), x + 1.01 H(x)]`, so a bound there suffices (`le_vSup_loc`), and
`step2At_of` only uses the envelope at points `x ∈ [z - H(z)/2, z + 0.51 H(z)]`
(`step2At_of_loc`).
-/

@[expose] public section

open Set MeasureTheory

namespace Margin.Rec

/-- `|m(x+h) - m(x)| ≤ vSup H m x` for `|h| ≤ 1.01 H(x)`, from a bound on the window only. -/
lemma le_vSup_loc {H m : ℝ → ℝ} {x hh : ℝ}
    (hbdd : ∃ C, ∀ y, |y - x| ≤ 1.01 * H x → |m y| ≤ C)
    (hh1 : |hh| ≤ 1.01 * H x) : |m (x + hh) - m x| ≤ vSup H m x := by
  obtain ⟨C, hC⟩ := hbdd
  have hx0 : |x - x| ≤ 1.01 * H x := by
    rw [sub_self, abs_zero]; exact (abs_nonneg _).trans hh1
  refine le_csSup (show BddAbove _ from ⟨2 * C, ?_⟩) ⟨hh, abs_le.mp hh1, rfl⟩
  rintro _ ⟨k, hk, rfl⟩
  have hk' : |x + k - x| ≤ 1.01 * H x := by
    rw [add_sub_cancel_left]; exact abs_le.mpr hk
  have := abs_sub (m (x + k)) (m x)
  linarith [hC (x + k) hk', hC x hx0]

/-- `step2At_of` with the envelope bound required only on the lower strip of `z`. -/
theorem step2At_of_loc {H m ρ v err : ℝ → ℝ} {z : ℝ} (hH : 0 < H z)
    (hv : ∀ x ∈ Icc (z - H z / 2) (z + 0.51 * H z), ∀ hh, |hh| ≤ 1.01 * H x →
      |m (x + hh) - m x| ≤ v x)
    (hHx : ∀ x ∈ Icc (z - H z / 2) (z + 0.51 * H z), H z ≤ 1.01 * H x)
    (hmi : ∀ s, 0 ≤ s → s ≤ 1.01 * H z →
      IntervalIntegrable m volume (z - H z / 2) (z + H z / 2 + s))
    (hbul : ∀ s, 0 ≤ s → s ≤ 1.01 * H z → ∃ ε δz mst σp σm Ep Em JAp JAm : ℝ,
      |H z * (ρ (z + s) - ρ z) - (σp - σm)| ≤ 3.3 * δz * H z ∧
      σp = JAp + Ep ∧ σm = JAm + Em ∧ |Ep| ≤ ε ∧ |Em| ≤ ε ∧
      |JAp - ∫ r in (z + H z / 2)..(z + H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst ∧
      |JAm - ∫ r in (z - H z / 2)..(z - H z / 2 + s), m r| ≤ 1.05 * δz * H z * mst ∧
      2 * ε / H z + (3.3 + 2.1 * mst) * δz ≤ err z) :
    Step2At H ρ v err z := by
  intro s hs0 hs b hb
  obtain ⟨ε, δz, mst, σp, σm, Ep, Em, JAp, JAm, hex, hσp, hσm, hEp, hEm, hJp, hJm, herr⟩ :=
    hbul s hs0 hs
  have hshift : ∀ x ∈ Icc (z - H z / 2) (z - H z / 2 + s), |m (x + H z) - m x| ≤ b := by
    intro x hx
    have hx' : x ∈ Icc (z - H z / 2) (z + 0.51 * H z) := ⟨hx.1, by linarith [hx.2]⟩
    have h1 := hv x hx' (H z) (by rw [abs_of_pos hH]; exact hHx x hx')
    exact h1.trans (hb x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have := step2_assembly hH hs0 hex hσp hσm hEp hEm hJp hJm (hmi s hs0 hs) hshift
  linarith

end Margin.Rec

end
