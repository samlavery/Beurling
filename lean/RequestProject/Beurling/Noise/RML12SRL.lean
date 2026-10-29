module

public import RequestProject.Beurling.Noise.RML9XBBase
public import RequestProject.Beurling.Queue6.ShortRecipQ

/-!
# `Queue6.ShortRecipLow` is `KR.RML9.ShortRecipLow`

The two statements of Lemma 5.29 restricted to `M ≤ Y/X₀` are the same proposition
(`shortRecipLow_iff`), so `Queue6.shortRecipLow_b` supplies the `hSR` inputs of `KR.RML9`,
`KR.RML10.WinAt`, `KR.RML12.HjAtM` and `BModel.RML12.HjAtR`.
-/

@[expose] public section

namespace KR.RML9

lemma shortRecipLow_iff (P : BeurlingSystem) (X₀ : ℕ) (Y : ℝ) :
    Queue6.ShortRecipLow P X₀ Y ↔ ShortRecipLow P X₀ Y := Iff.rfl

end KR.RML9

end
