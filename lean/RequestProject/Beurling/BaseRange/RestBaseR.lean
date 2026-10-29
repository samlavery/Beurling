module

public import RequestProject.Beurling.Model.MarginTop

/-!
# The field `hHux` of `BModel.RestBase` ((huxley), eq. (84))

`HuxleyFrom X₀` is the statement (84) about the rational primes from `X₀` on. It is not a fact
about the construction: it follows from the named hypothesis `Huxley84` (Heath-Brown's
short-interval theorem with the de la Vallée Poussin error term, §7.1; not in Mathlib) for
every `X₀` beyond a threshold. This file packages that:

* `restBase_of` : `RestBase θ X₀ ω b` from `HuxleyFrom X` and `X ≤ X₀`;
* `huxley_threshold` : from `Huxley84`, a threshold `X_H ≥ e^{10⁸}` with `RestBase θ X₀ ω b` for
  every `X₀ ≥ X_H` (and all `θ, ω, b`); also `BModel.ShortIntervalPNT` (`Huxley84` implies it).

Lemma 5.36(a) / Lemma 7.3(a) (`lemma_7_3_a`, `MAP_log_bounds`) and the counts
`count_ge`/`count_le` are consequences of `HuxleyFrom X₀` used downstream; they are not part
of this field.
-/

@[expose] public section

open Construction

namespace BaseRange

variable {θ : ℝ} {X₀ : ℕ}

/-- **The field `hHux`**: `RestBase θ X₀ ω b` from (84) from some `X ≤ X₀` on. -/
theorem restBase_of {X : ℝ} (h : HuxleyFrom X) (hX : X ≤ X₀) (ω : JitterΩ) (b : ℝ) :
    BModel.RestBase θ X₀ ω b :=
  ⟨huxleyFrom_mono hX h⟩

/-- **The threshold** `X_H` from the named hypothesis `Huxley84`: for `X₀ ≥ X_H`, `RestBase`
holds at every `θ, ω, b`. -/
theorem huxley_threshold (h : Huxley84) :
    ∃ XH : ℝ, Real.exp (10 ^ 8) ≤ XH ∧
      ∀ X₀ : ℕ, XH ≤ X₀ → ∀ (θ : ℝ) (ω : JitterΩ) (b : ℝ), BModel.RestBase θ X₀ ω b := by
  obtain ⟨X, hX⟩ := h
  refine ⟨max X (Real.exp (10 ^ 8)), le_max_right _ _, fun X₀ hX₀ θ ω b => ?_⟩
  exact restBase_of hX ((le_max_left _ _).trans hX₀) ω b

/-- `Huxley84` implies the hypothesis `BModel.ShortIntervalPNT` of the top level. -/
theorem shortIntervalPNT_of_huxley (h : Huxley84) : BModel.ShortIntervalPNT :=
  shortIntervalPNT_of_huxley84 h

end BaseRange
