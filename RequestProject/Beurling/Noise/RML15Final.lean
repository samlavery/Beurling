module

public import RequestProject.Beurling.Model.MarginFinal
public import RequestProject.Beurling.Noise.RML15Eta

/-!
# (Former refutation of `RestMarginR.ho`, obsolete since `oVc` is the oscillation of `T_c`)

`BModel.RML15.restMarginR_isEmpty`: under (huxley) and the standing facts, `RestMarginR θ X₀ ω b`
is empty for every `b ≥ X₀`. Its field `ho` would give `log X₀ · o_V(X₀) ≤ so`, while `hη`
and `hsize` force `so ≤ 0.0013`; but `o_V` (`BModel.oVc`) oscillates `T' = T_c + j₀ 1_{[X₀,∞)}`,
so `log X₀ · o_V(X₀) ≥ log X₀ · j₀ ≥ 0.98` (`ho_false`). The paper's `o_t` is the oscillation of
`T_c`; the jump is the separate base term `j₀ 1[|t - X₀| ≤ 1.01 H(t)]` (04g Steps 3, 5).
-/

@[expose] public section

open Real BModel

namespace BModel.RML15

variable {θ : ℝ} {X₀ : ℕ}

end BModel.RML15

end
