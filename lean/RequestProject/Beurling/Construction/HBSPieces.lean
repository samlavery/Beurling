module

public import RequestProject.Beurling.Construction.RigidFine

/-!
# Local versions of the absorbed-part bound and of Lemma 6.26, and other pieces for (HBS)

* `Absorbed.absorbed_target_error_loc`, `Absorbed.absorbed_target_error_cap_loc` (now in
  `AbsorbedTargetError`): Lemma 3.4 (absorbed part) at a height `x`, using the density bound
  only on `[X₀, x]`.
-/

@[expose] public section

open MeasureTheory Set Real Finset

namespace Absorbed

open scoped Classical

-- `absorbed_target_error_loc` and `absorbed_target_error_cap_loc` are proved in
-- `AbsorbedTargetError` (for a general window `h`).

end Absorbed

end
