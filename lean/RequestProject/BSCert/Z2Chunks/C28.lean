module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 28: `ℓ ∈ [90561545696566000, 162635524733520992]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk28 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 90561545696566000 162635524733520992 = true := by
  native_decide

end BSCert.Z2
