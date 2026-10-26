module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 01: `ℓ ∈ [5656947000, 10159065000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk01 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 5656947000 10159065000 = true := by
  native_decide

end BSCert.Z2
