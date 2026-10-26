module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 04: `ℓ ∈ [34402199000, 64870478000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk04 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 34402199000 64870478000 = true := by
  native_decide

end BSCert.Z2
