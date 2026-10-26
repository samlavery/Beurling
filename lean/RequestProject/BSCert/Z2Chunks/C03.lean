module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 03: `ℓ ∈ [19156432000, 34402199000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk03 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 19156432000 34402199000 = true := by
  native_decide

end BSCert.Z2
