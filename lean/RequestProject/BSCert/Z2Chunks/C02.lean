module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 02: `ℓ ∈ [10159065000, 19156432000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk02 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 10159065000 19156432000 = true := by
  native_decide

end BSCert.Z2
