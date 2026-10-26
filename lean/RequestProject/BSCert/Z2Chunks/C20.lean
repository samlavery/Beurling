module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 20: `ℓ ∈ [655880350897000, 1177866877271000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk20 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 655880350897000 1177866877271000 = true := by
  native_decide

end BSCert.Z2
