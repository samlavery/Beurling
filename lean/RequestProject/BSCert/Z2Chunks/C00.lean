module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 00: `ℓ ∈ [3000000000, 5656947000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk00 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 3000000000 5656947000 = true := by
  native_decide

end BSCert.Z2
