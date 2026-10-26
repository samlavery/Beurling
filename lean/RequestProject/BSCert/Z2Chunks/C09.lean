module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 09: `ℓ ∈ [743895702000, 1402726293000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk09 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 743895702000 1402726293000 = true := by
  native_decide

end BSCert.Z2
