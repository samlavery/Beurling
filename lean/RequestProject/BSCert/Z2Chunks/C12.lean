module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 12: `ℓ ∈ [4750129113000, 8957076887000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk12 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 4750129113000 8957076887000 = true := by
  native_decide

end BSCert.Z2
