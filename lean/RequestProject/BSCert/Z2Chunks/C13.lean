module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 13: `ℓ ∈ [8957076887000, 16085623190000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk13 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 8957076887000 16085623190000 = true := by
  native_decide

end BSCert.Z2
