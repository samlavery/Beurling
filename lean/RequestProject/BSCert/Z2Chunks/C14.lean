module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 14: `ℓ ∈ [16085623190000, 30331841572000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk14 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 16085623190000 30331841572000 = true := by
  native_decide

end BSCert.Z2
