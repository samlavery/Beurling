module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 05: `ℓ ∈ [64870478000, 122322961000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk05 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 64870478000 122322961000 = true := by
  native_decide

end BSCert.Z2
