module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 06: `ℓ ∈ [122322961000, 219674463000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk06 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 122322961000 219674463000 = true := by
  native_decide

end BSCert.Z2
