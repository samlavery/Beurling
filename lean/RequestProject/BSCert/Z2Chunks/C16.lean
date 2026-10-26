module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 16: `ℓ ∈ [57195211046000, 102714381575000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk16 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 57195211046000 102714381575000 = true := by
  native_decide

end BSCert.Z2
