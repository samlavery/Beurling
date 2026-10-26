module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 18: `ℓ ∈ [193683285522000, 347827353549000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk18 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 193683285522000 347827353549000 = true := by
  native_decide

end BSCert.Z2
