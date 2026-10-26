module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 17: `ℓ ∈ [102714381575000, 193683285522000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk17 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 102714381575000 193683285522000 = true := by
  native_decide

end BSCert.Z2
