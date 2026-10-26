module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 29: `ℓ ∈ [162635524733520992, 306673537725054016]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk29 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 162635524733520992 306673537725054016 = true := by
  native_decide

end BSCert.Z2
