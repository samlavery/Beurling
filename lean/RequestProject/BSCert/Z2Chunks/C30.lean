module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 30: `ℓ ∈ [306673537725054016, 550741612747123968]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk30 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 306673537725054016 550741612747123968 = true := by
  native_decide

end BSCert.Z2
