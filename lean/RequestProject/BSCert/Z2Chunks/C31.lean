module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 31: `ℓ ∈ [550741612747123968, 1000000000000000000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk31 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 550741612747123968 1000000000000000000 = true := by
  native_decide

end BSCert.Z2
