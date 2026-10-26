module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 26: `ℓ ∈ [25469595669933000, 48026721230329000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk26 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 25469595669933000 48026721230329000 = true := by
  native_decide

end BSCert.Z2
