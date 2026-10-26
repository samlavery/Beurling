module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 25: `ℓ ∈ [14182423894872000, 25469595669933000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk25 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 14182423894872000 25469595669933000 = true := by
  native_decide

end BSCert.Z2
