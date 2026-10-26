module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 07: `ℓ ∈ [219674463000, 414228962000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk07 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 219674463000 414228962000 = true := by
  native_decide

end BSCert.Z2
