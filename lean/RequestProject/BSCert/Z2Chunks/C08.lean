module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 08: `ℓ ∈ [414228962000, 743895702000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk08 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 414228962000 743895702000 = true := by
  native_decide

end BSCert.Z2
