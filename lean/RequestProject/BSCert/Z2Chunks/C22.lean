module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 22: `ℓ ∈ [2221043666898000, 4188109085548000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk22 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 2221043666898000 4188109085548000 = true := by
  native_decide

end BSCert.Z2
