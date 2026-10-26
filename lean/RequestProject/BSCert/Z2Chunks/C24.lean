module

public import RequestProject.BSCert.Z2Cover
meta import RequestProject.BSCert.Z2Cover

/-! Region Z2, piece 24: `ℓ ∈ [7521242195353000, 14182423894872000]` (bands of ratio `1.05`). -/

@[expose] public section

namespace BSCert.Z2

theorem chunk24 :
    cover (bandOK z2Table) 0 (gstep (21 / 20)) 1000 7521242195353000 14182423894872000 = true := by
  native_decide

end BSCert.Z2
