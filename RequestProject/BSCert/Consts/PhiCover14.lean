module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 14 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi14 : cover phiCell 10 (astep (1 / 1000)) 1000 (58 / 100) (62 / 100) = true := by
  decide +kernel

end BSCert.Consts
