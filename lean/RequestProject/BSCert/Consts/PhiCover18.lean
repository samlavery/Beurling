module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 18 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi18 : cover phiCell 10 (astep (1 / 1000)) 1000 (74 / 100) (78 / 100) = true := by
  decide +kernel

end BSCert.Consts
