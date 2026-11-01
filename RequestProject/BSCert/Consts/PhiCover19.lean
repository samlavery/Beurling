module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 19 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi19 : cover phiCell 10 (astep (1 / 1000)) 1000 (78 / 100) (82 / 100) = true := by
  decide +kernel

end BSCert.Consts
