module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 4 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi4 : cover phiCell 10 (astep (1 / 1000)) 1000 (18 / 100) (22 / 100) = true := by
  decide +kernel

end BSCert.Consts
