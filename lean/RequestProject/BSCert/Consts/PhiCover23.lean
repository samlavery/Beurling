module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 23 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi23 : cover phiCell 10 (astep (1 / 1000)) 1000 (94 / 100) (98 / 100) = true := by
  decide +kernel

end BSCert.Consts
