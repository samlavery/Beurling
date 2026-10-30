module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 15 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi15 : cover phiCell 10 (astep (1 / 1000)) 1000 (62 / 100) (66 / 100) = true := by
  decide +kernel

end BSCert.Consts
