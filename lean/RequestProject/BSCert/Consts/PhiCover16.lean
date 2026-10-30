module

public import RequestProject.BSCert.Consts.PhiCell

/-! Kernel-checked piece 16 of the cover of `phi_bounds.py` (`PhiCert`). -/

@[expose] public section

namespace BSCert.Consts

lemma check_phi16 : cover phiCell 10 (astep (1 / 1000)) 1000 (66 / 100) (70 / 100) = true := by
  decide +kernel

end BSCert.Consts
