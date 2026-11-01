module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 0 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg0 : chainBound cb2 ((pts.drop 0).take 21) = some (4918544413327869749177029 / 48038347986889265381376) := by decide +kernel

end BSCert.Consts
