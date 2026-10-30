module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 0 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg0 : chainBound cb3 ((pts.drop 0).take 21) = some (131380175489273983720590449 / 2951476100314476465031741440) := by decide +kernel

end BSCert.Consts
