module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 2 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg2 : chainBound cb2 ((pts.drop 40).take 21) = some (55899227936484224203748424163192666171248339400778901208804486177 / 2047651225462798897751163033694861724018737472077052274907545600) := by decide +kernel

end BSCert.Consts
