module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 1 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg1 : chainBound cb3 ((pts.drop 20).take 21) = some (14535464706545718149396987032464724058141 / 5730234841592234300706581067269506125004800) := by decide +kernel

end BSCert.Consts
