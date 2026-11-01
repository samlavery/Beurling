module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 12 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg12 : chainBound cb2 (pts.drop 240) = some (91892420685101224270329816382591279825884188941215815309250233493235 / 1122877604961021342111861939901472204276961141817801948370396813640163393536) := by decide +kernel

end BSCert.Consts
