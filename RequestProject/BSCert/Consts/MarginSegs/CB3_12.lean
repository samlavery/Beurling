module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 12 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg12 : chainBound cb3 (pts.drop 240) = some (452607484833022775228972301993028341227536886481252774468150498497479 / 376775202399874532744412078558120357783014017997677918660619906963055350572929515520) := by decide +kernel

end BSCert.Consts
