module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 4 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg4 : chainBound cb2 ((pts.drop 80).take 21) = some (22697745601676936409137244426624505218112058303268288226846116853615137479658437494343027193849538110889543 / 17915812321012056661888312521144954777053467762065479090749708504516338258632147012699433923494368541409280) := by decide +kernel

end BSCert.Consts
