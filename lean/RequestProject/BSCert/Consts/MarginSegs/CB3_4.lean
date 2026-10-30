module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 4 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg4 : chainBound cb3 ((pts.drop 80).take 21) = some (14904802316996761328914944060734712311964069986283390268751655309178570310633230136797496513463105725854253 / 15618552707453817654099915339443181555289539488300369346342080184886608210193673758022104087590066059744001392640) := by decide +kernel

end BSCert.Consts
