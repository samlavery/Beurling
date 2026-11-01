module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 3 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg3 : chainBound cb3 ((pts.drop 60).take 21) = some (1289886211905283954810842009611872893405734210267369138785315060557791268042925085779 / 102669372092253684390781285555584751654451801369720730467715256463856441699087185231216640) := by decide +kernel

end BSCert.Consts
