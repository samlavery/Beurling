module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 1 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg1 : chainBound cb2 ((pts.drop 20).take 21) = some (62363152637862447599427049826491037957 / 809596710430037081782952918620569600) := by decide +kernel

end BSCert.Consts
