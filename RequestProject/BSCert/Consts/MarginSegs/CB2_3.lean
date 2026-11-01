module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 3 of the chain bound `chainBound cb2 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb2_seg3 : chainBound cb2 ((pts.drop 60).take 21) = some (199291507052019016637835965590214681408826822230602778922100755840185387589757512653 / 30482393652037598815916011228510090131551899506917846476668263051260305585230315520) := by decide +kernel

end BSCert.Consts
