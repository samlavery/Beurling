module

public import RequestProject.BSCert.Consts.MarginCells

/-! Kernel-checked segment 2 of the chain bound `chainBound cb3 pts` (`margins.py`). -/

@[expose] public section

namespace BSCert.Consts

lemma cb3_seg2 : chainBound cb3 ((pts.drop 40).take 21) = some (10397631022106835220011758761433032785274601467043616605495388581 / 59642164760857772694675653589433981309018657320018532394818181529600) := by decide +kernel

end BSCert.Consts
