module

public import RequestProject.Beurling.Noise.BSL57RAsm
public import RequestProject.Beurling.Noise.BSL57RC
public import RequestProject.Beurling.Noise.BSL57RF

/-!
# Step 7(ii) from the four open remainder bounds (a), (b), (d), (e) of Lemma 5.7

Remainders (c) (`remC`) and (f) (`remF`) are proved; (a) `RemA`, (b) `RemB`, (d) `RemD`,
(e) `RemE` remain as hypotheses.
-/

@[expose] public section

namespace BSaias.Large

/-- **Step 7(ii) of the proof of Theorem 5.6** (`RegionLarge`) from the remainder bounds
(a), (b), (d), (e) of the proof of Lemma 5.7. -/
theorem regionLarge_of_ABDE (hA : RemA) (hB : RemB) (hD : RemD) (hE : RemE) : RegionLarge :=
  regionLarge_of_six hA hB remC hD hE remF

/-- `Lemma57Ineq` from (a), (b), (d), (e). -/
theorem lemma57Ineq_of_ABDE (hA : RemA) (hB : RemB) (hD : RemD) (hE : RemE) : Lemma57Ineq :=
  lemma57Ineq_of_remC (remC_of_six hA hB remC hD hE remF)

end BSaias.Large

end
