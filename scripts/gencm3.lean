import RequestProject.BSCert.Finite.KArith
open BSCert BSCert.FX BSCert.FiniteN.K
def main : IO Unit := do
  let mut C : ℤ := 0
  let mut out : Array ℤ := #[0]
  for n in [0:100001] do
    C := C + cm3HiK n
    if (n + 1) % 2500 = 0 ∨ n = 100000 then out := out.push C
  IO.FS.writeFile "/tmp/rhscratch/gen/cm3c.txt" (String.intercalate "\n" (out.toList.map toString))
  IO.println s!"{out.size} {((C : ℚ) / ZN).toFloat}  final check: {decide (100000000 * C + 2840 * ZI ≤ 75539000 * ZI)}"
