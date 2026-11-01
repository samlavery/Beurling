import RequestProject.BSCert.Finite.KArith
open BSCert BSCert.FX
def main : IO Unit := do
  let mut C : ℤ := 0
  for k in [0:10000] do C := C + cdiv ZI ((k + 1 : ℕ) : ℤ)
  IO.println C
