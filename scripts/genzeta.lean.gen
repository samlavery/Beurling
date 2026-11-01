import RequestProject.BSCert.Consts.ZetaK
open BSCert BSCert.FX BSCert.Consts BSCert.FiniteN
def CH : ℕ := 500
def sums : List (String × String × ℕ × ℕ) :=
  [("zH17287", "hi", 17287, 10000), ("zL17286", "lo", 17286, 10000), ("zH197", "hi", 197, 100),
   ("zD197", "d", 197, 100), ("zH18", "hi", 18, 10), ("zH1799997", "hi", 1799997, 1000000),
   ("zH177", "hi", 177, 100), ("zH1955", "hi", 1955, 1000)]
def term (kind : String) (a b k : ℕ) : ℤ :=
  if kind = "hi" then zTermHi a b k else if kind = "lo" then zTermLo a b k else zdTermHi a b k
def main : IO Unit := do
  let mut consts := ""
  let mut lemmas : Array String := #[]
  for (nm, kind, a, b) in sums do
    let mut C : ℤ := 0
    let mut out : Array ℤ := #[0]
    for k in [0:3000] do
      C := C + term kind a b k
      if (k + 1) % CH = 0 then out := out.push C
    consts := consts ++ s!"/-- Running sums for `{nm}`. -/\ndef {nm}C (k : ℕ) : ℤ := [{String.intercalate ", " (out.toList.map toString)}].getD k 0\n\n"
    let f := if kind = "hi" then s!"K.sumUp (zTermHi {a} {b})" else if kind = "lo" then s!"sumDown (zTermLo {a} {b})" else s!"K.sumUp (zdTermHi {a} {b})"
    for i in [0:6] do
      lemmas := lemmas.push s!"lemma {nm}_{i} : {f} {CH} ({CH} * {i}) ({nm}C {i}) = {nm}C {i+1} := by\n  decide +kernel\n"
    IO.eprintln s!"{nm}: {((C : ℚ) / ZN).toFloat}"
  IO.FS.writeFile "/tmp/rhscratch/gen/zeta_consts.txt" consts
  IO.FS.writeFile "/tmp/rhscratch/gen/zeta_lemmas.txt" (String.intercalate "\n" lemmas.toList)
