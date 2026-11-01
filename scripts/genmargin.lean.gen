import RequestProject.BSCert.Consts.MarginCells
open BSCert BSCert.Consts
def main : IO Unit := do
  IO.println s!"pts {pts.length} ptN {ptN}"
  let mut out := ""
  for (nm, cb) in [("cb2", cb2), ("cb3", cb3)] do
    let mut tot : ℚ := 0
    for k in [0:13] do
      let seg := if k = 12 then pts.drop 240 else (pts.drop (20 * k)).take 21
      match chainBound cb seg with
      | some u => out := out ++ s!"{nm} {k} {u.num} {u.den}\n"; tot := tot + u
      | none => IO.println s!"{nm} {k} NONE"
    IO.println s!"{nm} total {tot.toFloat}"
  match tail2 ptN, tail3 ptN with
  | some t2, some t3 => IO.println s!"tail2 {t2.toFloat} tail3 {t3.toFloat}"; out := out ++ s!"tail2 {t2.num} {t2.den}\ntail3 {t3.num} {t3.den}\n"
  | _, _ => IO.println "tail NONE"
  IO.FS.writeFile "/tmp/rhscratch/gen/margin_vals.txt" out
