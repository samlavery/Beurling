import RequestProject.BSCert.FX.Dickman
open BSCert BSCert.FX
def a0 : ℤ := match Ex.feval rExactEx [⟨2 * ZI, 2 * ZI⟩] with | some I => max I.lo ZI | none => ZI
def L0 : ℤ := max 0 (expLo (-a0))
partial def mkTree (a : Array REntry) (lo hi : Nat) : String :=
  if lo ≥ hi then ".leaf" else
  let m := (lo + hi) / 2
  let e := a[m]!
  s!"(.node ({e.1}, {e.2.1}, {e.2.2}) {mkTree a lo m} {mkTree a (m+1) hi})"
def main : IO Unit := do
  let extra : List Nat := [9, 26, 15810, 31620, 399999, 400001]
  let mut a := a0
  let mut L := L0
  let mut nxt : Float := 2.0
  let mut out : Array REntry := #[]
  for n in [2:400002] do
    if n.toFloat ≥ nxt || extra.contains n then
      out := out.push (n, a, L)
      if n.toFloat ≥ nxt then nxt := Float.ceil (n.toFloat * 1.01)
    let p := rlStepF a L
    a := p.1; L := p.2
  IO.println s!"{out.size} entries; last {out.back!.1} a={((out.back!.2.1 : ℚ)/ZN).toFloat}"
  for e in out do
    if extra.contains e.1 then IO.println s!"{e.1}: {((e.2.1 : ℚ)/ZN).toFloat}"
  IO.FS.writeFile "/tmp/rhscratch/gen/rtab_tree.txt" (mkTree out 0 out.size)
  IO.FS.writeFile "/tmp/rhscratch/gen/rtab_keys.txt" (String.intercalate "\n" (out.toList.map fun e => toString e.1))
