import RequestProject.BSCert.FX.Dickman
open BSCert BSCert.FX
def a0 : ℤ := match Ex.feval rExactEx [⟨2 * ZI, 2 * ZI⟩] with | some I => max I.lo ZI | none => ZI
partial def mkTree (a : Array REntry) (lo hi : Nat) : String :=
  if lo ≥ hi then ".leaf" else
  let m := (lo + hi) / 2
  let e := a[m]!
  s!"(.node ({e.1}, {e.2}) {mkTree a lo m} {mkTree a (m+1) hi})"
def stepA (a : ℤ) : ℤ := match expHi a with
  | some E => (a * E) / (E - ZI)
  | none => a
partial def bis (a : ℤ) (j : ℕ) (lo hi : ℤ) : ℤ :=
  if hi - lo ≤ 1 then lo else
  let m := (lo + hi) / 2
  let ok := match expHi m with
    | some E => decide (ZI < E) && decide ((m - a) * (E - ZI) ≤ (j : ℤ) * m * ZI)
    | none => false
  if ok then bis a j m hi else bis a j lo m
def main : IO Unit := do
  let extra : List Nat := [15810, 31620, 399999, 400001]
  let mut out : Array REntry := #[(2, a0)]
  let mut a := a0
  for n in [3:1001] do
    a := stepA a
    out := out.push (n, a)
  let mut n : Nat := 1000
  while n < 400001 do
    let g := (Float.ceil (n.toFloat * 1.003)).toUInt64.toNat
    let cand := (extra.filter (fun x => n < x ∧ x < g))
    let m := match cand with | x :: _ => x | [] => min g 400001
    let j := m - n
    a := bis a j a (a + (j : ℤ) * ZI)
    out := out.push (m, a)
    n := m
  IO.println s!"{out.size} entries"
  for e in out do
    if extra.contains e.1 || e.1 = 9 || e.1 = 26 then IO.println s!"{e.1}: {((e.2 : ℚ)/ZN).toFloat}"
  -- verify chain natively
  IO.println s!"chainOK: {chainOK out.toList}"
  IO.FS.writeFile "/tmp/rhscratch/gen/rtab_tree.txt" (mkTree out 0 out.size)
