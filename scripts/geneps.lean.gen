import RequestProject.Beurling.Noise.BSLargeEpsK
open BSCert BSCert.FX BSaias.Large
partial def leaves (f : ℤ → ℤ → Bool) : ℕ → ℤ → ℤ → Option (List (ℤ × ℤ))
  | 0, a, b => if f a b then some [(a, b)] else none
  | d + 1, a, b => if f a b then some [(a, b)] else
      match leaves f d a ((a + b) / 2), leaves f d ((a + b) / 2) b with
      | some l1, some l2 => some (l1 ++ l2)
      | _, _ => none
def lit (z : ℤ) : String := if z < 0 then s!"({z})" else toString z
partial def topCells (a b : ℤ) (num den : ℤ) (acc : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  if a ≥ b then acc else
  let y := a * num / den
  if b ≤ y then acc.push (a, b) else topCells y b num den (acc.push (a, y))
def main : IO Unit := do
  let a : ℕ := 10 ^ 18
  let b : ℕ := 10 ^ 30
  let tops := topCells ((a : ℤ) * ZI) ((b : ℤ) * ZI) 11 10 #[]
  let mut lv : Array (ℤ × ℤ) := #[]
  for c in tops do
    match leaves epsCellF 8 c.1 c.2 with
    | some l => lv := lv ++ l.toArray
    | none => throw (IO.userError s!"fail at {c.1}")
  let segmax := 30
  let segs := (Array.range ((lv.size + segmax - 1) / segmax)).map fun k =>
    lv.extract (k * segmax) ((k + 1) * segmax)
  let mut src := ""
  let mut g := ""
  let mut i := 0
  for sg in segs do
    let X := if i = 0 then s!"({a} * ZI)" else lit sg[0]!.1
    let Y := if i + 1 = segs.size then s!"({b} * ZI)" else lit sg.back!.2
    let mids := String.intercalate ", " ((sg.toList.drop 1).map fun c => lit c.1)
    src := src ++ s!"lemma epsK_{i} : coverL epsCellF {X}\n    [{mids}] {Y} = true := by decide +kernel\n\n"
    let S := s!"(coverL_sound (fun ℓ => 0 < 3 / 100 - epsBar ℓ) _ epsCellF_sound _ _ _ epsK_{i})"
    g := if i = 0 then S else s!"(glueF {g}\n    {S})"
    i := i + 1
  src := src ++ s!"theorem epsK_range :\n    ∀ ℓ : ℝ, toR ({a} * ZI) ≤ ℓ → ℓ ≤ toR ({b} * ZI) → 0 < 3 / 100 - epsBar ℓ :=\n  {g}\n\n"
  IO.FS.writeFile "/tmp/rhscratch/gen/eps_part.lean" src
  IO.eprintln s!"eps: {tops.size} top cells, {lv.size} leaves, {segs.size} declarations"
