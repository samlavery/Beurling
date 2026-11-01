module

public import RequestProject.BSCert.FX.Log
public import RequestProject.BSCert.Expr

/-!
# Fixed-point interval evaluation of expressions

`Ex.feval` is the analogue of `Ex.ieval` over the fixed-point intervals `FX.FI`; it is
evaluated by the kernel (`decide +kernel`). `Ex.feval_sound` says that it encloses the real
value `Ex.eval`, and `Ex.fcheckPos_sound` turns a successful positivity check into a proof.
The value of every `let` is forced to literals before it is used.
-/

@[expose] public section

namespace BSCert

open FX

namespace Ex

/-- Fixed-point interval semantics (`none` = failure). -/
def feval : Ex → List FI → Option FI
  | var i, env => env[i]?
  | cst q, _ => some (FI.ofQ q)
  | add a b, env => do let x ← feval a env; let y ← feval b env; pure (FI.add x y)
  | sub a b, env => do let x ← feval a env; let y ← feval b env; pure (FI.sub x y)
  | mul a b, env => do let x ← feval a env; let y ← feval b env; pure (FI.mul x y)
  | div a b, env => do
      let x ← feval a env; let y ← feval b env; let z ← FI.inv y; pure (FI.mul x z)
  | neg a, env => do let x ← feval a env; pure (FI.neg x)
  | sq a, env => do let x ← feval a env; pure (FI.sq x)
  | pos a, env => do let x ← feval a env; pure (FI.pos x)
  | max a b, env => do let x ← feval a env; let y ← feval b env; pure (FI.max x y)
  | min a b, env => do
      let x ← feval a env; let y ← feval b env; pure (FI.neg (FI.max (FI.neg x) (FI.neg y)))
  | exp a, env => do let x ← feval a env; FI.exp x
  | log a, env => do let x ← feval a env; FI.log x
  | sqrt a, env => do let x ← feval a env; pure (FI.sqrt x)
  | ite c a b, env => do
      let z ← feval c env
      if z.hi ≤ 0 then feval a env
      else if 0 < z.lo then feval b env
      else do let x ← feval a env; let y ← feval b env; pure (FI.hull x y)
  | lett e b, env => do let x ← feval e env; x.forceK fun x => feval b (env ++ [x])

/-- Pointwise enclosure of an environment. -/
def FEnvMem (env : List ℝ) (fenv : List FI) : Prop := List.Forall₂ FI.Mem env fenv

lemma fenvMem_get {env : List ℝ} {fenv : List FI} (h : FEnvMem env fenv) :
    ∀ (i : ℕ) (I : FI), fenv[i]? = some I → FI.Mem (env.getD i 0) I := by
  induction h with
  | nil => intro i I hI; simp at hI
  | cons hab _ ih =>
    intro i I hI
    cases i with
    | zero => simp at hI; subst hI; simpa using hab
    | succ i => simp at hI ⊢; exact ih i I (by simpa using hI)

theorem feval_sound : ∀ (e : Ex) (env : List ℝ) (fenv : List FI) (I : FI),
    FEnvMem env fenv → feval e fenv = some I → FI.Mem (eval e env) I := by
  intro e
  induction e with
  | var i => intro env fenv I h hI; exact fenvMem_get h i I hI
  | cst q => intro env fenv I _ hI; simp [feval] at hI; subst hI; exact FI.mem_ofQ q
  | add a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact FI.mem_add (iha env fenv x h hx) (ihb env fenv y h hy)
  | sub a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact FI.mem_sub (iha env fenv x h hx) (ihb env fenv y h hy)
  | mul a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact FI.mem_mul (iha env fenv x h hx) (ihb env fenv y h hy)
  | div a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hI
    have := FI.mem_inv (ihb env fenv y h hy) hz
    simp only [eval, div_eq_mul_inv]
    exact FI.mem_mul (iha env fenv x h hx) this.1
  | neg a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact FI.mem_neg (iha env fenv x h hx)
  | sq a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact FI.mem_sq (iha env fenv x h hx)
  | pos a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact FI.mem_pos (iha env fenv x h hx)
  | max a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact FI.mem_max (iha env fenv x h hx) (ihb env fenv y h hy)
  | min a b iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    have := FI.mem_neg (FI.mem_max (FI.mem_neg (iha env fenv x h hx))
      (FI.mem_neg (ihb env fenv y h hy)))
    simp only [eval]
    rwa [max_neg_neg, neg_neg] at this
  | exp a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact FI.mem_exp (iha env fenv x h hx) hI
  | log a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact (FI.mem_log (iha env fenv x h hx) hI).1
  | sqrt a iha =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact FI.mem_sqrt (iha env fenv x h hx)
  | ite c a b ihc iha ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨z, hz, hI⟩ := hI
    have hcz := ihc env fenv z h hz
    simp only [eval]
    split_ifs at hI with h1 h2
    · have : eval c env ≤ 0 := le_trans hcz.2 (by rw [← toR_zero]; exact toR_le_toR.mpr h1)
      rw [if_pos this]; exact iha env fenv I h hI
    · have : ¬ eval c env ≤ 0 := by
        have : (0 : ℝ) < toR z.lo := toR_pos.mpr h2
        linarith [hcz.1]
      rw [if_neg this]; exact ihb env fenv I h hI
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hI
      obtain ⟨x, hx, y, hy, rfl⟩ := hI
      split_ifs
      · exact FI.mem_hull_left (iha env fenv x h hx)
      · exact FI.mem_hull_right (ihb env fenv y h hy)
  | lett e b ihe ihb =>
    intro env fenv I h hI
    simp only [feval, Option.bind_eq_bind, Option.bind_eq_some_iff, FI.forceK_eq] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact ihb _ _ I (List.rel_append h (List.Forall₂.cons (ihe env fenv x h hx) List.Forall₂.nil)) hI

/-- Check that the fixed-point interval value of `e` is positive. -/
def fcheckPos (e : Ex) (fenv : List FI) : Bool :=
  match feval e fenv with
  | some I => decide (0 < I.lo)
  | none => false

theorem fcheckPos_sound {e : Ex} {env : List ℝ} {fenv : List FI} (h : FEnvMem env fenv)
    (hc : fcheckPos e fenv = true) : 0 < eval e env := by
  unfold fcheckPos at hc
  split at hc
  · rename_i I hI
    have := feval_sound e env fenv I h hI
    have h0 : 0 < toR I.lo := toR_pos.mpr (of_decide_eq_true hc)
    exact lt_of_lt_of_le h0 this.1
  · cases hc

lemma fmem_pt (q : ℚ) : FI.Mem (q : ℝ) (FI.ofQ q) := FI.mem_ofQ q

end Ex

end BSCert
