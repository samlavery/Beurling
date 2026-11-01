module

public import RequestProject.BSCert.Transc

/-!
# Expressions and their certified interval evaluation

`Ex` is a small expression language (with `let`-sharing), `Ex.eval` its real semantics and
`Ex.ieval` its interval semantics. The main theorem `Ex.ieval_sound` says that interval
evaluation encloses real evaluation, whenever the inputs are enclosed and the interval
evaluation succeeds. `Ex.checkPos_sound` turns a successful positivity check into a proof
that the real value is positive.
-/

@[expose] public section

namespace BSCert

/-- Expressions. `var i` is the `i`-th entry of the environment; `lett e b` evaluates `b` in
the environment extended *at the end* by the value of `e` (so variables are de Bruijn
levels: a `let`-bound value keeps its index in the whole body); `ite c a b` is
`if c ≤ 0 then a else b`. -/
inductive Ex where
  | var : ℕ → Ex
  | cst : ℚ → Ex
  | add : Ex → Ex → Ex
  | sub : Ex → Ex → Ex
  | mul : Ex → Ex → Ex
  | div : Ex → Ex → Ex
  | neg : Ex → Ex
  | sq : Ex → Ex
  | pos : Ex → Ex
  | max : Ex → Ex → Ex
  | min : Ex → Ex → Ex
  | exp : Ex → Ex
  | log : Ex → Ex
  | sqrt : Ex → Ex
  | ite : Ex → Ex → Ex → Ex
  | lett : Ex → Ex → Ex
deriving Inhabited

namespace Ex

/-- Real semantics. -/
noncomputable def eval : Ex → List ℝ → ℝ
  | var i, env => env.getD i 0
  | cst q, _ => (q : ℝ)
  | add a b, env => eval a env + eval b env
  | sub a b, env => eval a env - eval b env
  | mul a b, env => eval a env * eval b env
  | div a b, env => eval a env / eval b env
  | neg a, env => - eval a env
  | sq a, env => eval a env ^ 2
  | pos a, env => Max.max (eval a env) 0
  | max a b, env => Max.max (eval a env) (eval b env)
  | min a b, env => Min.min (eval a env) (eval b env)
  | exp a, env => Real.exp (eval a env)
  | log a, env => Real.log (eval a env)
  | sqrt a, env => Real.sqrt (eval a env)
  | ite c a b, env => if eval c env ≤ 0 then eval a env else eval b env
  | lett e b, env => eval b (env ++ [eval e env])

/-- Interval semantics (`none` = failure, e.g. a possible division by zero). -/
def ieval : Ex → List Itv → Option Itv
  | var i, env => env[i]?
  | cst q, _ => some (Itv.pt q)
  | add a b, env => do let x ← ieval a env; let y ← ieval b env; pure (Itv.add x y)
  | sub a b, env => do let x ← ieval a env; let y ← ieval b env; pure (Itv.sub x y)
  | mul a b, env => do let x ← ieval a env; let y ← ieval b env; pure (Itv.mul x y)
  | div a b, env => do
      let x ← ieval a env; let y ← ieval b env; let z ← Itv.inv y; pure (Itv.mul x z)
  | neg a, env => do let x ← ieval a env; pure (Itv.neg x)
  | sq a, env => do let x ← ieval a env; pure (Itv.sq x)
  | pos a, env => do let x ← ieval a env; pure (Itv.pos x)
  | max a b, env => do let x ← ieval a env; let y ← ieval b env; pure (Itv.max x y)
  | min a b, env => do
      let x ← ieval a env; let y ← ieval b env; pure (Itv.neg (Itv.max (Itv.neg x) (Itv.neg y)))
  | exp a, env => do let x ← ieval a env; Itv.exp x
  | log a, env => do let x ← ieval a env; Itv.log x
  | sqrt a, env => do let x ← ieval a env; pure (Itv.sqrt x)
  | ite c a b, env => do
      let z ← ieval c env
      if z.hi ≤ 0 then ieval a env
      else if 0 < z.lo then ieval b env
      else do let x ← ieval a env; let y ← ieval b env; pure (Itv.hull x y)
  | lett e b, env => do let x ← ieval e env; ieval b (env ++ [x])

instance : Add Ex := ⟨Ex.add⟩
instance : Sub Ex := ⟨Ex.sub⟩
instance : Mul Ex := ⟨Ex.mul⟩
instance : Div Ex := ⟨Ex.div⟩
instance : Neg Ex := ⟨Ex.neg⟩
instance (n : ℕ) : OfNat Ex n := ⟨Ex.cst n⟩
instance : OfScientific Ex := ⟨fun m s e => Ex.cst (OfScientific.ofScientific m s e)⟩

@[simp] lemma eval_hadd (a b : Ex) (env : List ℝ) : eval (a + b) env = eval a env + eval b env := rfl
@[simp] lemma eval_hsub (a b : Ex) (env : List ℝ) : eval (a - b) env = eval a env - eval b env := rfl
@[simp] lemma eval_hmul (a b : Ex) (env : List ℝ) : eval (a * b) env = eval a env * eval b env := rfl
@[simp] lemma eval_hdiv (a b : Ex) (env : List ℝ) : eval (a / b) env = eval a env / eval b env := rfl
@[simp] lemma eval_hneg (a : Ex) (env : List ℝ) : eval (-a) env = - eval a env := rfl
@[simp] lemma eval_ofNat (n : ℕ) (env : List ℝ) :
    eval (OfNat.ofNat n : Ex) env = ((n : ℚ) : ℝ) := rfl
@[simp] lemma eval_ofScientific (m : ℕ) (s : Bool) (e : ℕ) (env : List ℝ) :
    eval (OfScientific.ofScientific m s e : Ex) env = ((OfScientific.ofScientific m s e : ℚ) : ℝ) := rfl

/-- Pointwise enclosure of an environment. -/
def EnvMem (env : List ℝ) (ienv : List Itv) : Prop := List.Forall₂ Itv.Mem env ienv

lemma envMem_get {env : List ℝ} {ienv : List Itv} (h : EnvMem env ienv) :
    ∀ (i : ℕ) (I : Itv), ienv[i]? = some I → Itv.Mem (env.getD i 0) I := by
  induction h with
  | nil => intro i I hI; simp at hI
  | cons hab _ ih =>
    intro i I hI
    cases i with
    | zero => simp at hI; subst hI; simpa using hab
    | succ i => simp at hI ⊢; exact ih i I (by simpa using hI)

theorem ieval_sound : ∀ (e : Ex) (env : List ℝ) (ienv : List Itv) (I : Itv),
    EnvMem env ienv → ieval e ienv = some I → Itv.Mem (eval e env) I := by
  intro e
  induction e with
  | var i => intro env ienv I h hI; exact envMem_get h i I hI
  | cst q => intro env ienv I _ hI; simp [ieval] at hI; subst hI; exact Itv.mem_pt q
  | add a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact Itv.mem_add (iha env ienv x h hx) (ihb env ienv y h hy)
  | sub a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact Itv.mem_sub (iha env ienv x h hx) (ihb env ienv y h hy)
  | mul a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact Itv.mem_mul (iha env ienv x h hx) (ihb env ienv y h hy)
  | div a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hI
    have := Itv.mem_inv (ihb env ienv y h hy) hz
    simp only [eval, div_eq_mul_inv]
    exact Itv.mem_mul (iha env ienv x h hx) this.1
  | neg a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact Itv.mem_neg (iha env ienv x h hx)
  | sq a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact Itv.mem_sq (iha env ienv x h hx)
  | pos a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact Itv.mem_pos (iha env ienv x h hx)
  | max a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    exact Itv.mem_max (iha env ienv x h hx) (ihb env ienv y h hy)
  | min a b iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, y, hy, rfl⟩ := hI
    have := Itv.mem_neg (Itv.mem_max (Itv.mem_neg (iha env ienv x h hx))
      (Itv.mem_neg (ihb env ienv y h hy)))
    simp only [eval]
    rwa [max_neg_neg, neg_neg] at this
  | exp a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact Itv.mem_exp (iha env ienv x h hx) hI
  | log a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact (Itv.mem_log (iha env ienv x h hx) hI).1
  | sqrt a iha =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hI
    obtain ⟨x, hx, rfl⟩ := hI
    exact Itv.mem_sqrt (iha env ienv x h hx)
  | ite c a b ihc iha ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨z, hz, hI⟩ := hI
    have hcz := ihc env ienv z h hz
    simp only [eval]
    split_ifs at hI with h1 h2
    · have : eval c env ≤ 0 := le_trans hcz.2 (by exact_mod_cast h1)
      rw [if_pos this]; exact iha env ienv I h hI
    · have : ¬ eval c env ≤ 0 := by
        have : (0 : ℝ) < z.lo := by exact_mod_cast h2
        linarith [hcz.1]
      rw [if_neg this]; exact ihb env ienv I h hI
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hI
      obtain ⟨x, hx, y, hy, rfl⟩ := hI
      split_ifs
      · exact Itv.mem_hull_left (iha env ienv x h hx)
      · exact Itv.mem_hull_right (ihb env ienv y h hy)
  | lett e b ihe ihb =>
    intro env ienv I h hI
    simp only [ieval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hI
    obtain ⟨x, hx, hI⟩ := hI
    exact ihb _ _ I (List.rel_append h (List.Forall₂.cons (ihe env ienv x h hx) List.Forall₂.nil)) hI

/-- Check that the interval value of `e` is positive. -/
def checkPos (e : Ex) (ienv : List Itv) : Bool :=
  match ieval e ienv with
  | some I => decide (0 < I.lo)
  | none => false

theorem checkPos_sound {e : Ex} {env : List ℝ} {ienv : List Itv} (h : EnvMem env ienv)
    (hc : checkPos e ienv = true) : 0 < eval e env := by
  unfold checkPos at hc
  split at hc
  · rename_i I hI
    have := ieval_sound e env ienv I h hI
    have h0 : (0 : ℝ) < I.lo := by exact_mod_cast (of_decide_eq_true hc)
    exact lt_of_lt_of_le h0 this.1
  · cases hc

/-- The lower end of the interval value (or `0` on failure); used for table building. -/
def iLo (e : Ex) (ienv : List Itv) : Option ℚ := (ieval e ienv).map Itv.lo
/-- The upper end of the interval value. -/
def iHi (e : Ex) (ienv : List Itv) : Option ℚ := (ieval e ienv).map Itv.hi

lemma iLo_sound {e : Ex} {env : List ℝ} {ienv : List Itv} {q : ℚ} (h : EnvMem env ienv)
    (hq : iLo e ienv = some q) : (q : ℝ) ≤ eval e env := by
  unfold iLo at hq
  simp only [Option.map_eq_some_iff] at hq
  obtain ⟨I, hI, rfl⟩ := hq
  exact (ieval_sound e env ienv I h hI).1

lemma iHi_sound {e : Ex} {env : List ℝ} {ienv : List Itv} {q : ℚ} (h : EnvMem env ienv)
    (hq : iHi e ienv = some q) : eval e env ≤ (q : ℝ) := by
  unfold iHi at hq
  simp only [Option.map_eq_some_iff] at hq
  obtain ⟨I, hI, rfl⟩ := hq
  exact (ieval_sound e env ienv I h hI).2

end Ex

end BSCert
