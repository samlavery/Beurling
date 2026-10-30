module

public import RequestProject.BSCert.FX.Expr
public import RequestProject.BSCert.Dickman

/-!
# Fixed-point enclosures of the Dickman ratio `r`

The analogue of `BSCert.Dickman` (`r_low` table, `r_up`, `rEnc`) for the fixed-point
arithmetic. Lower bounds for `r(n)` are kept in a sparse table of pairs `(n, a)`; consecutive
entries are certified from (R3) by a single step (`A ≤ a/(1 - e^{-a})`) or, for `n ≥ 1000`,
by the jump lemma `jump` (`A - a ≤ j φ(A)`, `φ(t) = t/(e^t - 1)`), each with one evaluation of
`exp` (`pairOK`). Lookup returns the entry with the largest key `≤ ⌊x⌋` (`RT.find`).
-/

@[expose] public section

namespace BSCert.FX

open Ex

/-! ## Certified lower bounds for `r` at integers -/

/-- `φ(t) = t/(e^t - 1)` is non-increasing on `(0, ∞)` (convexity of `exp`). -/
lemma phi_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    t / (Real.exp t - 1) ≤ s / (Real.exp s - 1) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hes : 0 < Real.exp s - 1 := by have := Real.add_one_le_exp s; have := Real.add_one_lt_exp hs.ne'; linarith
  have het : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp ht.ne'; linarith
  have hconv := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0)
    (div_nonneg hs.le ht.le) (sub_nonneg.mpr ((div_le_one ht).mpr hst))
    (by ring : s / t + (1 - s / t) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have e1 : s / t * t = s := by field_simp
  rw [e1] at hconv
  rw [div_le_div_iff₀ het hes]
  have : t * (Real.exp s - 1) ≤ t * (s / t * (Real.exp t - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.le
  calc t * (Real.exp s - 1) ≤ t * (s / t * (Real.exp t - 1)) := this
    _ = s * (Real.exp t - 1) := by field_simp

/-- `s/(1 - e^{-s}) = s + s/(e^s - 1)`. -/
lemma g_eq {s : ℝ} (hs : 0 < s) : s / (1 - Real.exp (-s)) = s + s / (Real.exp s - 1) := by
  have he : 0 < Real.exp s - 1 := by have := Real.add_one_lt_exp hs.ne'; linarith
  have he' : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  rw [Real.exp_neg]
  have : 1 - (Real.exp s)⁻¹ = (Real.exp s - 1) / Real.exp s := by field_simp
  rw [this]
  field_simp
  ring

/-- **Jump lemma.** If `1 ≤ a ≤ r(x)` and `A - a ≤ j φ(A)` (`φ(t) = t/(e^t-1)`), then
`A ≤ r(x + j)`: as long as `r < A` along the way, every step of (R3) adds at least `φ(A)`. -/
lemma jump {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {x a A : ℝ} (hx : 2 ≤ x) (ha : 1 ≤ a)
    (har : a ≤ r x) (hA : 0 < A) (j : ℕ) (hj : A - a ≤ j * (A / (Real.exp A - 1))) :
    A ≤ r (x + j) := by
  set φ := A / (Real.exp A - 1) with hφ
  have hφ0 : 0 ≤ φ := by
    have : 0 < Real.exp A - 1 := by have := Real.add_one_lt_exp hA.ne'; linarith
    positivity
  have key : ∀ i : ℕ, min A (a + i * φ) ≤ r (x + i) := by
    intro i
    induction i with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; exact (min_le_right _ _).trans har
    | succ i ih =>
      set s := r (x + i)
      have hs1 : 1 ≤ s := hr.one_le (by linarith [i.cast_nonneg (α := ℝ)])
      have hs0 : 0 < s := by linarith
      have hrec := hr.recursion (x + (i + 1 : ℕ)) (by push_cast; linarith [i.cast_nonneg (α := ℝ)])
      rw [show x + ((i + 1 : ℕ) : ℝ) - 1 = x + i by push_cast; ring] at hrec
      rw [g_eq hs0] at hrec
      have hps : 0 ≤ s / (Real.exp s - 1) := by
        have : 0 < Real.exp s - 1 := by have := Real.add_one_lt_exp hs0.ne'; linarith
        positivity
      by_cases hsA : A ≤ s
      · have : s ≤ r (x + ((i + 1 : ℕ) : ℝ)) := by linarith
        exact (min_le_left _ _).trans (hsA.trans this)
      · push_neg at hsA
        have hm : a + i * φ ≤ s := by
          rcases min_choice A (a + i * φ) with h | h
          · rw [h] at ih; linarith
          · rwa [h] at ih
        have hφs : φ ≤ s / (Real.exp s - 1) := phi_anti hs0 hsA.le
        refine (min_le_right _ _).trans ?_
        push_cast at hrec ⊢
        linarith
  have := key j
  rwa [min_eq_left (by linarith)] at this

/-- An entry `(n, a)`: `a ≤ r(n)` (fixed point). -/
abbrev REntry := ℕ × ℤ

/-- The invariant at a point `x`. -/
def RInv (r : ℝ → ℝ) (x : ℝ) (a : ℤ) : Prop := 1 ≤ toR a ∧ toR a ≤ r x

/-- Two consecutive entries: a single step of (R3) (`A ≤ a e^a/(e^a - 1)`), or a jump
(`(A - a)(e^A - 1) ≤ j A`), with `e^a`, `e^A` bounded above by `expHi`. -/
def pairOK (e f : REntry) : Bool :=
  decide (2 ≤ e.1) && decide (e.1 ≤ f.1) && decide (ZI ≤ f.2) &&
    (if f.1 = e.1 + 1 then
      match expHi e.2 with
      | some E => decide (ZI < E) && decide (f.2 * (E - ZI) ≤ e.2 * E)
      | none => false
    else
      match expHi f.2 with
      | some E => decide (ZI < E) && decide ((f.2 - e.2) * (E - ZI) ≤ ((f.1 - e.1 : ℕ) : ℤ) * f.2 * ZI)
      | none => false)

lemma pairOK_spec {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {e f : REntry} (h : pairOK e f = true)
    (he : RInv r e.1 e.2) : RInv r f.1 f.2 := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, hle⟩, hZ⟩, hc⟩ := h
  obtain ⟨ha1, har⟩ := he
  have hA1 : 1 ≤ toR f.2 := by rw [← toR_ZI]; exact toR_le_toR.mpr hZ
  refine ⟨hA1, ?_⟩
  have hx2 : (2 : ℝ) ≤ e.1 := by exact_mod_cast h2
  split_ifs at hc with hstep
  · split at hc
    · rename_i E hE
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hE1, hc⟩ := hc
      have hEe := le_expHi hE
      have ha0 : 0 < toR e.2 := by linarith
      have hE1' : 1 < toR E := by rw [← toR_ZI]; exact toR_lt_toR.mpr hE1
      -- `toR A ≤ toR a · E/(E - 1) ≤ a/(1 - e^{-a})`
      have hc' : toR f.2 * (toR E - 1) ≤ toR e.2 * toR E := by
        have : ((f.2 * (E - ZI) : ℤ) : ℝ) ≤ ((e.2 * E : ℤ) : ℝ) := by exact_mod_cast hc
        unfold toR
        have hZ2 : (0 : ℝ) < (ZI : ℝ) * ZI := mul_pos ZR_pos ZR_pos
        have hz0 : (ZI : ℝ) ≠ 0 := ZR_pos.ne'
        have e1 : (f.2 : ℝ) / ZI * ((E : ℝ) / ZI - 1) = ((f.2 * (E - ZI) : ℤ) : ℝ) / (ZI * ZI) := by
          push_cast; field_simp <;> ring
        have e2 : (e.2 : ℝ) / ZI * ((E : ℝ) / ZI) = ((e.2 * E : ℤ) : ℝ) / (ZI * ZI) := by
          push_cast; field_simp <;> ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_right this hZ2.le
      have hg : toR e.2 * toR E / (toR E - 1) ≤ toR e.2 / (1 - Real.exp (-toR e.2)) := by
        rw [g_eq ha0]
        have hea : 0 < Real.exp (toR e.2) - 1 := by
          have := Real.add_one_lt_exp ha0.ne'; linarith
        rw [div_le_iff₀ (by linarith)]
        have : toR e.2 / (Real.exp (toR e.2) - 1) * (toR E - 1) ≥ toR e.2 := by
          rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hea]
          nlinarith
        nlinarith
      have hrec := hr.recursion ((e.1 : ℝ) + 1) (by linarith)
      rw [show (e.1 : ℝ) + 1 - 1 = e.1 by ring] at hrec
      have hmono := div_one_sub_exp_neg_mono ha0 har
      have : (f.1 : ℝ) = e.1 + 1 := by exact_mod_cast hstep
      rw [this]
      have hA : toR f.2 ≤ toR e.2 * toR E / (toR E - 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    · cases hc
  · split at hc
    · rename_i E hE
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hE1, hc⟩ := hc
      have hEe := le_expHi hE
      have hA0 : 0 < toR f.2 := by linarith
      have hE1' : 1 < toR E := by rw [← toR_ZI]; exact toR_lt_toR.mpr hE1
      set j := f.1 - e.1
      have hc' : (toR f.2 - toR e.2) * (toR E - 1) ≤ j * toR f.2 := by
        have : (((f.2 - e.2) * (E - ZI) : ℤ) : ℝ) ≤ (((j : ℤ) * f.2 * ZI : ℤ) : ℝ) := by
          exact_mod_cast hc
        unfold toR
        have hZ2 : (0 : ℝ) < (ZI : ℝ) * ZI := mul_pos ZR_pos ZR_pos
        have hz0 : (ZI : ℝ) ≠ 0 := ZR_pos.ne'
        have e1 : ((f.2 : ℝ) / ZI - (e.2 : ℝ) / ZI) * ((E : ℝ) / ZI - 1) =
            (((f.2 - e.2) * (E - ZI) : ℤ) : ℝ) / (ZI * ZI) := by
          push_cast; field_simp <;> ring
        have e2 : (j : ℝ) * ((f.2 : ℝ) / ZI) = (((j : ℤ) * f.2 * ZI : ℤ) : ℝ) / (ZI * ZI) := by
          push_cast; field_simp <;> ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_right this hZ2.le
      have hjump : toR f.2 - toR e.2 ≤ j * (toR f.2 / (Real.exp (toR f.2) - 1)) := by
        have hea : 0 < Real.exp (toR f.2) - 1 := by
          have := Real.add_one_lt_exp hA0.ne'; linarith
        have h1 : toR f.2 - toR e.2 ≤ j * toR f.2 / (toR E - 1) := by
          rw [le_div_iff₀ (by linarith)]; exact hc'
        refine h1.trans ?_
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact div_le_div_of_nonneg_left hA0.le hea (by linarith)
      have := jump hr hx2 ha1 har hA0 j hjump
      rwa [show (e.1 : ℝ) + j = f.1 by simp only [j]; push_cast [Nat.cast_sub hle]; ring] at this
    · cases hc

/-- All consecutive pairs of a list are `pairOK`. -/
def chainOK : List REntry → Bool
  | [] => true
  | [_] => true
  | e :: f :: rest => pairOK e f && chainOK (f :: rest)

lemma pairOK_le {e f : REntry} (h : pairOK e f = true) : 2 ≤ e.1 ∧ e.1 ≤ f.1 := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

lemma chainOK_spec {r : ℝ → ℝ} (hr : DickmanRatioFacts r) :
    ∀ (l : List REntry) (e : REntry), chainOK (e :: l) = true → 2 ≤ e.1 →
      RInv r e.1 e.2 → ∀ g ∈ e :: l, 2 ≤ g.1 ∧ RInv r g.1 g.2 := by
  intro l
  induction l with
  | nil => intro e _ h2 he g hg; simp at hg; subst hg; exact ⟨h2, he⟩
  | cons f rest ih =>
    intro e h h2 he g hg
    simp only [chainOK, Bool.and_eq_true] at h
    have hf := pairOK_spec hr h.1 he
    have hle := pairOK_le h.1
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨h2, he⟩
    · exact ih f h.2 (by omega) hf g hg

/-! ## Search tree -/

/-- A search tree of entries (keys increasing in order). -/
inductive RT where
  | leaf : RT
  | node : REntry → RT → RT → RT

/-- The entries, in order. -/
def RT.toList : RT → List REntry
  | .leaf => []
  | .node e l r => l.toList ++ e :: r.toList

/-- The value `a` of the entry with the largest key `≤ x` (or `d`). -/
def RT.find : RT → ℕ → ℤ → ℤ
  | .leaf, _, d => d
  | .node e l r, x, d => if x < e.1 then RT.find l x d else RT.find r x e.2

lemma RT.find_spec : ∀ (t : RT) (x : ℕ) (d : ℤ),
    t.find x d = d ∨ ∃ g ∈ t.toList, g.1 ≤ x ∧ t.find x d = g.2 := by
  intro t
  induction t with
  | leaf => intro x d; left; rfl
  | node e l r ihl ihr =>
    intro x d
    simp only [RT.find, RT.toList]
    split_ifs with hx
    · rcases ihl x d with h | ⟨g, hg, h1, h2⟩
      · left; exact h
      · right; exact ⟨g, List.mem_append_left _ hg, h1, h2⟩
    · rcases ihr x e.2 with h | ⟨g, hg, h1, h2⟩
      · right; exact ⟨e, by simp, by omega, h⟩
      · right; exact ⟨g, by simp [hg], h1, h2⟩

/-! ## Enclosure of `r` -/

/-- A certified table: all entries satisfy the invariant. -/
def TabOKF (r : ℝ → ℝ) (t : RT) : Prop := ∀ g ∈ t.toList, 2 ≤ g.1 ∧ RInv r g.1 g.2

/-- Lower bound for `r` on `[x, ∞)` (`x = X / 2^128 ≥ 1`). -/
def rLowF (t : RT) (X : ℤ) : ℤ :=
  if X < 2 * ZI then
    match feval rExactEx [⟨X, X⟩] with
    | some I => Max.max I.lo ZI
    | none => ZI
  else Max.max (t.find (X / ZI).toNat ZI) ZI

/-- The choice of `δ` in (R4) (only affects sharpness). -/
def deltaF (X : ℤ) : ℚ :=
  if X < 4 * ZI then 3 / 10 else if X < 19 * ZI then 1 / 5 else if X < 147 * ZI then 3 / 20
  else if X < 26215 * ZI then 1 / 10 else 1 / 20

/-- Upper bound for `r` on `[1, x]`. -/
def rUpF (X : ℤ) : Option ℤ :=
  if X ≤ 2 * ZI then (feval rExactEx [⟨X, X⟩]).map (·.hi)
  else (feval (rUpEx (deltaF X)) [⟨X, X⟩]).map (·.hi)

/-- Enclosure of `r(u)` for `u ∈ [ua, ub]`. -/
def rEncF (t : RT) (ua ub : ℤ) : Option FI :=
  if ZI ≤ ua then (rUpF ub).map fun h => ⟨rLowF t ua, h⟩ else none

lemma mem_pt (X : ℤ) : FI.Mem (toR X) ⟨X, X⟩ := ⟨le_rfl, le_rfl⟩

lemma rLowF_le {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {t : RT} (ht : TabOKF r t) {X : ℤ}
    (hX : ZI ≤ X) {u : ℝ} (hu : toR X ≤ u) : toR (rLowF t X) ≤ r u := by
  have hX1 : (1 : ℝ) ≤ toR X := by rw [← toR_ZI]; exact toR_le_toR.mpr hX
  have hu1 : 1 ≤ u := hX1.trans hu
  have hmono : r (toR X) ≤ r u := hr.mono (Set.mem_Ici.mpr hX1) (Set.mem_Ici.mpr hu1) hu
  have hone := hr.one_le hu1
  have hZ : toR ZI ≤ r u := by rw [toR_ZI]; exact hone
  unfold rLowF
  split_ifs with h2
  · split
    · rename_i I hI
      have := feval_sound rExactEx [toR X] _ I
        (List.Forall₂.cons (mem_pt X) List.Forall₂.nil) hI
      have hx2 : toR X ≤ 2 := by
        have : toR X < toR (2 * ZI) := toR_lt_toR.mpr h2
        unfold toR at this ⊢; push_cast at this; rw [mul_div_assoc, div_self ZR_pos.ne'] at this
        linarith
      rw [FI.toR_max]
      refine max_le ?_ hZ
      simp only [rExactEx, Ex.eval, List.getD_cons_zero] at this
      rw [hr.exact_one_two (toR X) hX1 hx2] at hmono
      push_cast at this
      linarith [this.1]
    · exact hZ
  · rw [FI.toR_max]
    refine max_le ?_ hZ
    rcases RT.find_spec t (X / ZI).toNat ZI with h | ⟨g, hg, hk, hv⟩
    · rw [h]; exact hZ
    · rw [hv]
      obtain ⟨hg2, -, har⟩ := ht g hg
      have hk' : (g.1 : ℝ) ≤ toR X := by
        have h1 : ((g.1 : ℕ) : ℤ) ≤ X / ZI := by
          have : 0 ≤ X / ZI := Int.ediv_nonneg (by linarith [ZI_pos]) ZI_pos.le
          omega
        have h2' : ((X / ZI : ℤ) : ℝ) ≤ toR X := by
          have := fdiv_le (a := X) ZI_pos
          exact this
        have : ((g.1 : ℤ) : ℝ) ≤ ((X / ZI : ℤ) : ℝ) := by exact_mod_cast h1
        push_cast at this
        linarith
      have hg1 : (1 : ℝ) ≤ g.1 := by
        have : (2 : ℝ) ≤ g.1 := by exact_mod_cast hg2
        linarith
      exact har.trans ((hr.mono (Set.mem_Ici.mpr hg1) (Set.mem_Ici.mpr hX1) hk').trans hmono)

lemma deltaF_mem (X : ℤ) : 0 < deltaF X ∧ deltaF X < 1 := by
  unfold deltaF; split_ifs <;> norm_num

lemma le_rUpF {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {X h : ℤ} (hh : rUpF X = some h)
    {u : ℝ} (hu1 : 1 ≤ u) (hu : u ≤ toR X) : r u ≤ toR h := by
  have hx1 : (1 : ℝ) ≤ toR X := le_trans hu1 hu
  have hmono : r u ≤ r (toR X) := hr.mono (Set.mem_Ici.mpr hu1) (Set.mem_Ici.mpr hx1) hu
  unfold rUpF at hh
  split_ifs at hh with h2
  · simp only [Option.map_eq_some_iff] at hh
    obtain ⟨I, hI, rfl⟩ := hh
    have := feval_sound rExactEx [toR X] _ I (List.Forall₂.cons (mem_pt X) List.Forall₂.nil) hI
    have hx2 : toR X ≤ 2 := by
      have : toR X ≤ toR (2 * ZI) := toR_le_toR.mpr h2
      unfold toR at this ⊢; push_cast at this; rw [mul_div_assoc, div_self ZR_pos.ne'] at this
      linarith
    rw [hr.exact_one_two (toR X) hx1 hx2] at hmono
    simp only [rExactEx, Ex.eval, List.getD_cons_zero] at this
    push_cast at this
    linarith [this.2]
  · simp only [Option.map_eq_some_iff] at hh
    obtain ⟨I, hI, rfl⟩ := hh
    have := feval_sound (rUpEx (deltaF X)) [toR X] _ I
      (List.Forall₂.cons (mem_pt X) List.Forall₂.nil) hI
    simp only [rUpEx, Ex.eval, List.getD_cons_zero] at this
    have hx2 : (2 : ℝ) ≤ toR X := by
      have : toR (2 * ZI) < toR X := toR_lt_toR.mpr (not_le.mp h2)
      unfold toR at this ⊢; push_cast at this; rw [mul_div_assoc, div_self ZR_pos.ne'] at this
      linarith
    obtain ⟨hd0, hd1⟩ := deltaF_mem X
    have hup := hr.upper (toR X) (deltaF X) hx2 (by exact_mod_cast hd0) (by exact_mod_cast hd1)
    push_cast at this
    linarith [this.2]

theorem rEncF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {t : RT} (ht : TabOKF r t)
    {ua ub : ℤ} {I : FI} (h : rEncF t ua ub = some I) {u : ℝ} (hua : toR ua ≤ u)
    (hub : u ≤ toR ub) : FI.Mem (r u) I := by
  unfold rEncF at h
  split_ifs at h with h1
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  have h1' : (1 : ℝ) ≤ toR ua := by rw [← toR_ZI]; exact toR_le_toR.mpr h1
  exact ⟨rLowF_le hr ht h1 hua, le_rUpF hr hq (le_trans h1' hua) hub⟩

end BSCert.FX
