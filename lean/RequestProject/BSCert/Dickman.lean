module

public import RequestProject.BSCert.Expr

/-!
# Enclosures of the Dickman ratio `r = -ρ'/ρ`

Dickman's function is not in Mathlib, so the facts about `r` that the certificate uses are
taken as hypotheses, collected in `DickmanRatioFacts` (these are (R2)–(R4) of the paper, and
the explicit formula on `[1, 2]`):

* (R2) `r` is non-decreasing on `[1, ∞)`;
* on `[1, 2]`, `r(x) = 1/(x (1 - log x))`;
* (R3) `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})` for `v ≥ 3`;
* (R4) `r(x) ≤ log((x+1)/δ)/(1-δ)` for `x ≥ 2`, `0 < δ < 1`.

(Dickman's function is now constructed in `DickmanFn.lean`, and `DickmanCert.lean` proves
`DickmanRatioFacts Dickman.ratio`, so these hypotheses hold for the true Dickman ratio.)

From these we compute, as the scripts do,
* `r_low`: a table of lower bounds for `r(n)`, `n ≥ 2`, obtained by iterating (R3) from
  `r(2) = 1/(2 - 2 log 2)`;
* `r_up`: the bound (R4) for a suitable `δ`, or the exact formula on `[1, 2]`;
and prove that `rEnc ua ub` encloses `r(u)` for every `u ∈ [ua, ub]`.

For speed, the table iterates `a ↦ a/(1-L)` where `L ≤ e^{-a}` is propagated by
`L' = L (1 - (a' - a)) ≤ e^{-a'}` (using `1 - d ≤ e^{-d}`), so no exponential is evaluated
inside the loop. This still gives certified lower bounds, because `t ↦ t/(1-e^{-t})` is
increasing (`div_one_sub_exp_neg_mono`, a convexity argument).
-/

@[expose] public section

namespace BSCert

/-- The facts about the Dickman ratio `r(v) = -ρ'(v)/ρ(v)` used by the certificate
(paper, Section 5.2, "Facts on Dickman's function", (R2)–(R4)). -/
structure DickmanRatioFacts (r : ℝ → ℝ) : Prop where
  /-- (R2) `r` is non-decreasing on `[1, ∞)`. -/
  mono : MonotoneOn r (Set.Ici 1)
  /-- On `[1, 2]`, `r(x) = 1/(x (1 - log x))`. -/
  exact_one_two : ∀ x : ℝ, 1 ≤ x → x ≤ 2 → r x = 1 / (x * (1 - Real.log x))
  /-- (R3) `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})`. -/
  recursion : ∀ v : ℝ, 3 ≤ v → r (v - 1) / (1 - Real.exp (-r (v - 1))) ≤ r v
  /-- (R4) `r(x) ≤ log((x+1)/δ)/(1-δ)` for `0 < δ < 1`. -/
  upper : ∀ x δ : ℝ, 2 ≤ x → 0 < δ → δ < 1 → r x ≤ Real.log ((x + 1) / δ) / (1 - δ)

/-- `t ↦ t/(1 - e^{-t})` is non-decreasing on `(0, ∞)`. -/
lemma div_one_sub_exp_neg_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a / (1 - Real.exp (-a)) ≤ b / (1 - Real.exp (-b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hea : 0 < 1 - Real.exp (-a) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha); linarith
  have heb : 0 < 1 - Real.exp (-b) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb); linarith
  -- convexity: e^{-a} ≤ (a/b) e^{-b} + (1 - a/b)
  have hconv := convexOn_exp.2 (Set.mem_univ (-b)) (Set.mem_univ 0)
    (div_nonneg ha.le hb.le) (sub_nonneg.mpr ((div_le_one hb).mpr hab))
    (by ring : a / b + (1 - a / b) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have e1 : a / b * -b = -a := by field_simp
  rw [e1] at hconv
  rw [div_le_div_iff₀ hea heb]
  have : a / b * (1 - Real.exp (-b)) ≤ 1 - Real.exp (-a) := by nlinarith
  have := mul_le_mul_of_nonneg_left this hb.le
  calc a * (1 - Real.exp (-b)) = b * (a / b * (1 - Real.exp (-b))) := by field_simp
    _ ≤ b * (1 - Real.exp (-a)) := this

lemma DickmanRatioFacts.one_le {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ r x := by
  have h1 : r 1 = 1 := by rw [hr.exact_one_two 1 le_rfl (by norm_num)]; simp
  have := hr.mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  linarith

/-! ## The table `r_low` -/

/-- `1/(x (1 - log x))` (the exact formula on `[1,2]`), as an expression in `var 0`. -/
def rExactEx : Ex := .div (.cst 1) (.mul (.var 0) (.sub (.cst 1) (.log (.var 0))))

/-- `log((x+1)/δ)/(1-δ)`, as an expression in `var 0`. -/
def rUpEx (δ : ℚ) : Ex := .div (.log (.div (.add (.var 0) (.cst 1)) (.cst δ))) (.cst (1 - δ))

/-- `e^{-t}`, as an expression in `var 0`. -/
def expNegEx : Ex := .exp (.neg (.var 0))

/-- Starting value: a lower bound for `r(2) = 1/(2 - 2 log 2)` (or `1`). -/
def rl2 : ℚ :=
  match Ex.iLo rExactEx [Itv.pt 2] with
  | some q => if 1 ≤ q then q else 1
  | none => 1

/-- Starting value of the companion bound `L ≤ e^{-a}`. -/
def rl2L : ℚ :=
  match Ex.iLo expNegEx [Itv.pt rl2] with
  | some q => max q 0
  | none => 0

/-- One step of the `r_low` recursion. -/
def rlStep (p : ℚ × ℚ) : ℚ × ℚ :=
  let a := p.1
  let L := p.2
  if 0 < a ∧ 0 ≤ L ∧ L < 1 then
    let a' := max a (rdn (a / (1 - L)))
    if a' - a ≤ 1 / 4096 then (a', max 0 (rdn (L * (1 - (a' - a)))))
    else (a', match Ex.iLo expNegEx [Itv.pt a'] with
      | some q => max q 0
      | none => 0)
  else (a, 0)

/-- The sequence of pairs; `(rlSeq n).1 ≤ r(n+2)`. -/
def rlSeq : ℕ → ℚ × ℚ
  | 0 => (rl2, rl2L)
  | n + 1 => rlStep (rlSeq n)

lemma rl2_spec {r : ℝ → ℝ} (hr : DickmanRatioFacts r) : 1 ≤ rl2 ∧ (rl2 : ℝ) ≤ r 2 := by
  have h1 := hr.one_le (x := 2) (by norm_num)
  unfold rl2
  split
  · rename_i q hq
    split_ifs with h
    · refine ⟨h, ?_⟩
      have := Ex.iLo_sound (env := [(2 : ℚ)]) (List.Forall₂.cons (Itv.mem_pt 2) List.Forall₂.nil) hq
      rw [hr.exact_one_two 2 (by norm_num) le_rfl]
      simpa [rExactEx, Ex.eval] using this
    · exact ⟨le_rfl, by simpa using h1⟩
  · exact ⟨le_rfl, by simpa using h1⟩

lemma rl2L_spec : 0 ≤ rl2L ∧ (rl2L : ℝ) ≤ Real.exp (-(rl2 : ℝ)) := by
  unfold rl2L
  split
  · rename_i q hq
    have := Ex.iLo_sound (env := [(rl2 : ℝ)])
      (List.Forall₂.cons (Itv.mem_pt rl2) List.Forall₂.nil) hq
    refine ⟨le_max_right _ _, ?_⟩
    push_cast
    exact max_le (by simpa [expNegEx, Ex.eval] using this) (Real.exp_pos _).le
  · exact ⟨le_rfl, by simp [(Real.exp_pos _).le]⟩

/-- Invariant of the recursion. -/
lemma rlSeq_spec {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (n : ℕ) :
    1 ≤ (rlSeq n).1 ∧ ((rlSeq n).1 : ℝ) ≤ r (n + 2) ∧ 0 ≤ (rlSeq n).2 ∧
      ((rlSeq n).2 : ℝ) ≤ Real.exp (-(((rlSeq n).1 : ℚ) : ℝ)) := by
  induction n with
  | zero =>
    simp only [rlSeq, CharP.cast_eq_zero, zero_add]
    exact ⟨(rl2_spec hr).1, (rl2_spec hr).2, rl2L_spec.1, rl2L_spec.2⟩
  | succ n ih =>
    obtain ⟨ha1, har, hL0, hLe⟩ := ih
    set a := (rlSeq n).1
    set L := (rlSeq n).2
    have hmono : r ((n : ℝ) + 2) ≤ r ((n : ℝ) + 1 + 2) :=
      hr.mono (Set.mem_Ici.mpr (by linarith [n.cast_nonneg (α := ℝ)]))
        (Set.mem_Ici.mpr (by linarith [n.cast_nonneg (α := ℝ)])) (by linarith)
    simp only [rlSeq]
    rw [show ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 1 + 2 by push_cast; ring]
    unfold rlStep
    simp only
    by_cases hc : 0 < a ∧ 0 ≤ L ∧ L < 1
    swap
    · rw [if_neg hc]
      exact ⟨ha1, le_trans har hmono, le_rfl, by simp [(Real.exp_pos _).le]⟩
    rw [if_pos hc]
    · obtain ⟨ha0, -, hL1⟩ := hc
      have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
      have hL1' : (L : ℝ) < 1 := by exact_mod_cast hL1
      -- the new lower bound
      have hgr : (a : ℝ) / (1 - Real.exp (-(a : ℝ))) ≤ r ((n : ℝ) + 1 + 2) := by
        have h3 := hr.recursion ((n : ℝ) + 1 + 2) (by linarith [n.cast_nonneg (α := ℝ)])
        have e : (n : ℝ) + 1 + 2 - 1 = (n : ℝ) + 2 := by ring
        rw [e] at h3
        exact le_trans (div_one_sub_exp_neg_mono ha0' har) h3
      have hdiv : (a : ℝ) / (1 - L) ≤ (a : ℝ) / (1 - Real.exp (-(a : ℝ))) := by
        have hpos : 0 < 1 - Real.exp (-(a : ℝ)) := by
          have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0'); linarith
        exact div_le_div_of_nonneg_left ha0'.le hpos (by linarith)
      set a' := max a (rdn (a / (1 - L))) with ha'
      have ha'r : (a' : ℝ) ≤ r ((n : ℝ) + 1 + 2) := by
        rw [ha']; push_cast
        refine max_le (le_trans har hmono) ?_
        apply rdn_le_real
        push_cast
        exact le_trans hdiv hgr
      have haa' : a ≤ a' := le_max_left _ _
      by_cases hsmall : a' - a ≤ 1 / 4096
      swap
      · rw [if_neg hsmall]
        refine ⟨le_trans ha1 haa', ha'r, ?_⟩
        split
        · rename_i q hq
          have := Ex.iLo_sound (env := [(a' : ℝ)])
            (List.Forall₂.cons (Itv.mem_pt a') List.Forall₂.nil) hq
          refine ⟨le_max_right _ _, ?_⟩
          push_cast
          exact max_le (by simpa [expNegEx, Ex.eval] using this) (Real.exp_pos _).le
        · exact ⟨le_rfl, by simp [(Real.exp_pos _).le]⟩
      rw [if_pos hsmall]
      refine ⟨le_trans ha1 haa', ha'r, le_max_left _ _, ?_⟩
      push_cast
      refine max_le (Real.exp_pos _).le ?_
      apply rdn_le_real
      push_cast
      -- L (1 - d) ≤ e^{-a} e^{-d} = e^{-a'}
      have hd : (1 : ℝ) - (a' - a) ≤ Real.exp (-((a' : ℝ) - a)) := by
        have := Real.add_one_le_exp (-((a' : ℝ) - a)); linarith
      have hL0' : (0 : ℝ) ≤ L := by exact_mod_cast hL0
      have e2 : Real.exp (-(a' : ℝ)) = Real.exp (-(a : ℝ)) * Real.exp (-((a' : ℝ) - a)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e2]
      rcases le_total 0 ((1 : ℝ) - (a' - a)) with h0 | h0
      · exact mul_le_mul hLe hd h0 (Real.exp_pos _).le
      · have : (L : ℝ) * (1 - (a' - a)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hL0' h0
        exact le_trans this (by positivity)

/-- Build the table `#[(rlSeq 0).1, …]` of length `k + acc.size`. -/
def buildTable : ℕ → ℚ × ℚ → Array ℚ → Array ℚ
  | 0, _, acc => acc
  | k + 1, p, acc => buildTable k (rlStep p) (acc.push p.1)

lemma buildTable_spec : ∀ (k : ℕ) (m : ℕ) (acc : Array ℚ), acc.size = m →
    (∀ i (h : i < acc.size), acc[i] = (rlSeq i).1) →
    ∀ i (h : i < (buildTable k (rlSeq m) acc).size),
      (buildTable k (rlSeq m) acc)[i] = (rlSeq i).1 := by
  intro k
  induction k with
  | zero => intro m acc _ hacc i h; exact hacc i h
  | succ k ih =>
    intro m acc hsz hacc i h
    have := ih (m + 1) (acc.push (rlSeq m).1) (by simp [hsz]) ?_ i
    · simpa [buildTable, rlSeq] using this h
    · intro j hj
      rw [Array.getElem_push]
      split_ifs with hj'
      · exact hacc j hj'
      · simp at hj; have : j = m := by omega
        subst this; rfl

/-- The table of `r_low` values: entry `i` is a lower bound for `r(i + 2)`. -/
def rlowTable (N : ℕ) : Array ℚ := buildTable N (rlSeq 0) #[]

/-- A table is valid if entry `i` is a lower bound for `r(i + 2)`. -/
def TableOK (r : ℝ → ℝ) (tbl : Array ℚ) : Prop :=
  ∀ i (h : i < tbl.size), ((tbl[i] : ℚ) : ℝ) ≤ r ((i : ℝ) + 2)

lemma rlowTable_ok {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (N : ℕ) : TableOK r (rlowTable N) := by
  intro i h
  have key : (rlowTable N)[i] = (rlSeq i).1 := buildTable_spec N 0 #[] rfl (by simp) i h
  rw [key]
  exact (rlSeq_spec hr i).2.1

/-! ## Enclosure of `r` on an interval -/

/-- Lower bound for `r` on `[x, ∞)` (for `x ≥ 1`). -/
def rLow (tbl : Array ℚ) (x : ℚ) : ℚ :=
  if x < 2 then
    match Ex.iLo rExactEx [Itv.pt x] with
    | some q => max q 1
    | none => 1
  else
    let n := (⌊x⌋.toNat - 2)
    if h : 0 < tbl.size then max (tbl[min n (tbl.size - 1)]'(by omega)) 1 else 1

/-- The candidate values of `δ` in (R4) (as in the scripts). -/
def deltas : List ℚ := [1/20, 1/10, 3/20, 1/5, 3/10, 2/5, 1/2]

/-- Choose `δ` heuristically (floating point; only affects sharpness). -/
def chooseDelta (x : ℚ) : ℚ :=
  let xf := x.toFloat
  let score (d : ℚ) : Float := Float.log ((xf + 1) / d.toFloat) / (1 - d.toFloat)
  (deltas.foldl (fun (best : ℚ × Float) d =>
      let s := score d; if s < best.2 then (d, s) else best) (1/2, score (1/2))).1

/-- Upper bound for `r` on `[1, x]`. -/
def rUp (x : ℚ) : Option ℚ :=
  if x ≤ 2 then Ex.iHi rExactEx [Itv.pt x]
  else
    let d := chooseDelta x
    if 0 < d ∧ d < 1 then Ex.iHi (rUpEx d) [Itv.pt x] else none

/-- Enclosure of `r(u)` for `u ∈ [ua, ub]`. -/
def rEnc (tbl : Array ℚ) (ua ub : ℚ) : Option Itv :=
  if 1 ≤ ua then (rUp ub).map fun h => ⟨rLow tbl ua, h⟩ else none

lemma rLow_le {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    {x : ℚ} (hx : 1 ≤ x) {u : ℝ} (hu : (x : ℝ) ≤ u) : ((rLow tbl x : ℚ) : ℝ) ≤ r u := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hu1 : 1 ≤ u := le_trans hx' hu
  have hmono : r x ≤ r u := hr.mono (Set.mem_Ici.mpr hx') (Set.mem_Ici.mpr hu1) hu
  have hone := hr.one_le hu1
  unfold rLow
  dsimp only
  split_ifs with h2 htb
  · split
    · rename_i q hq
      have := Ex.iLo_sound (env := [(x : ℝ)]) (List.Forall₂.cons (Itv.mem_pt x)
        List.Forall₂.nil) hq
      have hx2 : (x : ℝ) ≤ 2 := by exact_mod_cast h2.le
      · push_cast
        refine max_le ?_ hone
        simp only [rExactEx, Ex.eval, List.getD_cons_zero] at this
        rw [hr.exact_one_two x hx' hx2] at hmono
        push_cast at this
        linarith
    · simpa using hone
  · push_cast
    refine max_le ?_ hone
    set n := ⌊x⌋.toNat - 2
    set j := min n (tbl.size - 1)
    have hj := ht j (by omega)
    have hfl : (2 : ℤ) ≤ ⌊x⌋ := by
      rw [Int.le_floor]; push_cast; exact_mod_cast not_lt.mp h2
    have hjle : (j : ℝ) + 2 ≤ x := by
      have h1 : (j : ℤ) + 2 ≤ ⌊x⌋ := by omega
      have h2' : ((⌊x⌋ : ℤ) : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
      have : ((j : ℤ) : ℝ) + 2 ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this
      linarith
    have : r ((j : ℝ) + 2) ≤ r u :=
      hr.mono (Set.mem_Ici.mpr (by linarith [j.cast_nonneg (α := ℝ)])) (Set.mem_Ici.mpr hu1)
        (le_trans hjle hu)
    linarith
  · simpa using hone

lemma le_rUp {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {x q : ℚ} (h : rUp x = some q)
    {u : ℝ} (hu1 : 1 ≤ u) (hu : u ≤ (x : ℝ)) : r u ≤ (q : ℝ) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans hu1 hu
  have hmono : r u ≤ r x := hr.mono (Set.mem_Ici.mpr hu1) (Set.mem_Ici.mpr hx1) hu
  unfold rUp at h
  dsimp only at h
  split_ifs at h with h2 hd
  · have := Ex.iHi_sound (env := [(x : ℝ)]) (List.Forall₂.cons (Itv.mem_pt x)
      List.Forall₂.nil) h
    have hx2 : (x : ℝ) ≤ 2 := by exact_mod_cast h2
    rw [hr.exact_one_two x hx1 hx2] at hmono
    simp only [rExactEx, Ex.eval, List.getD_cons_zero] at this
    push_cast at this
    linarith
  · have := Ex.iHi_sound (env := [(x : ℝ)]) (List.Forall₂.cons (Itv.mem_pt x)
      List.Forall₂.nil) h
    simp only [rUpEx, Ex.eval, List.getD_cons_zero] at this
    have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast (not_le.mp h2).le
    have hd0 : (0 : ℝ) < chooseDelta x := by exact_mod_cast hd.1
    have hd1 : ((chooseDelta x : ℚ) : ℝ) < 1 := by exact_mod_cast hd.2
    have hup := hr.upper x (chooseDelta x) hx2 hd0 hd1
    push_cast at this
    linarith

theorem rEnc_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    {ua ub : ℚ} {I : Itv} (h : rEnc tbl ua ub = some I) {u : ℝ} (hua : (ua : ℝ) ≤ u)
    (hub : u ≤ (ub : ℝ)) : Itv.Mem (r u) I := by
  unfold rEnc at h
  split_ifs at h with h1
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  have h1' : (1 : ℝ) ≤ ua := by exact_mod_cast h1
  exact ⟨rLow_le hr ht h1 hua, le_rUp hr hq (le_trans h1' hua) hub⟩

end BSCert
