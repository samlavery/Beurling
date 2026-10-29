module

public import RequestProject.Beurling.Queue6.Family

/-!
# `T(x) ≤ 3x` on the good event (Lemma 3.4, from Lemma 6.26 on `Good(<t)`)

The target of the construction splits on `[X₀, ∞)` as `T = X₀ + J + C` (`targetD_split`), with
`J(x) = Ψ(x, X₀) - Ψ(X₀, X₀) + #(A ∩ [1, x])` and `C(x) ≤ 1.01 (x - X₀)` (`contD_upper_log`).
Since `Ψ(x, X₀) ≤ x`, the bound `T(x) ≤ 3x` only needs `#(A ∩ [1, x]) ≤ x/2`.

There is no sure bound on the absorbed count: it is controlled in the paper by **Lemma 6.26**
(pointwise sparsity of `Abs`, "`#(Abs ∩ [u, u+h]) ≤ h L^{-4}` on `Good(<t)` for every
`t ≥ t_u := 9u/L^{11} + H(u)`"), which Lemma 3.4 (target error) assumes ("On the event of
Lemma 6.26"). Lemma 6.26 on `Good(<t)` is not among the events or results of the formal
family (the formal Lemma 6.26, `Construction.lemma626_construction`, uses (HBS) for the realised
system at every height). It is isolated here as the named hypothesis `Lemma626Good`.

* `countA_le_of_windows` : covering `[X₀, x]` by the windows `[u, u + u^b]`, the window bound
  `≤ u^b/4` gives `#(A ∩ [1, x]) ≤ (x + x^b)/4` when `A` has no element `≤ X₀`;
* `T_le_three_of_lemma626` : `T(x) ≤ 3x` for `X₀ ≤ x ≤ t` on `Good(<t)` (`G0`);
* `tbound_of_lemma626` : the field `tbound` of `Queue6.QueueInputs`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **Lemma 6.26 on `Good(<t)`** (pointwise sparsity of `Abs`, §6.8; named hypothesis): for
`u ≥ X₀`, on `Good(<t)` with `t ≥ t_u = 9u/(log u)^{11} + H(u)`,
`#(Abs ∩ [u, u + u^{θ/2}]) ≤ u^{θ/2} (log u)^{-4}`. -/
def Lemma626Good (θ : ℝ) (X₀ : ℕ) (D : Sec5Family) : Prop :=
  ∀ (t : ℕ) (u : ℝ) (ω : JitterΩ), (X₀ : ℝ) ≤ u →
    9 * u / Real.log u ^ 11 + capH X₀ u ≤ t → ω ∈ G0 θ X₀ D t →
      (localCountA (absSet X₀ (DF θ X₀ ω)) u (u + u ^ (θ / 2)) : ℝ) ≤
        u ^ (θ / 2) / Real.log u ^ 4

/-- **The covering count.** If `A` is locally finite with no element in `[1, X]`, and every window
`[u, u + u^b]` with `X ≤ u < x` holds at most `u^b/4` points of `A`, then
`#(A ∩ [1, x]) ≤ (x + x^b - X)/4`. -/
theorem countA_le_of_windows {A : Set ℝ} (hA : LocFin A) {X b x : ℝ} (hX : 1 ≤ X) (hb : 0 ≤ b)
    (hlow : A ∩ Icc 1 X = ∅)
    (hwin : ∀ u, X ≤ u → u < x → (localCountA A u (u + u ^ b) : ℝ) ≤ u ^ b / 4)
    (hx : X ≤ x) :
    countA A x ≤ (x + x ^ b - X) / 4 := by
  set w : ℕ → ℝ := fun i => Nat.rec X (fun _ v => v + v ^ b) i with hw
  have hw0 : w 0 = X := rfl
  have hws : ∀ i, w (i + 1) = w i + w i ^ b := fun i => rfl
  have hwX : ∀ i : ℕ, X + i ≤ w i := by
    intro i
    induction i with
    | zero => simp [hw0]
    | succ i ih =>
      rw [hws]
      have h1 : 1 ≤ w i ^ b := Real.one_le_rpow (by linarith) hb
      push_cast; linarith
  have key : ∀ i, (∀ j < i, w j < x) → ((A ∩ Icc 1 (w i)).ncard : ℝ) ≤ (w i - X) / 4 := by
    intro i
    induction i with
    | zero => intro _; rw [hw0, hlow]; simp
    | succ i ih =>
      intro hj
      have hih := ih (fun j hj' => hj j (by omega))
      have hwi := hj i (by omega)
      have hsub : A ∩ Icc 1 (w (i + 1)) ⊆
          (A ∩ Icc 1 (w i)) ∪ (A ∩ Icc (w i) (w i + w i ^ b)) := by
        intro a ⟨ha, ha1, ha2⟩
        by_cases hai : a ≤ w i
        · exact Or.inl ⟨ha, ha1, hai⟩
        · push_neg at hai; exact Or.inr ⟨ha, hai.le, by rw [← hws]; exact ha2⟩
      have hfin : ((A ∩ Icc 1 (w i)) ∪ (A ∩ Icc (w i) (w i + w i ^ b))).Finite :=
        (hA.finite_Icc _ _).union (hA.finite_Icc _ _)
      have h1 := (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
      have h2 := hwin (w i) (by linarith [hwX i]) hwi
      unfold localCountA at h2
      have h1' : ((A ∩ Icc 1 (w (i + 1))).ncard : ℝ) ≤
          ((A ∩ Icc 1 (w i)).ncard : ℝ) + ((A ∩ Icc (w i) (w i + w i ^ b)).ncard : ℝ) := by
        exact_mod_cast h1
      rw [hws]; linarith
  have hex : ∃ i, x ≤ w i := by
    obtain ⟨n, hn⟩ := exists_nat_ge (x - X)
    exact ⟨n, by linarith [hwX n]⟩
  classical
  set K := Nat.find hex with hK
  have hKx : x ≤ w K := Nat.find_spec hex
  have hlt : ∀ j < K, w j < x := fun j hj => by
    have := Nat.find_min hex hj; push_neg at this; exact this
  have hc := key K hlt
  have hmono : countA A x ≤ ((A ∩ Icc 1 (w K)).ncard : ℝ) := by
    unfold countA
    exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_right _
      (Set.Icc_subset_Icc le_rfl hKx)) (hA.finite_Icc _ _)
  rcases Nat.eq_zero_or_eq_succ_pred K with h0 | hs
  · rw [h0, hw0] at hc
    have : 0 ≤ x ^ b := Real.rpow_nonneg (by linarith) b
    rw [h0, hw0] at hmono
    linarith
  · set k := K.pred
    have hk := hlt k (by omega)
    have hwK : w K = w k + w k ^ b := by rw [hs]
    have hwk0 : 0 ≤ w k := by linarith [hwX k]
    have hp : w k ^ b ≤ x ^ b := Real.rpow_le_rpow hwk0 hk.le hb
    linarith

/-- `Ψ(x, X₀) ≤ x` for `x ≥ 0`. -/
lemma smoothCount_le_self (X₀ : ℕ) {x : ℝ} (hx : 0 ≤ x) : (Rankin.smoothCount X₀ x : ℝ) ≤ x := by
  unfold Rankin.smoothCount
  have hsub : Nat.smoothNumbersUpTo ⌊x⌋₊ X₀ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro d hd
    rw [Nat.mem_smoothNumbersUpTo] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hd.2.1, hd.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  have h2 : ((Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).card : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  exact h2.trans (Nat.floor_le hx)

/-- **`T(x) ≤ 3x` on `Good(<t)`** for `X₀ ≤ x ≤ t`, from Lemma 6.26 on `Good(<t)`
(Lemma 3.4 with the crude constant `3`). -/
theorem T_le_three_of_lemma626 (hc : Cond θ X₀) {D : Sec5Family} (hL : Lemma626Good θ X₀ D)
    {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) {x : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hxt : x ≤ t) : (Mcl θ X₀ ω).T x ≤ 3 * x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hstd := hc.std ω
  set Dd := DF θ X₀ ω with hDd
  have hDM : Dd = DM hstd.limModel (Ucl ω) := by rw [hDd, DF, Mcl_eq hc]
  have hT : (Mcl θ X₀ ω).T x = targetD θ X₀ Dd x := by
    rw [Mcl_eq hc, hstd.limModel_T_eq x, hDM]
  rw [hT, targetD_split θ Dd hx]
  have hLF : LocFinD Dd := by rw [hDM]; exact locFinD_DM hc.hX hstd.hU _
  -- the continuous part
  have hC := contD_upper_log hc.hθ hc.hX Dd hLF le_rfl hx
  rw [contD_at] at hC
  have hlX : 10 ^ 8 ≤ Real.log X₀ := hc.hX
  have hC' : contD θ X₀ Dd x ≤ 1.01 * (x - X₀) := by
    have h1 : 0.02 / Real.log X₀ ≤ 0.01 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : 0 ≤ x - X₀ := by linarith
    nlinarith
  -- the absorbed count
  set A := absSet X₀ Dd with hA
  have hAfin : LocFin A := absSet_locFin hLF
  have hlow : A ∩ Icc 1 (X₀ : ℝ) = ∅ := by
    have h0 := hstd.countA_X₀
    rw [← hDM] at h0
    unfold countA at h0
    have h0' : (A ∩ Icc 1 (X₀ : ℝ)).ncard = 0 := by exact_mod_cast h0
    exact (Set.ncard_eq_zero (hAfin.finite_Icc _ _)).mp h0'
  have hb0 : 0 ≤ θ / 2 := by linarith [hc.hθ.1]
  have hb1 : θ / 2 ≤ 1 := by linarith [hc.hθ.2]
  have hwin : ∀ u, (X₀ : ℝ) ≤ u → u < x →
      (localCountA A u (u + u ^ (θ / 2)) : ℝ) ≤ u ^ (θ / 2) / 4 := by
    intro u hu hux
    obtain ⟨hLu, -, -⟩ := logs_of_ge hX0 hc.hX hu
    have h4 := four_capH_le hX0 hc.hX hu
    have hu0 : 0 < u := by linarith
    have htu : 9 * u / Real.log u ^ 11 + capH X₀ u ≤ t := by
      have h11 : 18 ≤ Real.log u ^ 11 := by
        have : (10 ^ 8 : ℝ) ≤ Real.log u ^ 11 :=
          hLu.trans (le_self_pow₀ (by linarith) (by norm_num))
        linarith
      have : 9 * u / Real.log u ^ 11 ≤ u / 2 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have h := hL t u ω hu htu hω
    have hp : 0 ≤ u ^ (θ / 2) := Real.rpow_nonneg hu0.le _
    have h44 : (4 : ℝ) ≤ Real.log u ^ 4 := by
      have : (10 ^ 8 : ℝ) ≤ Real.log u ^ 4 :=
        hLu.trans (le_self_pow₀ (by linarith) (by norm_num))
      linarith
    exact h.trans (div_le_div_of_nonneg_left hp (by norm_num) h44)
  have hcnt := countA_le_of_windows hAfin hX1.le hb0 hlow hwin hx
  have hxb : x ^ (θ / 2) ≤ x := by
    conv_rhs => rw [← Real.rpow_one x]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hb1
  -- the smooth count
  have hS := smoothCount_le_self X₀ (by linarith : (0 : ℝ) ≤ x)
  have hS0 : (0 : ℝ) ≤ Rankin.smoothCount X₀ (X₀ : ℝ) := Nat.cast_nonneg _
  unfold jumpD jumpPart
  rw [← hA]
  linarith

/-- **The field `tbound` of `Queue6.QueueInputs`** (Lemma 3.4 on the good event), from Lemma 6.26
on `Good(<t)`: `T(x) ≤ 3x` up to `2^n X₀/2` holds on all of `Good(< t(tB n))`. -/
theorem tbound_of_lemma626 (hc : Cond θ X₀) {D : Sec5Family} (hL : Lemma626Good θ X₀ D)
    (n : ℕ) : jitterMeasure ((tB (θ := θ) (X₀ := X₀) n)ᶜ ∩ G0 θ X₀ D (ttB X₀ n)) = 0 := by
  have hE : (tB (θ := θ) (X₀ := X₀) n)ᶜ ∩ G0 θ X₀ D (ttB X₀ n) = ∅ := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hnot hω
    apply hnot
    intro x hx hxX
    refine T_le_three_of_lemma626 hc hL hω hx ?_
    unfold ttB
    push_cast
    linarith [Nat.le_ceil (2 ^ n * (X₀ : ℝ) / 2)]
  rw [hE, measure_empty]

end BModel
