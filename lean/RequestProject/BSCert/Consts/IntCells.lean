module

public import RequestProject.BSCert.Transc
public import RequestProject.BSCert.FX.LogQ

/-!
# Certified upper bounds for integrals `∫_a^∞ f(v) dv` with `U = 1 + 2 log v`

On a cell `[p, q]` the integrand is bounded by `P(U)/v²` with `P` a polynomial of degree `≤ 4`
in `U = 1 + 2 log v`. Since `(U^m)/v² = d/dv [-S_m(U)/v]` with
`S_m(U) = ∑_{j ≤ m} 2^j m!/(m-j)! U^{m-j}` (so `S_m - 2 S_m' = U^m`), the integral of the bound is
`N(U_p)/p - N(U_q)/q` with `N = ∑ a_m S_m`. The values `U_p = 1 + 2 log p` at integer points
are enclosed with the certified fixed-point `log` (`FX.logLoQF`, `FX.logHiQF`).
-/

@[expose] public section

namespace BSCert.Consts

open Real MeasureTheory BSCert Set

/-- `U = 1 + 2 log v`. -/
noncomputable def Uf (v : ℝ) : ℝ := 1 + 2 * Real.log v

/-- Coefficients of a polynomial of degree `≤ 4`. -/
structure Co where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ

/-- `P(U) = ∑ a_m U^m`. -/
noncomputable def polyU (c : Co) (U : ℝ) : ℝ :=
  c.a0 + c.a1 * U + c.a2 * U ^ 2 + c.a3 * U ^ 3 + c.a4 * U ^ 4

/-- `N(U) = ∑ a_m S_m(U)`. -/
noncomputable def numU (c : Co) (U : ℝ) : ℝ :=
  c.a0 + c.a1 * (U + 2) + c.a2 * (U ^ 2 + 4 * U + 8) + c.a3 * (U ^ 3 + 6 * U ^ 2 + 24 * U + 48)
    + c.a4 * (U ^ 4 + 8 * U ^ 3 + 48 * U ^ 2 + 192 * U + 384)

/-- The antiderivative `Φ(v) = -N(U(v))/v` of `P(U(v))/v²`. -/
noncomputable def Phi (c : Co) (v : ℝ) : ℝ := -(numU c (Uf v)) / v

lemma hasDerivAt_Phi (c : Co) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (Phi c) (polyU c (Uf v) / v ^ 2) v := by
  have hU : HasDerivAt Uf (2 / v) v := by
    have := ((Real.hasDerivAt_log hv.ne').const_mul 2).const_add 1
    convert! this using 1
  set U := Uf v
  have hN : HasDerivAt (fun x => numU c (Uf x))
      ((c.a1 + c.a2 * (2 * U + 4) + c.a3 * (3 * U ^ 2 + 12 * U + 24)
        + c.a4 * (4 * U ^ 3 + 24 * U ^ 2 + 96 * U + 192)) * (2 / v)) v := by
    have hp : HasDerivAt (fun u : ℝ => numU c u)
        (c.a1 + c.a2 * (2 * U + 4) + c.a3 * (3 * U ^ 2 + 12 * U + 24)
          + c.a4 * (4 * U ^ 3 + 24 * U ^ 2 + 96 * U + 192)) U := by
      unfold numU
      have h1 := hasDerivAt_id U
      have h2 := hasDerivAt_pow 2 U
      have h3 := hasDerivAt_pow 3 U
      have h4 := hasDerivAt_pow 4 U
      have := ((((hasDerivAt_const U (c.a0 : ℝ)).add
        ((h1.add_const 2).const_mul (c.a1 : ℝ))).add
        (((h2.add (h1.const_mul 4)).add_const 8).const_mul (c.a2 : ℝ))).add
        ((((h3.add (h2.const_mul 6)).add (h1.const_mul 24)).add_const 48).const_mul (c.a3 : ℝ))).add
        (((((h4.add (h3.const_mul 8)).add (h2.const_mul 48)).add (h1.const_mul 192)).add_const
          384).const_mul (c.a4 : ℝ))
      convert! this using 1
      norm_num
      ring
    exact hp.comp v hU
  have := hN.neg.div (hasDerivAt_id v) hv.ne'
  unfold Phi
  convert! this using 1
  simp only [id, polyU, numU, Pi.neg_apply]
  field_simp
  ring

lemma continuousOn_polyU_div (c : Co) {s : Set ℝ} (hs : ∀ v ∈ s, 0 < v) :
    ContinuousOn (fun v => polyU c (Uf v) / v ^ 2) s := by
  apply ContinuousOn.div
  · unfold polyU Uf
    have : ContinuousOn Real.log s := Real.continuousOn_log.mono (fun v hv => (hs v hv).ne')
    fun_prop
  · fun_prop
  · intro v hv; exact pow_ne_zero 2 (hs v hv).ne'

/-- One cell: `∫_p^q f ≤ Φ(q) - Φ(p)` when `f ≤ P(U)/v²` on `[p, q]`. -/
lemma cell_le {f : ℝ → ℝ} {c : Co} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hf : ContinuousOn f (Icc p q)) (hb : ∀ v ∈ Icc p q, f v ≤ polyU c (Uf v) / v ^ 2) :
    ∫ v in p..q, f v ≤ Phi c q - Phi c p := by
  have hpos : ∀ v ∈ Icc p q, 0 < v := fun v hv => lt_of_lt_of_le hp hv.1
  have hg : ContinuousOn (fun v => polyU c (Uf v) / v ^ 2) (Icc p q) :=
    continuousOn_polyU_div c hpos
  have hgi : IntervalIntegrable (fun v => polyU c (Uf v) / v ^ 2) volume p q :=
    (hg.mono (by rw [uIcc_of_le hpq])).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => hasDerivAt_Phi c
    (hpos v (by rwa [uIcc_of_le hpq] at hv))) hgi]
  exact intervalIntegral.integral_mono_on hpq
    ((hf.mono (by rw [uIcc_of_le hpq])).intervalIntegrable) hgi hb

/-- Tail: `∫_p^M f ≤ -Φ(p)` for every `M ≥ p`, when `f ≤ P(U)/v²` and `N(U) ≥ 0` on `[p, ∞)`. -/
lemma tail_cell_le {f : ℝ → ℝ} {c : Co} {p : ℝ} (hp : 0 < p) (hf : ContinuousOn f (Ici p))
    (hb : ∀ v, p ≤ v → f v ≤ polyU c (Uf v) / v ^ 2) (hN : ∀ v, p ≤ v → 0 ≤ numU c (Uf v))
    {M : ℝ} (hM : p ≤ M) : ∫ v in p..M, f v ≤ -Phi c p := by
  have h := cell_le hp hM (hf.mono Icc_subset_Ici_self) (fun v hv => hb v hv.1)
  have : Phi c M ≤ 0 := by
    unfold Phi
    have := hN M hM
    have hM0 : 0 < M := lt_of_lt_of_le hp hM
    rw [neg_div]
    have : 0 ≤ numU c (Uf M) / M := div_nonneg this hM0.le
    linarith
  linarith

/-- From bounds on `∫_a^M f` to integrability on `(a, ∞)` and the bound for `∫_a^∞ f`. -/
lemma integral_Ioi_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hnn : ∀ x, a ≤ x → 0 ≤ f x)
    (hcont : ContinuousOn f (Ici a)) (h : ∀ M, b ≤ M → ∫ x in a..M, f x ≤ C) :
    IntegrableOn f (Ioi a) ∧ ∫ x in Ioi a, f x ≤ C := by
  have hloc : ∀ M : ℝ, IntegrableOn f (Ioc a M) := by
    intro M
    rcases le_total a M with haM | haM
    · exact (hcont.mono (Icc_subset_Ici_self)).integrableOn_compact isCompact_Icc |>.mono_set
        Ioc_subset_Icc_self
    · rw [Ioc_eq_empty (not_lt.mpr haM)]; exact integrableOn_empty
  have hint : IntegrableOn f (Ioi a) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := Filter.atTop) (b := id) C a
      hloc Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop b] with M hM
    have hM' : a ≤ M := le_trans hab hM
    have e : ∫ x in a..id M, ‖f x‖ = ∫ x in a..M, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [id] at hx
      rw [uIcc_of_le hM'] at hx
      simp [Real.norm_eq_abs, abs_of_nonneg (hnn x hx.1)]
    rw [e]; exact h M hM
  refine ⟨hint, ?_⟩
  have ht := intervalIntegral_tendsto_integral_Ioi a hint Filter.tendsto_id
  apply le_of_tendsto ht
  filter_upwards [Filter.eventually_ge_atTop b] with M hM
  exact h M hM

/-! ## Interval evaluation -/

/-- Enclosure of `U_p = 1 + 2 log p` for a positive integer `p`. -/
def UItv (p : ℕ) : Itv := ⟨1 + 2 * FX.logLoQF (p : ℚ), 1 + 2 * FX.logHiQF (p : ℚ)⟩

lemma mem_UItv {p : ℕ} (hp : 0 < p) : Itv.Mem (Uf p) (UItv p) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have h1 := FX.logLoQF_le hp'
  have h2 := FX.le_logHiQF hp'
  push_cast at h1 h2
  constructor <;> simp only [UItv, Uf] <;> push_cast <;> linarith

/-- Interval evaluation of `N`. -/
def numItv (c : Co) (U : Itv) : Itv :=
  let p := Itv.pt
  let U2 := Itv.mul U U
  let U3 := Itv.mul U2 U
  let U4 := Itv.mul U3 U
  Itv.add (Itv.add (Itv.add (Itv.add (p c.a0) (Itv.mul (p c.a1) (Itv.add U (p 2))))
    (Itv.mul (p c.a2) (Itv.add (Itv.add U2 (Itv.mul (p 4) U)) (p 8))))
    (Itv.mul (p c.a3) (Itv.add (Itv.add (Itv.add U3 (Itv.mul (p 6) U2)) (Itv.mul (p 24) U)) (p 48))))
    (Itv.mul (p c.a4) (Itv.add (Itv.add (Itv.add (Itv.add U4 (Itv.mul (p 8) U3))
      (Itv.mul (p 48) U2)) (Itv.mul (p 192) U)) (p 384)))

lemma mem_numItv (c : Co) {x : ℝ} {U : Itv} (hx : Itv.Mem x U) : Itv.Mem (numU c x) (numItv c U) := by
  have h2 := Itv.mem_mul hx hx
  have h3 := Itv.mem_mul h2 hx
  have h4 := Itv.mem_mul h3 hx
  have pt := fun q : ℚ => Itv.mem_pt q
  have e : numU c x = c.a0 + c.a1 * (x + (2 : ℚ)) + c.a2 * (x * x + (4 : ℚ) * x + (8 : ℚ))
      + c.a3 * (x * x * x + (6 : ℚ) * (x * x) + (24 : ℚ) * x + (48 : ℚ))
      + c.a4 * (x * x * x * x + (8 : ℚ) * (x * x * x) + (48 : ℚ) * (x * x)
        + (192 : ℚ) * x + (384 : ℚ)) := by
    unfold numU; push_cast; ring
  rw [e]
  unfold numItv
  simp only
  refine Itv.mem_add (Itv.mem_add (Itv.mem_add (Itv.mem_add (pt _) (Itv.mem_mul (pt _)
    (Itv.mem_add hx (pt _)))) (Itv.mem_mul (pt _) (Itv.mem_add (Itv.mem_add h2
    (Itv.mem_mul (pt _) hx)) (pt _)))) (Itv.mem_mul (pt _) (Itv.mem_add (Itv.mem_add
    (Itv.mem_add h3 (Itv.mem_mul (pt _) h2)) (Itv.mem_mul (pt _) hx)) (pt _))))
    (Itv.mem_mul (pt _) (Itv.mem_add (Itv.mem_add (Itv.mem_add (Itv.mem_add h4
    (Itv.mem_mul (pt _) h3)) (Itv.mem_mul (pt _) h2)) (Itv.mem_mul (pt _) hx)) (pt _)))

/-- Upper bound for `Φ(q) - Φ(p) = N(U_p)/p - N(U_q)/q`. -/
def phiDiffHi (c : Co) (p q : ℕ) : ℚ :=
  (numItv c (UItv p)).hi / p - (numItv c (UItv q)).lo / q

lemma Phi_sub_le {c : Co} {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Phi c q - Phi c p ≤ phiDiffHi c p q := by
  have h1 := (mem_numItv c (mem_UItv hp)).2
  have h2 := (mem_numItv c (mem_UItv hq)).1
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold Phi phiDiffHi
  push_cast
  have a1 : numU c (Uf p) / p ≤ ((numItv c (UItv p)).hi : ℝ) / p :=
    div_le_div_of_nonneg_right h1 hp'.le
  have a2 : ((numItv c (UItv q)).lo : ℝ) / q ≤ numU c (Uf q) / q :=
    div_le_div_of_nonneg_right h2 hq'.le
  rw [neg_div, neg_div]
  linarith

/-- Upper bound for `-Φ(p) = N(U_p)/p`. -/
def phiTailHi (c : Co) (p : ℕ) : ℚ := (numItv c (UItv p)).hi / p

lemma neg_Phi_le {c : Co} {p : ℕ} (hp : 0 < p) : -Phi c p ≤ phiTailHi c p := by
  have h1 := (mem_numItv c (mem_UItv hp)).2
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold Phi phiTailHi
  push_cast
  rw [neg_div, neg_neg]
  exact div_le_div_of_nonneg_right h1 hp'.le

/-! ## Chains of cells -/

/-- Sum of the cell bounds along a list of points. -/
def chainBound (cb : ℕ → ℕ → Option ℚ) : List ℕ → Option ℚ
  | p :: q :: rest =>
    match cb p q, chainBound cb (q :: rest) with
    | some u, some r => some (u + r)
    | _, _ => none
  | _ => some 0

/-- Splitting a chain at the point of index `n`. -/
lemma chainBound_take_drop (cb : ℕ → ℕ → Option ℚ) :
    ∀ (n : ℕ) (L : List ℕ) (u v : ℚ), n < L.length → chainBound cb (L.take (n + 1)) = some u →
      chainBound cb (L.drop n) = some v → chainBound cb L = some (u + v) := by
  intro n
  induction n with
  | zero =>
    intro L u v hn hu hv
    obtain ⟨a, L', rfl⟩ : ∃ a L', L = a :: L' := by
      cases L with
      | nil => simp at hn
      | cons a L' => exact ⟨a, L', rfl⟩
    simp only [List.take_succ_cons, List.take_zero, chainBound, Option.some.injEq] at hu
    simp only [List.drop_zero] at hv
    rw [hv, ← hu, zero_add]
  | succ n ih =>
    intro L u v hn hu hv
    obtain ⟨a, L', rfl⟩ : ∃ a L', L = a :: L' := by
      cases L with
      | nil => simp at hn
      | cons a L' => exact ⟨a, L', rfl⟩
    obtain ⟨b, L'', rfl⟩ : ∃ b L'', L' = b :: L'' := by
      cases L' with
      | nil => simp at hn
      | cons b L'' => exact ⟨b, L'', rfl⟩
    simp only [List.take_succ_cons, List.drop_succ_cons] at hu hv
    simp only [chainBound] at hu ⊢
    split at hu
    · rename_i w r hw hr
      simp only [Option.some.injEq] at hu
      subst hu
      have := ih (b :: L'') r v (by simpa using hn) hr hv
      rw [hw, this]
      simp only [Option.some.injEq]; ring
    · cases hu

lemma chainBound_sound {f : ℝ → ℝ} {cb : ℕ → ℕ → Option ℚ}
    (hcb : ∀ p q u, cb p q = some u → p ≤ q ∧ ∫ v in (p : ℝ)..q, f v ≤ u)
    (hint : ∀ p q : ℕ, p ≤ q → 0 < p → IntervalIntegrable f volume p q) :
    ∀ (L : List ℕ) (p : ℕ) (u : ℚ), 0 < p → chainBound cb (p :: L) = some u →
      p ≤ (p :: L).getLast (by simp) ∧
      ∫ v in (p : ℝ)..((p :: L).getLast (by simp) : ℕ), f v ≤ u := by
  intro L
  induction L with
  | nil =>
    intro p u _ h
    simp only [chainBound, Option.some.injEq] at h
    subst h
    simp
  | cons q rest ih =>
    intro p u hp h
    simp only [chainBound] at h
    split at h
    · rename_i a r ha hr
      cases h
      obtain ⟨hpq, h1⟩ := hcb p q a ha
      obtain ⟨hq2, h2⟩ := ih q r (lt_of_lt_of_le hp hpq) hr
      have hlast : (p :: q :: rest).getLast (by simp) = (q :: rest).getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hlast]
      refine ⟨le_trans hpq hq2, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint p q hpq hp) (hint q _ hq2 (lt_of_lt_of_le hp hpq))]
      push_cast
      linarith
    · cases h

end BSCert.Consts
