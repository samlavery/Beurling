module

public import RequestProject.Beurling.Model.E3Comp
public import RequestProject.Beurling.Noise.BSDefs

/-!
# (H_BS) for the realised system on `QC(< t) ∩ {E1 of time < t}`, and the transfer of smooth
cofactor sums

* `hbs_QE` : on the queue constraints and the cluster events of time `< t` (and the a.s. event
  `NiceEv`), the realised system satisfies (H_BS) (04a-setup.tex) on `[1, Z]` for every horizon
  `X₀ ≤ Z` with `4Z + 2 ≤ t` (Remark *horizon*: `hbs_local` reads the queue bound and the cluster
  event only at the heights `≤ Z`);
* `sum_le_vSmooth` : a sum `∑ 1/m` over live exponent vectors of the prime data with values in
  `(Y, 2Y]` and all prime values `≤ z` is at most `v(log Y, z)` of the realised system
  (the quantity of Lemma 5.3, smooth-v).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6 SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section HBSQE

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- **(H_BS) on `[1, Z]` on `QC(< t) ∩ {E1 of time < t}`** (04a-setup.tex, (H_BS), with
`X₀⁻ = X₀ - H(X₀)/2`, `η₁ = η₂ = 1/1000`, `ε₁ = hbsEps`), for a horizon `X₀ ≤ Z` with
`4Z + 2 ≤ t`. -/
theorem hbs_QE {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) (h0 : Std θ X₀ ω)
    {Z : ℝ} (hZX : (X₀ : ℝ) ≤ Z) (hZt : 4 * Z + 2 ≤ t) :
    (realisedSystem h0.limModel (capH X₀) ω).HBS (Xm X₀) Z (1 / 1000) (1 / 1000)
      (hbsEps X₀) := by
  classical
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXb : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hTB : ∀ m, ttB X₀ m < t → ω ∈ tB (θ := θ) (X₀ := X₀) m := fun m hm =>
    tB_all_of_QE hc hev hQC hE1 ⟨hU, hSG, hnt⟩ m hm.le
  -- the scale `n'`: `Z ≤ 2^{n'} X₀/2 < 2Z`
  have hex : ∃ n : ℕ, Z ≤ 2 ^ n * (X₀ : ℝ) / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * Z / X₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith
  set n' := Nat.find hex with hn'
  have hZn : Z ≤ 2 ^ n' * (X₀ : ℝ) / 2 := Nat.find_spec hex
  have hn2 : 2 ^ n' * (X₀ : ℝ) / 2 < 2 * Z := by
    rcases Nat.eq_zero_or_pos n' with h0' | hpos
    · rw [h0']; simp; linarith
    · obtain ⟨k, hk⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
      have hlt := Nat.find_min hex (show k < n' by omega)
      push_neg at hlt
      rw [hk, pow_succ]
      linarith
  have httB : ttB X₀ n' < t := by
    unfold ttB
    have h1 : ((⌈2 ^ n' * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) < t := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ n' * (X₀ : ℝ) / 2 by positivity)
      linarith
    exact_mod_cast h1
  have hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v) := by
    intro v hv hvZ
    have hvt : ⌈v⌉₊ < t := by
      have h1 : (⌈v⌉₊ : ℝ) < t := by
        have := Nat.ceil_lt_add_one (show 0 ≤ v by linarith)
        linarith
      exact_mod_cast h1
    refine cluster_of_QE hc hev hE1 hTB h0 hSG hv hvt ?_ httB
    obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hX hv
    have hv0 : 0 < v := by linarith
    have h11 : (100 : ℝ) ≤ Real.log v ^ 11 := by
      have : (10 ^ 8 : ℝ) ≤ Real.log v ^ 11 :=
        hl.trans (le_self_pow₀ (by linarith) (by norm_num))
      linarith
    have : 4 * v / Real.log v ^ 11 ≤ v / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    nlinarith
  have hQ : ∀ y, (X₀ : ℝ) ≤ y → y ≤ Z →
      (M.queue (M.slotIdx y) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx y)) := by
    intro y hy hyZ
    refine queue_of_QE hc hQC h0 hy ?_
    have hlog := log_le_lin hc (show 0 < y by linarith)
    linarith
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have hmain := hbs_local hc.hθ hX M ω hU (limModel_placed_infinite h0)
    (constructionScale X₀) hT Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hZX hQ hcl
  have hXmh : (X₀ : ℝ) / 2 ≤ X₀ - capH X₀ X₀ / 2 := Xm_half hc
  exact
    { X0m_ge := by
        have h1 := Xm_half hc
        have : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) / 2 := by
          have := Real.add_one_le_exp (Real.log X₀)
          rw [Real.exp_log (by linarith)] at this; linarith
        linarith
      eta1_nonneg := by norm_num
      eta1_le := le_rfl
      eta2_nonneg := by norm_num
      eta2_le := le_rfl
      floor_eq := fun v h1 h2 _ => realised_floor_eq hok hU hX h0.limModel_low h1 h2
      err := fun v h1 h2 => hmain v h1 h2
      eta2 := fun v h1 _ => hbsEps_mul_log_le hX (by unfold Xm at h1; linarith)
      eta1 := fun x K w hw => hbsEps_dyadic_sum_le hX K w (fun k hk =>
        ⟨(hw k hk).1, (hw k hk).2.1, by unfold Xm at hw; linarith [(hw k hk).2.2.1]⟩) }

end HBSQE

/-! ### Smooth cofactor sums -/

section Transfer

variable {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **Transfer to `v(log Y, z)`**: for a finite set `F` of live exponent vectors of `DM M U`
with values in `(Y, 2Y]` and all prime values `≤ z`, `∑_{e ∈ F} 1/m(e) ≤ v(log Y, z)` of the
realised system (Lemma 5.3, smooth-v, 04a-setup.tex). -/
theorem sum_le_vSmooth (h : RealisedOK M (capH X₀) U) (F : Finset (PIdx X₀ →₀ ℕ)) {Y z : ℝ}
    (hF : ∀ e ∈ F, Live (DM M U) e ∧ Y < eval (DM M U) e ∧ eval (DM M U) e ≤ 2 * Y ∧
      ∀ i ∈ e.support, pval (DM M U) i ≤ z) :
    ∑ e ∈ F, 1 / eval (DM M U) e ≤ (realisedSystem M (capH X₀) U).vSmooth Y z := by
  classical
  set P := realisedSystem M (capH X₀) U with hP
  have hpre : ∀ e : PIdx X₀ →₀ ℕ, ∃ f, Live (DM M U) e → mapE M f = e := by
    intro e
    by_cases he : Live (DM M U) e
    · obtain ⟨f, hf⟩ := exists_mapE (U := U) he
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h' => absurd h' he⟩
  choose g hg using hpre
  set φ : (PIdx X₀ →₀ ℕ) → (ℕ →₀ ℕ) := fun e => Finsupp.equivMapDomain h.equiv.symm (g e)
    with hφ
  have hback : ∀ e, Finsupp.equivMapDomain h.equiv (φ e) = g e := by
    intro e; ext i; simp [hφ, Finsupp.equivMapDomain_apply]
  have hval : ∀ e, Live (DM M U) e → P.val (φ e) = eval (DM M U) e := by
    intro e he
    rw [hP, val_eq_idxVal h, hback, ← eval_mapE, hg e he]
  have hcoef : ∀ e j, (φ e) j = g e (h.equiv j) := by
    intro e j; simp [hφ, Finsupp.equivMapDomain_apply]
  have hmapE : ∀ (f : RealisedIdx M →₀ ℕ) (i : RealisedIdx M), mapE M f (toPIdx M i) = f i := by
    intro f i
    unfold mapE
    exact Finsupp.mapDomain_apply (toPIdx_injective M) f i
  have hinj : Set.InjOn φ F := by
    intro e1 h1 e2 h2 h12
    have := congrArg (Finsupp.equivMapDomain h.equiv) h12
    rw [hback, hback] at this
    rw [← hg e1 (hF e1 h1).1, ← hg e2 (hF e2 h2).1, this]
  rw [← Finset.sum_image (f := fun f => 1 / P.val f) (g := φ) hinj |>.trans
    (Finset.sum_congr rfl fun e he => by rw [hval e (hF e he).1])]
  unfold BeurlingSystem.vSmooth
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ => ?_
  · intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hlive, hY, h2Y, hz⟩ := hF e he
    rw [Finset.mem_filter]
    refine ⟨?_, by rw [hval e hlive]; exact hY, fun j hj => ?_⟩
    · unfold BeurlingSystem.elems
      rw [Set.Finite.mem_toFinset]
      show P.val (φ e) ≤ 2 * Y
      rw [hval e hlive]; exact h2Y
    · rw [hP, realisedSystem_p h, ← pval_toPIdx]
      refine hz _ (Finsupp.mem_support_iff.mpr ?_)
      rw [← hg e hlive, hmapE, ← hcoef]
      exact Finsupp.mem_support_iff.mp hj
  · exact div_nonneg zero_le_one (P.val_pos f).le

end Transfer

end BModel
