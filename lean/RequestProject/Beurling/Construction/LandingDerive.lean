module

public import RequestProject.Beurling.Construction.SlotCounts

/-!
# The landing data of Corollary 3.8, derived from the construction

With the arrivals tied to the composites of the realised system (`ArrivalsLinked`), the landing
data `Landing`/`LandingInit` are no longer inputs. For a height `x ≥ X₀` in the relative slot
`k = slotIdx x`:

* `N(x) = 1 + #(primes ≤ x) + #(composites ≤ x)` (`realised_N_eq`);
* Lemma 3.6: `V_k = #(composites < s_{k+1}) + #(rational primes) + #(primes placed at slots ≤ k) + 1`
  (`V_eq_count`), from its base case at the first slot;
* hence `N(x) = V_k - C + E₊ - E₋` (`N_decomp`), with `C ≤ A_k` the composites in `(x, s_{k+1})`,
  `E₊` the primes placed later that land at or below `x`, and `E₋` the primes placed earlier that
  land above `x`;
* `E± ≤ H(x) + 3/2` (`Ep_le`, `Em_le`), from the count of placed slot starts in a window and the
  slow variation of `H`.

The remaining slot facts used here are collected in `SlotFacts` (the base case of Lemma 3.6 and the
window count of placed slot starts) and `JitterWidthRegular` (a deterministic property of `H`).
`Theorem21InputsO` is `Theorem21InputsN` with the landing data replaced by these.
-/

@[expose] public section

open Set Real CaplLink SlotModel Target Oscillation Absorbed Filter QueueMono Greedy Bookkeeping
  DesignedZero GoodHeights Decomp

namespace Construction

/-- **The slot facts used for the landing data**, pathwise: the base case of Lemma 3.6 (the
elements below the first slot start `s_1` are `1`, the rational primes and the composites, `X₀` in
all; no composite lies in `(X₀, s_1)`) and the count of placed slot starts in a window. -/
structure SlotFacts {X₀ : ℕ} (M : SlotModel X₀) (U : ℕ → ℝ) : Prop where
  init_count : (X₀ : ℝ) = ((compLt M (capH X₀) U (M.slot 1)).ncard : ℝ) +
      ({p : ℕ | p.Prime ∧ p < X₀}.ncard : ℝ) + 1
  init_gap : compIoo M (capH X₀) U X₀ (M.slot 1) = ∅
  window : PlacedWindowCount M

section Hyp

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ} {θ : ℝ} {a : ℕ → ℝ}

/-- **The decomposition `N(x) = V_k - C + E₊ - E₋`.** -/
theorem N_decomp (L : LinkedModel θ X₀ M U a) (S : SlotFacts M U) (h : RealisedOK M (capH X₀) U)
    {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    (realisedSystem M (capH X₀) U).N x =
      (M.V (M.slotIdx x) : ℝ) - ((compIoo M (capH X₀) U x (M.slot (M.slotIdx x + 1))).ncard : ℝ) +
        ((epSet M (capH X₀) U (M.slotIdx x) x).ncard : ℝ) -
        ((emSet M (capH X₀) U (M.slotIdx x) x).ncard : ℝ) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 L.hX
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hslot := (M.mem_slot hX₀ hx).2.1
  rw [realised_N_eq h (by linarith), realised_primes_eq h hx (M.slotIdx x),
    realised_comp_eq h hslot, V_eq_count h L.hlink S.init_count]
  ring

/-- **`Landing` from the construction**, with `κp = log` (so `W = H(x)`). -/
theorem landing_of_linked (L : LinkedModel θ X₀ M U a) (S : SlotFacts M U)
    (hreg : JitterWidthRegular X₀) (h : RealisedOK M (capH X₀) U) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) :
    M.Landing ((realisedSystem M (capH X₀) U).N x)
      (capH X₀ x / 2 * (1 + Real.log x / Real.log x)) x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast (one_lt_of_logX hX0 L.hX).le
  have hlx : Real.log x ≠ 0 := by
    have := (logs_of_ge hX0 L.hX hx).1; linarith
  have hW : capH X₀ x / 2 * (1 + Real.log x / Real.log x) = capH X₀ x := by
    rw [div_self hlx]; ring
  rw [hW]
  exact M.landing_of_counts (capH_nonneg _ _) (N_decomp L S h hx) (Nat.cast_nonneg _)
    (compIoo_le_slotArr h L.hlink S.init_gap hX₀ hx)
    (Ep_le h L.hX L.hU S.window hreg hx) (Em_le L.hX L.hU L.hTlow S.window hx)

/-- **`LandingInit` from the construction**, with `κp = log` (so `W = H(X₀)`). -/
theorem landingInit_of_linked (L : LinkedModel θ X₀ M U a) (S : SlotFacts M U)
    (hreg : JitterWidthRegular X₀) (h : RealisedOK M (capH X₀) U)
    {x : ℝ} (hx : (X₀ : ℝ) ≤ x) (hearly : x < (X₀ : ℝ) + 2 * capH X₀ x) :
    M.LandingInit ((realisedSystem M (capH X₀) U).N x)
      (capH X₀ X₀ / 2 * (1 + Real.log X₀ / Real.log X₀)) x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast (one_lt_of_logX hX0 L.hX).le
  have hlx : Real.log X₀ ≠ 0 := by have := L.hX; linarith
  have hW : capH X₀ X₀ / 2 * (1 + Real.log X₀ / Real.log X₀) = capH X₀ X₀ := by
    rw [div_self hlx]; ring
  rw [hW]
  have hH := capH_initial_le hX0 L.hX hx hearly
  have hEp := Ep_le h L.hX L.hU S.window hreg hx
  have hEm := Em_le L.hX L.hU L.hTlow S.window hx
  exact M.landingInit_of_counts (capH_nonneg _ _) (N_decomp L S h hx) (Nat.cast_nonneg _)
    (compIoo_le_slotArr h L.hlink S.init_gap hX₀ hx) (by linarith) (by linarith)

end Hyp

/-! ### The top-level hypothesis without the landing data -/

/-- `PartIRestJ` without the landing data: the target formula and the queue window data. -/
def PartIRestO (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ)
    (M : SlotModel X₀) : Prop :=
  (∀ x, M.T x = target X₀ (kappaParam X₀) (countA A) (absorbedDensityCap (thetaB θ) A u)
      (osc θ (designedAlpha P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (switchOn X₀)) x) ∧
    M.QueueWindowData

/-- **Theorem 2.1, hypothesis on the concrete construction, without the landing data.**
`Theorem21InputsN` with `PartIRestJ` replaced by `PartIRestO`: the landing data `Landing` and
`LandingInit` of Corollary 3.8 are derived from the link between the arrivals and the composites
of `P(ω)`, the slot facts `SlotFacts` (base case of Lemma 3.6, window count of placed slot starts)
and the slow variation of `H` (`JitterWidthRegular`). -/
def Theorem21InputsO : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ → JitterWidthRegular X₀ ∧
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ArrivalsLinked (M ω) (capH X₀) ω ∧ SlotFacts (M ω) ω ∧
        PartIRestO θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) (constructionScale X₀) (M ω) ∧
        Theorem410RestM θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsO` implies `Theorem21InputsN`: the landing data hold for the construction. -/
theorem theorem21InputsN_of_O (h : Theorem21InputsO) : Theorem21InputsN := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨hreg, M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hlink, hS, ⟨hT, hq⟩, hC, hcl⟩ := hP ω hG hω
  have L : LinkedModel θ X₀ (M ω) ω (constructionScale X₀) := ⟨hθ, hlog, hω, hT, hlink⟩
  have hTlow : ∀ x : ℝ, x < X₀ → (M ω).T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hinf : {k | placedAt (M ω) k}.Infinite :=
    placed_infinite_of_growth hω hlog hTlow
      (fun x hx => T_ge_of_formula hθ hlog hT hx) hlink
  have hok := realisedOK_of (M ω) hω hlog hTlow hinf
  refine ⟨hlink, ⟨hT, hq, Real.log, fun x hx => ⟨?_, le_rfl⟩, fun x hx _ => ?_,
    fun x hx hearly => ?_⟩, hC, hcl⟩
  · exact Real.log_nonneg (by
      have := one_lt_of_logX (Nat.cast_nonneg _) hlog; linarith)
  · exact landing_of_linked L hS hreg hok hx
  · exact landingInit_of_linked L hS hreg hok hx hearly

/-- Theorem 2.1 from `Theorem21InputsO`. -/
theorem theorem21_of_O (h : Theorem21InputsO) : Theorem21 :=
  theorem21_of_N (theorem21InputsN_of_O h)

/-- **Corollary 2.2** from `Theorem21InputsO`. -/
theorem corollary_2_2_of_O (h : Theorem21InputsO) : ¬ QuestionQ :=
  corollary_2_2_of_N (theorem21InputsN_of_O h)

end Construction

end
