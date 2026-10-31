module

public import RequestProject.Beurling.Construction.NoHBS

/-!
# The construction scales `a_k`

Section 4 of the paper defines the construction scale `a_k` by `x_k = a_k + 2H(a_k)`, where `x_k` is
the `k`-th switch-on point (`switchOn X₀ k`) and `H = capH X₀` is the jitter width.

Here `a_k` is **defined** (`constructionScale`) as the supremum of the heights `a ≥ X₀` with
`a + 2H(a) ≤ x_k`. Since `H` is non-decreasing on `[X₀, ∞)`, this is the threshold of the
inequality: every `a ∈ [X₀, a_k)` satisfies `a + 2H(a) ≤ x_k` and every `a > a_k` violates it
(`add_two_capH_le_of_lt_constructionScale`, `lt_add_two_capH_of_constructionScale_lt`). When `H`
is continuous (as in the paper) this is the solution of `x_k = a_k + 2H(a_k)`.

The scale condition `0 < a_k ≤ x_k ≤ (1 + 10⁻³) a_k`, previously an input of the top-level
hypothesis, is proved (`constructionScale_spec`). `Theorem21InputsM` is `Theorem21InputsL` with the
scales fixed to `a_k` and without the scale condition; it implies `Theorem21InputsL`
(`theorem21InputsL_of_M`), hence Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Set Real CaplLink SlotModel GoodHeights Decomp InitialRange QueueMono

namespace Construction

/-- The heights `a ≥ X₀` with `a + 2H(a) ≤ x_k`. -/
def scaleSet (X₀ : ℝ) (k : ℕ) : Set ℝ := {a | X₀ ≤ a ∧ a + 2 * capH X₀ a ≤ switchOn X₀ k}

/-- **The construction scale `a_k`**: the supremum of the heights `a ≥ X₀` with
`a + 2H(a) ≤ x_k`. -/
noncomputable def constructionScale (X₀ : ℝ) (k : ℕ) : ℝ := sSup (scaleSet X₀ k)

lemma switchOn_mono (X₀ : ℝ) : Monotone (switchOn X₀) := by
  refine monotone_nat_of_le_succ fun k => ?_
  show switchOn X₀ k ≤ Real.exp (switchOn X₀ k)
  linarith [Real.add_one_le_exp (switchOn X₀ k)]

lemma two_pow_le_of_logX {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := by
  have hX0 : 0 < X₀ := lt_trans one_pos (one_lt_of_logX hX0' hX)
  have h1 : Real.log ((2 : ℝ) ^ (16 : ℕ)) ≤ Real.log X₀ := by
    rw [Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; nlinarith
  exact (Real.log_le_log_iff (by positivity) hX0).mp h1

/-- `x_k ≥ 1.001 X₀`. -/
lemma switchOn_ge_mul {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (k : ℕ) :
    (1 + 1 / 1000) * X₀ ≤ switchOn X₀ k := by
  have h16 := two_pow_le_of_logX hX0' hX
  have h0 : (1 + 1 / 1000) * X₀ ≤ switchOn X₀ 0 := by
    show (1 + 1 / 1000) * X₀ ≤ Real.exp (X₀ ^ 2)
    have := Real.add_one_le_exp (X₀ ^ 2)
    nlinarith
  exact h0.trans (switchOn_mono X₀ (Nat.zero_le k))

/-- The witness `x_k / 1.001` lies in the scale set. -/
lemma div_mem_scaleSet {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (k : ℕ) :
    switchOn X₀ k / (1 + 1 / 1000) ∈ scaleSet X₀ k := by
  have h16 := two_pow_le_of_logX hX0' hX
  have hX0 : (0 : ℝ) ≤ X₀ := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) 16]
  set x := switchOn X₀ k
  set b := x / (1 + 1 / 1000) with hb
  have hxb : x = (1 + 1 / 1000) * b := by rw [hb]; field_simp
  have hXb : X₀ ≤ b := by
    have := switchOn_ge_mul hX0' hX k
    rw [hb, le_div_iff₀ (by norm_num)]; linarith
  refine ⟨hXb, ?_⟩
  have hH := capH_le_rpow hX0 hX hXb
  have hb0 : 0 < b := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) 16]
  have hsplit : b = b ^ (1 / 8 : ℝ) * b ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hb0]; norm_num
  have h78 : (2 : ℝ) ^ (14 : ℕ) ≤ b ^ (7 / 8 : ℝ) := by
    have e : ((2 : ℝ) ^ (16 : ℕ)) ^ (7 / 8 : ℝ) = 2 ^ (14 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) (h16.trans hXb) (by norm_num)
  have h18 : 0 ≤ b ^ (1 / 8 : ℝ) := Real.rpow_nonneg hb0.le _
  have : 2 * b ^ (1 / 8 : ℝ) ≤ b / 1000 := by
    calc 2 * b ^ (1 / 8 : ℝ) ≤ b ^ (1 / 8 : ℝ) * b ^ (7 / 8 : ℝ) / 1000 := by nlinarith
      _ = b / 1000 := by rw [← hsplit]
  linarith

lemma scaleSet_nonempty {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (k : ℕ) :
    (scaleSet X₀ k).Nonempty := ⟨_, div_mem_scaleSet hX0' hX k⟩

lemma scaleSet_bddAbove (X₀ : ℝ) (k : ℕ) : BddAbove (scaleSet X₀ k) :=
  ⟨switchOn X₀ k, fun a ha => by linarith [ha.2, capH_nonneg X₀ a]⟩

/-- **The scale condition**: `0 < a_k ≤ x_k ≤ (1 + 10⁻³) a_k`, and `X₀ ≤ a_k`. -/
theorem constructionScale_spec {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (k : ℕ) :
    X₀ ≤ constructionScale X₀ k ∧ 0 < constructionScale X₀ k ∧
      constructionScale X₀ k ≤ switchOn X₀ k ∧
      switchOn X₀ k ≤ (1 + 1 / 1000) * constructionScale X₀ k := by
  have h16 := two_pow_le_of_logX hX0' hX
  have hmem := div_mem_scaleSet hX0' hX k
  have hb : switchOn X₀ k / (1 + 1 / 1000) ≤ constructionScale X₀ k :=
    le_csSup (scaleSet_bddAbove X₀ k) hmem
  have hXa : X₀ ≤ constructionScale X₀ k := hmem.1.trans hb
  refine ⟨hXa, by linarith [pow_pos (two_pos : (0 : ℝ) < 2) 16], ?_, ?_⟩
  · exact csSup_le (scaleSet_nonempty hX0' hX k) fun a ha => by linarith [ha.2, capH_nonneg X₀ a]
  · rw [div_le_iff₀ (by norm_num)] at hb; linarith

/-- Below `a_k` (and above `X₀`) the inequality `a + 2H(a) ≤ x_k` holds. -/
theorem add_two_capH_le_of_lt_constructionScale {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {k : ℕ}
    {a : ℝ} (ha : X₀ ≤ a) (hlt : a < constructionScale X₀ k) :
    a + 2 * capH X₀ a ≤ switchOn X₀ k := by
  have h16 := two_pow_le_of_logX hX0' hX
  have hX0 : (0 : ℝ) ≤ X₀ := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) 16]
  obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup (scaleSet_nonempty hX0' hX k) hlt
  have hH := capH_monotoneOn hX0 hX (mem_Ici.mpr ha) (mem_Ici.mpr hb.1) hab.le
  linarith [hb.2]

/-- Above `a_k` the inequality `a + 2H(a) ≤ x_k` fails. -/
theorem lt_add_two_capH_of_constructionScale_lt {X₀ : ℝ} (hX0' : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {k : ℕ}
    {a : ℝ} (hlt : constructionScale X₀ k < a) : switchOn X₀ k < a + 2 * capH X₀ a := by
  by_contra h
  push_neg at h
  have hXa : X₀ ≤ a := (constructionScale_spec hX0' hX k).1.trans hlt.le
  exact absurd (le_csSup (scaleSet_bddAbove X₀ k) ⟨hXa, h⟩) (not_le.mpr hlt)

/-- `Theorem410RestSp` with the scales fixed to `a_k`, without the (proved) scale condition. -/
def Theorem410RestM (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ k, Lemma48PiecesCount X₀ (DesignedZero.heightScale θ kappa0Param (switchOn X₀ k))
      (earlyOf P θ X₀ (kappaParam X₀) A u
        (designedAlpha P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (designedGamma P θ X₀ (kappaParam X₀) A u kappa0Param (switchOn X₀)
          (constructionScale X₀))
        (switchOn X₀) (constructionScale X₀) k)

/-- **Theorem 2.1, hypothesis on the concrete construction, with the construction scales
`a_k` fixed.** `Theorem21InputsL` with `a := constructionScale X₀` and without the scale
condition `0 < a_k ≤ x_k ≤ 1.001 a_k` (proved, `constructionScale_spec`). -/
def Theorem21InputsM : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        {k | placedAt (M ω) k}.Infinite ∧
        PartIRestJ θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) (constructionScale X₀) (M ω) ∧
        Theorem410RestM θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsM` implies `Theorem21InputsL`, with the scales `a_k`. -/
theorem theorem21InputsL_of_M (h : Theorem21InputsM) : Theorem21InputsL := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨M, ι, hι, E, time, htab, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨M, ι, hι, E, time, htab, fun ω hG hω => ?_⟩
  obtain ⟨hinf, hI, hC, hcl⟩ := hP ω hG hω
  refine ⟨hinf, constructionScale X₀, hI, ⟨hC, fun k => ?_⟩, hcl⟩
  obtain ⟨-, h0, h1, h2⟩ := constructionScale_spec (Nat.cast_nonneg _) hlog k
  exact ⟨h0, h1, h2⟩

/-- Theorem 2.1 from `Theorem21InputsM`. -/
theorem theorem21_of_M (h : Theorem21InputsM) : Theorem21 :=
  theorem21_of_L (theorem21InputsL_of_M h)

/-- **Corollary 2.2** from `Theorem21InputsM`. -/
theorem corollary_2_2_of_M (h : Theorem21InputsM) : ¬ QuestionQ :=
  corollary_2_2_of_L (theorem21InputsL_of_M h)

end Construction

end
