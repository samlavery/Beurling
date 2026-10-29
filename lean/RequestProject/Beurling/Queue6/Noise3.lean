module

public import RequestProject.Beurling.Queue6.Budget6

/-!
# Lemma 5.22 (per-scale noise): the per-window Freedman events E3, E3′ and their budget

For a dyadic scale `u = 2^m X₀` and a window `W = [a, b)` with integer endpoints,
`u ≤ a < b ≤ 2u`, `b - a ≤ 1.03 H(u) + 1` (the windows of `𝒲'_u`, §5 "The per-window Freedman
events"), the event `E3_W` (`E3ev`) states (F1) and (F2) for the martingales `Mart(W)`,
`Mart⁽²⁾(W)` of the truncated increments (§5 "Truncation")
`X̃_q(W) = min(X_q(W), 2M₁(u))`, `X̃⁽²⁾_q(W) = min(X⁽²⁾_q(W), b₂)`, in decision order, at every
time `n`:

* (F1) `|Mart_n(W)| ≤ √(2 V̄_W λ'_u) + (4/3) M₁(u) λ'_u`, `V̄_W = 2M₁(u) · 50 log(2u) · |W|`;
* (F2) `|Mart⁽²⁾_n(W)| ≤ √(2 V̄²_W λ'_u) + (2/3) b₂ λ'_u`, `V̄²_W = b₂ s₂(u) |W|`;

with `λ'_u = 3 log u + 2 log log u + 2 + log H(u)`, `b₂ = 2 A_u M₁(u)`,
`A_u = #{a ≥ 2 : (X₀⁻)^a ≤ 2u}` and `s₂(u)` of (s2). Its time is `t(W) = b`.

`e3_budget` : **the budget of Lemma 5.22**: at every scale, the failures on
`QC(< t(W)) ∩ Good(< t(W))` sum to at most `1.2 u⁻²`. By Freedman's inequality (two-sided,
`freedman_two_all`) the failure probability of each of (F1), (F2) is `≤ 2e^{-λ'}` given the
variance bounds of the proof of Lemma 5.22, which are the named inputs:

* `E3CompBound` — "The variance bound holds on `Good(< t(W))`": `Comp(W) ≤ 50 log(2u) |W|`,
  read through the partial sums of the conditional means of the truncated counts;
* `E3S2Bound` — eq. (s2): `Comp⁽²⁾(W) ≤ s₂(u) |W|`, in the same form;

each on the queue constraints and the cluster events E1 of time `< t(W)` (the only inputs the
proof reads: "No window event (E2, E3, E3′, E4) is read").

Deviations, all recorded: the windows are half-open `[a, b)` with `a < b` (the counts of §6.3
are over `[α, β)`); one event per window of `𝒲'_u` (the events of `𝒲_u ⊂ 𝒲'_u` are the same
events, so `Good` is unchanged); the bounds hold at every time `n` (the paper states them for
the whole sums); the martingales are those of the truncated increments, which agree with the
true ones on `Good(< t(W))` ("Truncation is inactive on `Good(< t(W))`").
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Filter Finset Freedman Construction BModel
  CaplLink QueueMono

namespace Queue6

/-! ### Freedman's inequality, two-sided, all times -/

section Two

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {Y : ℕ → Ω → ℝ} {b : ℝ}

/-- **Freedman's inequality, two-sided, at all times**: for counts `0 ≤ Y_k ≤ b`, `ℱ_{k+1}`-
measurable, whose partial compensators are `≤ v/b` a.s. on `G`,
`P({∃ n, |∑_{k<n} (Y_k - E[Y_k|ℱ_k])| > √(2vλ) + 2bλ/3} ∩ G) ≤ 2 e^{-λ}`. -/
theorem freedman_two_all (hb : 0 < b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) {v l : ℝ} (hv : 0 < v) (hl : 0 < l)
    (G : Set Ω) (hG : ∀ᵐ ω ∂μ, ω ∈ G → ∀ n, ∑ k ∈ range n, (μ[Y k | ℱ k]) ω ≤ v / b) :
    μ ({ω | ∃ n, Real.sqrt (2 * v * l) + 2 * b * l / 3 <
        |∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)|} ∩ G) ≤
      ENNReal.ofReal (2 * Real.exp (-l)) := by
  set a := Real.sqrt (2 * v * l) + 2 * b * l / 3 with ha_def
  have ha : 0 < a := by positivity
  set ξ : ℕ → Ω → ℝ := fun k ω => Y k ω - clipB ℱ μ b Y k ω with hξ
  set nξ : ℕ → Ω → ℝ := fun k ω => -(Y k ω - clipB ℱ μ b Y k ω) with hnξ
  have hmd := martDiff_bounded (μ := μ) (ℱ := ℱ) hb.le hY0 hYb hmeas
  have hmdn : MartDiff ℱ μ nξ b b :=
    { meas := fun k => (hmd.meas k).neg
      le_b := fun k ω => by
        have := clipB_bounds (ℱ := ℱ) (μ := μ) (Y := Y) hb.le k ω
        simp only [hnξ]; linarith [hY0 k ω]
      bdd := fun k ω => by simp only [hnξ, abs_neg]; exact hmd.bdd k ω
      mean_zero := fun k => by
        have h1 := condExp_neg (μ := μ) (fun ω => Y k ω - clipB ℱ μ b Y k ω) (ℱ k)
        filter_upwards [h1, hmd.mean_zero k] with ω e1 e2
        have e3 : nξ k = -(fun ω => Y k ω - clipB ℱ μ b Y k ω) := rfl
        rw [e3, e1]
        simp only [Pi.neg_apply, Pi.zero_apply] at e2 ⊢
        rw [e2, neg_zero] }
  have hVeq : ∀ n ω, V ℱ μ nξ n ω = V ℱ μ ξ n ω := by
    intro n ω
    unfold V
    refine sum_congr rfl fun k _ => ?_
    have : (fun ω => nξ k ω ^ 2) = fun ω => ξ k ω ^ 2 := funext fun ω => by
      simp only [hnξ, hξ, neg_sq]
    rw [this]
  set E1 := {ω | ∃ n, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v}
  set E2 := {ω | ∃ n, a ≤ S nξ n ω ∧ V ℱ μ nξ n ω ≤ v}
  have hc := ae_all_iff.mpr fun k => clipB_ae_eq (μ := μ) (ℱ := ℱ) hY0 hYb hmeas k
  have hvar := ae_all_iff.mpr fun k => condVar_le (μ := μ) (ℱ := ℱ) hb.le hY0 hYb hmeas k
  have hsub : ({ω | ∃ n, a < |∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)|} ∩ G : Set Ω) ≤ᵐ[μ]
      (E1 ∪ E2 : Set Ω) := by
    filter_upwards [hc, hvar, hG] with ω hcω hvω hGω
    rintro ⟨⟨n, hS⟩, hωG⟩
    have hsum := hGω hωG n
    have hS' : ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω) = S ξ n ω := by
      simp only [S, ξ]; exact sum_congr rfl fun k _ => by rw [hcω k]
    have hV : V ℱ μ ξ n ω ≤ v := by
      unfold V
      calc ∑ k ∈ range n, (μ[fun ω => ξ k ω ^ 2 | ℱ k]) ω
          ≤ ∑ k ∈ range n, b * (μ[Y k | ℱ k]) ω :=
            sum_le_sum fun k _ => by rw [← hcω k]; exact hvω k
        _ = b * ∑ k ∈ range n, (μ[Y k | ℱ k]) ω := by rw [mul_sum]
        _ ≤ b * (v / b) := mul_le_mul_of_nonneg_left hsum hb.le
        _ = v := by field_simp
    rw [hS'] at hS
    rcases le_or_gt 0 (S ξ n ω) with h0 | h0
    · left
      rw [abs_of_nonneg h0] at hS
      exact ⟨n, hS.le, hV⟩
    · right
      rw [abs_of_neg h0] at hS
      have hSn : S nξ n ω = -S ξ n ω := by
        simp only [S, nξ, ξ, sum_neg_distrib]
      refine ⟨n, ?_, ?_⟩
      · rw [hSn]; exact hS.le
      · rw [hVeq]; exact hV
  have hF1 := freedman_iUnion (μ := μ) (ℱ := ℱ) hmd hb.le ha hv
  have hF2 := freedman_iUnion (μ := μ) (ℱ := ℱ) hmdn hb.le ha hv
  have hlam := lam_le_b hv hl hb.le
  have hF1' : μ.real E1 ≤ Real.exp (-l) := hF1.trans (Real.exp_le_exp.mpr (neg_le_neg hlam))
  have hF2' : μ.real E2 ≤ Real.exp (-l) := hF2.trans (Real.exp_le_exp.mpr (neg_le_neg hlam))
  calc μ ({ω | ∃ n, a < |∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)|} ∩ G)
      ≤ μ (E1 ∪ E2) := measure_mono_ae hsub
    _ ≤ μ E1 + μ E2 := measure_union_le _ _
    _ = ENNReal.ofReal (μ.real E1) + ENNReal.ofReal (μ.real E2) := by
        rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-l)) + ENNReal.ofReal (Real.exp (-l)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hF1') (ENNReal.ofReal_le_ofReal hF2')
    _ = ENNReal.ofReal (2 * Real.exp (-l)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

end Two

/-! ### The objects of Lemma 5.22 -/

variable (θ : ℝ) (X₀ : ℕ)

/-- `λ'_u = 3 log u + 2 log log u + 2 + log H(u)`. -/
noncomputable def lamE3 (u : ℝ) : ℝ :=
  3 * Real.log u + 2 * Real.log (Real.log u) + 2 + Real.log (capH X₀ u)

/-- `A_u = #{a ≥ 2 : (X₀⁻)^a ≤ 2u} = ⌊log(2u)/log X₀⁻⌋ - 1`. -/
noncomputable def AuE3 (u : ℝ) : ℕ := ⌊Real.log (2 * u) / Real.log (Xm X₀)⌋₊ - 1

/-- `b₂ = 2 A_u M₁(u)`. -/
noncomputable def b2E3 (u : ℝ) : ℝ := 2 * (AuE3 X₀ u : ℝ) * capM1 X₀ u

/-- `s₂(u) = 9 L_u exp(-max(log X₀⁻, ½ √(L_u log L_u)))` (eq. (s2)). -/
noncomputable def s2E3 (u : ℝ) : ℝ :=
  9 * Real.log u *
    Real.exp (-(max (Real.log (Xm X₀)) (Real.sqrt (Real.log u * Real.log (Real.log u)) / 2)))

/-- **The windows of `𝒲'_u`** at scale `m` (`u = 2^m X₀`): `[a, b)`, integer endpoints,
`u ≤ a < b ≤ 2u`, `b - a ≤ 1.03 H(u) + 1`. -/
def AdmW (m : ℕ) (a b : ℤ) : Prop :=
  uS X₀ m ≤ a ∧ a < b ∧ (b : ℝ) ≤ 2 * uS X₀ m ∧
    ((b - a : ℤ) : ℝ) ≤ 1.03 * capH X₀ (uS X₀ m) + 1

/-- The truncated increment `X̃_q(W) = min(X_q(W), 2M₁(u))` of the prime decided at relative
slot `k + 1` (non-absorbed composites of `W` with latest prime `q`, `q ‖ n`). -/
noncomputable def X3 (m : ℕ) (a b : ℤ) (k : ℕ) (ω : JitterΩ) : ℝ :=
  min (Xcount (CM θ X₀ ω) (Ucl ω) a b k 1) (2 * capM1 X₀ (uS X₀ m))

/-- The truncated increment `X̃⁽²⁾_q(W) = min(X⁽²⁾_q(W), b₂)` (`q² | n`). -/
noncomputable def X32 (m : ℕ) (a b : ℤ) (k : ℕ) (ω : JitterΩ) : ℝ :=
  min (X2count (CM θ X₀ ω) (Ucl ω) a b k) (b2E3 X₀ (uS X₀ m))

/-- `Mart_n(W) = ∑_{k<n} (X̃_k(W) - E[X̃_k(W) | ℱ_k])`. -/
noncomputable def MartE3 (m : ℕ) (a b : ℤ) (n : ℕ) (ω : JitterΩ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (X3 θ X₀ m a b k ω - (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω)

/-- `Mart⁽²⁾_n(W) = ∑_{k<n} (X̃⁽²⁾_k(W) - E[X̃⁽²⁾_k(W) | ℱ_k])`. -/
noncomputable def Mart2E3 (m : ℕ) (a b : ℤ) (n : ℕ) (ω : JitterΩ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (X32 θ X₀ m a b k ω - (jitterMeasure[X32 θ X₀ m a b k | jitterFiltration k]) ω)

/-- `V̄_W = 2M₁(u) · 50 log(2u) · |W|`. -/
noncomputable def VbE3 (m : ℕ) (a b : ℤ) : ℝ :=
  2 * capM1 X₀ (uS X₀ m) * (50 * Real.log (2 * uS X₀ m)) * ((b - a : ℤ) : ℝ)

/-- `V̄²_W = b₂ s₂(u) |W|`. -/
noncomputable def Vb2E3 (m : ℕ) (a b : ℤ) : ℝ :=
  b2E3 X₀ (uS X₀ m) * s2E3 X₀ (uS X₀ m) * ((b - a : ℤ) : ℝ)

/-- **The event `E3_W`** ((F1) and (F2) at every time) for a window of `𝒲'_u`; `univ`
otherwise. Here `2 (2M₁) λ'/3 = (4/3) M₁ λ'`. -/
def E3ev (m : ℕ) (a b : ℤ) : Set JitterΩ :=
  {ω | AdmW X₀ m a b → ∀ n,
    |MartE3 θ X₀ m a b n ω| ≤ Real.sqrt (2 * VbE3 X₀ m a b * lamE3 X₀ (uS X₀ m)) +
      2 * (2 * capM1 X₀ (uS X₀ m)) * lamE3 X₀ (uS X₀ m) / 3 ∧
    |Mart2E3 θ X₀ m a b n ω| ≤ Real.sqrt (2 * Vb2E3 X₀ m a b * lamE3 X₀ (uS X₀ m)) +
      2 * b2E3 X₀ (uS X₀ m) * lamE3 X₀ (uS X₀ m) / 3}

/-- **The family of the events E3, E3′ of Definition 6.8** (Lemma 5.22): indexed by
`(m, a, b)`, with time `t(W) = b` and scale `m`. -/
def e3Family : Sec5Family where
  ι := ℕ × ℤ × ℤ
  E p := E3ev θ X₀ p.1 p.2.1 p.2.2
  time p := p.2.2.toNat
  scale p := p.1

/-- The good set read by Lemma 5.22 at the time `t`: the queue constraints and the cluster
events E1 of time `< t`. -/
def GoodE1 (t : ℕ) : Set JitterΩ :=
  QC (okQ θ X₀) (tq θ X₀) t ∩ {ω | ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n}

/-- **The variance input of Lemma 5.22** ("The variance bound holds on `Good(< t(W))`":
`Comp(W) ≤ 50 log(2u) |W|`), read through the partial compensators of the truncated counts. -/
def E3CompBound : Prop :=
  ∀ m a b, AdmW X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ GoodE1 θ X₀ b.toNat → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω ≤
      50 * Real.log (2 * uS X₀ m) * ((b - a : ℤ) : ℝ)

/-- **Eq. (s2) of Lemma 5.22** (`Comp⁽²⁾(W) ≤ s₂(u) |W|`), read through the partial
compensators of the truncated counts. -/
def E3S2Bound : Prop :=
  ∀ m a b, AdmW X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ GoodE1 θ X₀ b.toNat → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[X32 θ X₀ m a b k | jitterFiltration k]) ω ≤
      s2E3 X₀ (uS X₀ m) * ((b - a : ℤ) : ℝ)

variable {θ X₀}

/-! ### One window -/

section Window

variable (hc : Cond θ X₀)
include hc

lemma uS_facts (m : ℕ) : (X₀ : ℝ) ≤ uS X₀ m ∧ 10 ^ 8 ≤ Real.log (uS X₀ m) ∧
    1 ≤ capH X₀ (uS X₀ m) ∧ 1 ≤ capM1 X₀ (uS X₀ m) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  exact ⟨hu, (logs_of_ge hX0 hc.hX hu).1, capH_ge_one hX0 hc.hX hu,
    QueueBound.one_le_capM1 hX0 hc.hX hu⟩

lemma lamE3_ge (m : ℕ) : 3 * Real.log (uS X₀ m) + Real.log (capH X₀ (uS X₀ m)) + 36 ≤
    lamE3 X₀ (uS X₀ m) := by
  obtain ⟨-, hl, hH, -⟩ := uS_facts hc m
  unfold lamE3
  have h18 : (18 : ℝ) ≤ Real.log (Real.log (uS X₀ m)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he := Real.exp_one_lt_d9
    have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 18
    rw [e]; nlinarith
  linarith

lemma lamE3_pos (m : ℕ) : 0 < lamE3 X₀ (uS X₀ m) := by
  obtain ⟨-, hl, hH, -⟩ := uS_facts hc m
  have := lamE3_ge hc m
  have := Real.log_nonneg hH
  linarith

lemma s2E3_pos (u : ℝ) (hu : 10 ^ 8 ≤ Real.log u) : 0 < s2E3 X₀ u := by
  unfold s2E3; have := Real.exp_pos (-(max (Real.log (Xm X₀))
    (Real.sqrt (Real.log u * Real.log (Real.log u)) / 2)))
  have : 0 < Real.log u := by linarith
  positivity

/-- **Lemma 5.22 for one window**: `P(E3_Wᶜ ∩ GoodE1(t(W))) ≤ 4 e^{-λ'_u}`. -/
theorem e3_window (hC : E3CompBound θ X₀) (hS : E3S2Bound θ X₀) {m : ℕ} {a b : ℤ}
    (hW : AdmW X₀ m a b) :
    jitterMeasure ((E3ev θ X₀ m a b)ᶜ ∩ GoodE1 θ X₀ b.toNat) ≤
      ENNReal.ofReal (4 * Real.exp (-lamE3 X₀ (uS X₀ m))) := by
  classical
  obtain ⟨hu, hl, hH, hM⟩ := uS_facts hc m
  set u := uS X₀ m with hudef
  set l := lamE3 X₀ u
  have hl0 : 0 < l := lamE3_pos hc m
  have hab : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by
    have := hW.2.1; exact_mod_cast (by omega : (0 : ℤ) < b - a)
  have hu1 : (1 : ℝ) < u := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  have hlog2 : 0 < Real.log (2 * u) := Real.log_pos (by linarith)
  set G := GoodE1 θ X₀ b.toNat
  -- (F1)
  set F1 := {ω | ∃ n, Real.sqrt (2 * VbE3 X₀ m a b * l) + 2 * (2 * capM1 X₀ u) * l / 3 <
      |∑ k ∈ Finset.range n, (X3 θ X₀ m a b k ω -
        (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω)|}
  set F2 := {ω | ∃ n, Real.sqrt (2 * Vb2E3 X₀ m a b * l) + 2 * b2E3 X₀ u * l / 3 <
      |∑ k ∈ Finset.range n, (X32 θ X₀ m a b k ω -
        (jitterMeasure[X32 θ X₀ m a b k | jitterFiltration k]) ω)|}
  have hsub : (E3ev θ X₀ m a b)ᶜ ⊆ F1 ∪ F2 := by
    intro ω hω
    simp only [E3ev, mem_compl_iff, mem_setOf_eq, _root_.not_imp, not_forall] at hω
    obtain ⟨-, n, hn⟩ := hω
    by_cases h1 : |MartE3 θ X₀ m a b n ω| ≤ Real.sqrt (2 * VbE3 X₀ m a b * l) +
        2 * (2 * capM1 X₀ u) * l / 3
    · right
      have h2 := fun h2 => hn ⟨h1, h2⟩
      exact ⟨n, lt_of_not_ge h2⟩
    · left; exact ⟨n, lt_of_not_ge h1⟩
  have hM0 : 0 < 2 * capM1 X₀ u := by linarith
  have hY0 : ∀ k ω, 0 ≤ X3 θ X₀ m a b k ω := fun k ω =>
    le_min (Nat.cast_nonneg _) hM0.le
  have hYb : ∀ k ω, X3 θ X₀ m a b k ω ≤ 2 * capM1 X₀ u := fun k ω => min_le_right _ _
  have hYm : ∀ k, StronglyMeasurable[jitterFiltration (k + 1)] (X3 θ X₀ m a b k) := fun k =>
    ((xcount_adapted hc (a : ℝ) b k 1).min measurable_const).stronglyMeasurable
  have hv1 : 0 < VbE3 X₀ m a b := by unfold VbE3; positivity
  have hB1 : jitterMeasure (F1 ∩ G) ≤ ENNReal.ofReal (2 * Real.exp (-l)) := by
    refine freedman_two_all hM0 hY0 hYb hYm hv1 hl0 G ?_
    filter_upwards [hC m a b hW] with ω h hG n
    refine (h hG n).trans (le_of_eq ?_)
    unfold VbE3; rw [← hudef]; field_simp
  have hB2 : jitterMeasure (F2 ∩ G) ≤ ENNReal.ofReal (2 * Real.exp (-l)) := by
    rcases Nat.eq_zero_or_pos (AuE3 X₀ u) with h0 | hA
    · -- `A_u = 0`: the truncated increments vanish
      have hb2 : b2E3 X₀ u = 0 := by unfold b2E3; rw [h0]; simp
      have hz : ∀ k, X32 θ X₀ m a b k = 0 := by
        intro k; funext ω
        unfold X32; rw [← hudef, hb2]
        exact le_antisymm (min_le_right _ _) (le_min (Nat.cast_nonneg _) le_rfl)
      have hF2 : F2 = ∅ := by
        ext ω
        simp only [F2, hz, condExp_zero, Pi.zero_apply, sub_zero, Finset.sum_const_zero,
          abs_zero, mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_lt]
        intro _
        positivity
      rw [hF2, Set.empty_inter, measure_empty]; exact zero_le _
    · have hb2 : 0 < b2E3 X₀ u := by
        unfold b2E3
        have : (1 : ℝ) ≤ AuE3 X₀ u := by exact_mod_cast hA
        positivity
      have hY0' : ∀ k ω, 0 ≤ X32 θ X₀ m a b k ω := fun k ω =>
        le_min (Nat.cast_nonneg _) hb2.le
      have hYb' : ∀ k ω, X32 θ X₀ m a b k ω ≤ b2E3 X₀ u := fun k ω => min_le_right _ _
      have hYm' : ∀ k, StronglyMeasurable[jitterFiltration (k + 1)] (X32 θ X₀ m a b k) :=
        fun k => ((x2count_adapted hc (a : ℝ) b k).min measurable_const).stronglyMeasurable
      have hs2 := s2E3_pos hc u hl
      have hv2 : 0 < Vb2E3 X₀ m a b := by unfold Vb2E3; positivity
      refine freedman_two_all hb2 hY0' hYb' hYm' hv2 hl0 G ?_
      filter_upwards [hS m a b hW] with ω h hG n
      refine (h hG n).trans (le_of_eq ?_)
      unfold Vb2E3; rw [← hudef]; field_simp
  calc jitterMeasure ((E3ev θ X₀ m a b)ᶜ ∩ G)
      ≤ jitterMeasure (F1 ∩ G ∪ F2 ∩ G) := by
        refine measure_mono fun ω ⟨h1, h2⟩ => ?_
        rcases hsub h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, h2⟩
    _ ≤ jitterMeasure (F1 ∩ G) + jitterMeasure (F2 ∩ G) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-l)) + ENNReal.ofReal (2 * Real.exp (-l)) :=
        add_le_add hB1 hB2
    _ = ENNReal.ofReal (4 * Real.exp (-l)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- `(u + 1)(1.03 H + 2) · 4 e^{-λ'_u} ≤ 1.2 u⁻²`. -/
lemma e3_numeric (m : ℕ) :
    ((uS X₀ m + 1) * (1.03 * capH X₀ (uS X₀ m) + 2)) *
      (4 * Real.exp (-lamE3 X₀ (uS X₀ m))) ≤ 1.2 / uS X₀ m ^ 2 := by
  obtain ⟨hu, hl, hH, -⟩ := uS_facts hc m
  set u := uS X₀ m
  set H := capH X₀ u
  have hu0 : 0 < u := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  have hu1 : 1 ≤ u := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  have hH0 : 0 < H := by linarith
  have hlam := lamE3_ge hc m
  have he : Real.exp (-lamE3 X₀ u) ≤ 1 / (u ^ 3 * H * 100) := by
    have h1 : Real.exp (-lamE3 X₀ u) ≤
        Real.exp (-(3 * Real.log u + Real.log H + 36)) := Real.exp_le_exp.mpr (by linarith)
    have e : Real.exp (3 * Real.log u + Real.log H + 36) = u ^ 3 * H * Real.exp 36 := by
      have e3 : Real.exp (3 * Real.log u) = u ^ 3 := by
        rw [show (3 : ℝ) * Real.log u = Real.log (u ^ 3) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]
      rw [Real.exp_add, Real.exp_add, e3, Real.exp_log hH0]
    have h36 : (100 : ℝ) ≤ Real.exp 36 := by
      have := Real.add_one_le_exp (36 : ℝ)
      have h2 : Real.exp 36 = Real.exp 18 * Real.exp 18 := by rw [← Real.exp_add]; norm_num
      have h3 := Real.add_one_le_exp (18 : ℝ)
      nlinarith
    have h1' : Real.exp (-lamE3 X₀ u) ≤ (u ^ 3 * H * Real.exp 36)⁻¹ := by
      rw [← e, ← Real.exp_neg]; exact h1
    refine h1'.trans ?_
    rw [one_div]
    apply inv_anti₀ (by positivity)
    have : 0 < u ^ 3 * H := by positivity
    nlinarith
  have hp : 0 ≤ (u + 1) * (1.03 * H + 2) := by positivity
  calc ((u + 1) * (1.03 * H + 2)) * (4 * Real.exp (-lamE3 X₀ u))
      ≤ ((u + 1) * (1.03 * H + 2)) * (4 * (1 / (u ^ 3 * H * 100))) := by gcongr
    _ ≤ (2 * u * (3.03 * H)) * (4 * (1 / (u ^ 3 * H * 100))) := by
        gcongr
        · linarith
        · linarith
    _ = 0.2424 / u ^ 2 := by field_simp; ring
    _ ≤ 1.2 / u ^ 2 := by gcongr; norm_num

/-- **The budget of Lemma 5.22 (Table 1, E3 and E3′)**: at every scale `m`, the failures of the
events of `e3Family` on `QC(< t(W)) ∩ Good(< t(W))` sum to at most `1.2 u⁻²`, `u = 2^m X₀`. -/
theorem e3_budget (hC : E3CompBound θ X₀) (hS : E3S2Bound θ X₀) (m : ℕ) :
    ∑' i : {i // (e3Family θ X₀).scale i = m},
      jitterMeasure (((e3Family θ X₀).E i)ᶜ ∩ QC (okQ θ X₀) (tq θ X₀) ((e3Family θ X₀).time i) ∩
        goodBefore (Sum.elim (E1ev θ X₀) (e3Family θ X₀).E)
          (Sum.elim (tE1 X₀) (e3Family θ X₀).time) ((e3Family θ X₀).time i)) ≤
      ENNReal.ofReal (1.2 / uS X₀ m ^ 2) := by
  classical
  obtain ⟨hu, hl, hH, -⟩ := uS_facts hc m
  set u := uS X₀ m with hudef
  set c := ENNReal.ofReal (4 * Real.exp (-lamE3 X₀ u))
  let e : {i // (e3Family θ X₀).scale i = m} ≃ ℤ × ℤ :=
    { toFun := fun p => p.1.2
      invFun := fun q => ⟨(m, q), rfl⟩
      left_inv := fun p => by
        obtain ⟨⟨m', q⟩, h⟩ := p; change m' = m at h; subst h; rfl
      right_inv := fun q => rfl }
  set g : ℤ × ℤ → ENNReal := fun q =>
    jitterMeasure ((E3ev θ X₀ m q.1 q.2)ᶜ ∩ QC (okQ θ X₀) (tq θ X₀) q.2.toNat ∩
      goodBefore (Sum.elim (E1ev θ X₀) (e3Family θ X₀).E)
        (Sum.elim (tE1 X₀) (e3Family θ X₀).time) q.2.toNat)
  have hre : ∑' i : {i // (e3Family θ X₀).scale i = m},
      jitterMeasure (((e3Family θ X₀).E i)ᶜ ∩ QC (okQ θ X₀) (tq θ X₀) ((e3Family θ X₀).time i) ∩
        goodBefore (Sum.elim (E1ev θ X₀) (e3Family θ X₀).E)
          (Sum.elim (tE1 X₀) (e3Family θ X₀).time) ((e3Family θ X₀).time i)) =
      ∑' q, g q := by
    rw [← e.symm.tsum_eq]; rfl
  rw [hre]
  -- the support: `a ∈ [⌈u⌉, ⌊2u⌋]`, `b - a ≤ ⌊1.03 H + 1⌋`
  set W := ⌊1.03 * capH X₀ u + 1⌋₊
  set a0 : ℤ := ⌈u⌉
  set a1 : ℤ := ⌊2 * u⌋
  set s : Finset (ℤ × ℤ) :=
    (Finset.Icc a0 a1 ×ˢ Finset.range (W + 1)).image fun x => (x.1, x.1 + x.2)
  have hsupp : ∀ q ∉ s, g q = 0 := by
    intro q hq
    simp only [g]
    by_cases hadm : AdmW X₀ m q.1 q.2
    · exfalso; apply hq
      obtain ⟨hua, hab, hb2, hW⟩ := hadm
      refine Finset.mem_image.mpr ⟨(q.1, (q.2 - q.1).toNat), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hua, ?_⟩,
          Finset.mem_range.mpr ?_⟩
        · apply Int.le_floor.mpr
          have : (q.1 : ℝ) < q.2 := by exact_mod_cast hab
          linarith
        · have h0 : 0 ≤ q.2 - q.1 := by omega
          have h1 : (q.2 - q.1).toNat ≤ W := by
            apply Nat.le_floor
            have : (((q.2 - q.1).toNat : ℕ) : ℝ) = ((q.2 - q.1 : ℤ) : ℝ) := by
              rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
            rw [this]; exact hW
          omega
      · have h0 : 0 ≤ q.2 - q.1 := by omega
        simp only [Int.toNat_of_nonneg h0]; ext <;> simp
    · have : (E3ev θ X₀ m q.1 q.2)ᶜ = ∅ := by
        ext ω; simp only [E3ev, mem_compl_iff, mem_setOf_eq, mem_empty_iff_false, iff_false,
          not_not]
        intro h; exact absurd h hadm
      rw [this]; simp
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ q ∈ s, g q ≤ c := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    simp only [g]
    by_cases hadm : AdmW X₀ m x.1 (x.1 + x.2)
    · refine le_trans (measure_mono ?_) (e3_window hc hC hS hadm)
      rintro ω ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun n hn => ?_⟩
      simp only [goodBefore, mem_iInter] at h3
      exact h3 (Sum.inl n) hn
    · have : (E3ev θ X₀ m x.1 (x.1 + x.2))ᶜ = ∅ := by
        ext ω; simp only [E3ev, mem_compl_iff, mem_setOf_eq, mem_empty_iff_false, iff_false,
          not_not]
        intro h; exact absurd h hadm
      rw [this]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≤ (u + 1) * (1.03 * capH X₀ u + 2) := by
    have h1 : s.card ≤ (Finset.Icc a0 a1).card * (W + 1) := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_range]
    have h2 : ((Finset.Icc a0 a1).card : ℝ) ≤ u + 1 := by
      rw [Int.card_Icc]
      have hb0 : (u : ℝ) ≤ a0 := Int.le_ceil u
      have hb1 : (a1 : ℝ) ≤ 2 * u := Int.floor_le _
      rcases le_or_gt a0 (a1 + 1) with h | h
      · have : ((a1 + 1 - a0).toNat : ℝ) = ((a1 + 1 - a0 : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        rw [this]; push_cast; linarith
      · rw [Int.toNat_of_nonpos (by omega)]; simp; linarith
    have h3 : ((W : ℕ) : ℝ) ≤ 1.03 * capH X₀ u + 1 := Nat.floor_le (by linarith)
    have : (s.card : ℝ) ≤ ((Finset.Icc a0 a1).card : ℝ) * ((W : ℝ) + 1) := by
      exact_mod_cast h1
    refine this.trans ?_
    exact mul_le_mul h2 (by linarith) (by positivity) (by linarith)
  have hnum := e3_numeric hc m
  rw [← hudef] at hnum
  have hc0 : 0 ≤ 4 * Real.exp (-lamE3 X₀ u) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc (s.card : ℝ) * (4 * Real.exp (-lamE3 X₀ u))
      ≤ ((u + 1) * (1.03 * capH X₀ u + 2)) * (4 * Real.exp (-lamE3 X₀ u)) :=
        mul_le_mul_of_nonneg_right hcard hc0
    _ ≤ 1.2 / u ^ 2 := hnum

end Window

end Queue6

end
