module

public import RequestProject.Beurling.BaseRange.Lemma73Final
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# Lemma 7.3 for the realised system of the construction

`lemma73Inputs_R` : **`Lemma73Inputs`** for `P = PR θ X₀ ω`, `t = Queue6.twR`, `X₀⁻ = Xm X₀`,
`H = Hc X₀`, on `SG`, from (HBS) on `[1, Z]`, the local count of `BModel.hbs_local`, the width
inputs of `paperWidth_Hc` and (huxley). (`BModel.twR_eq` identifies `Queue6.twR (hokR hc ω)`
with the `twR θ X₀ ω` of `MarginObjects`.)
-/

@[expose] public section

open Real Finset BeurlingSystem Construction BModel CaplLink

namespace BaseRange

variable {θ : ℝ} {X₀ : ℕ}

/-- The primes below `X₀⁻` are rational, decided at their value. -/
theorem twR_eq_below_Xm (hc : Cond θ X₀) (ω : JitterΩ) (j : ℕ)
    (hj : (Queue6.PR θ X₀ ω).p j < Xm X₀) :
    Queue6.twR (Queue6.hokR hc ω) (qp j) = (Queue6.PR θ X₀ ω).p j := by
  rw [Queue6.twR_qp, Queue6.PR_p hc ω]
  rw [Queue6.PR_p hc ω] at hj
  rcases hi : (Queue6.hokR hc ω).equiv j with p | k
  · rfl
  · exfalso
    rw [hi] at hj
    have h1 : Xm X₀ ≤ valF θ X₀ k.1 ω := valF_ge_Xm hc k.1 ω
    simp only [realisedVal] at hj
    change valF θ X₀ k.1 ω < Xm X₀ at hj
    linarith

/-- `t(p) ≤ p` below `X₀⁻` (the hypothesis `hdec` of the edge expansion). -/
theorem twR_le_labelVal (hc : Cond θ X₀) (ω : JitterΩ) :
    ∀ p, p.Prime → (Queue6.PR θ X₀ ω).labelVal p < Xm X₀ →
      Queue6.twR (Queue6.hokR hc ω) p ≤ (Queue6.PR θ X₀ ω).labelVal p := by
  intro p hp hlt
  have hq : qp (Nat.count Nat.Prime p) = p := exists_qp_eq hp
  have hl : (Queue6.PR θ X₀ ω).labelVal p = (Queue6.PR θ X₀ ω).p (Nat.count Nat.Prime p) := rfl
  rw [hl] at hlt ⊢
  conv_lhs => rw [← hq]
  rw [twR_eq_below_Xm hc ω _ hlt]

/-- **Lemma 7.3's inputs for the realised system**, all parts proved. -/
theorem lemma73Inputs_R (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    {Z η1 η2 ε : ℝ} {ε1 : ℝ → ℝ} (hbs : (Queue6.PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : KR.WidthReal.CapHSlope X₀ ε)
    (hD : KR.WidthReal.CapHDiff X₀) (hH : HuxleyFrom X₀) (hXZ : (X₀ : ℝ) ≤ Z) {xmax : ℝ}
    (hZ : xmax / Xm X₀ ≤ Z)
    (hloc : ∀ v, Xm X₀ ≤ v → v ≤ Z →
      |(Queue6.PR θ X₀ ω).N v - ⌊v⌋₊| ≤ Construction.hbsEps X₀ v * v) :
    Lemma73Inputs X₀ xmax
      (mu0R (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀)
      (KR.Sharp.mu1R (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (Queue6.PR θ X₀ ω) (Queue6.twR (Queue6.hokR hc ω)) (Xm X₀) X₀) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hX
  have hXp : ¬ X₀.Prime := by
    intro hp
    have h2 : X₀ = 2 := (Nat.Prime.even_iff hp).mp hev
    have : (3 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀); rw [Real.exp_log hX0] at this; linarith
    rw [h2] at this; norm_num at this
  have hT := Queue6.tnpHyp_R hc hev hSG hX1 hbs
    (KR.WidthReal.paperWidth_Hc hX hε0 hε hS hD)
  obtain ⟨h1, h2⟩ := Xm_facts hc
  exact lemma73Inputs_tnp hT hX hH hXp h1 h2 hXZ (twR_le_labelVal hc ω) hZ hloc
    (Hc_Xm_half_le_kappa hc)

end BaseRange
