module

public import RequestProject.Beurling.Noise.RML10Rest
public import RequestProject.Beurling.Noise.RML7GMain

/-!
# The field `hS4` of `RestMargin` (Proposition 5.38, Step 4)

`hS4_11` gives the field `hS4` from the Step 4 decomposition at each `t ∈ [T₀, b]`, with the
weights `ω_t(v)` of Lemma 5.21 bounded by `Margin.Var.logt_omega_le`
(`log t · ω_t(v) ≤ 2.9 log(3v)`, Lemma 5.21 (i)–(ii) with Rankin), via `Margin.RML6.hS4_of`
(`Margin.Var.step4`). The decision order for Lemma 5.21 (`DecidedSmall`) comes from
`TNP.Hyp` (`KR.RML7G.decidedSmall_of`).

The remaining inputs at each `t` are bundled in `S4At` (Queue6: Lemma 5.22's `ν, δ` and the
Step 4 decomposition; Model: the sizes).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML11

variable {θ : ℝ} {X₀ : ℕ}

/-- **The Step 4 data at a height `t`** (Proposition 5.38, Step 4, 04g-margin.tex): a finite
set of dyadic scales `Vs`, Lemma 5.22's `ν, δ ≥ 0` at these scales, the oscillation and
filter-switching sizes `o, η` with `log t · o ≤ so`, `log t · η ≤ sη`, the Step 4
decomposition `o_V + 2η_V + ∑_w e/w ≤ o + 2η + 4 ∑ ω ν + 1.0001 ∑ ω δ` (with
`ω v = ω_t(v)`, the filtered cofactor weight of Lemma 5.21), and the size
`so + 2 sη + 27 ∑ log(3v) ν + 4.3 ∑ log(3v) δ ≤ E_S`. -/
structure S4At (ω : JitterΩ) (M ES jP Z t : ℝ) : Type where
  Vs : Finset ℝ
  ν : ℝ → ℝ
  δ : ℝ → ℝ
  o : ℝ
  η : ℝ
  so : ℝ
  sη : ℝ
  /-- the scales: `v > 0`, `log 3v ≥ 10⁸`, `t/v ≤ Z` (the (HBS) horizon of Lemma 5.21) -/
  hv : ∀ v ∈ Vs, 0 < v ∧ 100000000 ≤ Real.log (3 * v) ∧ t / v ≤ Z
  hν : ∀ v ∈ Vs, 0 ≤ ν v
  hδ : ∀ v ∈ Vs, 0 ≤ δ v
  ho : Real.log t * o ≤ so
  hη : Real.log t * η ≤ sη
  /-- the Step 4 decomposition (Queue6: Lemma 5.22 on the windows) -/
  hS : (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t +
      ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
        RML10.e10 X₀ (PR θ X₀ ω) M t w / KR.Vl (PR θ X₀ ω) w ≤
      o + 2 * η + 4 * ∑ v ∈ Vs, (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v * ν v +
        1.0001 * ∑ v ∈ Vs, (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v * δ v
  /-- the size of Step 4 -/
  hES : so + 2 * sη + 27 * ∑ v ∈ Vs, Real.log (3 * v) * ν v +
      4.3 * ∑ v ∈ Vs, Real.log (3 * v) * δ v ≤ ES

lemma omegaW_nonneg (P : BeurlingSystem) (tw : ℕ → ℝ) (y v : ℝ) : 0 ≤ P.omegaW tw y v := by
  unfold BeurlingSystem.omegaW
  exact Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le

/-- **The field `hS4`** of `RestMargin`. -/
theorem hS4_11 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {M : ℝ} (ES jP b : ℝ)
    {Z η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT)
    (D : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → S4At (θ := θ) (X₀ := X₀) ω M ES jP Z t) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t + ∑ w ∈ Margin.Rec.Fset
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t, RML10.e10 X₀ (PR θ X₀ ω) M t w /
          KR.Vl (PR θ X₀ ω) w ≤ (RML7.canonP X₀ epsH ES jP).ES / Real.log t := by
  intro t ht htb
  have h1 := RML10.T0_gt_one hX ES jP
  have ht1 : 1 < t := by linarith
  set d := D t ht htb
  have hω : ∀ v ∈ d.Vs, Real.log t *
      (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v ≤ 2.9 * Real.log (3 * v) := by
    intro v hv
    obtain ⟨hv0, hL, hZ⟩ := d.hv v hv
    exact Margin.Var.logt_omega_le htnp.hbs (KR.RML7G.decidedSmall_of htnp hv0) hv0 hL
      (by linarith) hZ
  have hS4 := Margin.RML6.hS4_of d.Vs
    (fun v => (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v) d.ν d.δ ht1 d.ho d.hη
    d.hν d.hδ (fun v _ => omegaW_nonneg _ _ _ _) hω d.hS d.hES
  exact hS4

end BModel.RML11

end
