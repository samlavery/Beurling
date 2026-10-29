module

public import RequestProject.Beurling.Model.RestK
public import RequestProject.Beurling.Model.OscBlockG

/-!
# Lemma 5.34, second bullet, for the realised system (the field `hG`)

`hG_c` : `BModel.RML7.hG_field_paper` (correction #110, constant `35.8 C_N C'_S`) at the Model
data, with `J = Jc`, `o_j = obG j` (the oscillation of `T_c` on the windows of the block, eq.
(osc)) and `F̄_j = obG j + F̄_r(x, j)`, so

  `bb(x) = 35.8 · C_N · 10 · ∑_{i ≤ J} (log 3v_i)² (obG i + F̄_r(x, i))`.

The block bound of `(1 - B)F_c` is `blockG_le` with `oscG_le`; the remaining input is the block
bound `|F_r| ≤ F̄_r(x, i)` on `[X₀⁻2ⁱ, X₀⁻2ⁱ⁺¹)` (block `0` taken as `(-∞, 2X₀⁻)`) at heights
`≤ x` (`hFrB`; 04f-bridge.tex, `lem:predictable`: `F̄_r = o + 6/H + ν̄ + 54 sup η`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **The field `hG`** (Lemma 5.34, second bullet) at the Model data. -/
theorem hG_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) θ (b + Queue6.Hc X₀ b))
    (FrB : ℝ → ℕ → ℝ) (hFrB0 : ∀ x i, 0 ≤ FrB x i)
    (hFrB : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → ∀ i r, r ≤ x → r < 2 * (Xm X₀ * 2 ^ i) →
        (i = 0 ∨ Xm X₀ * 2 ^ i ≤ r) →
        |((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
          ℝ → ℝ) r| ≤ FrB x i) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ro (tw := twR θ X₀ ω) hO
        (KR.Ops.Ko (tw := twR θ X₀ ω) hO
          (RML7.Fcex hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀)))) : ℝ → ℝ) x| ≤
        35.8 * CNt X₀ * 10 * ∑ i ∈ range (Jc X₀ x + 1),
          Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * (obG X₀ i + FrB x i) := by
  have hX := hc.hX
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  obtain ⟨h1, h2, h3, h4⟩ := Zc_facts hc hb
  have hob0 : ∀ j, 0 ≤ obG X₀ j := fun j => Bsc_nonneg hc (by positivity)
  refine RML7.hG_field_paper hT hX (KR.Chain.p_ge_two_of hT (Xm_le_Zc' hc b))
    (by norm_num [epsH, lamH]) (by norm_num [lamH]) (lam0 := lamH) h4 h3 x0s _ _ _ _
    (fun y => (NKc X₀ y).1) (fun y => (NKc X₀ y).2) (fun y => (NKc_spec hc y).2.1)
    (fun y => (NKc_spec hc y).2.2) (Jc X₀) (fun x i => obG X₀ i + FrB x i)
    (fun _ j => obG X₀ j) (fun x _ _ => Jc_spec hXm x)
    (fun x j => ⟨hob0 j, by linarith [hFrB0 x j]⟩) (fun hO => ⟨?_, ?_, ?_⟩)
  · exact ((LMb_Fcex hO (jzX X₀) (LMb_ρLd hc hev ω) (LMb_TcLd hc hev ω) (LMb_NTd hc hev ω)
      LMb.zero).Ko hO).1
  · exact ((LMb_Fcex hO (jzX X₀) (LMb_ρLd hc hev ω) (LMb_TcLd hc hev ω) (LMb_NTd hc hev ω)
      LMb.zero).Ko hO).2
  · intro x hx hxb j _ s hs1 hs2 hs3
    refine blockG_le hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) (obG X₀)
      (fun i => obG X₀ i + FrB x i) (fun i => by linarith [hob0 i, hFrB0 x i]) ?_ ?_ j s hs1
      hs2 hs3
    · intro j' s' r hs1' hs2' hs3' hr
      rw [TcLd_coe hc hev ω]
      exact oscG_le hc hev hb hbt hQC hE1 hN hT hx hxb j' hs1' hs2' hs3' hr
    · intro i r hr1 hr2 hr3
      have := hFrB hO x hx hxb i r hr1 hr2 hr3
      linarith [hob0 i]

end BModel

end
