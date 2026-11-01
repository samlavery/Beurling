module

public import RequestProject.Beurling.Noise.RML12HJ
public import RequestProject.Beurling.Model.JXnn

/-!
# The `hj` input of `hsmall_11` for the realised system

`BModel.RML12.hj_all` : for every `t ∈ [X₀^{1.01}, b]`,
`0 ≤ jXdef … t ≤ e^{-59}` for the realised system (`PR θ X₀ ω`, `Hc X₀`, `twR`, `Xm X₀`, the
width parameter `epsH/10`, `λ₀ = lamH`, `j₀ = jzX X₀`, the scale indices `NKc X₀`), i.e. the
hypothesis `hj` of `BModel.RML11.hsmall_11` with `a₄ = e^{-59}` (`hj_all_hsmall`).

The lower bound is `jXnn_c`; the upper bound is `KR.RML12.hj_all_le` (Proposition 5.31(ii) and
(iii)), with the scale index condition from `NKc_spec`.
-/

@[expose] public section

open Set Real Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP

namespace BModel.RML12

variable {θ : ℝ} {X₀ : ℕ}

/-- The start-dependent inputs at a start `y` for the realised system (the scale index condition
is supplied by `NKc_spec`): the (H_BS) horizons (Model), Theorem 5.24 at `2(y/X₀)^{0.55}`
(Model / LocalPNT) and Lemma 5.29 up to `y` (`ShortRecip`, Queue6). -/
structure HjAtR (P : BeurlingSystem) (X0m Z : ℝ) (X₀ : ℕ) (y : ℝ) : Prop where
  hZ : 2 * y / X0m ≤ Z
  hZ2 : 18 * y ≤ Z ^ 2
  hT : LocalPNT.Theorem524Concl P X₀ (2 * (y / X₀) ^ (0.55 : ℝ))
  hSR : KR.RML9.ShortRecipLow P X₀ y

set_option maxHeartbeats 1000000 in
/-- **`hj` for `hsmall_11`**: `0 ≤ j_{X₀}(t) ≤ e^{-59}` on `[X₀^{1.01}, b]`. -/
theorem hj_all (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b Z η1 η2 εT : ℝ}
    {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT
      (epsH / 10))
    (hX0e : Xm X₀ = X₀ - Queue6.Hc X₀ X₀ / 2) (hH1 : 1 ≤ Queue6.Hc X₀ X₀)
    (hδ : Queue6.Hc X₀ X₀ / X₀ ≤ 1 / 1000)
    (hδs : 200000 * (Queue6.Hc X₀ X₀ / X₀) ≤ Real.exp (-61))
    (hH8 : Queue6.Hc X₀ X₀ ≤ (X₀ : ℝ) ^ (1 / 8 : ℝ)) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j)
    (ht : ∀ r, r.Prime → 0 < twR θ X₀ ω r)
    (htv : ∀ r, r.Prime → (PR θ X₀ ω).labelVal r ≤ 2 * twR θ X₀ ω r)
    (hjz : jzX X₀ ≤ 1.0001 / Real.log X₀) (hZ0 : 2500 ≤ Z)
    (hA : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → ∀ y, InW (Queue6.Hc X₀ t) t y →
      HjAtR (PR θ X₀ ω) (Xm X₀) Z X₀ y) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      0 ≤ jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ∧
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ≤ Real.exp (-59) := by
  have hlam : 1 + 2 * (epsH / 10) ≤ lamH := by unfold epsH lamH; norm_num
  have hlam1 : lamH ≤ 1.001 := by unfold lamH; norm_num
  have hj0 := jzX_nonneg hc
  have hHw := KR.WidthReal.Hc_Xm_half_le hc.hX (X₀ := X₀)
  intro t ht1 htb
  refine ⟨jXnn_c hc hev htnp (by unfold lamH; norm_num) hj0 (NKc X₀) t, ?_⟩
  refine KR.RML12.hj_all_le htnp hX0e hH1 hδ hδs hH8 hp2 ht htv hlam hlam1 hHw hj0 hjz hZ0
    (fun t' ht' htb' y hy => ?_) t ht1 htb
  obtain ⟨hZ, hZ2, hT, hSR⟩ := hA t' ht' htb' y hy
  obtain ⟨-, -, hK⟩ := NKc_spec hc y
  exact ⟨hZ, hZ2, hT, hSR, fun v hv => sqrt_le_Pk hK (dyScales_le hv)⟩

end BModel.RML12

end
