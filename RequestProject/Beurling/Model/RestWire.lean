module

public import RequestProject.Beurling.Model.RestData
public import RequestProject.Beurling.Noise.RML8GField

/-!
# Lemma 5.34 for the realised system: the Model parts of `hK` and `hG`

`F_r := (B - 1)T_c + ϑ/H - ν - NT` (the source of the first bullet) and
`F_c := B(T_c + J) + ϑ/H - ν - NT - BJ = T_c + F_r` (`Fc_eq`); the second bullet reads
`(1 - B)F_c` (`BModel.RML7.Fcex`).

* `LMb_Frx`, `LMb_Fcex`, `LMb_KoFcex` : `F_r`, `(1-B)F_c` and `K_pt (1-B)F_c` are locally bounded
  and measurable (the `LBd`/`Measurable` parts of the inputs of `RML7.hK_field`,
  `RML7.hG_field_paper`);
* `Jc` : the number of dyadic blocks `[X₀⁻2ʲ, X₀⁻2ʲ⁺¹)` below `x + H(x)/2` (`Jc_spec`);
* `blockG_le` : **the block bound** `|(1-B)F_c(s)| ≤ o_j + 2(F̄_{j-1} + F̄_j + F̄_{j+1})`
  (04f-bridge.tex, `lem:predictable`: `sup_{[v,2v)} |(1-B)F_c| ≤ o_v + 2 max F̄_r(v')`), from
  the oscillation `o_j` of `T_c` on the windows and the block bounds `F̄_i` of `|F_r|`, via
  `KR.RML7G.abs_sub_Bavg_le`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `F_r = (B - 1)T_c + ϑ/H - ν - NT`. -/
noncomputable abbrev Frx {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL NT vtH : KR.Ops.LocInt) (j0 : ℝ) : KR.Ops.LocInt :=
  (KR.Ops.Bo hO TcL - TcL) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT

/-- `F_c` (before `1 - B`). -/
noncomputable abbrev Fcx {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL NT vtH : KR.Ops.LocInt) (j0 : ℝ) : KR.Ops.LocInt :=
  KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT -
    NT - KR.Ops.Bo hO (JL j0 X₀)

/-- `F_c = T_c + F_r` (`B` is linear). -/
lemma Fc_eq {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL NT vtH : KR.Ops.LocInt) (j0 : ℝ) (r : ℝ) :
    (Fcx hO ρL TcL NT vtH j0 : ℝ → ℝ) r =
      (TcL : ℝ → ℝ) r + (Frx hO ρL TcL NT vtH j0 : ℝ → ℝ) r := by
  have hadd := (KR.Ops.Bo hO).map_add TcL (JL j0 X₀)
  have e : ((KR.Ops.Bo hO (TcL + JL j0 X₀) : KR.Ops.LocInt) : ℝ → ℝ) r =
      ((KR.Ops.Bo hO TcL : KR.Ops.LocInt) : ℝ → ℝ) r +
        ((KR.Ops.Bo hO (JL j0 X₀) : KR.Ops.LocInt) : ℝ → ℝ) r := by
    rw [hadd]; rfl
  simp only [Fcx, Frx, AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply]
  rw [e]; ring

lemma LMb_nuRes {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {ρL TcL NT vtH : KR.Ops.LocInt} (j0 : ℝ) (hρ : LMb ρL) (hT : LMb TcL) (hN : LMb NT)
    (hv : LMb vtH) : LMb (nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT) := by
  unfold nuRes
  exact ((((hT.add (LMb.JL j0)).Bo hO).add hv).sub hN |>.sub hρ).sub ((hρ.Ko hO).Bo hO)

lemma LMb_Frx {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {ρL TcL NT vtH : KR.Ops.LocInt} (j0 : ℝ) (hρ : LMb ρL) (hT : LMb TcL) (hN : LMb NT)
    (hv : LMb vtH) : LMb (Frx hO ρL TcL NT vtH j0) :=
  ((((hT.Bo hO).sub hT).add hv).sub (LMb_nuRes hO j0 hρ hT hN hv)).sub hN

lemma LMb_Fcx {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {ρL TcL NT vtH : KR.Ops.LocInt} (j0 : ℝ) (hρ : LMb ρL) (hT : LMb TcL) (hN : LMb NT)
    (hv : LMb vtH) : LMb (Fcx hO ρL TcL NT vtH j0) :=
  (((((hT.add (LMb.JL j0)).Bo hO).add hv).sub (LMb_nuRes hO j0 hρ hT hN hv)).sub hN).sub
    ((LMb.JL j0).Bo hO)

lemma LMb_Fcex {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {ρL TcL NT vtH : KR.Ops.LocInt} (j0 : ℝ) (hρ : LMb ρL) (hT : LMb TcL) (hN : LMb NT)
    (hv : LMb vtH) : LMb (RML7.Fcex hO ρL TcL NT vtH j0) :=
  (LMb_Fcx hO j0 hρ hT hN hv).sub ((LMb_Fcx hO j0 hρ hT hN hv).Bo hO)

open Classical in
variable (X₀) in
/-- The number of dyadic blocks of `X₀⁻` below `x + H(x)/2`: the least `n` with
`(x + H(x)/2)/X₀⁻ < 2ⁿ`. -/
noncomputable def Jc (x : ℝ) : ℕ :=
  Nat.find (pow_unbounded_of_one_lt ((x + Queue6.Hc X₀ x / 2) / Xm X₀)
    (one_lt_two : (1 : ℝ) < 2))

lemma Jc_spec (hX : 0 < Xm X₀) (x : ℝ) : x + Queue6.Hc X₀ x / 2 ≤ Xm X₀ * 2 ^ Jc X₀ x := by
  classical
  have h := Nat.find_spec (pow_unbounded_of_one_lt ((x + Queue6.Hc X₀ x / 2) / Xm X₀)
    (one_lt_two : (1 : ℝ) < 2))
  rw [div_lt_iff₀ hX] at h
  unfold Jc; linarith

/-- **`Jc` is least**: `X₀⁻ 2^{Jc x} ≤ max(X₀⁻, 2(x + H(x)/2))`. -/
lemma Jc_le (hX : 0 < Xm X₀) (x : ℝ) :
    Xm X₀ * 2 ^ Jc X₀ x ≤ max (Xm X₀) (2 * (x + Queue6.Hc X₀ x / 2)) := by
  classical
  rcases h0 : Jc X₀ x with _ | n
  · simp
  · have hmin := Nat.find_min (pow_unbounded_of_one_lt ((x + Queue6.Hc X₀ x / 2) / Xm X₀)
      (one_lt_two : (1 : ℝ) < 2)) (m := n) (by
        have : Jc X₀ x = Nat.find (pow_unbounded_of_one_lt ((x + Queue6.Hc X₀ x / 2) / Xm X₀)
          (one_lt_two : (1 : ℝ) < 2)) := rfl
        omega)
    push_neg at hmin
    rw [le_div_iff₀ hX] at hmin
    rw [pow_succ]
    exact le_max_of_le_right (by nlinarith)

set_option maxHeartbeats 1000000 in
/-- **The block bound of the second bullet** (`lem:predictable`): on the block
`[X₀⁻2ʲ, X₀⁻2ʲ⁺¹)` below `(x + H(x)/2)/2`, `|(1 - B)F_c| ≤ o_j + 2(F̄_{j-1} + F̄_j + F̄_{j+1})`,
given the oscillation `o_j` of `T_c` on the windows and `|F_r| ≤ F̄_i` on the blocks (block `0`
taken as `(-∞, 2X₀⁻)`) at the heights read, `≤ 0.6x` (correction #109). -/
theorem blockG_le {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL NT vtH : KR.Ops.LocInt) (j0 : ℝ) {x : ℝ} (ob Fb : ℕ → ℝ) (hF0 : ∀ i, 0 ≤ Fb i)
    (hosc : ∀ j s r, Xm X₀ * 2 ^ j ≤ s → s < 2 * (Xm X₀ * 2 ^ j) →
      s ≤ (x + Queue6.Hc X₀ x / 2) / 2 → |r - s| ≤ Queue6.Hc X₀ s / 2 →
      |(TcL : ℝ → ℝ) r - (TcL : ℝ → ℝ) s| ≤ ob j)
    (hFr : ∀ i r, r ≤ 0.6 * x → r < 2 * (Xm X₀ * 2 ^ i) → (i = 0 ∨ Xm X₀ * 2 ^ i ≤ r) →
      |(Frx hO ρL TcL NT vtH j0 : ℝ → ℝ) r| ≤ Fb i)
    (j : ℕ) (s : ℝ) (hs1 : Xm X₀ * 2 ^ j ≤ s) (hs2 : s < 2 * (Xm X₀ * 2 ^ j))
    (hs3 : s ≤ (x + Queue6.Hc X₀ x / 2) / 2) :
    |((RML7.Fcex hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) s| ≤ KR.RML8G.Mpap ob Fb j := by
  have hX := hO.X0m_pos
  have hHs := hO.pos s
  have hv0 : 0 < Xm X₀ * 2 ^ j := by positivity
  have hsm : Xm X₀ / 2 ≤ s := by
    have : Xm X₀ ≤ Xm X₀ * 2 ^ j := le_mul_of_one_le_right hX.le (one_le_pow₀ (by norm_num))
    linarith
  have hsmall := hO.small s hsm
  have hxm : Xm X₀ / 2 ≤ x := by
    by_contra h; push_neg at h
    have := hO.low x h
    linarith
  have hHx := hO.small x hxm
  have hx0 : s ≤ x := by linarith
  set Rb := (if j = 0 then 0 else Fb (j - 1)) + Fb j + Fb (j + 1) with hRb
  have hR : ∀ r, s - Queue6.Hc X₀ s / 2 ≤ r → r ≤ s + Queue6.Hc X₀ s / 2 →
      |(Frx hO ρL TcL NT vtH j0 : ℝ → ℝ) r| ≤ Rb := by
    intro r hr1 hr2
    have hrx : r ≤ 0.6 * x := by nlinarith
    have hp1 := hF0 (j + 1)
    have hp0 := hF0 j
    have hpm : 0 ≤ (if j = 0 then 0 else Fb (j - 1)) := by
      split_ifs
      · exact le_rfl
      · exact hF0 _
    rcases lt_or_ge r (Xm X₀ * 2 ^ j) with h1 | h1
    · rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        have := hFr 0 r hrx (by rw [pow_zero, mul_one] at h1 ⊢; linarith) (Or.inl rfl)
        have := hF0 1
        simp only [hRb, if_pos rfl, zero_add, if_true]; linarith
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have e : Xm X₀ * 2 ^ (k + 1) = 2 * (Xm X₀ * 2 ^ k) := by ring
        have hk : Xm X₀ * 2 ^ k ≤ r := by rw [e] at hs1 h1; nlinarith
        have := hFr k r hrx (by rw [e] at h1; linarith) (Or.inr hk)
        simp only [hRb, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        linarith
    · rcases lt_or_ge r (2 * (Xm X₀ * 2 ^ j)) with h2 | h2
      · have := hFr j r hrx h2 (Or.inr h1)
        simp only [hRb]; linarith
      · have e : Xm X₀ * 2 ^ (j + 1) = 2 * (Xm X₀ * 2 ^ j) := by ring
        have := hFr (j + 1) r hrx (by rw [e]; nlinarith) (Or.inr (by rw [e]; exact h2))
        simp only [hRb]; linarith
  have hint : IntervalIntegrable ((Fcx hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) volume
      (s - Queue6.Hc X₀ s / 2) (s + Queue6.Hc X₀ s / 2) := (Fcx hO ρL TcL NT vtH j0).2 _ _
  have hB := KR.RML7G.abs_sub_Bavg_le hHs (Fc_eq hO ρL TcL NT vtH j0) hint
    (fun r h1 h2 => hosc j s r hs1 hs2 hs3 (by rw [abs_le]; constructor <;> linarith)) hR
  have e : ((RML7.Fcex hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) s =
      ((Fcx hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) s -
        Margin.Bavg (Queue6.Hc X₀ s) ((Fcx hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) s := rfl
  rw [e]
  refine hB.trans ?_
  unfold KR.RML8G.Mpap
  rw [← hRb]

end BModel

end
