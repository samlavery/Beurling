module

public import RequestProject.Beurling.Noise.RML8GMain
public import RequestProject.Beurling.Noise.RML7Fields
public import RequestProject.Beurling.Noise.Saias59

/-!
# Lemma 5.34, second bullet (correction #110), with the constant `35.8 C_N C'_S`

The paper (04f-bridge.tex, `lem:predictable`):

  `log x · |(B R_res G)(x)| ≤ 5.1 C_N C'_S ∑_v (log 3v)² sup_{[v,2v)} |(1-B)F_c|
                           ≤ 35.8 C_N C'_S ∑_v (log 3v)² F̄_r(v)`,

with `sup_{[v,2v)}|(1-B)F_c| ≤ o_v + 2 max_{v' ∈ {v/2, v, 2v}} F̄_r(v')`, `o_v ≤ F̄_r(v)`, the
max bounded by the sum of its three terms and reindexed (weight `1 + 2 + 2 + 2(1 + 10⁻⁷)`), and
`5.1 · 7.0001 ≤ 35.8`.

* `Mpap o Fb j = o j + 2 (Fb (j-1) + Fb j + Fb (j+1))` (with `Fb (-1) := 0`: blocks below `X₀⁻`
  contribute `0`) is the paper's block bound of `(1-B)F_c`;
* `reindex7` : `∑_{j<J} (log 3v_j)² Mpap j ≤ 7.0001 ∑_{i ≤ J} (log 3v_i)² Fb i`;
* `BModel.RML7.hG_field_paper` : **the field `hG` of `RealMarginLoc`** with
  `bb x = 35.8 · C_N · 10 · ∑_{i ≤ J} (log 3v_i)² F̄_r(x, i)`, from the block bounds
  `|(1-B)F_c| ≤ Mpap` (inputs: `o_v`, `F̄_r(v) = o_v + 6/H(v) + ν̄(v) + 54 sup η`).
  The kernel side is `hG_field` with `gScaleBound_Kpt_tight` (`A = C'_S ∑ (log 3v)² Mpap`,
  `C'_S = 10`); the factor `(1 + 5.1 C_N)·log x/log(x - H/2)` is `≤ 5.1·1.0002 C_N`, which with
  `7.0001` gives `≤ 35.8 C_N` (`C_N ≥ 143`).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP KR.Chain

namespace KR.RML8G

/-- The paper's block bound of `(1 - B)F_c` on `[v_j, 2v_j)`:
`o_j + 2(F̄_{j-1} + F̄_j + F̄_{j+1})` (`F̄_{-1} := 0`). -/
noncomputable def Mpap (o Fb : ℕ → ℝ) (j : ℕ) : ℝ :=
  o j + 2 * ((if j = 0 then 0 else Fb (j - 1)) + Fb j + Fb (j + 1))

lemma Mpap_nonneg {o Fb : ℕ → ℝ} (ho : ∀ j, 0 ≤ o j) (hF : ∀ j, 0 ≤ Fb j) (j : ℕ) :
    0 ≤ Mpap o Fb j := by
  unfold Mpap
  have := hF j; have := hF (j + 1); have := ho j
  have h0 : 0 ≤ (if j = 0 then 0 else Fb (j - 1)) := by split_ifs <;> simp [hF]
  positivity

/-- **The reindexing of correction #110**: if `L` increases by `log 2` per block, `L ≥ 10⁸`,
and `0 ≤ o ≤ F̄`, then `∑_{j<J} L_j² Mpap j ≤ 7.0001 ∑_{i<J+1} L_i² F̄_i`. -/
theorem reindex7 {L o Fb : ℕ → ℝ} (hL : ∀ i, 100000000 ≤ L i)
    (hstep : ∀ i, L (i + 1) = L i + Real.log 2) (ho : ∀ j, 0 ≤ o j) (hoF : ∀ j, o j ≤ Fb j)
    (J : ℕ) :
    ∑ j ∈ range J, L j ^ 2 * Mpap o Fb j ≤ 7.0001 * ∑ i ∈ range (J + 1), L i ^ 2 * Fb i := by
  have hF : ∀ j, 0 ≤ Fb j := fun j => (ho j).trans (hoF j)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : ∀ i, L i ^ 2 ≤ L (i + 1) ^ 2 := fun i => by
    rw [hstep i]; have := hL i; nlinarith
  have hup : ∀ i, L (i + 1) ^ 2 ≤ (1 + 1 / 10 ^ 7) * L i ^ 2 := fun i => by
    rw [hstep i]; have := hL i; nlinarith
  set S := ∑ i ∈ range (J + 1), L i ^ 2 * Fb i
  have hw0 : ∀ i, 0 ≤ L i ^ 2 * Fb i := fun i => mul_nonneg (sq_nonneg _) (hF i)
  have hSJ : ∑ j ∈ range J, L j ^ 2 * Fb j ≤ S := by
    have := Finset.sum_range_succ (fun i => L i ^ 2 * Fb i) J
    linarith [hw0 J]
  -- the four pieces
  have h1 : ∑ j ∈ range J, L j ^ 2 * o j ≤ S :=
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hoF j) (sq_nonneg _)).trans hSJ
  have h3 : ∑ j ∈ range J, L j ^ 2 * Fb (j + 1) ≤ S := by
    calc ∑ j ∈ range J, L j ^ 2 * Fb (j + 1) ≤ ∑ j ∈ range J, L (j + 1) ^ 2 * Fb (j + 1) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmono j) (hF _)
      _ ≤ S := by
          have := Finset.sum_range_succ' (fun i => L i ^ 2 * Fb i) J
          linarith [hw0 0]
  have h4 : ∑ j ∈ range J, L j ^ 2 * (if j = 0 then 0 else Fb (j - 1)) ≤
      (1 + 1 / 10 ^ 7) * S := by
    rcases J with _ | J
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hw0 i)
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, if_true, mul_zero, add_zero, Nat.succ_ne_zero, if_false]
    calc ∑ i ∈ range J, L (i + 1) ^ 2 * Fb i ≤ ∑ i ∈ range J, (1 + 1 / 10 ^ 7) *
          (L i ^ 2 * Fb i) :=
          Finset.sum_le_sum fun i _ => by nlinarith [hup i, hF i]
      _ = (1 + 1 / 10 ^ 7) * ∑ i ∈ range J, L i ^ 2 * Fb i := by rw [Finset.mul_sum]
      _ ≤ (1 + 1 / 10 ^ 7) * S := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
          · intro i _ _; exact hw0 i
  have hexp : ∑ j ∈ range J, L j ^ 2 * Mpap o Fb j =
      ∑ j ∈ range J, (L j ^ 2 * o j + 2 * (L j ^ 2 * (if j = 0 then 0 else Fb (j - 1))) +
        2 * (L j ^ 2 * Fb j) + 2 * (L j ^ 2 * Fb (j + 1))) :=
    Finset.sum_congr rfl fun j _ => by unfold Mpap; ring
  rw [hexp, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw0 i
  nlinarith

end KR.RML8G

namespace BModel.RML7

variable {θ : ℝ} {X₀ : ℕ} {ω : JitterΩ}

/-- `C_N ≥ 143`. -/
lemma CNt_ge (hX : 10 ^ 8 ≤ Real.log X₀) : 143 ≤ CNt X₀ := by
  have hP := BeurlingSystem.Cor59.PhiInf_ge (τ := 100000000) (by norm_num)
  have he := BeurlingSystem.Cor59.exp4_ge
  have hm : 2.01 * BSaias.PhiInf 100000000 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_left _ _
  have hl : 0 ≤ 4.71 / Real.log X₀ := div_nonneg (by norm_num) (by linarith)
  unfold CNt
  nlinarith

/-- The source of the second bullet: `(1 - B)F_c` with
`F_c = B(T_c + J) + ϑ/H - ν - NT - BJ`. -/
noncomputable abbrev Fcex (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL NT vtH : KR.Ops.LocInt) (j0 : ℝ) : KR.Ops.LocInt :=
  (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT -
      NT - KR.Ops.Bo hO (JL j0 X₀)) -
    KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
      nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀))

set_option maxHeartbeats 1000000 in
/-- **The field `hG` of `RealMarginLoc` with the paper's constant** (Lemma 5.34, second
bullet, correction #110): with block bounds `|(1-B)F_c| ≤ o_j + 2(F̄_{j-1} + F̄_j + F̄_{j+1})`
on `[X₀⁻2^j, X₀⁻2^{j+1})` (below `(x + H(x)/2)/2`), `0 ≤ o_j ≤ F̄_j`,
`bb x = 35.8 · C_N · C'_S · ∑_{i ≤ J} (log 3v_i)² F̄_i`, `C'_S = 10`. -/
theorem hG_field_paper {Z η1 η2 ε lam0 b j0 : ℝ} {ε1 : ℝ → ℝ}
    (htnp : TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε (ε / 10))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j)
    (hlam : 1 + 3 * (ε / 10) ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z) (hZ18 : 18 * (b + Queue6.Hc X₀ b) ≤ Z ^ 2)
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θ
      (b + Queue6.Hc X₀ b))
    (ρL TcL NT vtH : KR.Ops.LocInt)
    (Nf Kf : ℝ → ℕ) (hNf : ∀ y, y < (X₀ : ℝ) * 2 ^ Nf y / 4)
    (hKf : ∀ y, √(2 * y) ≤ Pk (Xm X₀) (Kf y)) (Jf : ℝ → ℕ) (Fb ob : ℝ → ℕ → ℝ)
    (hJ : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      x + Queue6.Hc X₀ x / 2 ≤ Xm X₀ * 2 ^ Jf x)
    (hob : ∀ x j, 0 ≤ ob x j ∧ ob x j ≤ Fb x j)
    (hGf : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀),
      KR.Ops.LBd ((KR.Ops.Ko (tw := twR θ X₀ ω) hO (Fcex hO ρL TcL NT vtH j0) :
          KR.Ops.LocInt) : ℝ → ℝ) ∧
      Measurable ((KR.Ops.Ko (tw := twR θ X₀ ω) hO (Fcex hO ρL TcL NT vtH j0) :
          KR.Ops.LocInt) : ℝ → ℝ) ∧
      ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → ∀ j < Jf x, ∀ s,
        Xm X₀ * 2 ^ j ≤ s → s < 2 * (Xm X₀ * 2 ^ j) → s ≤ (x + Queue6.Hc X₀ x / 2) / 2 →
        |((Fcex hO ρL TcL NT vtH j0 : KR.Ops.LocInt) : ℝ → ℝ) s| ≤
          KR.RML8G.Mpap (ob x) (Fb x) j) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ro (tw := twR θ X₀ ω) hO
        (KR.Ops.Ko (tw := twR θ X₀ ω) hO (Fcex hO ρL TcL NT vtH j0))) : ℝ → ℝ) x| ≤
        35.8 * CNt X₀ * 10 * ∑ i ∈ range (Jf x + 1),
          Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * Fb x i := by
  intro hO x hx hxb
  have hXm8 := htnp.hXm
  have hXmpos := htnp.width.X0m_pos
  have hX12 : (12 : ℝ) ≤ X₀ := by
    have h1 : (100000000 : ℝ) ≤ Real.log X₀ := by norm_num at hX ⊢; linarith
    by_contra hc; push_neg at hc
    have : Real.log X₀ ≤ Real.log 12 := Real.log_le_log (by
      have : (0 : ℝ) < X₀ := by
        rcases Nat.eq_zero_or_pos X₀ with h0 | h0
        · rw [h0] at h1; simp at h1; linarith
        · exact_mod_cast h0
      exact this) hc.le
    have : Real.log 12 ≤ 11 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 12 by norm_num); linarith
    linarith
  set A : ℝ → ℝ := fun x => 10 * ∑ j ∈ range (Jf x),
    Real.log (3 * (Xm X₀ * 2 ^ j)) ^ 2 * KR.RML8G.Mpap (ob x) (Fb x) j with hA
  have hGb := hG_field (θ := θ) (X₀ := X₀) (ω := ω) (j0 := j0) htnp hX hp2 hlam hlam1 hZ hZ18
    x0s ρL TcL NT vtH Nf Kf hNf hKf A
    (fun x y u => ∑ j ∈ range (Jf x), KR.RML8G.Mpap (ob x) (Fb x) j *
      KR.RML8G.Om8 (Xm X₀ * 2 ^ j) u)
    (fun hO' => by
      obtain ⟨hL1, hL2, hbd⟩ := hGf hO'
      refine ⟨hL1, hL2, fun x hx hxb => ?_⟩
      obtain ⟨-, -, hxH, hwin⟩ := win_facts hX htnp.width hZ hZ18 hx hxb
      have hx1 : 1 ≤ x - Queue6.Hc X₀ x / 2 := by
        have : (10 : ℝ) ^ 7 ≤ Xm X₀ := htnp.hbs.X0m_ge
        norm_num at this; linarith
      exact KR.RML7G.gScaleBound_Kpt_tight htnp hO' hX12 Nf _ (hJ x hx hxb) hx1
        (fun y h1 h2 => (hwin y h1 h2).2.1) _
        (fun j => KR.RML8G.Mpap_nonneg (fun j => (hob x j).1)
          (fun j => (hob x j).1.trans (hob x j).2) j)
        (hbd x hx hxb)) hO x hx hxb
  refine hGb.trans ?_
  -- the constant
  simp only [bG]
  set C := CNt X₀
  set S := ∑ i ∈ range (Jf x + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * Fb x i
  have hC := CNt_ge hX
  have hFb0 : ∀ j, 0 ≤ Fb x j := fun j => (hob x j).1.trans (hob x j).2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hFb0 i)
  have hLi : ∀ i : ℕ, 100000000 ≤ Real.log (3 * (Xm X₀ * 2 ^ i)) := fun i => by
    have : Xm X₀ ≤ 3 * (Xm X₀ * 2 ^ i) := by
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num); nlinarith
    exact hXm8.trans (Real.log_le_log hXmpos this)
  have hre := KR.RML8G.reindex7 (L := fun i => Real.log (3 * (Xm X₀ * 2 ^ i)))
    (o := ob x) (Fb := Fb x) hLi (fun i => by
      rw [show 3 * (Xm X₀ * 2 ^ (i + 1)) = (3 * (Xm X₀ * 2 ^ i)) * 2 by ring,
        Real.log_mul (by positivity) (by norm_num)])
    (fun j => (hob x j).1) (fun j => (hob x j).2) (Jf x)
  have hAx : A x ≤ 10 * (7.0001 * S) := by
    simp only [hA]; exact mul_le_mul_of_nonneg_left hre (by norm_num)
  have hA0 : 0 ≤ A x := by
    simp only [hA]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
      (KR.RML8G.Mpap_nonneg (fun j => (hob x j).1) hFb0 j))
  -- `log x/log(x - H/2) ≤ log x/(log x - 0.06)`
  obtain ⟨-, -, hxH, -⟩ := win_facts hX htnp.width hZ hZ18 hx hxb
  have hx0 : 0 < x := by linarith [htnp.width.X0m_pos, (KR.WidthReal.Hc_pos hX) x]
  have hsm := htnp.width.small x (by linarith [(KR.WidthReal.Hc_pos hX) x])
  have hX1 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) :=
    Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
  have hlx : 100000000 ≤ Real.log x := by
    have h1 : (100000000 : ℝ) ≤ Real.log X₀ := by norm_num at hX ⊢; linarith
    exact h1.trans (Real.log_le_log (by linarith) (hX1.trans hx))
  have hl95 : Real.log x - 0.06 ≤ Real.log (x - Queue6.Hc X₀ x / 2) := by
    have h1 : 0.95 * x ≤ x - Queue6.Hc X₀ x / 2 := by linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hx0.ne'] at h2
    have h3 : 1 - 1 / 0.95 ≤ Real.log 0.95 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.95 by norm_num)
      simpa [one_div] using this
    norm_num at h3; linarith
  have hlp : 0 < Real.log (x - Queue6.Hc X₀ x / 2) := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hlp]
  have hQ : (1 + 5.1 * C) * A x ≤ (1 + 5.1 * C) * (10 * (7.0001 * S)) :=
    mul_le_mul_of_nonneg_left hAx (by linarith)
  have hkey : Real.log x * ((1 + 5.1 * C) * (10 * (7.0001 * S))) ≤
      35.8 * C * 10 * S * (Real.log x - 0.06) := by
    have e1 : Real.log x * ((1 + 5.1 * C) * (10 * (7.0001 * S))) =
        S * (Real.log x * (70.001 + 357.0051 * C)) := by ring
    have e2 : 35.8 * C * 10 * S * (Real.log x - 0.06) =
        S * (358 * C * Real.log x - 21.48 * C) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ hS0
    nlinarith
  have hlx0 : 0 ≤ Real.log x := by linarith
  calc Real.log x * ((1 + 5.1 * C) * A x)
      ≤ Real.log x * ((1 + 5.1 * C) * (10 * (7.0001 * S))) :=
        mul_le_mul_of_nonneg_left hQ hlx0
    _ ≤ 35.8 * C * 10 * S * (Real.log x - 0.06) := hkey
    _ ≤ 35.8 * C * 10 * S * Real.log (x - Queue6.Hc X₀ x / 2) :=
        mul_le_mul_of_nonneg_left hl95 (by positivity)

end BModel.RML7

end
