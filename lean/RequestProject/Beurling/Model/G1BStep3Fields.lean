module

public import RequestProject.Beurling.Model.G1BJump
public import RequestProject.Beurling.Model.G1BOth

/-!
# The Model fields of Steps 3–4 of `KR.RML6.G1BInputs` (Proposition 5.35(B))

04f-bridge.tex, proof of Proposition 5.35, range (B), Steps 3–4. `step3_R` provides, for the
realised system on range (B) on `Good(< t)`, every Step 3–4 field of
`G1BInputs (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ T' y` except `hthr` (owner Queue6, for
`thrS = threshSum tJ y (2δ)`, recorded in `thrS_eq`), as the structure `Step3Out`:

* `thrS = threshSum tJ y (2δ)`, `j₀ = jzX X₀`, `jS`, `detS`, `othS` and `hdec34`
  (`hdec34_R`);
* `N = y/X₀`, `H_N = H(y/X₀)`, `θ` and `hjS`, `hN`, `hHN0`, `hHN`, `hθ0`, `hθ` (`hjS_R`,
  `hN_R`, `hHN_R`);
* `C_S = 77`, `hdet` (`hdet_R`);
* `hoth` (`hoth_R`).

Named inputs (paper statements, not proved here): `JumpCountR` (Step 3, second bullet, the count
`#(𝒩 ∩ I) ≤ 4.01δN_* + 2H(N_*) + 2 + N_*^{θ/2}`) and `RprimeChangeR` (Step 3 "Resolvable `R'_j`"
with Step 4 "Pointwise"; proved below `x₁` by `rprimeChange_of_lt`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **The Step 3–4 fields of `G1BInputs`** at a start `y` and window parameter `δ`, for
`ρ^sh = rhoSh P tw X₀⁻ · T'` with `T' = T_c + j₀ 1_{[X₀,∞)}`. -/
structure Step3Out (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (Tp : ℝ → ℝ)
    (y δ : ℝ) where
  thrS : ℝ
  j0 : ℝ
  jS : ℝ
  detS : ℝ
  othS : ℝ
  hdec34 : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    rhoSh P tw X0m z Tp - rhoSh P tw X0m y Tp ≤ 4 * thrS + j0 * jS + detS + othS
  N : ℝ
  HN : ℝ
  θ : ℝ
  hj0 : 0 ≤ j0
  hj1 : j0 ≤ 1
  hjS : jS ≤ 4.1 * δ + 3 * HN / N + 2 * N ^ (thetaB θ - 1)
  hN : Real.exp (Real.log y / 2) ≤ N
  hHN0 : 0 ≤ HN
  hHN : HN ≤ N ^ (1 / 8 : ℝ)
  hθ0 : 0 ≤ θ
  hθ : θ ≤ 1 / 2
  CS : ℝ
  hCS0 : 0 ≤ CS
  hCS : CS ≤ 77
  hdet : Real.log y * detS ≤ CS * (7 * Real.log X0 ^ 4 * (X0 : ℝ) ^ (-(1 / 12) : ℝ) +
    90 * Real.log X0 ^ (4.7 : ℝ) * Real.exp (-(Real.log X0 / 12)))
  hoth : Real.log y * othS ≤ 1 / 10 ^ 27

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- `δ ≤ X₀^{-1/2}` forces `δ ≤ 1/1000`. -/
lemma delta_small {δ : ℝ} (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) : δ ≤ 1 / 1000 := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  refine hδ.trans ?_
  rw [Real.rpow_def_of_pos (by linarith)]
  have h := Real.add_one_le_exp (Real.log X₀ / 2)
  have hX := hc.hX
  rw [show Real.log X₀ * (-(1 / 2)) = -(Real.log X₀ / 2) by ring, Real.exp_neg,
    inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

set_option maxHeartbeats 2000000 in
/-- **The field `hoth`** (Steps 3–4): `log y · othS ≤ 10⁻²⁷` on range (B), from the `σ_𝒜`
bound and `RprimeChangeR`. -/
theorem hoth_R {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) (hRp : RprimeChangeR θ X₀ ω y δ) :
    Real.log y * othS θ X₀ ω y δ ≤ 1 / 10 ^ 27 := by
  have hX := hc.hX
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  have hδs := delta_small hc hev hδ
  set Λ := Real.log X₀ with hΛ
  have hly : Real.exp (Λ / 100) ≤ Real.log y := by
    rw [Real.rpow_def_of_pos hXp] at hyB
    have e : Λ * (1 / 100) = Λ / 100 := by ring
    rw [e] at hyB; exact hyB.le
  have hL31 := KR.RML6.logx_big (by linarith) hly
  have hly0 : 0 < Real.log y := by linarith
  haveI : Nonempty (Icc (y * (1 - 2 * δ)) (y * (1 - δ))) :=
    ⟨⟨y * (1 - δ), Set.mem_Icc.mpr ⟨by nlinarith, le_rfl⟩⟩⟩
  -- the two suprema
  set A := 2 / Real.log y ^ 2 + 3000 * Construction.kappa0Param X₀ with hA
  have hosc : Real.log y * oscS θ X₀ ω y δ ≤ A := by
    rw [mul_comm, ← le_div_iff₀ hly0]
    unfold oscS
    refine ciSup_le fun z => ?_
    rw [le_div_iff₀ hly0, mul_comm]
    exact hRp z.1 z.2
  have hsig : Real.log y * sigS θ X₀ ω y δ ≤ 1 / 10 ^ 30 := by
    rw [mul_comm, ← le_div_iff₀ hly0]
    unfold sigS
    refine ciSup_le fun z => ?_
    rw [le_div_iff₀ hly0, mul_comm]
    obtain ⟨z, hz1, hz2⟩ := z
    have hr0 : 1 / 2 ≤ z / y := by rw [le_div_iff₀ hy0]; nlinarith
    have hr1 : z / y ≤ 1 := by rw [div_le_one hy0]; nlinarith
    exact log_mul_abs_rhoSh_sigF_le hc hev hb hbt hQC hE1 hN hT hy hyb hr0 hr1
  -- the size of `A`
  have hA1 : 2 / Real.log y ^ 2 ≤ 1 / 10 ^ 60 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (10 : ℝ) ^ 62 ≤ Real.log y ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hL31 2; norm_num at this ⊢; linarith
    nlinarith
  have hA2 : 3000 * Construction.kappa0Param X₀ ≤ 1 / 10 ^ 30 := by
    unfold Construction.kappa0Param
    have hX2 : (X₀ : ℝ) = Real.exp Λ := by rw [hΛ, Real.exp_log hXp]
    have h8 := Real.pow_div_factorial_le_exp Λ (by linarith) 5
    norm_num [Nat.factorial] at h8
    rw [← hX2] at h8
    have hΛ8 : (10 : ℝ) ^ 8 ≤ Λ := hX
    have h40 : ((10 : ℝ) ^ 8) ^ 5 ≤ Λ ^ 5 := pow_le_pow_left₀ (by norm_num) hΛ8 5
    rw [mul_one_div, div_le_div_iff₀ hXp (by norm_num)]
    nlinarith
  unfold othS
  have : Real.log y * (oscS θ X₀ ω y δ + sigS θ X₀ ω y δ) =
      Real.log y * oscS θ X₀ ω y δ + Real.log y * sigS θ X₀ ω y δ := by ring
  rw [this]
  have : A ≤ 1 / 10 ^ 60 + 1 / 10 ^ 30 := by rw [hA]; linarith
  have : (1 : ℝ) / 10 ^ 60 + 1 / 10 ^ 30 + 1 / 10 ^ 30 ≤ 1 / 10 ^ 27 := by norm_num
  linarith

/-- **The Step 3–4 fields of `G1BInputs`** for the realised system (Proposition 5.35(B)), on
`Good(< t)` with (H_BS) on `[1, Zc b]` (through `hT`), at a start `X₀ ≤ y ≤ b + H(b)` of range
(B), for a window parameter `0 < δ ≤ X₀^{-1/2}`, from the named inputs `JumpCountR` and
`RprimeChangeR`. -/
noncomputable def step3_R {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) (hJ : JumpCountR θ X₀ ω y δ)
    (hRp : RprimeChangeR θ X₀ ω y δ) :
    Step3Out (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
      (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) y δ where
  thrS := thrS θ X₀ ω y δ
  j0 := jzX X₀
  jS := jS θ X₀ ω y δ
  detS := detS θ X₀ ω y δ
  othS := othS θ X₀ ω y δ
  hdec34 := by
    have hZ := Zc_facts hc hb
    have hXm0 := Xm_pos' hc
    have hδs := delta_small hc hev hδ
    refine hdec34_R hc hev ω hT hy ?_ hδ0 (by linarith)
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]
    have : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
    linarith
  N := y / X₀
  HN := Queue6.Hc X₀ (y / X₀)
  θ := θ
  hj0 := jzX_nonneg hc
  hj1 := jzX_le_one (θ := θ) hc
  hjS := by
    have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
    exact hjS_R hc hev ω (by linarith) hyB hδ0 (delta_small hc hev hδ) hJ
  hN := by
    have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
    exact (hN_R hc (by linarith) hyB).1
  hHN0 := by
    have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
    exact (hHN_R hc (by linarith) hyB).1
  hHN := by
    have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
    exact (hHN_R hc (by linarith) hyB).2
  hθ0 := by linarith [hc.hθ.1]
  hθ := by linarith [hc.hθ.2]
  CS := 77
  hCS0 := by norm_num
  hCS := le_rfl
  hdet := by
    have hZ := Zc_facts hc hb
    have hXm0 := Xm_pos' hc
    refine hdet_R hc hev ω hT hy ?_ hδ0 hδ
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  hoth := hoth_R hc hev hb hbt hQC hE1 hN hT hy hyb hyB hδ0 hδ hRp

/-- `thrS` of `step3_R` is the threshold mass of Lemma 5.23 at `2δ` (for the field `hthr`). -/
theorem thrS_eq {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) (hJ : JumpCountR θ X₀ ω y δ)
    (hRp : RprimeChangeR θ X₀ ω y δ) :
    (step3_R hc hev hb hbt hQC hE1 hN hT hy hyb hyB hδ0 hδ hJ hRp).thrS =
      (PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * δ) := rfl

end

end BModel

end
