module

public import RequestProject.Beurling.Model.G1BSec5

/-!
# The window records `KR.RML10.WinAt` at the window heights (the field `W` of `RestResH`)

* `hT_at` : Theorem 5.24 at any height `X₀ ≤ ž ≤ b + H(b)` whose queue slots are decided before
  `t` (`u + 26 log u + 2 < t` for `u ≤ ž`), on `QC(< t) ∩ {E1 < t} ∩ NiceEv` (as `hT_c`);
* `winAt_c` : `WinAt` at `s ∈ [X₀^{1.01}, b]` from the bridge record `bridge_c` at the start `s`
  (scales, `s⁰`, (osc), `TermOsc`), `hosc_c`, `hbdd_c`, Proposition 5.18(iii)
  (`etaX0SumLoc_of`), and `hT_at` at `2(s/X₀)^{0.55}`; Lemma 5.29 (`ShortRecip`, Queue6) is
  the input `hSR`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed AbsorbEmpty Queue6 KR
  KR.TNP KR.Chain KR.TcLoc

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **Theorem 5.24 at a height `ž`** below the certified horizon (`hT_c`'s argument at a
general height). -/
theorem hT_at {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {zc : ℝ} (hzcX : (X₀ : ℝ) ≤ zc) (hzcb : zc ≤ b + Queue6.Hc X₀ b)
    (hut : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → u + 26 * Real.log u + 2 < t) :
    LocalPNT.Theorem524Concl (PR θ X₀ ω) X₀ zc := by
  classical
  have hNice := hN
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  -- the realised model
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := h0.limModel_low
  have hPR : PR θ X₀ ω = realisedSystem M (capH X₀) ω := by
    show realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω) = _
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hDF : DF θ X₀ ω = DM M ω := by
    unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hAeq : realisedA M (capH X₀) ω = absSet X₀ (DF θ X₀ ω) := by
    rw [realisedA_eq hok hnc, hDF]
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  -- the floor
  have hfl : ∀ u, u < Xm X₀ → (PR θ X₀ ω).N u = ⌊u⌋₊ := by
    intro u hu
    rcases lt_or_ge u 1 with h1 | h1
    · rw [(PR θ X₀ ω).N_eq_zero h1, Nat.floor_eq_zero.mpr h1]; simp
    · rw [hPR]
      exact realised_floor_eq hok hU hX hTlow h1 (by unfold Xm at hu; exact hu)
  have hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 40 : ℝ) ≤ Xm X₀ := by
    unfold Xm
    have h1 := InitialRange.capH_le_rpow40 hX0 hX (le_refl (X₀ : ℝ))
    have h3 : 0 ≤ capH X₀ X₀ := by linarith [capH_ge_one hX0 hX (le_refl (X₀ : ℝ))]
    linarith
  -- the lag
  have hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |(PR θ X₀ ω).N u - targetD θ X₀ (DF θ X₀ ω) u| ≤ u ^ lagExponent θ := by
    intro u hu huz
    have hQ := queue_of_QE hc hQC h0 hu (hut u hu huz)
    have hl := lag_local M hc.hθ.1 hc.hθ.2 hX (realisedSystem M (capH X₀) ω).N Real.log
      (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
      (fun x hx _ => landing_of_linked L S hreg hok hx)
      (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hu hQ
    rw [h0.limModel_T_eq u, ← hDF, ← hPR] at hl
    exact hl
  -- Lemma 3.4 for the capped absorbed density
  have hAu := realisedU_spec hok hU hX hTlow (θ := θ) (by linarith [hc.hθ.1])
    (by linarith [hc.hθ.2])
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C : AbsorbedCoupling (realisedSystem M (capH X₀) ω) R.M R.H R.U
      (realisedA M (capH X₀) ω) (realisedLatest M (capH X₀) ω) := realisedCoupling hok
  have hb2 : 0 < thetaB θ := thetaB_pos (by linarith [hc.hθ.1])
  have hW : AbsorbedWindowHyp (thetaB θ) X₀ (absSet X₀ (DF θ X₀ ω)) (uA θ) := by
    rw [← hAeq]
    exact ⟨hb2, thetaB_le_one (by linarith [hc.hθ.2]), hX1.le, fun a ha => (hAu a ha).1,
      fun a ha => (hAu a ha).2, C.locFin⟩
  have hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |countA (absSet X₀ (DF θ X₀ ω)) u - ∫ v in (X₀ : ℝ)..u,
        absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v| ≤ 2 * u ^ (thetaB θ) := by
    intro u hu huz
    refine absorbed_target_error_cap_loc hW (by linarith) hu fun v hv hvu => ?_
    refine rhoA_le_L4 hc hev hb hbt hQC hE1 hNice hv ?_
    have : 0 ≤ Queue6.Hc X₀ b := (KR.WidthReal.Hc_pos hX b).le
    linarith [hvu.trans huz, hzcb]
  exact theorem_5_24_data (DF θ X₀ ω) hc.hθ hX hev hc.hHB
    (countA (absSet X₀ (DF θ X₀ ω)))
    (absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ)) hXm (Xm_le_X0 hc) hfl hlag hA
    hzcX le_rfl

set_option maxHeartbeats 2000000 in
/-- **The window record `WinAt` at a height `s ∈ [X₀^{1.01}, b]`** on `Good(< t)`, `b ≤ t`, with
Theorem 5.24 at `h = 2(s/X₀)^{0.55}` (`X₀ ≤ h ≤ s/2`) and Lemma 5.29 (`hSR`, Queue6). -/
noncomputable def winAt_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {s : ℝ} (hs : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ s) (hsb : s ≤ b)
    (hh1 : (X₀ : ℝ) ≤ 2 * (s / X₀) ^ (0.55 : ℝ)) (hh2 : 2 * (s / X₀) ^ (0.55 : ℝ) ≤ s / 2)
    (hSR : KR.RML9.ShortRecipLow (PR θ X₀ ω) X₀ s) :
    KR.RML10.WinAt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (TcR θ X₀ ω (jzX X₀)) s :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n :=
    fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have hH := KR.WidthReal.Hc_pos hX (X₀ := X₀) s
  have hW : InW (Queue6.Hc X₀ s) s s := ⟨by linarith, by linarith⟩
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  have x0s := Queue6.x0sHyp_G0 (e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  let R := bridge_c hc hev hb hbs hN.2.1 hX1 hs hsb hW
    (hosc_c hc hev hb hbt hG.1 hE1 hN hT hs hsb hW) (hbdd_c hc hev hb hT s hs hsb)
  { N := R.N
    K := R.K
    hN2 := R.hN2
    hN := R.hN
    hK := R.hK
    s0 := KR.X0S.sX0 (X₀ : ℝ)
    o := R.o
    etaX0 := x0s.etaX0SumLoc_of dyScales_dyadic (by linarith)
    etaX0Sum := R.etaX0Sum
    osc := R.osc
    hosc := hosc_c hc hev hb hbt hG.1 hE1 hN hT hs hsb hW
    termOsc := R.termOsc
    hT := hT_at hc hev hb hbt hG.1 hE1 hN hh1 (by linarith) fun u hu huh => by
      have hs0 : 0 < s := by linarith [one_lt_X0 hc]
      have hl : Real.log u ≤ Real.log s := Real.log_le_log (by linarith [one_lt_X0 hc])
        (by linarith)
      have hls : 26 * Real.log s + 2 < s / 2 := by
        have h1 := Real.add_one_le_exp (Real.log s / 2)
        have h2 : Real.exp (Real.log s / 2) ^ 2 = s := by
          rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ (by norm_num),
            Real.exp_log hs0]
        have hL : 10 ^ 8 ≤ Real.log s := by
          have := Real.log_le_log (by linarith [one_lt_X0 hc]) ((RML10.X0_le_X1 hX).trans hs)
          linarith
        nlinarith
      have : (t : ℝ) ≥ s := by linarith
      linarith
    hSR := hSR }

set_option maxHeartbeats 1000000 in
/-- **The window heights** `s ∈ [y/4, Ytop]` of a range-(B) start `y ≤ b + H(b)`:
`X₀^{1.01} ≤ s ≤ b`, `X₀ ≤ 2(s/X₀)^{0.55} ≤ s/2`. -/
lemma win_range (ω : JitterΩ) {b y s : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hs1 : y / 4 ≤ s)
    (hs2 : s ≤ KR.RML9.Ytop X₀ y (deltaB θ X₀ ω y)) :
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ s ∧ s ≤ b ∧ (X₀ : ℝ) ≤ 2 * (s / X₀) ^ (0.55 : ℝ) ∧
      2 * (s / X₀) ^ (0.55 : ℝ) ≤ s / 2 := by
  have hX := hc.hX
  have hX1 := one_lt_X0 hc
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  set Λ := Real.log X₀ with hΛ
  set L := Real.log y with hL
  have hLe : Real.exp (Λ / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hXp] at hyL
    have : Λ * (1 / 100) = Λ / 100 := by ring
    rw [this] at hyL; exact hyL.le
  obtain ⟨-, h3⟩ := D_le hX hLe (c := 0) le_rfl zero_le_one
  have hs0 : 0 < s := by linarith
  have hls : L - 2 ≤ Real.log s := by
    have h1 : Real.log (y / 4) ≤ Real.log s := Real.log_le_log (by positivity) hs1
    rw [Real.log_div hy0.ne' (by norm_num)] at h1
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      linarith [Real.log_two_lt_d9]
    linarith
  have hsX : Real.log (s / X₀) = Real.log s - Λ := Real.log_div hs0.ne' hXp.ne'
  have hsX0 : 0 < s / X₀ := by positivity
  have hp : (s / X₀) ^ (0.55 : ℝ) = Real.exp (0.55 * (Real.log s - Λ)) := by
    rw [Real.rpow_def_of_pos hsX0, hsX]; ring_nf
  refine ⟨?_, KR.RML9.Ytop_le_b (by norm_num at hX ⊢; linarith) hy0 hyL (deltaB_pos hc ω hy)
    (deltaB_low hc ω hy) hyb |> fun h => hs2.trans h, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (by positivity) hs0, Real.log_rpow hXp]; linarith
  · rw [hp]
    have h2 : (2 : ℝ) ≥ 1 := by norm_num
    have : Real.exp Λ ≤ Real.exp (0.55 * (Real.log s - Λ)) := Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.exp_log hXp] at this
    linarith
  · rw [hp]
    have hs : s = Real.exp (Real.log s) := (Real.exp_log hs0).symm
    have h4 : 4 * Real.exp (0.55 * (Real.log s - Λ)) ≤ Real.exp (Real.log s) := by
      have e : Real.exp (Real.log s) = Real.exp (0.55 * (Real.log s - Λ)) *
          Real.exp (0.45 * Real.log s + 0.55 * Λ) := by rw [← Real.exp_add]; ring_nf
      rw [e]
      have h5 : (4 : ℝ) ≤ Real.exp (0.45 * Real.log s + 0.55 * Λ) := by
        have := Real.add_one_le_exp (0.45 * Real.log s + 0.55 * Λ); nlinarith
      have := Real.exp_pos (0.55 * (Real.log s - Λ))
      nlinarith
    linarith

/-- The window `J` of a range-(B) start lies in `[X₀^{1.01}, b]`. -/
lemma J_range (ω : JitterΩ) {b y : ℝ} (hb : (X₀ : ℝ) ≤ b) (hy : (X₀ : ℝ) ≤ y)
    (hyb : y ≤ b + Queue6.Hc X₀ b) (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) {z : ℝ}
    (hz : z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y)) : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ z ∧ z ≤ b := by
  have hX := hc.hX
  have hR := KR.RML9.g1_range (by norm_num at hX ⊢; linarith) (y_pos_c hc hy) hyL
    (deltaB_le (θ := θ) ω y)
  obtain ⟨-, -, -, -, hδ4, -, -⟩ := hR
  have hδ0 := deltaB_pos hc ω hy
  have hz1 : y / 2 ≤ z := by nlinarith [hz.1]
  have h1 := X1_le_half hc hy hyL
  have hX1t := RML10.X0_le_X1 hX
  have hzX : (X₀ : ℝ) ≤ z := by linarith
  have h2 := horJ hc ω hb hy hyb hyL hzX hz.2
  have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) z).le
  exact ⟨by linarith, by linarith⟩

end BModel

end
