module

public import RequestProject.Beurling.Model.G1BDelta
public import RequestProject.Beurling.Model.G1BJump

/-!
# The jump count `JumpCountR` (Proposition 5.35(B), Step 3, "The jump of `T'` at `X₀`")

04f-bridge.tex, proof of Proposition 5.35, range (B), Step 3, second bullet: with `N_* = y/X₀`
and `I = (N_*(1-2δ), N_*]`,

  `#(𝒩 ∩ I) ≤ 4.01 δ N_* + 2H(N_*) + 2 + N_*^{θ/2}`.

Proof here: the lag bound (Corollary 3.8) at both ends of `I` (`lag_absA`, the queue-lag input
of `hT_c`), the target count `T(I) ≤ (Ψ(N_*) - Ψ(a)) + |I| + R(N_*) - R(a) + (#𝒜 - ∫ρ̄_𝒜)|_a^{N_*}`
(`ρ_det ≥ 0`), with `Ψ(I) ≤ |I| + 1`, `|R'| ≤ 0.02/log` (Lemma 3.3) and Lemma 3.4 for the absorbed
part (`|#𝒜 - ∫ρ̄_𝒜| ≤ 2u^{θ/2}`, in place of the window covering by Lemma 6.26). All error terms
`O(N_*^{θ/2})` are absorbed by `0.009 δ N_*`, as `1/δ ≤ e^{c_LP √(log y)/2} log⁴ y + X₀^{1/2}`
is `≤ 2 y^{1/4}` (`jumpCount_c`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed AbsorbEmpty Queue6
  SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section Lag

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **The lag bound and Lemma 3.4 below `y(1-δ)`** on `Good(< t)` (the inputs of `hT_c`):
Corollary 3.8 at each height `u ≤ y(1-δ)` and Lemma 3.4 for the capped absorbed density. -/
theorem lag_absA {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    (∀ u, (X₀ : ℝ) ≤ u → u ≤ y * (1 - deltaB θ X₀ ω y) →
      |(PR θ X₀ ω).N u - targetD θ X₀ (DF θ X₀ ω) u| ≤ u ^ lagExponent θ) ∧
    (∀ u, (X₀ : ℝ) ≤ u → u ≤ y * (1 - deltaB θ X₀ ω y) →
      |countA (absSet X₀ (DF θ X₀ ω)) u - ∫ v in (X₀ : ℝ)..u,
        absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v| ≤ 2 * u ^ (thetaB θ)) := by
  classical
  have hNice := hN
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hy0 : 0 < y := by linarith
  set δ := deltaB θ X₀ ω y with hδdef
  set zc := y * (1 - δ) with hzc
  have hδ0 := deltaB_pos hc ω hy
  have hgap := deltaB_gap hc ω hy hyL
  -- `y - y^{1/8} ≤ t`
  have hyt : y - y ^ (1 / 8 : ℝ) ≤ t := by
    have h8 : 0 ≤ y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hy0.le _
    rcases le_total y b with h | h
    · linarith
    · have hH : Queue6.Hc X₀ b ≤ y ^ (1 / 8 : ℝ) := by
        unfold Queue6.Hc; rw [max_eq_left hb]
        exact (InitialRange.capH_le_rpow hX0 hX hb).trans
          (Real.rpow_le_rpow (by linarith) h (by norm_num))
      linarith
  have hzcy : zc ≤ y := by
    have : 0 ≤ y * δ := by positivity
    simp only [hzc]; nlinarith
  have hzcX : (X₀ : ℝ) ≤ zc := by
    have hL0 : 0 < Real.log y := logy_pos hc hy
    have h8 : 0 ≤ y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hy0.le _
    -- `y^{1/8} ≤ y/2` and `y ≥ 2X₀` give `zc ≥ X₀`
    have hδ1 : δ ≤ 1 / 2 := by
      refine (deltaB_le ω y).trans ?_
      rw [Real.rpow_neg hX0, ← one_div]
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)]
      have : (2 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) hX0]
        linarith [X₀_ge_two_pow hX]
      linarith
    have hy2 : 2 * (X₀ : ℝ) ≤ y := by
      have hLe : Real.exp (Real.log X₀ / 100) ≤ Real.log y := by
        rw [Real.rpow_def_of_pos (by linarith)] at hyL
        have : Real.log X₀ * (1 / 100) = Real.log X₀ / 100 := by ring
        rw [this] at hyL; exact hyL.le
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log X₀ / 100 by positivity)
      have hl : Real.log X₀ + 1 ≤ Real.log y := by nlinarith
      have := Real.add_one_le_exp (Real.log X₀ + 1)
      have e : Real.exp (Real.log X₀ + 1) = X₀ * Real.exp 1 := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have : (X₀ : ℝ) * Real.exp 1 ≤ y := by
        rw [← e, ← Real.exp_log hy0]; exact Real.exp_le_exp.mpr hl
      nlinarith
    simp only [hzc]; nlinarith
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
  -- the queue bound below `ž`
  have hut : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → u + 26 * Real.log u + 2 < t := by
    intro u hu huz
    have : Real.log u ≤ Real.log y := Real.log_le_log (by linarith) (huz.trans hzcy)
    linarith
  -- the floor
  have hfl : ∀ u, u < Xm X₀ → (PR θ X₀ ω).N u = ⌊u⌋₊ := by
    intro u hu
    rcases lt_or_ge u 1 with h1 | h1
    · rw [(PR θ X₀ ω).N_eq_zero h1, Nat.floor_eq_zero.mpr h1]; simp
    · rw [hPR]
      exact realised_floor_eq hok hU hX hTlow h1 (by unfold Xm at hu; exact hu)
  have hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ Xm X₀ := by
    unfold Xm
    have h1 := InitialRange.capH_le_rpow hX0 hX (le_refl (X₀ : ℝ))
    have h2 : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
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
    linarith
  exact ⟨hlag, hA⟩

end Lag

/-! ### Counting -/

open Classical in
/-- `#{e : a < e ≤ N} = N(N) - N(a)`. -/
lemma card_filter_gt (P : BeurlingSystem) {a N : ℝ} (haN : a ≤ N) :
    (((P.elems N).filter (fun e => a < P.val e)).card : ℝ) = P.N N - P.N a := by
  rw [P.N_eq_card, P.N_eq_card]
  have hc := Finset.card_filter_add_card_filter_not (s := P.elems N)
    (fun e => a < P.val e)
  have he : (P.elems N).filter (fun e => ¬ a < P.val e) = P.elems a := by
    ext e
    simp only [Finset.mem_filter, BeurlingSystem.mem_elems, not_lt]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans haN, h⟩
  rw [he] at hc
  have : (((P.elems N).filter (fun e => a < P.val e)).card : ℝ) + (P.elems a).card =
      (P.elems N).card := by exact_mod_cast hc
  linarith

/-- `Ψ(N) - Ψ(a) ≤ N - a + 1` for `0 ≤ a ≤ N` (unit spacing of the integers). -/
lemma smoothCount_sub_le (X₀ : ℕ) {a N : ℝ} (ha : 0 ≤ a) (haN : a ≤ N) :
    (Rankin.smoothCount X₀ N : ℝ) - Rankin.smoothCount X₀ a ≤ N - a + 1 := by
  unfold Rankin.smoothCount
  have hfl : ⌊a⌋₊ ≤ ⌊N⌋₊ := Nat.floor_mono haN
  have hsub : Nat.smoothNumbersUpTo ⌊N⌋₊ X₀ ⊆
      Nat.smoothNumbersUpTo ⌊a⌋₊ X₀ ∪ Finset.Ioc ⌊a⌋₊ ⌊N⌋₊ := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    rw [Finset.mem_union, Nat.mem_smoothNumbersUpTo, Finset.mem_Ioc]
    rcases le_or_gt n ⌊a⌋₊ with h | h
    · exact Or.inl ⟨h, hn.2⟩
    · exact Or.inr ⟨h, hn.1⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Ioc] at hc
  have hc' : ((Nat.smoothNumbersUpTo ⌊N⌋₊ X₀).card : ℝ) ≤
      (Nat.smoothNumbersUpTo ⌊a⌋₊ X₀).card + ((⌊N⌋₊ : ℝ) - ⌊a⌋₊) := by
    rw [← Nat.cast_sub hfl]; exact_mod_cast hc
  have h1 := Nat.floor_le (ha.trans haN)
  have h2 := Nat.lt_floor_add_one a
  linarith

/-- `|R(N) - R(a)| ≤ 10⁻⁹ (N - a)` on `[X₀, ∞)` (Lemma 3.3: `|R'| ≤ 0.02/log`). -/
lemma osc_sub_le (hc : Cond θ X₀) (D : PrimeData) {a N : ℝ} (ha : (X₀ : ℝ) ≤ a)
    (haN : a ≤ N) :
    |Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) N -
      Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) a| ≤
        (N - a) / 10 ^ 9 := by
  have hX := hc.hX
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  have hd : ∀ x ∈ Set.Icc a N,
      DifferentiableAt ℝ
        (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) x :=
    fun x hx => (hasDerivAt_osc _ _ hX1.le (by linarith [hx.1])).differentiableAt
  have hb : ∀ x ∈ Set.Icc a N,
      ‖deriv (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) x‖ ≤
        1 / 10 ^ 9 := by
    intro x hx
    have hxX : (X₀ : ℝ) ≤ x := ha.trans hx.1
    have h := abs_deriv_osc_le hc.hθ hX (gammaD_range (θ := θ) hX D) hxX
    have hl : 10 ^ 8 ≤ Real.log x := hX.trans (Real.log_le_log (by linarith) hxX)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have := (convex_Icc a N).norm_image_sub_le_of_norm_deriv_le hd hb
    (Set.left_mem_Icc.mpr haN) (Set.right_mem_Icc.mpr haN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ N - a by linarith)]
    at this
  linarith

/-- `D = e^{c√L/2} L⁴ + e^{Λ/2} ≤ 2 e^{L/4}` for `L ≥ e^{Λ/100}`, `Λ ≥ 10⁸`, `c ≤ 1`. -/
lemma D_le {Λ L c : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : Real.exp (Λ / 100) ≤ L) (_hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) :
    Real.exp (c * √L / 2) * L ^ 4 + Real.exp (Λ / 2) ≤ 2 * Real.exp (L / 4) ∧ 3 * Λ ≤ L := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Λ / 100 by positivity)
  have hL3 : 3 * Λ ≤ L := by nlinarith
  have hL8 : (3 * 10 ^ 8 : ℝ) ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hp := Real.pow_div_factorial_le_exp (L / 8) (by positivity) 8
  have e8 : ((8 : ℕ).factorial : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [e8, div_pow] at hp
  have hL4 : L ^ 4 ≤ Real.exp (L / 8) := by
    have hL4b : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hL8 4; nlinarith
    have : L ^ 8 = L ^ 4 * L ^ 4 := by ring
    have h8 : (8 : ℝ) ^ 8 * 40320 ≤ 10 ^ 32 := by norm_num
    have hp' : L ^ 8 / 8 ^ 8 / 40320 = L ^ 8 / (8 ^ 8 * 40320) := by ring
    rw [hp', div_le_iff₀ (by norm_num)] at hp
    nlinarith
  have hs : c * √L / 2 ≤ L / 8 := by
    have hsq := Real.sq_sqrt hL0.le
    have hs0 := Real.sqrt_nonneg L
    have hs4 : 4 ≤ √L := by
      rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
    have : c * √L ≤ √L := by nlinarith
    nlinarith
  have hE1 : Real.exp (c * √L / 2) * L ^ 4 ≤ Real.exp (L / 4) := by
    have : Real.exp (L / 4) = Real.exp (L / 8) * Real.exp (L / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact mul_le_mul (Real.exp_le_exp.mpr hs) hL4 (by positivity) (Real.exp_pos _).le
  have hE2 : Real.exp (Λ / 2) ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
  exact ⟨by linarith, hL3⟩

/-! ### The jump count -/

section Jump

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **`JumpCountR` at `δ = deltaB`** (04f-bridge.tex, Proposition 5.35(B), Step 3, "The jump of
`T'` at `X₀`") on `QC(< t) ∩ {E1 of time < t} ∩ NiceEv`, at every start `X₀ ≤ y ≤ b + H(b)` with
`log y > X₀^{1/100}`, `b ≤ t`: `#(𝒩 ∩ (N_*(1-2δ), N_*]) ≤ 4.01 δ N_* + 2H(N_*) + 2 + N_*^{θ/2}`,
`N_* = y/X₀`. -/
theorem jumpCount_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    JumpCountR θ X₀ ω y (deltaB θ X₀ ω y) := by
  obtain ⟨hlag, hA⟩ := lag_absA hc hev hb hbt hQC hE1 hN hy hyb hyL
  unfold JumpCountR
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hδ0 := deltaB_pos hc ω hy
  have hlow := deltaB_low hc ω hy
  set δ := deltaB θ X₀ ω y with hδdef
  have hδs : δ ≤ 1 / 1000 := by
    refine (deltaB_le ω y).trans ?_
    rw [Real.rpow_def_of_pos hXp]
    have h := Real.add_one_le_exp (Real.log X₀ / 2)
    rw [show Real.log X₀ * (-(1 / 2)) = -(Real.log X₀ / 2) by ring, Real.exp_neg,
      inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  set Λ := Real.log X₀ with hΛ
  set L := Real.log y with hL
  have hLe : Real.exp (Λ / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hXp] at hyL
    have : Λ * (1 / 100) = Λ / 100 := by ring
    rw [this] at hyL; exact hyL.le
  have hcl := cLP_mem (Λ := Λ) (by linarith)
  obtain ⟨hD, hL3⟩ := D_le hX hLe hcl.1 hcl.2
  have hX2 : (X₀ : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Λ / 2) := by
    rw [Real.rpow_def_of_pos hXp]; congr 1; ring
  rw [hX2] at hlow
  have hδE : 1 / δ ≤ 2 * Real.exp (L / 4) := hlow.trans hD
  set Nn := y / (X₀ : ℝ) with hNn
  have hNe : Nn = Real.exp (L - Λ) := by
    rw [hNn, Real.exp_sub, Real.exp_log hy0, Real.exp_log hXp]
  have hXe : (X₀ : ℝ) = Real.exp Λ := (Real.exp_log hXp).symm
  have hN2 : 2 * (X₀ : ℝ) ≤ Nn := by
    rw [hNe]
    have h1 : Real.exp (2 * Λ) ≤ Real.exp (L - Λ) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (2 * Λ) = (X₀ : ℝ) * X₀ := by
      rw [hXe, ← Real.exp_add]; ring_nf
    nlinarith
  set a := Nn * (1 - 2 * δ) with ha
  have haN : a ≤ Nn := by
    have : 0 ≤ Nn * δ := by positivity
    simp only [ha]; nlinarith
  have haX : (X₀ : ℝ) ≤ a := by simp only [ha]; nlinarith
  have hNz : Nn ≤ y * (1 - δ) := by
    have h1 : Nn * 2 ≤ y := by
      rw [hNn, div_mul_eq_mul_div, div_le_iff₀ hXp]; nlinarith
    nlinarith
  have hNX : (X₀ : ℝ) ≤ Nn := haX.trans haN
  rw [card_filter_gt _ haN]
  -- the lag at both ends
  have hl1 := abs_le.mp (hlag Nn hNX hNz)
  have hl2 := abs_le.mp (hlag a haX (haN.trans hNz))
  have hA1 := abs_le.mp (hA Nn hNX hNz)
  have hA2 := abs_le.mp (hA a haX (haN.trans hNz))
  -- the target increment
  set D := DF θ X₀ ω
  have hT : targetD θ X₀ D Nn - targetD θ X₀ D a =
      ((Rankin.smoothCount X₀ Nn : ℝ) - Rankin.smoothCount X₀ a) +
      (countA (absSet X₀ D) Nn - ∫ v in (X₀ : ℝ)..Nn,
        absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) v) -
      (countA (absSet X₀ D) a - ∫ v in (X₀ : ℝ)..a,
        absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) v) + (Nn - a) -
      ((∫ u in (X₀ : ℝ)..Nn, Target.rhoDet X₀ (kappaParam X₀) u) -
        ∫ u in (X₀ : ℝ)..a, Target.rhoDet X₀ (kappaParam X₀) u) +
      (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) Nn -
        Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) a) := by
    unfold targetD Target.target
    rw [if_neg (not_lt.mpr hNX), if_neg (not_lt.mpr haX)]
    ring
  have hκ := (kappa_facts hX).1
  have hdet : 0 ≤ (∫ u in (X₀ : ℝ)..Nn, Target.rhoDet X₀ (kappaParam X₀) u) -
      ∫ u in (X₀ : ℝ)..a, Target.rhoDet X₀ (kappaParam X₀) u := by
    have hX01 : 1 ≤ X₀ := by exact_mod_cast hX1.le
    rw [intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_rhoDet X₀ hκ hX01 hNX) (intervalIntegrable_rhoDet X₀ hκ hX01 haX)]
    exact intervalIntegral.integral_nonneg haN fun u hu =>
      rhoDet_nonneg X₀ hκ (by linarith [hu.1])
  have hΨ := smoothCount_sub_le X₀ (by linarith) haN
  have hR := abs_le.mp (osc_sub_le hc D haX haN)
  -- the powers
  have hN1 : (1 : ℝ) ≤ Nn := by linarith
  have hθ2 : thetaB θ ≤ 1 / 4 := thetaB_le_quarter (by linarith [hc.hθ.2])
  have hlagθ : lagExponent θ ≤ thetaB θ := by
    unfold lagExponent
    have := min_le_left θ (1 / 2 - θ)
    have := half_le_thetaB (show 0 ≤ θ by linarith [hc.hθ.1]); linarith
  have hθ0 : 0 ≤ thetaB θ := (thetaB_pos (by linarith [hc.hθ.1])).le
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have p1 : a ^ (thetaB θ) ≤ Nn ^ (thetaB θ) := Real.rpow_le_rpow (by linarith) haN hθ0
  have p2 : Nn ^ lagExponent θ ≤ Nn ^ (thetaB θ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hlagθ
  have p3 : a ^ lagExponent θ ≤ Nn ^ (thetaB θ) :=
    (Real.rpow_le_rpow_of_exponent_le ha1 hlagθ).trans p1
  have p4 : Nn ^ (thetaB θ) ≤ Nn ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hθ2
  -- the numerics: `5 N^{1/4} ≤ 0.009 δ N`
  have hnum : 5 * Nn ^ (1 / 4 : ℝ) ≤ 0.009 * (δ * Nn) := by
    have hq : Nn ^ (1 / 4 : ℝ) = Real.exp ((L - Λ) / 4) := by
      rw [hNe, ← Real.exp_mul]; congr 1; ring
    have hsplit : Real.exp (L - Λ) =
        Real.exp ((L - Λ) / 4) * Real.exp (L / 2 - 3 * Λ / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hbig : (2000 : ℝ) ≤ Real.exp (L / 2 - 3 * Λ / 4) := by
      have := Real.add_one_le_exp (L / 2 - 3 * Λ / 4); linarith
    have hE := Real.exp_pos (L / 4)
    have hδN : Real.exp (L - Λ) / (2 * Real.exp (L / 4)) ≤ δ * Nn := by
      rw [hNe, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hδ0] at hδE
      have := Real.exp_pos (L - Λ)
      nlinarith
    rw [hq]
    rw [hsplit] at hδN
    have e : Real.exp ((L - Λ) / 4) * Real.exp (L / 2 - 3 * Λ / 4) * Real.exp (L / 4) /
        (2 * Real.exp (L / 4)) = Real.exp ((L - Λ) / 4) * Real.exp (L / 2 - 3 * Λ / 4) / 2 := by
      field_simp
    rw [e] at hδN
    have := Real.exp_pos ((L - Λ) / 4)
    nlinarith
  have hH := (KR.WidthReal.Hc_pos hX (X₀ := X₀) Nn).le
  have hNa : Nn - a = 2 * (δ * Nn) := by simp only [ha]; ring
  have hdiv : (Nn - a) / 10 ^ 9 = 2 * (δ * Nn) / 10 ^ 9 := by rw [hNa]
  have hδN0 : 0 ≤ δ * Nn := by positivity
  nlinarith

end Jump

end BModel

end
