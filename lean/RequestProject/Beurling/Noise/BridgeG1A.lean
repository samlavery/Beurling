module

public import RequestProject.Beurling.Noise.BridgeG1Resp
public import RequestProject.Beurling.BaseRange.Margin

/-!
# Proposition 5.35 (positivity of the sharp reference), range (A)

Range (A) is `X₀ + H ≤ x ≤ X_sw`, `log X_sw = X₀^{1/100}`. There the source is
`T' = 1 - ρ_det + σ_𝒜`, and Lemma 7.3 (eq. (86)) decomposes the sharp reference as

  `ρ^sh(x) = MA[ℙ](x) + ρ_edge(x) + ((1 + K_pt)⁻¹ μ₀)(x) + ((1 + K_pt)⁻¹ μ₁)(x) + r_𝒜(x)`,

where `(1 + K_pt)⁻¹ g (x) = ∑_n c_n(x) g(x/n)/n` is the sharp resolvent (`KR.rhoSh`) and `r_𝒜` is
the response to the absorbed source `σ_𝒜`. The decomposition itself and the bound on `r_𝒜` are
inputs (`hdec`, `hA`): the first is the identity (86) of §7.2 for the realised system, the
second is the paper's "`σ_𝒜`: likewise, at most `e^{-80}`" (it involves only the absorbed set,
which is kept generic here). Everything else of the proof is proved:

* `MA[ℙ](x) log x ≥ 0.99` and the edge bounds: Lemma 7.3(a), (d)(ii), (d)(iii)
  (`BaseRange.lemma_7_3`, under (84) and the realised inputs `Lemma73Inputs`);
* the `μ₀` response: `log x |(1 + K_pt)⁻¹ μ₀ (x)| ≤ log x (log x + 1) 2κ (log x)³ ≤ X₀^{-0.34}`
  (Lemma M with `B₁ = 1`: `G1.abs_rhoSh_le_harm`, `HBS.harm_le`, and `BaseRange.use_mu0`);
* the `μ₁` response: `log x |(1 + K_pt)⁻¹ μ₁ (x)| ≤ C_S · 7·10⁻⁶ ≤ 6·10⁻⁴` (Corollary 5.9 on the
  dyadic blocks, `G1.log_mul_abs_rhoSh_le`, with (87), `BaseRange.mu1sum`);
* the final arithmetic (`BaseRange.use_rangeA_low`, `use_rangeA_high`).

`G1.prop_5_35_A` : `ρ^sh(x) log x ≥ 0.822` for `X₀ ≤ x ≤ X₀^{1.01}`, and `≥ 0.989` for
`X₀^{1.01}/2 ≤ x` with `log x ≤ X₀^{1/100}` (the paper's `0.82 - o(1)` and `0.97 - o(1)`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.G1

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- The sharp resolvent at `x` reads `g` only on `[0, x]`. -/
lemma rhoSh_congr {g g' : ℝ → ℝ} (hx : 0 ≤ x) (hgg : ∀ u, u ≤ x → g u = g' u) :
    rhoSh P tw X0m x g = rhoSh P tw X0m x g' := by
  rw [rhoSh_eq_elems, rhoSh_eq_elems]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hgg _ (div_le_self hx (P.one_le_val e))]

/-- The truncation of `μ₁` at the horizon (the function of `BaseRange.Lemma73c`). -/
noncomputable def trunc (xmax : ℝ) (μ : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ xmax then μ u else 0

/-- On a dyadic block, `|μ₁| ≤ sup_{block} |μ₁|` (the supremum exists by the first bound of
Lemma 7.3(c)). -/
lemma le_blockSup {X0 : ℝ} (hX0 : 1 < X0) {μ : ℝ → ℝ} (hμ : BaseRange.Mu1Pointwise X0 μ)
    (j : ℕ) {u : ℝ} (hu1 : 2 ^ j * X0 ≤ u) (hu2 : u ≤ 2 * (2 ^ j * X0)) :
    |μ u| ≤ BaseRange.blockSup X0 μ j := by
  have hX0p : 0 < X0 := by linarith
  have hlX : 0 < Real.log X0 := Real.log_pos hX0
  have hj1 : X0 ≤ 2 ^ j * X0 := le_mul_of_one_le_left hX0p.le (one_le_pow₀ (by norm_num))
  refine le_csSup ?_ (Set.mem_image_of_mem _ (show u ∈ Set.Icc (2 ^ j * X0) (2 * (2 ^ j * X0))
    from ⟨hu1, hu2⟩))
  refine ⟨2 / Real.log X0 ^ 3 *
    (Real.log (Real.log (2 * (2 ^ j * X0)) / Real.log X0) + 1.01), ?_⟩
  rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
  have hw0 : X0 ≤ w := hj1.trans hw1
  refine (hμ.1 w hw0).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hwpos : 0 < w := lt_of_lt_of_le hX0p hw0
  have hlw : Real.log X0 ≤ Real.log w := Real.log_le_log hX0p hw0
  have hl1 : 0 < Real.log w / Real.log X0 := div_pos (lt_of_lt_of_le hlX hlw) hlX
  have hl2 : Real.log w ≤ Real.log (2 * (2 ^ j * X0)) := Real.log_le_log hwpos hw2
  have : Real.log (Real.log w / Real.log X0) ≤
      Real.log (Real.log (2 * (2 ^ j * X0)) / Real.log X0) :=
    Real.log_le_log hl1 (div_le_div_of_nonneg_right hl2 hlX.le)
  linarith

/-- **Proposition 5.35, range (A).** -/
theorem prop_5_35_A {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
    (hHux : BaseRange.HuxleyFrom X0) {xmax : ℝ} {μ0 μ1 ρedge : ℝ → ℝ}
    (hin : BaseRange.Lemma73Inputs X0 xmax μ0 μ1 ρedge)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hX0m : X0m ≤ X0) (hx : (X0 : ℝ) ≤ x) (hxmax : x ≤ xmax) (hZ : 2 * x / X0m ≤ Z)
    (hxl : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ))
    (hμ0 : ∀ u : ℝ, u < X0 → μ0 u = 0) (hμ1 : ∀ u : ℝ, u < X0 → μ1 u = 0)
    {Tp : ℝ → ℝ} {rA : ℝ}
    (hdec : rhoSh P tw X0m x Tp = BaseRange.MAP X0 (Construction.kappaParam X0) x + ρedge x +
      rhoSh P tw X0m x μ0 + rhoSh P tw X0m x μ1 + rA)
    (hA : |rA * Real.log x| ≤ Real.exp (-80)) :
    (x ≤ (X0 : ℝ) ^ (1.01 : ℝ) → 0.822 ≤ rhoSh P tw X0m x Tp * Real.log x) ∧
    ((X0 : ℝ) ^ (1.01 : ℝ) / 2 ≤ x → 0.989 ≤ rhoSh P tw X0m x Tp * Real.log x) := by
  classical
  have hXmpos := h.X0m_pos
  have hX1 : (1 : ℝ) < X0 := BaseRange.one_lt_of_log hX
  have hX0p : (0 : ℝ) < X0 := by linarith
  have hxm : X0m ≤ x := hX0m.trans hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨ha, hb, hc, -, hd2, hd3⟩ := BaseRange.lemma_7_3 hX hHux hin
  have hma := (ha x hx).2
  -- the `μ₀` response
  have hr0 : |rhoSh P tw X0m x μ0 * Real.log x| ≤ (X0 : ℝ) ^ (-0.34 : ℝ) := by
    have hZ1 : x / X0m ≤ Z := by
      refine le_trans ?_ hZ
      rw [div_le_div_iff₀ hXmpos hXmpos]; nlinarith
    have hbnd := abs_rhoSh_le_harm (P := P) (tw := tw) h ht hXmpos hxm hZ1
      (g := μ0) (M := 2 * Construction.kappaParam X0 * Real.log x ^ 3) (by
        intro u hu1 hu2
        have hκ0 := (BModel.kappa_facts hX).1
        rcases lt_or_ge u X0 with hlt | hge
        · rw [hμ0 u hlt, abs_zero]; positivity
        · refine (hb u hge (hu2.trans hxmax)).trans ?_
          have hu0 : 0 < u := by linarith
          have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
          have : Real.log u ≤ Real.log x := Real.log_le_log hu0 hu2
          have := pow_le_pow_left₀ hlu this 3
          nlinarith)
    have hlxm : Real.log (x / X0m) ≤ Real.log x := by
      rw [Real.log_div hx0.ne' hXmpos.ne']
      have : 0 ≤ Real.log X0m := by linarith
      linarith
    have hκ0 := (BModel.kappa_facts hX).1
    have hM0 : 0 ≤ 2 * Construction.kappaParam X0 * Real.log x ^ 3 := by positivity
    have hu := BaseRange.use_mu0 hX hx hxl
    rw [abs_mul, abs_of_pos hL]
    calc |rhoSh P tw X0m x μ0| * Real.log x
        ≤ (Real.log (x / X0m) + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3) *
            Real.log x := mul_le_mul_of_nonneg_right hbnd hL.le
      _ ≤ (Real.log x + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3) *
            Real.log x := by gcongr
      _ = Real.log x * (Real.log x + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3) :=
            by ring
      _ ≤ _ := hu
  -- the `μ₁` response
  have hr1 : |rhoSh P tw X0m x μ1 * Real.log x| ≤ 6e-4 := by
    set μ1' := trunc xmax μ1
    have hcongr : rhoSh P tw X0m x μ1 = rhoSh P tw X0m x μ1' :=
      rhoSh_congr hx0.le fun u hu => by simp only [μ1', trunc, if_pos (hu.trans hxmax)]
    have hpw : BaseRange.Mu1Pointwise X0 μ1' := hin.c
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (x / X0) (by norm_num : (1 : ℝ) < 2)
    have hJ' : x < 2 ^ J * (X0 : ℝ) := by rwa [div_lt_iff₀ hX0p] at hJ
    have hsum := log_mul_abs_rhoSh_le (P := P) (tw := tw) h hXm ht htv
      (X0 := (X0 : ℝ)) hX0m hxm hZ (g := μ1')
      (fun u hu => by simp only [μ1', trunc]; split_ifs <;> simp [hμ1 u hu])
      (b := BaseRange.blockSup X0 μ1') (fun j => BaseRange.blockSup_nonneg j)
      (fun j u h1 h2 => le_blockSup hX1 hpw j h1 h2) hJ'
    obtain ⟨hsm, htsum, h7⟩ := BaseRange.mu1sum hpw hX0p hX
    have hpart : ∑ j ∈ (range J).filter (fun j => 2 ^ j * (X0 : ℝ) ≤ x),
        Real.log (2 * (2 ^ j * (X0 : ℝ))) * BaseRange.blockSup X0 μ1' j ≤
        690 / Real.log X0 := by
      refine le_trans ?_ htsum
      refine Summable.sum_le_tsum _ (fun j _ => ?_) hsm
      apply mul_nonneg _ (BaseRange.blockSup_nonneg j)
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hCS := BeurlingSystem.CS_le
    have hCS0 : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_trans (by norm_num) (le_max_right _ _)
    rw [hcongr, abs_mul, abs_of_pos hL, mul_comm]
    calc Real.log x * |rhoSh P tw X0m x μ1'|
        ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (690 / Real.log X0) :=
          hsum.trans (mul_le_mul_of_nonneg_left hpart hCS0)
      _ ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * 7e-6 :=
          mul_le_mul_of_nonneg_left h7 hCS0
      _ ≤ 6e-4 := (BaseRange.use_saias hCS).1
  rw [hdec]
  constructor
  · intro hx2
    exact BaseRange.use_rangeA_low hX hma (hd2 x hx hx2) hr0 hr1 hA
  · intro hx2
    have hre : |ρedge x * Real.log x| ≤
        3 * (X0 : ℝ) ^ (-0.01 : ℝ) + (X0 : ℝ) ^ (-0.34 : ℝ) := by
      rw [abs_mul, abs_of_pos hL]; exact hd3 x hx2 hxl hxmax
    exact BaseRange.use_rangeA_high hX hma hre hr0 hr1 hA

end KR.G1

end
