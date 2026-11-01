module

public import RequestProject.Beurling.Model.G1BDec34
public import RequestProject.Beurling.Model.RhoDetOsc
public import RequestProject.Beurling.BaseRange.EulerQ
public import RequestProject.BSCert.Consts.MarginCert

/-!
# The `ρ_det` smooth change in Step 3 of Proposition 5.35(B): the field `hdet`

04f-bridge.tex, proof of Proposition 5.35, range (B), Step 3, third bullet. For `v ≥ X₀`,
`v' = max(rv, X₀)`, `r ∈ [1-2δ, 1]`:

* `abs_detF_le` : `|ρ_det(v) - ρ_det(v')| ≤ min((10δ + 3/X₀)/(κ(1-2δ)), 3Ψ(2v, X₀)/(κv))` (the
  linear window of length `κv` and the unit spacing of the rigid set, `rhoDet_kappa_sub_le`;
  and `ρ_det(w) ≤ Ψ(2v, X₀)/(κw)` for `w ≤ v`);
* `psi_rankin` : Rankin's bound with exponent `1 - 1/(2Λ)`,
  `Ψ(Y, X₀) ≤ 2Λ e⁴ Y e^{-log Y/(2Λ)}` (`Rankin.smoothCount_le_rankin`, the Euler product
  `BaseRange.rankinConst_le`, `Ein(2) < 3.69`);
* `hdet_R` : **the field `hdet`**, with `C_S = 77`: Corollary 5.9 in the dyadic form
  (`KR.G1.log_mul_abs_rhoSh_le`), the first bound on the blocks below `2^{j₁} X₀`,
  `j₁ = ⌈4Λ²⌉`, and the second beyond, give
  `log y · detS ≤ 77 (7Λ⁴ X₀^{-1/12} + 90 Λ^{4.7} e^{-Λ/12})`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### Rankin's bound -/

/-- **Rankin's bound** with exponent `1 - 1/(2Λ)`: `Ψ(Y, X₀) ≤ 2Λ e⁴ · Y e^{-log Y/(2Λ)}`. -/
theorem psi_rankin (hX : 10 ^ 8 ≤ Real.log X₀) {Y : ℝ} (hY : 1 ≤ Y) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤
      2 * Real.log X₀ * Real.exp 4 * (Y * Real.exp (-(Real.log Y) / (2 * Real.log X₀))) := by
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  set σ := 1 / (2 * Λ) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 / 100 := by
    rw [hσ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hY0 : 0 < Y := by linarith
  have h1 := Rankin.smoothCount_le_rankin X₀ (θ := 1 - σ) (by linarith) hY0.le
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  have hX3 : 3 ≤ X₀ := by
    have : (3 : ℝ) ≤ X₀ := by
      have := X₀_ge_two_pow hX; norm_num at this
      exact_mod_cast (by omega : 3 ≤ X₀)
    exact_mod_cast this
  set N := X₀ - 1 with hN
  have hN1 : N + 1 = X₀ := Nat.sub_add_cancel (by omega)
  have hN2 : 2 ≤ N := by omega
  have hlogN : Real.log N ≤ Λ := by
    rw [hΛ]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast (by omega))
  have hσN : σ * Real.log N ≤ 2 := by
    have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have : σ * Real.log N ≤ σ * Λ := mul_le_mul_of_nonneg_left hlogN hσ0.le
    have e : σ * Λ = 1 / 2 := by rw [hσ]; field_simp
    linarith
  have hcast : ((N + 1 : ℕ) : ℝ) = (X₀ : ℝ) := by rw [hN1]
  have h2 := BaseRange.rankinConst_le hσ0 hσ1 hN2 hσN (by rw [hcast]; linarith)
  rw [hN1] at h2
  have hE := BSCert.Consts.Ein_two_bounds.2
  have hexp : Real.exp (BSCert.EiFn.Ein 2 + 840 * σ) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    have : 840 * σ ≤ 840 / 100 := by linarith
    have : 840 * σ ≤ 0.31 := by
      rw [hσ, mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hR : Rankin.rankinConst X₀ (1 - σ) ≤ 2 * Λ * Real.exp 4 := by
    calc _ ≤ 1.8 * Λ * Real.exp (BSCert.EiFn.Ein 2 + 840 * σ) := h2
      _ ≤ 2 * Λ * Real.exp 4 := by
          have := Real.exp_pos (BSCert.EiFn.Ein 2 + 840 * σ)
          nlinarith
  have hYp : Y ^ (1 - σ) = Y * Real.exp (-(Real.log Y) / (2 * Λ)) := by
    rw [Real.rpow_sub hY0, Real.rpow_one, Real.rpow_def_of_pos hY0, div_eq_mul_inv,
      ← Real.exp_neg]
    congr 2
    rw [hσ]; ring
  rw [hYp] at h1
  have hY1 : 0 ≤ Y * Real.exp (-(Real.log Y) / (2 * Λ)) := by positivity
  calc _ ≤ Y * Real.exp (-(Real.log Y) / (2 * Λ)) * Rankin.rankinConst X₀ (1 - σ) := h1
    _ ≤ Y * Real.exp (-(Real.log Y) / (2 * Λ)) * (2 * Λ * Real.exp 4) :=
        mul_le_mul_of_nonneg_left hR hY1
    _ = _ := by ring

/-! ### The block bounds -/

section

variable (hc : Cond θ X₀)
include hc

/-- `ρ_det(w) ≤ Ψ(2v, X₀)/(κw)` for `0 < w ≤ v`. -/
lemma rhoDet_le_psi {w v : ℝ} (hw : 0 < w) (hwv : w ≤ v) :
    Target.rhoDet X₀ (kappaParam X₀) w ≤
      (Rankin.smoothCount X₀ (2 * v) : ℝ) / (kappaParam X₀ * w) := by
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hc.hX
  unfold Target.rhoDet
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : Target.rigidCount X₀ w ((1 + kappaParam X₀) * w) ≤
      Rankin.smoothCount X₀ ((1 + kappaParam X₀) * w) := by
    unfold Target.rigidCount Rankin.smoothCount
    exact Finset.card_filter_le _ _
  have h2 := Target.smoothCount_mono X₀ (show (1 + kappaParam X₀) * w ≤ 2 * v by nlinarith)
  exact_mod_cast h1.trans h2

/-- **The two block bounds** of the `ρ_det` change (Step 3, third bullet). -/
theorem abs_detF_le {r u δ : ℝ} (hr1 : 1 - 2 * δ ≤ r) (hr : r ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4) (hu : (X₀ : ℝ) ≤ u) :
    |detF X₀ r u| ≤ (10 * δ + 3 / X₀) / (kappaParam X₀ * (1 - 2 * δ)) ∧
      |detF X₀ r u| ≤ 3 * (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * u) := by
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hc.hX
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hu0 : 0 < u := by linarith
  have hr0 : 1 / 2 ≤ r := by linarith
  set v' := max (r * u) X₀ with hv'
  have hv1 : (X₀ : ℝ) ≤ v' := le_max_right _ _
  have hv2 : v' ≤ u := max_le (by nlinarith) hu
  have hv3 : r * u ≤ v' := le_max_left _ _
  have hv0 : 0 < v' := by linarith
  unfold detF
  rw [if_pos hu, ← hv']
  constructor
  · have h := rhoDet_kappa_sub_le hc.hX hv1 hv2
    rw [abs_sub_comm] at h
    refine h.trans ?_
    have hd : u - v' ≤ 2 * δ * u := by nlinarith
    have hlow : (1 - 2 * δ) * u ≤ v' := by nlinarith
    have hpos : 0 < 1 - 2 * δ := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 3 / (X₀ : ℝ) * u ≥ 3 := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by linarith)]; linarith
    have hk : 0 < kappaParam X₀ := hκ0
    -- `(5(u - v') + 3) κ (1-2δ) ≤ (10δ + 3/X₀) κ v'`
    have e1 : (5 * (u - v') + 3) * (1 - 2 * δ) ≤ (10 * δ + 3 / X₀) * v' := by
      have : (5 * (u - v') + 3) * (1 - 2 * δ) ≤ 10 * δ * u * (1 - 2 * δ) + 3 * (1 - 2 * δ) := by
        nlinarith
      have h4 : 3 * (1 - 2 * δ) ≤ 3 / X₀ * ((1 - 2 * δ) * u) := by nlinarith
      have h5 : 3 / (X₀ : ℝ) * ((1 - 2 * δ) * u) ≤ 3 / X₀ * v' :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      have h6 : 10 * δ * u * (1 - 2 * δ) ≤ 10 * δ * v' := by nlinarith
      nlinarith
    nlinarith
  · have h0u := rhoDet_nonneg X₀ hκ0 hu0.le
    have h0v := rhoDet_nonneg X₀ hκ0 hv0.le
    have hbu := rhoDet_le_psi hc hu0 le_rfl
    have hbv := rhoDet_le_psi hc hv0 hv2
    have hP0 : (0 : ℝ) ≤ Rankin.smoothCount X₀ (2 * u) := Nat.cast_nonneg _
    have hbv' : (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * v') ≤
        2 * (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : u ≤ 2 * v' := by nlinarith
      nlinarith [mul_nonneg hP0 hκ0.le]
    have e : 3 * (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * u) =
        (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * u) +
          2 * (Rankin.smoothCount X₀ (2 * u) : ℝ) / (kappaParam X₀ * u) := by ring
    rw [e, abs_le]; constructor <;> linarith

end

/-! ### Numerics -/

/-- `x e^{-x/c} ≤ c`. -/
lemma mul_exp_neg_le {x c : ℝ} (hc : 0 < c) : x * Real.exp (-x / c) ≤ c := by
  have h := Real.add_one_le_exp (x / c)
  have h0 := Real.exp_pos (x / c)
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ h0]
  have : x = c * (x / c) := by field_simp
  nlinarith

/-- `1/(1 - e^{-x}) ≤ 2/x` for `0 < x ≤ 1`. -/
lemma one_sub_exp_neg_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : x / 2 ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have h0 := Real.exp_pos x
  rw [Real.exp_neg]
  have : (Real.exp x)⁻¹ ≤ 1 / (1 + x) := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h2 : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-! ### The field `hdet` -/

section Det

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 4000000 in
/-- **The dyadic sum of Step 3, third bullet**: for `r ∈ [1-2δ, 1]`, `δ ≤ X₀^{-1/2}`,
`log y |∑_n c_n(y) (ρ_det(y/n) - ρ_det(max(ry/n, X₀)))/n| ≤ 77(T₁ + T₂)` with
`T₁ ≤ 7Λ⁴X₀^{-1/12}`, `T₂ ≤ 90Λ^{4.7}e^{-Λ/12}`. -/
theorem log_mul_abs_rhoSh_detF_le (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y δ r : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyZ : 2 * y / Xm X₀ ≤ Z) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) (hr1 : 1 - 2 * δ ≤ r) (hr : r ≤ 1) :
    Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ r)| ≤
      77 * (7 * Real.log X₀ ^ 4 * (X₀ : ℝ) ^ (-(1 / 12) : ℝ) +
        90 * Real.log X₀ ^ (4.7 : ℝ) * Real.exp (-(Real.log X₀ / 12))) := by
  classical
  set Λ := Real.log X₀ with hΛ
  have hX := hc.hX
  have hΛ0 : 0 < Λ := by linarith
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hX
  set κ := kappaParam X₀ with hκ
  set a : ℝ := 5 / 12 - 2 * 0.01 with ha
  have hκe : κ = Real.exp (-(a * Λ)) := by
    rw [hκ]; unfold kappaParam; rw [Real.rpow_def_of_pos hXp, ha]; congr 1; ring
  have hκinv : 1 / κ = Real.exp (a * Λ) := by
    rw [hκe, one_div, ← Real.exp_neg, neg_neg]
  have hXe : (X₀ : ℝ) = Real.exp Λ := (Real.exp_log hXp).symm
  have hδe : δ ≤ Real.exp (-(Λ / 2)) := by
    refine hδ.trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos hXp]; congr 1; ring
  -- `exp` lower bounds
  have hexpL : ∀ c : ℝ, 0 < c → 1 + c * Λ ≤ Real.exp (c * Λ) := fun c _ => by
    have := Real.add_one_le_exp (c * Λ); linarith
  have hδs : δ ≤ 1 / 1000 := by
    have := hexpL (1 / 2) (by norm_num)
    have h2 : Real.exp (-(Λ / 2)) ≤ 1 / 1000 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
      have : Λ / 2 = 1 / 2 * Λ := by ring
      rw [this]; nlinarith
    linarith
  have hδ4 : δ ≤ 1 / 4 := by linarith
  have hP := Nat.cast_nonneg (α := ℝ)
  have hdec := KR.Chain.dec_R hT
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  -- the block bounds
  set BA := (10 * δ + 3 / X₀) / (κ * (1 - 2 * δ)) with hBA
  set C := 2 * Λ * Real.exp 4 with hC
  set j₁ : ℕ := ⌈4 * Λ ^ 2⌉₊ with hj₁
  set b : ℕ → ℝ := fun j => if j < j₁ then BA else
    12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ)) with hb
  have hBA0 : 0 ≤ BA := by
    have : 0 < 1 - 2 * δ := by linarith
    positivity
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    simp only [hb]; split_ifs
    · exact hBA0
    · positivity
  have hg0 : ∀ u : ℝ, u < X₀ → detF X₀ r u = 0 := fun u hu => by
    unfold detF; rw [if_neg (not_le.mpr hu)]
  have hblk : ∀ (j : ℕ) (u : ℝ), 2 ^ j * (X₀ : ℝ) ≤ u → u ≤ 2 * (2 ^ j * X₀) →
      |detF X₀ r u| ≤ b j := by
    intro j u h1 h2
    have hj1 : (X₀ : ℝ) ≤ 2 ^ j * X₀ := le_mul_of_one_le_left hXp.le (one_le_pow₀ (by norm_num))
    have hu : (X₀ : ℝ) ≤ u := hj1.trans h1
    obtain ⟨hA, hB⟩ := abs_detF_le hc hr1 hr hδ0.le hδ4 hu
    simp only [hb]
    split_ifs with hj
    · exact hA
    · refine hB.trans ?_
      set Y : ℝ := 2 ^ (j + 2) * X₀ with hY
      have hY1 : 1 ≤ Y := by
        have : (1 : ℝ) ≤ 2 ^ (j + 2) := one_le_pow₀ (by norm_num)
        nlinarith
      have hmono := Target.smoothCount_mono X₀ (show 2 * u ≤ Y by
        rw [hY, pow_add]; nlinarith)
      have hR := psi_rankin hX hY1
      have hlogY : Real.log Y = Λ + (j + 2) * Real.log 2 := by
        rw [hY, Real.log_mul (by positivity) hXp.ne', Real.log_pow]; push_cast; ring
      rw [hlogY] at hR
      have hu0 : 0 < u := by linarith
      have hj0 : (0 : ℝ) < 2 ^ j * X₀ := by positivity
      calc 3 * (Rankin.smoothCount X₀ (2 * u) : ℝ) / (κ * u)
          ≤ 3 * (Rankin.smoothCount X₀ Y : ℝ) / (κ * (2 ^ j * X₀)) := by
            apply div_le_div₀ (by positivity) (by exact_mod_cast
              (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmono) (by norm_num : (0:ℝ) ≤ 3)))
              (by positivity) (mul_le_mul_of_nonneg_left h1 hκ0.le)
        _ ≤ 3 * (C * (Y * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ)))) /
              (κ * (2 ^ j * X₀)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have := hR
            rw [hC]; nlinarith
        _ = 12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ)) := by
            rw [hY, pow_add]; field_simp; ring
  -- Corollary 5.9
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, y < 2 ^ J * X₀ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (y / X₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨J, by rw [div_lt_iff₀ hXp] at hJ; linarith⟩
  have hR := KR.G1.log_mul_abs_rhoSh_le (P := PR θ X₀ ω) (tw := twR θ X₀ ω) hT.hbs hT.hXm
    hdec.1 hdec.2 hXmX (hXmX.trans hy) hyZ (g := detF X₀ r) hg0 hb0 hblk hJ
  have hCS := BeurlingSystem.CS_le
  set ℓ : ℕ → ℝ := fun j => Real.log (2 * (2 ^ j * (X₀ : ℝ))) with hℓ
  have hℓe : ∀ j : ℕ, ℓ j = Λ + (j + 1) * Real.log 2 := fun j => by
    simp only [hℓ]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hXp.ne',
      Real.log_pow]; ring
  have hℓ0 : ∀ j, 0 ≤ ℓ j := fun j => by rw [hℓe]; positivity
  have hS0 : 0 ≤ ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y), ℓ j * b j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hℓ0 j) (hb0 j)
  -- the two parts of the dyadic sum
  set q := Real.exp (-(Real.log 2) / (4 * Λ)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < Real.log 2 / (4 * Λ) := by positivity
    rw [neg_div]; linarith)
  set T1 := (j₁ : ℝ) * (Λ + (j₁ + 1) * Real.log 2) * BA with hT1
  set T2 := 12 * C / κ * (4 * Λ) * (q ^ j₁ / (1 - q)) with hT2
  have hsplit : ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y), ℓ j * b j ≤
      T1 + T2 := by
    have e1 : ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y), ℓ j * b j ≤
        ∑ j ∈ Finset.range J, ℓ j * b j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun j _ _ => mul_nonneg (hℓ0 j) (hb0 j)
    have e2 : ∑ j ∈ Finset.range J, ℓ j * b j =
        ∑ j ∈ (Finset.range J).filter (· < j₁), ℓ j * BA +
          ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < j₁), ℓ j *
            (12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ))) := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hb]; split_ifs <;> ring
    have e3 : ∑ j ∈ (Finset.range J).filter (· < j₁), ℓ j * BA ≤ T1 := by
      have hterm : ∀ j ∈ (Finset.range J).filter (· < j₁), ℓ j * BA ≤
          (Λ + (j₁ + 1) * Real.log 2) * BA := by
        intro j hj
        have hjj : (j : ℝ) < j₁ := by exact_mod_cast (Finset.mem_filter.mp hj).2
        apply mul_le_mul_of_nonneg_right _ hBA0
        rw [hℓe]; nlinarith
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, hT1, mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by
        have : 0 ≤ Λ + (j₁ + 1) * Real.log 2 := by positivity
        positivity)
      have : (Finset.range J).filter (· < j₁) ⊆ Finset.range j₁ := by
        intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      have := Finset.card_le_card this
      rw [Finset.card_range] at this
      exact_mod_cast this
    have e4 : ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < j₁), ℓ j *
        (12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ))) ≤ T2 := by
      have hterm : ∀ j ∈ (Finset.range J).filter (fun j => ¬ j < j₁), ℓ j *
          (12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ))) ≤
          12 * C / κ * (4 * Λ) * q ^ j := by
        intro j _
        have hL := hℓe j
        set L := ℓ j
        have h1 : Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ)) ≤
            Real.exp (-L / (4 * Λ)) * Real.exp (-L / (4 * Λ)) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          rw [hL, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h2 : L * Real.exp (-L / (4 * Λ)) ≤ 4 * Λ := mul_exp_neg_le (by positivity)
        have h3 : Real.exp (-L / (4 * Λ)) ≤ q ^ j := by
          rw [hq, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
          rw [hL, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hK : 0 ≤ 12 * C / κ := by positivity
        calc L * (12 * C / κ * Real.exp (-(Λ + (j + 2) * Real.log 2) / (2 * Λ)))
            ≤ L * (12 * C / κ * (Real.exp (-L / (4 * Λ)) * Real.exp (-L / (4 * Λ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hK) (hℓ0 j)
          _ = 12 * C / κ * (L * Real.exp (-L / (4 * Λ))) * Real.exp (-L / (4 * Λ)) := by ring
          _ ≤ 12 * C / κ * (4 * Λ) * q ^ j := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left h2 hK) h3 (Real.exp_pos _).le
              positivity
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum, hT2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hIco : (Finset.range J).filter (fun j => ¬ j < j₁) = Finset.Ico j₁ J := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hIco]
      exact geom_sum_Ico_le_of_lt_one hq0 hq1
    linarith
  -- numerics
  have hT1b : T1 ≤ 7 * Λ ^ 4 * (X₀ : ℝ) ^ (-(1 / 12) : ℝ) := by
    have hj₁ : (j₁ : ℝ) ≤ 4 * Λ ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hj₁0 : (0 : ℝ) ≤ j₁ := Nat.cast_nonneg _
    have hBAb : BA ≤ 22 * Real.exp ((a - 1 / 2) * Λ) := by
      have h3 : 3 / (X₀ : ℝ) ≤ Real.exp (-(Λ / 2)) := by
        rw [hXe, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
        have := hexpL (1 / 2) (by norm_num)
        have e : -(Λ / 2) + Λ = 1 / 2 * Λ := by ring
        rw [e]; linarith
      have hpos : 0 < 1 - 2 * δ := by linarith
      have hnum : 10 * δ + 3 / X₀ ≤ 11 * Real.exp (-(Λ / 2)) := by linarith
      rw [hBA, div_le_iff₀ (by positivity)]
      have hee : Real.exp ((a - 1 / 2) * Λ) * Real.exp (-(a * Λ)) = Real.exp (-(Λ / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e : 22 * Real.exp ((a - 1 / 2) * Λ) * (κ * (1 - 2 * δ)) =
          22 * (1 - 2 * δ) * Real.exp (-(Λ / 2)) := by
        rw [hκe, ← hee]; ring
      rw [e]
      have : 11 ≤ 22 * (1 - 2 * δ) := by linarith
      nlinarith [Real.exp_pos (-(Λ / 2))]
    have hpoly : (j₁ : ℝ) * (Λ + (j₁ + 1) * Real.log 2) ≤ 13 * Λ ^ 4 := by
      have h1 : Λ + (j₁ + 1) * Real.log 2 ≤ 3 * Λ ^ 2 := by nlinarith
      have h2 : (0 : ℝ) ≤ Λ + (j₁ + 1) * Real.log 2 := by positivity
      calc (j₁ : ℝ) * (Λ + (j₁ + 1) * Real.log 2) ≤ (4 * Λ ^ 2 + 1) * (3 * Λ ^ 2) :=
            mul_le_mul hj₁ h1 h2 (by positivity)
        _ ≤ 13 * Λ ^ 4 := by
            have hL2 : 3 ≤ Λ ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left hL2 (sq_nonneg Λ)]
    have hX12 : (X₀ : ℝ) ^ (-(1 / 12) : ℝ) = Real.exp (-(Λ / 12)) := by
      rw [Real.rpow_def_of_pos hXp]; congr 1; ring
    rw [hX12]
    have hsl : 286 * Real.exp ((a - 1 / 2) * Λ) ≤ 7 * Real.exp (-(Λ / 12)) := by
      have e : (a - 1 / 2) * Λ = -(Λ / 12) + -(2 * 0.01 * Λ) := by rw [ha]; ring
      rw [e, Real.exp_add]
      have h1 := hexpL (2 * 0.01) (by norm_num)
      have h2 : Real.exp (-(2 * 0.01 * Λ)) ≤ 1 / 100 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
        nlinarith
      have := Real.exp_pos (-(Λ / 12))
      nlinarith
    calc T1 = (j₁ : ℝ) * (Λ + (j₁ + 1) * Real.log 2) * BA := rfl
      _ ≤ 13 * Λ ^ 4 * (22 * Real.exp ((a - 1 / 2) * Λ)) :=
          mul_le_mul hpoly hBAb hBA0 (by positivity)
      _ = Λ ^ 4 * (286 * Real.exp ((a - 1 / 2) * Λ)) := by ring
      _ ≤ Λ ^ 4 * (7 * Real.exp (-(Λ / 12))) :=
          mul_le_mul_of_nonneg_left hsl (by positivity)
      _ = 7 * Λ ^ 4 * Real.exp (-(Λ / 12)) := by ring
  have hT2b : T2 ≤ 90 * Λ ^ (4.7 : ℝ) * Real.exp (-(Λ / 12)) := by
    have hx0 : 0 < Real.log 2 / (4 * Λ) := by positivity
    have hx1 : Real.log 2 / (4 * Λ) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h1q := one_sub_exp_neg_ge hx0 hx1
    rw [← neg_div] at h1q
    have hinv : 1 / (1 - q) ≤ 12 * Λ := by
      rw [div_le_iff₀ (by linarith)]
      have : Real.log 2 / (4 * Λ) * (12 * Λ) = 3 * Real.log 2 := by field_simp; ring
      nlinarith
    have hqj : q ^ j₁ ≤ Real.exp (-(0.69 * Λ)) := by
      rw [hq, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      have hj : 4 * Λ ^ 2 ≤ (j₁ : ℝ) := Nat.le_ceil _
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hC0 : 0 < C := by rw [hC]; positivity
    have hK0 : 0 ≤ 12 * C * Real.exp (a * Λ) * (4 * Λ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0.le) (Real.exp_pos _).le) (by linarith)
    have hT2e : T2 = (12 * C * Real.exp (a * Λ) * (4 * Λ)) * (q ^ j₁ * (1 / (1 - q))) := by
      rw [hT2, ← hκinv]; ring
    have hT2' : T2 ≤ 12 * C * Real.exp (a * Λ) * (4 * Λ) *
        (Real.exp (-(0.69 * Λ)) * (12 * Λ)) := by
      rw [hT2e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hqj hinv (one_div_pos.mpr (by linarith)).le (Real.exp_pos _).le) hK0
    refine hT2'.trans ?_
    have hee : Real.exp (a * Λ) * Real.exp (-(0.69 * Λ)) =
        Real.exp (-(Λ / 12)) * Real.exp (-(0.21 * Λ)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [ha]; ring
    have e : 12 * C * Real.exp (a * Λ) * (4 * Λ) * (Real.exp (-(0.69 * Λ)) * (12 * Λ)) =
        (1152 * Real.exp 4 * Real.exp (-(0.21 * Λ))) * Λ ^ 3 * Real.exp (-(Λ / 12)) := by
      have : 12 * C * Real.exp (a * Λ) * (4 * Λ) * (Real.exp (-(0.69 * Λ)) * (12 * Λ)) =
          12 * C * (4 * Λ) * (12 * Λ) * (Real.exp (a * Λ) * Real.exp (-(0.69 * Λ))) := by ring
      rw [this, hee, hC]; ring
    rw [e]
    have hsmall : 1152 * Real.exp 4 * Real.exp (-(0.21 * Λ)) ≤ 90 := by
      have he4 : Real.exp 4 ≤ 55 := by
        have h := Real.exp_one_lt_d9
        have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e4]
        calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by gcongr
          _ ≤ 55 := by norm_num
      have h21 : Real.exp (-(0.21 * Λ)) ≤ 1 / 10 ^ 6 := by
        have := hexpL 0.21 (by norm_num)
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
        nlinarith
      have := Real.exp_pos (-(0.21 * Λ))
      nlinarith
    have hpow : Λ ^ 3 ≤ Λ ^ (4.7 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hE := Real.exp_pos (-(Λ / 12))
    have hL3 : 0 ≤ Λ ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hsmall hpow hL3 (by norm_num)) hE.le
  -- assembly
  calc Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ r)|
      ≤ _ := hR
    _ ≤ 77 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y), ℓ j * b j :=
        mul_le_mul_of_nonneg_right hCS hS0
    _ ≤ 77 * (T1 + T2) := mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have : Real.exp (-(Λ / 12)) = Real.exp (-(Real.log X₀ / 12)) := rfl
        linarith

/-- **The field `hdet`** (Proposition 5.35(B), Step 3, third bullet), with `C_S = 77`. -/
theorem hdet_R (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyZ : 2 * y / Xm X₀ ≤ Z) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) :
    Real.log y * detS θ X₀ ω y δ ≤
      77 * (7 * Real.log X₀ ^ 4 * (X₀ : ℝ) ^ (-(1 / 12) : ℝ) +
        90 * Real.log X₀ ^ (4.7 : ℝ) * Real.exp (-(Real.log X₀ / 12))) := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hδ1 : δ ≤ 1 / 4 := by
    refine hδ.trans ?_
    rw [Real.rpow_def_of_pos (by linarith)]
    have h := Real.add_one_le_exp (Real.log X₀ / 2)
    have hX := hc.hX
    rw [show Real.log X₀ * (-(1 / 2)) = -(Real.log X₀ / 2) by ring, Real.exp_neg,
      inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  haveI : Nonempty (Icc (y * (1 - 2 * δ)) (y * (1 - δ))) :=
    ⟨⟨y * (1 - δ), Set.mem_Icc.mpr ⟨by nlinarith, le_rfl⟩⟩⟩
  rw [mul_comm, ← le_div_iff₀ hly]
  unfold detS
  refine ciSup_le fun z => ?_
  rw [le_div_iff₀ hly, mul_comm]
  obtain ⟨z, hz1, hz2⟩ := z
  have hr1 : 1 - 2 * δ ≤ z / y := by rw [le_div_iff₀ hy0]; nlinarith
  have hr : z / y ≤ 1 := by rw [div_le_one hy0]; nlinarith
  exact log_mul_abs_rhoSh_detF_le hc hev ω hT hy hyZ hδ0 hδ hr1 hr

end Det

end BModel

end
