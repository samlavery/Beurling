module

public import RequestProject.Beurling.Noise.RML7Eta
public import RequestProject.Beurling.Noise.RML6K

/-!
# Round 8: the size inputs `hεN`, `hj`, `hsmall2` of `KR.RML6.G1BInputs`

* `KR.RML8E.epsN_le` (`hεN`): the paper's
  `ε_N = 5.1 C_N Σ_u log(2u) F̄_r(u) + 35.8 C_N C_S' Σ_v (log 3v)² F̄_r(v) + sup 6 log x/H(x)`
  is `≤ 10⁻¹³` for `C_N ≤ 158`, `C_S' = 10`, the (sw-sums)/(osc) sizes
  `Σ_u log(2u) F̄_r(u) ≤ 10⁻²⁰`, `Σ_v (log 3v)² F̄_r(v) ≤ e^{-41} + 2·10⁻²²` and
  `6 log x/H ≤ 10⁻²⁰` (Lemma 5.34, 04f-bridge.tex lines 108-121; the largest part is
  `35.8·158·10·e^{-41} ≤ 8.85·10⁻¹⁴`).
* `KR.RML8E.sumG_split`: the split `Σ (log 3v)² F̄_r = Σ (log 3v)²(o + 6/H + ν̄ + 54η)`.
* `KR.RML8E.jX0_huge` (`hj`): the final arithmetic of Proposition 5.31(iii) (huge range,
  04x-x0band.tex lines 389-391): from `𝔅(y) ≤ (400δ + e^{-60}) τ₀/J`, `τ₀ ≤ 1.0001Λ`,
  `log y ≤ J + Λ + 1`, `J ≥ 600Λ⁴`, `j₀ ≤ 1.0001/Λ`, `400δ ≤ e^{-60}/2` and
  `4.3 C_N E_θ ≤ e^{-0.99Λ}`: `log y · j₀ (𝔅 + 4.3 C_N E_θ/log y) ≤ e^{-59}`;
  `KR.RML8E.huge_of_logy` : `log y ≥ X₀^{1/100}` puts `y` in the huge range,
  `J = log(y/X₀) ≥ 600Λ⁴`.
* `KR.RML8E.etaG_le_etaS`, `KR.RML8E.hsmall2_of` (`hNT`'s `η` and `hsmall2`): with
  `η := 1662400 Φ₂(X₀⁻/2)/log y`, `η(s) ≤ η` at every `s` with `log y ≤ 2 log s` (from
  `logy_eta_le`), and `log y (ν̄ + 54η) ≤ 10⁻²⁶` given `log y · ν̄ ≤ 10⁻²⁷` (Lemma 5.22 with
  (sw-sums); Queue6) and `Φ₂(X₀⁻/2) ≤ e^{-200}` (`Phi_tiny`).
-/

@[expose] public section

open Real

namespace KR.RML8E

/-- `e^{41} ≥ 6.398·10¹⁷`. -/
lemma exp41_ge : (6.398e17 : ℝ) ≤ Real.exp 41 := by
  have h1 := Real.exp_one_gt_d9
  have e : Real.exp 41 = Real.exp 1 ^ 41 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h2 : (2.7182818283 : ℝ) ^ 41 ≤ Real.exp 1 ^ 41 :=
    pow_le_pow_left₀ (by norm_num) h1.le 41
  have h3 : (6.398e17 : ℝ) ≤ (2.7182818283 : ℝ) ^ 41 := by norm_num
  linarith

/-- `e^{-41} ≤ 1.5630·10⁻¹⁸`. -/
lemma exp_neg41_le : Real.exp (-41) ≤ 1.5630e-18 := by
  rw [Real.exp_neg]
  have h := exp41_ge
  have hp : (0 : ℝ) < 6.398e17 := by norm_num
  calc (Real.exp 41)⁻¹ ≤ (6.398e17 : ℝ)⁻¹ := inv_anti₀ hp h
    _ ≤ 1.5630e-18 := by norm_num

/-- **`hεN`: `ε_N ≤ 10⁻¹³`** (Lemma 5.34): with `C_N ≤ 158`, `C_S' = 10` and the sizes of
(sw-sums), (osc) and Lemma 5.20. -/
theorem epsN_le {CN SK SG h6 : ℝ} (hCN : CN ≤ 158) (hSK0 : 0 ≤ SK)
    (hSK : SK ≤ 1 / 10 ^ 20) (hSG0 : 0 ≤ SG) (hSG : SG ≤ Real.exp (-41) + 2 / 10 ^ 22)
    (hh6 : h6 ≤ 1 / 10 ^ 20) :
    5.1 * CN * SK + 35.8 * CN * 10 * SG + h6 ≤ 1 / 10 ^ 13 := by
  have he := exp_neg41_le
  have hSG' : SG ≤ 1.5632e-18 := by linarith
  have t1 : 5.1 * CN * SK ≤ 5.1 * 158 * (1 / 10 ^ 20) :=
    mul_le_mul (by nlinarith) hSK hSK0 (by norm_num)
  have t2 : 35.8 * CN * 10 * SG ≤ 35.8 * 158 * 10 * 1.5632e-18 :=
    mul_le_mul (by nlinarith) hSG' hSG0 (by norm_num)
  norm_num at t1 t2 ⊢
  linarith

/-- The split of the `G`-sum over the four parts of `F̄_r = o + 6/H + ν̄ + 54η`. -/
lemma sumG_split {ι : Type*} (s : Finset ι) (w o h ν η : ι → ℝ) :
    ∑ v ∈ s, w v * (o v + h v + ν v + 54 * η v) =
      ∑ v ∈ s, w v * o v + ∑ v ∈ s, w v * h v + ∑ v ∈ s, w v * ν v +
        54 * ∑ v ∈ s, w v * η v := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => by ring

/-- `Σ (log 3v)² F̄_r ≤ e^{-41} + 2·10⁻²²` from the four (sw-sums)/(osc)/Lemma 5.20 sizes:
`Σ (log 3v)² o_v ≤ e^{-41}` (osc; Model), `Σ (log 3v)² 6/H ≤ 5·10⁻²³`,
`Σ (log 3v)² ν̄ ≤ 10⁻²²` (sw-sums; Queue6), `54 Σ (log 3v)² η ≤ 5·10⁻²³` (Lemma 5.20). -/
theorem sumG_le {ι : Type*} (s : Finset ι) (w o h ν η : ι → ℝ)
    (ho : ∑ v ∈ s, w v * o v ≤ Real.exp (-41)) (hh : ∑ v ∈ s, w v * h v ≤ 5 / 10 ^ 23)
    (hν : ∑ v ∈ s, w v * ν v ≤ 1 / 10 ^ 22) (hη : 54 * ∑ v ∈ s, w v * η v ≤ 5 / 10 ^ 23) :
    ∑ v ∈ s, w v * (o v + h v + ν v + 54 * η v) ≤ Real.exp (-41) + 2 / 10 ^ 22 := by
  rw [sumG_split]
  have : (5 : ℝ) / 10 ^ 23 + 1 / 10 ^ 22 + 5 / 10 ^ 23 = 2 / 10 ^ 22 := by norm_num
  linarith

/-! ## `hj`: the huge range of Proposition 5.31 -/

/-- `log y ≥ X₀^{1/100}` puts `y` in the huge range: `J = log y - Λ ≥ 600 Λ⁴`
(`Λ = log X₀ ≥ 10⁸`). -/
theorem huge_of_logy {Λ ly : ℝ} (hΛ : 100000000 ≤ Λ) (hly : Real.exp (Λ / 100) ≤ ly) :
    600 * Λ ^ 4 ≤ ly - Λ := by
  have ht : 0 ≤ Λ / 100 := by positivity
  have h8 := Real.pow_div_factorial_le_exp (x := Λ / 100) ht 8
  have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hf] at h8
  have hΛ0 : 0 < Λ := by linarith
  -- `(Λ/100)^8/40320 ≥ 600Λ⁴ + Λ`
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have key : 600 * Λ ^ 4 + Λ ≤ (Λ / 100) ^ 8 / 40320 := by
    have e : (Λ / 100) ^ 8 / 40320 = Λ ^ 4 * (Λ ^ 4 / (10 ^ 16 * 40320)) := by ring
    rw [e]
    have h1 : 601 ≤ Λ ^ 4 / (10 ^ 16 * 40320) := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    have hΛ1 : Λ ≤ Λ ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith
  linarith

/-- **`hj`: `j_{X₀} ≤ e^{-59}` in the huge range** (Proposition 5.31(iii), final arithmetic). -/
theorem jX0_huge {Λ J ly jz B δ τ0 CNE : ℝ} (hΛ : 100000000 ≤ Λ) (hJ : 600 * Λ ^ 4 ≤ J)
    (hly0 : 0 < ly) (hly : ly ≤ J + Λ + 1) (hτ0 : 0 ≤ τ0) (hτ : τ0 ≤ 1.0001 * Λ)
    (hjz0 : 0 ≤ jz) (hjz : jz ≤ 1.0001 / Λ) (hδ0 : 0 ≤ δ) (hδ : 400 * δ ≤ Real.exp (-60) / 2)
    (hB : B ≤ (400 * δ + Real.exp (-60)) * τ0 / J) (hE0 : 0 ≤ CNE)
    (hE : CNE ≤ Real.exp (-(0.99 * Λ))) :
    ly * jz * (B + CNE / ly) ≤ Real.exp (-59) := by
  have hΛ0 : 0 < Λ := by linarith
  have hJ0 : 0 < J := by nlinarith [pow_pos hΛ0 4]
  set c := 400 * δ + Real.exp (-60) with hc
  have hc0 : 0 ≤ c := by positivity
  -- `ly · jz · τ₀/J ≤ 1.0003`
  have hratio : ly * jz * (τ0 / J) ≤ 1.0003 := by
    have h1 : jz * τ0 ≤ 1.0001 / Λ * (1.0001 * Λ) := mul_le_mul hjz hτ hτ0 (by positivity)
    have h2 : 1.0001 / Λ * (1.0001 * Λ) = 1.00020001 := by field_simp; norm_num
    have h3 : ly / J ≤ 1.0000001 := by
      rw [div_le_iff₀ hJ0]
      have hΛ3 : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
      nlinarith [pow_pos hΛ0 3]
    have e : ly * jz * (τ0 / J) = (ly / J) * (jz * τ0) := by ring
    rw [e]
    calc (ly / J) * (jz * τ0) ≤ 1.0000001 * 1.00020001 :=
          mul_le_mul h3 (h1.trans h2.le) (by positivity) (by norm_num)
      _ ≤ 1.0003 := by norm_num
  have hBpart : ly * jz * B ≤ 1.0003 * c := by
    have : ly * jz * B ≤ ly * jz * (c * τ0 / J) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have e : ly * jz * (c * τ0 / J) = c * (ly * jz * (τ0 / J)) := by ring
    rw [e] at this
    nlinarith
  have hEpart : ly * jz * (CNE / ly) ≤ Real.exp (-(0.99 * Λ)) := by
    have e : ly * jz * (CNE / ly) = jz * CNE := by field_simp
    rw [e]
    have hjz1 : jz ≤ 1 := hjz.trans (by rw [div_le_one hΛ0]; linarith)
    calc jz * CNE ≤ 1 * CNE := mul_le_mul_of_nonneg_right hjz1 hE0
      _ ≤ _ := by linarith
  -- `e^{-0.99Λ} ≤ e^{-60}/1000`
  have hsmall : Real.exp (-(0.99 * Λ)) ≤ Real.exp (-60) / 1000 := by
    have h1 : Real.exp (-(0.99 * Λ)) ≤ Real.exp (-67) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-67) = Real.exp (-60) * Real.exp (-7) := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (-7) ≤ 1 / 1000 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 7) (by norm_num)]
      have := Real.add_one_le_exp (7 : ℝ)
      have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have he1 := Real.exp_one_gt_d9
      have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      rw [h7]; norm_num at this ⊢; linarith
    rw [h2] at h1
    have := Real.exp_pos (-60)
    nlinarith
  have hfin : Real.exp (-59) = Real.exp (-60) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have he1 := Real.exp_one_gt_d9
  have hpos := Real.exp_pos (-60)
  have hcle : c ≤ 1.5 * Real.exp (-60) := by rw [hc]; linarith
  rw [mul_add]
  rw [hfin]
  nlinarith

/-- **`hj` at the heights of range (B)**: for `log y > X₀^{1/100}` (`Λ = log X₀ ≥ 10⁸`), with
`J := log y - Λ`, the huge-range bound of Proposition 5.31(iii)
`𝔅(y) ≤ (400δ + e^{-60}) τ₀/J` (input `hB`; §5, the level analysis of 04x lines 325-389, not
formalized), `τ₀ ≤ 1.0001Λ`, `j₀ ≤ 1.0001/Λ` (BaseRange `jzX_le`), `400δ ≤ e^{-60}/2` and
`4.3 C_N E_θ ≤ e^{-0.99Λ}` (Lemma 5.20) give `log y · j₀(𝔅 + 4.3 C_N E_θ/log y) ≤ e^{-59}`. -/
theorem hj_of_range {X0 : ℕ} {y jz B δ τ0 CNE : ℝ} (hΛ : 100000000 ≤ Real.log X0)
    (hy : (X0 : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hτ0 : 0 ≤ τ0)
    (hτ : τ0 ≤ 1.0001 * Real.log X0) (hjz0 : 0 ≤ jz) (hjz : jz ≤ 1.0001 / Real.log X0)
    (hδ0 : 0 ≤ δ) (hδ : 400 * δ ≤ Real.exp (-60) / 2)
    (hB : B ≤ (400 * δ + Real.exp (-60)) * τ0 / (Real.log y - Real.log X0))
    (hE0 : 0 ≤ CNE) (hE : CNE ≤ Real.exp (-(0.99 * Real.log X0))) :
    Real.log y * jz * (B + CNE / Real.log y) ≤ Real.exp (-59) := by
  have hX0 : (0 : ℝ) < X0 := by
    by_contra hc; push_neg at hc
    have : (X0 : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hr : (X0 : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Real.log X0 / 100) := by
    rw [Real.rpow_def_of_pos hX0]; ring_nf
  rw [hr] at hy
  have hJ := huge_of_logy hΛ hy.le
  have hly0 : 0 < Real.log y := lt_trans (Real.exp_pos _) hy
  exact jX0_huge hΛ hJ hly0 (by linarith) hτ0 hτ hjz0 hjz hδ0 hδ hB hE0 hE

/-! ## `hsmall2`, with the choice of `η` -/

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- The choice `η := 1662400 Φ₂(X₀⁻/2)/log y` (Lemma 5.20, last claim, read at the heights `s`
of the windows of `J`, where `log y ≤ 2 log s`). -/
noncomputable def etaS (H : ℝ → ℝ) (X0m y : ℝ) : ℝ :=
  1662400 * TNP.Phi H 2 (X0m / 2) / Real.log y

/-- `η(s) ≤ η` at every height `s ≥ 1` of the windows (`log y ≤ 2 log s`, `9s ≤ Z²`). -/
theorem etaG_le_etaS (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {y s : ℝ} (hy : 1 < y)
    (hs : 1 ≤ s) (hys : Real.log y ≤ 2 * Real.log s) (hZ0 : 2500 ≤ Z) (hZ : 9 * s ≤ Z ^ 2) :
    KR.etaG P H tw X0m (fun _ => 1) s ≤ etaS H X0m y := by
  have hb := TNP.logy_eta_le h hs hZ0 hZ
  have hly : 0 < Real.log y := Real.log_pos hy
  have hls : 0 < Real.log s := by linarith
  have he0 := KR.RML6K.etaG_one_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) s
  unfold etaS
  rw [le_div_iff₀ hly]
  calc KR.etaG P H tw X0m (fun _ => 1) s * Real.log y
      ≤ KR.etaG P H tw X0m (fun _ => 1) s * (2 * Real.log s) :=
        mul_le_mul_of_nonneg_left hys he0
    _ = 2 * (Real.log s * KR.etaG P H tw X0m (fun _ => 1) s) := by ring
    _ ≤ 2 * (831200 * TNP.Phi H 2 (X0m / 2)) := by linarith
    _ = 1662400 * TNP.Phi H 2 (X0m / 2) := by ring

/-- **`hsmall2`**: `log y (ν̄ + 54η) ≤ 10⁻²⁶` for `η = etaS`, given `log y · ν̄ ≤ 10⁻²⁷`
(Lemma 5.22 with (sw-sums); Queue6) and `Φ₂(X₀⁻/2) ≤ e^{-200}` (`WidthReal.Phi_tiny`). -/
theorem hsmall2_of {y nb : ℝ} (hy : 1 < y) (hnb : Real.log y * nb ≤ 1 / 10 ^ 27)
    (hPhi : TNP.Phi H 2 (X0m / 2) ≤ Real.exp (-200)) :
    Real.log y * (nb + 54 * etaS H X0m y) ≤ 1 / 10 ^ 26 := by
  have hly : 0 < Real.log y := Real.log_pos hy
  have e : Real.log y * (nb + 54 * etaS H X0m y) =
      Real.log y * nb + 54 * 1662400 * TNP.Phi H 2 (X0m / 2) := by
    unfold etaS; field_simp
  rw [e]
  have h200 : Real.exp (-200) ≤ 1 / 10 ^ 40 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 200) (by norm_num)]
    have h1 : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
    have he := Real.exp_one_gt_d9
    have : (2 : ℝ) ^ 200 ≤ Real.exp 1 ^ 200 := pow_le_pow_left₀ (by norm_num) (by linarith) 200
    rw [h1]; norm_num at this ⊢; linarith
  have : 54 * 1662400 * TNP.Phi H 2 (X0m / 2) ≤ 54 * 1662400 * (1 / 10 ^ 40) := by
    have := hPhi.trans h200; nlinarith
  norm_num at this ⊢
  linarith

end KR.RML8E

end
