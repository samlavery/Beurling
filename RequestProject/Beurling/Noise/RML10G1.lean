module

public import RequestProject.Beurling.Noise.RML10G1Win

/-!
# `KR.RML9.G1ResSec5` from the Model's concrete bounds (Proposition 5.35(B))

`sec5_of` builds the exact `KR.RML9.G1ResSec5 P tw X0m X₀ y δ ρ ν NT vtH TcL Jl Tc hO` that
`KR.RML9.g1BInputs_of` consumes, with

* `CN = C_N = CNt X₀` (`hCN` by `CNt_bounds`);
* the bullets of Lemma 5.34 at the Model's bounds
  `aK z = aK(C_N, S z, H_c, z)` and `bG z = 35.8 C_N · 10 · Gs z` (`Model/RestK`, `RestG`:
  `S = SK θ X₀ ω nb`, `Gs z = ∑_{i ≤ Jc z} (log 3v_i)² (obG i + FrBv nb i)`);
* `SK = S_b`, `SG = G_b`, `h6` as in `hsize_of` (`hsize`, `h6_le`);
* `hHhalf` from `WinGlob.hHw`;
* `hBRs` by `brs_of`, `hXBs` with `Bx = BxY X₀ y`, `CNE = 0` by `xbs_of`, and Proposition
  5.31(iii) with `δ_x = e^{-60}/800`, `τ₀ = 1.0001 Λ` by `hBx_of`.

`g1BInputs_of'` is `KR.RML9.g1BInputs_of` with this `G1ResSec5`.
-/

@[expose] public section

open Real Set KR.Ops

namespace KR.RML10

open KR.TNP KR.Chain KR.RML9

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X₀ : ℕ} {y Z η1 η2 : ℝ}
  {ε1 : ℝ → ℝ} {εW θW εS δ thrS : ℝ} {ρ ν NT vtH TcL Jl : LocInt} {ϑ NTpt Tc : ℝ → ℝ}

/-- `z - H(z)/2 ≥ y/4` and `z ≥ y/2` on `J`, so `log y - log 4 ≤ log(z - H(z)/2), log z`. -/
lemma J_logs (hO : OpHyp P (Queue6.Hc X₀) X0m) (hy4 : 4 * X0m ≤ y) (hδ : δ ≤ 1 / 4) {z : ℝ}
    (hz : z ∈ Jint y δ) :
    Real.log y - Real.log 4 ≤ Real.log (z - Queue6.Hc X₀ z / 2) ∧
      Real.log y - Real.log 4 ≤ Real.log z := by
  obtain ⟨hz1, -⟩ := hz
  have hXm := hO.X0m_pos
  have hy0 : 0 < y := by linarith
  have hzl : y / 2 ≤ z := by nlinarith
  have hH := hO.small z (by linarith)
  have hHp := hO.pos z
  have e : Real.log y - Real.log 4 = Real.log (y / 4) := (Real.log_div hy0.ne' (by norm_num)).symm
  rw [e]
  exact ⟨Real.log_le_log (by positivity) (by linarith),
    Real.log_le_log (by positivity) (by linarith)⟩

/-- **`G1ResSec5` at the Model's bounds.** -/
noncomputable def sec5_of (hO : OpHyp P (Queue6.Hc X₀) X0m)
    (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ))
    -- the bullets of Lemma 5.34 at the Model's bounds (Model: `hK_c`, `hG_c`)
    (S Gs : ℝ → ℝ)
    (hKb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO TcL - TcL) + vtH - ν - NT)))) : ℝ → ℝ) z| ≤
        KR.RML6K.aK (CNt X₀) (S z) (Queue6.Hc X₀) z)
    (hGb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl) -
        Bo hO (Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl)))) : ℝ → ℝ) z| ≤
          35.8 * CNt X₀ * 10 * Gs z)
    -- the sizes (Model: (osc), (sw-sums), Lemma 5.20 at the Model's `SK`, `GK`/`FrBv`)
    (Sb Gb h6' : ℝ)
    (hS0 : ∀ z ∈ Jint y δ, 0 ≤ S z) (hSb : ∀ z ∈ Jint y δ, S z ≤ Sb)
    (hSb20 : Sb ≤ 1 / 10 ^ 20)
    (hG0 : ∀ z ∈ Jint y δ, 0 ≤ Gs z) (hGbd : ∀ z ∈ Jint y δ, Gs z ≤ Gb)
    (hGb41 : Gb ≤ Real.exp (-41) + 2 / 10 ^ 22)
    (h6 : ∀ z ∈ Jint y δ, 6 * Real.log y / Queue6.Hc X₀ z ≤ h6') (hh6 : h6' ≤ 5 / 10 ^ 21)
    -- the start-dependent inputs at the window heights
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ))
    (W : ∀ s, y / 4 ≤ s → s ≤ Ytop X₀ y δ → WinAt P tw X0m X₀ Tc s) :
    G1ResSec5 P tw X0m X₀ y δ ρ ν NT vtH TcL Jl Tc hO :=
  have hsz := sizes G.htnp G.hX0e G.hX0m
  have hΛ : 100000000 ≤ Real.log X₀ := hsz.2.1
  have hR := g1_range hΛ hy0 hy hδ
  have hy4 : 4 * (X₀ : ℝ) ≤ y := hR.2.2.1
  have hly : 100000000 ≤ Real.log y := by linarith [hR.2.2.2.2.2.1]
  have hCNb := CNt_bounds hΛ
  have hX0p : (0 : ℝ) < X₀ := hsz.2.2.2.2
  have hr : (X₀ : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Real.log X₀ / 100) := by
    rw [Real.rpow_def_of_pos hX0p]; ring_nf
  have hy' : Real.exp (Real.log X₀ / 100) < Real.log y := by rw [← hr]; exact hy
  have hSb0 : 0 ≤ Sb := by
    have hz : y * (1 - 2 * δ) ∈ Jint y δ :=
      ⟨le_rfl, by nlinarith [hR.2.2.2.2.1]⟩
    exact (hS0 _ hz).trans (hSb _ hz)
  have hGb0 : 0 ≤ Gb := by
    have hz : y * (1 - 2 * δ) ∈ Jint y δ :=
      ⟨le_rfl, by nlinarith [hR.2.2.2.2.1]⟩
    exact (hG0 _ hz).trans (hGbd _ hz)
  have hl4 : Real.log 4 < Real.log y := by linarith [log4_lt]
  have hYy : ∀ s, s ≤ Ytop X₀ y δ → s ≤ y := fun s hs => by
    have h1 := Ytop_le hΛ hy0 hy hδ0 hδlow
    have h2 := KR.WidthReal.Hc_pos (by norm_num; linarith : (10 : ℝ) ^ 8 ≤ Real.log X₀) y
    linarith
  { CN := CNt X₀
    hCN := hCNb.2
    SK := Sb
    SG := Gb
    h6 := h6' + (5.1 * CNt X₀ * Sb + 35.8 * CNt X₀ * 10 * Gb) *
      (Real.log 4 / (Real.log y - Real.log 4))
    hSK0 := hSb0
    hSK := hSb20
    hSG0 := hGb0
    hSG := hGb41
    hh6 := h6_le hCNb.1 hCNb.2 hSb0 hSb20 hGb0 hGb41 hh6 hly
    aK := fun z => KR.RML6K.aK (CNt X₀) (S z) (Queue6.Hc X₀) z
    bG := fun z => 35.8 * CNt X₀ * 10 * Gs z
    hKb := hKb
    hGb := hGb
    hsize := hsize_of hCNb.1 hl4 hS0 hSb hG0 hGbd
      (fun z hz => J_logs hO (by linarith [G.hX0m]) hR.2.2.2.2.1 hz)
      (fun z _ => hO.pos z) h6
    hHhalf := G.hHw
    hBRs := fun s hs1 hs2 => brs_of G hy4 hly hs1 (hYy s hs2) (W s hs1 hs2)
    Bx := BxY X₀ y
    CNE := 0
    hXBs := fun s hs1 hs2 => by
      rw [zero_div, add_zero]
      exact xbs_of G hy4 hy' hs1 (hYy s hs2) (W s hs1 hs2)
    δx := Real.exp (-60) / 800
    τ0 := 1.0001 * Real.log X₀
    hτ0 := by linarith
    hτ := le_rfl
    hδx0 := by positivity
    hδx := by linarith
    hBx := hBx_of hΛ hX0p hy' (by linarith [G.hH1]) G.hδs
    hCNE0 := le_rfl
    hCNE := (Real.exp_pos _).le }

/-- **`G1BInputs`** at a range-(B) start `y`: `KR.RML9.g1BInputs_of` with `sec5_of`. -/
noncomputable def g1BInputs_of' (hO : OpHyp P (Queue6.Hc X₀) X0m) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y)
    (M : G1ResModel P tw X0m X₀ y Z η1 η2 ε1 εW θW εS δ thrS ρ ν NT vtH TcL Jl ϑ NTpt Tc hO)
    (Q : G1ResQueue6 P tw X0m X₀ y Z η1 η2 ε1 εW θW δ thrS ρ ν ϑ)
    (B : G1ResBaseRange X₀) (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc)
    (S Gs : ℝ → ℝ)
    (hKb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO TcL - TcL) + vtH - ν - NT)))) : ℝ → ℝ) z| ≤
        KR.RML6K.aK (CNt X₀) (S z) (Queue6.Hc X₀) z)
    (hGb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl) -
        Bo hO (Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl)))) : ℝ → ℝ) z| ≤
          35.8 * CNt X₀ * 10 * Gs z)
    (Sb Gb h6' : ℝ)
    (hS0 : ∀ z ∈ Jint y δ, 0 ≤ S z) (hSb : ∀ z ∈ Jint y δ, S z ≤ Sb)
    (hSb20 : Sb ≤ 1 / 10 ^ 20)
    (hG0 : ∀ z ∈ Jint y δ, 0 ≤ Gs z) (hGbd : ∀ z ∈ Jint y δ, Gs z ≤ Gb)
    (hGb41 : Gb ≤ Real.exp (-41) + 2 / 10 ^ 22)
    (h6 : ∀ z ∈ Jint y δ, 6 * Real.log y / Queue6.Hc X₀ z ≤ h6') (hh6 : h6' ≤ 5 / 10 ^ 21)
    (W : ∀ s, y / 4 ≤ s → s ≤ Ytop X₀ y δ → WinAt P tw X0m X₀ Tc s) :
    KR.RML6.G1BInputs P tw X0m X₀ (TpR X₀ Tc) y :=
  g1BInputs_of hO hy0 hy M Q B
    (sec5_of hO G hy0 hy M.hδ0 M.hδ S Gs hKb hGb Sb Gb h6' hS0 hSb hSb20 hG0 hGbd hGb41 h6
      hh6 M.hδlow W)

end KR.RML10

end
