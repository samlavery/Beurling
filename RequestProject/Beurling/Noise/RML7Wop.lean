module

public import RequestProject.Beurling.Noise.KRTransProp
public import RequestProject.Beurling.Noise.TauNearLocNum
public import RequestProject.Beurling.Noise.TNPThread
public import RequestProject.Beurling.Noise.RML6K

/-!
# Proposition 5.18 at the localized horizon (round 7)

* `KR.prop_5_18_terminal_loc` : the third bound of Proposition 5.18 with step (iii) asked only at
  the positions `≤ x` (`EtaX0SumLoc`), as in Proposition 5.26 / Lemma 5.27.
* `KR.prop_5_18_terminal_hbs_loc` : the same under (HBS), with `NomWeights` and `TransferBound`
  discharged (`nomWeights_full`, `transferBound`).
* `KR.TNP.wop_start` : **the per-start weight bound** of the first bullet of Lemma 5.34: at a start
  `y`, for every dyadic scale `u ∈ dyScales X₀ y N`,
  `W^op_y(u) ≤ 5.1 C_N log(2u)/log y`, with Lemma 5.20 from its localized proof
  (`etaBound_energy_loc`, `energy_small_loc`; horizon `2500 ≤ Z`, `18y ≤ Z²`), the weak width bound
  `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`, `2y/X₀⁻ ≤ Z`, and `EtaX0SumLoc` at `y`. Every dyadic scale is
  `≥ X₀/4`, so the terminal-block bound applies to all of them.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- **Proposition 5.18, the third bound**, with step (iii) asked only at the positions `≤ x`. -/
theorem prop_5_18_terminal_loc {X0 ε θ lam0 CN : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hXm1 : 1 < X0m) (hCN : 0 ≤ CN)
    {Sc : Finset ℝ} {s s0 : ℝ → ℝ} (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hSc : ∀ v ∈ Sc, 1 / 2 ≤ v) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hNom : NomWeights P H tw X0m x Sc CN) (hTr : TransferBound P H tw X0m x Sc lam0 CN)
    (hX0s : EtaX0SumLoc P H X0m X0 Sc s0 x) {u : ℝ} (hu : u ∈ Sc)
    (hlog : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u)) :
    Wop P H tw X0m x u ≤ 5.1 * CN * Real.log (2 * u) / Real.log x := by
  classical
  have hXm : 0 < X0m := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc v hv]
  have hA := Aw_le hP hX0 hp2 ht hlam hx hXm1 hCN hcov hSc hEta hE hNom hTr
  have hLu : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith [hSc u hu])
  have h1 : Wop P H tw X0m x u ≤ Aw P H tw X0m x u + ∑ n ∈ NW P x u,
      (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n := by
    unfold Wop Aw
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P n).le
    exact (TVt_le_full hP hX0 hp2 n).trans (add_le_add le_rfl (SX0_le hP hX0 hp2 n))
  have h2 := (regroupX0 (tw := tw) (X0 := X0) hp2 hXm u).trans
    (cover_gen_loc (tw := tw) (by linarith) hcov hSc0 hX0s.1)
  have h3 : ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v ≤
      2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) := by
    calc ∑ v ∈ Sc, Aw P H tw X0m x v * s0 v
        ≤ ∑ v ∈ Sc, 2 * CN / Real.log x * (Real.log (2 * v) * s0 v) :=
          Finset.sum_le_sum fun v hv => by
            have := mul_le_mul_of_nonneg_right (hA v hv) (hX0s.1 v hv).1
            calc Aw P H tw X0m x v * s0 v ≤ 2 * CN * Real.log (2 * v) / Real.log x * s0 v := this
              _ = _ := by ring
      _ = 2 * CN / Real.log x * ∑ v ∈ Sc, Real.log (2 * v) * s0 v := by rw [Finset.mul_sum]
      _ ≤ 2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) :=
          mul_le_mul_of_nonneg_left hX0s.2 (by positivity)
  have h4 := hA u hu
  have h5 : 2 * CN / Real.log x * (1.52 * Real.log (2 * X0)) ≤
      2 * CN / Real.log x * (1.53 * Real.log (2 * u)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have e : 5.1 * CN * Real.log (2 * u) / Real.log x =
      2 * CN * Real.log (2 * u) / Real.log x + 2 * CN / Real.log x * (1.53 * Real.log (2 * u)) +
        0.04 * CN * Real.log (2 * u) / Real.log x := by ring
  have h6 : 0 ≤ 0.04 * CN * Real.log (2 * u) / Real.log x := by positivity
  linarith

/-- **Proposition 5.18, the terminal blocks** under (HBS), with step (iii) localized at `x`. -/
theorem prop_5_18_terminal_hbs_loc {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0s : EtaX0SumLoc P H X0m X0 Sc s0 x) {u : ℝ} (hu : u ∈ Sc)
    (hlog : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u)) :
    Wop P H tw X0m x u ≤
      5.1 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
        Real.log (2 * u) / Real.log x := by
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hCN : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0) := by
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  exact prop_5_18_terminal_loc hP hX0e hp2 ht hlam hx hX1 hCN hcov hSc1 hEta hE
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc)
    (transferBound P h hXm hP hp2 ht htv hlam hlam1 hxZ hX0 hX0m hSc1 hSc) hX0s hu hlog

end KR

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- Every dyadic scale `u = X₀2^k/4` satisfies `1.52 log(2X₀) ≤ 1.53 log(2u)` (`log X₀ ≥ 10⁸`). -/
lemma hlog_dyScales {X0 y : ℝ} {N : ℕ} (hX0 : 0 < X0) (hl : 100000000 ≤ Real.log X0) {u : ℝ}
    (hu : u ∈ dyScales X0 y N) : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u) := by
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h1 : X0 / 2 ≤ 2 * (X0 * 2 ^ k / 4) := by nlinarith
  have h2 : Real.log (X0 / 2) ≤ Real.log (2 * (X0 * 2 ^ k / 4)) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_div hX0.ne' (by norm_num)] at h2
  rw [Real.log_mul (by norm_num) hX0.ne']
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- **The per-start weight bound** (Proposition 5.18 at the localized horizon): at a start `y`,
for every dyadic scale `u`, `W^op_y(u) ≤ 5.1 C_N log(2u)/log y`. -/
theorem wop_start (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {lam0 X0 y : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y)
    (hyZ : 2 * y / X0m ≤ Z) (hZ0 : 2500 ≤ Z) (h18 : 18 * y ≤ Z ^ 2) {N K : ℕ}
    (hN : y < X0 * 2 ^ N / 4) (hK : √(2 * y) ≤ Pk X0m K) {s0 : ℝ → ℝ}
    (hX0s : EtaX0SumLoc P H X0m X0 (dyScales X0 y N) s0 y) :
    ∀ u ∈ dyScales X0 y N, Wop P H tw X0m y u ≤ 5.1 * CNt X0 * Real.log (2 * u) / Real.log y := by
  intro u hu
  obtain ⟨hX, hl, h2, h4, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hC0, hC⟩ := CNt_bounds hl
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  have hS : Sep (dyScales X0 y N) := dyScales_sep hX0
  have hS1 : ∀ v ∈ dyScales X0 y N, 1 ≤ v := fun v hv => dyScales_ge h4 hv
  have h3 : ∀ v ∈ dyScales X0 y N, 18 * v ≤ Z ^ 2 := fun v hv => by
    have := dyScales_le hv; linarith
  have h5 : ∀ v ∈ dyScales X0 y N, √(2 * v) ≤ Pk X0m K := fun v hv =>
    sqrt_le_Pk hK (dyScales_le hv)
  exact prop_5_18_terminal_hbs_loc h.hbs h.hXm h.width hX0e hp2 ht htv hlam hlam1 hy hyZ
    (by linarith) hX0m (cover_NAll hX0 hX (by linarith) hN) (fun v hv => by linarith [hS1 v hv])
    (fun v hv => dyScales_kind hX0 h2 hv) (etaBound_energy_loc h hS hS1 hZ0 h3 h5).1
    (KR.WidthReal.energy_small_loc h hH hS hS1 hZ0 h3 h5 hlam0 (by linarith) hC0 hC) hX0s hu
    (hlog_dyScales hX0 hl hu)

end KR.TNP

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **The scale-wise bounds `F̄_y(u)` on `|F_r|`** (proof of Lemma 5.34, first bullet): at each
start `y` of the window of `x`, on the windows `|t - y/n| ≤ 1.02 H(y/n)` of the levels `n` of
the dyadic scale `u`, `|F_r(t)| ≤ F̄_y(u)`, `F̄ ≥ 0`, and `∑_u log(2u) F̄_y(u) ≤ S`. The bounds
on the pieces of `F_r = (BT_c - T_c) + ϑ/H - ν - NT` (oscillation, `6/H`, `ν̄`, `54η`) are
construction facts (Model: `T'`, `NT`, `ϑ`; Queue6: `ν`, Lemma 5.22). -/
def FrScaleBound (P : BeurlingSystem) (H : ℝ → ℝ) (X0 : ℝ) (F : ℝ → ℝ) (x S : ℝ)
    (Nf : ℝ → ℕ) (Fb : ℝ → ℝ → ℝ) : Prop :=
  ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
    (∀ u ∈ dyScales X0 y (Nf y), 0 ≤ Fb y u ∧ ∀ n ∈ NW P y u, 2 ≤ n → ∀ t,
      |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |F t| ≤ Fb y u) ∧
    ∑ u ∈ dyScales X0 y (Nf y), Real.log (2 * u) * Fb y u ≤ S

/-- **Lemma 5.34, first bullet** at `x`, from Proposition 5.18 at the localized horizon
(`wop_start`) and the scale-wise bounds `FrScaleBound`: with `a(x) = aK C_N S H x`,
`log x · |B K_pt B R F(x)| ≤ a(x)`. -/
theorem hK_loc (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hO : Ops.OpHyp P H X0m) {lam0 X0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (F : Ops.LocInt)
    (hF : Ops.LBd (F : ℝ → ℝ)) (hFm : Measurable (F : ℝ → ℝ)) {x S : ℝ}
    (hx : X0m + H x / 2 ≤ x)
    (hXmZ : X0m ≤ Z)
    (hwin : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 → 2 * y / X0m ≤ Z ∧ 18 * y ≤ Z ^ 2)
    (Nf Kf : ℝ → ℕ) (hNf : ∀ y, y < X0 * 2 ^ Nf y / 4) (hKf : ∀ y, √(2 * y) ≤ Pk X0m (Kf y))
    (s0 : ℝ → ℝ → ℝ)
    (hX0s : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      EtaX0SumLoc P H X0m X0 (dyScales X0 y (Nf y)) (s0 y) y)
    (Fb : ℝ → ℝ → ℝ) (hFb : FrScaleBound P H X0 (F : ℝ → ℝ) x S Nf Fb) :
    Real.log x * |(Ops.Bo hO (Ops.Ko (tw := tw) hO (Ops.Bo hO (Ops.Ro (tw := tw) hO F))) :
      ℝ → ℝ) x| ≤ RML6K.aK (CNt X0) S H x := by
  obtain ⟨hX, hl, h2, h4, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hC0, -⟩ := CNt_bounds hl
  have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  have hx1 : 1 < x - H x / 2 := by norm_num at hXm7; linarith
  refine RML6K.hK_of_scales hO h.width ?_ F hF hFm hx1 hC0 fun y hy1 hy2 => ?_
  · intro p hp
    have := hp2 (Nat.count Nat.Prime p)
    unfold BeurlingSystem.labelVal; exact this
  obtain ⟨hyZ, h18⟩ := hwin y hy1 hy2
  have hy : X0m ≤ y := by linarith
  have hZ0 : 2500 ≤ Z := by norm_num at hXm7; linarith
  obtain ⟨hFb1, hFbS⟩ := hFb y hy1 hy2
  refine ⟨dyScales X0 y (Nf y), Fb y, cover_levels hX0 hX h2 (hNf y),
    fun u hu => (hFb1 u hu).1, fun u hu => (hFb1 u hu).2, fun u hu => ?_, fun u hu => ?_,
    hFbS⟩
  · exact wop_start h hH hX0e hX0m hp2 ht htv hlam hlam1 hy hyZ hZ0 h18 (hNf y) (hKf y)
      (hX0s y hy1 hy2) u hu
  · exact Real.log_nonneg (by linarith [dyScales_ge h4 hu])

end KR.TNP


namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **The scale-wise bounds on `G = K_pt((1-B)F_c)`** (proof of Lemma 5.34, second bullet):
at each start `y` of the window of `x`, `log y · |G(y)| ≤ A`, and on the windows of the levels of
each dyadic scale `u`, `|G| ≤ Ḡ_y(u)` with `∑_u log(2u) Ḡ_y(u) ≤ A`. In the paper both come from
`|G(z)| ≤ 3 ∑_v ω_z(v) sup_{[v,3v]} F⁺` and Lemma 5.21(iii)
(`∑_Y log(2Y) sup_{[Y,2Y)} ω_·(v) ≤ C_S' (log 3v)²`), with `A = 3 C_S' ∑_v (log 3v)² F⁺(v)`. -/
def GScaleBound (P : BeurlingSystem) (H : ℝ → ℝ) (X0 : ℝ) (G : ℝ → ℝ) (x A : ℝ)
    (Nf : ℝ → ℕ) (Gb : ℝ → ℝ → ℝ) : Prop :=
  ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
    Real.log y * |G y| ≤ A ∧
    (∀ u ∈ dyScales X0 y (Nf y), 0 ≤ Gb y u ∧ ∀ n ∈ NW P y u, 2 ≤ n → ∀ t,
      |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |G t| ≤ Gb y u) ∧
    ∑ u ∈ dyScales X0 y (Nf y), Real.log (2 * u) * Gb y u ≤ A

/-- `b(x) = (log x/log(x - H(x)/2)) (1 + 5.1 C_N) A`: with `A = 3 C_S' ∑_v (log 3v)² F⁺(v)` this
is the paper's `15.3 C_N C_S' ∑_v (log 3v)² F⁺(v)` (plus the `n = 1` term `3 C_S' ∑ …`). -/
noncomputable def bG (CN A : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log x / Real.log (x - H x / 2) * ((1 + 5.1 * CN) * A)

/-- **Lemma 5.34, second bullet** at `x`, from Proposition 5.18 at the localized horizon
(`wop_start`) and the scale-wise bounds `GScaleBound`:
`log x · |B R_res G(x)| ≤ b(x)`. -/
theorem hG_loc (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hO : Ops.OpHyp P H X0m) {lam0 X0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (G : Ops.LocInt)
    (hG : Ops.LBd (G : ℝ → ℝ)) (hGm : Measurable (G : ℝ → ℝ)) {x A : ℝ}
    (hx : X0m + H x / 2 ≤ x)
    (hXmZ : X0m ≤ Z)
    (hwin : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 → 2 * y / X0m ≤ Z ∧ 18 * y ≤ Z ^ 2)
    (Nf Kf : ℝ → ℕ) (hNf : ∀ y, y < X0 * 2 ^ Nf y / 4) (hKf : ∀ y, √(2 * y) ≤ Pk X0m (Kf y))
    (s0 : ℝ → ℝ → ℝ)
    (hX0s : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      EtaX0SumLoc P H X0m X0 (dyScales X0 y (Nf y)) (s0 y) y)
    (Gb : ℝ → ℝ → ℝ) (hGb : GScaleBound P H X0 (G : ℝ → ℝ) x A Nf Gb) :
    Real.log x * |(Ops.Bo hO (Ops.Ro (tw := tw) hO G) : ℝ → ℝ) x| ≤ bG (CNt X0) A H x := by
  obtain ⟨hX, hl, h2, h4, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hC0, -⟩ := CNt_bounds hl
  have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  have hx1 : 1 < x - H x / 2 := by norm_num at hXm7; linarith
  have hlx0 : 0 < Real.log (x - H x / 2) := Real.log_pos hx1
  have hHx := hO.pos x
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := by
    intro p _; unfold BeurlingSystem.labelVal; exact hp2 _
  refine RML6K.hG_of_start (tw := tw) hO h.width G hG hlx fun y hy1 hy2 => ?_
  obtain ⟨hyZ, h18⟩ := hwin y hy1 hy2
  have hy : X0m ≤ y := by linarith
  have hZ0 : 2500 ≤ Z := by norm_num at hXm7; linarith
  obtain ⟨hGy, hGb1, hGS⟩ := hGb y hy1 hy2
  have hly : Real.log (x - H x / 2) ≤ Real.log y := Real.log_le_log (by linarith) hy1
  have hly0 : 0 < Real.log y := lt_of_lt_of_le hlx0 hly
  have hA0 : 0 ≤ A := le_trans (mul_nonneg hly0.le (abs_nonneg _)) hGy
  have hks := RML6K.kernel_sum_le (tw := tw) h.width hval2 (cover_levels hX0 hX h2 (hNf y)) hGm
    (fun u hu => (hGb1 u hu).1) (fun u hu => (hGb1 u hu).2)
  have hW := wop_start h hH hX0e hX0m hp2 ht htv hlam hlam1 hy hyZ hZ0 h18 (hNf y) (hKf y)
    (hX0s y hy1 hy2)
  have hsum : ∑ u ∈ dyScales X0 y (Nf y), Gb y u * Wop P H tw X0m y u ≤
      5.1 * CNt X0 * A / Real.log y := by
    calc ∑ u ∈ dyScales X0 y (Nf y), Gb y u * Wop P H tw X0m y u
        ≤ ∑ u ∈ dyScales X0 y (Nf y), Gb y u * (5.1 * CNt X0 * Real.log (2 * u) / Real.log y) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hW u hu) (hGb1 u hu).1
      _ = 5.1 * CNt X0 * (∑ u ∈ dyScales X0 y (Nf y), Real.log (2 * u) * Gb y u) /
            Real.log y := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun u _ => by ring
      _ ≤ 5.1 * CNt X0 * A / Real.log y := by
          apply div_le_div_of_nonneg_right _ hly0.le
          exact mul_le_mul_of_nonneg_left hGS (by positivity)
  have hR : |Rres P H tw X0m y (G : ℝ → ℝ)| ≤ |(G : ℝ → ℝ) y| + 5.1 * CNt X0 * A / Real.log y := by
    unfold Rres
    refine (abs_add_le _ _).trans (add_le_add le_rfl (hks.trans hsum))
  have hGy' : |(G : ℝ → ℝ) y| ≤ A / Real.log y := by
    rw [le_div_iff₀ hly0, mul_comm]; exact hGy
  have hB : |Rres P H tw X0m y (G : ℝ → ℝ)| ≤ (1 + 5.1 * CNt X0) * A / Real.log y := by
    have : A / Real.log y + 5.1 * CNt X0 * A / Real.log y = (1 + 5.1 * CNt X0) * A / Real.log y :=
      by ring
    linarith
  have hBA : 0 ≤ (1 + 5.1 * CNt X0) * A := by positivity
  calc Real.log x * |Rres P H tw X0m y (G : ℝ → ℝ)|
      ≤ Real.log x * ((1 + 5.1 * CNt X0) * A / Real.log y) :=
        mul_le_mul_of_nonneg_left hB hlx
    _ ≤ Real.log x * ((1 + 5.1 * CNt X0) * A / Real.log (x - H x / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hlx
        exact div_le_div_of_nonneg_left hBA hlx0 hly
    _ = bG (CNt X0) A H x := by unfold bG; ring

end KR.TNP

end
