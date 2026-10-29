module

public import RequestProject.Beurling.Noise.BridgeXBG
public import RequestProject.Beurling.Noise.BridgeBR

/-!
# Lemma 5.27, Steps 1–2 at one level: the exact decomposition

For a start `x` and a level `n ≥ 2`, the true kernel `C_n` (density `gK … (phiT tw X₀⁻) n`) is
`C_n = C_n^nom + ∑_{n' ∣ n} 𝒯^nom_{n'→n} S^τ_{n'} + S^{X₀}_n` (`Etil_split`). Integrating against
`1_{[X₀, ∞)}` and using the recursions of `C_n^nom` and of the masses,

  `C_n([X₀, ∞)) - c_n 1[x/n ≥ X₀] = c_n (G(x/n) - 1[x/n ≥ X₀]) + ∑_{d ∣ n, d < n} Δ_{d→n}
     + ∫_{[X₀,∞)} ∑_{n'} 𝒯^nom_{n'→n} S^τ_{n'}`   (`level_identity`),

with the step contributions `Δ_{d→n}` (`xbStep`):

* `d = 1`: `Δ = 0` (`xbStep_one`);
* `d ≥ 2`, not `X₀`-near: `Δ = -κ_{d→n} ∫ G(·/w) d(D_w D_d)` (`xbStep_far`);
* `d ≥ 2`, `X₀`-near: `Δ = -∫ φ G(·/w) d(D_w D_d) - ∫ (φ - κ) G(·/w) Ẽ_d` (`xbStep_near`),
  where `φ = φ_{d→n}(·/w)` is the true filter; this is (level-defect) with the part of
  `S^{X₀}_n` coming from `Ẽ_d = C_d - C_d^nom` split off.

Here `D_d = C_d^nom - c_d δ_{x/d}`, `w = n/d`, and `∫ G(·/w) d(D_w D_d) =
∫ g_d(v) (G(v/w) - G(x/n)) dv` since `C_d^nom` has mass `c_d` (`nom_mass`).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

/-- `TV(D_d) = ∫ |g_d| + |c_d|` (`D_d = C_d^nom - c_d δ_{x/d}`). -/
noncomputable def TVD (d : ℕ) : ℝ :=
  (∫⁻ t, ‖gNom P H tw X0m x d t‖ₑ).toReal + |cN P tw X0m x d|

/-- `‖D_d‖_KR = ∫ |F_{D_d}|`. -/
noncomputable def KRD (d : ℕ) : ℝ :=
  (∫⁻ t, ‖cdf (gNom P H tw X0m x d) t -
    cN P tw X0m x d * stepF (posn P.labelVal x d) t‖ₑ).toReal

/-- `TV(Ẽ_d) = TV(C_d - C_d^nom)`. -/
noncomputable def TVE (d : ℕ) : ℝ :=
  (∫⁻ t, ‖Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d t‖ₑ).toReal

open scoped Classical in
/-- The contribution `Δ_{d→n}` of the step `d → n` to `C_n([X₀,∞)) - c_n 1[x/n ≥ X₀]`. -/
noncomputable def xbStep (X0 : ℝ) (d n : ℕ) : ℝ :=
  -(∫ t in Ici X0, stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d n t) -
    (if X0Near P.labelVal x H X0m d n then
      ∫ t in Ici X0, srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t
    else 0) +
    kapN tw X0m P.labelVal x d n * cN P tw X0m x d * Gs H X0 (posn P.labelVal x n)

variable {P H tw X0m x}

lemma integrable_stepK_nom (hH : WidthReg H) (d n : ℕ) :
    Integrable (stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d n) := by
  have hφ := constF_ok (kapN_mem (tw := tw) (X0m := X0m) P.labelVal x)
  have hb : ∀ d n c, |constF (kapN tw X0m P.labelVal x) d n c| ≤ 1 := fun d n c => by
    rw [abs_le]; constructor <;> linarith [(hφ d n).2 c]
  by_cases h1 : d = 1
  · have e : stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d n = fun t =>
        constF (kapN tw X0m P.labelVal x) 1 n (posn P.labelVal x n) *
          kd H (posn P.labelVal x n) t := by
      funext t; unfold stepK; rw [if_pos h1]
    rw [e]; exact (integrable_kd hH _).const_mul _
  · have e : stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d n =
        Qd H (LemmaM.valN P.labelVal (n / d)) (fun v =>
          constF (kapN tw X0m P.labelVal x) d n (v / LemmaM.valN P.labelVal (n / d)) *
            gK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d v) := by
      funext t; unfold stepK; rw [if_neg h1]
    rw [e]
    obtain ⟨hi, hm⟩ := integrable_gK (val := P.labelVal) (x := x) hH hφ d
    exact integrable_Qd hH _ (integrable_mul_comp (hφ d n).1 (hb d n) hi _)
      (measurable_mul_comp (hφ d n).1 hm _)

/-- **The exact decomposition at one level** (Lemma 5.27, Steps 1–2). -/
theorem level_identity {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) {n : ℕ} (hn : 2 ≤ n) :
    (∫ t in Ici X0, gK P.labelVal x H (phiT tw X0m) n t) -
        cN P tw X0m x n * (if X0 ≤ posn P.labelVal x n then 1 else 0) =
      cN P tw X0m x n * (Gs H X0 (posn P.labelVal x n) -
          (if X0 ≤ posn P.labelVal x n then 1 else 0)) +
        ∑ d ∈ n.properDivisors, xbStep P H tw X0m x X0 d n +
        ∫ t in Ici X0, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
          Tch P.labelVal H (kapN tw X0m P.labelVal x) n' (Stau P.labelVal x H tw X0m n') n t := by
  classical
  have hH := hP.reg
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  set κ := kapN tw X0m P.labelVal x
  set TS : ℝ → ℝ := fun t => ∑ n' ∈ n.divisors.filter (2 ≤ ·),
    Tch P.labelVal H κ n' (Stau P.labelVal x H tw X0m n') n t
  have hTS : Integrable TS := integrable_finset_sum _ fun n' _ =>
    (integrable_Tch hH _ n' (integrable_Stau hH n').1 (integrable_Stau hH n').2 n).1
  have hsrc : ∀ d, Integrable (srcStep P.labelVal x H (phiT tw X0m) κ d n) :=
    fun d => (integrable_srcStep hH d n).1
  have hstK : ∀ d, Integrable (stepK P.labelVal x H (constF κ) d n) :=
    fun d => integrable_stepK_nom hH d n
  -- the decomposition of the density
  have hdec : ∀ t, gK P.labelVal x H (phiT tw X0m) n t =
      (- ∑ d ∈ n.properDivisors, stepK P.labelVal x H (constF κ) d n t) + TS t +
        (- ∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
          srcStep P.labelVal x H (phiT tw X0m) κ d n t) := by
    intro t
    have h1 := Etil_split (tw := tw) (x := x) hP hX0e hval2 hn t
    unfold Etil at h1
    have h2 := gK_eq P.labelVal x H (φ := constF κ) hn t
    unfold SX0 SsrcP at h1
    rw [← h2]
    linarith
  have hint : ∫ t in Ici X0, gK P.labelVal x H (phiT tw X0m) n t =
      (- ∑ d ∈ n.properDivisors, ∫ t in Ici X0, stepK P.labelVal x H (constF κ) d n t) +
        (∫ t in Ici X0, TS t) -
        ∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
          ∫ t in Ici X0, srcStep P.labelVal x H (phiT tw X0m) κ d n t := by
    simp_rw [hdec]
    have hA : Integrable (fun t => - ∑ d ∈ n.properDivisors,
        stepK P.labelVal x H (constF κ) d n t) :=
      (integrable_finset_sum _ fun d _ => hstK d).neg
    have hB : Integrable (fun t => - ∑ d ∈ n.properDivisors.filter
        (fun d => X0Near P.labelVal x H X0m d n),
          srcStep P.labelVal x H (phiT tw X0m) κ d n t) :=
      (integrable_finset_sum _ fun d _ => hsrc d).neg
    have hAT : Integrable (fun t => - ∑ d ∈ n.properDivisors,
        stepK P.labelVal x H (constF κ) d n t + TS t) := hA.add hTS
    have e1 := integral_add (μ := volume.restrict (Ici X0)) hAT.integrableOn hB.integrableOn
    have e2 := integral_add (μ := volume.restrict (Ici X0)) hA.integrableOn hTS.integrableOn
    simp only at e1 e2
    rw [e1, e2, integral_neg, integral_neg,
      integral_finset_sum _ fun d _ => (hstK d).integrableOn,
      integral_finset_sum _ fun d _ => (hsrc d).integrableOn]
    ring
  have hmass := mass_eq (nomFilter P.labelVal x tw X0m) hn
  have hsum : ∑ d ∈ n.properDivisors, xbStep P H tw X0m x X0 d n =
      (- ∑ d ∈ n.properDivisors, ∫ t in Ici X0, stepK P.labelVal x H (constF κ) d n t) -
        (∑ d ∈ n.properDivisors.filter (fun d => X0Near P.labelVal x H X0m d n),
          ∫ t in Ici X0, srcStep P.labelVal x H (phiT tw X0m) κ d n t) -
        cN P tw X0m x n * Gs H X0 (posn P.labelVal x n) := by
    unfold xbStep
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_filter, ← Finset.sum_mul]
    unfold cN
    rw [hmass]
    ring
  rw [hint, hsum]
  ring

/-- `Δ_{1→n} = 0`. -/
lemma xbStep_one (X0 : ℝ) (n : ℕ) : xbStep P H tw X0m x X0 1 n = 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  unfold xbStep
  have e1 : (fun t => stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) 1 n t) =
      fun t => kapN tw X0m P.labelVal x 1 n * kd H (posn P.labelVal x n) t := by
    funext t; unfold stepK constF; rw [if_pos rfl]
  have e2 : ∀ t, srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) 1 n t = 0 :=
    srcStep_one hval n
  simp_rw [e1, e2]
  rw [integral_const_mul]
  simp only [integral_zero, ite_self, sub_zero]
  have : cN P tw X0m x 1 = 1 := mass_one _
  rw [this]
  unfold Gs
  ring

/-- The nominal step `d → n` (`d ≠ 1`) as a step on densities. -/
lemma stepK_nom_ne_one {d n : ℕ} (hd1 : d ≠ 1) :
    stepK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) d n =
      Qd H (Vl P (n / d)) (fun v => kapN tw X0m P.labelVal x d n * gNom P H tw X0m x d v) := by
  funext t; unfold stepK; rw [if_neg hd1]; rfl

/-- The source of the step `d → n` (`d ≠ 1`) as a step on densities. -/
lemma srcStep_ne_one {d n : ℕ} (hd1 : d ≠ 1) :
    srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n =
      Qd H (Vl P (n / d)) (fun v => (phiT tw X0m d n (v / Vl P (n / d)) -
        kapN tw X0m P.labelVal x d n) * gK P.labelVal x H (phiT tw X0m) d v) := by
  funext t; unfold srcStep; rw [if_neg hd1]

/-- **The step contribution off `X₀`-near steps**:
`Δ_{d→n} = -κ_{d→n} (∫ g_d G(·/w) - c_d G(x/n))`. -/
lemma xbStep_far (hH : WidthReg H) (X0 : ℝ) {d n : ℕ} (hd1 : d ≠ 1)
    (hX : ¬ X0Near P.labelVal x H X0m d n) :
    xbStep P H tw X0m x X0 d n = -(kapN tw X0m P.labelVal x d n *
      ((∫ v, gNom P H tw X0m x d v * Gs H X0 (v / Vl P (n / d))) -
        cN P tw X0m x d * Gs H X0 (posn P.labelVal x n))) := by
  classical
  obtain ⟨hgi, hgm⟩ := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hH d
  unfold xbStep
  rw [if_neg hX, stepK_nom_ne_one hd1, setIntegral_Qd hH _ _ (hgi.const_mul _)
    (measurable_const.mul hgm)]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-- **The step contribution on `X₀`-near steps**:
`Δ_{d→n} = -(∫ g_d Ψ - c_d Ψ(x/d)) - ∫ (φ - κ) G(·/w) Ẽ_d` with `Ψ = φ(·/w) G(·/w)`. -/
lemma xbStep_near (hH : WidthReg H) (X0 : ℝ) {d n : ℕ} (hdn : d ∣ n) (hn0 : n ≠ 0)
    (hd1 : d ≠ 1) (hX : X0Near P.labelVal x H X0m d n) :
    xbStep P H tw X0m x X0 d n =
      -((∫ v, gNom P H tw X0m x d v * (phiT tw X0m d n (v / Vl P (n / d)) *
          Gs H X0 (v / Vl P (n / d)))) -
        cN P tw X0m x d * (phiT tw X0m d n (posn P.labelVal x d / Vl P (n / d)) *
          Gs H X0 (posn P.labelVal x d / Vl P (n / d)))) -
      ∫ v, Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d v *
        ((phiT tw X0m d n (v / Vl P (n / d)) - kapN tw X0m P.labelVal x d n) *
          Gs H X0 (v / Vl P (n / d))) := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hφ := trueFilter_ok tw X0m
  obtain ⟨hgi, hgm⟩ := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hH d
  obtain ⟨hti, htm⟩ := integrable_gKT (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m) hH d
  set w := Vl P (n / d)
  set κ := kapN tw X0m P.labelVal x d n
  set g := gNom P H tw X0m x d
  set gT := gK P.labelVal x H (phiT tw X0m) d
  set E := Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d
  set φv : ℝ → ℝ := fun v => phiT tw X0m d n (v / w)
  set Gv : ℝ → ℝ := fun v => Gs H X0 (v / w)
  have hφm : Measurable φv := (hφ d n).1.comp (measurable_id.div_const _)
  have hφb : ∀ v, 0 ≤ φv v ∧ φv v ≤ 1 := fun v => (hφ d n).2 _
  have hGb : ∀ v, 0 ≤ Gv v ∧ Gv v ≤ 1 := fun v => Gs_mem hH X0 _
  have hpn : posn P.labelVal x d / w = posn P.labelVal x n := posn_div hval hdn hn0
  have hκ : κ = φv (posn P.labelVal x d) := by
    simp only [φv, κ, hpn]; unfold kapN; rw [nomFilter_eq_trueFilter hval]
  have hE : ∀ v, gT v = g v + E v := fun v => by simp only [E, Etil, gT, g, gNom]; ring
  -- the source integral
  have hsrcI : Integrable (fun v => (φv v - κ) * gT v) := by
    have hb : ∀ᵐ v ∂volume, ‖φv v - κ‖ ≤ 1 := Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_le]
      have := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x d n
      constructor <;> linarith [(hφb v).1, (hφb v).2]
    simpa [mul_comm] using hti.bdd_mul (c := 1) (hφm.sub measurable_const).aestronglyMeasurable hb
  have hsrcM : Measurable (fun v => (φv v - κ) * gT v) := (hφm.sub measurable_const).mul htm
  unfold xbStep
  rw [if_pos hX, stepK_nom_ne_one hd1, srcStep_ne_one hd1,
    setIntegral_Qd hH _ _ (hgi.const_mul _) (measurable_const.mul hgm),
    setIntegral_Qd hH _ _ hsrcI hsrcM]
  -- integrability of the pieces
  have hGm : Measurable Gv := by
    have : Gv = fun v => ramp ((v / w - X0) / H (v / w) + 1 / 2) := by
      funext v; exact Gs_eq_ramp hH X0 _
    rw [this]
    exact continuous_ramp.measurable.comp (((measurable_id.div_const _).sub_const _).div
      (hH.lip.continuous.measurable.comp (measurable_id.div_const _)) |>.add_const _)
  have hb1 : ∀ᵐ v ∂volume, ‖φv v * Gv v‖ ≤ 1 := Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφb v).1 (hGb v).1)]
    nlinarith [(hφb v).1, (hφb v).2, (hGb v).1, (hGb v).2]
  have hb2 : ∀ᵐ v ∂volume, ‖(φv v - κ) * Gv v‖ ≤ 1 := Filter.Eventually.of_forall fun v => by
    have := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x d n
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |φv v - κ| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(hφb v).1, (hφb v).2]
    have h2 : |Gv v| ≤ 1 := by rw [abs_of_nonneg (hGb v).1]; exact (hGb v).2
    nlinarith [abs_nonneg (φv v - κ), abs_nonneg (Gv v)]
  have hEi : Integrable E := hti.sub hgi
  have i1 : Integrable (fun v => g v * (φv v * Gv v)) := by
    simpa [mul_comm] using hgi.bdd_mul (c := 1) (hφm.mul hGm).aestronglyMeasurable hb1
  have i2 : Integrable (fun v => E v * ((φv v - κ) * Gv v)) := by
    simpa [mul_comm] using hEi.bdd_mul (c := 1)
      ((hφm.sub measurable_const).mul hGm).aestronglyMeasurable hb2
  have i3 : Integrable (fun v => g v * ((φv v - κ) * Gv v)) := by
    simpa [mul_comm] using hgi.bdd_mul (c := 1)
      ((hφm.sub measurable_const).mul hGm).aestronglyMeasurable hb2
  have e1 : (fun v => κ * g v * Gv v) = fun v => g v * (φv v * Gv v) -
      g v * ((φv v - κ) * Gv v) := by funext v; ring
  have e2 : (fun v => (φv v - κ) * gT v * Gv v) = fun v => g v * ((φv v - κ) * Gv v) +
      E v * ((φv v - κ) * Gv v) := by funext v; rw [hE]; ring
  change -(∫ v, κ * g v * Gv v) - (∫ v, (φv v - κ) * gT v * Gv v) +
    κ * cN P tw X0m x d * Gs H X0 (posn P.labelVal x n) = _
  rw [e1, e2, integral_sub i1 i3, integral_add i3 i2, ← hpn]
  change _ = -((∫ v, g v * (φv v * Gv v)) -
      cN P tw X0m x d * (φv (posn P.labelVal x d) * Gv (posn P.labelVal x d))) -
    ∫ v, E v * ((φv v - κ) * Gv v)
  rw [← hκ]
  ring

/-- **A terminal parent contributes nothing**: `Δ_{d→n} = 0` if `d` is terminal. -/
lemma xbStep_terminal {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (X1 : ℝ) {d n : ℕ} (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1)
    (hT : Terminal P.labelVal x H X0m X0 d) : xbStep P H tw X0m x X1 d n = 0 := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hXm := hP.X0m_pos
  have hHX := hP.reg.pos X0
  have hX0big : X0m / 2 ≤ X0 := by linarith
  have hsm := hP.small X0 hX0big
  have hk : kapN tw X0m P.labelVal x d n = 0 := by
    unfold kapN; rw [nomFilter_eq_trueFilter hval]
    unfold trueFilter
    rw [if_neg]
    intro h
    have hpn := posn_div (x := x) hval hdn hn0
    unfold Terminal at hT
    have hpd0 : 0 < posn P.labelVal x d := by
      have := h.2; rw [← hpn] at this
      have hw0 : (0 : ℝ) < Vl P (n / d) := by linarith
      by_contra hc; push_neg at hc
      have : posn P.labelVal x d / Vl P (n / d) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hw0.le
      linarith
    have h2 : posn P.labelVal x n ≤ posn P.labelVal x d / 2 := by
      rw [← hpn]; exact div_le_div_of_nonneg_left hpd0.le (by norm_num) hw
    linarith [h.2]
  unfold xbStep
  have hs : ∀ t, srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n t = 0 :=
    srcStep_terminal hP hX0e hp2 hd hd1 hT
  rw [stepK_nom_ne_one hd1, hk]
  simp only [zero_mul, hs, integral_zero, ite_self, sub_zero]
  unfold Qd
  simp

end KR

end
