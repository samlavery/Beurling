module

public import RequestProject.Beurling.Model.SigmaA
public import RequestProject.Beurling.Model.Choices
public import RequestProject.Beurling.Queue6.WinCount
public import RequestProject.Beurling.Queue6.Step2Count
public import RequestProject.Beurling.Noise.RML6Var
public import RequestProject.Beurling.Noise.RML6Var2Misc

/-!
# Model lemmas wiring fields of `RealMarginLoc`

* `TpCont_abs_le` : `|T'_cont| ≤ 2` (§5.1);
* `marginM_bdd` : `m` is bounded below any height (field `hmbdd`; `compDen_le`);
* `oVc`, `hoscV_c` : the canonical oscillation `o_V(t) = sup_{|h| ≤ 1.01 H(t)} |T'(t+h) - T'(t)|`
  and the field `hoscV`, from `|T_c| ≤ 2` below the horizon (`TcR_abs_le`);
* `jbc` : the canonical `j_b` of Step 6(b) (`hsum_canon`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section

variable (hc : Cond θ X₀)
include hc

/-- **`|T'_cont| ≤ 2`** (§5.1: `T'_cont = 1 - ρ_det - ρ̄_𝒜 + R'` on `[X₀, ∞)`, `0` below). -/
lemma TpCont_abs_le (ω : JitterΩ) (t : ℝ) : |TpCont θ X₀ ω t| ≤ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hκ0 := (kappa_facts hc.hX).1
  rcases lt_or_ge t (X₀ : ℝ) with hlt | hge
  · unfold TpCont; rw [if_neg (not_le.mpr hlt)]; norm_num
  · have ht0 : 0 < t := by linarith
    have hLt : 10 ^ 8 ≤ Real.log t := hc.hX.trans (Real.log_le_log (by linarith) hge)
    have hdt0 : 0 ≤ Target.rhoDet X₀ (kappaParam X₀) t := rhoDet_nonneg X₀ hκ0 ht0.le
    have hdt1 : Target.rhoDet X₀ (kappaParam X₀) t ≤ 1 + 1 / 100 :=
      (BaseRange.rhoDet_le_one_add X₀ hκ0 ht0).trans (by linarith [inv_kappa_le hc hge])
    set D := DF θ X₀ ω
    have hA1 : absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) t ≤ 1 / 100 := by
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hA0 : 0 ≤ absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) t := by
      refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) (by linarith))
      unfold absorbedBump
      split_ifs
      · by_cases hm : t ∈ Icc (uA θ a) a
        · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos ht0 _).le
        · rw [Set.indicator_of_notMem hm]
      · exact le_rfl
    have hR := abs_deriv_osc_le hc.hθ hc.hX (gammaD_range (θ := θ) hc.hX D) hge
    have hR1 : 0.02 / Real.log t ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hR2 : |deriv (Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) t| ≤
        1 / 100 := hR.trans hR1
    have hR' := abs_le.mp hR2
    unfold TpCont; rw [if_pos hge, abs_le]
    constructor <;> nlinarith [hR'.1, hR'.2]

/-- `j₀ ≤ 1`. -/
lemma jzX_le_one : jzX X₀ ≤ 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have := rhoDet_nonneg X₀ (kappa_facts hc.hX).1 hX0
  unfold jzX; linarith

/-- **`m` is bounded below any height** (field `hmbdd`): `|T'_cont| ≤ 2` and `c(y) ≤ K(B)` for
`y ≤ B` (`compDen_le`). -/
theorem marginM_bdd (hev : Even X₀) (ω : JitterΩ) (B : ℝ) :
    ∃ C, ∀ y, y ≤ B → |marginM θ X₀ ω y| ≤ C := by
  classical
  set K := 2 * ∑ w ∈ (cof_finite hc B ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  refine ⟨2 + K.toReal, fun y hy => ?_⟩
  have h1 := TpCont_abs_le hc ω y
  have h2 : (compDen θ X₀ ω y).toReal ≤ K.toReal :=
    ENNReal.toReal_mono hK (compDen_le hc hev ω hy)
  have h3 : 0 ≤ (compDen θ X₀ ω y).toReal := ENNReal.toReal_nonneg
  unfold marginM
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end

variable (θ X₀) in
/-- `T' = T_c + j₀ 1_{[X₀,∞)}` at `j₀ = jzX X₀`. -/
noncomputable def Tpc (ω : JitterΩ) (t : ℝ) : ℝ :=
  TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t

variable (θ X₀) in
/-- **The canonical oscillation** `o_V(t) = sup_{|h| ≤ 1.01 H(t)} |T_c(t+h) - T_c(t)|` (of `T_c`;
the jump at `X₀` is a separate source). -/
noncomputable def oVc (ω : JitterΩ) (t : ℝ) : ℝ :=
  Margin.RML6.supW (fun h => |TcR θ X₀ ω (jzX X₀) (t + h) - TcR θ X₀ ω (jzX X₀) t|)
    (1.01 * Queue6.Hc X₀ t)

/-- **The field `hoscV`** at `o_V = oVc`, for `t ≤ b`, below the (H_BS) horizon `Zc b`. -/
theorem hoscV_c (hc : Cond θ X₀) (hev : Even X₀) (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ}
    {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {b : ℝ} (hb0 : 0 ≤ b) (hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z) {t : ℝ} (htb : t ≤ b) {hh : ℝ}
    (hhh : |hh| ≤ 1.01 * Queue6.Hc X₀ t) :
    |TcR θ X₀ ω (jzX X₀) (t + hh) - TcR θ X₀ ω (jzX X₀) t| ≤ oVc θ X₀ ω t := by
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hmono := KR.WidthReal.Hc_mono hc.hX
  have hHt : Queue6.Hc X₀ t ≤ Queue6.Hc X₀ b := hmono htb
  have hH0 : 0 ≤ Queue6.Hc X₀ t := by unfold Queue6.Hc; exact capH_nonneg _ _
  have hbd : ∀ y, y ≤ b + 1.01 * Queue6.Hc X₀ b → |TcR θ X₀ ω (jzX X₀) y| ≤ 2 := by
    intro y hy
    have hyZ : y / Xm X₀ ≤ Z := by
      refine le_trans ?_ hZ
      rw [div_le_div_iff_of_pos_right hXm0]
      linarith [show (0 : ℝ) ≤ Queue6.Hc X₀ b by unfold Queue6.Hc; exact capH_nonneg _ _]
    exact TcR_abs_le hc hev ω hT hyZ
  unfold oVc
  refine Margin.RML6.le_supW (F := fun h => |TcR θ X₀ ω (jzX X₀) (t + h) -
    TcR θ X₀ ω (jzX X₀) t|) (C := 4) (fun h hh' => ?_) hhh
  have hh1 := (abs_le.mp hh').2
  have e1 := hbd (t + h) (by linarith)
  have e2 := hbd t (by linarith)
  exact (abs_sub _ _).trans (by linarith)

variable (θ X₀) in
/-- **The canonical `j_b`** of Step 6(b): `ρ^sh T' log t - m log t - 10⁻¹²` (`hsum_canon`; the
content is `hjb`, Proposition 5.33). -/
noncomputable def jbc (ω : JitterΩ) (t : ℝ) : ℝ :=
  rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t
      (fun s => TcR θ X₀ ω (jzX X₀) s + jzX X₀ * KR.Chain.ind X₀ s) * Real.log t -
    marginM θ X₀ ω t * Real.log t - 1 / 10 ^ 12

end BModel
