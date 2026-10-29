module

public import RequestProject.Beurling.Model.MarginSteps
public import RequestProject.Beurling.Model.MarginTail


/-!
# The bound `m*` of the margin density near the strips (input of `RML10.hS2sp_10`,
`hS2sm_10`)

`Mm θ X₀ ω b = 2 + c̄(2b)` with `c̄(β) = 2 ∑_{w ≤ β/X₀⁻} w⁻¹` (`compDen_le`): `|m| ≤ Mm` below
`2b` (`|T'_cont| ≤ 2`, `0 ≤ c ≤ c̄`), and `m` is integrable on bounded intervals
(`marginM_ii`). `hm10` is the input `hm` of `hS2sp_10`/`hS2sm_10`: integrability and
`|m| ≤ Mm` on `[z - 3H(z), z + 3H(z)]` at every strip point `z` (`z ≤ b`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

open Classical in
variable (θ X₀) in
/-- `m* = 2 + 2 ∑_{w ≤ 2b/X₀⁻} w⁻¹`. -/
noncomputable def Mm (ω : JitterΩ) (b : ℝ) : ℝ :=
  if hc : Cond θ X₀ then
    2 + (2 * ∑ w ∈ (cof_finite hc (2 * b) ω).toFinset,
      ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹).toReal
  else 2

variable (hc : Cond θ X₀)
include hc

lemma Mm_nonneg (ω : JitterΩ) (b : ℝ) : 0 ≤ Mm θ X₀ ω b := by
  unfold Mm; rw [dif_pos hc]; positivity

/-- `|m| ≤ m*` below `2b`. -/
lemma abs_marginM_le (hev : Even X₀) (ω : JitterΩ) {b x : ℝ} (hx : x ≤ 2 * b) :
    |marginM θ X₀ ω x| ≤ Mm θ X₀ ω b := by
  set K := 2 * ∑ w ∈ (cof_finite hc (2 * b) ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  have h1 : (compDen θ X₀ ω x).toReal ≤ K.toReal :=
    ENNReal.toReal_mono hK (compDen_le hc hev ω hx)
  have h0 : 0 ≤ (compDen θ X₀ ω x).toReal := ENNReal.toReal_nonneg
  have hT := abs_le.mp (TpCont_abs_le hc ω x)
  unfold Mm; rw [dif_pos hc]
  unfold marginM
  rw [abs_le]; constructor <;> linarith [hT.1, hT.2]

/-- A strip point lies below `b`. -/
lemma S2Rng_le {ω : JitterΩ} {p : Margin.Rec.CP} {T0 b z : ℝ} (hT0 : 0 ≤ T0)
    (hz : S2Rng θ X₀ ω p T0 b z) : z ≤ b := by
  obtain ⟨t, ht0, htb, w, -, -, hz2⟩ := hz
  have hV : 1 ≤ KR.Vl (PR θ X₀ ω) w :=
    LemmaM.one_le_valN _ (fun r _ => (PR θ X₀ ω).one_le_labelVal r)
  have : t / KR.Vl (PR θ X₀ ω) w ≤ t := div_le_self (by linarith) hV
  linarith

/-- **The input `hm` of `RML10.hS2sp_10`, `hS2sm_10`** at `M = m*`. -/
theorem hm10 (hev : Even X₀) (ω : JitterΩ) (ES jP b : ℝ) (hb : (X₀ : ℝ) ≤ b) :
    ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z →
      IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z),
        |marginM θ X₀ ω x| ≤ Mm θ X₀ ω b := by
  intro z hz
  have hX := hc.hX
  have hT0 : 0 ≤ (RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc := by
    have := hT0'_c hc ES jP (b := b) _ le_rfl (hT0T_c hc ES jP hb)
    exact this.1
  have hzb := S2Rng_le hc hT0 hz
  have hH := KR.WidthReal.Hc_pos hX (X₀ := X₀) z
  have hHb : Queue6.Hc X₀ z ≤ b / 40 := by
    unfold Queue6.Hc
    have h1 := KR.WidthReal.capH_le_tenth hX (le_max_right z (X₀ : ℝ))
    have h2 : max z (X₀ : ℝ) ≤ b := max_le hzb hb
    linarith
  have hle : z - 3 * Queue6.Hc X₀ z ≤ z + 3 * Queue6.Hc X₀ z := by linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp
    (marginM_ii hc hev ω hle), fun x hx => abs_marginM_le hc hev ω ?_⟩
  have := hx.2
  have hb0 : (0 : ℝ) ≤ b := le_trans (Nat.cast_nonneg _) hb
  linarith

end BModel

end
