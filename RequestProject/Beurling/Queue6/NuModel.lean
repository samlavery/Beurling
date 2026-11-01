module

public import RequestProject.Beurling.Queue6.RhoNoise
public import RequestProject.Beurling.Model.BtNT
public import RequestProject.Beurling.Model.FrBound

/-!
# The Model's `ν` is `B m - ρ̃` (the input of `BModel.Nu522`)

At the Model data (`ρ̃ = rhoT`, `T_c = TcR`, `NT = B NT_pt`, `ϑ = 0`), the residual of the margin
identity is exactly `ν_Model = B m - ρ̃` (`nuModel_eq`, from `Btc_eq`: `ρ̃ + ν + NT - B m =
B NT_pt`). So `Nu522` with `ϑ = 0` is the statement `|ρ̃ - B m| ≤ ν̄_i` on the blocks, which is
`rho_noise` (Lemma 5.22 at a point) where its horizon allows: `X₀ ≤ r`, `r + 2H(r) ≤ t`
(`nu522_point`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`ν_Model = B m - ρ̃`** at the Model data. -/
theorem nuModel_eq (ω : JitterΩ) (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Hc X₀) (Xm X₀)) (r : ℝ) :
    (nuRes hO (BModel.twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) :
      ℝ → ℝ) r = Margin.Bavg (Hc X₀ r) (marginM θ X₀ ω) r - rhoT θ X₀ ω r := by
  classical
  have hρ : (ρLd θ X₀ ω : ℝ → ℝ) = rhoT θ X₀ ω := by
    unfold ρLd; rw [dif_pos ⟨hc, hev⟩]; rfl
  have hT : (TcLd θ X₀ ω : ℝ → ℝ) = TcR θ X₀ ω (jzX X₀) := by
    unfold TcLd; rw [dif_pos ⟨hc, hev⟩]; rfl
  have hNT : (NTd θ X₀ ω : ℝ → ℝ) r = Margin.Bavg (Hc X₀ r) (NTpt θ X₀ ω) r := by
    unfold NTd; rw [dif_pos hO]
    have : (NTptLd θ X₀ ω : ℝ → ℝ) = NTpt θ X₀ ω := by
      unfold NTptLd; rw [dif_pos ⟨hc, hev⟩]; rfl
    show Margin.Bavg (Hc X₀ r) (NTptLd θ X₀ ω : ℝ → ℝ) r = _
    rw [this]
  have hB := Btc_eq hc hev ω hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) 0 (NTd θ X₀ ω) hρ hT r
  unfold Btc at hB
  rw [hNT] at hB
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_add] at hB
  linarith

/-- **`Nu522` at a point, with `ϑ = 0`**: a.s., on `Good(< t) ∩ NiceEv`, for `X₀ ≤ r`,
`r + 2H(r) ≤ t`: `|ν_Model(r) + 0/H(r)| ≤ ν̄(r)` for every `OpHyp`. -/
theorem nu522_point : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Hc X₀) (Xm X₀), ∀ r : ℝ,
      (X₀ : ℝ) ≤ r → r + 2 * Hc X₀ r ≤ t →
      |(nuRes hO (BModel.twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) :
        ℝ → ℝ) r + 0 / Hc X₀ r| ≤ nuB X₀ r := by
  filter_upwards [rho_noise hc hev] with ω hω
  intro t hG hN hO r hr hrt
  rw [nuModel_eq hc hev ω hO r, zero_div, add_zero, abs_sub_comm]
  exact hω t hG hN r hr hrt

end Queue6

end
