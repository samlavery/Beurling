module

public import RequestProject.Beurling.Model.G1BRes
public import RequestProject.Beurling.Queue6.NuBlock
public import RequestProject.Beurling.Queue6.NuModel
public import RequestProject.Beurling.Queue6.Hthr
public import RequestProject.Beurling.Queue6.HthrB
public import RequestProject.Beurling.Queue6.G1BQueue6

/-!
# The Queue6 group `G1ResQueue6` of `KR.RML9.g1BInputs_of` from Queue6's lemmas

`g1ResQueue6_c` supplies `KR.RML9.G1ResQueue6` at the Model data (`ν = nuLd`, `ϑ = 0`,
`δ = deltaB`, `thrS = threshSum tJ y (2δ)`) at a range-(B) start `y ≤ b + H(b)` from:

* `tnpR` (`htnp`); `Queue6.g1B_hcount_R` (`Eloc`, `hcount`); `Queue6.hH_R` with `Hy = H(y)`,
  `K_loc = 0`; `Queue6.hthr_Zc` (Lemma 5.23 at `2δ`);
* the pointwise noise bound `|ν_Model(z)| ≤ ν̄(z)` for `z + 2H(z) ≤ b` (`Queue6.nu522_point`,
  as the hypothesis `hpt`) with `ν̄(z) ≤ ν̄_i` (`Queue6.nuB_le_nbQ`) and
  `log y · ν̄_i ≤ 10⁻²⁷` (`Queue6.log_nbQ_le`): the window `J` lies in two blocks, and
  `z + 2H(z) ≤ b` on `J` (`horJ`: `δy ≥ y^{3/4}/2`).

Lemma 5.23 at `2δ` is `Queue6.hthr_Zc` on `Good(< t)`, `b ≤ t`, with (H_BS) on `[1, Zc b]`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 1000000 in
/-- **The window `J` lies below the horizon**: `z + 2H(z) ≤ b` for `X₀ ≤ z ≤ y(1-δ)`,
`y ≤ b + H(b)`, `log y > X₀^{1/100}` (`δy ≥ y^{3/4}/2 ≥ 3y^{1/8}`). -/
lemma horJ (ω : JitterΩ) {b y : ℝ} (hb : (X₀ : ℝ) ≤ b) (hy : (X₀ : ℝ) ≤ y)
    (hyb : y ≤ b + Queue6.Hc X₀ b) (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) {z : ℝ}
    (hzX : (X₀ : ℝ) ≤ z) (hz : z ≤ y * (1 - deltaB θ X₀ ω y)) :
    z + 2 * Queue6.Hc X₀ z ≤ b := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_X0 hc
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  set Λ := Real.log X₀ with hΛ
  have hδ0 := deltaB_pos hc ω hy
  have hlow := deltaB_low hc ω hy
  obtain ⟨c0, c1⟩ := cLP_mem (Λ := Λ) (by linarith)
  have hLe : Real.exp (Λ / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hXp] at hyL
    have : Λ * (1 / 100) = Λ / 100 := by ring
    rw [this] at hyL; exact hyL.le
  have hD := (D_le hX hLe c0 c1).1
  have hX12 : (X₀ : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Λ / 2) := by
    rw [Real.rpow_def_of_pos hXp]; congr 1; ring
  rw [hX12] at hlow
  have hinv : 1 / deltaB θ X₀ ω y ≤ 2 * Real.exp (L / 4) := hlow.trans hD
  have hL3 := (D_le hX hLe c0 c1).2
  have hL20 : 20 ≤ L := by linarith
  -- `δy ≥ e^{3L/4}/2`
  have hy : y = Real.exp L := (Real.exp_log hy0).symm
  have hδy : Real.exp (3 * L / 4) / 2 ≤ deltaB θ X₀ ω y * y := by
    have h1 : 1 ≤ 2 * Real.exp (L / 4) * deltaB θ X₀ ω y := by
      rwa [div_le_iff₀ hδ0] at hinv
    have e : Real.exp (3 * L / 4) * Real.exp (L / 4) = y := by
      rw [hy, ← Real.exp_add]; ring_nf
    have hE := Real.exp_pos (L / 4)
    have hE3 := Real.exp_pos (3 * L / 4)
    nlinarith [mul_le_mul_of_nonneg_left h1 hE3.le]
  -- `H(z) ≤ y^{1/8}`, `H(b) ≤ y^{1/8}` if `b < y`
  have hzy : z ≤ y := by nlinarith
  have h18 : ∀ w, (X₀ : ℝ) ≤ w → w ≤ y → Queue6.Hc X₀ w ≤ Real.exp (L / 8) := by
    intro w hw hwy
    unfold Queue6.Hc; rw [max_eq_left hw]
    refine (InitialRange.capH_le_rpow hX0 hX hw).trans ?_
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by
      have := Real.log_le_log (by linarith) hwy; nlinarith)
  have hHz := h18 z hzX hzy
  have hgap : 3 * Real.exp (L / 8) ≤ Real.exp (3 * L / 4) / 2 := by
    have : Real.exp (3 * L / 4) = Real.exp (L / 8) * Real.exp (5 * L / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have h6 : (6 : ℝ) ≤ Real.exp (5 * L / 8) := by
      have := Real.add_one_le_exp (5 * L / 8); linarith
    have := Real.exp_pos (L / 8)
    nlinarith
  rcases le_total y b with h | h
  · nlinarith
  · have hHb := h18 b hb h
    nlinarith

variable (hev : Even X₀)
include hev

set_option maxHeartbeats 2000000 in
/-- **The Queue6 group of `KR.RML9.g1BInputs_of`** at a range-(B) start `y`, on
`Good(< t) ∩ NiceEv` with `b ≤ t`, from the pointwise noise bound `hpt` (`Queue6.nu522_point`
at time `b`). -/
noncomputable def g1ResQueue6_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (hpt : ∀ r : ℝ, (X₀ : ℝ) ≤ r → r + 2 * Queue6.Hc X₀ r ≤ b →
      |(nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) :
        ℝ → ℝ) r + 0 / Queue6.Hc X₀ r| ≤ nuB X₀ r)
    {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    KR.RML9.G1ResQueue6 (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ y (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) epsH (epsH / 10) (deltaB θ X₀ ω y)
      ((PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y)) (ρLd θ X₀ ω)
      (nuLd θ X₀ ω) (fun _ => 0) :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hR := KR.RML9.g1_range (by norm_num at hX ⊢; linarith) (y_pos_c hc hy) hyL
    (deltaB_le (θ := θ) ω y)
  have hblk := exists_blk hXm (y / 2)
  let i0 := Classical.choose hblk
  have hi0 : InBlk X₀ i0 (y / 2) := (Classical.choose_spec hblk).1
  have hcnt := g1B_hcount_R hc hev hN hy hyL
  have hHR := hH_R hc hy
  { htnp := tnpR hc hev hbs hN.2.1 hX1
    Eloc := Queue6.Eloc X₀ (y * (1 - deltaB θ X₀ ω y))
    hE0 := hcnt.1
    hE := hcnt.2.1
    hcount := by rw [ρLd_coe hc hev ω]; exact hcnt.2.2
    nb := max (nbQ X₀ i0) (nbQ X₀ (i0 + 1))
    hν := by
      intro z hz
      obtain ⟨hX0p, -, hy4, -, hδ4, -, -⟩ := hR
      have hδ0 := deltaB_pos hc ω hy
      have hXmX := Xm_le_X0 hc
      have hz1 : y / 2 ≤ z := by nlinarith [hz.1]
      have hz2 : z ≤ y := by nlinarith [hz.2]
      have hzX : (X₀ : ℝ) ≤ z := by linarith
      have hp := hpt z hzX (horJ hc ω hb hy hyb hyL hzX hz.2)
      rw [zero_div, add_zero, ← nuLd_eq ω hO] at hp
      have hv0 : Xm X₀ * 2 ^ i0 ≤ y / 2 := by
        rcases hi0.2 with h | h
        · have h2 := hi0.1; rw [h] at h2 ⊢; simp at h2 ⊢; linarith
        · exact h
      rcases lt_or_ge z (2 * (Xm X₀ * 2 ^ i0)) with h | h
      · have := nuB_le_nbQ hc (by linarith) (⟨h, Or.inr (by linarith)⟩ : InBlk X₀ i0 z)
        exact hp.trans (this.trans (le_max_left _ _))
      · have e : Xm X₀ * 2 ^ (i0 + 1) = 2 * (Xm X₀ * 2 ^ i0) := by ring
        have := nuB_le_nbQ hc (by linarith)
          (⟨by rw [e]; linarith [hi0.1], Or.inr (by rw [e]; exact h)⟩ : InBlk X₀ (i0 + 1) z)
        exact hp.trans (this.trans (le_max_right _ _))
    hnb := by
      have hy0 := y_pos_c hc hy
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith [one_lt_X0 hc])
      have e : Real.log y * max (nbQ X₀ i0) (nbQ X₀ (i0 + 1)) =
          max (Real.log y * nbQ X₀ i0) (Real.log y * nbQ X₀ (i0 + 1)) :=
        mul_max_of_nonneg _ _ hl0
      rw [e]
      have h1 : y ≤ 16 * (Xm X₀ * 2 ^ i0) := by nlinarith [hi0.1]
      have h2 : y ≤ 16 * (Xm X₀ * 2 ^ (i0 + 1)) := by
        have : Xm X₀ * 2 ^ (i0 + 1) = 2 * (Xm X₀ * 2 ^ i0) := by ring
        rw [this]; nlinarith [hi0.1]
      exact max_le (log_nbQ_le hc hy0.le h1) (log_nbQ_le hc hy0.le h2)
    hϑ := fun _ _ => by simp
    Hy := Queue6.Hc X₀ y
    Kloc := 0
    hthr := hthr_Zc hc hev (e3Family θ X₀) hG hN hb hbt hbs hy hyb hyL
    hH1 := hHR.1
    hH := hHR.2.1
    hK0 := hHR.2.2.1
    hK := hHR.2.2.2 }

end BModel

end
