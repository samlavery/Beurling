module

public import RequestProject.Beurling.LocalPNT.TailT
public import RequestProject.Beurling.LocalPNT.Dirichlet
public import RequestProject.Beurling.LocalPNT.ZetaJOne
public import RequestProject.Beurling.LocalPNT.EulerJ
public import RequestProject.Beurling.LocalPNT.Stieltjes

/-!
# Step 3 of the proof of Theorem 5.24: positivity transfer

The paper compares `ζ^♯` with the Euler proxy `P_y = exp(∫_{[1,y]} u^{-s} dΠ)`. We use instead the
finite Euler product `ζ_J(s) = ∏_{p_j ≤ y} (1 - p_j^{-s})^{-1}` over the realised primes `≤ y`
(`zetaF P (P.primesLe y)`): it has the two properties used, `-ζ_J'/ζ_J` is a Dirichlet series with
non-negative coefficients `log p` at the prime powers, and `ζ_J = ∑_{n ≤ y} n^{-s} + (tail over
elements > y)` with a non-negative tail; `log ζ_J - log P_y` is the transform of a measure on
`(y, ∞)`. With `Δ = ζ^♯ - ζ_J` and `g = Δ/ζ_J`:

* `norm_Delta_le`: `|Δ(s)| ≤ y^{1-σ} ((1 + 6κσ)/(σ-1) + e^{11} log² y)` for `σ > 1`
  (`dT₀ ≥ 0` via `norm_tail_mellin_monotone_le`, the `T₀` tail `tailT_le`, and the tail of `ζ_J`);
* `zetaFR_le`: `ζ_J(σ) ≤ (1 + 2κ)/(σ - 1) + 70 + y^{1-σ} e^{11} log² y` for `1 < σ ≤ 2`;
* `norm_g_le`: `|g(s)| ≤ (log y)^{-4}` for `1 + 8 log log y/log y ≤ σ ≤ 2`.
-/

@[expose] public section

open Set Real MeasureTheory Complex Construction

namespace LocalPNT

/-- `g = (ζ^♯ - ζ_J)/ζ_J`. -/
noncomputable def gJ (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ)
    (s : ℂ) : ℂ :=
  (zetaSharp P θ X₀ α γ xp y s - zetaF P (P.primesLe y) s) / zetaF P (P.primesLe y) s

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- The tail of `ζ_J`: `ζ_J(σ) - ∑_{n ≤ y} n^{-σ} ≤ y^{1-σ} ζ_J(1)` and the complex version. -/
lemma zetaF_tail {s : ℂ} (hs : 1 ≤ s.re) :
    ‖zetaF P (P.primesLe y) s - ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)‖ ≤
      y ^ (1 - s.re) * zetaFR P (P.primesLe y) 1 ∧
    zetaFR P (P.primesLe y) s.re - ∑ e ∈ P.elems y, P.val e ^ (-s.re) ≤
      y ^ (1 - s.re) * zetaFR P (P.primesLe y) 1 := by
  classical
  set J := P.primesLe y
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hs0 : 0 < s.re := by linarith
  have hC := hasSum_zetaF P J hs0
  have hR := hasSum_zetaFR P J hs0
  have hR1 := hasSum_zetaFR P J (σ := 1) one_pos
  -- the finite part
  have hfin : ∀ e ∉ P.elems y, (if P.val e ≤ y then ((P.val e : ℝ) : ℂ) ^ (-s) else 0) = 0 := by
    intro e he; rw [if_neg]; simpa using he
  have hF : HasSum (fun e : ℕ →₀ ℕ => if P.val e ≤ y then ((P.val e : ℝ) : ℂ) ^ (-s) else 0)
      (∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)) := by
    have : HasSum (fun e : ℕ →₀ ℕ => if P.val e ≤ y then ((P.val e : ℝ) : ℂ) ^ (-s) else 0)
        (∑ e ∈ P.elems y, if P.val e ≤ y then ((P.val e : ℝ) : ℂ) ^ (-s) else 0) :=
      hasSum_sum_of_ne_finset_zero hfin
    convert this using 1
    exact Finset.sum_congr rfl fun e he => by rw [if_pos ((BeurlingSystem.mem_elems P).mp he)]
  have hFR : HasSum (fun e : ℕ →₀ ℕ => if P.val e ≤ y then P.val e ^ (-s.re) else 0)
      (∑ e ∈ P.elems y, P.val e ^ (-s.re)) := by
    have hfin' : ∀ e ∉ P.elems y, (if P.val e ≤ y then P.val e ^ (-s.re) else 0) = 0 := by
      intro e he; rw [if_neg]; simpa using he
    have : HasSum (fun e : ℕ →₀ ℕ => if P.val e ≤ y then P.val e ^ (-s.re) else 0)
        (∑ e ∈ P.elems y, if P.val e ≤ y then P.val e ^ (-s.re) else 0) :=
      hasSum_sum_of_ne_finset_zero hfin'
    convert this using 1
    exact Finset.sum_congr rfl fun e he => by rw [if_pos ((BeurlingSystem.mem_elems P).mp he)]
  -- the tails
  set tC : (ℕ →₀ ℕ) → ℂ := fun e => if e.support ⊆ J ∧ y < P.val e then
    ((P.val e : ℝ) : ℂ) ^ (-s) else 0
  set tR : (ℕ →₀ ℕ) → ℝ := fun e => if e.support ⊆ J ∧ y < P.val e then
    P.val e ^ (-s.re) else 0
  have hsplitC : ∀ e, (if e.support ⊆ J then ((P.val e : ℝ) : ℂ) ^ (-s) else 0) =
      (if P.val e ≤ y then ((P.val e : ℝ) : ℂ) ^ (-s) else 0) + tC e := by
    intro e; simp only [tC]
    by_cases hv : P.val e ≤ y
    · rw [if_pos (support_subset_primesLe P hv), if_pos hv, if_neg (by
        rintro ⟨_, h2⟩; linarith)]; ring
    · rw [if_neg hv]; push_neg at hv; by_cases hJ : e.support ⊆ J
      · rw [if_pos hJ, if_pos ⟨hJ, hv⟩]; ring
      · rw [if_neg hJ, if_neg (fun h => hJ h.1)]; ring
  have hsplitR : ∀ e, (if e.support ⊆ J then P.val e ^ (-s.re) else 0) =
      (if P.val e ≤ y then P.val e ^ (-s.re) else 0) + tR e := by
    intro e; simp only [tR]
    by_cases hv : P.val e ≤ y
    · rw [if_pos (support_subset_primesLe P hv), if_pos hv, if_neg (by
        rintro ⟨_, h2⟩; linarith)]; ring
    · rw [if_neg hv]; push_neg at hv; by_cases hJ : e.support ⊆ J
      · rw [if_pos hJ, if_pos ⟨hJ, hv⟩]; ring
      · rw [if_neg hJ, if_neg (fun h => hJ h.1)]; ring
  have htC : HasSum tC (zetaF P J s - ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)) := by
    have := hC.sub hF
    convert this using 2 with e
    rw [hsplitC e]; ring
  have htR : HasSum tR (zetaFR P J s.re - ∑ e ∈ P.elems y, P.val e ^ (-s.re)) := by
    have := hR.sub hFR
    convert this using 2 with e
    rw [hsplitR e]; ring
  -- majorant `y^{1-σ} · (term at σ = 1)`
  have hmaj : ∀ e, tR e ≤ y ^ (1 - s.re) * (if e.support ⊆ J then P.val e ^ (-(1 : ℝ)) else 0) := by
    intro e; simp only [tR]
    by_cases hc : e.support ⊆ J ∧ y < P.val e
    · rw [if_pos hc, if_pos hc.1]
      have hv0 := P.val_pos e
      have : P.val e ^ (-s.re) = P.val e ^ (1 - s.re) * P.val e ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hv0]; ring_nf
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0.le _)
      exact Real.rpow_le_rpow_of_nonpos hy0 hc.2.le (by linarith)
    · rw [if_neg hc]
      split_ifs <;> [exact mul_nonneg (Real.rpow_nonneg hy0.le _)
        (Real.rpow_nonneg (P.val_pos e).le _); simp]
  have hR1' := hR1.mul_left (y ^ (1 - s.re))
  have hRle : zetaFR P J s.re - ∑ e ∈ P.elems y, P.val e ^ (-s.re) ≤
      y ^ (1 - s.re) * zetaFR P J 1 := hasSum_le hmaj htR (by simpa using hR1')
  refine ⟨?_, hRle⟩
  -- complex: `‖tC e‖ = tR e`
  have hnorm : ∀ e, ‖tC e‖ = tR e := by
    intro e; simp only [tC, tR]
    split_ifs
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (P.val_pos e), Complex.neg_re]
    · simp
  have hsumm : Summable (fun e => ‖tC e‖) := by
    simp only [hnorm]; exact htR.summable
  rw [← htC.tsum_eq]
  calc ‖∑' e, tC e‖ ≤ ∑' e, ‖tC e‖ := norm_tsum_le_tsum_norm hsumm
    _ = zetaFR P J s.re - ∑ e ∈ P.elems y, P.val e ^ (-s.re) := by
        simp only [hnorm]; exact htR.tsum_eq
    _ ≤ _ := hRle

/-- `ζ_J(1) ≤ e^{11} log² y`. -/
lemma zetaFR_one_le : zetaFR P (P.primesLe y) 1 ≤ Real.exp 11 * Real.log y ^ (2 : ℝ) := by
  have := h.zetaJ_one_le
  simpa [zetaFR] using this

/-- **`|Δ(s)| ≤ y^{1-σ}((1 + 6κσ)/(σ-1) + e^{11} log² y)`** for `σ > 1`. -/
theorem norm_Delta_le {s : ℂ} (hs : 1 < s.re) :
    ‖zetaSharp P θ X₀ α γ xp y s - zetaF P (P.primesLe y) s‖ ≤
      y ^ (1 - s.re) * ((1 + 6 * kap X₀ * s.re) / (s.re - 1) +
        Real.exp 11 * Real.log y ^ (2 : ℝ)) := by
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  obtain ⟨-, hZ⟩ := h.zetaSharp_eq hs
  rw [hZ]
  set T := T0 θ X₀ α γ xp
  -- the `T₀` part
  have hmono : MonotoneOn T (Ici y) := fun a _ b _ hab => h.T0_monotone hab
  have hlin : ∀ x ≥ y, |T x| ≤ (1 + 3 * kap X₀) * x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith
    have h1 := h.abs_T0_sub_le (le_trans h.y_ge hx)
    have hT0 : 0 ≤ T x := by
      have := h.T0_monotone (show (0 : ℝ) ≤ x from hx0)
      have hT00 : T 0 = 0 := by simp [T, LPHyp.T0_low (show (0 : ℝ) < X₀ from h.X0_pos)]
      linarith
    rw [abs_of_nonneg hT0]
    have := (abs_le.mp h1).2; linarith
  obtain ⟨-, -, hT⟩ := norm_tail_mellin_monotone_le hy0 hmono hlin hs
  obtain ⟨-, hTT⟩ := h.tailT_le hs
  have hJ := (h.zetaF_tail hs.le).1
  have hJ1 := h.zetaFR_one_le
  have hyp : 0 ≤ y ^ (1 - s.re) := Real.rpow_nonneg hy0.le _
  have e : (∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)) +
      s * (∫ x in Ioi y, ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
        zetaF P (P.primesLe y) s =
      s * (∫ x in Ioi y, ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
        (zetaF P (P.primesLe y) s - ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)) := by ring
  rw [e]
  calc _ ≤ ‖s * (∫ x in Ioi y, ((T x - T y : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))‖ +
        ‖zetaF P (P.primesLe y) s - ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ (1 + 6 * kap X₀ * s.re) * y ^ (1 - s.re) / (s.re - 1) +
        y ^ (1 - s.re) * (Real.exp 11 * Real.log y ^ (2 : ℝ)) := by
        gcongr
        · exact hT.trans hTT
        · exact hJ.trans (mul_le_mul_of_nonneg_left hJ1 hyp)
    _ = _ := by ring

/-- **`ζ_J(σ) ≤ (1 + 2κ)/(σ-1) + 70 + y^{1-σ} e^{11} log² y`** for `1 < σ ≤ 2`. -/
theorem zetaFR_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    zetaFR P (P.primesLe y) σ ≤
      (1 + 2 * kap X₀) / (σ - 1) + 70 + y ^ (1 - σ) * (Real.exp 11 * Real.log y ^ (2 : ℝ)) := by
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have h1 := (h.zetaF_tail (s := (σ : ℂ)) (by simpa using hσ1.le)).2
  simp only [Complex.ofReal_re] at h1
  have h2 := h.sum_elems_rpow_le hσ1 hσ2
  have h3 := mul_le_mul_of_nonneg_left h.zetaFR_one_le (Real.rpow_nonneg hy0.le (1 - σ))
  linarith

lemma logy_ge : 10 ^ 8 ≤ Real.log y :=
  h.logX.trans (Real.log_le_log h.X0_pos h.y_ge)

/-- `y^{1-σ} log⁸ y ≤ 1` for `σ - 1 ≥ 8 log log y/log y`. -/
lemma rpow_mul_log_pow_le {σ : ℝ} (hσ : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ σ) :
    y ^ (1 - σ) * Real.log y ^ 8 ≤ 1 := by
  have hL := h.logy_ge
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hL0 : 0 < Real.log y := by linarith
  rw [Real.rpow_def_of_pos hy0, ← Real.exp_log (pow_pos hL0 8), ← Real.exp_add,
    Real.exp_le_one_iff, Real.log_pow]
  have : 8 * Real.log (Real.log y) ≤ (σ - 1) * Real.log y := by
    have := mul_le_mul_of_nonneg_right (show 8 * Real.log (Real.log y) / Real.log y ≤ σ - 1 by
      linarith) hL0.le
    rwa [div_mul_cancel₀ _ hL0.ne'] at this
  push_cast; nlinarith

/-- **`|g(s)| ≤ (log y)^{-4}`** for `1 + 8 log log y/log y ≤ σ ≤ 2` (Step 3, eq. lp-transfer). -/
theorem norm_g_le {s : ℂ} (hs1 : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ s.re)
    (hs2 : s.re ≤ 2) :
    ‖gJ P θ X₀ α γ xp y s‖ * Real.log y ^ 4 ≤ 1 := by
  set L := Real.log y
  have hL := h.logy_ge
  have hL0 : 0 < L := by linarith
  have hLL : 0 < Real.log L := Real.log_pos (by linarith)
  have hLL2 : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hη : 8 * Real.log L / L ≤ s.re - 1 := by linarith
  have hη0 : 0 < s.re - 1 := lt_of_lt_of_le (by positivity) hη
  have hσ : 1 < s.re := by linarith
  have hκ := kappa_pos_aux h.logX
  have hκ1 : kap X₀ ≤ 1 / 100 := (kappa_le_aux h.logX).trans (by
    rw [div_le_div_iff₀ (by nlinarith [h.logX]) (by norm_num)]; nlinarith [h.logX])
  have hinvη : 1 / (s.re - 1) ≤ L := by
    rw [div_le_iff₀ hη0]
    have : 8 * Real.log L / L * L ≤ (s.re - 1) * L := mul_le_mul_of_nonneg_right hη hL0.le
    rw [div_mul_cancel₀ _ hL0.ne'] at this
    have h1 : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
    linarith
  have hE := h.rpow_mul_log_pow_le hs1
  set E := y ^ (1 - s.re)
  have hE0 : 0 ≤ E := Real.rpow_nonneg (lt_of_lt_of_le h.X0_pos h.y_ge).le _
  have hL2 : Real.log y ^ (2 : ℝ) = L ^ 2 := by rw [Real.rpow_two]
  have hΔ := h.norm_Delta_le hσ
  have hZ := h.zetaFR_le hσ hs2
  rw [hL2] at hΔ hZ
  have he11 : Real.exp 11 ≤ 60000 := by
    have := Real.exp_one_lt_d9
    have h11 : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h11]
    calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 11
      _ ≤ 60000 := by norm_num
  -- `|Δ| ≤ E (2L + e^{11} L²)`, `ζ_J(σ) ≤ 2L`
  have hfrac : (1 + 6 * kap X₀ * s.re) / (s.re - 1) ≤ 2 * L := by
    rw [div_eq_mul_one_div]
    have : 1 + 6 * kap X₀ * s.re ≤ 2 := by nlinarith
    calc (1 + 6 * kap X₀ * s.re) * (1 / (s.re - 1)) ≤ 2 * (1 / (s.re - 1)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 2 * L := by linarith
  have hfrac2 : (1 + 2 * kap X₀) / (s.re - 1) ≤ 1.02 * L := by
    rw [div_eq_mul_one_div]
    calc (1 + 2 * kap X₀) * (1 / (s.re - 1)) ≤ 1.02 * (1 / (s.re - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1.02 * L := by linarith
  have hEL : E * L ^ 2 ≤ 1 := by
    have : E * L ^ 8 = (E * L ^ 2) * L ^ 6 := by ring
    have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    nlinarith [mul_nonneg hE0 (sq_nonneg L)]
  have hZ' : zetaFR P (P.primesLe y) s.re ≤ 2 * L := by
    have : E * (Real.exp 11 * L ^ 2) ≤ 60000 := by
      have := mul_le_mul_of_nonneg_left hEL (Real.exp_pos 11).le
      nlinarith
    linarith
  have hΔ' : ‖zetaSharp P θ X₀ α γ xp y s - zetaF P (P.primesLe y) s‖ ≤
      E * (60002 * L ^ 2) := by
    refine hΔ.trans (mul_le_mul_of_nonneg_left ?_ hE0)
    nlinarith [sq_nonneg L]
  have hinv := norm_inv_zetaF_le P (P.primesLe y) (show 0 < s.re by linarith)
  have hg : ‖gJ P θ X₀ α γ xp y s‖ ≤ E * (60002 * L ^ 2) * (2 * L) := by
    unfold gJ
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hΔ' (hinv.trans hZ') (norm_nonneg _) (by positivity)
  have hL5 : 2 * 60002 ≤ L := by linarith
  calc ‖gJ P θ X₀ α γ xp y s‖ * L ^ 4 ≤ E * (60002 * L ^ 2) * (2 * L) * L ^ 4 :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (E * L ^ 8) * (2 * 60002 / L) := by field_simp
    _ ≤ 1 * 1 := by
        apply mul_le_mul hE _ (by positivity) zero_le_one
        rw [div_le_one hL0]; exact hL5
    _ = 1 := by ring

end LPHyp

end LocalPNT

end
