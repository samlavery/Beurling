module

public import RequestProject.Beurling.Noise.RML7XBNear
public import RequestProject.Beurling.Noise.KRVarWidth

/-!
# Proposition 5.31(i): the kernel bounds (TVD-bounds) at one start

From Theorem 5.15 (`theorem_5_15_nominal`) for the nominal kernels of the start `y`
(04x-x0band.tex, eq. (TVD-bounds)):

* `halfTVD_le` : `½ TV(D_d) ≤ |c_d| + ¼λ₀ ∑_{e ∣ d, 1<e<d} |c_e| (H_e/H_d) H_ord(d/e) e/d`;
* `KRD_le` : `‖D_d‖_KR ≤ ¼λ₀ ∑_{e ∣ d, e > 1} |c_e| H_e H_ord(d/e) e/d`;
* `Hlev_le` : `H_e ≤ V(d/e)^ε H_d` for `e ∣ d` (eq. (RH));
* `abs_cN_le` : `|c_e| ≤ μ²(e)` (Lemma 5.5).
-/

@[expose] public section

open Finset Real BeurlingSystem MeasureTheory

namespace KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- `μ²(m)` as a real number. -/
noncomputable def musqR (m : ℕ) : ℝ := ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2

lemma musqR_nonneg (m : ℕ) : 0 ≤ musqR m := by unfold musqR; positivity

/-- `|c_e| ≤ μ²(e)` (Lemma 5.5: `c_e = μ(e) χ(e) 1[y/e ≥ X₀⁻]`). -/
lemma abs_cN_le (ht : ∀ p, p.Prime → 0 < tw p) (hX : 0 ≤ X0m) (hy : X0m ≤ y) {m : ℕ}
    (hm : 1 ≤ m) : |cN P tw X0m y m| ≤ musqR m := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  unfold cN
  rw [mass_eq_moebius P.labelVal y ht hval hX hy hm]
  unfold musqR
  rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> rw [h] <;> split_ifs <;> simp

/-- **(RH) at the levels**: `H(y/e) ≤ V(d/e)^ε H(y/d)` for `e ∣ d`, `y/d ≥ X₀⁻/2`. -/
lemma Hlev_le {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {e d : ℕ} (hed : e ∣ d) (hd0 : d ≠ 0)
    (hpd : X0m / 2 ≤ posn P.labelVal y d) :
    H (posn P.labelVal y e) ≤
      LemmaM.valN P.labelVal (d / e) ^ ε * H (posn P.labelVal y d) := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  rw [posn_mul hval hed hd0]
  exact hP.RH _ _ hpd (KR.one_le_valN_label P _)

/-- **(TVD-bounds), first**: `½ TV(D_d) ≤ |c_d| + ¼λ₀ ∑_{1<e<d} |c_e| (H_e/H_d) H_ord(d/e) e/d`. -/
lemma halfTVD_le {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) {d : ℕ}
    (hd : 2 ≤ d) :
    1 / 2 * TVD P H tw X0m y d ≤ |cN P tw X0m y d| + 1 / 4 * lam0 *
      ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
          (BSCert.X0Band.Hord (d / e) : ℝ) *
            (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  obtain ⟨⟨hTV, -⟩, -⟩ := theorem_5_15_nominal (x := y) hP hval2 ht hlam hy hd
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal y
  have hle := lintegral_gK_nom_le hval hP.reg hκ hd (x := y)
  set S := ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
    |mass (nomFilter P.labelVal y tw X0m) e| *
      (Hlev P.labelVal y H e / Hlev P.labelVal y H d) * (BSCert.X0Band.Hord (d / e) : ℝ) *
        (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => by
    have h1 := hP.reg.pos (posn P.labelVal y e)
    have h2 := hP.reg.pos (posn P.labelVal y d)
    have h3 := KR.valN_labelVal_pos P e
    have h4 := KR.valN_labelVal_pos P d
    unfold Hlev; positivity
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hB : 0 ≤ |mass (nomFilter P.labelVal y tw X0m) d| + 1 / 2 * lam0 * S := by positivity
  have hI : (∫⁻ t, ‖gNom P H tw X0m y d t‖ₑ).toReal ≤
      |mass (nomFilter P.labelVal y tw X0m) d| + 1 / 2 * lam0 * S := by
    have := (hle.trans hTV)
    exact ENNReal.toReal_le_of_le_ofReal hB this
  unfold TVD
  unfold cN at hI ⊢
  linarith

/-- **(TVD-bounds), second**: `‖D_d‖_KR ≤ ¼λ₀ ∑_{e ∣ d, e > 1} |c_e| H_e H_ord(d/e) e/d`. -/
lemma KRD_le {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) {d : ℕ}
    (hd : 2 ≤ d) :
    KRD P H tw X0m y d ≤ 1 / 4 * lam0 *
      ∑ e ∈ d.divisors.filter (1 < ·), |cN P tw X0m y e| * Hlev P.labelVal y H e *
        (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  obtain ⟨⟨-, hKR⟩, -⟩ := theorem_5_15_nominal (x := y) hP hval2 ht hlam hy hd
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal y
  have hcdf := kerV_eq_cdf hval hP.reg hκ d hd (x := y)
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hS0 : 0 ≤ 1 / 4 * lam0 * ∑ e ∈ d.divisors.filter (1 < ·),
      |mass (nomFilter P.labelVal y tw X0m) e| * Hlev P.labelVal y H e *
        (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => ?_)
    have h1 := hP.reg.pos (posn P.labelVal y e)
    have h3 := KR.valN_labelVal_pos P e
    have h4 := KR.valN_labelVal_pos P d
    unfold Hlev; positivity
  have heq : KRD P H tw X0m y d =
      (KRn (DkerV P.labelVal y H (nomFilter P.labelVal y tw X0m) d)).toReal := by
    unfold KRD KRn DkerV
    rw [hcdf]
  rw [heq]
  unfold cN
  exact ENNReal.toReal_le_of_le_ofReal hS0 hKR

end KR.XB7

end
