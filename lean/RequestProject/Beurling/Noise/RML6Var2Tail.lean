module

public import RequestProject.Beurling.Noise.RML6Var2Head

/-!
# Proposition 5.38, Step 5: Rankin's tail (field `htail`)

`htail_loc` : for `ε' ≤ 0.045`, `Kc ≥ 0`, `X₀⁻/2 ≤ c_∞`, `log t ≥ 10⁸` and `2t/X₀⁻ ≤ Z`,

  `∑_{M : c(M) ≤ t/M, M > √t} Aw(M) E_S/log(t/M) ≤ 0.06 E_S/log t`

(the levels of `NAll P t (X₀⁻/2)`). The paper uses Rankin's trick at `s = 1.75`; we use
`s = 1.8`, which `𝒩` controls by `∑ H_ord(m) m^{-1.8} ≤ 7.55` (`hord_18_le`):
`M^{ε'-2} ≤ M^{-1.8} (√t)^{-0.155}` for `M > √t`, and `log(t/M) ≥ log(X₀⁻/2)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR

variable (P : BeurlingSystem)

/-- `∑_{m ∈ s} H_ord(m) m^{-1.8} ≤ 7.55` for any finite set of elements `m ≥ 2` of value
`≤ B ≤ Z` (the divisor closure of `s` and `hord_18_le`). -/
theorem hord18_set {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {B : ℝ} (hB : B ≤ Z)
    (s : Finset ℕ) (hs : ∀ m ∈ s, 2 ≤ m ∧ LemmaM.valN P.labelVal m ≤ B) :
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (-(1.8 : ℝ)) ≤ 7.55 := by
  set V := LemmaM.valN P.labelVal
  have hV1 : ∀ m, 1 ≤ V m := KR.one_le_valN_label P
  set S := s.biUnion Nat.divisors
  have hs0 : ∀ m ∈ s, m ≠ 0 := fun m hm => by have := (hs m hm).1; omega
  have hdiv : ∀ m ∈ S, ∀ d, d ∣ m → d ∈ S := by
    intro m hm d hd
    obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨m', hm', Nat.mem_divisors.mpr
      ⟨dvd_trans hd (Nat.mem_divisors.mp hmm').1, hs0 m' hm'⟩⟩
  have h0 : 0 ∉ S := by
    intro h0
    obtain ⟨m', -, hm⟩ := Finset.mem_biUnion.mp h0
    simp at hm
  have hSB : ∀ m ∈ S, V m ≤ B := by
    intro m hm
    obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp hm
    exact (KR.valN_dvd_le P (Nat.mem_divisors.mp hmm').1 (hs0 m' hm')).trans (hs m' hm').2
  have hsS : s ⊆ S.filter (2 ≤ ·) := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨m, hm,
      Nat.mem_divisors.mpr ⟨dvd_rfl, hs0 m hm⟩⟩, (hs m hm).1⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsS
    (fun m _ _ => by have := hV1 m; positivity)) (hord_18_le P h hXm hB S hdiv h0 hSB)

/-- `L e^{-cL} ≤ 2/(c² L)` for `c, L > 0`. -/
lemma mul_exp_neg_le {c L : ℝ} (hc : 0 < c) (hL : 0 < L) :
    L * Real.exp (-(c * L)) ≤ 2 / (c ^ 2 * L) := by
  have h1 : 1 + c * L + (c * L) ^ 2 / 2 ≤ Real.exp (c * L) := by
    have := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ c * L); linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith [mul_pos hc hL, sq_nonneg (c * L)]

end KR

namespace Margin.Rec

/-- **The field `htail`** (Step 5, Rankin's tail): see the module docstring. -/
theorem htail_loc {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (P : BeurlingSystem)
    (h : P.HBS X0m Z η1 η2 ε1) (hXm : 100000000 ≤ Real.log X0m) (p : CP) (hpXm : p.Xm = X0m)
    (hε' : p.ε' ≤ 0.045) (hKc : 0 ≤ p.Kc) (hcinf : p.Xm / 2 ≤ p.cinf) (hES : 0 ≤ p.ES)
    {t : ℝ} (ht0 : 0 < t) (ht : 100000000 ≤ Real.log t) (hZ : 2 * t / X0m ≤ Z) :
    ∑ M ∈ ((KR.NAll P t (p.Xm / 2)).filter (fun M =>
        cutL P p M ≤ t / Vv P M)).filter (fun M => ¬ Vv P M ≤ √t),
      Aw P p M * (p.ES / Real.log (t / Vv P M)) ≤ 0.06 * p.ES / Real.log t := by
  have hX := h.X0m_pos
  have hXm2 : 1 ≤ Real.log (X0m / 2) := by
    rw [Real.log_div hX.ne' (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  set Lt := Real.log t
  have hLt0 : 0 < Lt := by linarith
  set S := ((KR.NAll P t (p.Xm / 2)).filter (fun M =>
        cutL P p M ≤ t / Vv P M)).filter (fun M => ¬ Vv P M ≤ √t)
  have hmem : ∀ M ∈ S, 2 ≤ M ∧ LemmaM.valN P.labelVal M ≤ 2 * t / X0m ∧
      p.Xm / 2 ≤ t / Vv P M ∧ √t < Vv P M := by
    intro M hM
    obtain ⟨hM1, hM3⟩ := Finset.mem_filter.mp hM
    obtain ⟨hM0, hM2⟩ := Finset.mem_filter.mp hM1
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hM0
    have hval : LemmaM.valN P.labelVal (iota e) ≤ 2 * t / X0m := by
      rw [mem_elems, hpXm] at he
      rw [P.valN_iota]
      calc P.val e ≤ t / (X0m / 2) := he
        _ = 2 * t / X0m := by field_simp
    have hlt : √t < Vv P (iota e) := not_le.mp hM3
    refine ⟨?_, hval, ?_, hlt⟩
    · by_contra hc; push_neg at hc
      have h1 : iota e = 1 := by have := iota_pos e; omega
      have hst : 1 ≤ √t := by
        rw [Real.one_le_sqrt]
        by_contra hc'; push_neg at hc'
        have := Real.log_lt_log ht0 hc'; rw [Real.log_one] at this; linarith
      rw [h1, Vv_one] at hlt; linarith
    · have : p.cinf ≤ cutL P p (iota e) := by
        unfold cutL
        have := Real.rpow_nonneg (Vv_pos (P := P) (iota e)).le (p.ε - 1)
        nlinarith
      linarith
  -- pointwise bound
  have hsq0 : 0 < √t := Real.sqrt_pos.mpr ht0
  have hpt : ∀ M ∈ S, Aw P p M * (p.ES / Real.log (t / Vv P M)) ≤
      ((BSCert.X0Band.Hord M : ℝ) * LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ))) *
        (√t ^ (-(0.155 : ℝ)) * p.ES) := by
    intro M hM
    obtain ⟨hM2, -, hcut, hlt⟩ := hmem M hM
    have hV := Vv_pos (P := P) M
    have hV1 : 1 ≤ Vv P M := KR.one_le_valN_label P M
    have hAw : Aw P p M ≤ (BSCert.X0Band.Hord M : ℝ) * LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ)) *
        √t ^ (-(0.155 : ℝ)) := by
      unfold Aw
      have e1 : Vv P M ^ (-(1.955 : ℝ)) = Vv P M ^ (-(1.8 : ℝ)) * Vv P M ^ (-(0.155 : ℝ)) := by
        rw [← Real.rpow_add hV]; norm_num
      have h1 : Vv P M ^ (p.ε' - 2) ≤ Vv P M ^ (-(1.955 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hV1 (by linarith)
      have h2 : Vv P M ^ (-(0.155 : ℝ)) ≤ √t ^ (-(0.155 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hsq0 hlt.le (by norm_num)
      have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord M : ℝ) := by positivity
      calc (BSCert.X0Band.Hord M : ℝ) * Vv P M ^ (p.ε' - 2)
          ≤ (BSCert.X0Band.Hord M : ℝ) * (Vv P M ^ (-(1.8 : ℝ)) * Vv P M ^ (-(0.155 : ℝ))) := by
            rw [← e1]; exact mul_le_mul_of_nonneg_left h1 hH
        _ ≤ (BSCert.X0Band.Hord M : ℝ) * (Vv P M ^ (-(1.8 : ℝ)) * √t ^ (-(0.155 : ℝ))) := by
            gcongr
        _ = _ := by ring
    have hlog : 1 ≤ Real.log (t / Vv P M) := by
      refine hXm2.trans (Real.log_le_log (by positivity) ?_)
      rw [← hpXm]; exact hcut
    have hq : p.ES / Real.log (t / Vv P M) ≤ p.ES := div_le_self hES hlog
    have hq0 : 0 ≤ p.ES / Real.log (t / Vv P M) := div_nonneg hES (by linarith)
    calc Aw P p M * (p.ES / Real.log (t / Vv P M))
        ≤ ((BSCert.X0Band.Hord M : ℝ) * LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ)) *
            √t ^ (-(0.155 : ℝ))) * p.ES :=
          mul_le_mul hAw hq hq0 (by positivity)
      _ = _ := by ring
  have hsum := KR.hord18_set P h hXm hZ S (fun M hM => ⟨(hmem M hM).1, (hmem M hM).2.1⟩)
  -- `(√t)^{-0.155} = e^{-0.0775 L}` is tiny against `1/L`
  have hrp : √t ^ (-(0.155 : ℝ)) = Real.exp (-(0.0775 * Lt)) := by
    rw [Real.rpow_def_of_pos hsq0, Real.log_sqrt ht0.le]; congr 1; ring
  have hsmall : 7.55 * (Lt * √t ^ (-(0.155 : ℝ))) ≤ 0.06 := by
    rw [hrp]
    have := KR.mul_exp_neg_le (c := 0.0775) (by norm_num) hLt0
    have h2 : 2 / (0.0775 ^ 2 * Lt) ≤ 2 / (0.0775 ^ 2 * 100000000) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have h3 : (2 : ℝ) / (0.0775 ^ 2 * 100000000) ≤ 0.001 := by norm_num
    nlinarith
  have hp0 : 0 ≤ √t ^ (-(0.155 : ℝ)) := by positivity
  calc ∑ M ∈ S, Aw P p M * (p.ES / Real.log (t / Vv P M))
      ≤ ∑ M ∈ S, ((BSCert.X0Band.Hord M : ℝ) * LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ))) *
          (√t ^ (-(0.155 : ℝ)) * p.ES) := Finset.sum_le_sum hpt
    _ = (∑ M ∈ S, (BSCert.X0Band.Hord M : ℝ) * LemmaM.valN P.labelVal M ^ (-(1.8 : ℝ))) *
          (√t ^ (-(0.155 : ℝ)) * p.ES) := by rw [Finset.sum_mul]
    _ ≤ 7.55 * (√t ^ (-(0.155 : ℝ)) * p.ES) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ 0.06 * p.ES / Lt := by
        rw [le_div_iff₀ hLt0]
        have : 7.55 * (√t ^ (-(0.155 : ℝ)) * p.ES) * Lt =
            (7.55 * (Lt * √t ^ (-(0.155 : ℝ)))) * p.ES := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hsmall hES

end Margin.Rec

end
