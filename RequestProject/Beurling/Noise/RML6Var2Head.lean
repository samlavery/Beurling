module

public import RequestProject.Beurling.Noise.KRHord
public import RequestProject.Beurling.Noise.MarginVarCert
public import RequestProject.Beurling.Noise.MarginChainLoc

/-!
# Proposition 5.38, Step 5: the head sum `A₀(0.045)` for `𝒩` (field `hhead`)

The field `hhead` of `BModel.RealMarginLoc` asks `∑_{V(M) ≤ √t} Aw(M) ≤ 1 + A₀(0.045)` with the
exact value `A₀(0.045) = ordA 1.955` of the series for `ℕ`. Over `𝒩` this has no slack: the
elements of value `≥ X₀⁻` add positive terms. What holds (`hordA0_1955`, as `hordSumsB` for
`0.03`) is

  `∑_{m ∈ s} H_ord(m) m^{ε'-2} ≤ 2.2181`   (`ε' ≤ 0.045`, elements `2 ≤ m` of value `≤ B ≤ Z`),

from `ordA 1.955 ≤ 2.218` (`MarginVarCert`) and the tail `X₀⁻^{-0.155} · 7.55`. With it:

* `hhead_loc` : the corrected head bound `∑_{V(M) ≤ √t} Aw(M) ≤ 1 + 2.2181` for the levels of
  `NAll P t (X₀⁻/2)`, `2t/X₀⁻ ≤ Z`;
* `hv_of_chain'` : Step 5 (`KR.Chain.hv_of_chain`) with this bound; the constant `6.5` is
  unchanged (`2(1 + 2.2181) + 0.06 = 6.4962`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR

variable (P : BeurlingSystem)

lemma zeta1955_lt_two : BSCert.Consts.zetaR 1.955 < 2 :=
  lt_of_le_of_lt (BSCert.Consts.zetaR_strictAntiOn.antitoneOn (show (1 : ℝ) < 1.8 by norm_num)
    (show (1 : ℝ) < 1.955 by norm_num) (by norm_num)) BSCert.Consts.zeta_18_lt_two

lemma summable_hord1955 :
    Summable fun m : ℕ => if 2 ≤ m then (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.955 : ℝ))
      else 0 := by
  have hs := (BSCert.Consts.hasSum_Hord (s := 1.955) (by norm_num) zeta1955_lt_two).summable
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hs
  · split_ifs <;> positivity
  · split_ifs
    · exact le_of_eq (by norm_num)
    · positivity

/-- **`A₀(ε')` for `𝒩`, `ε' ≤ 0.045`**: `∑_{m ∈ s} H_ord(m) m^{ε'-2} ≤ 2.2181` for every finite
set of elements `m ≥ 2` of value `≤ B ≤ Z`. -/
theorem hordA0_1955 {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε : ℝ} (hε : ε ≤ 0.045) {B : ℝ} (hB : B ≤ Z)
    (s : Finset ℕ) (hs : ∀ m ∈ s, 2 ≤ m ∧ LemmaM.valN P.labelVal m ≤ B) :
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (ε - 2) ≤ 2.2181 := by
  set V := LemmaM.valN P.labelVal
  have hV1 : ∀ m, 1 ≤ V m := KR.one_le_valN_label P
  have hX := h.X0m_pos
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  set S := s.biUnion Nat.divisors
  have hs0 : ∀ m ∈ s, m ≠ 0 := fun m hm => by have := (hs m hm).1; omega
  have hdiv : ∀ m ∈ S, ∀ d, d ∣ m → d ∈ S := by
    intro m hm d hd
    obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp hm
    have hm'0 := hs0 m' hm'
    exact Finset.mem_biUnion.mpr ⟨m', hm', Nat.mem_divisors.mpr
      ⟨dvd_trans hd (Nat.mem_divisors.mp hmm').1, hm'0⟩⟩
  have h0 : 0 ∉ S := by
    intro h0
    obtain ⟨m', -, hm⟩ := Finset.mem_biUnion.mp h0
    simp at hm
  have hSB : ∀ m ∈ S, V m ≤ B := by
    intro m hm
    obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp hm
    exact (KR.valN_dvd_le P (Nat.mem_divisors.mp hmm').1 (hs0 m' hm')).trans (hs m' hm').2
  have h18 := hord_18_le P h hXm hB S hdiv h0 hSB
  have hsS : s ⊆ S.filter (2 ≤ ·) := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨m, hm,
      Nat.mem_divisors.mpr ⟨dvd_rfl, hs0 m hm⟩⟩, (hs m hm).1⟩
  set F18 : ℕ → ℝ := fun m => (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.8 : ℝ))
  have hF18 : ∑ m ∈ s.filter (fun m => ¬ V m < X0m), F18 m ≤ 7.55 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      ((Finset.filter_subset _ _).trans hsS)
      (fun m _ _ => by have := hV1 m; simp only [F18]; positivity)) h18
  -- `X₀⁻^{-0.155}` is tiny
  have htiny : X0m ^ (-(0.155 : ℝ)) ≤ 1 / 10 ^ 20 := by
    have h1 := rpow_neg_le hX1 (by norm_num : (0 : ℝ) < 0.155)
    have h2 : (15500000 : ℝ) ≤ 0.155 * Real.log X0m := by nlinarith
    have h3 : (15500000 : ℝ) ^ 5 ≤ (0.155 * Real.log X0m) ^ 5 :=
      pow_le_pow_left₀ (by norm_num) h2 5
    have h4 : 120 / (0.155 * Real.log X0m) ^ 5 ≤ 120 / (15500000 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
    have h5 : 120 / (15500000 : ℝ) ^ 5 ≤ 1 / 10 ^ 20 := by norm_num
    linarith
  have hlow : ∀ m ∈ s.filter (fun m => V m < X0m), V m = m := by
    intro m hm
    obtain ⟨hms, hlt⟩ := Finset.mem_filter.mp hm
    exact valN_eq_self P h (hs0 m hms) hlt ((hs m hms).2.trans hB)
  have hexp : ∀ m, V m ^ (ε - 2) ≤ V m ^ (-(1.955 : ℝ)) := fun m =>
    Real.rpow_le_rpow_of_exponent_le (hV1 m) (by linarith)
  have hhi1 : ∀ m ∈ s.filter (fun m => ¬ V m < X0m),
      (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) ≤ X0m ^ (-(0.155 : ℝ)) * F18 m := by
    intro m hm
    have hXV : X0m ≤ V m := not_lt.mp (Finset.mem_filter.mp hm).2
    have hV0 : 0 < V m := by linarith [hV1 m]
    have e : V m ^ (-(1.955 : ℝ)) = V m ^ (-(0.155 : ℝ)) * V m ^ (-(1.8 : ℝ)) := by
      rw [← Real.rpow_add hV0]; norm_num
    have h2 : V m ^ (-(0.155 : ℝ)) ≤ X0m ^ (-(0.155 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hX hXV (by norm_num)
    have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) := by positivity
    have h18' : (0 : ℝ) ≤ V m ^ (-(1.8 : ℝ)) := by positivity
    calc (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)
        ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.955 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hexp m) hH
      _ ≤ (BSCert.X0Band.Hord m : ℝ) * (X0m ^ (-(0.155 : ℝ)) * V m ^ (-(1.8 : ℝ))) := by
          rw [e]; gcongr
      _ = X0m ^ (-(0.155 : ℝ)) * F18 m := by simp only [F18]; ring
  have hp : 0 ≤ X0m ^ (-(0.155 : ℝ)) := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not s (fun m => V m < X0m)]
  have hlo : ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
      V m ^ (ε - 2) ≤ 2.218 := by
    calc ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)
        ≤ ∑ m ∈ s.filter (fun m => V m < X0m), (if 2 ≤ m then
            (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.955 : ℝ)) else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm2 := (hs m (Finset.mem_filter.mp hm).1).1
          rw [if_pos hm2, ← hlow m hm]
          exact mul_le_mul_of_nonneg_left (hexp m) (by positivity)
      _ ≤ ∑' m : ℕ, (if 2 ≤ m then
            (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.955 : ℝ)) else 0) :=
          summable_hord1955.sum_le_tsum _ (fun m _ => by split_ifs <;> positivity)
      _ = BSCert.Consts.ordA 1.955 := by
          rw [BSCert.Consts.ordA_eq_tsum (by norm_num) zeta1955_lt_two]
      _ ≤ 2.218 := BSCert.Consts.ordA_1955_le
  have hhi : ∑ m ∈ s.filter (fun m => ¬ V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
      V m ^ (ε - 2) ≤ X0m ^ (-(0.155 : ℝ)) * 7.55 := by
    refine (Finset.sum_le_sum hhi1).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hF18 hp
  nlinarith

end KR

namespace Margin.Rec

/-- **The corrected field `hhead`** (Step 5): for `2t/X₀⁻ ≤ Z` and `ε' ≤ 0.045`, the head sum
over any subset of the levels of `NAll P t (X₀⁻/2)` is at most `1 + 2.2181`. -/
theorem hhead_loc {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (P : BeurlingSystem)
    (h : P.HBS X0m Z η1 η2 ε1) (hXm : 100000000 ≤ Real.log X0m) (p : CP) (hpXm : p.Xm = X0m)
    (hε' : p.ε' ≤ 0.045) {t : ℝ} (hZ : 2 * t / X0m ≤ Z)
    (s : Finset ℕ) (hs : s ⊆ KR.NAll P t (p.Xm / 2)) :
    ∑ M ∈ s, Aw P p M ≤ 1 + 2.2181 := by
  have hX := h.X0m_pos
  have hmem : ∀ M ∈ s, M ≠ 0 ∧ LemmaM.valN P.labelVal M ≤ 2 * t / X0m := by
    intro M hM
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hs hM)
    rw [mem_elems, hpXm] at he
    refine ⟨(iota_pos e).ne', ?_⟩
    rw [P.valN_iota]
    calc P.val e ≤ t / (X0m / 2) := he
      _ = 2 * t / X0m := by field_simp
  rw [← Finset.sum_filter_add_sum_filter_not s (fun M => 2 ≤ M)]
  have h2 := KR.hordA0_1955 P h hXm hε' hZ (s.filter (fun M => 2 ≤ M)) (fun m hm => by
    obtain ⟨hms, hm2⟩ := Finset.mem_filter.mp hm
    exact ⟨hm2, (hmem m hms).2⟩)
  have h1 : ∑ M ∈ s.filter (fun M => ¬ 2 ≤ M), Aw P p M ≤ 1 := by
    have hsub : s.filter (fun M => ¬ 2 ≤ M) ⊆ {1} := by
      intro M hM
      obtain ⟨hMs, hM2⟩ := Finset.mem_filter.mp hM
      have := (hmem M hMs).1
      rw [Finset.mem_singleton]; omega
    calc ∑ M ∈ s.filter (fun M => ¬ 2 ≤ M), Aw P p M ≤ ∑ M ∈ ({1} : Finset ℕ), Aw P p M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun M _ _ => Aw_nonneg M)
      _ = 1 := by
          rw [Finset.sum_singleton]
          unfold Aw
          rw [Vv_one, Real.one_rpow, BSCert.X0Band.Hord_eq 1, if_pos le_rfl]; norm_num
  have h2' : ∑ M ∈ s.filter (fun M => 2 ≤ M), Aw P p M ≤ 2.2181 := by
    refine le_of_eq_of_le ?_ h2
    rfl
  linarith

end Margin.Rec


end
