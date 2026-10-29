module

public import RequestProject.Beurling.Noise.ThreshMassDefs
public import RequestProject.Beurling.LemmaM
public import RequestProject.Beurling.Noise.Saias59

/-!
# Threshold changes of the sharp coefficients (Proposition 5.35(B), Step 3, first bullet)

04f-bridge.tex, proof of Proposition 5.35, range (B), Step 3, "Threshold changes": for a start
`y` and `z < y`, the sharp coefficient `c_n(·) = μ(n) χ^t_·(n)` (Lemma 5.5) changes between `z` and
`y` only if `χ_y(n) = 1` and `χ_z(n) = 0`, that is, only if the threshold
`τ(n) = max_{p ∣ n} t(p) ∏_{q ∣ n, t(q) ≥ t(p)} q` lies in `[z, y)` (Lemma 5.23,
04e-lp.tex). Here this is `tauIn_of_chi`: in the index world of `BeurlingSystem.TauIn`
(`n = iota e`, `t(p_j) = t_j`), `χ_y(iota e) ∧ ¬ χ_z(iota e)` gives `τ(e) ∈ [a, y)` for every
`a ≤ z`. Ties `t(p) = t(q)` are harmless: the ordered product of `χ` (ties broken by the label)
at the rank-least prime of a tie class equals the unordered product `Mprod` of every member of
the class.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem) {t tw : ℕ → ℝ}

/-- The ordered product of `χ` at the label `qp j`, in the index world. -/
lemma valS_iota_filter (tw : ℕ → ℝ) (e : ℕ →₀ ℕ) (j : ℕ) :
    LemmaM.valS P.labelVal ((iota e).primeFactors.filter
        fun q => LemmaM.rk tw (qp j) ≤ LemmaM.rk tw q) =
      ∏ i ∈ e.support.filter (fun i => LemmaM.rk tw (qp j) ≤ LemmaM.rk tw (qp i)), P.p i := by
  unfold LemmaM.valS
  rw [primeFactors_iota, Finset.filter_image,
    Finset.prod_image (fun a _ b _ h => qp_injective h)]
  simp only [labelVal_qp]

lemma prod_p_mono {s s' : Finset ℕ} (h : s ⊆ s') : ∏ i ∈ s, P.p i ≤ ∏ i ∈ s', P.p i :=
  P.prod_p_le_of_subset h

/-- **Threshold changes** (Step 3, first bullet; Lemma 5.23 at `[a, y)`): if `χ_y(iota e)`
holds and `χ_z(iota e)` fails, with `a ≤ z`, then `τ(e) ∈ [a, y)`. The decision order on labels
is `tw` with `tw (qp j) = t j`. -/
theorem tauIn_of_chi (htw : ∀ j, tw (qp j) = t j) (ht : ∀ j, 0 < t j) {e : ℕ →₀ ℕ}
    {a y z : ℝ} (hy : LemmaM.chi tw P.labelVal y (iota e))
    (hz : ¬ LemmaM.chi tw P.labelVal z (iota e)) (haz : a ≤ z) :
    P.TauIn t a y e := by
  classical
  obtain ⟨hsq, hchi⟩ := hy
  have hrk : ∀ i i' : ℕ, LemmaM.rk tw (qp i) ≤ LemmaM.rk tw (qp i') → t i ≤ t i' := by
    intro i i' h
    have := LemmaM.t_le_of_rk_le tw h
    rwa [htw, htw] at this
  refine ⟨?_, ?_⟩
  · -- the failing prime
    have hz' : ¬ LemmaM.chiS tw P.labelVal z (iota e).primeFactors := fun h => hz ⟨hsq, h⟩
    unfold LemmaM.chiS at hz'
    push_neg at hz'
    obtain ⟨p, hp, hle⟩ := hz'
    rw [primeFactors_iota, Finset.mem_image] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    refine ⟨j, hj, ?_⟩
    rw [valS_iota_filter, htw] at hle
    have hsub : e.support.filter (fun i => LemmaM.rk tw (qp j) ≤ LemmaM.rk tw (qp i)) ⊆
        e.support.filter (fun i => t j ≤ t i) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hi1, hrk _ _ hi2⟩
    have hm := P.prod_p_mono hsub
    have := (ht j).le
    unfold Mprod
    nlinarith
  · intro j hj
    -- the rank-least member of the tie class of `j`
    set C := e.support.filter (fun i => t i = t j) with hC
    have hjC : j ∈ C := Finset.mem_filter.mpr ⟨hj, rfl⟩
    obtain ⟨i0, hi0C, hmin⟩ := C.exists_min_image (fun i => LemmaM.rk tw (qp i)) ⟨j, hjC⟩
    obtain ⟨hi0, hti0⟩ := Finset.mem_filter.mp hi0C
    have hset : e.support.filter (fun i => t j ≤ t i) =
        e.support.filter (fun i => LemmaM.rk tw (qp i0) ≤ LemmaM.rk tw (qp i)) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hti⟩
        refine ⟨hi, ?_⟩
        rcases hti.lt_or_eq with hlt | heq
        · rw [LemmaM.rk_le_iff, htw, htw]
          left; rw [hti0]; exact hlt
        · exact hmin i (Finset.mem_filter.mpr ⟨hi, heq.symm⟩)
      · rintro ⟨hi, hr⟩
        exact ⟨hi, hti0 ▸ hrk _ _ hr⟩
    have hc := hchi (qp i0) (by rw [primeFactors_iota]; exact Finset.mem_image_of_mem _ hi0)
    rw [valS_iota_filter, htw] at hc
    unfold Mprod
    rw [hset, ← hti0]
    exact hc

/-- `χ` is monotone in the start: `χ_z(n) → χ_y(n)` for `z ≤ y`. -/
lemma chi_mono {val : ℕ → ℝ} {n : ℕ} {z y : ℝ} (hzy : z ≤ y) (h : LemmaM.chi tw val z n) :
    LemmaM.chi tw val y n :=
  ⟨h.1, fun p hp => lt_of_lt_of_le (h.2 p hp) hzy⟩

end BeurlingSystem

end
