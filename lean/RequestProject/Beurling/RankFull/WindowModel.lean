module

public import RequestProject.Beurling.RankFull.Config

/-!
# The window model: elements, exponent vectors, (V1), and Proposition 6.11 for it

Decided slots `dec ⊆ Fin N` carry jittered primes of values `q n`. An element of `N` in a window
`J` is a pair `(v, d)`: an exponent vector `v` over the decided slots (degree `≤ D`) and an
`X₀`-smooth rigid part `d ≤ Dmax`, with value `d ∏_n q_n^{v_n} ∈ J` (`windowElems`; the
exponents are also capped entrywise by `D`, for finiteness). The window set `S(J)` is the set of
non-zero exponent vectors of these elements (`windowVecs`).

* `RankFull.Config.zero_notMem_windowVecs` : `0 ∉ S(J)`;
* `RankFull.Config.card_windowElems_le` : **(V1) and the rigid element**: if `J` has length
  `< 1` and every prime value is `≥ 1`, then `#(N ∩ J) ≤ |S(J)| + 1` (two elements with the same
  vector differ by `M|d - d'| ≥ 1`, and at most one rigid integer lies in `J`);
* `RankFull.Config.prop_6_11_model` : **Proposition 6.11** for the window model of a
  `JitterLaw`-type process (decided slots `A n`, values `q n`): the reduction to skeletons is now
  proved (`skeletonReduction`), and the inputs are the skeleton bound for `skelCount`
  (Lemma A.5 + Theorem A.10, `SkeletonBound`), Theorem 6.23(a), measurability, and the
  parameter bounds.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

/-- The value `d ∏_n q_n^{v_n}` of an element. -/
noncomputable def elemVal (q : Fin N → ℝ) (p : (Fin N → ℕ) × ℕ) : ℝ :=
  (p.2 : ℝ) * ∏ n, q n ^ p.1 n

/-- The elements of `N` in the window `J` (degree `≤ D`, rigid part `≤ Dmax`). -/
noncomputable def windowElems (dec : Finset (Fin N)) (q : Fin N → ℝ) (X₀ D Dmax : ℕ)
    (J : Set ℝ) : Finset ((Fin N → ℕ) × ℕ) :=
  ((Fintype.piFinset fun _ => range (D + 1)) ×ˢ Nat.smoothNumbersUpTo Dmax X₀).filter fun p =>
    (∀ n, p.1 n ≠ 0 → n ∈ dec) ∧ ∑ n, p.1 n ≤ D ∧ elemVal q p ∈ J

/-- The window set `S(J)`: the non-zero exponent vectors of the elements in `J`. -/
noncomputable def windowVecs (dec : Finset (Fin N)) (q : Fin N → ℝ) (X₀ D Dmax : ℕ)
    (J : Set ℝ) : Finset (Fin N → ℕ) :=
  ((windowElems dec q X₀ D Dmax J).filter fun p => p.1 ≠ 0).image Prod.fst

lemma zero_notMem_windowVecs (dec : Finset (Fin N)) (q : Fin N → ℝ) (X₀ D Dmax : ℕ)
    (J : Set ℝ) : (0 : Fin N → ℕ) ∉ windowVecs dec q X₀ D Dmax J := by
  intro h
  obtain ⟨p, hp, hp0⟩ := Finset.mem_image.mp h
  exact (Finset.mem_filter.mp hp).2 hp0

/-- **(V1) and the rigid element**: `#(N ∩ J) ≤ |S(J)| + 1` for a window `J ⊆ [a, a + δ)` with
`δ < 1`, when all prime values are `≥ 1`. -/
theorem card_windowElems_le {dec : Finset (Fin N)} {q : Fin N → ℝ} (hq : ∀ n ∈ dec, 1 ≤ q n)
    (X₀ D Dmax : ℕ) {J : Set ℝ} {a δ : ℝ} (hJ : J ⊆ Set.Ico a (a + δ)) (hδ : δ < 1) :
    (windowElems dec q X₀ D Dmax J).card ≤ (windowVecs dec q X₀ D Dmax J).card + 1 := by
  set W := windowElems dec q X₀ D Dmax J
  have hsplit := Finset.card_filter_add_card_filter_not (s := W) (fun p => p.1 ≠ 0)
  -- the non-zero part: `Prod.fst` is injective (V1)
  have hinj : Set.InjOn Prod.fst (W.filter fun p => p.1 ≠ 0 : Set ((Fin N → ℕ) × ℕ)) := by
    rintro ⟨v, d⟩ hp ⟨v', d'⟩ hp' (h : v = v')
    subst h
    have hp1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1
    have hp1' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).1
    obtain ⟨hpd, hsupp, -, hval⟩ := Finset.mem_filter.mp hp1
    obtain ⟨hpd', -, -, hval'⟩ := Finset.mem_filter.mp hp1'
    have hM : 1 ≤ ∏ n, q n ^ v n := by
      have h := Finset.prod_le_prod (s := univ) (f := fun _ => (1 : ℝ))
        (g := fun n => q n ^ v n) (fun _ _ => zero_le_one) (fun n _ => by
          by_cases hv : v n = 0
          · simp [hv]
          · exact one_le_pow₀ (hq n (hsupp n hv)))
      simpa using h
    simp only [Prod.mk.injEq, true_and]
    by_contra hdd
    have h1 := hJ hval
    have h2 := hJ hval'
    simp only [elemVal, Set.mem_Ico] at h1 h2
    set M := ∏ n, q n ^ v n
    rcases Nat.lt_or_gt_of_ne hdd with h | h
    · have hd : (d : ℝ) + 1 ≤ d' := by exact_mod_cast h
      have : M ≤ (d' : ℝ) * M - d * M := by nlinarith
      linarith
    · have hd : (d' : ℝ) + 1 ≤ d := by exact_mod_cast h
      have : M ≤ (d : ℝ) * M - d' * M := by nlinarith
      linarith
  -- the zero part: at most one rigid integer in `J`
  have hzero : (W.filter fun p => ¬ p.1 ≠ 0).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨v, d⟩ hp ⟨v', d'⟩ hp'
    obtain ⟨hp1, hv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1', hv'⟩ := Finset.mem_filter.mp hp'
    simp only [ne_eq, not_not] at hv hv'
    subst hv; subst hv'
    have h1 := hJ (Finset.mem_filter.mp hp1).2.2.2
    have h2 := hJ (Finset.mem_filter.mp hp1').2.2.2
    simp only [elemVal, Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one,
      Set.mem_Ico] at h1 h2
    simp only [Prod.mk.injEq, true_and]
    by_contra hdd
    rcases Nat.lt_or_gt_of_ne hdd with h | h
    · have : (d : ℝ) + 1 ≤ d' := by exact_mod_cast h
      linarith
    · have : (d' : ℝ) + 1 ≤ d := by exact_mod_cast h
      linarith
  have himg : (windowVecs dec q X₀ D Dmax J).card = (W.filter fun p => p.1 ≠ 0).card :=
    Finset.card_image_of_injOn hinj
  omega

/-- **Proposition 6.11 for the window model**: windows `Jw J ⊆ [a_J, a_J + δ)`, `δ < 1`, prime
values `≥ 1`; `S(J) = windowVecs`, `#(N ∩ J) = #windowElems`, and `X_𝔰 = skelCount`. The bound
`#(N ∩ J) ≤ |S(J)| + 1` and the reduction to skeletons are proved; the remaining inputs are
`SkeletonBound` for `skelCount` (Lemma A.5 + Theorem A.10 with `C = B'`), Theorem 6.23(a)
(`hcap`), measurability and the parameter bounds. -/
theorem prop_6_11_model {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) (dec : Ω → Finset (Fin N)) (q : Ω → Fin N → ℝ)
    (hq : ∀ ω, ∀ n ∈ dec ω, 1 ≤ q ω n) (X₀' D Dmax : ℕ) (Jw : ι → Set ℝ) (a : ι → ℝ) {δ : ℝ}
    (hJ : ∀ J, Jw J ⊆ Set.Ico (a J) (a J + δ)) (hδ : δ < 1) (r₀ : ℕ)
    {c Q M₁ L z θ A Eu A_R b X₀ : ℝ} {H : ℝ → ℝ} (hH : SlotHyp H X₀)
    (hM₁ : M₁ = r₀ + Covers.phi c Q r₀ + 1) (hL : 465 ≤ L) (hz0 : 0 < z) (hz : z ≤ Real.exp L)
    (hθ : 0 < θ) (hb : 0 < b) (hθab : θ * Real.exp ((3 * H X₀ + 2) / X₀) * b ≤ 1.01)
    (hAR0 : 0 ≤ A_R) (hAR : A_R ≤ 1.8 * (L + 4)) (hu : 1 + r₀ / X₀ ≤ 2 * L)
    (hr₀ : L / (3 * Real.log L) + 3 ≤ r₀)
    (hW : (W.card : ℝ) ≤ 2 * z / (4 * L ^ (-6 : ℝ)) + 1)
    (hEu : 0 < Eu) (hEuA : Eu ≤ A) (hAtop : A ≤ A_R * b)
    (hXm : ∀ J (E : Matrix (Fin r₀) (Fin r₀) ℕ) l,
      Measurable fun ω => skelCount (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)) E l)
    (hmeas : ∀ J ∈ W, Measurable fun ω =>
      (rankFullCount r₀ (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)) : ℝ≥0∞))
    (hbound : ∀ J ∈ W, SkeletonBound P Good r₀ θ (4 * L ^ (-6 : ℝ)) A Eu
      (fun j => tauSlot H X₀ j)
      (fun E l ω => skelCount (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)) E l))
    (hcap : P ({ω | ∃ J ∈ W, Covers.rank (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)) < r₀ ∧
      (r₀ : ℝ) + Covers.phi c Q r₀ ≤ (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)).card} ∩ Good) ≤
        ENNReal.ofReal (L ^ (-3 : ℝ))) :
    P ({ω | ∃ J ∈ W, M₁ < (windowElems (dec ω) (q ω) X₀' D Dmax (Jw J)).card} ∩ Good) ≤
      ENNReal.ofReal (L ^ (-2 : ℝ)) :=
  prop_6_11_full P hGood W (fun J ω => windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J))
    (fun J ω => (windowElems (dec ω) (q ω) X₀' D Dmax (Jw J)).card)
    (fun J ω => card_windowElems_le (hq ω) X₀' D Dmax (hJ J) hδ) r₀ hH hM₁ hL hz0 hz hθ hb
    hθab hAR0 hAR hu hr₀ hW hEu hEuA hAtop
    (fun J E l ω => skelCount (windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)) E l) hXm hmeas
    (fun J _ => skeletonReduction r₀ (fun ω => windowVecs (dec ω) (q ω) X₀' D Dmax (Jw J)))
    hbound hcap

end RankFull.Config
