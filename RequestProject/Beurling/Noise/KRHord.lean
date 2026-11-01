module

public import RequestProject.Beurling.Noise.KRHordZeta
public import RequestProject.Beurling.Noise.KRHordCert

/-!
# The ordered-factorisation sums for `𝒩` (§5.9.1, "Ordered factorisations")

For a Beurling system satisfying (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸`, and `ε ≤ 0.03`:

  `∑_{m ∈ s} H_ord(m) m^{ε-2} ≤ 2.0674`,  `∑_{m ∈ s} H_ord(m) m^{ε-2} log m ≤ 9.4091`

for every finite set `s` of elements `m ≥ 2` of value `≤ B ≤ Z` (`hordSumsB`). These are the
values `A₀(0.03) ≤ 2.06734`, `A₁(0.03) ≤ 9.409` for `ℕ` (`KRHordCert.lean`, correction #103)
plus the tails of the paper's argument:

* the elements of value `< X₀⁻` are rational integers (`valN_eq_self`), so their part is a
  partial sum of the series for `ℕ`;
* for the others, `m^{ε-2} ≤ X₀⁻^{-0.17} m^{-1.8}` (and `m^{ε-2} log m ≤ 100 X₀⁻^{-0.16} m^{-1.8}`),
  and `∑ H_ord(m) m^{-1.8} ≤ (Z - 1)/(2 - Z) ≤ 8.6` with `Z = ζ_𝒩(1.8) ≤ 1.883`
  (`hord_gen`, the identity `∑ H_ord(m) m^{-s} = 1/(2 - ζ_𝒩(s))` as an inequality on
  divisor-closed finite sets, and `zetaPartial_le`).

The paper states the sums over all of `𝒩`; (HBS) on `[1, Z]` controls `𝒩` only on `[1, Z]`,
and Corollary 5.17(b) reads them only up to `y/u ≤ 2y/X₀⁻ ≤ Z`, so they are stated with the
bound `B` (`HordSumsB`). `cor_5_17_b_full` is Corollary 5.17(b) with `C_N` under (HBS) and
`λ₀ ≤ 1.001` only.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR

/-! ## The generating inequality on a divisor-closed set -/

/-- `∑_{m ∈ S, m ≥ 2} H_ord(m) f(m) ≤ z/(1 - z)` if `S` is divisor-closed, `f` is
multiplicative and `∑_{g ∈ S, g ≥ 2} f(g) ≤ z < 1`. -/
theorem hord_gen (S : Finset ℕ) (hdiv : ∀ m ∈ S, ∀ d, d ∣ m → d ∈ S) (h0 : 0 ∉ S)
    (f : ℕ → ℝ) (hf0 : ∀ m, 0 ≤ f m) (hf1 : f 1 = 1)
    (hfm : ∀ d g, d ≠ 0 → g ≠ 0 → f (d * g) = f d * f g) {z : ℝ}
    (hz : ∑ g ∈ S.filter (2 ≤ ·), f g ≤ z) (hz1 : z < 1) :
    ∑ m ∈ S.filter (2 ≤ ·), (BSCert.X0Band.Hord m : ℝ) * f m ≤ z / (1 - z) := by
  set S2 := S.filter (2 ≤ ·)
  set T := ∑ m ∈ S2, (BSCert.X0Band.Hord m : ℝ) * f m
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (hf0 m)
  have hz0 : 0 ≤ z := (Finset.sum_nonneg fun g _ => hf0 g).trans hz
  -- the whole set: `∑_{m ∈ S} H_ord(m) f(m) ≤ 1 + T`
  have hall : ∑ m ∈ S, (BSCert.X0Band.Hord m : ℝ) * f m ≤ 1 + T := by
    rw [← Finset.sum_filter_add_sum_filter_not S (2 ≤ ·)]
    have hsub : S.filter (fun m => ¬ 2 ≤ m) ⊆ {1} := by
      intro m hm
      obtain ⟨hmS, hm2⟩ := Finset.mem_filter.mp hm
      have : m ≠ 0 := fun h => h0 (h ▸ hmS)
      rw [Finset.mem_singleton]; omega
    have h1 : ∑ m ∈ S.filter (fun m => ¬ 2 ≤ m), (BSCert.X0Band.Hord m : ℝ) * f m ≤ 1 := by
      calc ∑ m ∈ S.filter (fun m => ¬ 2 ≤ m), (BSCert.X0Band.Hord m : ℝ) * f m
          ≤ ∑ m ∈ ({1} : Finset ℕ), (BSCert.X0Band.Hord m : ℝ) * f m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun m _ _ => mul_nonneg (by positivity) (hf0 m))
        _ = 1 := by
            rw [Finset.sum_singleton, hf1, BSCert.X0Band.Hord_eq 1, if_pos le_rfl]; simp
    linarith
  -- the recursion
  have key : T ≤ (∑ d ∈ S, (BSCert.X0Band.Hord d : ℝ) * f d) * ∑ g ∈ S2, f g := by
    have e1 : T = ∑ x ∈ S2.sigma (fun m => m.properDivisors),
        (BSCert.X0Band.Hord x.2 : ℝ) * f x.2 * f (x.1 / x.2) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm2 := (Finset.mem_filter.mp hm).2
      rw [BSCert.X0Band.Hord_eq m, if_neg (by omega)]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdm, hdlt⟩ := Nat.mem_properDivisors.mp hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; omega
      have hq0 : m / d ≠ 0 := by
        intro hq; rw [Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero hd0)] at hq; omega
      have : f m = f d * f (m / d) := by
        rw [← hfm d (m / d) hd0 hq0, Nat.mul_div_cancel' hdm]
      rw [this]; ring
    rw [e1, Finset.sum_mul_sum, ← Finset.sum_product']
    set φ : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
    have hinj : Set.InjOn φ (S2.sigma (fun m => m.properDivisors)) := by
      intro x hx y hy hxy
      simp only [φ, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have hx' := Finset.mem_sigma.mp hx
      have hy' := Finset.mem_sigma.mp hy
      have hxd := (Nat.mem_properDivisors.mp hx'.2).1
      have hyd := (Nat.mem_properDivisors.mp hy'.2).1
      have : x.1 = y.1 := by
        have ex := Nat.mul_div_cancel' hxd
        have ey := Nat.mul_div_cancel' hyd
        rw [← ex, ← ey, h1, ← h1, h2, h1]
      exact Sigma.ext this (heq_of_eq h1)
    calc ∑ x ∈ S2.sigma (fun m => m.properDivisors),
          (BSCert.X0Band.Hord x.2 : ℝ) * f x.2 * f (x.1 / x.2)
        = ∑ y ∈ (S2.sigma (fun m => m.properDivisors)).image φ,
            (BSCert.X0Band.Hord y.1 : ℝ) * f y.1 * f y.2 :=
          (Finset.sum_image (f := fun y : ℕ × ℕ => (BSCert.X0Band.Hord y.1 : ℝ) * f y.1 * f y.2)
            hinj).symm
      _ ≤ ∑ y ∈ S ×ˢ S2, (BSCert.X0Band.Hord y.1 : ℝ) * f y.1 * f y.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
            obtain ⟨hm, hd⟩ := Finset.mem_sigma.mp hx
            obtain ⟨hmS, hm2⟩ := Finset.mem_filter.mp hm
            obtain ⟨hdm, hdlt⟩ := Nat.mem_properDivisors.mp hd
            have hd0 : x.2 ≠ 0 := by rintro h; rw [h] at hdm; simp at hdm; omega
            refine Finset.mem_product.mpr ⟨hdiv _ hmS _ hdm, Finset.mem_filter.mpr
              ⟨hdiv _ hmS _ (Nat.div_dvd_of_dvd hdm), ?_⟩⟩
            have hq := Nat.mul_div_cancel' hdm
            rcases Nat.lt_or_ge (x.1 / x.2) 2 with hlt | hge
            · interval_cases h : x.1 / x.2
              · simp at hq; omega
              · simp at hq; omega
            · exact hge
          · intro y _ _; exact mul_nonneg (mul_nonneg (by positivity) (hf0 _)) (hf0 _)
  have h2 : T ≤ (1 + T) * z := by
    refine key.trans ?_
    have hA0 : 0 ≤ ∑ d ∈ S, (BSCert.X0Band.Hord d : ℝ) * f d :=
      Finset.sum_nonneg fun d _ => mul_nonneg (by positivity) (hf0 d)
    exact mul_le_mul hall hz (Finset.sum_nonneg fun g _ => hf0 g) (by linarith)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ## Values of the labels -/

variable (P : BeurlingSystem)

lemma valN_dvd_le {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) :
    LemmaM.valN P.labelVal d ≤ LemmaM.valN P.labelVal m :=
  LemmaM.valN_le_of_dvd _ (fun r _ => P.one_le_labelVal r) hd hm

lemma one_le_valN_label (m : ℕ) : 1 ≤ LemmaM.valN P.labelVal m :=
  LemmaM.one_le_valN _ fun r _ => P.one_le_labelVal r

/-- Below `X₀⁻` the elements are rational integers: `V(m) = m`. -/
lemma valN_eq_self {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {m : ℕ}
    (hm : m ≠ 0) (hX : LemmaM.valN P.labelVal m < X0m) (hZ : LemmaM.valN P.labelVal m ≤ Z) :
    LemmaM.valN P.labelVal m = m := by
  have hlab : ∀ r ∈ m.primeFactors, P.labelVal r = r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hle : P.labelVal r ≤ LemmaM.valN P.labelVal m := by
      rw [← KR.valN_prime P.labelVal hrp]
      exact KR.valN_dvd_le P (Nat.dvd_of_mem_primeFactors hr) hm
    have := h.ident (x := LemmaM.valN P.labelVal m) hX hZ (Nat.count Nat.Prime r)
      (Or.inl hle)
    unfold labelVal
    rw [this, exists_qp_eq hrp]
  unfold LemmaM.valN
  have e : (m.factorization.prod fun p k => P.labelVal p ^ k) =
      m.factorization.prod fun p k => ((p : ℝ) ^ k) := by
    apply Finsupp.prod_congr
    intro p hp
    rw [Nat.support_factorization] at hp
    rw [hlab p hp]
  rw [e]
  have := Nat.prod_factorization_pow_eq_self hm
  conv_rhs => rw [← this]
  simp only [Finsupp.prod]
  push_cast
  rfl

/-! ## The sums -/

/-- The ordered-factorisation sums of `P` read up to the value `B`: every finite set `s` of
elements `m ≥ 2` with `m ≤ B` has `∑ H_ord(m) m^{ε-2} ≤ A₀` and
`∑ H_ord(m) m^{ε-2} log m ≤ A₁`. -/
def HordSumsB (Q : BeurlingSystem) (ε A0 A1 B : ℝ) : Prop :=
  ∀ s : Finset ℕ, (∀ m ∈ s, 2 ≤ m ∧ LemmaM.valN Q.labelVal m ≤ B) →
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN Q.labelVal m ^ (ε - 2) ≤ A0 ∧
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN Q.labelVal m ^ (ε - 2) *
      Real.log (LemmaM.valN Q.labelVal m) ≤ A1

/-- `∑_{m ∈ S, m ≥ 2} H_ord(m) m^{-1.8} ≤ 7.55` on divisor-closed sets of values `≤ B ≤ Z`. -/
lemma hord_18_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {B : ℝ} (hB : B ≤ Z) (S : Finset ℕ)
    (hdiv : ∀ m ∈ S, ∀ d, d ∣ m → d ∈ S) (h0 : 0 ∉ S)
    (hSB : ∀ m ∈ S, LemmaM.valN P.labelVal m ≤ B) :
    ∑ m ∈ S.filter (2 ≤ ·), (BSCert.X0Band.Hord m : ℝ) *
      LemmaM.valN P.labelVal m ^ (-(1.8 : ℝ)) ≤ 7.55 := by
  set V := LemmaM.valN P.labelVal
  have hV1 : ∀ m, 1 ≤ V m := KR.one_le_valN_label P
  have hzeta : ∑ g ∈ S.filter (2 ≤ ·), V g ^ (-(1.8 : ℝ)) ≤ 0.883 := by
    rcases lt_or_ge B 1 with hB1 | hB1
    · have : S.filter (2 ≤ ·) = ∅ := by
        ext g; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hg _; have := hSB g hg; have := hV1 g; linarith
      rw [this, Finset.sum_empty]; norm_num
    set T := (P.elems B).filter (fun e => iota e ∈ S.filter (2 ≤ ·))
    have himg : S.filter (2 ≤ ·) = T.image iota := by
      ext g
      constructor
      · intro hg
        have hg' := Finset.mem_filter.mp hg
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp
          (KR.mem_image_iota P (by omega) (hSB g hg'.1))
        exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hg⟩, rfl⟩
      · intro hg
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
        exact (Finset.mem_filter.mp he).2
    rw [himg, Finset.sum_image (fun a _ b _ hab => iota_injective hab)]
    simp_rw [V, P.valN_iota]
    have h0B : (0 : ℕ →₀ ℕ) ∈ P.elems B := by
      rw [mem_elems]; simpa [BeurlingSystem.val] using hB1
    have hsub : T ⊆ (P.elems B).erase 0 := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      refine Finset.mem_erase.mpr ⟨?_, he1⟩
      rintro rfl
      have := (Finset.mem_filter.mp he2).2
      simp [iota] at this
    have htot := zetaPartial_le P h hXm hB
    rw [← Finset.add_sum_erase _ _ h0B] at htot
    have hv0 : P.val 0 = 1 := by simp [BeurlingSystem.val]
    rw [hv0, Real.one_rpow] at htot
    calc ∑ e ∈ T, P.val e ^ (-(1.8 : ℝ)) ≤ ∑ e ∈ (P.elems B).erase 0, P.val e ^ (-(1.8 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by
            have := P.val_pos e; positivity)
      _ ≤ 0.883 := by linarith
  have hg := hord_gen S hdiv h0 (fun m => V m ^ (-(1.8 : ℝ)))
    (fun m => by have := hV1 m; positivity) (by simp [V, LemmaM.valN_one])
    (fun d g hd hg => by
      simp only [V]
      rw [LemmaM.valN_mul _ hd hg, Real.mul_rpow (by linarith [hV1 d]) (by linarith [hV1 g])])
    hzeta (by norm_num)
  refine hg.trans ?_
  norm_num

lemma zeta197_lt_two : BSCert.Consts.zetaR 1.97 < 2 :=
  lt_of_le_of_lt (BSCert.Consts.zetaR_strictAntiOn.antitoneOn (show (1 : ℝ) < 1.8 by norm_num)
    (show (1 : ℝ) < 1.97 by norm_num) (by norm_num)) BSCert.Consts.zeta_18_lt_two

/-- The series `∑_{m ≥ 2} H_ord(m) m^{-1.97}` is summable. -/
lemma summable_hord197 :
    Summable fun m : ℕ => if 2 ≤ m then (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ))
      else 0 := by
  have hs := (BSCert.Consts.hasSum_Hord (s := 1.97) (by norm_num) zeta197_lt_two).summable
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hs
  · split_ifs <;> positivity
  · split_ifs
    · exact le_of_eq (by norm_num)
    · positivity

/-- The series `∑ log m · H_ord(m) m^{-1.97}` is summable. -/
lemma summable_hordlog197 :
    Summable fun m : ℕ => Real.log m * (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) := by
  have hs := ((BSCert.Consts.hasSum_Hord (s := 1.8) (by norm_num)
    BSCert.Consts.zeta_18_lt_two).summable).mul_left (1 / 0.17)
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hs
  · have := Real.log_natCast_nonneg m; positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [BSCert.X0Band.Hord_eq 0]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hl := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 0.17)
    have e : (m : ℝ) ^ (0.17 : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) = (m : ℝ) ^ (-(1.8 : ℝ)) := by
      rw [← Real.rpow_add hm0]; norm_num
    have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) := by positivity
    have hp : (0 : ℝ) ≤ (m : ℝ) ^ (-(1.97 : ℝ)) := by positivity
    calc Real.log m * (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ))
        ≤ (m : ℝ) ^ (0.17 : ℝ) / 0.17 * (BSCert.X0Band.Hord m : ℝ) *
            (m : ℝ) ^ (-(1.97 : ℝ)) := by gcongr
      _ = 1 / 0.17 * ((BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.8 : ℝ))) := by
          rw [← e]; ring

/-- **The ordered-factorisation sums of `𝒩`** (§5.9.1): under (HBS) on `[1, Z]` with
`log X₀⁻ ≥ 10⁸`, for `ε ≤ 0.03` and `B ≤ Z`, `A₀ ≤ 2.0674` and `A₁ ≤ 9.4091` up to `B`. -/
theorem hordSumsB {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε : ℝ} (hε : ε ≤ 0.03) {B : ℝ} (hB : B ≤ Z) :
    HordSumsB P ε 2.0674 9.4091 B := by
  intro s hs
  set V := LemmaM.valN P.labelVal
  have hV1 : ∀ m, 1 ≤ V m := KR.one_le_valN_label P
  have hX := h.X0m_pos
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  -- the divisor closure
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
  have hF0 : 0 ≤ ∑ m ∈ s.filter (fun m => ¬ V m < X0m), F18 m :=
    Finset.sum_nonneg fun m _ => by have := hV1 m; simp only [F18]; positivity
  -- tiny powers of `X₀⁻`
  have htiny : ∀ c : ℝ, 0.16 ≤ c → X0m ^ (-c) ≤ 1 / 10 ^ 20 := by
    intro c hc
    have h1 := rpow_neg_le hX1 (by linarith : (0 : ℝ) < c)
    have h2 : (16000000 : ℝ) ≤ c * Real.log X0m := by nlinarith
    have h3 : (16000000 : ℝ) ^ 5 ≤ (c * Real.log X0m) ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
    have h4 : 120 / (c * Real.log X0m) ^ 5 ≤ 120 / (16000000 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
    have h5 : 120 / (16000000 : ℝ) ^ 5 ≤ 1 / 10 ^ 20 := by norm_num
    linarith
  -- the low part: rational integers
  have hlow : ∀ m ∈ s.filter (fun m => V m < X0m), V m = m := by
    intro m hm
    obtain ⟨hms, hlt⟩ := Finset.mem_filter.mp hm
    exact valN_eq_self P h (hs0 m hms) hlt ((hs m hms).2.trans hB)
  have hexp : ∀ m, V m ^ (ε - 2) ≤ V m ^ (-(1.97 : ℝ)) := fun m =>
    Real.rpow_le_rpow_of_exponent_le (hV1 m) (by linarith)
  -- the high part, pointwise
  have hhi1 : ∀ m ∈ s.filter (fun m => ¬ V m < X0m),
      (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) ≤ X0m ^ (-(0.17 : ℝ)) * F18 m := by
    intro m hm
    have hXV : X0m ≤ V m := not_lt.mp (Finset.mem_filter.mp hm).2
    have hV0 : 0 < V m := by linarith [hV1 m]
    have e : V m ^ (-(1.97 : ℝ)) = V m ^ (-(0.17 : ℝ)) * V m ^ (-(1.8 : ℝ)) := by
      rw [← Real.rpow_add hV0]; norm_num
    have h2 : V m ^ (-(0.17 : ℝ)) ≤ X0m ^ (-(0.17 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hX hXV (by norm_num)
    have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) := by positivity
    have h18' : (0 : ℝ) ≤ V m ^ (-(1.8 : ℝ)) := by positivity
    calc (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)
        ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.97 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hexp m) hH
      _ ≤ (BSCert.X0Band.Hord m : ℝ) * (X0m ^ (-(0.17 : ℝ)) * V m ^ (-(1.8 : ℝ))) := by
          rw [e]; gcongr
      _ = X0m ^ (-(0.17 : ℝ)) * F18 m := by simp only [F18]; ring
  have hhi2 : ∀ m ∈ s.filter (fun m => ¬ V m < X0m),
      (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) * Real.log (V m) ≤
        100 * X0m ^ (-(0.16 : ℝ)) * F18 m := by
    intro m hm
    have hXV : X0m ≤ V m := not_lt.mp (Finset.mem_filter.mp hm).2
    have hV0 : 0 < V m := by linarith [hV1 m]
    have hl := Real.log_le_rpow_div hV0.le (by norm_num : (0 : ℝ) < 0.01)
    have hl0 : 0 ≤ Real.log (V m) := Real.log_nonneg (hV1 m)
    have e : V m ^ (-(1.97 : ℝ)) * V m ^ (0.01 : ℝ) =
        V m ^ (-(0.16 : ℝ)) * V m ^ (-(1.8 : ℝ)) := by
      rw [← Real.rpow_add hV0, ← Real.rpow_add hV0]; norm_num
    have h2 : V m ^ (-(0.16 : ℝ)) ≤ X0m ^ (-(0.16 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hX hXV (by norm_num)
    have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) := by positivity
    have h18' : (0 : ℝ) ≤ V m ^ (-(1.8 : ℝ)) := by positivity
    have h197 : (0 : ℝ) ≤ V m ^ (-(1.97 : ℝ)) := by positivity
    calc (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) * Real.log (V m)
        ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (-(1.97 : ℝ)) * (V m ^ (0.01 : ℝ) / 0.01) := by
          have := mul_le_mul_of_nonneg_left (hexp m) hH
          exact mul_le_mul this hl hl0 (by positivity)
      _ = 100 * (BSCert.X0Band.Hord m : ℝ) * (V m ^ (-(1.97 : ℝ)) * V m ^ (0.01 : ℝ)) := by
          ring
      _ = 100 * (BSCert.X0Band.Hord m : ℝ) * (V m ^ (-(0.16 : ℝ)) * V m ^ (-(1.8 : ℝ))) := by
          rw [e]
      _ ≤ 100 * (BSCert.X0Band.Hord m : ℝ) * (X0m ^ (-(0.16 : ℝ)) * V m ^ (-(1.8 : ℝ))) := by
          gcongr
      _ = 100 * X0m ^ (-(0.16 : ℝ)) * F18 m := by simp only [F18]; ring
  have t17 := htiny 0.17 (by norm_num)
  have t16 := htiny 0.16 (by norm_num)
  have hp17 : 0 ≤ X0m ^ (-(0.17 : ℝ)) := by positivity
  have hp16 : 0 ≤ X0m ^ (-(0.16 : ℝ)) := by positivity
  constructor
  · rw [← Finset.sum_filter_add_sum_filter_not s (fun m => V m < X0m)]
    have hlo : ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) ≤ 2.06734 := by
      calc ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)
          ≤ ∑ m ∈ s.filter (fun m => V m < X0m), (if 2 ≤ m then
              (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) else 0) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hm2 := (hs m (Finset.mem_filter.mp hm).1).1
            rw [if_pos hm2, ← hlow m hm]
            exact mul_le_mul_of_nonneg_left (hexp m) (by positivity)
        _ ≤ ∑' m : ℕ, (if 2 ≤ m then
              (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) else 0) :=
            summable_hord197.sum_le_tsum _ (fun m _ => by split_ifs <;> positivity)
        _ = BSCert.Consts.ordA 1.97 := by
            rw [BSCert.Consts.ordA_eq_tsum (by norm_num) zeta197_lt_two]
        _ ≤ 2.06734 := BSCert.Consts.ordA_197_le_103
    have hhi : ∑ m ∈ s.filter (fun m => ¬ V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) ≤ X0m ^ (-(0.17 : ℝ)) * 7.55 := by
      refine (Finset.sum_le_sum hhi1).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hF18 hp17
    nlinarith
  · rw [← Finset.sum_filter_add_sum_filter_not s (fun m => V m < X0m)]
    have hlo : ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) * Real.log (V m) ≤ 9.409 := by
      calc ∑ m ∈ s.filter (fun m => V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
            V m ^ (ε - 2) * Real.log (V m)
          ≤ ∑ m ∈ s.filter (fun m => V m < X0m), Real.log m *
              (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [← hlow m hm]
            have hl0 : 0 ≤ Real.log (V m) := Real.log_nonneg (hV1 m)
            have := mul_le_mul_of_nonneg_left (hexp m)
              (show (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) by positivity)
            nlinarith
        _ ≤ ∑' m : ℕ, Real.log m * (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-(1.97 : ℝ)) :=
            summable_hordlog197.sum_le_tsum _ (fun m _ => by
              have := Real.log_natCast_nonneg m; positivity)
        _ = BSCert.Consts.ordA1 1.97 := by
            rw [BSCert.Consts.tsum_Hord_log (s₁ := 1.8) (by norm_num)
              BSCert.Consts.zeta_18_lt_two (by norm_num)]
        _ ≤ 9.409 := BSCert.Consts.ordA1_197_le_103
    have hhi : ∑ m ∈ s.filter (fun m => ¬ V m < X0m), (BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) * Real.log (V m) ≤ 100 * X0m ^ (-(0.16 : ℝ)) * 7.55 := by
      refine (Finset.sum_le_sum hhi2).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hF18 (by positivity)
    nlinarith

end KR

end
