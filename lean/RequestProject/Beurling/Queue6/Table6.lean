module

public import RequestProject.Beurling.Queue6.Budget6

/-!
# Table 1 per scale (Lemma 6.10): `TableBudget` for the event family

At the dyadic scale `u = 2^m X₀` the failure probabilities on the good events sum to at most
`1.0001 (log X₀ + m log 2)^{-2} + 3.2 u^{-2}`:

* E1 (Proposition 6.11, one dyadic height per scale): `(log z)^{-2} ≤ 1.0001 L_u^{-2}`;
* E2 (Theorem 6.6(i)): `#𝓘_u · (K₀ + 7) e^{-4L} ≤ u^{-2}`;
* E4 (Lemma 6.1): `#𝒥_u · 2 u^{-4} ≤ u^{-2}`;
* E3, E3′ (Lemma 5.22): `≤ 1.2 u^{-2}`;
* the null events of R1′ and `𝒩₌`: `0`.

`Queue6.tableBudget_EF` : `TableBudget jitterMeasure X₀ (EF θ X₀ D) (tF X₀ D) (sF D)`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueBound QueueMono
  Greedy QueueDet SlotModel

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-- `(log z_m)^{-2} ≤ 1.0001 (log X₀ + m log 2)^{-2}`. -/
lemma e1_numeric (hX : 10 ^ 8 ≤ Real.log X₀) (m : ℕ) :
    Real.log (zH X₀ m) ^ (-2 : ℝ) ≤ 1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hz : Real.log (zH X₀ m) = Real.log X₀ + m * Real.log 2 - Real.log 2 := by
    unfold zH
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
      Real.log_pow]
    ring
  set L := Real.log X₀ + m * Real.log 2
  have hL : 10 ^ 8 ≤ L := by
    have : (0 : ℝ) ≤ m * Real.log 2 := by positivity
    linarith
  rw [hz, Real.rpow_neg (by linarith), Real.rpow_two, ← one_div,
    div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- **E2 per scale**: `∑_{I ∈ 𝓘_u} P(Fr(I)ᶜ ∩ Good(<b)) ≤ u^{-2}`. -/
theorem e2_scale (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueInputs θ X₀) (m : ℕ) :
    ∑' p : {p : ℕ × ℤ × ℤ // p.1 = m},
      jitterMeasure ((FrE θ X₀ p.1.1 p.1.2.1 p.1.2.2)ᶜ ∩ G0 θ X₀ Q.sec5 (tE2 p.1.2.2)) ≤
      ENNReal.ofReal (1 / uS X₀ m ^ 2) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  set u := uS X₀ m
  set c := ENNReal.ofReal ((K0 X₀ u + 7) * Real.exp (-(4 * Lq u)))
  -- reindex by `ℤ × ℤ`
  let e : {p : ℕ × ℤ × ℤ // p.1 = m} ≃ ℤ × ℤ :=
    { toFun := fun p => p.1.2
      invFun := fun q => ⟨(m, q), rfl⟩
      left_inv := fun p => by obtain ⟨⟨m', q⟩, h⟩ := p; simp only at h; subst h; rfl
      right_inv := fun q => rfl }
  set g : ℤ × ℤ → ENNReal := fun q =>
    jitterMeasure ((FrE θ X₀ m q.1 q.2)ᶜ ∩ G0 θ X₀ Q.sec5 (tE2 q.2))
  have hre : ∑' p : {p : ℕ × ℤ × ℤ // p.1 = m},
      jitterMeasure ((FrE θ X₀ p.1.1 p.1.2.1 p.1.2.2)ᶜ ∩ G0 θ X₀ Q.sec5 (tE2 p.1.2.2)) =
      ∑' q, g q := by
    rw [← e.symm.tsum_eq]; rfl
  rw [hre]
  -- the support
  set W := ⌊Wlen X₀ u⌋₊
  set b0 : ℤ := ⌈u⌉
  set b1 : ℤ := ⌊3 * u⌋
  set s : Finset (ℤ × ℤ) :=
    (Finset.range (W + 1) ×ˢ Finset.Icc b0 b1).image fun x => (x.2 - x.1, x.2)
  have hsupp : ∀ q ∉ s, g q = 0 := by
    intro q hq
    simp only [g]
    by_cases hadm : Adm X₀ m q.1 q.2
    · exfalso; apply hq
      obtain ⟨hub, hb3, hab, hW⟩ := hadm
      refine Finset.mem_image.mpr ⟨((q.2 - q.1).toNat, q.2), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · have h0 : 0 ≤ q.2 - q.1 := by omega
          have : ((q.2 - q.1 : ℤ) : ℝ) ≤ Wlen X₀ u := hW
          have h1 : (q.2 - q.1).toNat ≤ W := by
            apply Nat.le_floor
            have : (((q.2 - q.1).toNat : ℕ) : ℝ) = ((q.2 - q.1 : ℤ) : ℝ) := by
              rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
            rw [this]; exact hW
          omega
        · exact Int.ceil_le.mpr hub
        · exact Int.le_floor.mpr hb3
      · have h0 : 0 ≤ q.2 - q.1 := by omega
        simp only [Int.toNat_of_nonneg h0]; ext <;> simp
    · unfold FrE; rw [if_neg hadm]; simp
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ q ∈ s, g q ≤ c := fun q _ => frE_fail hθ hX hHB hnull hev hX₀ Q m q.1 q.2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≤ (Wlen X₀ u + 1) * (2 * u + 1) := by
    have h1 : s.card ≤ (W + 1) * (Finset.Icc b0 b1).card := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_range]
    have h2 : ((Finset.Icc b0 b1).card : ℝ) ≤ 2 * u + 1 := by
      rw [Int.card_Icc]
      have hb0 : (u : ℝ) ≤ b0 := Int.le_ceil u
      have hb1 : (b1 : ℝ) ≤ 3 * u := Int.floor_le _
      rcases le_or_gt b0 (b1 + 1) with h | h
      · have : ((b1 + 1 - b0).toNat : ℝ) = ((b1 + 1 - b0 : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        rw [this]; push_cast; linarith
      · rw [Int.toNat_of_nonpos (by omega)]; simp; linarith
    have h3 : ((W : ℕ) : ℝ) ≤ Wlen X₀ u := Nat.floor_le (by
      unfold Wlen
      have : (0 : ℝ) ≤ Real.log (3 * u) := Real.log_nonneg (by linarith)
      positivity)
    have : (s.card : ℝ) ≤ ((W : ℝ) + 1) * ((Finset.Icc b0 b1).card : ℝ) := by exact_mod_cast h1
    refine this.trans ?_
    apply mul_le_mul (by linarith) h2 (Nat.cast_nonneg _)
    unfold Wlen
    have : (0 : ℝ) ≤ Real.log (3 * u) := Real.log_nonneg (by linarith)
    positivity
  have hnum := count_numeric hX0 hX hu
  have hc0 : 0 ≤ ((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * Lq u)) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc (s.card : ℝ) * (((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * Lq u)))
      ≤ ((Wlen X₀ u + 1) * (2 * u + 1)) * (((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * Lq u))) :=
        mul_le_mul_of_nonneg_right hcard hc0
    _ = (Wlen X₀ u + 1) * (2 * u + 1) * ((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * Lq u)) := by ring
    _ ≤ 1 / u ^ 2 := hnum

/-- **E4 per scale**: `∑_{J ∈ 𝒥_u} P(Land(J)ᶜ ∩ Good) ≤ u^{-2}`. -/
theorem e4_scale (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (Q : QueueInputs θ X₀) (m : ℕ) (G : ℕ → Set JitterΩ) :
    ∑' p : {p : ℕ × ℕ × ℕ // p.1 = m},
      jitterMeasure ((LandE θ X₀ p.1.1 p.1.2.1 p.1.2.2)ᶜ ∩ G (tE4 X₀ p.1.1 p.1.2.2)) ≤
      ENNReal.ofReal (1 / uS X₀ m ^ 2) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  set u := uS X₀ m
  set c := ENNReal.ofReal (2 * Real.exp (-(4 * Real.log u)))
  let e : {p : ℕ × ℕ × ℕ // p.1 = m} ≃ ℕ × ℕ :=
    { toFun := fun p => p.1.2
      invFun := fun q => ⟨(m, q), rfl⟩
      left_inv := fun p => by obtain ⟨⟨m', q⟩, h⟩ := p; simp only at h; subst h; rfl
      right_inv := fun q => rfl }
  set g : ℕ × ℕ → ENNReal := fun q =>
    jitterMeasure ((LandE θ X₀ m q.1 q.2)ᶜ ∩ G (tE4 X₀ m q.2))
  have hre : ∑' p : {p : ℕ × ℕ × ℕ // p.1 = m},
      jitterMeasure ((LandE θ X₀ p.1.1 p.1.2.1 p.1.2.2)ᶜ ∩ G (tE4 X₀ p.1.1 p.1.2.2)) =
      ∑' q, g q := by
    rw [← e.symm.tsum_eq]; rfl
  rw [hre]
  set W := ⌊12 * capH X₀ u⌋₊
  set J := ⌊6 * u + 2⌋₊
  set s : Finset (ℕ × ℕ) :=
    (Finset.range (W + 1) ×ˢ Finset.range (J + 1)).image fun x => (x.2 - x.1, x.2)
  have hsupp : ∀ q ∉ s, g q = 0 := by
    intro q hq
    simp only [g]
    by_cases hJ : AdmJ X₀ m q.1 q.2
    · exfalso; apply hq
      obtain ⟨hij, hW, hhi⟩ := hJ
      refine Finset.mem_image.mpr ⟨(q.2 - q.1, q.2), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
        · have : q.2 - q.1 ≤ W := by
            apply Nat.le_floor
            rw [Nat.cast_sub hij.le]; exact hW
          omega
        · have : q.2 ≤ J := by
            apply Nat.le_floor
            unfold Jhi at hhi; linarith
          omega
      · ext <;> simp; omega
    · unfold LandE; rw [if_neg hJ]; simp
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ q ∈ s, g q ≤ c := fun q _ =>
    (measure_mono Set.inter_subset_left).trans (landE_fail hθ hX hHB Q m q.1 q.2)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hH1 := BModel.capH_ge_one hX0 hX hu
  have hcard : (s.card : ℝ) ≤ (12 * capH X₀ u + 1) * (6 * u + 3) := by
    have h1 : s.card ≤ (W + 1) * (J + 1) := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_range, Finset.card_range]
    have h2 : ((W : ℕ) : ℝ) ≤ 12 * capH X₀ u := Nat.floor_le (by linarith)
    have h3 : ((J : ℕ) : ℝ) ≤ 6 * u + 2 := Nat.floor_le (by linarith)
    have : (s.card : ℝ) ≤ ((W : ℝ) + 1) * ((J : ℝ) + 1) := by exact_mod_cast h1
    refine this.trans ?_
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hnum := land_numeric hX0 hX hu
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc (s.card : ℝ) * (2 * Real.exp (-(4 * Real.log u)))
      ≤ ((12 * capH X₀ u + 1) * (6 * u + 3)) * (2 * Real.exp (-(4 * Real.log u))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 1 / u ^ 2 := hnum

/-- **E1 per scale**: one dyadic height per scale, `(log z)^{-2} ≤ 1.0001 L_u^{-2}`
(Proposition 6.11: at `z ≥ X₀` from the window model, `eclW_fail`; at `z = X₀/2` the named
input `cluster0`). -/
theorem e1_scale (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hev : Even X₀) (Q : QueueInputs θ X₀) (m : ℕ) :
    ∑' n : {n : ℕ // id n = m},
      jitterMeasure ((E1ev θ X₀ n.1)ᶜ ∩ G0 θ X₀ Q.sec5 (tE1 X₀ n.1)) ≤
      ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2) := by
  have hsub : Subsingleton {n : ℕ // id n = m} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
  rw [tsum_eq_single ⟨m, rfl⟩ (fun b hb => absurd (Subsingleton.elim b _) hb)]
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (e1_numeric hX m))
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; exact Q.cluster0
  · have hc : Cond θ X₀ := ⟨hθ, hX, hHB⟩
    have := eclW_fail hc hev Q.slotHyp hm (G0 θ X₀ Q.sec5 (tE1 X₀ m)) (Q.S3d hc hev m hm)
      (Q.multi hc hev m hm) (Q.cover hc hev m hm)
    simpa [E1ev, dif_pos (And.intro hc hev)] using this

/-- **The target bound per scale** (Lemma 3.4 on the good event): no failure. -/
theorem tB_scale (Q : QueueInputs θ X₀) (m : ℕ) :
    ∑' n : {n : ℕ // id n = m},
      jitterMeasure ((tB (θ := θ) (X₀ := X₀) n.1)ᶜ ∩ G0 θ X₀ Q.sec5 (ttB X₀ n.1)) = 0 :=
  ENNReal.tsum_eq_zero.mpr fun n => Q.tbound n.1

/-- **E3, E3′ per scale** (Lemma 5.22): the bound of `QueueInputs.budget5` on the larger good
event. -/
theorem e5_scale (Q : QueueInputs θ X₀) (m : ℕ) :
    ∑' i : {i // Q.sec5.scale i = m},
      jitterMeasure ((Q.sec5.E i)ᶜ ∩ G0 θ X₀ Q.sec5 (Q.sec5.time i)) ≤
      ENNReal.ofReal (1.2 / uS X₀ m ^ 2) := by
  refine le_trans (ENNReal.tsum_le_tsum fun i => measure_mono ?_) (Q.budget5 m)
  rintro ω ⟨h1, hq, hg⟩
  refine ⟨⟨h1, hq⟩, ?_⟩
  simp only [goodBefore, mem_iInter] at hg ⊢
  intro j hj
  rcases j with n | k
  · exact hg (Sum.inl n) hj
  · exact hg (Sum.inr (Sum.inr (Sum.inr (Sum.inr k)))) hj

/-- **Table 1 for the base family**: on the good events of Definition 6.8, the failures at the
scale `m` sum to at most `1.0001 (log X₀ + m log 2)^{-2} + 3.2 (2^m X₀)^{-2}`. -/
theorem base_scale (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueInputs θ X₀) (m : ℕ) :
    ∑' i : {i : ι0 Q.sec5 // s0 Q.sec5 i = m},
      jitterMeasure ((E0 θ X₀ Q.sec5 i)ᶜ ∩ G0 θ X₀ Q.sec5 (t0 X₀ Q.sec5 i)) ≤
      ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 + 3.2 / (2 ^ m * X₀) ^ 2) := by
  set f := fun i : ι0 Q.sec5 =>
    jitterMeasure ((E0 θ X₀ Q.sec5 i)ᶜ ∩ G0 θ X₀ Q.sec5 (t0 X₀ Q.sec5 i))
  have h1 := tsum_subtype_sum (f := f) (s0 Q.sec5) m
  have h2 := tsum_subtype_sum (f := fun i => f (Sum.inr i))
    (fun i => s0 Q.sec5 (Sum.inr i)) m
  have h3 := tsum_subtype_sum (f := fun i => f (Sum.inr (Sum.inr i)))
    (fun i => s0 Q.sec5 (Sum.inr (Sum.inr i))) m
  have h4 := tsum_subtype_sum (f := fun i => f (Sum.inr (Sum.inr (Sum.inr i))))
    (fun i => s0 Q.sec5 (Sum.inr (Sum.inr (Sum.inr i)))) m
  simp only at h2 h3 h4
  rw [h1, h2, h3, h4]
  have bt := tB_scale Q m
  have bt' : ∑' x : {i // s0 Q.sec5 (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) = m},
      f (Sum.inr (Sum.inr (Sum.inr (Sum.inl x.1)))) = 0 := bt
  rw [bt', zero_add]
  have b1 := e1_scale hθ hX hHB hev Q m
  have b2 := e2_scale hθ hX hHB hnull hev hX₀ Q m
  have b4 := e4_scale hθ hX hHB Q m (G0 θ X₀ Q.sec5)
  have b5 := e5_scale Q m
  have hX0 : (0 : ℝ) < X₀ := by have := one_lt_of_logX (Nat.cast_nonneg _) hX; linarith
  have hu0 : 0 < uS X₀ m := uS_pos hX0 m
  calc _ ≤ ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2) +
        (ENNReal.ofReal (1 / uS X₀ m ^ 2) +
          (ENNReal.ofReal (1 / uS X₀ m ^ 2) + ENNReal.ofReal (1.2 / uS X₀ m ^ 2))) := by
        gcongr
        · exact b1
        · exact b2
        · exact b4
        · exact b5
    _ = ENNReal.ofReal (1.0001 / (Real.log X₀ + m * Real.log 2) ^ 2 +
          (1 / uS X₀ m ^ 2 + (1 / uS X₀ m ^ 2 + 1.2 / uS X₀ m ^ 2))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        unfold uS
        have e : (1 : ℝ) / (2 ^ m * X₀) ^ 2 + (1 / (2 ^ m * X₀) ^ 2 + 1.2 / (2 ^ m * X₀) ^ 2) =
            3.2 / (2 ^ m * X₀) ^ 2 := by ring
        linarith

/-- The null events of R1′ are null. -/
lemma nev_null (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueInputs θ X₀) (p : ℕ × ℤ × ℤ) :
    jitterMeasure (Nev θ X₀ Q.sec5 p)ᶜ = 0 := by
  by_cases hadm : Adm X₀ p.1 p.2.1 p.2.2
  · have h := R1cond_ae hθ hX hHB hnull hev hX₀ Q hadm
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [h] with ω hω
    simp only [Nev, mem_compl_iff, mem_setOf_eq, not_not]
    intro _ hG; exact hω hG
  · have : (Nev θ X₀ Q.sec5 p)ᶜ = ∅ := by
      ext ω; simp only [Nev, mem_compl_iff, mem_setOf_eq, mem_empty_iff_false, iff_false,
        not_not]
      intro h; exact absurd h hadm
    rw [this, measure_empty]

/-- **Table 1 / Lemma 6.10 per scale for the event family.** -/
theorem tableBudget_EF (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull)
    (hev : Even X₀) (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueInputs θ X₀) :
    TableBudget jitterMeasure X₀ (EF θ X₀ Q.sec5) (tF X₀ Q.sec5) (sF Q.sec5) := by
  intro m
  set f := fun i : ιF Q.sec5 => jitterMeasure ((EF θ X₀ Q.sec5 i)ᶜ ∩
    goodBefore (EF θ X₀ Q.sec5) (tF X₀ Q.sec5) (tF X₀ Q.sec5 i))
  rw [tsum_subtype_sum (f := f) (sF Q.sec5) m]
  have hinr : ∑' x : {i // sF Q.sec5 (Sum.inr i) = m}, f (Sum.inr x.1) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    simp only [f]
    refine measure_mono_null Set.inter_subset_left ?_
    rcases x with ⟨p | u, -⟩
    · exact nev_null hθ hX hHB hnull hev hX₀ Q p
    · rcases u with u | u
      · simp only [EF, Sum.elim_inr, Sum.elim_inl, compl_compl]; exact hnull θ hθ X₀ hev hX₀
      · simp only [EF, Sum.elim_inr]
        have hc : Cond θ X₀ := ⟨hθ, hX, hHB⟩
        unfold SG
        rw [Set.compl_iInter]
        refine measure_iUnion_null fun m' => measure_mono_null ?_ (good_compl_null hc (m' + 1))
        intro ω hω hG
        apply hω
        have := hG
        simp only [goodLt, mem_iInter] at this
        exact this m' (Finset.mem_range.mpr (Nat.lt_succ_self m'))
  rw [hinr, add_zero]
  refine le_trans (ENNReal.tsum_le_tsum fun x => ?_) (base_scale hθ hX hHB hnull hev hX₀ Q m)
  simp only [f, EF, tF, Sum.elim_inl]
  unfold G0
  rw [← withQC_fail]
  exact measure_mono (Set.inter_subset_inter_right _
    (goodBefore_sum_inl _ _ _ _ _))

end Queue6

end
