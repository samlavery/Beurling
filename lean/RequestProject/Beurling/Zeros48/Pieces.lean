module

public import RequestProject.Beurling.Zeros48.Target
public import RequestProject.Beurling.Zeros48.Osc
public import RequestProject.Beurling.Zeros48.Early
public import RequestProject.Beurling.Zeros48.Numerics

/-!
# Lemma 4.8(ii): the pieces of `D̂_{<a_k}` for the realised system

This is the proof of Lemma 4.8(ii) (§4, after (Gammalow)) for the realised system: with
`ℬ = ℕ_P \ (𝒟 ∪ A)` (`residual`), on the box `Q`

  `D̂_{<a_k} = ∑_{n ∈ ℬ, n ≤ a_k} n^{-s} - ∫_{X₀}^{a_k} x^{-s} (1 - ρ_det - ρ̄_A + R') dx`,

the residual elements below `X = X₀ + 1` are put in a bounded part `p`, the integral is written in
logarithmic coordinates, and the residual elements in `[X, a_k]` are counted in short intervals by
`#ℬ ∩ [u, v] = D(v) - D(u-) + ∫_{[u,v]} T'_cont` with `|D| ≤ x^η` and `T'_cont ≤ 1.01`.
The result is `Lemma48PiecesCount` for every `k` (`lemma48PiecesCount_realised`).
-/

@[expose] public section

open Set MeasureTheory Complex Construction Target Rankin Absorbed Decomp Oscillation CaplLink
  GoodHeights DesignedZero

namespace Zeros48

/-! ### Two elementary lemmas -/

/-- A finite family of reals, listed in non-decreasing order. -/
lemma exists_sorted_enum {β : Type*} (E : Finset β) (f : β → ℝ) :
    ∃ (m : ℕ) (n : Fin m → ℝ), Monotone n ∧ (∀ i, ∃ e ∈ E, n i = f e) ∧
      (∀ {γ : Type} [AddCommMonoid γ] (F : ℝ → γ), ∑ i, F (n i) = ∑ e ∈ E, F (f e)) := by
  classical
  set m := E.card
  set eq := E.equivFin
  set v : Fin m → ℝ := fun i => f (eq.symm i)
  refine ⟨m, v ∘ Tuple.sort v, Tuple.monotone_sort v, fun i => ⟨eq.symm (Tuple.sort v i),
    (eq.symm (Tuple.sort v i)).2, rfl⟩, fun F => ?_⟩
  show ∑ i, F (v (Tuple.sort v i)) = _
  rw [Equiv.sum_comp (Tuple.sort v) (fun i => F (v i))]
  rw [← Finset.sum_coe_sort E]
  exact Fintype.sum_equiv eq.symm _ _ (fun _ => rfl)

/-- A dyadic scale `2^J X ∈ [a, 2a]` (`0 < X ≤ a`). -/
lemma exists_dyadic {X a : ℝ} (hX : 0 < X) (hXa : X ≤ a) :
    ∃ J : ℕ, a ≤ 2 ^ J * X ∧ 2 ^ J * X ≤ 2 * a := by
  classical
  have hex : ∃ J : ℕ, a ≤ 2 ^ J * X := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (a / X) (by norm_num : (1 : ℝ) < 2)
    exact ⟨J, by rw [div_lt_iff₀ hX] at hJ; linarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simp; linarith
  · obtain ⟨J, hJ⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt := Nat.find_min hex (show J < Nat.find hex by omega)
    push_neg at hlt
    rw [hJ, pow_succ]
    nlinarith

/-- Bounded and equal on `(a, b]` to a measurable function: interval integrable. -/
lemma intervalIntegrable_of_eqOn {f g : ℝ → ℝ} (hg : Measurable g) {a b C : ℝ} (hab : a ≤ b)
    (heq : ∀ x ∈ Ioc a b, f x = g x) (hb : ∀ x ∈ Ioc a b, |g x| ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have : IntegrableOn g (Ioc a b) :=
    Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact hb x hx)
  exact this.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioc

/-! ### The continuous part of the target on `[X₀, a]` -/

section Cont

variable {X₀ : ℕ} {κ a : ℝ} {rhoA R ρAF Rp Rd : ℝ → ℝ} {L : ℝ}

lemma contPart_self (rhoA R : ℝ → ℝ) : contPart X₀ κ rhoA R X₀ = 0 := by
  simp [contPart]

lemma intervalIntegrable_rhoDet (hX1 : (1 : ℝ) ≤ X₀) (hκ : 0 < κ) (hκ1 : κ ≤ 1) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxa : x ≤ a) :
    IntervalIntegrable (rhoDet X₀ κ) volume X₀ x :=
  intervalIntegrable_of_eqOn (measurable_rhoDetF X₀ κ a) hx
    (fun t ht => rhoDet_eq_rhoDetF X₀ hκ (by linarith [ht.1]) (ht.2.trans hxa))
    (C := 3 / κ) (fun t ht => by
      have ht1 : 1 ≤ t := by linarith [ht.1]
      rw [← rhoDet_eq_rhoDetF X₀ hκ (by linarith) (ht.2.trans hxa),
        abs_of_nonneg (rhoDet_nonneg X₀ hκ (by linarith))]
      exact rhoDet_le X₀ hκ hκ1 ht1)

/-- The standing hypotheses on `ρ̄_A` and `R` on `[X₀, a]`. -/
structure ContHyp (X₀ : ℕ) (a : ℝ) (rhoA R ρAF Rp Rd : ℝ → ℝ) (L : ℝ) : Prop where
  rhoA_eq : ∀ v ∈ Icc (X₀ : ℝ) a, rhoA v = ρAF v
  rhoAF_meas : Measurable ρAF
  rhoA_nonneg : ∀ v ∈ Icc (X₀ : ℝ) a, 0 ≤ rhoA v
  rhoA_le : ∀ v ∈ Icc (X₀ : ℝ) a, rhoA v ≤ 1
  R_eq : ∀ x ∈ Icc (X₀ : ℝ) a, R x = Rp x
  Rd_meas : Measurable Rd
  Rd_le : ∀ x ∈ Icc (X₀ : ℝ) a, |Rd x| ≤ L
  ftc : ∀ u ∈ Icc (X₀ : ℝ) a, ∀ v ∈ Icc (X₀ : ℝ) a, u ≤ v → Rp v - Rp u = ∫ t in u..v, Rd t
  lip : ∀ u ∈ Icc (X₀ : ℝ) a, ∀ v ∈ Icc (X₀ : ℝ) a, u ≤ v → Rp v - Rp u ≤ L * (v - u)

lemma ContHyp.intervalIntegrable_rhoA (hc : ContHyp X₀ a rhoA R ρAF Rp Rd L) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxa : x ≤ a) : IntervalIntegrable rhoA volume X₀ x :=
  intervalIntegrable_of_eqOn hc.rhoAF_meas hx (fun t ht => hc.rhoA_eq t ⟨ht.1.le, ht.2.trans hxa⟩)
    (C := 1) (fun t ht => by
      have hmem : t ∈ Icc (X₀ : ℝ) a := ⟨ht.1.le, ht.2.trans hxa⟩
      rw [← hc.rhoA_eq t hmem, abs_of_nonneg (hc.rhoA_nonneg t hmem)]
      exact hc.rhoA_le t hmem)

/-- **`T_cont = ∫_{X₀}^x (1 - ρ_det - ρ̄_A + R')`** on `[X₀, a]`. -/
lemma ContHyp.contPart_eq (hc : ContHyp X₀ a rhoA R ρAF Rp Rd L) (hX1 : (1 : ℝ) ≤ X₀)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {x : ℝ} (hx : x ∈ Icc (X₀ : ℝ) a) :
    contPart X₀ κ rhoA R x = ∫ t in (X₀ : ℝ)..x, (1 - rhoDetF X₀ κ a t - ρAF t + Rd t) := by
  have hXa : (X₀ : ℝ) ≤ a := hx.1.trans hx.2
  have hXmem : (X₀ : ℝ) ∈ Icc (X₀ : ℝ) a := ⟨le_rfl, hXa⟩
  have i1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume X₀ x := intervalIntegrable_const
  have i2 : IntervalIntegrable (rhoDetF X₀ κ a) volume X₀ x :=
    (intervalIntegrable_rhoDet (a := a) hX1 hκ hκ1 hx.1 hx.2).congr
      (fun t ht => by
        rw [uIoc_of_le hx.1] at ht
        exact rhoDet_eq_rhoDetF X₀ hκ (by linarith [ht.1]) (ht.2.trans hx.2))
  have i3 : IntervalIntegrable ρAF volume X₀ x :=
    (hc.intervalIntegrable_rhoA hx.1 hx.2).congr
      (fun t ht => by
        rw [uIoc_of_le hx.1] at ht
        exact hc.rhoA_eq t ⟨ht.1.le, ht.2.trans hx.2⟩)
  have i4 : IntervalIntegrable Rd volume X₀ x :=
    intervalIntegrable_of_eqOn hc.Rd_meas hx.1 (fun _ _ => rfl) (C := L)
      (fun t ht => hc.Rd_le t ⟨ht.1.le, ht.2.trans hx.2⟩)
  have hnot : ¬ x < X₀ := not_lt.mpr hx.1
  unfold contPart
  rw [if_neg hnot, intervalIntegral.integral_add ((i1.sub i2).sub i3) i4,
    intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const, smul_eq_mul, mul_one,
    ← hc.ftc X₀ hXmem x hx hx.1, hc.R_eq x hx, hc.R_eq X₀ hXmem]
  have e1 : ∫ t in (X₀ : ℝ)..x, rhoDet X₀ κ t = ∫ t in (X₀ : ℝ)..x, rhoDetF X₀ κ a t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.1] at ht
    exact rhoDet_eq_rhoDetF X₀ hκ (by linarith [ht.1]) (ht.2.trans hx.2)
  have e2 : ∫ t in (X₀ : ℝ)..x, rhoA t = ∫ t in (X₀ : ℝ)..x, ρAF t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.1] at ht
    exact hc.rhoA_eq t ⟨ht.1, ht.2.trans hx.2⟩
  rw [e1, e2]

/-- **`T'_cont ≤ 1 + L`**: `T_cont(v) - T_cont(u) ≤ (1 + L)(v - u)` on `[X₀, a]`. -/
lemma ContHyp.contPart_sub_le (hc : ContHyp X₀ a rhoA R ρAF Rp Rd L) (hX1 : (1 : ℝ) ≤ X₀)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {u v : ℝ} (hu : (X₀ : ℝ) ≤ u) (huv : u ≤ v) (hva : v ≤ a) :
    contPart X₀ κ rhoA R v - contPart X₀ κ rhoA R u ≤ (1 + L) * (v - u) := by
  have hua : u ≤ a := huv.trans hva
  have hv : (X₀ : ℝ) ≤ v := hu.trans huv
  have humem : u ∈ Icc (X₀ : ℝ) a := ⟨hu, hua⟩
  have hvmem : v ∈ Icc (X₀ : ℝ) a := ⟨hv, hva⟩
  unfold contPart
  rw [if_neg (not_lt.mpr hu), if_neg (not_lt.mpr hv)]
  have hd1 : (∫ t in (X₀ : ℝ)..v, rhoDet X₀ κ t) - ∫ t in (X₀ : ℝ)..u, rhoDet X₀ κ t =
      ∫ t in u..v, rhoDet X₀ κ t :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_rhoDet hX1 hκ hκ1 hv hva)
      (intervalIntegrable_rhoDet hX1 hκ hκ1 hu hua)
  have hd2 : (∫ t in (X₀ : ℝ)..v, rhoA t) - ∫ t in (X₀ : ℝ)..u, rhoA t = ∫ t in u..v, rhoA t :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable_rhoA hv hva)
      (hc.intervalIntegrable_rhoA hu hua)
  have hp1 : 0 ≤ ∫ t in u..v, rhoDet X₀ κ t :=
    intervalIntegral.integral_nonneg huv fun t ht => rhoDet_nonneg X₀ hκ (by linarith [ht.1])
  have hp2 : 0 ≤ ∫ t in u..v, rhoA t :=
    intervalIntegral.integral_nonneg huv fun t ht =>
      hc.rhoA_nonneg t ⟨hu.trans ht.1, ht.2.trans hva⟩
  have hR := hc.lip u humem v hvmem huv
  rw [hc.R_eq u humem, hc.R_eq v hvmem]
  nlinarith

end Cont

/-! ### Lemma 4.8(ii) for the realised system -/

section Main

variable {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}

lemma residualLe_mono (h : RealisedOK M H U) {x y : ℝ} (hxy : x ≤ y) :
    residualLe h x ⊆ residualLe h y := by
  intro e he
  simp only [residualLe, Finset.mem_filter, BeurlingSystem.mem_elems] at he ⊢
  exact ⟨he.1.trans hxy, he.2⟩

lemma residualLe_eq_filter (h : RealisedOK M H U) {x y : ℝ} (hxy : x ≤ y) :
    residualLe h x = (residualLe h y).filter (fun e => (realisedSystem M H U).val e ≤ x) := by
  ext e
  simp only [residualLe, Finset.mem_filter, BeurlingSystem.mem_elems]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans hxy, h2⟩, h1⟩
  · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩

lemma heightScale_pos {θ κ₀ x : ℝ} (hκ₀ : 0 < κ₀) (hx : 1 < x) :
    0 < heightScale θ κ₀ x := by
  unfold heightScale
  have := Real.log_pos hx
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < x) (1 - θ)
  positivity

lemma oscLip_nonneg {θ α γ xp : ℝ} (hxp : 0 < xp) : 0 ≤ oscLip θ α γ xp := by
  unfold oscLip
  have := Real.rpow_pos_of_pos hxp (θ - 1)
  positivity

end Main

end Zeros48

end
