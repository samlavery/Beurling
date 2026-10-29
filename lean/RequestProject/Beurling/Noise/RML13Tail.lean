module

public import RequestProject.Beurling.Noise.RML13Grp

/-!
# Proposition 5.38, Step 4: the size of the grouped errors, and the field `h4`

The scales `v_j = X₀⁻ 2^j/2` meet the blocks `k₀(v_j) ∈ [j − 2, j]` (`k0_bS`), so every block
index occurs for at most five scales (`sum_mult_le`), and `log 3v_j ≤ 2 log 3u_i` on the
blocks met (`log_bS_le`). With Queue6's `∑ log(3u) ν(u) ≤ 200/Λ⁴`, `∑ log(3u) δ(u) ≤ 1/Λ⁴`:

  `27 ∑_j log(3v_j) ν'(v_j) + 4.3 ∑_j log(3v_j) δ'(v_j) ≤ 60000/Λ⁴` (`tail_le`).

Then Lemma 5.21 (`hS4_of`, through `Margin.Var.logt_omega_le`) gives the filtered field

  `log t (o(t) + 2η(t) + ∑_{w ∈ F} κ_w(t) e(t, w)/w) ≤ so + 2sη + 60000/Λ⁴`  (`h4_13`).
-/

@[expose] public section

open Finset Real Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML13

variable {θ : ℝ} {X₀ : ℕ}

/-- Five-fold multiplicity: if `i ∈ A j` forces `|i − j| ≤ 2`, then
`∑_{j<J} ∑_{i ∈ A j} f i ≤ 5 ∑_{i ∈ ⋃ A j} f i` for `f ≥ 0`. -/
lemma sum_mult_le (J : ℕ) (A : ℕ → Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hA : ∀ j i, i ∈ A j → j ≤ i + 2 ∧ i ≤ j + 2) :
    ∑ j ∈ range J, ∑ i ∈ A j, f i ≤ 5 * ∑ i ∈ (range J).biUnion A, f i := by
  classical
  set T := (range J).biUnion A
  have h1 : ∀ j ∈ range J, ∑ i ∈ A j, f i = ∑ i ∈ T, if i ∈ A j then f i else 0 := by
    intro j hj
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, T, Finset.mem_biUnion]
    exact ⟨fun h => ⟨⟨j, hj, h⟩, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf i)
  have hsub : (range J).filter (fun j => i ∈ A j) ⊆ Icc (i - 2) (i + 2) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have := hA j i hj.2
    rw [Finset.mem_Icc]; omega
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  have h5 : i + 2 + 1 - (i - 2) ≤ 5 := by omega
  exact_mod_cast this.trans h5

section Tail

variable (hc : Cond θ X₀)
include hc

omit hc in
lemma uS_eq (j : ℕ) : uS X₀ j = 2 ^ j * X₀ := rfl

/-- `k₀(v_j) ∈ [j − 2, j]`. -/
lemma k0_bS (j : ℕ) : j - 2 ≤ k0 X₀ (bS X₀ j) ∧ k0 X₀ (bS X₀ j) ≤ j := by
  have hX0 := X0_pos hc
  obtain ⟨hXm1, hXm2⟩ := Xm_bounds hc
  have hloX : (X₀ : ℝ) ≤ loB X₀ (bS X₀ j) := le_max_right _ _
  obtain ⟨h1, h2⟩ := mB_spec hX0 hloX
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hb1 : bS X₀ j ≤ (X₀ : ℝ) / 2 * 2 ^ j := by
    unfold bS; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hb2 : 0.99 * (X₀ : ℝ) / 2 * 2 ^ j ≤ bS X₀ j := by
    unfold bS; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  unfold k0
  constructor
  · by_contra hcon
    push_neg at hcon
    have h3 := uS_mono (X₀ := X₀) (show mB X₀ (loB X₀ (bS X₀ j)) + 1 + 2 ≤ j by omega)
    rw [uS_add] at h3
    norm_num at h3
    have h4 : 0.848 * bS X₀ j ≤ loB X₀ (bS X₀ j) := le_max_left _ _
    have hQ : uS X₀ j = 2 ^ j * X₀ := rfl
    have hb3 : 0.495 * (2 ^ j * (X₀ : ℝ)) ≤ bS X₀ j := by nlinarith
    have hQ0 : 0 < 2 ^ j * (X₀ : ℝ) := by positivity
    linarith
  · by_contra hcon
    push_neg at hcon
    have h3 := uS_mono (X₀ := X₀) (show j + 1 ≤ mB X₀ (loB X₀ (bS X₀ j)) by omega)
    rw [uS_eq, pow_succ] at h3
    have h4 : loB X₀ (bS X₀ j) ≤ max ((X₀ : ℝ) / 2 * 2 ^ j) X₀ :=
      max_le_max (by nlinarith) le_rfl
    have h5 : max ((X₀ : ℝ) / 2 * 2 ^ j) X₀ < 2 ^ j * 2 * X₀ :=
      max_lt (by nlinarith) (by nlinarith)
    linarith

/-- `log 3v_j ≤ 2 log 3u_i` for the blocks `i ≥ k₀(v_j)`. -/
lemma log_bS_le {j i : ℕ} (hi : k0 X₀ (bS X₀ j) ≤ i) :
    Real.log (3 * bS X₀ j) ≤ 2 * Real.log (3 * uS X₀ i) := by
  have hX0 := X0_pos hc
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hloX : (X₀ : ℝ) ≤ loB X₀ (bS X₀ j) := le_max_right _ _
  obtain ⟨-, h2⟩ := mB_spec hX0 hloX
  rw [uS_succ] at h2
  have h3 := uS_mono (X₀ := X₀) hi
  have h4 : 0.848 * bS X₀ j ≤ loB X₀ (bS X₀ j) := le_max_left _ _
  have hu := (uS_facts hc i).1
  have hb := bS_pos hc j
  have hle : 3 * bS X₀ j ≤ (3 * uS X₀ i) ^ 2 := by
    unfold k0 at h3; nlinarith
  rw [← Real.log_rpow (by linarith)]
  refine Real.log_le_log (by linarith) ?_
  norm_num; exact hle

/-- **The size of Step 4**: `27 ∑ log(3v) ν'(v) + 4.3 ∑ log(3v) δ'(v) ≤ 60000/Λ⁴`. -/
theorem tail_le (J : ℕ) :
    27 * ∑ j ∈ range J, Real.log (3 * bS X₀ j) * nu13 X₀ (bS X₀ j) +
      4.3 * ∑ j ∈ range J, Real.log (3 * bS X₀ j) * dl13 X₀ (bS X₀ j) ≤
      60000 / Real.log X₀ ^ 4 := by
  set A : ℕ → Finset ℕ := fun j => Icc (k0 X₀ (bS X₀ j)) (k0 X₀ (bS X₀ j) + 2)
  have hA : ∀ j i, i ∈ A j → j ≤ i + 2 ∧ i ≤ j + 2 := by
    intro j i hi
    have := k0_bS hc j
    simp only [A, Finset.mem_Icc] at hi
    omega
  have hL : ∀ i, 0 ≤ Real.log (3 * uS X₀ i) := fun i => by
    have := (uS_facts hc i).2.1
    have hu := (uS_facts hc i).1
    have := Real.log_le_log (by linarith [X0_pos hc]) (show uS X₀ i ≤ 3 * uS X₀ i by linarith)
    linarith
  have key : ∀ g : ℝ → ℝ, (∀ i, 0 ≤ g (uS X₀ i)) →
      ∑ j ∈ range J, Real.log (3 * bS X₀ j) * ∑ i ∈ A j, g (uS X₀ i) ≤
        2 * (5 * ∑ i ∈ (range J).biUnion A, Real.log (3 * uS X₀ i) * g (uS X₀ i)) := by
    intro g hg
    have h1 : ∑ j ∈ range J, Real.log (3 * bS X₀ j) * ∑ i ∈ A j, g (uS X₀ i) ≤
        ∑ j ∈ range J, ∑ i ∈ A j, 2 * (Real.log (3 * uS X₀ i) * g (uS X₀ i)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have := log_bS_le hc (j := j) (i := i) (Finset.mem_Icc.mp hi).1
      nlinarith [hg i]
    refine h1.trans ?_
    simp_rw [← Finset.mul_sum]
    have := sum_mult_le J A (fun i => Real.log (3 * uS X₀ i) * g (uS X₀ i))
      (fun i => mul_nonneg (hL i) (hg i)) hA
    linarith
  have hν := key (nuQ X₀) fun i => Queue6.nuQ_nonneg hc (uS_facts hc i).1
  have hδ := key (dQ X₀) fun i => Queue6.dQ_nonneg (X₀ := X₀) (RML10.one_le_uS hc.hX i)
  have hν' := Queue6.sum_nuQ_le hc ((range J).biUnion A)
  have hδ' := Queue6.sum_dQ_le hc ((range J).biUnion A)
  have hΛ : 0 < Real.log X₀ ^ 4 := by have := hc.hX; positivity
  have e1 : 200 / Real.log X₀ ^ 4 * 54000 / 200 = 54000 / Real.log X₀ ^ 4 := by ring
  have e2 : 1 / Real.log X₀ ^ 4 * 43 = 43 / Real.log X₀ ^ 4 := by ring
  have e3 : 54000 / Real.log X₀ ^ 4 + 43 / Real.log X₀ ^ 4 ≤ 60000 / Real.log X₀ ^ 4 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hΛ.le
  unfold nu13 dl13
  nlinarith

omit hc in
lemma bS_strictMono (hXm : 0 < Xm X₀) : StrictMono (bS X₀) := fun a b hab => by
  unfold bS
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hab) (by linarith)

/-- **The field `h4` of Proposition 5.38, Step 4, with the filter `κ_w(t)`** (04g Step 3:
the error sum `S(t)` runs over the cofactors with `κ_w(t) = 1`), at `e = e12` at any
`m* ≤ 3.1 log(max z X₀) + 4.2` (on `z ≤ b`) and any `ES ≥ so + 2sη + 60000/Λ⁴`. Inputs:
the (TNP) hypothesis at the horizon `Z ≥ max(X₀⁻, 2b/X₀⁻)`, and the oscillation/average
bounds `log t · o(t) ≤ so`, `log t · η(t) ≤ sη` on `[T₀, b]`. -/
theorem h4_13 (ω : JitterΩ) {Z η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ} {Mf : ℝ → ℝ}
    (hM0 : ∀ z, 0 ≤ Mf z) (hMm : Monotone Mf) {b : ℝ}
    (hMB : ∀ z, z ≤ b → Mf z ≤ 3.1 * Real.log (max z X₀) + 4.2)
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT)
    (ES jP so sη : ℝ) (hZ : Xm X₀ ≤ Z) (hbZ : 2 * b / Xm X₀ ≤ Z)
    (ho : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → Real.log t * oVc θ X₀ ω t ≤ so)
    (hη : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → Real.log t * ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP) t ≤ sη)
    (hES : so + 2 * sη + 60000 / Real.log X₀ ^ 4 ≤ ES) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      Real.log t * (oVc θ X₀ ω t + 2 * ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP) t +
        ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
            (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w)) ≤ ES := by
  intro t ht htb
  have h1 := RML10.T0_gt_one hc.hX ES jP
  have ht1 : 1 < t := by linarith
  have hX0 := X0_pos hc
  obtain ⟨hXm1, -⟩ := Xm_bounds hc
  have hXm : 0 < Xm X₀ := by linarith
  have hp2 := KR.Chain.p_ge_two_of htnp hZ
  obtain ⟨J, hJ'⟩ := pow_unbounded_of_one_lt (t / (Xm X₀ / 2)) (by norm_num : (1 : ℝ) < 2)
  have hJ : t ≤ Xm X₀ / 2 * 2 ^ J := by
    rw [div_lt_iff₀ (by linarith)] at hJ'; linarith
  have hS := hS_kap hc hM0 hMm hMB ω hp2 hJ (by linarith) ES jP
  set om := fun v => (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v
  have hinj' : Set.InjOn (bS X₀) ↑(range J) := (bS_strictMono hXm).injective.injOn
  have hω : ∀ v ∈ (range J).image (bS X₀), Real.log t * om v ≤ 2.9 * Real.log (3 * v) := by
    intro v hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    have hb := bS_ge hc j
    have hv0 := bS_pos hc j
    have hL : 100000000 ≤ Real.log (3 * bS X₀ j) := by
      have := Real.log_le_log hX0 (show (X₀ : ℝ) ≤ 3 * bS X₀ j by linarith)
      have := hc.hX; norm_num at this ⊢; linarith
    have hZj : t / bS X₀ j ≤ Z := by
      have e1 : t / bS X₀ j ≤ t / (Xm X₀ / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) hb
      have e2 : t / (Xm X₀ / 2) ≤ 2 * b / Xm X₀ := by
        rw [div_div_eq_mul_div, mul_comm]
        exact div_le_div_of_nonneg_right (by linarith) hXm.le
      linarith
    exact Margin.Var.logt_omega_le htnp.hbs (KR.RML7G.decidedSmall_of htnp hv0) hv0 hL
      (by linarith) hZj
  have hS' : oVc θ X₀ ω t + 2 * ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP) t +
      ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
        Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
          (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w) ≤
      oVc θ X₀ ω t + 2 * ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP) t +
        4 * ∑ v ∈ (range J).image (bS X₀), om v * nu13 X₀ v +
        1.0001 * ∑ v ∈ (range J).image (bS X₀), om v * dl13 X₀ v := by
    rw [Finset.sum_image hinj', Finset.sum_image hinj']
    have e1 : ∑ j ∈ range J, om (bS X₀ j) * (2 * nu13 X₀ (bS X₀ j) + dl13 X₀ (bS X₀ j)) =
        2 * ∑ j ∈ range J, om (bS X₀ j) * nu13 X₀ (bS X₀ j) +
          ∑ j ∈ range J, om (bS X₀ j) * dl13 X₀ (bS X₀ j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : 0 ≤ ∑ j ∈ range J, om (bS X₀ j) * nu13 X₀ (bS X₀ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (RML11.omegaW_nonneg _ _ _ _) (nu13_nonneg hc _)
    have e3 : 0 ≤ ∑ j ∈ range J, om (bS X₀ j) * dl13 X₀ (bS X₀ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (RML11.omegaW_nonneg _ _ _ _) (dl13_nonneg hc _)
    have := hS.trans_eq e1
    linarith
  have hES' : so + 2 * sη + 27 * ∑ v ∈ (range J).image (bS X₀), Real.log (3 * v) * nu13 X₀ v +
      4.3 * ∑ v ∈ (range J).image (bS X₀), Real.log (3 * v) * dl13 X₀ v ≤ ES := by
    rw [Finset.sum_image hinj', Finset.sum_image hinj']
    have := tail_le hc J
    linarith
  have key := Margin.RML6.hS4_of ((range J).image (bS X₀)) om (nu13 X₀) (dl13 X₀) ht1
    (ho t ht htb) (hη t ht htb) (fun v _ => nu13_nonneg hc v) (fun v _ => dl13_nonneg hc v)
    (fun v _ => RML11.omegaW_nonneg _ _ _ _) hω hS' hES'
  have hlt : 0 < Real.log t := Real.log_pos ht1
  rw [le_div_iff₀ hlt] at key
  linarith

end Tail

end BModel.RML13

end
