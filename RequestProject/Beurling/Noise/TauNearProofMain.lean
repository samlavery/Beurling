module

public import RequestProject.Beurling.Noise.TauNearProofBlk
public import RequestProject.Beurling.Noise.TauNear
public import RequestProject.Beurling.Noise.BridgeNear

/-!
# Lemma 5.20 (`τ`-near energy)

Under the hypotheses `TNP.Hyp` (HBS, `PaperWidth`, the decision order, and the local count of
Corollary 6.3(ii) as used in the proof), for a `2`-separated finite family of scales `Sc`
(`TNP.Sep`; e.g. dyadic scales), with `18 v ≤ Z` and `√(2v) ≤ P_K` on `Sc`:

* `etaBound_energy` : **Lemma 5.20 for `E_η`**: `TauNearEnergy P H tw X₀⁻ (X₀⁻/2) Sc s̃` with the
  scale bounds `s̃ = blk … (1/(log P_k - 0.18))`; in fact
  `E_η = ∑_v log(2v) s̃_v ≤ 2.494·10⁶ Φ₁(X₀⁻/2) ≤ 10⁴ H(X₀⁻/2) log²(X₀⁻/2)/(X₀⁻/2)`;
* `etaBlk_sum` : **Lemma 5.20 for `E⁰_η`** in the block form `EtaBlk`:
  `∑_v s_v ≤ 6.234·10⁵ Φ₁(X₀⁻/2)`;
* `thetaBlk_sum` : **Lemma 5.20 for `E_θ`**: `ThetaBlk` with `∑_v log(2v) th_v ≤
  2.494·10⁶ Φ₃(X₀⁻/2)`;
* `thetaStar_on` : **Lemma 5.20 for `θ_*`** at every height `y` with `9y ≤ Z`:
  `θ(y) ≤ 2.078·10⁵ Φ₂(X₀⁻/2)`.

Here `Φ_a(P) = H(P)(log P + 2)^a/P`. The paper states the bounds with `H(X₀) log²X₀/X₀`; we keep
the explicit `Φ_a(X₀⁻/2)` (the powers of `log` are the paper's or better, the constants are
cruder), and `energy_numeric`-type bounds make all of them `≤ e^{-0.99Λ}`-small for the standard
width.

The statement `ThetaStar` (`θ(v) ≤ θ_*` for every real `v`) is not derivable from (HBS) on
`[1, Z]`, which does not see the system above `Z`; `thetaStar_on` is the bound at the heights
`9y ≤ Z`, which are the heights at which the proofs evaluate `θ`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-! ## Sizes of the dyadic scales -/

lemma Pk_ge (hX : 0 < X0m) (k : ℕ) : X0m / 2 ≤ Pk X0m k := by
  unfold Pk; have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); nlinarith

lemma log_Pk_ge (hX : 0 < X0m) (hXm : 100000000 ≤ Real.log X0m) (k : ℕ) :
    10000000 ≤ Real.log (Pk X0m k) := by
  have h1 : Real.log (X0m / 2) ≤ Real.log (Pk X0m k) :=
    Real.log_le_log (by positivity) (Pk_ge hX k)
  have h2 : Real.log (X0m / 2) = Real.log X0m - Real.log 2 := Real.log_div hX.ne' (by norm_num)
  have := Real.log_two_lt_d9
  linarith

lemma Pk_ge_one (hX : 0 < X0m) (hXm : 100000000 ≤ Real.log X0m) (k : ℕ) : 1 ≤ Pk X0m k := by
  have := log_Pk_ge hX hXm k
  by_contra hc; push_neg at hc
  have := Real.log_neg (Pk_pos hX k) hc
  linarith

lemma log_three_mul_le (hX : 0 < X0m) (k : ℕ) :
    Real.log (3 * Pk X0m k) ≤ Real.log (Pk X0m k) + 1.1 := by
  rw [Real.log_mul (by norm_num) (Pk_pos hX k).ne']
  have : Real.log 3 < 1.1 := by
    have h1 : (1.025 : ℝ) ≤ Real.exp 0.025 := by linarith [Real.add_one_le_exp (0.025 : ℝ)]
    have h2 : Real.exp 0.1 = Real.exp 0.025 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (1.025 : ℝ) ^ 4 ≤ Real.exp 0.025 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
    have h4 : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
    have h5 : (3 : ℝ) < Real.exp 1.1 := by
      rw [h4, h2]; nlinarith [Real.exp_pos 1, pow_pos (Real.exp_pos 0.025) 4]
    calc Real.log 3 < Real.log (Real.exp 1.1) := Real.log_lt_log (by norm_num) h5
      _ = 1.1 := Real.log_exp _
  linarith

lemma Pk_zero (X0m : ℝ) : Pk X0m 0 = X0m / 2 := by simp [Pk]

lemma exists_K (hX : 0 < X0m) (A : ℝ) : ∃ K, A ≤ Pk X0m K := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (A / (X0m / 2)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, ?_⟩
  unfold Pk
  rw [div_lt_iff₀ (by positivity)] at hK
  linarith

/-! ## `E⁰_η`: the block sums of `η` -/

/-- **Lemma 5.20, `E⁰_η`, block form**: the blocks `s_v = blk … 1` bound `η` on `[v, 2v)`, and
`∑_v s_v ≤ 623400 Φ₁(X₀⁻/2)`. -/
theorem etaBlk_sum (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 0 < v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) :
    EtaBlk P H tw X0m Sc (blk P H X0m K fun _ => 1) ∧
      ∑ v ∈ Sc, blk P H X0m K (fun _ => 1) v ≤ 623400 * Phi H 1 (X0m / 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  refine ⟨fun v hv => ⟨blk_nonneg hP K (fun _ => zero_le_one) v, fun y hvy hy =>
    blk_ge h (hSc v hv) hvy hy (hK v hv) (fun _ => zero_le_one)
      (fun _ _ _ _ _ => le_rfl)⟩, ?_⟩
  unfold blk
  rw [Finset.sum_comm]
  calc ∑ k ∈ range K, ∑ v ∈ Sc, 56 * H (Pk X0m k) * 1 / Pk X0m k *
        ∑ e ∈ SmB P X0m k v, 1 / P.val e
      = ∑ k ∈ range K, 56 * H (Pk X0m k) / Pk X0m k *
          ∑ v ∈ Sc, 1 * ∑ e ∈ SmB P X0m k v, 1 / P.val e := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ∑ k ∈ range K, 56 * H (Pk X0m k) / Pk X0m k *
          (3 * ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := hP.reg.pos (Pk X0m k); have := Pk_pos hX k
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact scale_sum (Lb := fun _ => 1) hX hS k (fun _ _ => zero_le_one)
          (fun _ _ _ _ => le_rfl)
    _ ≤ ∑ k ∈ range K, 304080 * Phi H 1 (Pk X0m k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk1 := Pk_ge_one hX h.hXm k
        have hu := U_harm (Sc := Sc) h.hbs hP hZ k hk1
        have hl3 := log_three_mul_le hX k
        have hHk := hP.reg.pos (Pk X0m k)
        have hk0 := Pk_pos hX k
        have hl := log_Pk_ge hX h.hXm k
        unfold Phi
        rw [pow_one]
        have hc : 0 ≤ 56 * H (Pk X0m k) / Pk X0m k := by positivity
        calc 56 * H (Pk X0m k) / Pk X0m k * (3 * ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e)
            ≤ 56 * H (Pk X0m k) / Pk X0m k * (3 * (1810 * (Real.log (Pk X0m k) + 2))) := by
              apply mul_le_mul_of_nonneg_left _ hc; nlinarith
          _ = 304080 * (H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k) := by ring
    _ ≤ 623400 * Phi H 1 (X0m / 2) := by
        rw [← Finset.mul_sum, ← Pk_zero]
        have := decay_sum hP h.hXm (a := 1) (by norm_num) K
        have := Phi_nonneg hP 1 (Pk_ge hX 0) (Pk_ge_one hX h.hXm 0)
        nlinarith

/-! ## `θ_*` -/

/-- **Lemma 5.20, `θ_*`**, at every height `y > 0` with `9y ≤ Z`:
`θ(y) = ∑_{w τ-near at y} (log(y/w) + 1)/w ≤ 207800 Φ₂(X₀⁻/2)`. -/
theorem thetaStar_on (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {y : ℝ} (hy : 0 < y)
    (hZ : 9 * y ≤ Z) :
    etaG P H tw X0m (fun c => Real.log c + 1) y ≤ 207800 * Phi H 2 (X0m / 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  obtain ⟨K, hK⟩ := exists_K hX (√y + 1)
  have hΨ0 : ∀ k, 0 ≤ Real.log (Pk X0m k) + 2 := fun k => by
    have := log_Pk_ge hX h.hXm k; linarith
  have hψ : ∀ k < K, ∀ c, 0.85 * Pk X0m k ≤ c → c ≤ 2.42 * Pk X0m k →
      Real.log c + 1 ≤ Real.log (Pk X0m k) + 2 := by
    intro k _ c hc1 hc2
    have hk0 := Pk_pos hX k
    have hc0 : 0 < c := by linarith
    have : Real.log c ≤ Real.log (2.42 * Pk X0m k) := Real.log_le_log hc0 hc2
    rw [Real.log_mul (by norm_num) hk0.ne'] at this
    have : Real.log 2.42 ≤ 0.91 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2.42 / 2 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this
      have := Real.log_two_lt_d9
      linarith
    linarith
  refine (etaG_le_blocks h hy (by linarith) hΨ0 hψ).trans ?_
  calc ∑ k ∈ range K, 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
        ∑ e ∈ Sm P X0m k y, 1 / P.val e
      ≤ ∑ k ∈ range K, 101360 * Phi H 2 (Pk X0m k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk1 := Pk_ge_one hX h.hXm k
        have hk0 := Pk_pos hX k
        have hl3 := log_three_mul_le hX k
        have hl := log_Pk_ge hX h.hXm k
        have hHk := hP.reg.pos (Pk X0m k)
        have hsm : ∑ e ∈ Sm P X0m k y, 1 / P.val e ≤ 1810 * Real.log (3 * Pk X0m k) := by
          rcases (Sm P X0m k y).eq_empty_or_nonempty with he | ⟨e, he⟩
          · rw [he, Finset.sum_empty]
            have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
          · have hz : (3 * Pk X0m k) ^ 2 ≤ Z := by
              simp only [Sm, Finset.mem_filter, mem_elems] at he
              have h1 := (P.one_le_val e).trans he.1
              rw [le_div_iff₀ (by positivity)] at h1
              nlinarith
            refine smooth_harm_le h.hbs (by linarith) hz _ ?_
            intro e he i hi
            simp only [Sm, Finset.mem_filter] at he
            exact he.2.2 i hi
        unfold Phi
        have hc : 0 ≤ 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k := by
          have := hΨ0 k; positivity
        calc 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
              ∑ e ∈ Sm P X0m k y, 1 / P.val e
            ≤ 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
                (1810 * (Real.log (Pk X0m k) + 2)) := by
              apply mul_le_mul_of_nonneg_left _ hc; nlinarith
          _ = 101360 * (H (Pk X0m k) * (Real.log (Pk X0m k) + 2) ^ 2 / Pk X0m k) := by ring
    _ ≤ 207800 * Phi H 2 (X0m / 2) := by
        rw [← Finset.mul_sum, ← Pk_zero]
        have := decay_sum hP h.hXm (a := 2) (by norm_num) K
        have := Phi_nonneg hP 2 (Pk_ge hX 0) (Pk_ge_one hX h.hXm 0)
        nlinarith

/-! ## The log-weighted scale sums (`E_η`, `E_θ`) -/

/-- `∑_v log(2v) ∑_{m ∈ SmB_k(v)} 1/m ≤ 3 · 7240.1 (log P_k + 2)²`. -/
theorem log_scale_sum (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) (k : ℕ) :
    ∑ v ∈ Sc, Real.log (2 * v) * ∑ e ∈ SmB P X0m k v, 1 / P.val e ≤
      3 * (7240.1 * (Real.log (Pk X0m k) + 2) ^ 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hk0 := Pk_pos hX k
  have hk1 := Pk_ge_one hX h.hXm k
  set Lb : ℝ → ℝ := fun m => Real.log 8 + 2 * Real.log (Pk X0m k) + Real.log m
  have hLb : ∀ v ∈ Sc, ∀ e ∈ SmB P X0m k v, Real.log (2 * v) ≤ Lb (P.val e) := by
    intro v hv e he
    simp only [SmB, Finset.mem_filter] at he
    have h1 := he.2.1
    rw [div_lt_iff₀ (by positivity)] at h1
    have hve := P.val_pos e
    have hv0 : 0 < v := by linarith [hSc v hv]
    have h2 : Real.log (2 * v) ≤ Real.log (8 * Pk X0m k ^ 2 * P.val e) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h3 : Real.log (8 * Pk X0m k ^ 2 * P.val e) =
        Real.log 8 + 2 * Real.log (Pk X0m k) + Real.log (P.val e) := by
      rw [Real.log_mul (by positivity) hve.ne', Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast; ring
    simp only [Lb]; linarith
  have hsum := scale_sum hX hS k (fun v hv => Real.log_nonneg (by linarith [hSc v hv])) hLb
  refine hsum.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsplit : ∑ e ∈ Sc.biUnion (SmB P X0m k), Lb (P.val e) / P.val e =
      (Real.log 8 + 2 * Real.log (Pk X0m k)) * ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e +
        ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) / P.val e := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by simp only [Lb]; ring
  rw [hsplit]
  have hu := U_harm (Sc := Sc) h.hbs hP hZ k hk1
  have hul := U_logharm (Sc := Sc) h.hbs hP hZ k hk1
  have hl3 := log_three_mul_le hX k
  have hl := log_Pk_ge hX h.hXm k
  have hl8 : Real.log 8 ≤ 2.08 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hl80 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hl30 : 0 ≤ Real.log (3 * Pk X0m k) := Real.log_nonneg (by linarith)
  set ℓ := Real.log (Pk X0m k)
  set ℓ3 := Real.log (3 * Pk X0m k)
  have hA : (Real.log 8 + 2 * ℓ) * ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e ≤
      (2.08 + 2 * ℓ) * (1810 * (ℓ + 1.1)) := by
    apply mul_le_mul (by linarith) (hu.trans (by nlinarith)) (Finset.sum_nonneg fun e _ =>
      (one_div_pos.mpr (P.val_pos e)).le) (by linarith)
  have hB : ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) / P.val e ≤
      3620 * (ℓ + 1.1) * (ℓ + 1.53) := by
    refine hul.trans ?_
    have : ℓ3 + 0.43 ≤ ℓ + 1.53 := by linarith
    have : 3620 * ℓ3 ≤ 3620 * (ℓ + 1.1) := by linarith
    nlinarith
  nlinarith

/-- **Lemma 5.20, `E_θ`**: `ThetaBlk` with the blocks `th_v = blk … (log P_k + 2)`, and
`E_θ = ∑_v log(2v) th_v ≤ 2493700 Φ₃(X₀⁻/2)`. -/
theorem thetaBlk_sum (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) :
    ThetaBlk P H tw X0m Sc (blk P H X0m K fun k => Real.log (Pk X0m k) + 2) ∧
      ∑ v ∈ Sc, Real.log (2 * v) * blk P H X0m K (fun k => Real.log (Pk X0m k) + 2) v ≤
        2493700 * Phi H 3 (X0m / 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hΨ0 : ∀ k, 0 ≤ Real.log (Pk X0m k) + 2 := fun k => by
    have := log_Pk_ge hX h.hXm k; linarith
  have hψ : ∀ k < K, ∀ c, 0.85 * Pk X0m k ≤ c → c ≤ 2.42 * Pk X0m k →
      Real.log c + 1 ≤ Real.log (Pk X0m k) + 2 := by
    intro k _ c hc1 hc2
    have hk0 := Pk_pos hX k
    have hc0 : 0 < c := by linarith
    have : Real.log c ≤ Real.log (2.42 * Pk X0m k) := Real.log_le_log hc0 hc2
    rw [Real.log_mul (by norm_num) hk0.ne'] at this
    have : Real.log 2.42 ≤ 0.91 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2.42 / 2 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this
      have := Real.log_two_lt_d9
      linarith
    linarith
  refine ⟨fun v hv => ⟨blk_nonneg hP K hΨ0 v, fun y hvy hy =>
    blk_ge h (by linarith [hSc v hv]) hvy hy (hK v hv) hΨ0 hψ⟩, ?_⟩
  unfold blk
  calc ∑ v ∈ Sc, Real.log (2 * v) * ∑ k ∈ range K, 56 * H (Pk X0m k) *
        (Real.log (Pk X0m k) + 2) / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e
      = ∑ k ∈ range K, 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
          ∑ v ∈ Sc, Real.log (2 * v) * ∑ e ∈ SmB P X0m k v, 1 / P.val e := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ k ∈ range K, 1216400 * Phi H 3 (Pk X0m k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hc : 0 ≤ 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k := by
          have := hP.reg.pos (Pk X0m k); have := Pk_pos hX k; have := hΨ0 k; positivity
        have hls := log_scale_sum h hS hSc hZ k
        have hk0 := Pk_pos hX k
        have hHk := hP.reg.pos (Pk X0m k)
        have hl0 := hΨ0 k
        calc 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
              ∑ v ∈ Sc, Real.log (2 * v) * ∑ e ∈ SmB P X0m k v, 1 / P.val e
            ≤ 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
                (3 * (7240.1 * (Real.log (Pk X0m k) + 2) ^ 2)) :=
              mul_le_mul_of_nonneg_left hls hc
          _ ≤ 1216400 * Phi H 3 (Pk X0m k) := by
              unfold Phi
              rw [show 56 * H (Pk X0m k) * (Real.log (Pk X0m k) + 2) / Pk X0m k *
                (3 * (7240.1 * (Real.log (Pk X0m k) + 2) ^ 2)) =
                1216336.8 * (H (Pk X0m k) * (Real.log (Pk X0m k) + 2) ^ 3 / Pk X0m k) by ring]
              have : 0 ≤ H (Pk X0m k) * (Real.log (Pk X0m k) + 2) ^ 3 / Pk X0m k := by
                positivity
              nlinarith
    _ ≤ 2493700 * Phi H 3 (X0m / 2) := by
        rw [← Finset.mul_sum, ← Pk_zero]
        have := decay_sum hP h.hXm (a := 3) (by norm_num) K
        have := Phi_nonneg hP 3 (Pk_ge hX 0) (Pk_ge_one hX h.hXm 0)
        nlinarith

/-! ## `E_η`: Lemma 5.20 as `TauNearEnergy` -/

/-- `η̃ = ∑_{w τ-near} ψ(v/w)/w` with `ψ(c) = 1/log c`. -/
lemma etaT_eq_etaG (v : ℝ) :
    etaT P H tw X0m v = etaG P H tw X0m (fun c => 1 / Real.log c) v := by
  unfold etaT etaG
  exact Finset.sum_congr rfl fun m _ => by rw [div_div, mul_comm]

/-- **Lemma 5.20 (`τ`-near energy), `E_η`**: the blocks `s̃_v = blk … (1/(log P_k - 0.18))`
bound `η̃` on `[v, 2v)` (`EtaBound`), and `E_η = ∑_v log(2v) s̃_v ≤ 2493900 Φ₁(X₀⁻/2)`; hence
`TauNearEnergy` holds at `X₀ := X₀⁻/2`. -/
theorem etaBound_energy (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {Sc : Finset ℝ} (hS : Sep Sc)
    (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ Pk X0m K) :
    EtaBound P H tw X0m Sc (blk P H X0m K fun k => 1 / (Real.log (Pk X0m k) - 0.18)) ∧
      ∑ v ∈ Sc, Real.log (2 * v) *
          blk P H X0m K (fun k => 1 / (Real.log (Pk X0m k) - 0.18)) v ≤
        2493900 * Phi H 1 (X0m / 2) ∧
      TauNearEnergy P H tw X0m (X0m / 2) Sc
        (blk P H X0m K fun k => 1 / (Real.log (Pk X0m k) - 0.18)) := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hΨ0 : ∀ k, 0 ≤ 1 / (Real.log (Pk X0m k) - 0.18) := fun k => by
    have := log_Pk_ge hX h.hXm k
    exact (one_div_pos.mpr (by linarith)).le
  have hψ : ∀ k < K, ∀ c, 0.85 * Pk X0m k ≤ c → c ≤ 2.42 * Pk X0m k →
      1 / Real.log c ≤ 1 / (Real.log (Pk X0m k) - 0.18) := by
    intro k _ c hc1 _
    have hk0 := Pk_pos hX k
    have hl := log_Pk_ge hX h.hXm k
    have hc0 : 0 < c := by linarith
    have h1 : Real.log (0.85 * Pk X0m k) ≤ Real.log c := Real.log_le_log (by positivity) hc1
    rw [Real.log_mul (by norm_num) hk0.ne'] at h1
    have h085 : -0.18 ≤ Real.log 0.85 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.85 by norm_num)
      have : (1 : ℝ) - 0.85⁻¹ ≥ -0.18 := by norm_num
      linarith
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hEB : EtaBound P H tw X0m Sc
      (blk P H X0m K fun k => 1 / (Real.log (Pk X0m k) - 0.18)) := by
    intro v hv
    refine ⟨blk_nonneg hP K hΨ0 v, fun y hvy hy => ?_⟩
    rw [etaT_eq_etaG]
    exact blk_ge h (by linarith [hSc v hv]) hvy hy (hK v hv) hΨ0 hψ
  have hsum : ∑ v ∈ Sc, Real.log (2 * v) *
      blk P H X0m K (fun k => 1 / (Real.log (Pk X0m k) - 0.18)) v ≤
      2493900 * Phi H 1 (X0m / 2) := by
    unfold blk
    calc ∑ v ∈ Sc, Real.log (2 * v) * ∑ k ∈ range K, 56 * H (Pk X0m k) *
          (1 / (Real.log (Pk X0m k) - 0.18)) / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e
        = ∑ k ∈ range K, 56 * H (Pk X0m k) * (1 / (Real.log (Pk X0m k) - 0.18)) / Pk X0m k *
            ∑ v ∈ Sc, Real.log (2 * v) * ∑ e ∈ SmB P X0m k v, 1 / P.val e := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ =>
            Finset.sum_congr rfl fun e _ => by ring
      _ ≤ ∑ k ∈ range K, 1216500 * Phi H 1 (Pk X0m k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hc : 0 ≤ 56 * H (Pk X0m k) * (1 / (Real.log (Pk X0m k) - 0.18)) / Pk X0m k := by
            have := hP.reg.pos (Pk X0m k); have := Pk_pos hX k; have := hΨ0 k; positivity
          have hls := log_scale_sum h hS hSc hZ k
          have hk0 := Pk_pos hX k
          have hHk := hP.reg.pos (Pk X0m k)
          have hl := log_Pk_ge hX h.hXm k
          refine (mul_le_mul_of_nonneg_left hls hc).trans ?_
          unfold Phi
          rw [pow_one]
          set ℓ := Real.log (Pk X0m k)
          have hℓ : 0 < ℓ - 0.18 := by linarith
          have hq : (ℓ + 2) ^ 2 / (ℓ - 0.18) ≤ 1.00001 * (ℓ + 2) := by
            rw [div_le_iff₀ hℓ]; nlinarith
          rw [show 56 * H (Pk X0m k) * (1 / (ℓ - 0.18)) / Pk X0m k *
              (3 * (7240.1 * (ℓ + 2) ^ 2)) =
              1216336.8 * (H (Pk X0m k) / Pk X0m k) * ((ℓ + 2) ^ 2 / (ℓ - 0.18)) by
            field_simp; norm_num]
          have hHP : 0 ≤ H (Pk X0m k) / Pk X0m k := by positivity
          calc 1216336.8 * (H (Pk X0m k) / Pk X0m k) * ((ℓ + 2) ^ 2 / (ℓ - 0.18))
              ≤ 1216336.8 * (H (Pk X0m k) / Pk X0m k) * (1.00001 * (ℓ + 2)) :=
                mul_le_mul_of_nonneg_left hq (by positivity)
            _ ≤ 1216500 * (H (Pk X0m k) * (ℓ + 2) / Pk X0m k) := by
                rw [show H (Pk X0m k) * (ℓ + 2) / Pk X0m k =
                  (H (Pk X0m k) / Pk X0m k) * (ℓ + 2) by ring]
                have : 0 ≤ (H (Pk X0m k) / Pk X0m k) * (ℓ + 2) :=
                  mul_nonneg hHP (by linarith)
                nlinarith
      _ ≤ 2493900 * Phi H 1 (X0m / 2) := by
          rw [← Finset.mul_sum, ← Pk_zero]
          have := decay_sum hP h.hXm (a := 1) (by norm_num) K
          have := Phi_nonneg hP 1 (Pk_ge hX 0) (Pk_ge_one hX h.hXm 0)
          nlinarith
  refine ⟨hEB, hsum, hEB, hsum.trans ?_⟩
  -- `2493900 (ℓ₀ + 2) ≤ 10⁴ ℓ₀²`
  have hl0 := log_Pk_ge hX h.hXm 0
  rw [Pk_zero] at hl0
  have hH0 := hP.reg.pos (X0m / 2)
  unfold Phi
  rw [pow_one, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  set ℓ := Real.log (X0m / 2)
  have : 2493900 * (ℓ + 2) ≤ 10000 * ℓ ^ 2 := by nlinarith
  nlinarith

end KR.TNP

end
