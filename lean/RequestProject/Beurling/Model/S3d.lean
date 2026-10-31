module

public import RequestProject.Beurling.Model.S3dMertens
public import RequestProject.Beurling.Model.RFLink
public import RequestProject.Beurling.RankFull.RankinRows
public import RequestProject.Beurling.Construction.HBSDerive
public import RequestProject.Beurling.Mertens

/-!
# Lemma A.6 (S3)(d) for the construction (the sure top bound, (F3′))

For the realised system `P(ω)` of the construction, on the event that (HBS) holds at every
height (`SparsityInputs`, from `Construction.sparsityInputs_of_cluster`), the Euler product
`Eu_rat · ∏_{decided n < u} (1 - 1/q_n)⁻¹` is at most `1.8 log V exp(2.21/Λ)`, where `V` bounds
the values of the decided primes. The three groups of the proof of (F3′) (§5):

* the rational primes `p ≤ y₀ = X₀/2`: the Mertens product estimate `ZinfR_one_le`
  (`∏_{p<X}(1 - 1/p)⁻¹ ≤ 1.8 log X`), in place of Rosser–Schoenfeld (3.29) and `e^γ`;
* the realised primes in `(y₀, V]` (the rational primes in `(y₀, X₀)` and the decided jittered
  primes, which are `≥ 7X₀/8 > y₀`): Lemma 5.1(iv) for `P(ω)` (`sum_wE_le`);
* (the third group of the paper, the primes decided before `s` with value above `s - H(s)`, is
  absorbed into the second, since (HBS) is available at every height on the event used here).

`tailSum Dmax X₀ ≤ Eu_rat` is the Euler product for the `X₀`-smooth numbers.

* `realised_sum_le` : the injection of the realised primes into `P(ω).primesLe V`;
* `euler_top_le` : the deterministic bound for a slot model with `RealisedOK`;
* `s3d_sure` : the bound on the event `SparsEv` for the construction, for `u ≤ s_max`, with
  `V = 3(2X₀ + s_max + 1)`.
-/

@[expose] public section

open Finset Real Construction CaplLink SlotModel

namespace BModel

/-- `tailSum Dmax X₀ ≤ ∏_{p < X₀} (1 - 1/p)⁻¹ = exp ∑_{p < X₀} w(p)` (Euler product for the
`X₀`-smooth numbers). -/
lemma tailSum_le_exp (Dmax X₀ : ℕ) :
    RankFull.Config.tailSum Dmax X₀ ≤ Real.exp (∑ p ∈ X₀.primesBelow, wE p) := by
  have h := RankFull.sum_smooth_rpow_le X₀ Dmax (θ := 1) one_pos
  unfold RankFull.Config.tailSum
  have e1 : ∑ d ∈ Nat.smoothNumbersUpTo Dmax X₀, ((d : ℝ))⁻¹ =
      ∑ d ∈ Nat.smoothNumbersUpTo Dmax X₀, (d : ℝ) ^ (-(1 : ℝ)) := by
    refine sum_congr rfl fun d _ => ?_
    rw [Real.rpow_neg_one]
  rw [e1]
  refine h.trans (le_of_eq ?_)
  unfold Rankin.rankinConst
  rw [Real.exp_sum]
  refine prod_congr rfl fun p hp => ?_
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt
  rw [exp_wE hp1, Real.rpow_neg_one]

section Realised

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

open Classical in
/-- **The realised primes above `y₀` inject into `P.primesLe V`**: the rational primes in
`(y₀, X₀)` and the decided primes `k ∈ κ` (values `≤ V`), for `y₀ < 7X₀/8`, `X₀ ≤ V`. -/
theorem realised_sum_le (h : RealisedOK M (capH X₀) U) (hU : ∀ j, U j ∈ Set.Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {y₀ V : ℝ}
    (hy₀ : y₀ < 7 / 8 * X₀) (hV : (X₀ : ℝ) ≤ V) (κ : Finset ℕ) (hκ : ∀ k ∈ κ, placedAt M k)
    (hκV : ∀ k ∈ κ, primeValueOf M (capH X₀) U k ≤ V) :
    ∑ p ∈ X₀.primesBelow.filter (fun p : ℕ => y₀ < (p : ℝ)), wE p +
      ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k) ≤
    ∑ j ∈ ((realisedSystem M (capH X₀) U).primesLe V).filter
      (fun j => y₀ < (realisedSystem M (capH X₀) U).p j),
      wE ((realisedSystem M (capH X₀) U).p j) := by
  set P := realisedSystem M (capH X₀) U with hP
  set sP : Finset {p : ℕ // p.Prime ∧ p < X₀} :=
    (X₀.primesBelow.filter (fun p : ℕ => y₀ < (p : ℝ))).subtype (fun p => p.Prime ∧ p < X₀)
  set sK : Finset {k : ℕ // placedAt M k} := κ.subtype (placedAt M)
  set F : Finset (RealisedIdx M) := sP.disjSum sK
  have e1 : ∑ i ∈ F, wE (realisedVal M (capH X₀) U i) =
      ∑ p ∈ X₀.primesBelow.filter (fun p : ℕ => y₀ < (p : ℝ)), wE p +
        ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k) := by
    rw [sum_disjSum]
    congr 1
    · exact sum_subtype_of_mem (fun p : ℕ => wE p) (fun p hp => by
        rw [mem_filter, Nat.mem_primesBelow] at hp; exact ⟨hp.1.2, hp.1.1⟩)
    · exact sum_subtype_of_mem (fun k : ℕ => wE (primeValueOf M (capH X₀) U k)) hκ
  rw [← e1]
  set e : RealisedIdx M ↪ ℕ := h.equiv.symm.toEmbedding
  have e2 : ∑ i ∈ F, wE (realisedVal M (capH X₀) U i) = ∑ j ∈ F.map e, wE (P.p j) := by
    rw [sum_map]
    refine sum_congr rfl fun i _ => ?_
    rw [hP, realisedSystem_p h]
    simp [e]
  rw [e2]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    have hv : P.p (e i) = realisedVal M (capH X₀) U i := by
      rw [hP, realisedSystem_p h]; simp [e]
    rw [mem_filter, BeurlingSystem.mem_primesLe, hv]
    rcases i with ⟨p, hp⟩ | ⟨k, hk⟩
    · have hi' : (⟨p, hp⟩ : {p : ℕ // p.Prime ∧ p < X₀}) ∈ sP := by
        simpa [F] using hi
      simp only [sP, mem_subtype, mem_filter] at hi'
      simp only [realisedVal]
      have : (p : ℝ) < X₀ := by exact_mod_cast hp.2
      exact ⟨by linarith, hi'.2⟩
    · have hi' : (⟨k, hk⟩ : {k : ℕ // placedAt M k}) ∈ sK := by
        simpa [F] using hi
      simp only [sK, mem_subtype] at hi'
      simp only [realisedVal]
      obtain ⟨h1, h2⟩ := primeValueOf_ge M hU hX hTlow k
      exact ⟨hκV k hi', by nlinarith⟩
  · intro j hj _
    rw [mem_filter] at hj
    exact wE_nonneg (P.one_lt j)

end Realised

/-- **The rational primes `p ≤ y₀`** (Mertens product estimate, `ZinfR_one_le`):
`∑_{p < X₀, p ≤ y₀} w(p) ≤ log 1.8 + log log y₀ + 1/(y₀ log y₀)` for `log y₀ ≥ 10⁴`. -/
theorem rat_low_le (X₀ : ℕ) {y₀ : ℝ} (hy0 : 0 < y₀) (hy : 10 ^ 4 ≤ Real.log y₀) :
    ∑ p ∈ X₀.primesBelow.filter (fun p : ℕ => ¬ y₀ < (p : ℝ)), wE p ≤
      Real.log 1.8 + Real.log (Real.log y₀) + 1 / (y₀ * Real.log y₀) := by
  have hL : 10 ^ 4 ≤ Real.log y₀ := hy
  set X₁ : ℕ := ⌊y₀⌋₊ + 1 with hX₁
  have hX₁y : y₀ ≤ X₁ := by rw [hX₁]; push_cast; exact (Nat.lt_floor_add_one y₀).le
  have hX₁y' : (X₁ : ℝ) ≤ y₀ + 1 := by rw [hX₁]; push_cast; linarith [Nat.floor_le hy0.le]
  have hlX : 10 ^ 4 ≤ Real.log X₁ := hL.trans (Real.log_le_log hy0 hX₁y)
  have hsub : ∑ p ∈ X₀.primesBelow.filter (fun p : ℕ => ¬ y₀ < (p : ℝ)), wE p ≤
      ∑ p ∈ X₁.primesBelow, wE p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [mem_filter, Nat.mem_primesBelow, not_lt] at hp
      rw [Nat.mem_primesBelow, hX₁]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hp.2), hp.1.2⟩
    · intro p hp _
      exact wE_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt)
  refine hsub.trans ?_
  have hR := Mertens.ZinfR_one_le hlX
  have e : BaseFactor.ZinfR X₁ 1 = Real.exp (∑ p ∈ X₁.primesBelow, wE p) := by
    unfold BaseFactor.ZinfR
    rw [Real.exp_sum]
    refine prod_congr rfl fun p hp => ?_
    rw [exp_wE (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt), Real.rpow_neg_one]
  rw [e] at hR
  have hLX0 : 0 < Real.log X₁ := by linarith
  have h2 := (Real.le_log_iff_exp_le (by positivity)).mpr hR
  rw [Real.log_mul (by norm_num) hLX0.ne'] at h2
  -- `log log X₁ ≤ log log y₀ + 1/(y₀ log y₀)`
  have hLy0 : 0 < Real.log y₀ := by linarith
  have h3 : Real.log X₁ ≤ Real.log y₀ + 1 / y₀ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (X₁ : ℝ) / y₀ by positivity)
    rw [Real.log_div (by positivity) hy0.ne'] at h
    have : (X₁ : ℝ) / y₀ - 1 ≤ 1 / y₀ := by
      rw [div_sub_one hy0.ne', div_le_div_iff_of_pos_right hy0]; linarith
    linarith
  have h4 : Real.log (Real.log X₁) ≤ Real.log (Real.log y₀) + 1 / (y₀ * Real.log y₀) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log X₁ / Real.log y₀ by positivity)
    rw [Real.log_div hLX0.ne' hLy0.ne'] at h
    have : Real.log X₁ / Real.log y₀ - 1 ≤ 1 / (y₀ * Real.log y₀) := by
      rw [div_sub_one hLy0.ne', show 1 / (y₀ * Real.log y₀) = (1 / y₀) / Real.log y₀ by
        field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hLy0.le
    linarith
  linarith

/-- The numerical step: `1/(2L₀²) + 2.20/L₀ + 11.6/(y₀L₀) ≤ 2.21/Λ` for `y₀ = X₀/2`,
`L₀ = log y₀`, `Λ = log X₀ ≥ 10⁸`. -/
lemma top_numeric {X : ℝ} (hX0 : 0 ≤ X) (hX : 10 ^ 8 ≤ Real.log X) :
    1 / (2 * Real.log (X / 2) ^ 2) + 2.20 / Real.log (X / 2) +
      11.6 / (X / 2 * Real.log (X / 2)) ≤ 2.21 / Real.log X := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXb : 10 ^ 8 ≤ X := by
    have h1 : Real.exp (10 ^ 8) ≤ X := by
      rw [← Real.exp_log (by linarith : 0 < X)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  set Λ := Real.log X with hΛ
  have hL0 : Real.log (X / 2) = Λ - Real.log 2 := Real.log_div (by linarith) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  set L₀ := Real.log (X / 2) with hL₀
  have hL0b : 10 ^ 8 - 1 ≤ L₀ := by rw [hL0]; linarith
  have hL0p : 0 < L₀ := by linarith
  have e : 1 / (2 * L₀ ^ 2) + 2.20 / L₀ + 11.6 / (X / 2 * L₀) =
      (1 / (2 * L₀) + 2.20 + 23.2 / X) / L₀ := by
    field_simp; ring
  rw [e]
  have hb1 : 1 / (2 * L₀) ≤ 1 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hb2 : 23.2 / X ≤ 1 / 10 ^ 6 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hbr : 1 / (2 * L₀) + 2.20 + 23.2 / X ≤ 2.2001 := by linarith
  calc (1 / (2 * L₀) + 2.20 + 23.2 / X) / L₀ ≤ 2.2001 / L₀ :=
        div_le_div_of_nonneg_right hbr hL0p.le
    _ ≤ 2.21 / Λ := by
        rw [div_le_div_iff₀ hL0p (by linarith)]; rw [hL0]; nlinarith

section Top

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **The deterministic sure top bound** ((F3′), second case; Lemma A.6 (S3)(d)): for a slot
model with `RealisedOK`, the local Mertens bound for its realised system, and decided primes
`k ∈ κ` with values `≤ V`,
`tailSum · ∏_{k ∈ κ} (1 - 1/p_k)⁻¹ ≤ 1.8 log V · exp(2.21/Λ)`. -/
theorem euler_top_le (h : RealisedOK M (capH X₀) U) (hU : ∀ j, U j ∈ Set.Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊)
    (hM : MertensUpper (realisedSystem M (capH X₀) U)) {V : ℝ}
    (hV : (X₀ : ℝ) ≤ V) (κ : Finset ℕ) (hκ : ∀ k ∈ κ, placedAt M k)
    (hκV : ∀ k ∈ κ, primeValueOf M (capH X₀) U k ≤ V) (Dmax : ℕ) :
    RankFull.Config.tailSum Dmax X₀ * Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) ≤
      1.8 * Real.log V * Real.exp (2.21 / Real.log X₀) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXb : 10 ^ 8 ≤ (X₀ : ℝ) := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  set y₀ : ℝ := (X₀ : ℝ) / 2 with hy₀
  have hy3 : 286 ≤ y₀ := by rw [hy₀]; linarith
  have hyV : y₀ ≤ V := by rw [hy₀]; linarith
  have hy78 : y₀ < 7 / 8 * X₀ := by rw [hy₀]; linarith
  have hLy4 : 10 ^ 4 ≤ Real.log y₀ := by
    rw [hy₀, Real.log_div (by linarith) (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  have hlow := rat_low_le X₀ (by linarith) hLy4
  have hyL : 1 / (y₀ * Real.log y₀) ≤ 1 / (2 * Real.log y₀ ^ 2) := by
    have hl0 : 0 < Real.log y₀ := by linarith
    have hly : 2 * Real.log y₀ ≤ y₀ := by
      have h := Real.log_le_sub_one_of_pos (show 0 < y₀ / 2 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h
      have := Real.log_two_lt_d9; linarith
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hly hl0.le
  have hreal := realised_sum_le h hU hX hTlow hy78 hV κ hκ hκV
  have hhigh := sum_wE_le hM (by linarith : (3 : ℝ) ≤ y₀) hyV
  have hsplit := sum_filter_add_sum_filter_not X₀.primesBelow (fun p : ℕ => y₀ < (p : ℝ))
    (fun p : ℕ => wE p)
  have hT := tailSum_le_exp Dmax X₀
  have hLy : 0 < Real.log y₀ := Real.log_pos (by linarith)
  have hLV : 0 < Real.log V := Real.log_pos (by linarith)
  have hdiv : Real.log (Real.log V / Real.log y₀) =
      Real.log (Real.log V) - Real.log (Real.log y₀) := Real.log_div hLV.ne' hLy.ne'
  have hnum := top_numeric hX0 hX
  rw [← hy₀] at hnum
  have hE : ∑ p ∈ X₀.primesBelow, wE p + ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k) ≤
      Real.log 1.8 + Real.log (Real.log V) + 2.21 / Real.log X₀ := by
    linarith
  calc RankFull.Config.tailSum Dmax X₀ *
        Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k))
      ≤ Real.exp (∑ p ∈ X₀.primesBelow, wE p) *
          Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) :=
        mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ = Real.exp (∑ p ∈ X₀.primesBelow, wE p + ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log 1.8 + Real.log (Real.log V) + 2.21 / Real.log X₀) :=
        Real.exp_le_exp.mpr hE
    _ = 1.8 * Real.log V * Real.exp (2.21 / Real.log X₀) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hLV, Real.exp_log (by norm_num)]

end Top

/-! ### The construction -/

section Construction

open MeasureTheory RankFull RankFull.Config

variable {θ : ℝ} {X₀ : ℕ}

/-- **The event of (F4)/(F3′)**: the local Mertens bound (Lemma 5.1(iv)) for the realised system
`P(ω)` at every height. It contains the event `SparsityInputs X₀ P(ω)` (`sparsEv_of_inputs`),
which `Construction.sparsityInputs_of_cluster` derives from Part I for `P(ω)` and the cluster
event. -/
def SparsEv (θ : ℝ) (X₀ : ℕ) : Set JitterΩ :=
  {ω | MertensUpper (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω))}

lemma sparsEv_of_inputs {ω : JitterΩ}
    (h : SparsityInputs X₀ (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω))) :
    ω ∈ SparsEv θ X₀ := by
  obtain ⟨X0m, η1, η2, ε1, -, -, hH, -⟩ := h
  exact mertensUpper_of_HBS hH

/-- **`SparsEv` from Part I and the cluster event** (`Construction.sparsityInputs_of_cluster`):
for jitters in `[0, 1]`, the conclusions of Part I for `P(ω)` (`PartIRestJ`) and the cluster
event `ClusterUpTo P(ω) X₀ (4v/log¹¹ v) M̄₁(v)` for all `v ≥ X₀` give (HBS) at every height, hence
`ω ∈ SparsEv`. -/
lemma sparsEv_of_cluster (hc : Cond θ X₀) {ω : JitterΩ} (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1)
    (a : ℕ → ℝ)
    (hI : PartIRestJ θ X₀ (realisedSystem (Mcl θ X₀ ω) (capH X₀) ω)
      (realisedA (Mcl θ X₀ ω) (capH X₀) ω) (fun n => solveU (thetaB θ) n) a (Mcl θ X₀ ω))
    (hcl : ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (Mcl θ X₀ ω) (capH X₀) ω) X₀
      (4 * v / Real.log v ^ 11) (capM1 X₀ v)) :
    ω ∈ SparsEv θ X₀ := by
  have hinf : {k | placedAt (Mcl θ X₀ ω) k}.Infinite := by
    rw [Mcl_eq hc]; exact limModel_placed_infinite (hc.std ω)
  have h := sparsityInputs_of_cluster hc.hθ hc.hX (Mcl θ X₀ ω) ω hω hinf a hI hcl
  apply sparsEv_of_inputs
  rw [Ucl_eq hω]
  exact h

/-- The bound `V(s_max) = 3(2X₀ + s_max + 1)` for the values of the primes decided at slot
indices `< s_max` (`s_{n+1} ≤ 2(2X₀ + n + 2)`, `H(s) ≤ s`). -/
noncomputable def vTop (X₀ smax : ℕ) : ℝ := 3 * (2 * X₀ + smax + 1)

/-- The value of a prime decided at slot index `n < s_max` is at most `vTop X₀ s_max`. -/
lemma valF_le_vTop (hc : Cond θ X₀) (ω : JitterΩ) {n smax : ℕ} (hn : n < smax) :
    valF θ X₀ n ω ≤ vTop X₀ smax := by
  have hstd := hc.std ω
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hs := slotF_ge hc n ω
  have hbox := (landing_mem_box (s := slotF θ X₀ n ω) (HF_pos hc n ω).le
    (clamp01_mem (ω (n + 1)))).2
  rw [← valF_eq] at hbox
  have hH := InitialRange.capH_le_rpow hX0 hc.hX hs
  have hs1 : 1 ≤ slotF θ X₀ n ω := by linarith [X₀_ge_two_pow hc.hX]
  have hr : slotF θ X₀ n ω ^ (1 / 8 : ℝ) ≤ slotF θ X₀ n ω := by
    conv_rhs => rw [← Real.rpow_one (slotF θ X₀ n ω)]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hlin : ∀ x, (X₀ : ℝ) ≤ x → 7 / 10 * x - X₀ - 1 ≤ hstd.limModel.T x := fun x hx => by
    rw [hstd.limModel_T_eq x]; exact targetD_ge_linear (by linarith [hstd.hθ.2]) hstd.hX _ hx
  have hsl : slotF θ X₀ n ω ≤ 2 * (2 * X₀ + (n + 1 : ℕ) + 1) := by
    unfold slotF; rw [Mcl_eq hc]; exact slot_le_linear hstd.hX hlin (n + 1)
  have hnm : ((n + 1 : ℕ) : ℝ) ≤ smax := by exact_mod_cast hn
  unfold HF at hbox
  unfold vTop
  linarith

variable (hc : Cond θ X₀) (hev : Even X₀)

open Classical in
/-- **Lemma A.6 (S3)(d) for the construction** (the sure top bound, (F3′)): on `SparsEv`, for
every slot index `u ≤ s_max`,
`tailSum · ∏_{decided n < u} (1 - 1/q_n)⁻¹ ≤ 1.8 log V(s_max) · exp(2.21/Λ)`. -/
theorem s3d_sure {ω : JitterΩ} (hω : ω ∈ SparsEv θ X₀) (N Dmax smax : ℕ)
    {u : ℕ} (hu : u ≤ smax) :
    tailSum Dmax X₀ *
      ∏ n ∈ Finset.univ.filter (fun n : Fin N => ω ∈ (constructionLaw2 hc hev).A n ∧
        (n : ℕ) < u), (1 - ((constructionLaw2 hc hev).q n ω)⁻¹)⁻¹ ≤
      1.8 * Real.log (vTop X₀ smax) *
        Real.exp (2.21 / Real.log X₀) := by
  set Fl := Finset.univ.filter (fun n : Fin N => ω ∈ (constructionLaw2 hc hev).A n ∧
    (n : ℕ) < u) with hFl
  set M := Mcl θ X₀ ω with hM
  have hstd := hc.std ω
  have hok : RealisedOK M (capH X₀) (Ucl ω) := by
    rw [hM, Mcl_eq hc]; exact limModel_realisedOK hstd
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    rw [hM, Mcl_eq hc]; exact hstd.limModel_low
  have hU : ∀ j, Ucl ω j ∈ Set.Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  set κ := Fl.map Fin.valEmbedding with hκ
  have hκP : ∀ k ∈ κ, placedAt M k := by
    intro k hk
    rw [hκ, mem_map] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    rw [hFl, mem_filter] at hn
    exact hn.2.1.1.1
  have hκV : ∀ k ∈ κ, primeValueOf M (capH X₀) (Ucl ω) k ≤ vTop X₀ smax := by
    intro k hk
    rw [hκ, mem_map] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    rw [hFl, mem_filter] at hn
    exact valF_le_vTop hc ω (lt_of_lt_of_le hn.2.2 hu)
  have hV : (X₀ : ℝ) ≤ vTop X₀ smax := by
    unfold vTop; have : (0 : ℝ) ≤ smax := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    linarith
  have hmain := euler_top_le hok hU hc.hX hTlow hω hV κ hκP hκV Dmax
  have e : ∏ n ∈ Fl, (1 - ((constructionLaw2 hc hev).q n ω)⁻¹)⁻¹ =
      Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) (Ucl ω) k)) := by
    rw [hκ, sum_map, Real.exp_sum]
    refine prod_congr rfl fun n hn => ?_
    rw [hFl, mem_filter] at hn
    have h1 := law2_hq hc hev ω n hn.2.1
    rw [← exp_wE h1]
    rfl
  rw [e]
  exact hmain

end Construction

/-! ### The (S3)(d) event joins the nested good events -/

section Family

open MeasureTheory RankFull RankFull.Config
open scoped ENNReal

open Classical in
/-- The Euler product over the decided indices `n < u` of a jitter law. -/
noncomputable def eulerLt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}
    (J : JitterLaw Ω P θE) (N u : ℕ) (ω : Ω) : ℝ :=
  ∏ n ∈ Finset.univ.filter (fun n : Fin N => ω ∈ J.A n ∧ (n : ℕ) < u), (1 - (J.q n ω)⁻¹)⁻¹

open Classical in
lemma eulerLt_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}
    (J : JitterLaw Ω P θE) (N : ℕ) {u u' : ℕ} (hu : u' ≤ u) :
    Measurable[J.F u] (eulerLt J N u') := by
  have e : eulerLt J N u' = fun ω => ∏ n : Fin N,
      (if ω ∈ J.A n ∧ (n : ℕ) < u' then (1 - (J.q n ω)⁻¹)⁻¹ else 1) := by
    funext ω; unfold eulerLt; rw [prod_filter]
  rw [e]
  refine Finset.measurable_prod _ fun n _ => ?_
  by_cases hn : (n : ℕ) < u'
  · simp only [hn, and_true]
    have hA : MeasurableSet[J.F u] (J.A n) := J.F_mono (by omega) _ (J.A_meas n)
    have hq : Measurable[J.F u] (J.q n) := (J.q_meas n).mono (J.F_mono (by omega)) le_rfl
    exact Measurable.ite hA ((measurable_const.sub hq.inv).inv) measurable_const
  · simp only [hn, and_false, if_false]
    exact measurable_const

/-- **The (S3)(d) event at stage `u`**: the Euler-product bound at every `u' ≤ u` (`u' ≤ s_max`).
It is `F_u`-measurable and decreasing in `u`; adding it to the nested good events turns the
sure bound `s3d_sure` (on `SparsEv`) into the adapted form used by `skeletonBound_jitter`. -/
def s3dEv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}
    (J : JitterLaw Ω P θE) (N Dmax X₀ smax : ℕ) (A : ℝ) (u : ℕ) : Set Ω :=
  {ω | ∀ u' ≤ u, u' ≤ smax → tailSum Dmax X₀ * eulerLt J N u' ω ≤ A}

lemma s3dEv_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}
    (J : JitterLaw Ω P θE) (N Dmax X₀ smax : ℕ) (A : ℝ) (u : ℕ) :
    MeasurableSet[J.F u] (s3dEv J N Dmax X₀ smax A u) := by
  have e : s3dEv J N Dmax X₀ smax A u = ⋂ u' ∈ Finset.range (u + 1),
      {ω | u' ≤ smax → tailSum Dmax X₀ * eulerLt J N u' ω ≤ A} := by
    ext ω
    simp only [s3dEv, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
    exact ⟨fun h u' hu' => h u' (by omega), fun h u' hu' => h u' (by omega)⟩
  rw [e]
  refine Finset.measurableSet_biInter _ fun u' hu' => ?_
  have hu'' : u' ≤ u := by have := Finset.mem_range.mp hu'; omega
  by_cases hs : u' ≤ smax
  · simp only [hs, true_implies]
    exact measurableSet_le ((eulerLt_measurable J N hu'').const_mul _) measurable_const
  · simp only [hs, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

lemma s3dEv_anti {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}
    (J : JitterLaw Ω P θE) (N Dmax X₀ smax : ℕ) (A : ℝ) {u u' : ℕ} (h : u ≤ u') :
    s3dEv J N Dmax X₀ smax A u' ⊆ s3dEv J N Dmax X₀ smax A u :=
  fun _ hω v hv hvs => hω v (hv.trans h) hvs

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)

/-- On `SparsEv`, the (S3)(d) event holds at every stage, with
`A ≥ 1.8 log V(s_max) exp(2.21/Λ)`. -/
lemma mem_s3dEv {ω : JitterΩ} (hω : ω ∈ SparsEv θ X₀) (N Dmax smax : ℕ) {A : ℝ}
    (hA : 1.8 * Real.log (vTop X₀ smax) *
      Real.exp (2.21 / Real.log X₀) ≤ A) (u : ℕ) :
    ω ∈ s3dEv (constructionLaw2 hc hev) N Dmax X₀ smax A u :=
  fun _ _ hu' => (s3d_sure hc hev hω N Dmax smax hu').trans hA

open Classical in
/-- **The skeleton bound for the construction, with (S3)(d) proved** (Lemma A.5 + Theorem A.10,
`skeletonBound_jitter`): as `skeletonBound_construction`, with the named hypothesis `S3dHyp`
replaced by `Good ⊆ SparsEv` (Lemma 5.1(iv) for `P(ω)`)
and `A ≥ 1.8 log V(s_max) exp(2.21/Λ)`. The nested good events are
`goodLt u ∩ s3dEv u`. -/
theorem skeletonBound_construction_S3 {N : ℕ} {Good : Set JitterΩ} (hGood : MeasurableSet Good)
    (smax : ℕ) (hGoodG : Good ⊆ goodLt θ X₀ smax) (hGoodS : Good ⊆ SparsEv θ X₀) {r₀ : ℕ}
    (hr0 : 1 ≤ r₀) {Jw : Set ℝ} (hJw : MeasurableSet Jw) {a δ : ℝ}
    (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) {V : ℝ} (hJV : Jw ⊆ Set.Iic V)
    (hsm : ⌊24 * V / 7⌋₊ ≤ smax) (D Dmax : ℕ) {A Eu : ℝ} (hEuA : Eu ≤ A)
    (hAtop : 1.8 * Real.log (vTop X₀ smax) *
      Real.exp (2.21 / Real.log X₀) ≤ A)
    (hmulti : MultiRunSkeletonBound jitterMeasure Good r₀ (1 + 1 / Real.log X₀) δ A Eu
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw) E l)) :
    SkeletonBound jitterMeasure Good r₀ (1 + 1 / Real.log X₀) δ A Eu
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := N) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ D Dmax Jw) E l) := by
  have hΛ : 0 < Real.log X₀ := by linarith [hc.hX]
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hA : 0 ≤ A := by
    refine le_trans ?_ hAtop
    have hV : 1 ≤ vTop X₀ smax := by
      unfold vTop; have : (0 : ℝ) ≤ smax := Nat.cast_nonneg _
      linarith
    have := Real.log_nonneg hV
    positivity
  have hτ1 : ∀ j : Fin r₀, 1 ≤ tauSlot (capH X₀) X₀ j := by
    intro j
    unfold tauSlot
    have h1 := InitialRange.capH_le_rpow hX0 hc.hX le_rfl
    have h2 := four_capH_le hX0 hc.hX le_rfl
    exact le_max_of_le_left (by linarith [X₀_ge_two_pow hc.hX])
  set J := constructionLaw2 hc hev with hJdef
  set G : ℕ → Set JitterΩ := fun u => goodLt θ X₀ u ∩ s3dEv J N Dmax X₀ smax A u with hGdef
  have hGm : ∀ u, MeasurableSet[J.F u] (G u) := fun u =>
    (good_meas hc u).inter (s3dEv_meas J N Dmax X₀ smax A u)
  have hGa : ∀ u u', u ≤ u' → G u' ⊆ G u := fun u u' h =>
    Set.inter_subset_inter (good_anti h) (s3dEv_anti J N Dmax X₀ smax A h)
  have hGoodG' : Good ⊆ G smax := fun ω hω =>
    ⟨hGoodG hω, mem_s3dEv hc hev (hGoodS hω) N Dmax smax hAtop smax⟩
  have hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → tailSum Dmax X₀ *
      ∏ n ∈ univ.filter (fun n : Fin N => ω ∈ J.A n ∧ (n : ℕ) < u), (1 - (J.q n ω)⁻¹)⁻¹ ≤ A :=
    fun ω u hu hω => hω.2 u le_rfl hu
  exact skeletonBound_jitter J (θ := 1 + 1 / Real.log X₀) (by positivity) le_rfl hGood G hGm
    hGa smax hGoodG' hr0 (fun j => tauSlot (capH X₀) X₀ j) hτ1 hJw hJ hδ X₀ D Dmax hA hEuA
    (fun ω n hn => law2_hq hc hev ω n hn)
    (fun ω n hn y hy hqy => (law2_hsmax hc hev hJV ω n hn y hy hqy).trans hsm)
    (fun ω n hn j hj => law2_hτSlot hc hev ω n hn j hj) hS3 hmulti

end Family

end BModel
