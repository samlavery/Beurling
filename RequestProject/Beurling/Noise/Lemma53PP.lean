module

public import RequestProject.Beurling.Noise.Lemma53Sums

/-!
# Lemma 5.3: the prime powers `p^k > z` with `p ≤ z`

`BeurlingSystem.HBS.pp_sum_le`: under (HBS) on `[1, Z]`, for `L = log z ≥ 100`, `z ≤ Z` and
`β ≥ 0.915`, any family of prime powers `p^{k+1} > z` with `p ≤ z` satisfies

  `∑ log p · p^{-(k+1)β} ≤ e^{-0.415 L} (0.5006 L + 5.33)`.

As in the paper: for `p ≤ √z` the `k`-sum is geometric and starts below `z^{-β}`, and
`∑_{p ≤ √z} log p ≤ ψ(√z) ≤ 1.42 √z` (Lemma 5.1(i)); for `p > √z` every `k ≥ 1` may occur, the
`k`-sum is `≤ 1.001 p^{-2β}`, and `∑_{√z < p ≤ z} log p/p ≤ L/2 + 2.2` (Lemma 5.1(iii)).
-/

@[expose] public section

open Finset Real

namespace BSaias

lemma geom_finset_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K : Finset ℕ) (k0 : ℕ)
    (hK : ∀ k ∈ K, k0 ≤ k) : ∑ k ∈ K, x ^ (k + 1) ≤ x ^ (k0 + 1) / (1 - x) := by
  set N := K.sup id + 1
  have hsub : K ⊆ Ico k0 N := by
    intro k hk
    rw [mem_Ico]
    exact ⟨hK k hk, Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)⟩
  calc ∑ k ∈ K, x ^ (k + 1) ≤ ∑ k ∈ Ico k0 N, x ^ (k + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx0 _)
    _ = x * ∑ k ∈ Ico k0 N, x ^ k := by rw [Finset.mul_sum]; congr 1; funext k; ring
    _ ≤ x * (x ^ k0 / (1 - x)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hx0 hx1) hx0
    _ = x ^ (k0 + 1) / (1 - x) := by ring

end BSaias

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `∑_{p ≤ x} log p ≤ ψ(x)`. -/
lemma sum_log_primesLe_le_psi (x : ℝ) : ∑ j ∈ P.primesLe x, Real.log (P.p j) ≤ P.psi x := by
  rw [psi_eq_sum]
  have : ∑ j ∈ P.primesLe x, Real.log (P.p j) =
      ∑ jk ∈ (P.primesLe x).image (fun j => (j, 0)), Real.log (P.p jk.1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
  rw [this]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro jk hjk
    simp only [mem_image, mem_primesLe] at hjk
    obtain ⟨j, hj, rfl⟩ := hjk
    simpa using hj
  · intro i _ _; exact P.log_p_nonneg _

namespace HBS

variable {P} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- **The prime powers `p^k > z`, `p ≤ z`** (proof of Lemma 5.3). -/
theorem pp_sum_le (h : P.HBS X0m Z η1 η2 ε1) {z β : ℝ} (hz1 : 1 ≤ z) (hL : 100 ≤ Real.log z)
    (hzZ : z ≤ Z)
    (hβ : 0.915 ≤ β) (T : Finset (ℕ × ℕ))
    (hT : ∀ jk ∈ T, P.p jk.1 ≤ z ∧ z < P.p jk.1 ^ (jk.2 + 1)) :
    ∑ jk ∈ T, Real.log (P.p jk.1) * Real.exp (-β * ((jk.2 + 1) * Real.log (P.p jk.1))) ≤
      Real.exp (-0.415 * Real.log z) * (0.5006 * Real.log z + 5.33) := by
  set L := Real.log z
  have hz0 : 0 < z := by linarith
  have hzexp : z = Real.exp L := (Real.exp_log hz0).symm
  set sz := Real.exp (L / 2)
  have hsz : 1 ≤ sz := Real.one_le_exp (by linarith)
  have hszz : sz ≤ z := by rw [hzexp]; exact Real.exp_le_exp.mpr (by linarith)
  -- every prime involved is `≥ 2`
  have hp2 : ∀ jk ∈ T, 2 ≤ P.p jk.1 := fun jk hjk => h.p_ge_two ((hT jk hjk).1.trans hzZ)
  set f : ℕ × ℕ → ℝ := fun jk =>
    Real.log (P.p jk.1) * Real.exp (-β * ((jk.2 + 1) * Real.log (P.p jk.1)))
  set J := T.image Prod.fst
  have hfib := (Finset.sum_fiberwise_of_maps_to (s := T) (t := J) (g := Prod.fst)
    (fun jk hjk => mem_image_of_mem _ hjk) f)
  rw [← hfib]
  -- the fibre sum
  set x : ℕ → ℝ := fun j => Real.exp (-β * Real.log (P.p j))
  have hfiber : ∀ j ∈ J, ∑ jk ∈ T.filter (fun jk => jk.1 = j), f jk ≤
      Real.log (P.p j) * (Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j) := by
    intro j hj
    obtain ⟨jk0, hjk0, rfl⟩ := mem_image.mp hj
    set j := jk0.1
    have hp := hp2 jk0 hjk0
    have hlp : 0 < Real.log (P.p j) := Real.log_pos (by linarith)
    have hx0 : 0 ≤ x j := (Real.exp_pos _).le
    have hx1 : x j < 1 := by
      simp only [x]; rw [Real.exp_lt_one_iff]; nlinarith
    set K := (T.filter (fun jk => jk.1 = j)).image Prod.snd
    have hK : K.Nonempty := ⟨jk0.2, mem_image.mpr ⟨jk0, mem_filter.mpr ⟨hjk0, rfl⟩, rfl⟩⟩
    have hsum : ∑ jk ∈ T.filter (fun jk => jk.1 = j), f jk =
        Real.log (P.p j) * ∑ k ∈ K, x j ^ (k + 1) := by
      rw [Finset.sum_image]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun jk hjk => ?_
        have hj' : jk.1 = j := (mem_filter.mp hjk).2
        simp only [f, x]
        rw [hj', ← Real.exp_nat_mul]
        congr 2; push_cast; ring
      · intro a ha b hb hab
        exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab
    rw [hsum]
    set k0 := K.min' hK
    have hk0 : k0 ∈ K := K.min'_mem hK
    obtain ⟨jk1, hjk1, hk1⟩ := mem_image.mp hk0
    have hj1 : jk1.1 = j := (mem_filter.mp hjk1).2
    have hT1 := hT jk1 (mem_filter.mp hjk1).1
    rw [hj1, hk1] at hT1
    have hgeo := BSaias.geom_finset_le hx0 hx1 K k0 (fun k hk => K.min'_le k hk)
    have hk0pos : 1 ≤ k0 := by
      by_contra hc; push_neg at hc
      have : k0 = 0 := by omega
      rw [this, zero_add, pow_one] at hT1; linarith [hT1.1]
    -- `x^{k₀+1} ≤ e^{-βL}` and `x^{k₀+1} ≤ x²`
    have hxk : x j ^ (k0 + 1) ≤ Real.exp (-β * L) ⊓ x j ^ 2 := by
      refine le_inf ?_ (pow_le_pow_of_le_one hx0 hx1.le (by omega))
      simp only [x]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : L < (k0 + 1 : ℕ) * Real.log (P.p j) := by
        rw [← Real.log_pow]
        exact Real.log_lt_log hz0 hT1.2
      push_cast at this ⊢
      nlinarith
    calc Real.log (P.p j) * ∑ k ∈ K, x j ^ (k + 1)
        ≤ Real.log (P.p j) * (x j ^ (k0 + 1) / (1 - x j)) :=
          mul_le_mul_of_nonneg_left hgeo hlp.le
      _ ≤ Real.log (P.p j) * ((Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j)) := by
          apply mul_le_mul_of_nonneg_left _ hlp.le
          exact div_le_div_of_nonneg_right hxk (by linarith)
      _ = _ := by ring
  refine (Finset.sum_le_sum hfiber).trans ?_
  -- split `J` at `√z`
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => P.p j ≤ sz)]
  have hJz : ∀ j ∈ J, 2 ≤ P.p j ∧ P.p j ≤ z := by
    intro j hj
    obtain ⟨jk, hjk, rfl⟩ := mem_image.mp hj
    exact ⟨hp2 jk hjk, (hT jk hjk).1⟩
  -- small primes
  have hsmall : ∑ j ∈ J.filter (fun j => P.p j ≤ sz),
      Real.log (P.p j) * (Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j) ≤
      3.124 * Real.exp (-0.415 * L) := by
    have hx : ∀ j ∈ J, 1 / (1 - x j) ≤ 2.2 := by
      intro j hj
      have hp := (hJz j hj).1
      have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      have hlp : Real.log 2 ≤ Real.log (P.p j) := Real.log_le_log (by norm_num) hp
      have : x j ≤ 0.5454 := by
        simp only [x]
        have h1 : Real.exp (-β * Real.log (P.p j)) ≤ Real.exp (-0.634) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have h2 : Real.exp (-0.634) ≤ 0.5454 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.634 by norm_num)
          linarith [show (1 : ℝ) / 0.5454 ≤ 1 + 0.634 + 0.634 ^ 2 / 2 by norm_num]
        linarith
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc _ ≤ ∑ j ∈ J.filter (fun j => P.p j ≤ sz),
          Real.log (P.p j) * Real.exp (-β * L) * 2.2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjJ := (mem_filter.mp hj).1
          have hlp : 0 ≤ Real.log (P.p j) := P.log_p_nonneg j
          have h1 := hx j hjJ
          have hx1 : 0 < 1 - x j := by
            have := (hJz j hjJ).1
            simp only [x]
            have : 0 < Real.log (P.p j) := Real.log_pos (by linarith)
            have : Real.exp (-β * Real.log (P.p j)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
            linarith
          rw [mul_div_assoc]
          calc Real.log (P.p j) * ((Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j))
              ≤ Real.log (P.p j) * (Real.exp (-β * L) * (1 / (1 - x j))) := by
                apply mul_le_mul_of_nonneg_left _ hlp
                rw [mul_one_div]
                exact div_le_div_of_nonneg_right inf_le_left hx1.le
            _ ≤ Real.log (P.p j) * (Real.exp (-β * L) * 2.2) := by
                apply mul_le_mul_of_nonneg_left _ hlp
                exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
            _ = _ := by ring
      _ = (∑ j ∈ J.filter (fun j => P.p j ≤ sz), Real.log (P.p j)) * (Real.exp (-β * L) * 2.2) := by
          rw [Finset.sum_mul]; congr 1; funext j; ring
      _ ≤ (1.42 * sz) * (Real.exp (-β * L) * 2.2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc _ ≤ ∑ j ∈ P.primesLe sz, Real.log (P.p j) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj; rw [mem_primesLe]; exact (mem_filter.mp hj).2
                · intro j _ _; exact P.log_p_nonneg j
            _ ≤ P.psi sz := P.sum_log_primesLe_le_psi sz
            _ ≤ 1.42 * sz := ((P.lemma_5_1 h hsz (hszz.trans hzZ)).1).2
      _ ≤ 3.124 * Real.exp (-0.415 * L) := by
          have : sz * Real.exp (-β * L) ≤ Real.exp (-0.415 * L) := by
            simp only [sz]; rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
          nlinarith [Real.exp_pos (-β * L)]
  -- large primes
  have hlarge : ∑ j ∈ J.filter (fun j => ¬ P.p j ≤ sz),
      Real.log (P.p j) * (Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j) ≤
      1.0011 * (L / 2 + 2.2) * Real.exp (-0.415 * L) := by
    have hb : ∀ j ∈ J.filter (fun j => ¬ P.p j ≤ sz),
        Real.log (P.p j) * (Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j) ≤
        1.0011 * Real.exp (-0.415 * L) * (Real.log (P.p j) / P.p j) := by
      intro j hj
      obtain ⟨hjJ, hjs⟩ := mem_filter.mp hj
      push_neg at hjs
      have hp0 : 0 < P.p j := P.p_pos j
      have hlp : L / 2 < Real.log (P.p j) := by
        rw [Real.lt_log_iff_exp_lt hp0]; exact hjs
      have hlp0 : 0 ≤ Real.log (P.p j) := P.log_p_nonneg j
      have hx : x j ≤ 1 / 1000 := by
        simp only [x]
        have h1 : Real.exp (-β * Real.log (P.p j)) ≤ Real.exp (-7) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have h2 : Real.exp (-7) ≤ 1 / 1000 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := Real.exp_one_gt_d9
          have h : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h]
          calc ((1 / 1000)⁻¹ : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
            _ ≤ _ := pow_le_pow_left₀ (by norm_num) this.le 7
        linarith
      have hx2 : x j ^ 2 ≤ Real.exp (-0.415 * L) * (1 / P.p j) := by
        simp only [x]
        rw [← Real.exp_nat_mul, show (1 : ℝ) / P.p j = Real.exp (-Real.log (P.p j)) by
          rw [Real.exp_neg, Real.exp_log hp0, one_div], ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      have hx1 : 0 < 1 - x j := by linarith [show (0:ℝ) < 1 / 1000 by norm_num]
      calc Real.log (P.p j) * (Real.exp (-β * L) ⊓ x j ^ 2) / (1 - x j)
          ≤ Real.log (P.p j) * (Real.exp (-0.415 * L) * (1 / P.p j)) / (1 - 1 / 1000) := by
            apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith)
            exact mul_le_mul_of_nonneg_left (inf_le_right.trans hx2) hlp0
        _ ≤ 1.0011 * Real.exp (-0.415 * L) * (Real.log (P.p j) / P.p j) := by
            have : 0 ≤ Real.log (P.p j) * (Real.exp (-0.415 * L) * (1 / P.p j)) := by positivity
            rw [div_le_iff₀ (by norm_num)]
            have e : Real.log (P.p j) * (Real.exp (-0.415 * L) * (1 / P.p j)) =
                Real.exp (-0.415 * L) * (Real.log (P.p j) / P.p j) := by ring
            rw [e]
            nlinarith [mul_nonneg (Real.exp_pos (-0.415 * L)).le (div_nonneg hlp0 hp0.le)]
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ j ∈ J.filter (fun j => ¬ P.p j ≤ sz), Real.log (P.p j) / P.p j ≤ L / 2 + 2.2 := by
      have hsplit : P.Sp z = P.Sp sz + ∑ j ∈ (P.primesLe z).filter (fun j => ¬ P.p j ≤ sz),
          Real.log (P.p j) / P.p j := by
        unfold Sp
        rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe z) (fun j => P.p j ≤ sz)]
        congr 1
        congr 1; ext j; simp only [mem_filter, mem_primesLe]
        exact ⟨fun h => h.2, fun h' => ⟨h'.trans hszz, h'⟩⟩
      have h1 := (P.lemma_5_1 h hz1 hzZ).2.2.1
      have h2 := (P.lemma_5_1 h hsz (hszz.trans hzZ)).2.2.1
      have hlsz : Real.log sz = L / 2 := Real.log_exp _
      have hsub : ∑ j ∈ J.filter (fun j => ¬ P.p j ≤ sz), Real.log (P.p j) / P.p j ≤
          ∑ j ∈ (P.primesLe z).filter (fun j => ¬ P.p j ≤ sz), Real.log (P.p j) / P.p j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨hjJ, hjs⟩ := mem_filter.mp hj
          exact mem_filter.mpr ⟨(P.mem_primesLe).mpr (hJz j hjJ).2, hjs⟩
        · intro j _ _; exact div_nonneg (P.log_p_nonneg j) (P.p_pos j).le
      rw [hlsz] at h2
      linarith [h1.2, h2.1]
    have he := Real.exp_pos (-0.415 * L)
    nlinarith
  nlinarith [Real.exp_pos (-0.415 * L)]

end HBS

end BeurlingSystem

end
