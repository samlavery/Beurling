module

public import RequestProject.Beurling.Queue6.PrimeCount
public import RequestProject.Beurling.Queue6.MertensLoc

/-!
# Lemma 5.23: the fields `kSum`, `jit`, `t_ge` of `BeurlingSystem.ThreshHyp` for `P(ω)`

* `tJ θ X₀ ω j` : the decision time of the `j`-th prime of `P(ω)`: `p_j` for a rational prime,
  the slot start `s_k` for the prime decided at relative slot `k + 1`;
* `jit_R`, `t_ge_R` : `|t(p_j) - p_j| ≤ H(t(p_j))/2` (box-centred placement) and `t ≥ 1`;
* `kSum_R` : **the field `kSum`** (`∑_{k ∈ Kset_j} 1/k ≤ 2 log x`): the `k`-sum is at most the
  Euler product `∏_{p_i ≤ x} (1 + 1/p_i) ≤ exp ∑_{p_i ≤ x} w(p_i)`, `w(p) = -log(1 - 1/p)`; the
  primes `≤ X₀/2` are rational (`rat_low_le`), the others are bounded by Lemma 5.1(iv) up to
  `Z ≥ x` (`sum_wE_le_loc`), so the product is `≤ 1.8 log x · e^{2.21/Λ} ≤ 2 log x`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable (θ : ℝ) (X₀ : ℕ)

/-- **The decision times of the primes of `P(ω)`**, by prime index. -/
noncomputable def tJ (ω : JitterΩ) (j : ℕ) : ℝ :=
  match realisedSrc (Mcl θ X₀ ω) (capH X₀) (Ucl ω) j with
  | none => (PR θ X₀ ω).p j
  | some k => slotF θ X₀ k ω

variable {θ X₀} (hc : Cond θ X₀)
include hc

/-- The two kinds of primes of `P(ω)`. -/
lemma tJ_cases (ω : JitterΩ) (j : ℕ) :
    (tJ θ X₀ ω j = (PR θ X₀ ω).p j ∧ ∃ p : {p : ℕ // p.Prime ∧ p < X₀},
        (PR θ X₀ ω).p j = (p.1 : ℝ)) ∨
      ∃ k, tJ θ X₀ ω j = slotF θ X₀ k ω ∧ (PR θ X₀ ω).p j = valF θ X₀ k ω := by
  have hok := realisedOK_Mcl hc ω
  have hpj : (PR θ X₀ ω).p j = realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (hok.equiv j) :=
    realisedSystem_p hok j
  have hsrc := realisedSrc_eq hok j
  unfold tJ
  rcases he : hok.equiv j with p | k
  · rw [he] at hsrc hpj
    left
    simp only [srcOfIdx] at hsrc
    rw [hsrc]
    exact ⟨rfl, p, hpj⟩
  · rw [he] at hsrc hpj
    right
    simp only [srcOfIdx] at hsrc
    rw [hsrc]
    exact ⟨k.1, rfl, hpj⟩

/-- **The field `jit`**: `|t(p_j) - p_j| ≤ H(t(p_j))/2`. -/
theorem jit_R (ω : JitterΩ) (j : ℕ) :
    |tJ θ X₀ ω j - (PR θ X₀ ω).p j| ≤ Hc X₀ (tJ θ X₀ ω j) / 2 := by
  rcases tJ_cases hc ω j with ⟨h1, -⟩ | ⟨k, h1, h2⟩
  · rw [h1, sub_self, abs_zero]
    exact div_nonneg (capH_nonneg _ _) (by norm_num)
  · rw [h1, h2, Hc_slot hc ω k]
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    rw [abs_le]; constructor <;> linarith

/-- **The field `t_ge`**: `1 ≤ t(p_j)`. -/
theorem t_ge_R (ω : JitterΩ) (j : ℕ) : 1 ≤ tJ θ X₀ ω j := by
  rcases tJ_cases hc ω j with ⟨h1, -⟩ | ⟨k, h1, -⟩
  · rw [h1]; linarith [two_le_p hc ω j]
  · rw [h1]
    have := slotF_ge hc k ω
    linarith [X₀_ge_two_pow hc.hX]

/-- The realised primes `≤ X₀/2` are rational, and their Euler factors are those of the
rational primes. -/
lemma low_wE_le (ω : JitterΩ) (x : ℝ) :
    ∑ j ∈ ((PR θ X₀ ω).primesLe x).filter (fun j => ¬ (X₀ : ℝ) / 2 < (PR θ X₀ ω).p j),
        wE ((PR θ X₀ ω).p j) ≤
      ∑ p ∈ X₀.primesBelow.filter (fun p : ℕ => ¬ (X₀ : ℝ) / 2 < (p : ℝ)), wE p := by
  classical
  set P := PR θ X₀ ω
  set A := (P.primesLe x).filter (fun j => ¬ (X₀ : ℝ) / 2 < P.p j)
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hbig := X₀_ge_two_pow hc.hX
  -- every `j ∈ A` is a rational prime
  have hrat : ∀ j ∈ A, ∃ p : {p : ℕ // p.Prime ∧ p < X₀}, P.p j = (p.1 : ℝ) := by
    intro j hj
    have hle := (Finset.mem_filter.mp hj).2
    rcases tJ_cases hc ω j with ⟨-, hp⟩ | ⟨k, -, h2⟩
    · exact hp
    · exfalso
      have h78 := valF_ge_78 hc k ω
      have hs := slotF_ge hc k ω
      apply hle
      show (X₀ : ℝ) / 2 < P.p j
      rw [h2]; linarith
  let g : ℕ → ℕ := fun j => ⌊P.p j⌋₊
  have hg : ∀ j ∈ A, ((g j : ℕ) : ℝ) = P.p j := fun j hj => by
    obtain ⟨p, hp⟩ := hrat j hj
    simp only [g, hp, Nat.floor_natCast]
  have hinj : Set.InjOn g A := by
    intro j hj j' hj' h
    have h1 := hg j hj
    have h2 := hg j' hj'
    have heq : P.p j = P.p j' := by rw [← h1, ← h2, h]
    -- equal values of rational primes: the same rational index
    have hok := realisedOK_Mcl hc ω
    apply hok.equiv.injective
    have e1 := realisedSystem_p hok j
    have e2 := realisedSystem_p hok j'
    obtain ⟨p, hp⟩ := hrat j hj
    obtain ⟨p', hp'⟩ := hrat j' hj'
    rcases he : hok.equiv j with q | k <;> rcases he' : hok.equiv j' with q' | k'
    · rw [he] at e1; rw [he'] at e2
      have : (q.1 : ℝ) = q'.1 := by
        have a : realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (Sum.inl q) = q.1 := rfl
        have b : realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (Sum.inl q') = q'.1 := rfl
        rw [← a, ← b, ← e1, ← e2]; exact heq
      have : q.1 = q'.1 := by exact_mod_cast this
      rw [Subtype.ext this]
    · exfalso
      rw [he'] at e2
      have h78 := valF_ge_78 hc k'.1 ω
      have hs := slotF_ge hc k'.1 ω
      have hle := (Finset.mem_filter.mp hj').2
      apply hle
      show (X₀ : ℝ) / 2 < P.p j'
      rw [e2]; show (X₀ : ℝ) / 2 < valF θ X₀ k'.1 ω; linarith
    · exfalso
      rw [he] at e1
      have h78 := valF_ge_78 hc k.1 ω
      have hs := slotF_ge hc k.1 ω
      have hle := (Finset.mem_filter.mp hj).2
      apply hle
      show (X₀ : ℝ) / 2 < P.p j
      rw [e1]; show (X₀ : ℝ) / 2 < valF θ X₀ k.1 ω; linarith
    · exfalso
      rw [he] at e1
      have h78 := valF_ge_78 hc k.1 ω
      have hs := slotF_ge hc k.1 ω
      have hle := (Finset.mem_filter.mp hj).2
      apply hle
      show (X₀ : ℝ) / 2 < P.p j
      rw [e1]; show (X₀ : ℝ) / 2 < valF θ X₀ k.1 ω; linarith
  have himg : A.image g ⊆ X₀.primesBelow.filter (fun p : ℕ => ¬ (X₀ : ℝ) / 2 < (p : ℝ)) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p, hp⟩ := hrat j hj
    have hgj : g j = p.1 := by simp only [g, hp, Nat.floor_natCast]
    rw [hgj, Finset.mem_filter, Nat.mem_primesBelow]
    refine ⟨⟨p.2.2, p.2.1⟩, ?_⟩
    have := (Finset.mem_filter.mp hj).2
    rw [hp] at this; exact this
  calc ∑ j ∈ A, wE (P.p j) = ∑ j ∈ A, wE ((g j : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun j hj => by rw [hg j hj]
    _ = ∑ n ∈ A.image g, wE (n : ℝ) :=
        (Finset.sum_image (f := fun n : ℕ => wE (n : ℝ)) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg fun n hn _ => by
        have := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hn).1).2.two_le
        exact wE_nonneg (by exact_mod_cast this)

set_option maxHeartbeats 1600000 in
/-- **The field `kSum` of `ThreshHyp`** for `P(ω)`, with the Mertens bound up to `Z ≥ x`:
`∑_{k ∈ Kset_j} 1/k ≤ 2 log x` for every decision order `t` and every `j`. -/
theorem kSum_R (ω : JitterΩ) {Z x : ℝ} (hM : MertensUpTo (PR θ X₀ ω) Z) (hx : (X₀ : ℝ) ≤ x)
    (hxZ : x ≤ Z) (t : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ (PR θ X₀ ω).Kset t x j, 1 / (PR θ X₀ ω).val k ≤ 2 * Real.log x := by
  classical
  set P := PR θ X₀ ω
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXb : 10 ^ 8 ≤ (X₀ : ℝ) := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  have h1 := P.sum_Kset_le_prod t x j
  set S := (P.primesLe x).filter (fun i => t i < t j)
  have hp1 : ∀ i, 1 ≤ 1 + 1 / P.p i := fun i => by
    have := P.p_pos i; have : 0 < 1 / P.p i := by positivity
    linarith
  have h2 : ∏ i ∈ S, (1 + 1 / P.p i) ≤ ∏ i ∈ P.primesLe x, (1 + 1 / P.p i) := by
    rw [← Finset.prod_sdiff (Finset.filter_subset (fun i => t i < t j) (P.primesLe x))]
    have h0 : 0 ≤ ∏ i ∈ S, (1 + 1 / P.p i) :=
      Finset.prod_nonneg fun i _ => (hp1 i).trans' zero_le_one
    have h1' : 1 ≤ ∏ i ∈ P.primesLe x \ S, (1 + 1 / P.p i) := by
      calc (1 : ℝ) = ∏ i ∈ P.primesLe x \ S, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => hp1 i
    nlinarith
  have h3 : ∏ i ∈ P.primesLe x, (1 + 1 / P.p i) ≤
      Real.exp (∑ i ∈ P.primesLe x, wE (P.p i)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => (hp1 i).trans' zero_le_one) fun i _ => ?_
    have hp := P.one_lt i
    have hpos := wE_arg_pos hp
    have hw : (P.p i)⁻¹ ≤ wE (P.p i) := by
      unfold wE
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    calc 1 + 1 / P.p i = (P.p i)⁻¹ + 1 := by rw [one_div]; ring
      _ ≤ Real.exp ((P.p i)⁻¹) := Real.add_one_le_exp _
      _ ≤ Real.exp (wE (P.p i)) := Real.exp_le_exp.mpr hw
  -- the Euler sum
  set y₀ : ℝ := (X₀ : ℝ) / 2 with hy₀
  have hy3 : 286 ≤ y₀ := by rw [hy₀]; linarith
  have hyx : y₀ ≤ x := by rw [hy₀]; linarith
  have hLy4 : 10 ^ 4 ≤ Real.log y₀ := by
    rw [hy₀, Real.log_div (by linarith) (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (P.primesLe x)
    (fun i => y₀ < P.p i) (fun i => wE (P.p i))
  have hhigh := sum_wE_le_loc hM (by linarith : (3 : ℝ) ≤ y₀) hyx hxZ
  have hlow := (low_wE_le hc ω x).trans (rat_low_le X₀ (by linarith) hLy4)
  rw [← hy₀] at hlow
  have hyL : 1 / (y₀ * Real.log y₀) ≤ 1 / (2 * Real.log y₀ ^ 2) := by
    have hl0 : 0 < Real.log y₀ := by linarith
    have hly : 2 * Real.log y₀ ≤ y₀ := by
      have h := Real.log_le_sub_one_of_pos (show 0 < y₀ / 2 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h
      have := Real.log_two_lt_d9; linarith
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hly hl0.le
  have hnum := top_numeric hX0 hX
  rw [← hy₀] at hnum
  have hLy : 0 < Real.log y₀ := by linarith
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hdiv : Real.log (Real.log x / Real.log y₀) =
      Real.log (Real.log x) - Real.log (Real.log y₀) := Real.log_div hLx.ne' hLy.ne'
  have hE : ∑ i ∈ P.primesLe x, wE (P.p i) ≤
      Real.log 1.8 + Real.log (Real.log x) + 2.21 / Real.log X₀ := by
    linarith
  -- `e^{2.21/Λ} ≤ 1.1`
  set a := 2.21 / Real.log X₀
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 0.01 := by
    show 2.21 / Real.log X₀ ≤ 0.01
    rw [div_le_iff₀ (by linarith)]; linarith
  have hea : Real.exp a ≤ 1.1 := by
    have h1 := Real.add_one_le_exp (-a)
    have h2 : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-a) := Real.exp_pos _
    nlinarith
  calc ∑ k ∈ P.Kset t x j, 1 / P.val k ≤ ∏ i ∈ S, (1 + 1 / P.p i) := h1
    _ ≤ Real.exp (∑ i ∈ P.primesLe x, wE (P.p i)) := h2.trans h3
    _ ≤ Real.exp (Real.log 1.8 + Real.log (Real.log x) + a) := Real.exp_le_exp.mpr hE
    _ = 1.8 * Real.log x * Real.exp a := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hLx, Real.exp_log (by norm_num)]
    _ ≤ 1.8 * Real.log x * 1.1 := by gcongr
    _ ≤ 2 * Real.log x := by nlinarith

omit hc in
/-- **Lemma 5.1(iv) up to `Z`** from (HBS) on `[1, Z]`. -/
lemma mertensUpTo_of_hbs {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) : MertensUpTo P Z := by
  intro y x hy hyx hxZ
  have := (abs_le.mp ((P.lemma_5_1 h (x := x) (by linarith) hxZ).2.2.2 y hy hyx)).2
  linarith

end Queue6

end
