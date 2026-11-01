module

public import RequestProject.Beurling.Queue6.Hthr
public import RequestProject.Beurling.Queue6.CountISmallB

/-!
# Lemma 5.23 at `2δ` with the heights the proof reads (Proposition 5.35(B), field `hthr`)

`hthr_R` (`Hthr.lean`) asked for `Good(< t₀)` with `y ≤ t₀` and Lemma 5.1(iv) up to `y`. The
proof of Lemma 5.23 reads less (04e-lp.tex, Lemma 5.23):

* `kSum` is needed only for `p_j` with `Mset_j ≠ ∅`, and then `t(p_j) p_j < x`, so
  `t(p_j) < 1.003 √x`; the primes of `k` are `t`-below `p_j`, so `≤ 2√x`: the Euler product needs
  Lemma 5.1(iv) only up to `2√x` (`euler_R`, `kSum_RB`);
* `countI` reads `Good(< t₀)` only at heights `≤ 0.61x` (`countI_RB`, `x ≤ 1.5 t₀`);
* `localCount` and the case `p > 1.01 x^{1/4}` of `countI` use `NiceEv` only.

* `threshHyp_RB`, `hthr_RB` : `ThreshHyp` and **`hthr`** from `Good(< t₀) ∩ NiceEv` with
  `y ≤ 1.5 t₀`, (HBS) on `[1, Z]` with `√y ≤ Z` and `MertensUpTo` up to `Z' ≥ 2√y`;
* `hthr_Zc` : the same for `X₀ ≤ b ≤ t₀`, `y ≤ b + H(b)`, from (HBS) on `[1, Zc b]` alone
  (e.g. `hT.hbs`); `hthr_tE2` : on `Good(< tE2 b)`, `b : ℤ`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 1600000 in
/-- **The Euler product up to `x`** from Lemma 5.1(iv) up to `Z ≥ x`:
`∏_{p_i ≤ x} (1 + 1/p_i) ≤ 2 log x` (the second half of the proof of `kSum_R`). -/
theorem euler_R (ω : JitterΩ) {Z x : ℝ} (hM : MertensUpTo (PR θ X₀ ω) Z) (hx : (X₀ : ℝ) ≤ x)
    (hxZ : x ≤ Z) :
    ∏ i ∈ (PR θ X₀ ω).primesLe x, (1 + 1 / (PR θ X₀ ω).p i) ≤ 2 * Real.log x := by
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
  have hp1 : ∀ i, 1 ≤ 1 + 1 / P.p i := fun i => by
    have := P.p_pos i; have : 0 < 1 / P.p i := by positivity
    linarith
  have h3 : ∏ i ∈ P.primesLe x, (1 + 1 / P.p i) ≤
      Real.exp (∑ i ∈ P.primesLe x, wE (P.p i)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => (hp1 i).trans' zero_le_one) fun i _ => ?_
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
  calc ∏ i ∈ P.primesLe x, (1 + 1 / P.p i) ≤ Real.exp (∑ i ∈ P.primesLe x, wE (P.p i)) := h3
    _ ≤ Real.exp (Real.log 1.8 + Real.log (Real.log x) + a) := Real.exp_le_exp.mpr hE
    _ = 1.8 * Real.log x * Real.exp a := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hLx, Real.exp_log (by norm_num)]
    _ ≤ 1.8 * Real.log x * 1.1 := by gcongr
    _ ≤ 2 * Real.log x := by nlinarith

set_option maxHeartbeats 1600000 in
/-- **The field `kSum` with Lemma 5.1(iv) up to `2√x`**: for `t = tJ` and `Mset_j ≠ ∅`,
`∑_{k ∈ Kset_j} 1/k ≤ 2 log x` (the primes of `k` are `≤ 2√x`). -/
theorem kSum_RB (ω : JitterΩ) {Z x δ : ℝ} (hM : MertensUpTo (PR θ X₀ ω) Z)
    (hx : (X₀ : ℝ) ^ 2 ≤ x) (hxZ : 2 * √x ≤ Z) (j : ℕ)
    (hne : ((PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j).Nonempty) :
    ∑ k ∈ (PR θ X₀ ω).Kset (tJ θ X₀ ω) x j, 1 / (PR θ X₀ ω).val k ≤ 2 * Real.log x := by
  classical
  set P := PR θ X₀ ω
  set t := tJ θ X₀ ω
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hx0 : 0 < x := by nlinarith
  have hsx := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hXs : (X₀ : ℝ) ≤ √x := Real.le_sqrt_of_sq_le hx
  -- `t(p_j) < 1.003 √x`
  obtain ⟨m, hm⟩ := hne
  obtain ⟨-, -, hjm, -, -, h2⟩ := Finset.mem_filter.mp hm
  have hjs := jitSmall_R hc ω j
  have htj1 := t_ge_R hc ω j
  rw [abs_le] at hjs
  have hpv : P.p j ≤ P.val m := by
    have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjm)
    calc P.p j = P.p j ^ 1 := (pow_one _).symm
      _ ≤ P.p j ^ m j := pow_le_pow_right₀ (P.one_lt j).le h1
      _ ≤ P.val m := P.pow_le_val m j
  have htp : t j * P.p j < x := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpv (by linarith)) h2
  have ht2 : 1.005 * t j ≤ 2 * √x := by
    by_contra hlt; push_neg at hlt
    have : (2 * √x) ^ 2 < (1.005 * t j) ^ 2 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    nlinarith
  -- the primes `t`-below `p_j` are `≤ 2√x`
  have hsub : (P.primesLe x).filter (fun i => t i < t j) ⊆ P.primesLe (2 * √x) := by
    intro i hi
    obtain ⟨-, hti⟩ := Finset.mem_filter.mp hi
    have his := jitSmall_R hc ω i
    have hti1 := t_ge_R hc ω i
    rw [abs_le] at his
    rw [BeurlingSystem.mem_primesLe]
    show P.p i ≤ 2 * √x
    have : P.p i ≤ 1.005 * t i := by linarith [his.2]
    have : t i ≤ t j := hti.le
    linarith
  have hp1 : ∀ i, 1 ≤ 1 + 1 / P.p i := fun i => by
    have := P.p_pos i; have : 0 < 1 / P.p i := by positivity
    linarith
  have h1 := P.sum_Kset_le_prod t x j
  have h2' : ∏ i ∈ (P.primesLe x).filter (fun i => t i < t j), (1 + 1 / P.p i) ≤
      ∏ i ∈ P.primesLe (2 * √x), (1 + 1 / P.p i) :=
    by
      rw [← Finset.prod_sdiff hsub]
      have h0 : 0 ≤ ∏ i ∈ (P.primesLe x).filter (fun i => t i < t j), (1 + 1 / P.p i) :=
        Finset.prod_nonneg fun i _ => (hp1 i).trans' zero_le_one
      have h1' : 1 ≤ ∏ i ∈ P.primesLe (2 * √x) \ (P.primesLe x).filter (fun i => t i < t j),
          (1 + 1 / P.p i) := by
        calc (1 : ℝ) = ∏ i ∈ P.primesLe (2 * √x) \ (P.primesLe x).filter (fun i => t i < t j),
              (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => hp1 i
      nlinarith
  have h3 := euler_R hc ω hM (by linarith) hxZ
  have hlog : Real.log (2 * √x) ≤ Real.log x := by
    apply Real.log_le_log (by positivity)
    have hX2 : (4 : ℝ) ≤ √x := by linarith [X₀_ge_two_pow hc.hX]
    nlinarith
  linarith

variable (hev : Even X₀) (D : Sec5Family)
include hev

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`ThreshHyp` for `P(ω)` at a range-(B) start `y`** (`t = tJ`, `H = Hc X₀`, `2δ`,
`δ = deltaB`, `K_loc = 0`), on `Good(< t₀) ∩ NiceEv` with `y ≤ 1.5 t₀`, from (HBS) on `[1, Z]`
(`√y ≤ Z`) and Lemma 5.1(iv) up to `Z' ≥ 2√y`. -/
theorem threshHyp_RB {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS X0m Z η1 η2 ε1) {Z' : ℝ}
    (hM : MertensUpTo (PR θ X₀ ω) Z') {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hyZ : √y ≤ Z) (hyZ' : 2 * √y ≤ Z')
    (hyt : y ≤ 1.5 * t₀) :
    (PR θ X₀ ω).ThreshHyp (tJ θ X₀ ω) (Hc X₀) y (2 * deltaB θ X₀ ω y) 0 X0m Z η1 η2 ε1 := by
  obtain ⟨hy3, hδge, hδle, ha, -⟩ := rangeB_sizes hc hev ω hy hyB
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX23 : (X₀ : ℝ) ^ 2 ≤ (X₀ : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hX3 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hbig := X₀_ge_two_pow hc.hX
  have hy16 : 16 ≤ y := by linarith
  exact
    { hbs := hbs
      sqrt_le := hyZ
      x_ge := hy16
      loglog := by
        have h2 : 1 ≤ Real.log y := by
          rw [Real.le_log_iff_exp_le (by linarith)]
          have := Real.exp_one_lt_d9; linarith
        exact Real.log_nonneg h2
      t_ge := t_ge_R hc ω
      jit := jit_R hc ω
      jit_small := jitSmall_R hc ω
      H_mono := H_mono_R hc
      H_two := fun z hz => H_two_R hc hz
      Hx_ge := Hx_ge_R hc y
      logH := logH_R hc hy
      δ_ge := hδge
      δ_le := hδle
      Kloc_nonneg := le_rfl
      kSum := fun j _ hne => kSum_RB hc ω hM (by linarith) hyZ' j hne
      countI := countI_RB hc D hev hG hN hy3 hyt hδge hδle
      localCount := localCount_R0 hc hev hN hy16 hδge hδle ha }

/-- **The field `hthr` of `KR.RML6.G1BRest`** (Lemma 5.23 at `2δ`, `δ = deltaB`, `Hy = Hc X₀ y`,
`Kloc = 0`) under the hypotheses of `threshHyp_RB`. -/
theorem hthr_RB {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS X0m Z η1 η2 ε1) {Z' : ℝ}
    (hM : MertensUpTo (PR θ X₀ ω) Z') {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hyZ : √y ≤ Z) (hyZ' : 2 * √y ≤ Z')
    (hyt : y ≤ 1.5 * t₀) :
    (PR θ X₀ ω).threshSum (tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y) ≤
      55 * (2 * deltaB θ X₀ ω y) * Real.log y *
          (Real.log (Hc X₀ y) + Real.log (1 / (2 * deltaB θ X₀ ω y)) + 2) +
        14 * (0 + 2) * Real.log y * √(Hc X₀ y / (2 * deltaB θ X₀ ω y * y)) :=
  (threshHyp_RB hc hev D hG hN hbs hM hy hyB hyZ hyZ' hyt).threshold_mass

/-- **`hthr` at the start `y ≤ b + H(b)` of `RestRes.g1B`**, on `Good(< t₀) ∩ NiceEv`, `b ≤ t₀`,
from (HBS) on `[1, Zc b]` only (`√y ≤ 2√y ≤ Zc b`; Lemma 5.1(iv) up to `Zc b`). -/
theorem hthr_Zc {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {b : ℝ} (hb : (X₀ : ℝ) ≤ b) (hbt : b ≤ t₀) {η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) η1 η2 ε1) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyb : y ≤ b + Hc X₀ b) (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    (PR θ X₀ ω).threshSum (tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y) ≤
      55 * (2 * deltaB θ X₀ ω y) * Real.log y *
          (Real.log (Hc X₀ y) + Real.log (1 / (2 * deltaB θ X₀ ω y)) + 2) +
        14 * (0 + 2) * Real.log y * √(Hc X₀ y / (2 * deltaB θ X₀ ω y * y)) := by
  obtain ⟨-, h2500, h18, -⟩ := Zc_facts hc hb
  have hH0 := Hc_nonneg (X₀ := X₀) b
  have hHb : Hc X₀ b ≤ b / 10 ^ 7 := by have := Hc_le hc b; rwa [max_eq_left hb] at this
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h2y : 2 * √y ≤ Zc X₀ b := by
    have hy0 : 0 ≤ y := by linarith
    have : (2 * √y) ^ 2 = 4 * y := by rw [mul_pow, Real.sq_sqrt hy0]; norm_num
    nlinarith [Real.sqrt_nonneg y]
  have hs := Real.sqrt_nonneg y
  exact hthr_RB hc hev D hG hN hbs (mertensUpTo_of_hbs hbs) hy hyB (by linarith) h2y
    (by linarith)

/-- **`hthr` on `Good(< tE2 b)`** (`b : ℤ`, the event of `Theorem21InputsH`). -/
theorem hthr_tE2 {b : ℤ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D (tE2 b)) (hN : ω ∈ NiceEv θ X₀)
    (hb : (X₀ : ℝ) ≤ b) {η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) η1 η2 ε1) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyb : y ≤ b + Hc X₀ b) (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    (PR θ X₀ ω).threshSum (tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y) ≤
      55 * (2 * deltaB θ X₀ ω y) * Real.log y *
          (Real.log (Hc X₀ y) + Real.log (1 / (2 * deltaB θ X₀ ω y)) + 2) +
        14 * (0 + 2) * Real.log y * √(Hc X₀ y / (2 * deltaB θ X₀ ω y * y)) := by
  have hbt : (b : ℝ) ≤ ((tE2 b : ℕ) : ℝ) := by
    unfold tE2; exact_mod_cast Int.self_le_toNat b
  exact hthr_Zc hc hev D hG hN hb hbt hbs hy hyb hyB

end Queue6

end
