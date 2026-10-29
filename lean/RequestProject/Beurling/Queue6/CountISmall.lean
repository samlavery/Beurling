module

public import RequestProject.Beurling.Queue6.NCount
public import RequestProject.Beurling.Queue6.S2Err

/-!
# Lemma 5.23, case (i): the field `countI` of `BeurlingSystem.ThreshHyp` for `P(ω)`

* `queueB_le_capH`, `lagD_le` : `B(v) ≤ H(v)`, so the lag `D(v) ≤ 4 H(x) + 5` for `X₀ ≤ v ≤ x`;
* `countI_small` : **case `p ≤ 1.01 x^{1/4}`** (04e-lp.tex, Lemma 5.23 (i), first bullet): the
  elements `m'` lie in `J_p = [c, d)`, `d = x/(t(p) p) ≥ 0.97 √x`, `|J_p| = δ d`, and on
  `Good(< t₀) ∩ NiceEv` (`t₀ ≥ x`) `N(J_p) ≤ 2.03 |J_p|` (`Ncount_le`: the lag at both ends is
  `≤ 8H(x) + 10 ≤ 10⁻³ |J_p|`, the absorbed count `≤ 0.01 |J_p|`), so `#Mset_j ≤ 4 δx/p²`;
* `countI_R` : **the field `countI`**, both cases (`countI_large` for `p > 1.01 x^{1/4}`).

Standing hypotheses (those of `ThreshHyp` used): `X₀³ ≤ x ≤ t₀`, `6 H(x) x^{-1/3} ≤ δ ≤ 1/4`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel Absorbed

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- `B(v) ≤ H(v)` for `v ≥ X₀`. -/
lemma queueB_le_capH {v : ℝ} (hv : (X₀ : ℝ) ≤ v) : queueB X₀ v ≤ capH X₀ v := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h1 := queueB_mono hX0 hc.hX hv (show v ≤ 4 * v by linarith)
  have h2 := queueB_le_H hc hv
  have hl := (logs_of_ge hX0 hc.hX hv).1
  have hl6 : 1 ≤ Real.log v ^ 6 := one_le_pow₀ (by linarith)
  have hH0 := capH_nonneg (X₀ : ℝ) v
  have : capH X₀ v / Real.log v ^ 6 ≤ capH X₀ v := div_le_self hH0 hl6
  linarith

/-- The lag `D(v) ≤ 4 H(x) + 5` for `X₀ ≤ v ≤ x`. -/
lemma lagD_le {v x : ℝ} (hv : (X₀ : ℝ) ≤ v) (hvx : v ≤ x) :
    lagD X₀ v ≤ 4 * capH X₀ x + 5 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h1 := queueB_le_capH hc hv
  have h2 := queueB_le_capH hc (le_refl (X₀ : ℝ))
  have hm1 := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hv) (mem_Ici.mpr (hv.trans hvx)) hvx
  have hm2 := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr le_rfl) (mem_Ici.mpr (hv.trans hvx))
    (hv.trans hvx)
  unfold lagD; linarith

variable (D : Sec5Family) (hev : Even X₀)
include hev

set_option maxHeartbeats 6400000 in
/-- **The field `countI`, case `p ≤ 1.01 x^{1/4}`**: `#Mset_j ≤ 4 δx/p_j²` on
`Good(< t₀) ∩ NiceEv`. -/
theorem countI_small {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {x δ : ℝ} (hx3 : (X₀ : ℝ) ^ 3 ≤ x) (hxt : x ≤ t₀) (hδge : 6 * Hc X₀ x / x ^ (1 / 3 : ℝ) ≤ δ)
    (hδ : δ ≤ 1 / 4) {j : ℕ} (hps : (PR θ X₀ ω).p j ≤ 1.01 * x ^ (1 / 4 : ℝ)) :
    (((PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j).card : ℝ) ≤ 4 * δ * x / (PR θ X₀ ω).p j ^ 2 := by
  classical
  set P := PR θ X₀ ω
  set p := P.p j with hpe
  set τ := tJ θ X₀ ω j with hτe
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hbig := X₀_ge_two_pow hc.hX
  have hX3 : 4 * (X₀ : ℝ) ^ 2 ≤ (X₀ : ℝ) ^ 3 := by nlinarith
  have hx0 : 0 < x := by nlinarith
  have hxX : (X₀ : ℝ) ≤ x := by nlinarith
  have hp2 : 2 ≤ p := two_le_p hc ω j
  have hτ1 : 0.99 * p ≤ τ := (tJ_near hc ω j).1
  have hτ2 : τ ≤ 1.01 * p := (tJ_near hc ω j).2
  have hτ0 : 0 < τ := by linarith
  have hτp : 0 < τ * p := by positivity
  set H := Hc X₀ x with hHe
  have hHx : 200 ≤ H := by
    have := Hc_ge hc x; rw [max_eq_left hxX] at this
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith); rw [hHe]; linarith
  -- `q = x^{1/24}`
  set q := x ^ (1 / 24 : ℝ) with hqe
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have hpow : ∀ n : ℕ, q ^ n = x ^ ((n : ℝ) / 24) := fun n => by
    rw [hqe, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have hq24 : q ^ 24 = x := by rw [hpow]; norm_num
  have hq6 : x ^ (1 / 4 : ℝ) = q ^ 6 := by rw [hpow]; norm_num
  have hq8 : x ^ (1 / 3 : ℝ) = q ^ 8 := by rw [hpow]; norm_num
  rw [hq6] at hps
  rw [hq8] at hδge
  have hq1 : 1 ≤ q := Real.one_le_rpow (by linarith) (by norm_num)
  -- `q^{12} ≥ 2X₀`
  have hq12X : 2 * (X₀ : ℝ) ≤ q ^ 12 := by
    have h1 : (q ^ 12) ^ 2 = x := by rw [← pow_mul]; exact hq24
    by_contra h; push_neg at h
    have : (q ^ 12) ^ 2 < (2 * (X₀ : ℝ)) ^ 2 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    nlinarith
  -- `δ ≥ 6H/q⁸`
  have hq8p : 0 < q ^ 8 := by positivity
  have hδ6 : 6 * H ≤ δ * q ^ 8 := by rwa [div_le_iff₀ hq8p] at hδge
  have hδ0 : 0 < δ := by
    have : 0 < 6 * H := by linarith
    nlinarith
  -- the window `[c, d)`
  set c := x * (1 - δ) / (τ * p) with hce
  set d := x / (τ * p) with hde
  have hp2q : p ^ 2 ≤ 1.0201 * q ^ 12 := by
    have : p ^ 2 ≤ (1.01 * q ^ 6) ^ 2 := pow_le_pow_left₀ (by linarith) hps 2
    nlinarith
  have hτpq : τ * p ≤ 1.0304 * q ^ 12 := by nlinarith
  have hdq : 0.97 * q ^ 12 ≤ d := by
    rw [hde, le_div_iff₀ hτp, ← hq24]
    have : q ^ 24 = q ^ 12 * q ^ 12 := by ring
    rw [this]
    have h12 : 0 < q ^ 12 := by positivity
    nlinarith
  have hτp4 : 3.96 ≤ τ * p := by nlinarith
  have hdx : 3.96 * d ≤ x := by rw [hde, mul_div_assoc', div_le_iff₀ hτp]; nlinarith
  have hcd : c = (1 - δ) * d := by rw [hce, hde]; ring
  have hJ : d - c = δ * d := by rw [hcd]; ring
  have hd0 : 0 < d := by have : 0 < q ^ 12 := by positivity
                         linarith
  set a := c - 1 with hae
  have ha : (X₀ : ℝ) ≤ a := by rw [hae, hcd]; nlinarith
  have had : a ≤ d := by rw [hae, hcd]; nlinarith
  have ha0 : 0 < a := by linarith
  -- `h = a^{θ/2} ≤ d^{1/4}`, `d^{1/4} ≥ 0.99 q³`
  have hθ := hc.hθ
  have hθ4 : θ / 2 ≤ 1 / 4 := by linarith [hθ.2]
  have hθ0 : 0 ≤ θ / 2 := by linarith [hθ.1]
  set h := a ^ (θ / 2) with hhe
  have hh0 : 0 < h := Real.rpow_pos_of_pos ha0 _
  set s := d ^ (1 / 4 : ℝ) with hse
  have hs4 : s ^ 4 = d := by
    rw [hse, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; norm_num
  have hs0 : 0 < s := Real.rpow_pos_of_pos hd0 _
  have hhs : h ≤ s := by
    rw [hhe, hse]
    calc a ^ (θ / 2) ≤ a ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hθ4
      _ ≤ d ^ (1 / 4 : ℝ) := Real.rpow_le_rpow ha0.le had (by norm_num)
  have hsq : 0.99 * q ^ 3 ≤ s := by
    by_contra hlt; push_neg at hlt
    have : s ^ 4 < (0.99 * q ^ 3) ^ 4 := pow_lt_pow_left₀ hlt hs0.le (by norm_num)
    have e : (0.99 * q ^ 3) ^ 4 = 0.96059601 * q ^ 12 := by ring
    have : 0 < q ^ 12 := by positivity
    linarith
  -- `δ d ≥ 1164 q · h` and `δ d ≥ 5.82 H q⁴`
  have hδd1 : 5.82 * H * q ^ 4 ≤ δ * d := by
    have : 6 * H * (0.97 * q ^ 12) ≤ δ * q ^ 8 * d := by
      apply mul_le_mul hδ6 hdq (by positivity) (by positivity)
    have e : 6 * H * (0.97 * q ^ 12) = 5.82 * H * q ^ 4 * q ^ 8 := by ring
    have e2 : δ * q ^ 8 * d = δ * d * q ^ 8 := by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_right this hq8p
  have hδdh : 1164 * h ≤ δ * d := by
    -- `δ d = δ s⁴ ≥ s (δ s³)`, `δ s³ ≥ (6H/q⁸) (0.97 q⁹) ≥ 1164 q ≥ 1164`
    have hs3 : 0.97 * q ^ 9 ≤ s ^ 3 := by
      have : (0.99 * q ^ 3) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by positivity) hsq 3
      nlinarith [pow_pos hq0 9]
    have h1 : 6 * H * (0.97 * q ^ 9) ≤ δ * q ^ 8 * s ^ 3 :=
      mul_le_mul hδ6 hs3 (by positivity) (by positivity)
    have h2 : 1164 * q ≤ δ * s ^ 3 := by
      have e : 6 * H * (0.97 * q ^ 9) = 5.82 * H * q * q ^ 8 := by ring
      have e2 : δ * q ^ 8 * s ^ 3 = δ * s ^ 3 * q ^ 8 := by ring
      rw [e, e2] at h1
      have := le_of_mul_le_mul_right h1 hq8p
      nlinarith
    have h3 : 1164 ≤ δ * s ^ 3 := by linarith
    calc 1164 * h ≤ 1164 * s := by linarith
      _ ≤ δ * s ^ 3 * s := mul_le_mul_of_nonneg_right h3 hs0.le
      _ = δ * d := by rw [← hs4]; ring
  -- the times
  have hlogd : Real.log d ≤ d / 1000 + 7 := by
    have := Real.log_le_sub_one_of_pos (show 0 < d / 1000 by positivity)
    rw [Real.log_div hd0.ne' (by norm_num)] at this
    have : Real.log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      rw [e]; nlinarith
    linarith
  have hδd : δ * d ≤ d := by nlinarith
  have hXx : 20 * (X₀ : ℝ) ≤ x := by nlinarith
  have ht1 : d + 26 * Real.log d + 2 < t₀ := by nlinarith
  have ht2 : 2 * (d + h) + 2 * X₀ + 4 ≤ t₀ := by nlinarith
  -- the count of `N`
  have hNc := Ncount_le D hc hev hG hN ha had ht1 ht2
  rw [← hhe] at hNc
  have hla := lagD_le hc (x := x) ha (by linarith)
  have hld := lagD_le hc (x := x) (ha.trans had) (by linarith)
  have hHc : capH X₀ x = H := by rw [hHe]; exact (Hc_eq hxX).symm
  rw [hHc] at hla hld
  -- the absorbed term is tiny
  have hX8 : (10 : ℝ) ^ 8 ≤ X₀ := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hc.hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  have hq4 : 500 ≤ q ^ 4 := by
    by_contra hlt; push_neg at hlt
    have : (q ^ 4) ^ 3 < 500 ^ 3 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have e : (q ^ 4) ^ 3 = q ^ 12 := by ring
    linarith
  have hδdH : 2910 * H ≤ δ * d := by nlinarith
  have hla4 : Real.log a ^ (-4 : ℤ) ≤ 1 / 10 ^ 32 := by
    have hl := (logs_of_ge hX0 hc.hX ha).1
    rw [zpow_neg, zpow_ofNat, one_div]
    apply inv_anti₀ (by positivity)
    have := pow_le_pow_left₀ (by norm_num) hl 4
    norm_num at this ⊢; linarith
  have hla40 : 0 ≤ Real.log a ^ (-4 : ℤ) := by
    have := (logs_of_ge hX0 hc.hX ha).1
    exact zpow_nonneg (by linarith) _
  have hd100 : 100 ≤ d := by nlinarith
  have hratio : (d + h) / a ≤ 1.4 := by
    rw [div_le_iff₀ ha0, hae, hcd]; nlinarith
  have hratio1 : 1 ≤ (d + h) / a := by rw [le_div_iff₀ ha0]; linarith
  have hpowr : (d + h) ^ (θ / 2) ≤ 1.4 * h := by
    have e : (d + h) ^ (θ / 2) = ((d + h) / a) ^ (θ / 2) * h := by
      rw [Real.div_rpow (by linarith) ha0.le, hhe, div_mul_cancel₀ _ (by positivity)]
    rw [e]
    have : ((d + h) / a) ^ (θ / 2) ≤ (d + h) / a := by
      calc ((d + h) / a) ^ (θ / 2) ≤ ((d + h) / a) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hratio1 (by linarith)
        _ = (d + h) / a := Real.rpow_one _
    nlinarith
  have hda : d - a = δ * d + 1 := by rw [hae, hcd]; ring
  have habs : ((d - a) / h + 2) * ((d + h) ^ (θ / 2) * Real.log a ^ (-4 : ℤ)) ≤
      δ * d / 10 ^ 30 := by
    have h1 : (d + h) ^ (θ / 2) * Real.log a ^ (-4 : ℤ) ≤ 1.4 * h * (1 / 10 ^ 32) :=
      mul_le_mul hpowr hla4 hla40 (by positivity)
    have h2 : 0 ≤ (d - a) / h + 2 := by
      have : 0 ≤ (d - a) / h := div_nonneg (by linarith) hh0.le
      linarith
    calc ((d - a) / h + 2) * ((d + h) ^ (θ / 2) * Real.log a ^ (-4 : ℤ))
        ≤ ((d - a) / h + 2) * (1.4 * h * (1 / 10 ^ 32)) := mul_le_mul_of_nonneg_left h1 h2
      _ = 1.4 * (d - a + 2 * h) / 10 ^ 32 := by field_simp
      _ ≤ δ * d / 10 ^ 30 := by
          rw [hda, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- the elements `m'` of `Mset_j` lie in `(a, d]`, injectively
  have hmaps : ∀ m ∈ P.Mset (tJ θ X₀ ω) x δ j, m.erase j ∈ P.elems d \ P.elems a := by
    intro m hm
    obtain ⟨hval, -⟩ := Mset_val ω hm
    obtain ⟨-, -, -, -, h1, h2⟩ := Finset.mem_filter.mp hm
    have h1' : x * (1 - δ) ≤ τ * (p * P.val (m.erase j)) := by rw [← hval]; exact h1
    have h2' : τ * (p * P.val (m.erase j)) < x := by rw [← hval]; exact h2
    have hv1 : c ≤ P.val (m.erase j) := by rw [hce, div_le_iff₀ hτp]; nlinarith
    have hv2 : P.val (m.erase j) < d := by rw [hde, lt_div_iff₀ hτp]; nlinarith
    rw [Finset.mem_sdiff, BeurlingSystem.mem_elems, BeurlingSystem.mem_elems]
    exact ⟨hv2.le, by rw [hae]; linarith⟩
  have hinj : Set.InjOn (fun m : ℕ →₀ ℕ => m.erase j)
      (P.Mset (tJ θ X₀ ω) x δ j : Set (ℕ →₀ ℕ)) := by
    intro m hm m' hm' h
    simp only at h
    rw [(Mset_val ω hm).2, (Mset_val ω hm').2, h]
  have hcard := Finset.card_le_card_of_injOn (fun m : ℕ →₀ ℕ => m.erase j) hmaps hinj
  have hsub : P.elems a ⊆ P.elems d := fun e he => by
    rw [BeurlingSystem.mem_elems] at he ⊢; linarith
  rw [Finset.card_sdiff_of_subset hsub] at hcard
  have hNd : P.N d = ((P.elems d).card : ℝ) := by
    unfold BeurlingSystem.N
    have : {e : ℕ →₀ ℕ | P.val e ≤ d} = (P.elems d : Set (ℕ →₀ ℕ)) := by
      ext e; simp [BeurlingSystem.mem_elems]
    rw [this, Set.ncard_coe_finset]
  have hNa : P.N a = ((P.elems a).card : ℝ) := by
    unfold BeurlingSystem.N
    have : {e : ℕ →₀ ℕ | P.val e ≤ a} = (P.elems a : Set (ℕ →₀ ℕ)) := by
      ext e; simp [BeurlingSystem.mem_elems]
    rw [this, Set.ncard_coe_finset]
  have hcard' : (((P.Mset (tJ θ X₀ ω) x δ j).card : ℕ) : ℝ) ≤ P.N d - P.N a := by
    rw [hNd, hNa, ← Nat.cast_sub (Finset.card_le_card hsub)]
    exact_mod_cast hcard
  -- conclusion: `#Mset ≤ 2.03 δd ≤ 4 δx/p²`
  have hdp : δ * d ≤ 1.0102 * (δ * x / p ^ 2) := by
    rw [hde, mul_div_assoc', div_le_iff₀ hτp]
    have hp20 : 0 < p ^ 2 := by positivity
    have : δ * x / p ^ 2 * (τ * p) ≥ δ * x / p ^ 2 * (0.99 * p * p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have e : δ * x / p ^ 2 * (0.99 * p * p) = 0.99 * (δ * x) := by field_simp
    nlinarith [mul_pos hδ0 hx0]
  have e4 : 4 * δ * x / p ^ 2 = 4 * (δ * x / p ^ 2) := by ring
  rw [e4]
  have hδxp : 0 ≤ δ * x / p ^ 2 := by positivity
  rw [hda] at hNc habs
  have hdiv : δ * d / 10 ^ 30 ≤ δ * d / 1000 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  have hfin : 2.00005 * (δ * d + 1) + 1 + δ * d / 1000 + (4 * H + 5) + (4 * H + 5) ≤
      2.03 * (δ * d) := by linarith
  have hchain : (((P.Mset (tJ θ X₀ ω) x δ j).card : ℕ) : ℝ) ≤ 2.03 * (δ * d) := by linarith
  linarith

end Queue6

end
