module

public import RequestProject.Beurling.Queue6.CompEq
public import RequestProject.Beurling.Queue6.Noise3

/-!
# Truncation is inactive at every jitter offset (Lemma 5.22, "Truncation is inactive on `Good`")

For a window `W = [a, b)` of `𝒲'_u` and the prime decided at relative slot `k + 1`, the cofactor
count `Φᴬ_k(ω, t) = #{m ∈ cofP k : a ≤ m t < b, m t ∉ 𝒜}` is at most `2 M₁(u)` for **every**
offset `t`, on the cluster event at the height `u` (Corollary 6.12 read for a hypothetical
landing point): a counted `m` has `t ≥ y(mt) = y(u)` (`mt` is not absorbed), so the cofactors lie
in the window `[a/t, b/t)` of length `≤ |W|/y(u) ≪ L^{-6}`, which two grid windows of the
cluster event cover (`two_window_cover`).

* `dyadicScale_eq` : the dyadic scale of `n ∈ [u, 2u)` is `u`;
* `winCount_le` : a short window of the realised system holds `≤ 2 M` elements on the cluster
  event (the counting core of `xcount_le`);
* `PhiA_le_trunc` : `Φᴬ_k(ω, t) ≤ 2 M₁(u)` for every `t`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono SlotModel AbsorbEmpty
open scoped ENNReal

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-- The dyadic scale of `n ∈ [X₀ 2^m, X₀ 2^{m+1})` is `X₀ 2^m`. -/
lemma dyadicScale_eq {X : ℝ} (hX : 0 < X) (m : ℕ) {n : ℝ} (h1 : 2 ^ m * X ≤ n)
    (h2 : n < 2 * (2 ^ m * X)) : dyadicScale X n = 2 ^ m * X := by
  unfold dyadicScale
  have hr : 0 < n / X := by
    have : 0 < 2 ^ m * X := by positivity
    exact div_pos (by linarith) hX
  have hlog : Int.log 2 (n / X) = m := by
    apply le_antisymm
    · have : n / X < (2 : ℝ) ^ ((m : ℤ) + 1) := by
        rw [zpow_add_one₀ (by norm_num), zpow_natCast, div_lt_iff₀ hX]; linarith
      have this' : n / X < ((2 : ℕ) : ℝ) ^ ((m : ℤ) + 1) := by push_cast; exact this
      have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hr).mp this'
      omega
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hr).mp
      push_cast
      rw [zpow_natCast, le_div_iff₀ hX]; linarith
  rw [hlog, zpow_natCast]; ring

section Count

variable {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **A short window of the realised system** holds at most `2M` elements on the cluster event
(the counting core of `xcount_le`, Corollary 6.12). -/
theorem winCount_le (hok : RealisedOK M (capH X₀) U) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hslot : ∀ l, 1 ≤ l → (X₀ : ℝ) ≤ M.slot l)
    {w δ Z Mc : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hwZ : w ≤ Z)
    (hlen : 3 * (X₀ : ℝ) / 4 ≤ w → δ ≤ 2 / Real.log w ^ 6)
    (hcl : ClusterUpTo (realisedSystem M (capH X₀) U) X₀ Z Mc) (hMc : 1 / 2 ≤ Mc) :
    (({f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧
      idxVal M (capH X₀) U f < w + δ}.ncard : ℕ) : ℝ) ≤ 2 * Mc := by
  have hX1 : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := two_pow_le_of_logX (Nat.cast_nonneg _) hX
  have hjit := jit_ge hX hU hslot
  by_cases hlow : w + δ ≤ 7 / 8 * (X₀ : ℝ)
  · have := low_le_one hok hjit hδ1 hlow
    have : (({f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧
        idxVal M (capH X₀) U f < w + δ}.ncard : ℕ) : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · push_neg at hlow
    rw [ncard_win_eq hok]
    have hw : 3 * (X₀ : ℝ) / 4 ≤ w := by linarith
    exact two_window_cover _ (by linarith) (by linarith) hcl hw hwZ (hlen hw)

end Count

section Trunc

variable (hc : Cond θ X₀)
include hc

lemma hslot_CM (ω : JitterΩ) : ∀ l, 1 ≤ l → (X₀ : ℝ) ≤ (CM θ X₀ ω).slot l := by
  intro l hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  exact slotF_ge hc k ω

/-- `y(u) ≥ 2133 H(u) M₁(u) (log u)⁹` and `H(u) ≥ (log u)²`, for `u ≥ X₀`. -/
lemma absorbYAt_ge {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    2133 * capH X₀ u * Real.log u ^ 9 ≤ absorbYAt X₀ u ∧ Real.log u ^ 2 ≤ capH X₀ u := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, hll⟩ := logs_of_ge hX0 hc.hX hu
  have hM := QueueBound.one_le_capM1 hX0 hc.hX hu
  have hH := capH_ge_one hX0 hc.hX hu
  set L := Real.log u
  have hL0 : 0 ≤ L := by linarith
  have hL0' : absorbL0 X₀ u ≥ 48 * capM1 X₀ u * L ^ 3 / 0.15 ^ 2 := le_max_right _ _
  have hL3 : 2133 * L ^ 3 ≤ absorbL0 X₀ u := by
    refine le_trans ?_ hL0'
    rw [le_div_iff₀ (by norm_num)]
    have : 0 ≤ L ^ 3 := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold absorbYAt
    have hL6 : 0 ≤ L ^ 6 := by positivity
    have hH0 : 0 ≤ capH X₀ u := by linarith
    calc 2133 * capH X₀ u * L ^ 9 = capH X₀ u * (2133 * L ^ 3) * L ^ 6 := by ring
      _ ≤ capH X₀ u * absorbL0 X₀ u * L ^ 6 := by gcongr
  · have h1 : Real.exp (8 * Real.log L ^ 2) ≤ capH X₀ u := le_max_left _ _
    have hl18 : 18 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have he := Real.exp_one_lt_d9
      have e : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
      have : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he.le 18
      rw [e]; nlinarith
    have h2 : L ^ 2 = Real.exp (2 * Real.log L) := by
      rw [show 2 * Real.log L = Real.log (L ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [h2]
    refine le_trans (Real.exp_le_exp.mpr ?_) h1
    nlinarith

set_option maxHeartbeats 800000 in
/-- **Truncation is inactive at every offset**: on the cluster event at the height `u`, for a
window `[a, b)` of `𝒲'_u`, `Φᴬ_k(ω, t) ≤ 2 M₁(u)` for every `t`. -/
theorem PhiA_le_trunc {m : ℕ} {a b : ℤ} (hW : AdmW X₀ m a b) (ω : JitterΩ) (k : ℕ)
    (hcl : ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (capM1 X₀ (uS X₀ m))) (t : ℝ) :
    PhiA θ X₀ k a b (ω, t) ≤ ENNReal.ofReal (2 * capM1 X₀ (uS X₀ m)) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set u := uS X₀ m with hudef
  have hu : (X₀ : ℝ) ≤ u := X₀_le_uS (X₀ := X₀) hX0p m
  obtain ⟨hua, hab, hb2, hlen⟩ := hW
  rw [← hudef] at hua hb2 hlen
  have hM := QueueBound.one_le_capM1 hX0 hc.hX hu
  obtain ⟨hy, hHL⟩ := absorbYAt_ge hc hu
  obtain ⟨hL, -, -⟩ := logs_of_ge hX0 hc.hX hu
  set L := Real.log u
  set y := absorbYAt X₀ u
  have hH := capH_ge_one hX0 hc.hX hu
  have hL9 : 1 ≤ L ^ 9 := one_le_pow₀ (by linarith)
  have hy0 : 0 < y := by nlinarith
  unfold PhiA
  split_ifs with hXt
  swap
  · exact zero_le
  set S : Set (PIdx X₀ →₀ ℕ) := {e | e ∈ cofP θ X₀ k ω ∧ (a : ℝ) ≤ eval (DD θ X₀ ω) e * t ∧
    eval (DD θ X₀ ω) e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e * t) ∧
      t < absorbY X₀ (eval (DD θ X₀ ω) e * t))} with hSdef
  have ht0 : 0 < t := by have := Xm_pos hc; linarith
  have hSfin : S.Finite := by
    refine (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
      (b / t)).subset fun e he => ?_
    refine ⟨he.1.1, pval_gt_one hc he.1.1, ?_⟩
    rw [le_div_iff₀ ht0]; exact he.2.2.1.le
  have hts : (∑' e : PIdx X₀ →₀ ℕ, if e ∈ cofP θ X₀ k ω ∧ (a : ℝ) ≤ eval (DD θ X₀ ω) e * t ∧
      eval (DD θ X₀ ω) e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e * t) ∧
        t < absorbY X₀ (eval (DD θ X₀ ω) e * t)) then (1 : ℝ≥0∞) else 0) = (S.ncard : ℝ≥0∞) := by
    rw [← tsum_ite_eq_ncard hSfin]
    exact tsum_congr fun e => by
      by_cases h : e ∈ S
      · rw [if_pos h]; exact if_pos h
      · rw [if_neg h]; exact if_neg h
  show (∑' e : PIdx X₀ →₀ ℕ, _) ≤ _
  rw [hts]
  rcases S.eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he, Set.ncard_empty]; simp
  -- `t ≥ y(u)`
  have hty : y ≤ t := by
    obtain ⟨-, h1, h2, h3⟩ := he0
    have hn1 : u ≤ eval (DD θ X₀ ω) e0 * t := by
      have : (u : ℝ) ≤ a := hua; linarith
    have hlog : 10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e0 * t) := by
      have := Real.log_le_log (by linarith) hn1; linarith
    have hds : dyadicScale X₀ (max X₀ (eval (DD θ X₀ ω) e0 * t)) = u := by
      rw [max_eq_right (hu.trans hn1)]
      exact dyadicScale_eq hX0p m (by rw [hudef] at hn1; unfold uS at hn1; exact hn1)
        (by have : (b : ℝ) ≤ 2 * u := hb2; rw [hudef] at this; unfold uS at this; linarith)
    by_contra hlt
    push_neg at hlt
    apply h3
    refine ⟨hlog, ?_⟩
    unfold absorbY
    rw [hds]; exact hlt
  -- the cofactor window
  set M := CM θ X₀ ω
  set w := (a : ℝ) / t
  set δ := ((b : ℝ) - a) / t
  have hT : S ⊆ mapE M '' {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) (Ucl ω) f ∧
      idxVal M (capH X₀) (Ucl ω) f < w + δ} := by
    intro e he
    obtain ⟨⟨hlive, -, -⟩, h1, h2, -⟩ := he
    obtain ⟨f, hf⟩ := exists_mapE (M := M) (U := Ucl ω) hlive
    refine ⟨f, ⟨?_, ?_⟩, hf⟩
    · have hv := eval_mapE M (Ucl ω) f
      rw [hf] at hv
      rw [← hv, div_le_iff₀ ht0]; exact h1
    · have hv := eval_mapE M (Ucl ω) f
      rw [hf] at hv
      have : w + δ = (b : ℝ) / t := by simp only [w, δ]; field_simp; ring
      rw [this, ← hv, lt_div_iff₀ ht0]; exact h2
  have hok : RealisedOK M (capH X₀) (Ucl ω) := by
    show RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)
    rw [Mcl_eq hc]; exact limModel_realisedOK (hc.std ω)
  have hTfin : {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) (Ucl ω) f ∧
      idxVal M (capH X₀) (Ucl ω) f < w + δ}.Finite :=
    (finite_idxVal_le hok (w + δ)).subset fun f hf => hf.2.le
  have hc1 : S.ncard ≤ {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) (Ucl ω) f ∧
      idxVal M (capH X₀) (Ucl ω) f < w + δ}.ncard :=
    (Set.ncard_le_ncard hT (hTfin.image _)).trans (Set.ncard_image_le hTfin)
  -- the window is short
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have hδy : δ ≤ ((b : ℝ) - a) / y := div_le_div_of_nonneg_left hba hy0 hty
  have hlenL : ((b : ℝ) - a) / y ≤ 1 / (2000 * L ^ 9) := by
    rw [div_le_div_iff₀ hy0 (by positivity)]
    have : ((b - a : ℤ) : ℝ) = (b : ℝ) - a := by push_cast; ring
    rw [this] at hlen
    have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have h1 : (b : ℝ) - a ≤ 1.04 * capH X₀ u := by nlinarith
    have hL9' : 0 ≤ L ^ 9 := by positivity
    have h2 : ((b : ℝ) - a) * (2000 * L ^ 9) ≤ 1.04 * capH X₀ u * (2000 * L ^ 9) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 1.04 * capH X₀ u * (2000 * L ^ 9) ≤ 2133 * capH X₀ u * L ^ 9 := by nlinarith
    linarith
  have hsmall : 1 / (2000 * L ^ 9) ≤ 2 / L ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L ^ 6 ≤ L ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hδ0 : 0 ≤ δ := div_nonneg hba ht0.le
  have hδ1 : δ < 1 := by
    have : 1 / (2000 * L ^ 9) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hwy : w ≤ 2 * u / y := by
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have : (a : ℝ) ≤ 2 * u := by linarith
    calc w = (a : ℝ) / t := rfl
      _ ≤ (a : ℝ) / y := div_le_div_of_nonneg_left (by linarith) hy0 hty
      _ ≤ 2 * u / y := div_le_div_of_nonneg_right this hy0.le
  have hu0 : 0 < u := by linarith
  have hwZ : w ≤ 4 * u / L ^ 11 := by
    refine hwy.trans ?_
    rw [div_le_div_iff₀ hy0 (by positivity)]
    have h11 : L ^ 11 = L ^ 2 * L ^ 9 := by ring
    have : L ^ 2 * L ^ 9 ≤ 2133 * capH X₀ u * L ^ 9 := by
      have : 0 ≤ L ^ 9 := by positivity
      nlinarith
    nlinarith
  have hwu : w ≤ u := by
    refine hwy.trans ?_
    have hHL9 : 1 ≤ capH X₀ u * L ^ 9 := one_le_mul_of_one_le_of_one_le hH hL9
    have hy2 : 2 ≤ y := by linarith
    rw [div_le_iff₀ hy0]
    have := mul_le_mul_of_nonneg_left hy2 hu0.le
    linarith
  have hlen' : 3 * (X₀ : ℝ) / 4 ≤ w → δ ≤ 2 / Real.log w ^ 6 := by
    intro hw
    have h16 := X₀_ge_two_pow hc.hX
    have hw1 : 1 < w := by linarith
    have hlw : 0 < Real.log w := Real.log_pos hw1
    have hlog : Real.log w ≤ L := Real.log_le_log (by linarith) hwu
    have h6 : 2 / L ^ 6 ≤ 2 / Real.log w ^ 6 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlw.le hlog 6)
    linarith
  have hcount := winCount_le hok hc.hX (fun j => clamp01_mem (ω j)) (hslot_CM hc ω) hδ0 hδ1
    hwZ hlen' hcl (by linarith)
  have : (S.ncard : ℝ) ≤ 2 * capM1 X₀ u := by
    refine le_trans ?_ hcount
    exact_mod_cast hc1
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal this

end Trunc

end Queue6

end
