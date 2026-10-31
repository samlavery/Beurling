module

public import RequestProject.Beurling.Model.TBoundGood

/-!
# `T(x) ≤ 3x` from the queue constraints and the cluster events alone

As `Model/TBoundGood.lean`, with the good event `Good(< t)` replaced by its parts actually
read: the queue constraints `QC(< t)`, the cluster events E1 of time `< t` and the target bounds
`tB m` of time `< t`. By induction on `n` (`tB_all_of_QE`), the target bounds themselves follow
from the queue constraints and the E1 events: every `tB n` with `t(tB n) ≤ t` holds on
`QC(< t) ∩ {E1 of time < t} ∩ NiceEv`. This is the form read by Lemma 5.22 (`GoodE1`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6 SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section QE

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc in
/-- **The queue bound at the slot of `x`** on `QC(< t)`, for `x + 26 log x + 2 < t`. -/
theorem queue_of_QE {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (h0 : Std θ X₀ ω) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxt : x + 26 * Real.log x + 2 < t) :
    (h0.limModel.queue (h0.limModel.slotIdx x) : ℝ) ≤
      queueBScale X₀ (h0.limModel.slot (h0.limModel.slotIdx x)) := by
  have hM := Mcl_eq_lim hc h0
  set j := h0.limModel.slotIdx x
  have hs := limModel_slotIdx_succ h0 hx
  have htq : tq θ X₀ j ω < t := by
    unfold tq
    have h1 : ((⌈(CM θ X₀ ω).slot (j + 1)⌉₊ + 1 : ℕ) : ℝ) < t := by
      have hc1 := Nat.ceil_lt_add_one (show 0 ≤ (CM θ X₀ ω).slot (j + 1) by
        rw [show CM θ X₀ ω = h0.limModel from hM]; linarith [h0.limModel.one_le_slot (j + 1)])
      push_cast
      rw [show CM θ X₀ ω = h0.limModel from hM] at hc1 ⊢
      linarith
    exact_mod_cast h1
  have hq := hQC j htq
  simp only [okQ, mem_setOf_eq] at hq
  rw [show CM θ X₀ ω = h0.limModel from hM] at hq
  exact hq

include hc hev in
/-- **The cluster event at the height `v`** on `Good(< t)` (Proposition 6.11 through the
window model), given a scale `m` with `t(tB m) < t` and `8/7 (2 · 4v/log¹¹ v + 1) ≤ 2^m X₀/2`,
and `⌈v⌉ < t`. -/
theorem cluster_of_QE {t : ℕ} {ω : JitterΩ}
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hTB : ∀ m, ttB X₀ m < t → ω ∈ tB (θ := θ) (X₀ := X₀) m) (h0 : Std θ X₀ ω)
    (hSG : ω ∈ SG (θ := θ) (X₀ := X₀)) {v : ℝ} (hv : (X₀ : ℝ) ≤ v) (hvt : ⌈v⌉₊ < t) {m : ℕ}
    (hm : 8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2)
    (hmt : ttB X₀ m < t) :
    ClusterUpTo (realisedSystem h0.limModel (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11)
      (capM1 X₀ v) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hc.hX hv
  have hv0 : 0 < v := by linarith [one_lt_of_logX hX0 hc.hX]
  have hZv : 4 * v / Real.log v ^ 11 ≤ v := by
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ≤ Real.log v ^ 11 := by
      calc (4 : ℝ) ≤ Real.log v := by linarith
        _ ≤ Real.log v ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith
  have hTBm : ω ∈ tB (θ := θ) (X₀ := X₀) m :=
    hTB m hmt
  have hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1)) :=
    tBound_mono hm hTBm
  have hcl : ∀ n, zH X₀ n ≤ 4 * v / Real.log v ^ 11 → ω ∈ EclW hc hev n := by
    intro n hn
    have ht1 : tE1 X₀ n < t := by
      have := cluster_time_le hc.hX hv hn
      unfold tE1
      exact lt_of_le_of_lt (Nat.ceil_mono this) hvt
    have := hE1 n ht1
    simpa [E1ev, dif_pos (And.intro hc hev)] using this
  have := clusterUpTo_of_eclW hc hev h0.hU hSG hZv hTB hcl
  rwa [constructedModel_eq h0] at this

include hc hev in
/-- **Lemma 6.26 on `Good(< t(tB n))`** (`n ≥ 2`) at every height `u < x ≤ 2^n X₀/2`: the
horizon-local induction `lemma626_horizon`, with the queue bound up to `max(X₀, x/2)` and the
cluster events, all of time `< t(tB n)`. -/
theorem lemma626_QE {n : ℕ} (hn : 2 ≤ n) {ω : JitterΩ}
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) (ttB X₀ n))
    (hE1 : ∀ n', tE1 X₀ n' < ttB X₀ n → ω ∈ E1ev θ X₀ n')
    (hTB : ∀ m, ttB X₀ m < ttB X₀ n → ω ∈ tB (θ := θ) (X₀ := X₀) m)
    (hN : ω ∈ NiceEv θ X₀) {x : ℝ} (hxW : x ≤ 2 ^ n * (X₀ : ℝ) / 2) {u : ℝ}
    (hu : (X₀ : ℝ) ≤ u) (hux : u < x) :
    (localCountA (absSet X₀ (DF θ X₀ ω)) u (u + u ^ (thetaB θ)) : ℝ) ≤
      u ^ (thetaB θ) * Real.log u ^ (-4 : ℤ) := by
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXb : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow hX
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  set W := 2 ^ n * (X₀ : ℝ) / 2 with hW
  have hW2 : 2 * (X₀ : ℝ) ≤ W := by
    have : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [hW]; nlinarith
  have ht0 : (W : ℝ) + 1 ≤ ttB X₀ n := by
    unfold ttB; push_cast; linarith [Nat.le_ceil W]
  -- the scale `n - 1`
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hWn' : 2 ^ n' * (X₀ : ℝ) / 2 = W / 2 := by rw [hW, pow_succ]; ring
  have httB : ttB X₀ n' < ttB X₀ (n' + 1) := by
    unfold ttB
    have h1 : ⌈2 ^ n' * (X₀ : ℝ) / 2⌉₊ < ⌈2 ^ (n' + 1) * (X₀ : ℝ) / 2⌉₊ := by
      rw [hWn', ← hW]
      have hlt : (⌈W / 2⌉₊ : ℝ) < ⌈W⌉₊ := by
        have := Nat.ceil_lt_add_one (show 0 ≤ W / 2 by linarith)
        have := Nat.le_ceil W
        linarith
      exact_mod_cast hlt
    omega
  have hscale : ∀ v, (X₀ : ℝ) ≤ v → v ≤ W →
      8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ 2 ^ n' * (X₀ : ℝ) / 2 := by
    intro v hv hvW
    rw [hWn']
    obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hX hv
    have hv0 : 0 < v := by linarith
    have h11 : (100 : ℝ) ≤ Real.log v ^ 11 := by
      have : (10 ^ 8 : ℝ) ≤ Real.log v ^ 11 :=
        hl.trans (le_self_pow₀ (by linarith) (by norm_num))
      linarith
    have : 4 * v / Real.log v ^ 11 ≤ v / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    nlinarith
  have hceil : ∀ v, v ≤ W → ⌈v⌉₊ < ttB X₀ (n' + 1) := by
    intro v hvW
    unfold ttB
    have := Nat.ceil_mono hvW
    rw [← hW]; omega
  have hclv : ∀ v, (X₀ : ℝ) ≤ v → v ≤ W →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v) :=
    fun v hv hvW => cluster_of_QE hc hev hE1 hTB h0 hSG hv (hceil v hvW) (hscale v hv hvW) httB
  -- the horizon `Z = max(X₀, x/2)`
  set Z := max (X₀ : ℝ) (x / 2) with hZ
  have hZX : (X₀ : ℝ) ≤ Z := le_max_left _ _
  have hZW : Z ≤ W / 2 := max_le (by linarith) (by linarith)
  have hQ : ∀ y, (X₀ : ℝ) ≤ y → y ≤ Z →
      (M.queue (M.slotIdx y) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx y)) := by
    intro y hy hyZ
    refine queue_of_QE hc hQC h0 hy ?_
    have hy0 : 0 < y := by linarith
    have hlog : Real.log y ≤ y / 100 + 98 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < y / 100 by positivity)
      rw [Real.log_div hy0.ne' (by norm_num)] at h
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
      linarith
    have : y ≤ W / 2 := hyZ.trans hZW
    linarith
  have hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v) :=
    fun v hv hvZ => hclv v hv (by linarith)
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have h2y : 2 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Z := by
    rcases two_absorbYAt_two_le hX0 hX hu with hy | hy
    · exact hy.le.trans hZX
    · exact hy.trans ((by linarith : u / 2 ≤ x / 2).trans (le_max_right _ _))
  have hmain := lemma626_horizon hc.hθ hX M ω hU (limModel_placed_infinite h0)
    (constructionScale X₀) hT Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hZX hQ hcl u hu h2y
    (hclv u hu (by linarith))
  have hA : realisedA M (capH X₀) ω = absSet X₀ (DF θ X₀ ω) := by
    rw [realisedA_eq hok hnc]
    unfold DF
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [← hA]
  exact hmain

include hc hev in
/-- **`T(x) ≤ 3x` up to `2^n X₀/2` on `Good(< t(tB n))`** (Lemma 3.4 on the good event), off the
null set `NiceEvᶜ`. -/
theorem tB_of_QE (n : ℕ) {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) (ttB X₀ n))
    (hE1 : ∀ n', tE1 X₀ n' < ttB X₀ n → ω ∈ E1ev θ X₀ n')
    (hTB : ∀ m, ttB X₀ m < ttB X₀ n → ω ∈ tB (θ := θ) (X₀ := X₀) m)
    (hN : ω ∈ NiceEv θ X₀) : ω ∈ tB (θ := θ) (X₀ := X₀) n := by
  intro x hx hxW
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rcases lt_or_ge n 2 with hn | hn
  · -- `x = X₀`
    have hxX : x ≤ X₀ := by
      have : (2 : ℝ) ^ n ≤ 2 := by
        calc (2 : ℝ) ^ n ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 2 := by norm_num
      nlinarith
    have hx' : x = X₀ := le_antisymm hxX hx
    rw [hx', Mcl_eq hc]
    rw [(hc.std ω).limModel_T_X₀]
    linarith
  · exact T_le_three_of_loc hc hx fun u hu hux => lemma626_QE hc hev hn hQC hE1 hTB hN hxW hu hux


include hc hev in
/-- **The target bounds from the queue constraints and the cluster events** (induction on `n`):
on `QC(< t) ∩ {E1 of time < t} ∩ NiceEv`, every `tB n` with `t(tB n) ≤ t` holds. -/
theorem tB_all_of_QE {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) :
    ∀ n, ttB X₀ n ≤ t → ω ∈ tB (θ := θ) (X₀ := X₀) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro hn
  refine tB_of_QE hc hev n (QC_anti _ _ hn hQC) (fun n' h => hE1 n' (lt_of_lt_of_le h hn))
    (fun m hm => IH m ?_ (le_trans hm.le hn)) hN
  -- `t(tB m) < t(tB n)` forces `m < n`
  by_contra hmn
  push_neg at hmn
  have : ttB X₀ n ≤ ttB X₀ m := by
    unfold ttB
    have h2 : (2 : ℝ) ^ n * (X₀ : ℝ) / 2 ≤ 2 ^ m * (X₀ : ℝ) / 2 := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmn
      have h0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
      nlinarith
    have := Nat.ceil_mono h2
    omega
  omega

end QE

end BModel
