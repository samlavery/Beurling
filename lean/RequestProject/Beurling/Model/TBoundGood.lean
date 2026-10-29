module

public import RequestProject.Beurling.Model.HBSGood
public import RequestProject.Beurling.Model.Top
public import RequestProject.Beurling.Model.TiesProof
public import RequestProject.Beurling.Model.Land
public import RequestProject.Beurling.Queue6.Path

/-!
# Lemma 6.26 on `Good(< t)` and the target bound `T(x) ≤ 3x` (Lemma 3.4)

On `Good(< t)` (`Queue6.G0`), the queue constraints `Q_j ≤ B(s_j)` with time
`⌈s_{j+1}⌉ + 1 < t` and the events of Table 1 with time `< t` hold. From them:

* `queue_of_G0` : the queue bound at the slot of every height `x` with `x + 26 log x + 2 < t`
  (consecutive slots are at most `13 log` apart, `limModel_slot_succ`);
* `cluster_of_G0` : the cluster event `ClusterUpTo P(ω) X₀ (4v/log¹¹ v) M̄₁(v)` at a height `v`
  with `⌈v⌉ < t`, given a scale `m` with `t(tB m) < t` covering `8/7 (2 · 4v/log¹¹ v + 1)`
  (Proposition 6.11 read through the window model, `clusterUpTo_of_eclW`);
* `lemma626_G0` : **Lemma 6.26 on `Good(< t)`** at the heights `u < x ≤ 2^n X₀/2`,
  `t = t(tB n)`, `n ≥ 2` (the horizon-local induction `lemma626_horizon`, reading the queue
  only up to `max(X₀, x/2)` and the cluster events only at times `< t`);
* `tB_of_G0`, `tbound_G0` : `T(x) ≤ 3x` up to `2^n X₀/2` on `Good(< t(tB n))` off a null set:
  the field `tbound` of `Queue6.QueueInputs`, with no named hypothesis.

The a.s. conditions used are: jitters in `[0, 1]`, all stages good (`SG`), and no ties
(`tiesEvent`, null by `tiesNull`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6 SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **`T(x) ≤ 3x`** (Lemma 3.4 with the crude constant `3`) from Lemma 6.26 at the heights
`u ∈ [X₀, x)`. -/
theorem T_le_three_of_loc (hc : Cond θ X₀) {ω : JitterΩ} {x : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hloc : ∀ u, (X₀ : ℝ) ≤ u → u < x →
      (localCountA (absSet X₀ (DF θ X₀ ω)) u (u + u ^ (θ / 2)) : ℝ) ≤
        u ^ (θ / 2) * Real.log u ^ (-4 : ℤ)) : (Mcl θ X₀ ω).T x ≤ 3 * x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hstd := hc.std ω
  set Dd := DF θ X₀ ω with hDd
  have hDM : Dd = DM hstd.limModel (Ucl ω) := by rw [hDd, DF, Mcl_eq hc]
  have hT : (Mcl θ X₀ ω).T x = targetD θ X₀ Dd x := by
    rw [Mcl_eq hc, hstd.limModel_T_eq x, hDM]
  rw [hT, targetD_split θ Dd hx]
  have hLF : LocFinD Dd := by rw [hDM]; exact locFinD_DM hc.hX hstd.hU _
  -- the continuous part
  have hC := contD_upper_log hc.hθ hc.hX Dd hLF le_rfl hx
  rw [contD_at] at hC
  have hlX : 10 ^ 8 ≤ Real.log X₀ := hc.hX
  have hC' : contD θ X₀ Dd x ≤ 1.01 * (x - X₀) := by
    have h1 : 0.02 / Real.log X₀ ≤ 0.01 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : 0 ≤ x - X₀ := by linarith
    nlinarith
  -- the absorbed count
  set A := absSet X₀ Dd with hA
  have hAfin : LocFin A := absSet_locFin hLF
  have hlow : A ∩ Icc 1 (X₀ : ℝ) = ∅ := by
    have h0 := hstd.countA_X₀
    rw [← hDM] at h0
    unfold countA at h0
    have h0' : (A ∩ Icc 1 (X₀ : ℝ)).ncard = 0 := by exact_mod_cast h0
    exact (Set.ncard_eq_zero (hAfin.finite_Icc _ _)).mp h0'
  have hb0 : 0 ≤ θ / 2 := by linarith [hc.hθ.1]
  have hb1 : θ / 2 ≤ 1 := by linarith [hc.hθ.2]
  have hwin : ∀ u, (X₀ : ℝ) ≤ u → u < x →
      (localCountA A u (u + u ^ (θ / 2)) : ℝ) ≤ u ^ (θ / 2) / 4 := by
    intro u hu hux
    obtain ⟨hLu, -, -⟩ := logs_of_ge hX0 hc.hX hu
    have h4 := four_capH_le hX0 hc.hX hu
    have hu0 : 0 < u := by linarith
    have h := hloc u hu hux
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv] at h
    have hp : 0 ≤ u ^ (θ / 2) := Real.rpow_nonneg hu0.le _
    have h44 : (4 : ℝ) ≤ Real.log u ^ 4 := by
      have : (10 ^ 8 : ℝ) ≤ Real.log u ^ 4 :=
        hLu.trans (le_self_pow₀ (by linarith) (by norm_num))
      linarith
    exact h.trans (div_le_div_of_nonneg_left hp (by norm_num) h44)
  have hcnt := countA_le_of_windows hAfin hX1.le hb0 hlow hwin hx
  have hxb : x ^ (θ / 2) ≤ x := by
    conv_rhs => rw [← Real.rpow_one x]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hb1
  -- the smooth count
  have hS := smoothCount_le_self X₀ (by linarith : (0 : ℝ) ≤ x)
  have hS0 : (0 : ℝ) ≤ Rankin.smoothCount X₀ (X₀ : ℝ) := Nat.cast_nonneg _
  unfold jumpD jumpPart
  rw [← hA]
  linarith

section Slots

variable {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- **Consecutive slots of the constructed model are at most `13 log z` apart** (the slope
`T' ≥ 0.08/log` of Lemma 3.3). -/
lemma limModel_slot_succ {i : ℕ} {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
    (hi : h.limModel.slot i ≤ z - 13 * Real.log z) : h.limModel.slot (i + 1) ≤ z := by
  set M := h.limModel
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hlz, -, -⟩ := logs_of_ge hX0 hX hz
  have hlz0 : 0 < Real.log z := by linarith
  have hs : (X₀ : ℝ) ≤ M.slot i := GreedyRun.slot_ge ⟨M, capH X₀, U, h.limModel_low⟩ i
  have hsz : M.slot i ≤ z := by linarith
  set D := DM M U
  have hD : LocFinD D := locFinD_DM hX h.hU M
  have hC := contD_lower h.hθ hX h.hHB D hD hs hsz
  have hJ := jumpD_mono (X₀ := X₀) D hD hsz
  have h1 : 0.08 * (13 * Real.log z) / Real.log z ≤ 0.08 * (z - M.slot i) / Real.log z :=
    div_le_div_of_nonneg_right (by linarith) hlz0.le
  have h2 : 0.08 * (13 * Real.log z) / Real.log z = 1.04 := by field_simp; norm_num
  have hT : ∀ y, (X₀ : ℝ) ≤ y → M.T y = X₀ + jumpD X₀ D y + contD θ X₀ D y := fun y hy => by
    rw [h.limModel_T_eq y]; exact targetD_split θ D hy
  have hlev := M.level_le_T_slot i
  apply M.slot_le
  refine ⟨by linarith [X₀_ge_two_pow hX], ?_⟩
  unfold SlotModel.level at hlev ⊢
  rw [hT _ hs] at hlev
  rw [hT _ hz]
  push_cast
  linarith

/-- The slot after the slot of `x` starts at most `26 log x` above `x`. -/
lemma limModel_slotIdx_succ {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    h.limModel.slot (h.limModel.slotIdx x + 1) ≤ x + 26 * Real.log x := by
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast hX1.le
  obtain ⟨hs1, -, -, -⟩ := h.limModel.mem_slot hX₀ hx
  obtain ⟨hlx, -, -⟩ := logs_of_ge hX0 hX hx
  have hx0 : 0 < x := by linarith
  set z := x + 26 * Real.log x
  have hz : x ≤ z := by have := Real.log_nonneg (show (1 : ℝ) ≤ x by linarith); linarith
  -- `13 log z ≤ 26 log x` since `z ≤ x²`
  have hzx : z ≤ x ^ 2 := by
    have := Real.log_le_sub_one_of_pos hx0
    nlinarith
  have hlogz : Real.log z ≤ 2 * Real.log x := by
    have := Real.log_le_log (by linarith) hzx
    rwa [Real.log_pow] at this
  refine limModel_slot_succ h (hx.trans hz) ?_
  push_cast at hlogz
  linarith

end Slots

/-! ### On `Good(< t)` -/

section Good

variable (D : Sec5Family)

lemma mem_E0_of_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (i : ι0 D)
    (hi : t0 X₀ D i < t) : ω ∈ E0 θ X₀ D i := by
  unfold G0 paperGood at hω
  have h2 := hω.2
  simp only [goodBefore, mem_iInter] at h2
  exact h2 i hi

/-- The almost-sure conditions: jitters in `[0, 1]`, all stages good, no ties. -/
def NiceEv (θ : ℝ) (X₀ : ℕ) : Set JitterΩ :=
  {ω | (∀ j, ω j ∈ Icc (0 : ℝ) 1) ∧ ω ∈ SG (θ := θ) (X₀ := X₀) ∧ ω ∉ tiesEvent θ X₀}

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc in
lemma Mcl_eq_lim {ω : JitterΩ} (h0 : Std θ X₀ ω) : Mcl θ X₀ ω = h0.limModel := by
  unfold Mcl; rw [Ucl_eq h0.hU]; exact constructedModel_eq h0

include hc in
/-- **The queue bound at the slot of `x`** on `Good(< t)`, for `x + 26 log x + 2 < t`. -/
theorem queue_of_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (h0 : Std θ X₀ ω) {x : ℝ}
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
  have hq := hω.1 j htq
  simp only [okQ, mem_setOf_eq] at hq
  rw [show CM θ X₀ ω = h0.limModel from hM] at hq
  exact hq

include hc hev in
/-- **The cluster event at the height `v`** on `Good(< t)` (Proposition 6.11 through the
window model), given a scale `m` with `t(tB m) < t` and `8/7 (2 · 4v/log¹¹ v + 1) ≤ 2^m X₀/2`,
and `⌈v⌉ < t`. -/
theorem cluster_of_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (h0 : Std θ X₀ ω)
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
    mem_E0_of_G0 D hω (Sum.inr (Sum.inr (Sum.inr (Sum.inl m)))) hmt
  have hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1)) :=
    tBound_mono hm hTBm
  have hcl : ∀ n, zH X₀ n ≤ 4 * v / Real.log v ^ 11 → ω ∈ EclW hc hev n := by
    intro n hn
    have ht1 : tE1 X₀ n < t := by
      have := cluster_time_le hc.hX hv hn
      unfold tE1
      exact lt_of_le_of_lt (Nat.ceil_mono this) hvt
    have := mem_E0_of_G0 D hω (Sum.inl n) ht1
    simpa [E0, E1ev, dif_pos (And.intro hc hev)] using this
  have := clusterUpTo_of_eclW hc hev h0.hU hSG hZv hTB hcl
  rwa [constructedModel_eq h0] at this

include hc hev in
/-- **Lemma 6.26 on `Good(< t(tB n))`** (`n ≥ 2`) at every height `u < x ≤ 2^n X₀/2`: the
horizon-local induction `lemma626_horizon`, with the queue bound up to `max(X₀, x/2)` and the
cluster events, all of time `< t(tB n)`. -/
theorem lemma626_G0 {n : ℕ} (hn : 2 ≤ n) {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D (ttB X₀ n))
    (hN : ω ∈ NiceEv θ X₀) {x : ℝ} (hxW : x ≤ 2 ^ n * (X₀ : ℝ) / 2) {u : ℝ}
    (hu : (X₀ : ℝ) ≤ u) (hux : u < x) :
    (localCountA (absSet X₀ (DF θ X₀ ω)) u (u + u ^ (θ / 2)) : ℝ) ≤
      u ^ (θ / 2) * Real.log u ^ (-4 : ℤ) := by
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
    fun v hv hvW => cluster_of_G0 D hc hev hω h0 hSG hv (hceil v hvW) (hscale v hv hvW) httB
  -- the horizon `Z = max(X₀, x/2)`
  set Z := max (X₀ : ℝ) (x / 2) with hZ
  have hZX : (X₀ : ℝ) ≤ Z := le_max_left _ _
  have hZW : Z ≤ W / 2 := max_le (by linarith) (by linarith)
  have hQ : ∀ y, (X₀ : ℝ) ≤ y → y ≤ Z →
      (M.queue (M.slotIdx y) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx y)) := by
    intro y hy hyZ
    refine queue_of_G0 D hc hω h0 hy ?_
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
theorem tB_of_G0 (n : ℕ) {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D (ttB X₀ n))
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
  · exact T_le_three_of_loc hc hx fun u hu hux => lemma626_G0 D hc hev hn hω hN hxW hu hux

include hc hev in
lemma niceEv_compl_null : jitterMeasure (NiceEv θ X₀)ᶜ = 0 := by
  have h1 := ae_jitter_mem
  have h2 := ae_stageGood hc
  have h3 : jitterMeasure (tiesEvent θ X₀) = 0 := by
    have hX := hc.hX
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      have hX1 := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
    exact tiesNull θ hc.hθ X₀ hev h1
  have h3' : ∀ᵐ ω ∂jitterMeasure, ω ∉ tiesEvent θ X₀ := by
    rw [ae_iff]; simpa using h3
  have : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    filter_upwards [h1, h2, h3'] with ω hU hG ht
    exact ⟨hU, by simpa [SG] using hG, ht⟩
  rwa [ae_iff] at this

include hc hev in
/-- **The field `tbound` of `Queue6.QueueInputs`**, with no named hypothesis. -/
theorem tbound_G0 (n : ℕ) :
    jitterMeasure ((tB (θ := θ) (X₀ := X₀) n)ᶜ ∩ G0 θ X₀ D (ttB X₀ n)) = 0 := by
  refine measure_mono_null (fun ω hω => ?_) (niceEv_compl_null hc hev)
  intro hN
  exact hω.1 (tB_of_G0 D hc hev n hω.2 hN)

end Good

end BModel
