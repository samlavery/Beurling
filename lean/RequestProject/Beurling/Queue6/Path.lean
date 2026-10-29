module

public import RequestProject.Beurling.Queue6.Family
public import RequestProject.Beurling.Queue6.Dyadic

/-!
# Theorem 6.6(ii) on the good event: the window data of the constructed model

At a slot `j ≥ 1` with `s_j ∈ [u, 2u)`, `u = 2^m X₀`, and a slot window `W = (i, j]` with
`ℓ_jit(W) ≤ K₀`, the integer hull `I = [⌊s_{i+1}⌋, ⌈s_{j+1}⌉)` is a window of `𝓘_u`
(`Queue6.adm_hull`). On the events `Fr(I)`, R1′ on `I` and the cluster event up to
`4u/(log u)^{11}`, the facts of the proof of Theorem 6.6(ii) hold for `W`
(`Queue6.windowFacts_at`):

* the excess identity with the sandwich (Lemma 3.9, `sandwich`);
* `C_jit(I) = S₁ + S₂` (`cjit_eq_sum`);
* truncation is inactive and `X⁽ⁿ⁾_q(I) ≤ 2M₁` (Corollary 6.12, `xcount_le`), with the
  threshold `q ≥ y(u/2)` (`latest_ge_absorbY`, `yq_le_absorbY`);
* `Fr(I)`(a) and R1′;
* the `a ≥ 2` part `S₂ ≤ λ · 2 a_max M₁ ≤ 8 M₁ L (L/Λ + 1)` (`Fr(I)`(b), `x2count_le`,
  `amax_le`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueBound QueueMono
  Greedy QueueDet SlotModel

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-- **The jittered primes are at least `X₀ - X₀^{1/8}/2 - 1/8`** (box-centred placement at slot
starts `s ≥ X₀`, and `s - H(s)/2` is quasi-monotone). -/
lemma jit_ge_X0m (hX : 10 ^ 8 ≤ Real.log X₀) {M : SlotModel X₀} {U : ℕ → ℝ}
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) {k : ℕ} (hs : (X₀ : ℝ) ≤ M.slot (k + 1)) :
    (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 8 : ℝ) / 2 - 1 / 8 ≤ primeValueOf M (capH X₀) U k := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hH : 0 ≤ capH X₀ (M.slot (k + 1)) := le_trans (Real.exp_pos _).le (le_max_left _ _)
  have h1 := (landing_mem_box (s := M.slot (k + 1)) hH (hU (k + 1))).1
  have h2 := floor_quasi_mono hX0 hX (le_refl (X₀ : ℝ)) hs
  have h3 := InitialRange.capH_le_rpow hX0 hX (le_refl (X₀ : ℝ))
  unfold primeValueOf
  nlinarith

variable (θ X₀) in
/-- The integer hull `[⌊s_{i+1}⌋, ⌈s_{j+1}⌉)` of the slot window `(i, j]`, as integers. -/
noncomputable def hullA (ω : JitterΩ) (i : ℕ) : ℤ := (⌊(CM θ X₀ ω).slot (i + 1)⌋₊ : ℤ)

variable (θ X₀) in
/-- The right end of the hull. -/
noncomputable def hullB (ω : JitterΩ) (j : ℕ) : ℤ := (⌈(CM θ X₀ ω).slot (j + 1)⌉₊ : ℤ)

section Window

variable {ω : JitterΩ} (F : ExcFacts θ (CM θ X₀ ω) (Ucl ω)) (hX : 10 ^ 8 ≤ Real.log X₀)
include F hX

omit F hX in
lemma hull_casts (i j : ℕ) : ((hullA θ X₀ ω i : ℤ) : ℝ) = (⌊(CM θ X₀ ω).slot (i + 1)⌋₊ : ℝ) ∧
    ((hullB θ X₀ ω j : ℤ) : ℝ) = (⌈(CM θ X₀ ω).slot (j + 1)⌉₊ : ℝ) := by
  unfold hullA hullB; push_cast; exact ⟨rfl, rfl⟩

/-- **The hull is a window of `𝓘_u`.** -/
theorem adm_hull {m : ℕ} {i j : ℕ} (hj : 1 ≤ j) (hij : i ≤ j)
    (hsj : uS X₀ m ≤ (CM θ X₀ ω).slot j ∧ (CM θ X₀ ω).slot j < 2 * uS X₀ m)
    (hK : ellW θ (CM θ X₀ ω) (Ucl ω) i j ≤ K0 X₀ (uS X₀ m)) :
    Adm X₀ m (hullA θ X₀ ω i) (hullB θ X₀ ω j) := by
  set M := CM θ X₀ ω
  obtain ⟨ha, hb⟩ := hull_casts (θ := θ) (X₀ := X₀) (ω := ω) i j
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  set u := uS X₀ m
  have hs1 := slot_gt F (Nat.le_add_left 1 i)
  have hss : M.slot (i + 1) ≤ M.slot (j + 1) := M.slot_mono (by omega)
  have hsj1 : M.slot j ≤ M.slot (j + 1) := M.slot_mono (by omega)
  have h3 := slot_succ_le F hj hu hsj.2
  have hlen := window_len F hij hK
  have hb1 : M.slot (j + 1) ≤ (⌈M.slot (j + 1)⌉₊ : ℝ) := Nat.le_ceil _
  have hb2 : (⌈M.slot (j + 1)⌉₊ : ℝ) < M.slot (j + 1) + 1 := Nat.ceil_lt_add_one (by linarith)
  have ha1 : (⌊M.slot (i + 1)⌋₊ : ℝ) ≤ M.slot (i + 1) := Nat.floor_le (by linarith)
  have ha2 : M.slot (i + 1) < (⌊M.slot (i + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : Real.log (M.slot (j + 1)) ≤ Real.log (3 * u) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (M.slot (j + 1)) := Real.log_nonneg (by linarith)
  refine ⟨by rw [hb]; linarith, by rw [hb]; linarith, ?_, ?_⟩
  · have : (⌊M.slot (i + 1)⌋₊ : ℝ) ≤ (⌈M.slot (j + 1)⌉₊ : ℝ) := by linarith
    have : ⌊M.slot (i + 1)⌋₊ ≤ ⌈M.slot (j + 1)⌉₊ := by exact_mod_cast this
    unfold hullA hullB; exact_mod_cast this
  · push_cast
    rw [ha, hb]
    unfold Wlen
    have hK' : ((ellW θ M (Ucl ω) i j : ℕ) : ℝ) ≤ K0 X₀ u := by exact_mod_cast hK
    have : 12.5 * ((K0 X₀ u : ℝ) + 1) * Real.log (M.slot (j + 1)) ≤
        13 * ((K0 X₀ u : ℝ) + 1) * Real.log (3 * u) := by
      have h0 : (0 : ℝ) ≤ (K0 X₀ u : ℝ) + 1 := by positivity
      have := mul_le_mul_of_nonneg_left hlog h0
      nlinarith
    have hlen' : M.slot (j + 1) - M.slot (i + 1) ≤
        12.5 * ((K0 X₀ u : ℝ) + 1) * Real.log (M.slot (j + 1)) := hlen
    linarith

/-- **The facts of the proof of Theorem 6.6(ii) for one slot window**, on `Fr(I)`, R1′ on `I`
and the cluster event. -/
theorem windowFacts_at (hok : RealisedOK (CM θ X₀ ω) (capH X₀) (Ucl ω)) {m : ℕ} {i j : ℕ}
    (hj : 1 ≤ j) (hij : i ≤ j)
    (hsj : uS X₀ m ≤ (CM θ X₀ ω).slot j ∧ (CM θ X₀ ω).slot j < 2 * uS X₀ m)
    (hK : ellW θ (CM θ X₀ ω) (Ucl ω) i j ≤ K0 X₀ (uS X₀ m))
    (hFr : ω ∈ FrE θ X₀ m (hullA θ X₀ ω i) (hullB θ X₀ ω j))
    (hR : R1cond θ X₀ m (hullA θ X₀ ω i) (hullB θ X₀ ω j) ω)
    (hcl : ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (Mq X₀ (uS X₀ m))) :
    WindowFacts (CM θ X₀ ω).arr j i (Mq X₀ (uS X₀ m)) (Lq (uS X₀ m)) (Real.log X₀)
      (ellW θ (CM θ X₀ ω) (Ucl ω) i j) := by
  classical
  have hU : ∀ k, Ucl ω k ∈ Icc (0 : ℝ) 1 := fun k => clamp01_mem _
  set M := CM θ X₀ ω
  set u := uS X₀ m
  set a := hullA θ X₀ ω i
  set b := hullB θ X₀ ω j
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  have hadm := adm_hull F hX hj hij hsj hK
  obtain ⟨hub, hb3, hab, hlenW⟩ := hadm
  obtain ⟨ha, hb⟩ := hull_casts (θ := θ) (X₀ := X₀) (ω := ω) i j
  have hfr : ω ∈ FrAll jitterFiltration jitterMeasure (Xt θ X₀ m a b) (Ind2 θ X₀ a b)
      (ellIo θ X₀ a b) (Mq X₀ u) (4 * Lq u) (K0 X₀ u + 5) := by
    have := hFr; unfold FrE at this; rwa [if_pos ⟨hub, hb3, hab, hlenW⟩] at this
  obtain ⟨hFra, hFrb⟩ := hfr
  -- the sandwich
  obtain ⟨hI1, hI2, hexc⟩ := sandwich F hij
  -- the slot facts
  have hslot : ∀ l, 1 ≤ l → (X₀ : ℝ) ≤ M.slot l := fun l hl => (slot_gt F hl).le
  have hs1 := slot_gt F (Nat.le_add_left 1 i)
  -- the cofactor windows
  have hlen0 : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : a ≤ b := hab; have : (a : ℝ) ≤ b := by exact_mod_cast this
    linarith
  have hlen : (b : ℝ) - a ≤ Wlen X₀ u := by push_cast at hlenW; exact hlenW
  obtain ⟨hc1, hc2, hc3⟩ := cofactor_facts hX0 hX hu hlen0 hlen hub hb3
  -- every composite of `I` lies above `max(X₀, u/2)`
  have hWq := Wlen_le_quarter hX0 hX hu
  have haq : uq X₀ u ≤ (a : ℝ) := by
    apply max_le
    · rw [ha]
      have : X₀ ≤ ⌊M.slot (i + 1)⌋₊ := Nat.le_floor hs1.le
      exact_mod_cast this
    · linarith
  -- the threshold
  have hy : ∀ e ∈ cjitSet M (Ucl ω) a b, yq X₀ u ≤ primeValueOf M (capH X₀) (Ucl ω) (latk M e) := by
    intro e he
    have hval : (a : ℝ) ≤ idxVal M (capH X₀) (Ucl ω) e := he.1.2.1
    have hX0e : (X₀ : ℝ) ≤ idxVal M (capH X₀) (Ucl ω) e :=
      (le_max_left _ _).trans (haq.trans hval)
    exact (yq_le_absorbY hX m (haq.trans hval)).trans
      (latest_ge_absorbY (by linarith) he.2.1 hX0e he.2.2)
  have hMq := Mq_ge_one hX0 hX hu
  have hXc : ∀ k n, Xcount M (Ucl ω) a b k n ≤ 2 * Mq X₀ u := fun k n =>
    xcount_le hok hX hU hslot (yq_ge_one (u := u) hX0 hX) hy hc1 hc2 hc3 hcl (by linarith) k n
  -- truncation is inactive
  have hXt : ∀ k, Xt θ X₀ m a b k ω = Xcount M (Ucl ω) a b k 1 := fun k => by
    unfold Xt; exact min_eq_left (hXc k 1)
  -- `a_max`
  set A := ⌊Lq u / Real.log X₀ + 1⌋₊
  have hA : ∀ k, ∀ e ∈ x2set M (Ucl ω) a b k, mult M e k ≤ A := by
    intro k e he
    have hr := he.1.2.1
    obtain ⟨hk, -⟩ := latk_mem (M := M) hr
    rw [he.2.1] at hk
    have hxe : e ∈ xset M (Ucl ω) a b k (mult M e k) := ⟨he.1, he.2.1, rfl⟩
    have hpow := pow_lt_of_xset hok hxe hk
    have hq1 : yq X₀ u ≤ primeValueOf M (capH X₀) (Ucl ω) k := by
      have := hy e he.1; rwa [he.2.1] at this
    have hq2 := jit_ge_X0m hX hU (M := M) (hslot (k + 1) (by omega))
    have hn := amax_le hX0 hX hu hq1 hq2 (lt_of_lt_of_le hpow hb3)
    exact Nat.le_floor hn
  have hAr : (A : ℝ) ≤ Lq u / Real.log X₀ + 1 :=
    Nat.floor_le (by have := Lq_big hX0 hX hu; positivity)
  have hX2 : ∀ k, X2count M (Ucl ω) a b k ≤ 2 * A * Mq X₀ u := fun k =>
    x2count_le hok (by linarith) (hA k) (fun n => hXc k n)
  -- the decomposition, with `N` large
  obtain ⟨N₀, hN₀⟩ := cjit_eq_sum F a b
  set N := N₀
  have hC := hN₀ N le_rfl
  set S1 := ∑ k ∈ Finset.range N, Xcount M (Ucl ω) a b k 1
  set S2 := ∑ k ∈ Finset.range N, X2count M (Ucl ω) a b k
  set Comp := ∑ k ∈ Finset.range N,
    (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
  have hCS : Cjit M (Ucl ω) a b = S1 + S2 := by rw [hC, Finset.sum_add_distrib]
  -- `S₂ ≤ λ · 2 A M₁`
  have hS2 : S2 ≤ 8 * Mq X₀ u * Lq u * (Lq u / Real.log X₀ + 1) := by
    have hpt : ∀ k, X2count M (Ucl ω) a b k ≤ Ind2 θ X₀ a b k ω * (2 * A * Mq X₀ u) := by
      intro k
      unfold Ind2
      split_ifs with h1
      · simpa using hX2 k
      · push_neg at h1
        have h0 : X2count M (Ucl ω) a b k = 0 := by
          unfold X2count at h1 ⊢
          have : (x2set M (Ucl ω) a b k).ncard < 1 := by exact_mod_cast h1
          have : (x2set M (Ucl ω) a b k).ncard = 0 := by omega
          rw [this]; simp
        rw [h0]; simp
    have hsum : S2 ≤ (∑ k ∈ Finset.range N, Ind2 θ X₀ a b k ω) * (2 * A * Mq X₀ u) := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun k _ => hpt k
    have hlam := hFrb N
    have hA0 : 0 ≤ 2 * (A : ℝ) * Mq X₀ u := by positivity
    have hL := Lq_big hX0 hX hu
    calc S2 ≤ (∑ k ∈ Finset.range N, Ind2 θ X₀ a b k ω) * (2 * A * Mq X₀ u) := hsum
      _ ≤ (4 * Lq u) * (2 * A * Mq X₀ u) := mul_le_mul_of_nonneg_right hlam hA0
      _ ≤ (4 * Lq u) * (2 * (Lq u / Real.log X₀ + 1) * Mq X₀ u) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have := mul_le_mul_of_nonneg_right hAr (by linarith : (0 : ℝ) ≤ 2 * Mq X₀ u)
          nlinarith
      _ = 8 * Mq X₀ u * Lq u * (Lq u / Real.log X₀ + 1) := by ring
  refine ⟨ellIo θ X₀ a b ω, Cjit M (Ucl ω) a b, S1, S2, Comp, ?_, hCS, ?_, ?_, ?_, ?_, hS2⟩
  · -- the excess identity
    have : (ellIo θ X₀ a b ω : ℝ) = ellI θ M (Ucl ω) (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) := by
      unfold ellIo; rw [ha, hb]
    have hC' : Cjit M (Ucl ω) a b = Cjit M (Ucl ω) (⌊M.slot (i + 1)⌋₊) (⌈M.slot (j + 1)⌉₊) := by
      rw [ha, hb]
    rw [this, hC']; exact hexc
  · unfold ellIo; rw [ha, hb]; exact hI1
  · unfold ellIo; rw [ha, hb]; exact hI2
  · intro hle
    have h := hFra hle N
    have : S1 - Comp = ∑ k ∈ Finset.range N, (Xt θ X₀ m a b k ω -
        (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω) := by
      rw [Finset.sum_sub_distrib]; simp only [S1, Comp, hXt]
    rw [this]; exact h.le
  · exact hR N

end Window

/-- `ℓ_jit((i, j])` decreases by steps of `0` or `1`. -/
lemma ellW_step {M : SlotModel X₀} {U : ℕ → ℝ} {i j : ℕ} (hij : i < j) :
    ellW θ M U (i + 1) j ≤ ellW θ M U i j ∧ ellW θ M U i j ≤ ellW θ M U (i + 1) j + 1 := by
  classical
  unfold ellW
  have e : Finset.Ioc i j = insert (i + 1) (Finset.Ioc (i + 1) j) := by
    ext l; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  rw [e, Finset.filter_insert]
  have hn : i + 1 ∉ Finset.Ioc (i + 1) j := by simp
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => hn (Finset.mem_filter.mp hm).1)]
    omega
  · omega

lemma ellW_self {M : SlotModel X₀} {U : ℕ → ℝ} (j : ℕ) : ellW θ M U j j = 0 := by
  classical
  unfold ellW; simp

/-- **The inputs of Theorem 6.6(ii) at slot `j`** on the events. -/
theorem slotInputs_at {ω : JitterΩ} (F : ExcFacts θ (CM θ X₀ ω) (Ucl ω)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hok : RealisedOK (CM θ X₀ ω) (capH X₀) (Ucl ω)) (j : ℕ)
    (hev : ∀ m, 1 ≤ j → uS X₀ m ≤ (CM θ X₀ ω).slot j → (CM θ X₀ ω).slot j < 2 * uS X₀ m →
      (∀ i ≤ j, ellW θ (CM θ X₀ ω) (Ucl ω) i j ≤ K0 X₀ (uS X₀ m) →
        ω ∈ FrE θ X₀ m (hullA θ X₀ ω i) (hullB θ X₀ ω j) ∧
        R1cond θ X₀ m (hullA θ X₀ ω i) (hullB θ X₀ ω j) ω) ∧
      ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
        (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (Mq X₀ (uS X₀ m))) :
    SlotInputs (CM θ X₀ ω).arr (queueBScale X₀ ((CM θ X₀ ω).slot j)) j := by
  classical
  set M := CM θ X₀ ω
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hB0 : ∀ s : ℝ, queueB X₀ X₀ ≤ queueBScale X₀ s := by
    intro s
    have e : queueBScale X₀ s = queueBScale X₀ (max X₀ s) := by
      unfold queueBScale; rw [max_eq_right (le_max_left _ _)]
    rw [e]
    have := queueBScale_monotone hX0 hX (le_max_left (X₀ : ℝ) s)
    have e2 : queueBScale X₀ X₀ = queueB X₀ X₀ := by
      unfold queueBScale
      rw [max_self, InitialRange.dyadicScale_eq_self (by linarith) le_rfl (by linarith)]
    linarith
  have hQ : ∀ {u : ℝ}, (X₀ : ℝ) ≤ u →
      queueBound75 (Mq X₀ u) (Lq u) (Real.log X₀) 0.15 3 ≤ queueB X₀ u := by
    intro u hu
    unfold queueB
    exact queueBound75_mono (by linarith [Mq_ge_one hX0 hX hu]) (Mq_le hX0 hX hu)
      (by linarith [Lq_big hX0 hX hu]) le_rfl (by linarith)
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · -- the paper's slot `j₀ - 1`: only the empty window
    subst h0
    have hu := le_refl (X₀ : ℝ)
    refine ⟨Mq X₀ X₀, Lq X₀, Real.log X₀, fun i => ellW θ M (Ucl ω) i 0, Lq_big hX0 hX hu, hX,
      Lq_sq_le_Mq hX0 hX hu, (hQ hu).trans (hB0 _), ellW_self 0,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    have hM := Mq_ge_one hX0 hX hu
    have hL := Lq_big hX0 hX hu
    refine ⟨0, 0, 0, 0, 0, ?_, by ring, by simp, by simp [ellW_self], fun _ => ?_, ?_, ?_⟩
    · simp [exc]
    · simp only [sub_zero]; positivity
    · simp only [Nat.cast_zero, zero_mul, zero_add]; norm_num
    · have : (0 : ℝ) ≤ Lq X₀ / Real.log X₀ + 1 := by positivity
      positivity
  · have hsj := slot_gt F hj
    obtain ⟨m, hm⟩ := exists_uS (X₀ := X₀) (by linarith) hsj.le
    have hs0 : 0 < M.slot j := by linarith
    have hu1 : uS X₀ m ≤ M.slot j := by rw [← hm]; exact dyadicScale_le (by linarith) hs0
    have hu2 : M.slot j < 2 * uS X₀ m := by rw [← hm]; exact lt_two_mul_dyadicScale (by linarith)
    have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
    obtain ⟨hwin, hcl⟩ := hev m hj hu1 hu2
    have hB : queueBScale X₀ (M.slot j) = queueB X₀ (uS X₀ m) := by
      rw [queueBScale_eq hsj.le, hm]
    refine ⟨Mq X₀ (uS X₀ m), Lq (uS X₀ m), Real.log X₀, fun i => ellW θ M (Ucl ω) i j,
      Lq_big hX0 hX hu, hX, Lq_sq_le_Mq hX0 hX hu, by rw [hB]; exact hQ hu, ellW_self j,
      fun i hi => ellW_step hi, fun i hi hK => ?_⟩
    obtain ⟨hFr, hR⟩ := hwin i hi hK
    exact windowFacts_at F hX hok hj hi ⟨hu1, hu2⟩ hK hFr hR hcl

/-! ### On the good event -/

section Good

variable (D : Sec5Family)

lemma mem_EF {ω : JitterΩ} (hω : ω ∈ goodAll (EF θ X₀ D)) (i : ιF D) : ω ∈ EF θ X₀ D i := by
  simp only [goodAll, mem_iInter] at hω; exact hω i

/-- The events of Table 1 with time `≤ t` hold when the queue constraints with time `< t` do. -/
lemma base_holds {ω : JitterΩ} (hω : ω ∈ goodAll (EF θ X₀ D)) {t : ℕ}
    (hq : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) {i : ι0 D} (hi : t0 X₀ D i ≤ t) :
    ω ∈ E0 θ X₀ D i := by
  have h := mem_EF D hω (Sum.inl i)
  simp only [EF, Sum.elim_inl, withQC, mem_union, mem_compl_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd (QC_anti _ _ hi hq) h

lemma G0_holds {ω : JitterΩ} (hω : ω ∈ goodAll (EF θ X₀ D)) {t : ℕ}
    (hq : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) : ω ∈ G0 θ X₀ D t := by
  refine ⟨hq, ?_⟩
  simp only [goodBefore, mem_iInter]
  exact fun i hi => base_holds D hω hq hi.le

/-- The queue constraints of the earlier slots give the constraints with time `< ⌈s_{j+1}⌉`. -/
lemma qc_of_prev {ω : JitterΩ} {j : ℕ}
    (hprev : ∀ i < j, (greedyQueue (CM θ X₀ ω).arr i : ℝ) ≤
      queueBScale X₀ ((CM θ X₀ ω).slot i)) :
    ω ∈ QC (okQ θ X₀) (tq θ X₀) ⌈(CM θ X₀ ω).slot (j + 1)⌉₊ := by
  intro i hi
  have hij : i < j := by
    by_contra hc; push_neg at hc
    have := Nat.ceil_mono ((CM θ X₀ ω).slot_mono (by omega : j + 1 ≤ i + 1))
    unfold tq at hi; omega
  exact hprev i hij

/-- `2z + H(2z) ≤ u` for the cluster heights `z ≤ 4u/(log u)^{11}`. -/
lemma cluster_time_le (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu : (X₀ : ℝ) ≤ u) {n : ℕ}
    (hz : zH X₀ n ≤ 4 * u / Real.log u ^ 11) : 2 * zH X₀ n + capH X₀ (2 * zH X₀ n) ≤ u := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hz0 := zH_ge (X₀ := X₀) n
  have h2z : (X₀ : ℝ) ≤ 2 * zH X₀ n := by linarith
  have hH := InitialRange.capH_le_rpow hX0 hX h2z
  have hr : (2 * zH X₀ n) ^ (1 / 8 : ℝ) ≤ 2 * zH X₀ n := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 * zH X₀ n by linarith)
      (show (1 / 8 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hl := (logs_of_ge hX0 hX hu).1
  have hu0 : 0 < u := by linarith
  have h11 : 4 * u / Real.log u ^ 11 ≤ u / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (16 : ℝ) ≤ Real.log u ^ 11 := by
      have : (16 : ℝ) ≤ Real.log u := by linarith
      calc (16 : ℝ) ≤ Real.log u := this
        _ ≤ Real.log u ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith
  linarith

/-- **Theorem 6.6(ii) and the cluster bound on the good event.** -/
theorem goodAll_facts (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hev : Even X₀) (hHB : ShortIntervalPNTFrom X₀) {ω : JitterΩ}
    (hω : ω ∈ goodAll (EF θ X₀ D)) (hU : ∀ k, ω k ∈ Icc (0 : ℝ) 1) :
    (constructedModel θ X₀ ω).QueueWindowData ∧ ∀ v ≥ (X₀ : ℝ),
      ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀
        (4 * v / Real.log v ^ 11) (capM1 X₀ v) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hUe : Ucl ω = ω := Ucl_eq hU
  have h0 : Std θ X₀ ω := ⟨hθ, hX, hU, hHB⟩
  have h : Std θ X₀ (Ucl ω) := by rw [hUe]; exact h0
  have hCMe : CM θ X₀ ω = constructedModel θ X₀ ω := by
    show constructedModel θ X₀ (Ucl ω) = _; rw [hUe]
  have hCM : CM θ X₀ ω = h.limModel := constructedModel_eq h
  -- no ties
  have ht : TieFree (CM θ X₀ ω) (Ucl ω) := by
    have h1 := mem_EF D hω (Sum.inr (Sum.inr (Sum.inl ())))
    simp only [EF, Sum.elim_inr, Sum.elim_inl, mem_compl_iff, tiesEvent, mem_setOf_eq, not_and,
      not_not] at h1
    rw [hCMe, hUe]; exact h1 h0
  have F : ExcFacts θ (CM θ X₀ ω) (Ucl ω) := by
    rw [hCM]; rw [hCM] at ht; exact excFacts_of h hev ht
  have hok : RealisedOK (CM θ X₀ ω) (capH X₀) (Ucl ω) := by rw [hCM]; exact limModel_realisedOK h
  suffices hsuff : (CM θ X₀ ω).QueueWindowData ∧ ∀ v ≥ (X₀ : ℝ),
      ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀ (4 * v / Real.log v ^ 11)
        (capM1 X₀ v) by
    rw [hCMe, hUe] at hsuff; exact hsuff
  set M := CM θ X₀ ω
  set B : ℕ → ℝ := fun j => queueBScale X₀ (M.slot j)
  have hBm : Monotone B := (queueBScale_monotone hX0 hX).comp M.slot_mono
  -- the cluster bound from the events of time `≤ t`
  have hc : Cond θ X₀ := ⟨hθ, hX, hHB⟩
  have hSG : ω ∈ SG (θ := θ) (X₀ := X₀) := by
    have h1 := mem_EF D hω (Sum.inr (Sum.inr (Sum.inr ())))
    simpa [EF] using h1
  have hG' : ∀ m, ω ∈ stageGood θ X₀ m := by simpa [SG] using hSG
  have hcl_t : ∀ {Z w : ℝ}, Z ≤ w →
      (∀ n, zH X₀ n ≤ Z → ω ∈ QC (okQ θ X₀) (tq θ X₀) (tE1 X₀ n)) →
      ∀ m, 8 / 7 * (2 * Z + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2 →
      ω ∈ QC (okQ θ X₀) (tq θ X₀) (ttB X₀ m) →
      ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀ Z (capM1 X₀ w) := by
    intro Z w hZw hzt m hm htm
    have hTBm : ω ∈ tB (θ := θ) (X₀ := X₀) m :=
      base_holds (i := Sum.inr (Sum.inr (Sum.inr (Sum.inl m)))) D hω htm le_rfl
    have hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * Z + 1)) := tBound_mono hm hTBm
    have hcl : ∀ n, zH X₀ n ≤ Z → ω ∈ EclW hc hev n := fun n hn => by
      have := base_holds (i := Sum.inl n) D hω (hzt n hn) le_rfl
      simpa [E0, E1ev, dif_pos (And.intro hc hev)] using this
    have := clusterUpTo_of_eclW hc hev hU hSG hZw hTB hcl
    show ClusterUpTo (realisedSystem (constructedModel θ X₀ (Ucl ω)) (capH X₀) (Ucl ω)) X₀ Z
      (capM1 X₀ w)
    rw [hUe]; exact this
  have key := queue_and_data (A := M.arr) (B := B) hBm fun j hprev => by
    have hq := qc_of_prev (θ := θ) (X₀ := X₀) (ω := ω) hprev
    refine slotInputs_at F hX hok j fun m hj hu1 hu2 => ⟨fun i hi hK => ?_, ?_⟩
    · have hadm := adm_hull F hX hj hi ⟨hu1, hu2⟩ hK
      have hb : tE2 (hullB θ X₀ ω j) = ⌈M.slot (j + 1)⌉₊ := by
        unfold tE2 hullB; simp; rfl
      refine ⟨?_, ?_⟩
      · have := base_holds (i := Sum.inr (Sum.inl (m, hullA θ X₀ ω i, hullB θ X₀ ω j))) D hω hq
          (by simp only [t0, Sum.elim_inr, Sum.elim_inl]; rw [hb])
        simpa [E0] using this
      · have hN := mem_EF D hω (Sum.inr (Sum.inl (m, hullA θ X₀ ω i, hullB θ X₀ ω j)))
        simp only [EF, Sum.elim_inr, Sum.elim_inl, Nev, mem_setOf_eq] at hN
        exact hN hadm (by rw [hb]; exact G0_holds D hω hq)
    · have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
      have hl := (logs_of_ge hX0 hX hu).1
      have hu0 : 0 < uS X₀ m := by linarith
      have h11 : 4 * uS X₀ m / Real.log (uS X₀ m) ^ 11 ≤ uS X₀ m / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (64 : ℝ) ≤ Real.log (uS X₀ m) ^ 11 := by
          calc (64 : ℝ) ≤ Real.log (uS X₀ m) := by linarith
            _ ≤ Real.log (uS X₀ m) ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
        nlinarith
      have hs2 : M.slot j ≤ M.slot (j + 1) := M.slot_mono (by omega)
      have h16 := X₀_ge_two_pow hX
      have hZu : 8 / 7 * (2 * (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) + 1) ≤
          2 ^ m * (X₀ : ℝ) / 2 := by
        have : 2 ^ m * (X₀ : ℝ) = uS X₀ m := rfl
        rw [this]; linarith
      refine hcl_t (w := uq X₀ (uS X₀ m)) (h11.trans (by
        have := le_max_right (X₀ : ℝ) (uS X₀ m / 2); unfold uq; linarith)) (fun n hn => ?_) m
        hZu ?_
      · refine QC_anti _ _ ?_ hq
        unfold tE1
        apply Nat.ceil_mono
        have := cluster_time_le hX hu (hn.trans le_rfl)
        linarith
      · refine QC_anti _ _ ?_ hq
        unfold ttB
        have h1 : 2 ^ m * (X₀ : ℝ) / 2 + 1 ≤ M.slot (j + 1) := by
          have : 2 ^ m * (X₀ : ℝ) = uS X₀ m := rfl
          linarith
        have := Nat.ceil_mono h1
        rw [Nat.ceil_add_one (by positivity)] at this
        exact this
  -- all queue constraints hold
  have hQall : ∀ t, ω ∈ QC (okQ θ X₀) (tq θ X₀) t := fun t i _ => (key i).2
  refine ⟨fun k => (key k).1, fun v hv => ?_⟩
  have hl := (logs_of_ge hX0 hX hv).1
  have hv0 : 0 < v := by linarith
  have hZv : 4 * v / Real.log v ^ 11 ≤ v := by
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ≤ Real.log v ^ 11 := by
      calc (4 : ℝ) ≤ Real.log v := by linarith
        _ ≤ Real.log v ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith
  -- a scale `m` with `8/7 (2Z + 1) ≤ 2^m X₀ / 2`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) /
    ((X₀ : ℝ) / 2)) (by norm_num : (1 : ℝ) < 2)
  have hX0' : (0 : ℝ) < (X₀ : ℝ) / 2 := by linarith
  rw [div_lt_iff₀ hX0'] at hm
  exact hcl_t hZv (fun n _ => hQall _) m (by nlinarith) (hQall _)

end Good

end Queue6

end
