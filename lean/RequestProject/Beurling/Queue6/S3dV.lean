module

public import RequestProject.Beurling.Model.TBoundGood
public import RequestProject.Beurling.Queue6.MertensLoc
public import RequestProject.Beurling.Queue6.TruncLaw

/-!
# Lemma A.6 (S3)(d) on `Good(< t(E1(z)))`, with the position cut-off ((F3′), second case)

At the height `z = z_n` the cluster event `E1(z)` has time `t = ⌈2z + H(2z)⌉`. On
`Good(< t)` (`Queue6.G0`) off the null set `NiceEvᶜ`:

* `mertens_G0` : the realised system satisfies Lemma 5.1(iv) up to `Z = 2z + 2`: (HBS) up to
  `Z` (`hbs_local`, Remark *horizon*) reads the queue bound and the cluster events only at
  heights `≤ Z`, which are among the constraints of time `< t`;
* `card_slot_le` : the slot count (F1): at most `θ · H_max` decisions have their box over a
  given point;
* `s3dV_sure` : **(S3)(d) for the position-cut law** (`truncLaw`, decisions with
  `c_n - H_n/2 ≤ 2z + 1`): `tailSum · ∏ (1 - 1/q_n)⁻¹ ≤ A_top(z) =
  1.8 log(2z + 2) · exp(2.21/Λ + 10⁻⁶)`. The three groups of (F3′): the rational primes and the
  realised primes up to `2z + 2` (`euler_top_le_loc`, Lemma 5.1(iv) up to `2z + 2`), and the
  decided primes above `2z + 2`, all of whose boxes contain the point `2z + 2`, bounded by the
  slot count (F1) rather than by (HBS): a factor `≤ e^{10⁻⁶}`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed SlotModel BModel
  RankFull RankFull.Config Finset
open scoped ENNReal

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-- **`A_top(z) = 1.8 log(2z + 2) · exp(2.21/Λ + 10⁻⁶)`** (Lemma A.6 (S3)(d) with the constant
`1.8` of the Mertens product estimate). -/
noncomputable def AtopV (X₀ : ℕ) (z : ℝ) : ℝ :=
  1.8 * Real.log (2 * z + 2) * Real.exp (2.21 / Real.log X₀ + 1e-6)

/-- The cut-off point `b(z) = 2z + 1` (every pivot value is at most `2z + 1`). -/
noncomputable def bCut (z : ℝ) : ℝ := 2 * z + 1

section Good

variable (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)

include hc in
lemma zH_ge_half (n : ℕ) : (X₀ : ℝ) / 2 ≤ zH X₀ n := by
  unfold zH
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  nlinarith

include hc in
lemma X0_ge_1e8 : (10 : ℝ) ^ 8 ≤ X₀ := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
  have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
  linarith

include hc hev in
/-- **Lemma 5.1(iv) up to `2z + 2` on `Good(< t(E1(z)))`**, off the null set `NiceEvᶜ`. -/
theorem mertens_G0 {n : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D (tE1 X₀ n))
    (hN : ω ∈ NiceEv θ X₀) :
    MertensUpTo (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)) (2 * zH X₀ n + 2) := by
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXb := X0_ge_1e8 hc
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  set z := zH X₀ n with hzdef
  have hz := zH_ge_half hc n
  set Z := 2 * z + 2 with hZdef
  have hZX : (X₀ : ℝ) ≤ Z := by linarith
  -- the time `t = ⌈2z + H(2z)⌉`
  have h2z : (X₀ : ℝ) ≤ 2 * z := by linarith
  have hH := log_le_capH hX0 hX h2z
  have hl2z := (logs_of_ge hX0 hX h2z).1
  have ht1 : 2 * z + capH X₀ (2 * z) ≤ (tE1 X₀ n : ℝ) := by
    unfold tE1; rw [← hzdef]; exact Nat.le_ceil _
  have hlogZ : Real.log Z ≤ Real.log (2 * z) + 1 := by
    have h1 : Real.log Z ≤ Real.log (2 * (2 * z)) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith [Real.log_two_lt_d9]
  have hQ : ∀ y, (X₀ : ℝ) ≤ y → y ≤ Z →
      (M.queue (M.slotIdx y) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx y)) := by
    intro y hy hyZ
    refine queue_of_G0 D hc hω h0 hy ?_
    have hly : Real.log y ≤ Real.log Z := Real.log_le_log (by linarith) hyZ
    linarith
  have hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v) := by
    intro v hv hvZ
    have hvt : ⌈v⌉₊ < tE1 X₀ n := by
      have h1 : (⌈v⌉₊ : ℝ) < v + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : (⌈v⌉₊ : ℝ) < tE1 X₀ n := by linarith
      exact_mod_cast h2
    have hm : 8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ 2 ^ n * (X₀ : ℝ) / 2 := by
      have e : 2 ^ n * (X₀ : ℝ) / 2 = z := by rw [hzdef]; unfold zH; ring
      rw [e]
      obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hX hv
      have hv0 : 0 < v := by linarith
      have h11 : (100 : ℝ) ≤ Real.log v ^ 11 := by
        have : (10 ^ 8 : ℝ) ≤ Real.log v ^ 11 :=
          hl.trans (le_self_pow₀ (by linarith) (by norm_num))
        linarith
      have : 4 * v / Real.log v ^ 11 ≤ v / 25 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
      nlinarith
    have hmt : ttB X₀ n < tE1 X₀ n := by
      have e : 2 ^ n * (X₀ : ℝ) / 2 = z := by rw [hzdef]; unfold zH; ring
      have h1 : ((ttB X₀ n : ℕ) : ℝ) < z + 2 := by
        unfold ttB; rw [e]; push_cast
        linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ z by linarith)]
      have h2 : ((ttB X₀ n : ℕ) : ℝ) < tE1 X₀ n := by linarith
      exact_mod_cast h2
    exact cluster_of_G0 D hc hev hω h0 hSG hv hvt hm hmt
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have hmain := hbs_local hc.hθ hX M ω hU (limModel_placed_infinite h0)
    (constructionScale X₀) hT Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hZX hQ hcl
  -- (HBS) up to `Z`
  set P := realisedSystem M (capH X₀) ω with hP
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := h0.limModel_low
  set X0m : ℝ := (X₀ : ℝ) - capH X₀ X₀ / 2 with hX0mdef
  have h4H := four_capH_le hX0 hX (le_refl (X₀ : ℝ))
  have hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊ :=
    fun w hw1 hw2 => realised_floor_eq hok hU hX hTlow hw1 hw2
  have hHBS : P.HBS X0m Z (1 / 1000) (1 / 1000) (hbsEps X₀) :=
    { X0m_ge := by
        have : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) / 2 := by linarith
        linarith
      eta1_nonneg := by norm_num
      eta1_le := le_rfl
      eta2_nonneg := by norm_num
      eta2_le := le_rfl
      floor_eq := fun v h1 h2 _ => hfl v h1 h2
      err := fun v h1 h2 => hmain v h1 h2
      eta2 := fun v h1 _ => hbsEps_mul_log_le hX (by linarith)
      eta1 := fun x K w hw => hbsEps_dyadic_sum_le hX K w (fun k hk =>
        ⟨(hw k hk).1, (hw k hk).2.1, by linarith [(hw k hk).2.2.1]⟩) }
  have hMP : MertensUpTo P Z := by
    intro y x hy hyx hxZ
    have := P.lemma_5_1 hHBS (x := x) (by linarith) hxZ
    have h2 := (abs_le.mp (this.2.2.2 y hy hyx)).2
    linarith
  have e : realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω) = P := by
    rw [hP, Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [e]
  exact hMP

end Good

/-- **The slot count (F1)**: the decisions in `F` whose boxes contain a common point `t`, with
widths `≤ H_m`, number at most `θ H_m`. -/
theorem card_slot_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θ : ℝ} (hθ : 0 ≤ θ)
    (J : JitterLaw Ω P (ENNReal.ofReal θ)) {N : ℕ} (ω : Ω) (F : Finset (Fin N)) (t : ℝ)
    {Hm : ℝ} (hHm : 0 < Hm) (hA : ∀ k ∈ F, ω ∈ J.A k)
    (hbox : ∀ k ∈ F, t ∈ box (J.c k ω) (J.H k ω)) (hH : ∀ k ∈ F, J.H k ω ≤ Hm) :
    (F.card : ℝ) ≤ θ * Hm := by
  classical
  set f : ℕ → ℝ≥0∞ := fun n => (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
    (box (J.c n ω) (J.H n ω)).indicator 1 t) ω with hf
  have hsum : ∑ n ∈ F.map Fin.valEmbedding, f n ≤ ENNReal.ofReal θ :=
    (ENNReal.sum_le_tsum _).trans (J.slots ω t)
  have hterm : ∀ k ∈ F, ENNReal.ofReal Hm⁻¹ ≤ f k := by
    intro k hk
    simp only [hf, Set.indicator_of_mem (hA k hk), Set.indicator_of_mem (hbox k hk),
      Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ (J.H_pos k ω) (hH k hk))
  have h1 : ∑ k ∈ F, ENNReal.ofReal Hm⁻¹ ≤ ENNReal.ofReal θ := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_map] at hsum
    exact hsum
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hθ).mp h1
  rw [← div_eq_mul_inv, div_le_iff₀ hHm] at h2
  exact h2

section Sure

variable (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)

include hc in
/-- The slot of a decision with `c - H(c)/2 ≤ 2z + 1` is at most `3z`, and `H(c) ≤ (3z)^{1/8}`. -/
lemma HF_le_of_cut {z : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z) (k : ℕ) (ω : JitterΩ)
    (hcut : slotF θ X₀ k ω - HF θ X₀ k ω / 2 ≤ 2 * z + 1) :
    HF θ X₀ k ω ≤ (3 * z) ^ (1 / 8 : ℝ) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := X0_ge_1e8 hc
  set c := slotF θ X₀ k ω
  have hcX : (X₀ : ℝ) ≤ c := slotF_ge hc k ω
  have hHc : HF θ X₀ k ω ≤ c ^ (1 / 8 : ℝ) := InitialRange.capH_le_rpow hX0 hc.hX hcX
  have hc1 : 1 ≤ c := by linarith
  -- `c^{1/8} ≤ c/2`
  have h18 : c ^ (1 / 8 : ℝ) ≤ c / 2 := by
    have hsq : c ^ (1 / 8 : ℝ) * c ^ (7 / 8 : ℝ) = c := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h78 : (2 : ℝ) ≤ c ^ (7 / 8 : ℝ) := by
      have : (2 : ℝ) ^ (8 / 7 : ℝ) ≤ c := by
        have h4 : (2 : ℝ) ^ (8 / 7 : ℝ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        norm_num at h4; linarith
      have := Real.rpow_le_rpow (by positivity) this (show (0 : ℝ) ≤ 7 / 8 by norm_num)
      rw [← Real.rpow_mul (by norm_num)] at this
      norm_num at this; exact this
    have hp : 0 ≤ c ^ (1 / 8 : ℝ) := by positivity
    nlinarith
  have hc3 : c ≤ 3 * z := by linarith
  exact hHc.trans (Real.rpow_le_rpow (by linarith) hc3 (by norm_num))

include hc in
/-- `(1 + 1/Λ) (3z)^{1/8} · 2/(2z + 2) ≤ 10⁻⁶`. -/
lemma top_small {z : ℝ} (hz : (X₀ : ℝ) / 2 ≤ z) :
    (1 + 1 / Real.log X₀) * (3 * z) ^ (1 / 8 : ℝ) * (2 / (2 * z + 2)) ≤ 1e-6 := by
  have hXb := X0_ge_1e8 hc
  have hX := hc.hX
  have hz0 : 0 < z := by linarith
  have h3z : (10 : ℝ) ^ 8 ≤ 3 * z := by linarith
  -- `(3z)^{1/8} ≤ 3z · 10⁻⁷`
  have h18 : (3 * z) ^ (1 / 8 : ℝ) ≤ 3 * z / 10 ^ 7 := by
    have hsq : (3 * z) ^ (1 / 8 : ℝ) * (3 * z) ^ (7 / 8 : ℝ) = 3 * z := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h78 : (10 : ℝ) ^ 7 ≤ (3 * z) ^ (7 / 8 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) h3z (show (0 : ℝ) ≤ 7 / 8 by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at this
      norm_num at this ⊢; linarith
    have hp : 0 ≤ (3 * z) ^ (1 / 8 : ℝ) := by positivity
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hΛ : 1 / Real.log X₀ ≤ 1e-8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : 2 / (2 * z + 2) ≤ 1 / z := by
    rw [div_le_div_iff₀ (by linarith) hz0]; linarith
  have hp : 0 ≤ (3 * z) ^ (1 / 8 : ℝ) := by positivity
  calc (1 + 1 / Real.log X₀) * (3 * z) ^ (1 / 8 : ℝ) * (2 / (2 * z + 2))
      ≤ 2 * (3 * z / 10 ^ 7) * (1 / z) := by
        gcongr
        · linarith
    _ = 6 / 10 ^ 7 := by field_simp; norm_num
    _ ≤ 1e-6 := by norm_num

include hc hev in
/-- **Lemma A.6 (S3)(d) for the position-cut law on `Good(< t(E1(z_n)))`** (the sure top bound
of (F3′)): for decisions `k ∈ F` of `truncLaw (constructionLaw2) (2z + 1)`, off `NiceEvᶜ`,
`tailSum · ∏_{k ∈ F} (1 - 1/q_k)⁻¹ ≤ A_top(z)`. -/
theorem s3dV_sure {n : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D (tE1 X₀ n))
    (hN : ω ∈ NiceEv θ X₀) {N : ℕ} (Dmax : ℕ) (F : Finset (Fin N))
    (hF : ∀ k ∈ F, ω ∈ (truncLaw (constructionLaw2 hc hev) (bCut (zH X₀ n))).A k) :
    tailSum Dmax X₀ * ∏ k ∈ F, (1 - ((constructionLaw2 hc hev).q k ω)⁻¹)⁻¹ ≤
      AtopV X₀ (zH X₀ n) := by
  classical
  set J := constructionLaw2 hc hev with hJ
  set z := zH X₀ n with hzdef
  have hz := zH_ge_half hc n
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := X0_ge_1e8 hc
  set Z := 2 * z + 2 with hZdef
  have hMZ := mertens_G0 D hc hev hω hN
  rw [← hzdef] at hMZ
  set M := Mcl θ X₀ ω with hM
  have hstd := hc.std ω
  have hok : RealisedOK M (capH X₀) (Ucl ω) := by
    rw [hM, Mcl_eq hc]; exact limModel_realisedOK hstd
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    rw [hM, Mcl_eq hc]; exact hstd.limModel_low
  have hU : ∀ j, Ucl ω j ∈ Set.Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  have hA : ∀ k ∈ F, ω ∈ J.A k := fun k hk => (hF k hk).1
  have hq1 : ∀ k ∈ F, 1 < J.q k ω := fun k hk => law2_hq hc hev ω k (hA k hk)
  -- the factors as exponentials
  have hfac : ∀ k ∈ F, (1 - (J.q k ω)⁻¹)⁻¹ = Real.exp (wE (J.q k ω)) :=
    fun k hk => (exp_wE (hq1 k hk)).symm
  rw [Finset.prod_congr rfl hfac, ← Real.exp_sum,
    ← Finset.sum_filter_add_sum_filter_not F (fun k : Fin N => J.q k ω ≤ Z), Real.exp_add]
  set F1 := F.filter (fun k : Fin N => J.q k ω ≤ Z) with hF1
  set F3 := F.filter (fun k : Fin N => ¬ J.q k ω ≤ Z) with hF3
  -- the first two groups: Lemma 5.1(iv) up to `Z`
  have hg1 : tailSum Dmax X₀ * Real.exp (∑ k ∈ F1, wE (J.q k ω)) ≤
      1.8 * Real.log Z * Real.exp (2.21 / Real.log X₀) := by
    set κ := F1.map Fin.valEmbedding with hκ
    have hκP : ∀ k ∈ κ, placedAt M k := by
      intro k hk
      rw [hκ, Finset.mem_map] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      exact (hA m (Finset.mem_filter.mp hm).1).1.1
    have hκV : ∀ k ∈ κ, primeValueOf M (capH X₀) (Ucl ω) k ≤ Z := by
      intro k hk
      rw [hκ, Finset.mem_map] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      exact (Finset.mem_filter.mp hm).2
    have h := euler_top_le_loc hok hU hX hTlow hMZ (V := Z) (by linarith) le_rfl κ hκP hκV
      Dmax
    have e : ∑ k ∈ κ, wE (primeValueOf M (capH X₀) (Ucl ω) k) = ∑ k ∈ F1, wE (J.q k ω) := by
      rw [hκ, Finset.sum_map]; rfl
    rw [e] at h
    exact h
  -- the third group: the slot count at the point `Z`
  have hg3 : ∑ k ∈ F3, wE (J.q k ω) ≤ 1e-6 := by
    have hHm : ∀ k ∈ F3, J.H k ω ≤ (3 * z) ^ (1 / 8 : ℝ) := by
      intro k hk
      have hcut := (hF k (Finset.mem_filter.mp hk).1).2
      exact HF_le_of_cut hc hz k ω hcut
    have hbox : ∀ k ∈ F3, Z ∈ box (J.c k ω) (J.H k ω) := by
      intro k hk
      obtain ⟨hkF, hkZ⟩ := Finset.mem_filter.mp hk
      have hcut : J.c k ω - J.H k ω / 2 ≤ 2 * z + 1 := (hF k hkF).2
      have hup : J.q k ω ≤ J.c k ω + J.H k ω / 2 := by
        show valF θ X₀ k ω ≤ slotF θ X₀ k ω + HF θ X₀ k ω / 2
        rw [valF_eq]
        exact (landing_mem_box (HF_pos hc k ω).le (clamp01_mem _)).2
      simp only [RankFull.box, Set.mem_Ico]
      constructor <;> linarith
    have hHpos : 0 < (3 * z) ^ (1 / 8 : ℝ) := by
      apply Real.rpow_pos_of_pos; linarith
    have hcard := card_slot_le (θ := 1 + 1 / Real.log X₀) (by positivity) J ω F3 Z hHpos
      (fun k hk => hA k (Finset.mem_filter.mp hk).1) hbox hHm
    have hw : ∀ k ∈ F3, wE (J.q k ω) ≤ 2 / Z := by
      intro k hk
      have hkZ : Z < J.q k ω := lt_of_not_ge (Finset.mem_filter.mp hk).2
      have hq2 : 2 ≤ J.q k ω := by linarith
      have h1 := wE_le hq2
      have hq0 : 0 < J.q k ω := by linarith
      have h2 : (J.q k ω)⁻¹ + 2 * (J.q k ω)⁻¹ ^ 2 ≤ 2 * (J.q k ω)⁻¹ := by
        have hi : (J.q k ω)⁻¹ ≤ 1 / 2 := by
          rw [inv_le_comm₀ hq0 (by norm_num)]; linarith
        have hi0 : 0 < (J.q k ω)⁻¹ := inv_pos.mpr hq0
        nlinarith
      have h3 : 2 * (J.q k ω)⁻¹ ≤ 2 / Z := by
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hkZ.le
      linarith
    have hsum := Finset.sum_le_sum hw
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hsm := top_small hc hz
    have hZ0 : 0 ≤ 2 / Z := div_nonneg (by norm_num) (by linarith)
    calc ∑ k ∈ F3, wE (J.q k ω) ≤ (F3.card : ℝ) * (2 / Z) := hsum
      _ ≤ (1 + 1 / Real.log X₀) * (3 * z) ^ (1 / 8 : ℝ) * (2 / Z) :=
          mul_le_mul_of_nonneg_right hcard hZ0
      _ ≤ 1e-6 := hsm
  have hT0 : 0 ≤ tailSum Dmax X₀ := by
    unfold tailSum; exact Finset.sum_nonneg fun d _ => by positivity
  calc tailSum Dmax X₀ * (Real.exp (∑ k ∈ F1, wE (J.q k ω)) *
        Real.exp (∑ k ∈ F3, wE (J.q k ω)))
      = (tailSum Dmax X₀ * Real.exp (∑ k ∈ F1, wE (J.q k ω))) *
          Real.exp (∑ k ∈ F3, wE (J.q k ω)) := by ring
    _ ≤ (1.8 * Real.log Z * Real.exp (2.21 / Real.log X₀)) * Real.exp 1e-6 := by
        have hlZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
        exact mul_le_mul hg1 (Real.exp_le_exp.mpr hg3) (Real.exp_pos _).le (by positivity)
    _ = AtopV X₀ z := by
        unfold AtopV
        rw [Real.exp_add]; ring

end Sure

end Queue6

end
