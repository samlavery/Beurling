module

public import RequestProject.Beurling.Noise.RML7GPt
public import RequestProject.Beurling.Noise.RML7Wop
public import RequestProject.Beurling.Noise.MarginVarStep4

/-!
# Lemma 5.34, second bullet (correction #110): the scale bounds `GScaleBound` for `G = K_pt F`

For a source `F` bounded by `M_j ≥ 0` on the dyadic blocks `[v_j, 2v_j)`, `v_j = X₀⁻ 2^j`
(`j < J`), the function `G = K_pt F` satisfies `GScaleBound` (the input `hGf` of
`BModel.RML7.hG_field`) with

  `A = 70 ∑_{j<J} (log 3v_j)² M_j`,   `Gb y u = ∑_j M_j sup_{t ∈ T(y,u)} ω_t(v_j)`,

`T(y,u) = [0.89u, 2.21u] ∩ [2X₀⁻, 0.56y]` (the points read at the levels of the scale `u`,
including the kernel mass landing in the neighbouring blocks).

The proof is the paper's regrouped one (04f-bridge.tex, `lem:predictable`, second bullet):
* the pointwise bound `|G(y)| ≤ ∑_j ω_y(v_j) M_j` (`abs_Kpt_le`);
* `log y · ω_y(v) ≤ 2.9 log 3v` (Lemma 5.21(ii), `Margin.Var.logt_omega_le`) for the first
  clause;
* for the scale sum, each `T(y,u)` meets at most three dyadic blocks `[2^m, 2^{m+1})`, the map
  from scales to blocks is injective, and Lemma 5.21(iii) (`HBS.lemS_iii`) bounds
  `∑_m log(2·2^m) sup_{[2^m,2^{m+1})} ω(v)` by `10 (log 3v)²` (the one block straddling `v`
  costs `log 2v`, by (i)).
-/

@[expose] public section

open Finset Real BeurlingSystem KR.Sharp KR.TNP

namespace KR.RML7G

variable {P : BeurlingSystem}

/-- The decision times read on the indices of the primes. -/
noncomputable abbrev tI (tw : ℕ → ℝ) : ℕ → ℝ := fun i => tw (qp i)

lemma omegaW_eq_zero_of_lt (tw : ℕ → ℝ) {t v : ℝ} (hv : 0 < v) (htv : t < v) :
    P.omegaW tw t v = 0 := by
  unfold omegaW
  refine Finset.sum_eq_zero fun e he => ?_
  exfalso
  obtain ⟨-, h1, -, -⟩ := Finset.mem_filter.mp he
  have he1 := P.one_le_val e
  have he0 := P.val_pos e
  rcases le_or_gt t 0 with ht | ht
  · have : t / P.val e ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht he0.le
    linarith
  · have : t / P.val e ≤ t := div_le_self ht.le he1
    linarith

/-- The supremum of `ω(v)` over the dyadic block `[2^m, 2^{m+1})` (as in Lemma 5.21(iii)). -/
noncomputable def Bk (tw : ℕ → ℝ) (v : ℝ) (m : ℕ) : ℝ :=
  ⨆ t : Set.Ico ((2 : ℝ) ^ m) (2 * 2 ^ m), P.omegaW tw t v

/-- The block majorant used for the scale sums: the block supremum above `v`, `1` on the block
straddling `v`, `0` below `v` and above `0.56 y`. -/
noncomputable def Bk' (tw : ℕ → ℝ) (v y : ℝ) (m : ℕ) : ℝ :=
  if (2 : ℝ) ^ m ≤ 0.56 * y then
    (if v ≤ 2 ^ m then Bk (P := P) tw v m else if v < 2 * 2 ^ m then 1 else 0) else 0

/-- `sup_{t ∈ T(y,u)} ω_t(v)`, `T(y,u) = [0.89u, 2.21u] ∩ [2X₀⁻, 0.56y]`. -/
noncomputable def Ssup (tw : ℕ → ℝ) (X0m y u v : ℝ) : ℝ :=
  ⨆ t : {t : ℝ // 0.89 * u ≤ t ∧ t ≤ 2.21 * u ∧ 2 * X0m ≤ t ∧ t ≤ 0.56 * y},
    P.omegaW tw t v

/-- The dyadic block index of `0.89u`. -/
noncomputable def kb (u : ℝ) : ℕ := Nat.log 2 ⌊0.89 * u⌋₊

lemma pow_log_floor {a : ℝ} (ha : 1 ≤ a) :
    (2 : ℝ) ^ Nat.log 2 ⌊a⌋₊ ≤ a ∧ a < 2 ^ (Nat.log 2 ⌊a⌋₊ + 1) := by
  have hf : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by simpa using ha)
  have h1 := Nat.pow_log_le_self 2 (show ⌊a⌋₊ ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊a⌋₊
  constructor
  · calc (2 : ℝ) ^ Nat.log 2 ⌊a⌋₊ = ((2 ^ Nat.log 2 ⌊a⌋₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ a := Nat.floor_le (by linarith)
  · have h3 : ⌊a⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊a⌋₊ + 1) := h2
    have h4 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
    calc a < (⌊a⌋₊ : ℝ) + 1 := h4
      _ ≤ ((2 ^ (Nat.log 2 ⌊a⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h3
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊a⌋₊ + 1) := by push_cast; ring

lemma kb_spec {u : ℝ} (hu : 1 ≤ 0.89 * u) :
    (2 : ℝ) ^ kb u ≤ 0.89 * u ∧ 0.89 * u < 2 ^ (kb u + 1) := pow_log_floor hu

lemma vZ_ge {X0m Z v y : ℝ} (hX : 0 < X0m) (hv : X0m ≤ v) (hy : 0 < y)
    (hZ : 2 * y / X0m ≤ Z) : 2 * y ≤ v * Z := by
  rw [div_le_iff₀ hX] at hZ
  have hZ0 : 0 ≤ Z := by nlinarith
  have := mul_le_mul_of_nonneg_left hv hZ0
  nlinarith

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma Bk'_nonneg (tw : ℕ → ℝ) (v y : ℝ) (m : ℕ) : 0 ≤ Bk' (P := P) tw v y m := by
  unfold Bk' Bk
  split_ifs
  · exact Real.iSup_nonneg fun t => P.omegaW_nonneg tw _ _
  · norm_num
  · exact le_rfl
  · exact le_rfl

/-- A point of the block `m` (below `0.56y`) has `ω_t(v) ≤ Bk' v y m`. -/
lemma omega_le_Bk' (h : P.HBS X0m Z η1 η2 ε1) (tw : ℕ → ℝ) {v y : ℝ} (hv : X0m ≤ v)
    (hX : 0 < X0m) (hZ : 2 * y / X0m ≤ Z) {t : ℝ} {m : ℕ} (ht1 : (2 : ℝ) ^ m ≤ t)
    (ht2 : t < 2 * 2 ^ m) (hty : t ≤ 0.56 * y) :
    P.omegaW tw t v ≤ Bk' (P := P) tw v y m := by
  have hv0 : 0 < v := lt_of_lt_of_le hX hv
  have hm0 : (0 : ℝ) < 2 ^ m := by positivity
  have hy0 : 0 < y := by linarith
  have hvZ : 2 * y ≤ v * Z := vZ_ge hX hv hy0 hZ
  -- `ω ≤ 1` on the blocks below `0.56y`
  have hone : ∀ s, 0 < s → s ≤ 1.12 * y → P.omegaW tw s v ≤ 1 := by
    intro s hs hsy
    apply h.lemS_i tw hv0
    rw [div_le_iff₀ hv0]; linarith
  unfold Bk'
  rw [if_pos (by linarith)]
  split_ifs with h1 h2
  · unfold Bk
    have hbdd : BddAbove (Set.range fun s : Set.Ico ((2 : ℝ) ^ m) (2 * 2 ^ m) =>
        P.omegaW tw s v) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact hone s (by linarith [s.2.1]) (by linarith [s.2.2])
    exact le_ciSup (f := fun s : Set.Ico ((2 : ℝ) ^ m) (2 * 2 ^ m) => P.omegaW tw s v) hbdd
      ⟨t, ht1, ht2⟩
  · exact hone t (by linarith) (by linarith)
  · push_neg at h1 h2
    rw [omegaW_eq_zero_of_lt tw hv0 (by linarith)]

/-- `T(y,u)` meets at most the three blocks `kb u, kb u + 1, kb u + 2`. -/
lemma Ssup_le (h : P.HBS X0m Z η1 η2 ε1) (tw : ℕ → ℝ) {v y u : ℝ} (hv : X0m ≤ v)
    (hX : 0 < X0m) (hZ : 2 * y / X0m ≤ Z) (hu : 1 ≤ 0.89 * u) :
    Ssup (P := P) tw X0m y u v ≤ ∑ i ∈ range 3, Bk' (P := P) tw v y (kb u + i) := by
  have hS0 : 0 ≤ ∑ i ∈ range 3, Bk' (P := P) tw v y (kb u + i) :=
    Finset.sum_nonneg fun i _ => Bk'_nonneg (P := P) tw v y _
  unfold Ssup
  refine Real.iSup_le (fun t => ?_) hS0
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := t
  obtain ⟨hk1, hk2⟩ := kb_spec hu
  have hk0 : (1 : ℝ) ≤ 2 ^ kb u := one_le_pow₀ (by norm_num)
  have htpos : 1 ≤ t := by linarith
  obtain ⟨hm1, hm2⟩ := pow_log_floor htpos
  set m := Nat.log 2 ⌊t⌋₊
  -- `kb u ≤ m ≤ kb u + 2`
  have hlo : kb u ≤ m := by
    by_contra hc; push_neg at hc
    have : (2 : ℝ) ^ (m + 1) ≤ 2 ^ kb u := pow_le_pow_right₀ (by norm_num) hc
    linarith
  have hhi : m ≤ kb u + 2 := by
    by_contra hc; push_neg at hc
    have : (2 : ℝ) ^ (kb u + 3) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hc
    have e : (2 : ℝ) ^ (kb u + 3) = 4 * 2 ^ (kb u + 1) := by ring
    linarith
  have hom := omega_le_Bk' h tw hv hX hZ hm1 (by rw [pow_succ] at hm2; linarith) ht4
  obtain ⟨i, hi, hmi⟩ : ∃ i < 3, m = kb u + i := ⟨m - kb u, by omega, by omega⟩
  rw [hmi] at hom
  exact hom.trans (Finset.single_le_sum (f := fun i => Bk' (P := P) tw v y (kb u + i))
    (fun i _ => Bk'_nonneg (P := P) tw v y _) (Finset.mem_range.mpr hi))

/-- `∑_m log(2·2^m) Bk'(m) ≤ 10 (log 3v)² + log 2v` (Lemma 5.21(i), (iii)). -/
lemma sum_Bk'_le (h : P.HBS X0m Z η1 η2 ε1) (tw : ℕ → ℝ) {v y : ℝ}
    (hd : P.DecidedSmall tw v) (hv : X0m ≤ v) (hX : 0 < X0m)
    (hL : 100000000 ≤ Real.log (3 * v)) (hZ : 2 * y / X0m ≤ Z) (M : ℕ) :
    ∑ m ∈ range M, Real.log (2 * 2 ^ m) * Bk' (P := P) tw v y m ≤
      10 * Real.log (3 * v) ^ 2 + Real.log (2 * v) := by
  classical
  have hv0 : 0 < v := lt_of_lt_of_le hX hv
  have hl : ∀ m : ℕ, 0 ≤ Real.log (2 * 2 ^ m) := fun m =>
    Real.log_nonneg (by have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num); linarith)
  have hvZ : ∀ m : ℕ, (2 : ℝ) ^ m ≤ 0.56 * y → 2 * 2 ^ m ≤ v * Z := by
    intro m hm
    have hm0 : (0 : ℝ) < 2 ^ m := by positivity
    have hy0 : 0 < y := by linarith
    have := vZ_ge hX hv hy0 hZ
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not (range M) (fun m => v ≤ (2 : ℝ) ^ m)]
  apply add_le_add
  · set B := (range M).filter (fun m => v ≤ (2 : ℝ) ^ m ∧ 2 * 2 ^ m ≤ v * Z)
    have hiii := h.lemS_iii hd hv0 hL M
    refine le_trans ?_ hiii
    calc ∑ m ∈ (range M).filter (fun m => v ≤ (2 : ℝ) ^ m),
          Real.log (2 * 2 ^ m) * Bk' (P := P) tw v y m
        ≤ ∑ m ∈ (range M).filter (fun m => v ≤ (2 : ℝ) ^ m),
          (if m ∈ B then Real.log (2 * 2 ^ m) * Bk (P := P) tw v m else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hvm := (Finset.mem_filter.mp hm).2
          unfold Bk'
          by_cases h1 : (2 : ℝ) ^ m ≤ 0.56 * y
          · have hB : m ∈ B := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, hvm,
              hvZ m h1⟩
            rw [if_pos h1, if_pos hvm, if_pos hB]
          · rw [if_neg h1, mul_zero]
            split_ifs
            · exact mul_nonneg (hl m) (Real.iSup_nonneg fun t => P.omegaW_nonneg tw _ _)
            · exact le_rfl
      _ = ∑ m ∈ ((range M).filter (fun m => v ≤ (2 : ℝ) ^ m)).filter (· ∈ B),
          Real.log (2 * 2 ^ m) * Bk (P := P) tw v m := (Finset.sum_filter _ _).symm
      _ ≤ ∑ m ∈ B, Real.log (2 * 2 ^ m) * Bk (P := P) tw v m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; exact (Finset.mem_filter.mp hm).2
          · intro m _ _
            exact mul_nonneg (hl m) (Real.iSup_nonneg fun t => P.omegaW_nonneg tw _ _)
      _ = _ := rfl
  · -- the block straddling `v`
    set D := ((range M).filter (fun m => ¬ v ≤ (2 : ℝ) ^ m)).filter
      (fun m => v < 2 * (2 : ℝ) ^ m)
    have hD1 : D.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [D, Finset.mem_filter] at ha hb
      by_contra hab
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · have : (2 : ℝ) ^ (a + 1) ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hlt
        rw [pow_succ] at this; push_neg at hb; linarith [ha.2, hb.1.2]
      · have : (2 : ℝ) ^ (b + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hlt
        rw [pow_succ] at this; push_neg at ha; linarith [hb.2, ha.1.2]
    have hlv : 0 ≤ Real.log (2 * v) := Real.log_nonneg (by
      have : (10 : ℝ) ^ 7 ≤ X0m := h.X0m_ge
      linarith)
    calc ∑ m ∈ (range M).filter (fun m => ¬ v ≤ (2 : ℝ) ^ m),
          Real.log (2 * 2 ^ m) * Bk' (P := P) tw v y m
        ≤ ∑ m ∈ (range M).filter (fun m => ¬ v ≤ (2 : ℝ) ^ m),
          (if v < 2 * (2 : ℝ) ^ m then Real.log (2 * v) else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hvm := (Finset.mem_filter.mp hm).2
          push_neg at hvm
          unfold Bk'
          rw [if_neg (not_le.mpr hvm)]
          by_cases h1 : (2 : ℝ) ^ m ≤ 0.56 * y
          · rw [if_pos h1]
            by_cases h2 : v < 2 * 2 ^ m
            · rw [if_pos h2, if_pos h2, mul_one]
              exact Real.log_le_log (by positivity) (by linarith)
            · rw [if_neg h2, if_neg h2, mul_zero]
          · rw [if_neg h1, mul_zero]
            split_ifs
            · exact hlv
            · exact le_rfl
      _ = ∑ m ∈ D, Real.log (2 * v) := (Finset.sum_filter _ _).symm
      _ = D.card * Real.log (2 * v) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * Real.log (2 * v) := by
          apply mul_le_mul_of_nonneg_right _ hlv; exact_mod_cast hD1
      _ = Real.log (2 * v) := one_mul _

/-- **The scale sum** of the second bullet of Lemma 5.34 (correction #110):
`∑_{u ∈ dyScales} log(2u) sup_{T(y,u)} ω(v) ≤ 66 (log 3v)²`. -/
theorem scale_sum_le (h : P.HBS X0m Z η1 η2 ε1) (tw : ℕ → ℝ) {X0 v y : ℝ} {N : ℕ}
    (hX0 : 12 ≤ X0) (hd : P.DecidedSmall tw v) (hv : X0m ≤ v) (hX : 0 < X0m)
    (hL : 100000000 ≤ Real.log (3 * v)) (hZ : 2 * y / X0m ≤ Z) :
    ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Ssup (P := P) tw X0m y u v ≤
      66 * Real.log (3 * v) ^ 2 := by
  classical
  set S := dyScales X0 y N
  have hsep : Sep S := dyScales_sep (by linarith)
  have hu : ∀ u ∈ S, 3 ≤ u := by
    intro u hu
    obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hkb1 : ∀ u ∈ S, 1 ≤ kb u := by
    intro u hu'
    have h3 := hu u hu'
    unfold kb
    apply Nat.le_log_of_pow_le (by norm_num)
    apply Nat.le_floor; push_cast; linarith
  have hlu : ∀ u ∈ S, 0 ≤ Real.log (2 * u) := fun u hu' =>
    Real.log_nonneg (by linarith [hu u hu'])
  -- `log 2u ≤ 2 log(2·2^{kb u + i})`
  have hlog : ∀ u ∈ S, ∀ i : ℕ, Real.log (2 * u) ≤ 2 * Real.log (2 * 2 ^ (kb u + i)) := by
    intro u hu' i
    obtain ⟨-, hk2⟩ := kb_spec (show 1 ≤ 0.89 * u by linarith [hu u hu'])
    have hk1 := hkb1 u hu'
    have h2k : (2 : ℝ) ≤ 2 ^ kb u := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ kb u := pow_le_pow_right₀ (by norm_num) hk1
    have hpi : (2 : ℝ) ^ kb u ≤ 2 ^ (kb u + i) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2u : 2 * u ≤ (2 * 2 ^ (kb u + i)) ^ 2 := by
      rw [pow_succ] at hk2
      nlinarith
    rw [← Real.log_rpow (by positivity)]
    exact Real.log_le_log (by linarith [hu u hu']) (by exact_mod_cast h2u)
  -- injectivity of the block map
  have hinj : ∀ i : ℕ, Set.InjOn (fun u => kb u + i) S := by
    intro i u hu' u' hu'' he
    simp only at he
    have he' : kb u = kb u' := by omega
    obtain ⟨a1, a2⟩ := kb_spec (show 1 ≤ 0.89 * u by linarith [hu u hu'])
    obtain ⟨b1, b2⟩ := kb_spec (show 1 ≤ 0.89 * u' by linarith [hu u' hu''])
    rw [he'] at a1 a2
    rw [pow_succ] at a2 b2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hsep u hu' u' hu'' hlt; nlinarith
    · have := hsep u' hu'' u hu' hlt; nlinarith
  have hstep : ∀ i ∈ range 3, ∑ u ∈ S, Real.log (2 * u) * Bk' (P := P) tw v y (kb u + i) ≤
      2 * (10 * Real.log (3 * v) ^ 2 + Real.log (2 * v)) := by
    intro i _
    calc ∑ u ∈ S, Real.log (2 * u) * Bk' (P := P) tw v y (kb u + i)
        ≤ ∑ u ∈ S, 2 * (Real.log (2 * 2 ^ (kb u + i)) * Bk' (P := P) tw v y (kb u + i)) := by
          refine Finset.sum_le_sum fun u hu' => ?_
          have := mul_le_mul_of_nonneg_right (hlog u hu' i) (Bk'_nonneg (P := P) tw v y (kb u + i))
          linarith
      _ = 2 * ∑ m ∈ S.image (fun u => kb u + i),
          Real.log (2 * 2 ^ m) * Bk' (P := P) tw v y m := by
          rw [Finset.mul_sum, Finset.sum_image (hinj i)]
      _ ≤ 2 * ∑ m ∈ range ((S.image (fun u => kb u + i)).sup id + 1),
          Real.log (2 * 2 ^ m) * Bk' (P := P) tw v y m := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
          · intro m _ _
            exact mul_nonneg (Real.log_nonneg (by
              have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num); linarith))
              (Bk'_nonneg (P := P) tw v y m)
      _ ≤ 2 * (10 * Real.log (3 * v) ^ 2 + Real.log (2 * v)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact sum_Bk'_le h tw hd hv hX hL hZ _
  have hl2v : Real.log (2 * v) ≤ Real.log (3 * v) ^ 2 := by
    have hv0 : 0 < v := lt_of_lt_of_le hX hv
    have h1 : Real.log (2 * v) ≤ Real.log (3 * v) :=
      Real.log_le_log (by positivity) (by linarith)
    nlinarith
  calc ∑ u ∈ S, Real.log (2 * u) * Ssup (P := P) tw X0m y u v
      ≤ ∑ u ∈ S, Real.log (2 * u) * ∑ i ∈ range 3, Bk' (P := P) tw v y (kb u + i) := by
        refine Finset.sum_le_sum fun u hu' => ?_
        exact mul_le_mul_of_nonneg_left
          (Ssup_le h tw hv hX hZ (by linarith [hu u hu'])) (hlu u hu')
    _ = ∑ i ∈ range 3, ∑ u ∈ S, Real.log (2 * u) * Bk' (P := P) tw v y (kb u + i) := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ ∑ i ∈ range 3, 2 * (10 * Real.log (3 * v) ^ 2 + Real.log (2 * v)) :=
        Finset.sum_le_sum hstep
    _ = 6 * (10 * Real.log (3 * v) ^ 2 + Real.log (2 * v)) := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ ≤ 66 * Real.log (3 * v) ^ 2 := by linarith

end KR.RML7G

end
