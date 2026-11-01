module

public import RequestProject.Beurling.Noise.KRTransStart
public import RequestProject.Beurling.Noise.KRTrueProp

/-!
# The transfer bound of Proposition 5.18 (proof, step (ii), first display)

For a `τ`-source level `n'` (`n' ≥ 2`, `y := x/n' ≥ X₀⁻`) and a scale `u`,

  `∑_{x/n ∈ [u,2u)} TV(𝒯^nom_{n'→n} S^τ_{n'})/n ≤ λ₀ (TV(S^τ_{n'})/n') · C_N log(2u)/log(x/n')`

(`transferBound`, the named hypothesis `TransferBound` of `KRTrueProp.lean`), with
`C_N = C_S(2.04 + 4.71/log X₀)`, under (HBS), the paper's width hypotheses and
`1 + 2θ ≤ λ₀ ≤ 1.001`, for scale families of dyadic type (`2u ≤ X₀⁻` or `2u ≥ X₀`).

The proof is the paper's: the source `S^τ_{n'}` lives on `[0.85 y, ∞)` (`Stau_lower`); the chain
from it is the superposition of the kernels started at `δ_v` with the nominal filters of the
start `y` (`Tch_rep`, `kSh_kapN`, `gK_congr`), so its total variation at level `n'm` is at most
`∫ |S^τ(v)| TV(C^{v,y}_m) dv`; and Corollary 5.17(b) for these kernels (`cor_5_17_b_sh`) bounds
`∑_{y/m ∈ [u,2u)} TV(C^{v,y}_m)/m ≤ C_N log(2u)/log y` for every `v ≥ 0.85 y`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-! ## Frozen filters -/

/-- The densities depend only on the filters into levels `m ≥ 2`. -/
lemma gK_congr {κ1 κ2 : ℕ → ℕ → ℝ} (h : ∀ d m, 2 ≤ m → κ1 d m = κ2 d m) (v : ℝ) :
    ∀ m, gK val v H (constF κ1) m = gK val v H (constF κ2) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [gK_le_one val v H (show m ≤ 1 by omega), gK_le_one val v H (show m ≤ 1 by omega)]
  funext t
  rw [gK_eq val v H hm, gK_eq val v H hm]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hI := ih d (Nat.mem_properDivisors.mp hd).2
  unfold stepK
  rw [hI]
  simp only [constF, h 1 m hm, h d m hm]

/-- The frozen filters of the chains from `n'` are the nominal filters of the start `x/n'`. -/
lemma kSh_kapN (hval : ∀ p, p.Prime → 1 ≤ val p) {n' : ℕ} (hn' : 1 ≤ n') (d : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    kSh (kapN tw X0m val x) n' d m = nomFilter val (posn val x n') tw X0m d m := by
  have hV' := LemmaM.valN_pos val hval (n := n')
  have hVm := LemmaM.valN_pos val hval (n := m)
  have hmul : LemmaM.valN val (n' * m) = LemmaM.valN val n' * LemmaM.valN val m :=
    LemmaM.valN_mul val (by omega) (by omega)
  have hdiv : n' * m / (n' * d) = m / d := Nat.mul_div_mul_left m d (by omega)
  have key : (LemmaM.filt tw val x (n' * m) (n' * d) ∧
      X0m ≤ x / LemmaM.valN val (n' * m)) ↔
      (LemmaM.filt tw val (posn val x n') m d ∧
        X0m ≤ posn val x n' / LemmaM.valN val m) := by
    unfold LemmaM.filt posn
    rw [hdiv, hmul, div_div]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun p hp => ?_, h2⟩
      have := h1 p hp
      rw [lt_div_iff₀ hV']; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun p hp => ?_, h2⟩
      have := h1 p hp
      rw [lt_div_iff₀ hV'] at this; linarith
  unfold kSh kapN nomFilter
  by_cases hA : LemmaM.filt tw val x (n' * m) (n' * d) ∧ X0m ≤ x / LemmaM.valN val (n' * m)
  · rw [if_pos hA, if_pos (key.mp hA)]
  · rw [if_neg hA, if_neg (fun hB => hA (key.mpr hB))]

/-! ## The support of the source -/

/-- **The source `S^τ_{n'}` lives on `[0.85 x/n', ∞)`** (for `x/n' ≥ X₀⁻`). -/
theorem Stau_lower {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ val p)
    {n : ℕ} (hpos : X0m ≤ posn val x n) {t : ℝ} (ht : Stau val x H tw X0m n t ≠ 0) :
    0.85 * posn val x n ≤ t := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  have hX := hP.X0m_pos
  unfold Stau SsrcP at ht
  obtain ⟨d, hd, hdt⟩ : ∃ d ∈ n.properDivisors.filter (fun d => ¬ X0Near val x H X0m d n),
      srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t ≠ 0 := by
    by_contra hc; push_neg at hc
    exact ht (by rw [Finset.sum_eq_zero hc, neg_zero])
  have hd' := (Finset.mem_filter.mp hd).1
  have hn0 : n ≠ 0 := by
    rintro rfl; simp at hd'
  have hdn := (Nat.mem_properDivisors.mp hd').1
  by_cases h1 : d = 1
  · subst h1; exact absurd (srcStep_one hval n t) hdt
  unfold srcStep at hdt
  rw [if_neg h1] at hdt
  unfold Qd at hdt
  set w := LemmaM.valN val (n / d)
  have hw := two_le_valN hval2 (two_le_div_of_mem hd')
  have hw0 : 0 < w := by linarith
  obtain ⟨v, hv⟩ : ∃ v, (phiT tw X0m d n (v / w) - kapN tw X0m val x d n) *
      gK val x H (phiT tw X0m) d v * kd H (v / w) t ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hdt (by rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall hc)])
  have hg : gK val x H (phiT tw X0m) d v ≠ 0 := fun h => hv (by rw [h]; ring)
  have hk : kd H (v / w) t ≠ 0 := fun h => hv (by rw [h]; ring)
  obtain ⟨hposd, hvd⟩ := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h) d v hg
  have hpd : posn val x d = posn val x n * w := posn_mul hval hdn hn0
  have hsd := hP.small (posn val x d) hposd
  have hvd' := (abs_le.mp hvd).1
  -- `v/w ≥ 0.898 x/n`
  have hvw : 0.898 * posn val x n ≤ v / w := by
    rw [le_div_iff₀ hw0]
    rw [hpd] at hvd' hsd
    nlinarith
  have hsv := hP.small (v / w) (by nlinarith)
  unfold kd Set.indicator at hk
  split_ifs at hk with hm
  · have := hm.1; nlinarith
  · simp at hk

/-! ## Finite total variation of the shifted kernels -/

/-- The shifted kernels have finite total variation. -/
lemma eVariationOn_kS_ne_top (P : BeurlingSystem) {ε θ lam0 : ℝ} {v y : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (hlam : 1 + 2 * θ ≤ lam0)
    (_hy : X0m ≤ y) (hv : 0.85 * y ≤ v) {n : ℕ} (hn : n ≠ 0) :
    eVariationOn (kS P H tw X0m v y n) univ ≠ ⊤ := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have : kS P H tw X0m v y 1 = stepF v := kerV_one _ _ _ _
    rw [this]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (eVariationOn_stepF_le v)
  have hκ0 : ∀ d m, nomFilter P.labelVal y tw X0m d m ≠ 0 →
      0.6 * X0m ≤ posn P.labelVal v m := by
    intro d m hk
    have h1 := nomFilter_ne_zero hk
    have hVm := KR.valN_labelVal_pos P m
    unfold posn at h1 ⊢
    have : 0.85 * (y / LemmaM.valN P.labelVal m) ≤ v / LemmaM.valN P.labelVal m := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hv hVm.le
    linarith
  obtain ⟨hTV, -⟩ := theorem_5_15 hval hP.reg (abs_nomFilter_le P.labelVal y tw X0m)
    (by norm_num : (1 : ℝ) / 2 ≤ 1.02) (by linarith [hP.theta_nonneg])
    (radiusCond_gen hP hval2 hκ0) (widthCond_gen hP hval2 hlam hκ0) h2 (x := v)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTV

/-- Below `X₀⁻` (for the start `y`) the shifted kernels vanish. -/
lemma kS_eq_zero_low (P : BeurlingSystem) {v y : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hlow : y / LemmaM.valN P.labelVal m < X0m) : kS P H tw X0m v y m = fun _ => 0 := by
  funext t
  rw [kS, kerV_eq _ _ _ _ hm]
  rw [Finset.sum_eq_zero fun d _ => ?_, neg_zero]
  have : nomFilter P.labelVal y tw X0m d m = 0 := by
    by_contra hc
    exact absurd (nomFilter_ne_zero hc) (by unfold posn; exact not_le.mpr hlow)
  rw [this, zero_mul]

/-- `∑ ∫ g_i ≤ ∫ ∑ g_i` (superadditivity of the lower integral). -/
lemma sum_lintegral_le {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ v, g i v ≤ ∫⁻ v, ∑ i ∈ s, g i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-! ## Corollary 5.17(b) for the shifted kernels, at every scale -/

variable (P : BeurlingSystem)

/-- `∑_{y/m ∈ [u,2u)} TV(C^{v,y}_m)/m ≤ C_N log(2u)/log y` for every start `v ≥ 0.85 y`, at
every scale of dyadic type (`2u ≤ X₀⁻` or `2u ≥ X₀`). -/
theorem WS_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) {X0 y u v : ℝ} (hy : X0m ≤ y) (hyZ : 2 * y / X0m ≤ Z)
    (hv : 0.85 * y ≤ v) (hX0 : 0 < Real.log X0) (hX0m : X0m ≤ X0) (hu1 : 1 / 2 ≤ u)
    (hdy : 2 * u ≤ X0m ∨ X0 ≤ 2 * u) :
    WS P H tw X0m v y u ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 *
      (2.04 + 4.71 / Real.log X0) * Real.log (2 * u) / Real.log y := by
  have hX := h.X0m_ge
  have hXp := h.X0m_pos
  have hy1 : 1 < y := by norm_num at hX; linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hu0 : 0 < u := by linarith
  have hCS : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_of_le_right (by norm_num)
  have hl2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 *
      (2.04 + 4.71 / Real.log X0) * Real.log (2 * u) / Real.log y := by positivity
  have hV1 : ∀ m, 1 ≤ LemmaM.valN P.labelVal m := KR.one_le_valN_label P
  rcases lt_or_ge y u with hyu | huy
  · -- no level in the window
    have : NW P y u = ∅ := by
      ext m
      simp only [Finset.notMem_empty, iff_false]
      intro hm
      obtain ⟨-, h1, -⟩ := (mem_NW P hu0).mp hm
      have := div_le_self (by linarith : (0 : ℝ) ≤ y) (hV1 m)
      linarith
    rw [WS, this, Finset.sum_empty]; exact hK0
  rcases hdy with hlow | hhigh
  · -- the window lies below `X₀⁻`
    have : WS P H tw X0m v y u = 0 := by
      rw [WS]
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨hm0, -, h2⟩ := (mem_NW P hu0).mp hm
      rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        rw [LemmaM.valN_one, div_one] at h2; linarith
      · rw [kS_eq_zero_low P hm2 (by linarith), eVariationOn_zero_fun, ENNReal.toReal_zero,
          zero_div]
    rw [this]; exact hK0
  · have hu : X0m / 2 ≤ u := by linarith
    have hB : y / u ≤ Z := by
      refine le_trans ?_ hyZ
      rw [div_le_div_iff₀ hu0 hXp]; nlinarith
    have hε : ε ≤ 0.03 := by have := hP.eps_le; linarith
    have hb := cor_5_17_b_sh (P := P) (lam0 := lam0) hP hp2 ht hlam hy hv hy1 hu huy hCS
      (saiasAt_of_hbs P h hXm (thm56_of_hbs P h) ht htv hy hyZ) (hordSumsB P h hXm hε hB)
      hu1
    have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
    have hX0u : Real.log X0 ≤ Real.log (2 * u) :=
      Real.log_le_log (by linarith) hhigh
    refine cor_5_17_b_CN hCS hy1 hX0 hX0u ?_ ?_ hb
    · nlinarith
    · nlinarith

/-! ## The transfer bound -/

/-- **The transfer bound** (Proposition 5.18, proof, step (ii), first display), with
`C_N = C_S(2.04 + 4.71/log X₀)`. -/
theorem transferBound {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) {X0 x : ℝ} (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) :
    TransferBound P H tw X0m x Sc lam0
      (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hκ : ∀ d n, 0 ≤ kapN tw X0m P.labelVal x d n ∧ kapN tw X0m P.labelVal x d n ≤ 1 :=
    fun d n => kapN_mem P.labelVal x d n
  have hXp := h.X0m_pos
  intro n' hn'2 hpos u hu
  set y := posn P.labelVal x n'
  set f := Stau P.labelVal x H tw X0m n'
  set CN := max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  have hV1 : ∀ m, 1 ≤ V m := KR.one_le_valN_label P
  obtain ⟨hfi, hfm⟩ := integrable_Stau (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m)
    hP.reg n'
  have hn'1 : 1 ≤ n' := by omega
  have hy : X0m ≤ y := hpos
  have hyx : y ≤ x := by
    have hx0 : 0 ≤ x := by
      have : 0 < y := by linarith
      by_contra hc; push_neg at hc
      have : y < 0 := div_neg_of_neg_of_pos hc (hV n')
      linarith
    exact div_le_self hx0 (hV1 n')
  have hyZ : 2 * y / X0m ≤ Z := le_trans (div_le_div_of_nonneg_right (by linarith) hXp.le) hxZ
  have hu0 : 0 < u := by linarith [hSc1 u hu]
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith [hSc1 u hu])
  have hCS : (0 : ℝ) ≤ CN := by
    have : 0 ≤ 4.71 / Real.log X0 := by positivity
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  set K := CN * Real.log (2 * u) / Real.log y
  have hK0 : 0 ≤ K := by positivity
  -- `E(v, n)`: the total variation at level `n` of the kernel from `δ_v`
  set E : ℝ → ℕ → ℝ≥0∞ := fun v n =>
    if n' ∣ n then eVariationOn (kS P H tw X0m v y (n / n')) univ else 0
  -- per level
  have hlev : ∀ n ∈ NW P x u, ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≤
      ∫⁻ v, ‖f v‖ₑ * E v n := by
    intro n hn
    obtain ⟨hn0, -, -⟩ := (mem_NW P hu0).mp hn
    by_cases hd : n' ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
      have hmn : n' * m / n' = m := Nat.mul_div_cancel_left m (by omega)
      rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        rw [mul_one, Tch_self]
        refine lintegral_mono fun v => ?_
        have hE : 1 ≤ E v n' := by
          simp only [E, if_pos (dvd_refl n'), Nat.div_self (show 0 < n' by omega)]
          have : kS P H tw X0m v y 1 = stepF v := kerV_one _ _ _ _
          rw [this]; exact one_le_eVariationOn_stepF v
        calc ‖f v‖ₑ = ‖f v‖ₑ * 1 := (mul_one _).symm
          _ ≤ ‖f v‖ₑ * E v n' := by gcongr
      · refine (lintegral_Tch_le hP.reg hκ hn'1 hfi hfm hm2).trans (lintegral_mono fun v => ?_)
        simp only [E, if_pos (dvd_mul_right n' m), hmn]
        gcongr
        rw [gK_congr (fun d m' hm' => kSh_kapN hval hn'1 d (by omega)) v m]
        exact lintegral_gK_nom_le hval hP.reg (fun d n => ⟨by unfold nomFilter; split_ifs <;>
          norm_num, by unfold nomFilter; split_ifs <;> norm_num⟩) hm2
    · rw [Tch_not_dvd f n hd]; simp
  -- per start
  have hstart : ∀ v, f v ≠ 0 → ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * E v n ≤
      ENNReal.ofReal (K / V n') := by
    intro v hfv
    have hv : 0.85 * y ≤ v := Stau_lower hP hval2 hpos hfv
    set T := (NW P x u).filter (n' ∣ ·)
    have hfin : ∀ n ∈ T, E v n = ENNReal.ofReal
        ((eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal) := by
      intro n hn
      obtain ⟨hn1, hd⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, -, -⟩ := (mem_NW P hu0).mp hn1
      have hm0 : n / n' ≠ 0 := by
        obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left m (by omega)]; rintro rfl; simp at hn0
      simp only [E, if_pos hd]
      rw [ENNReal.ofReal_toReal (eVariationOn_kS_ne_top P hP hp2 hlam hy hv hm0)]
    calc ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * E v n
        = ∑ n ∈ T, ENNReal.ofReal (1 / V n) * E v n := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          split_ifs with hd
          · rfl
          · simp only [E, if_neg hd, mul_zero]
      _ = ENNReal.ofReal (∑ n ∈ T,
            (eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal / V n) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => div_nonneg ENNReal.toReal_nonneg
            (hV n).le)]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hfin n hn, ← ENNReal.ofReal_mul (by have := hV n; positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (K / V n') := by
          apply ENNReal.ofReal_le_ofReal
          have hreidx : ∑ n ∈ T, (eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal / V n =
              1 / V n' * ∑ m ∈ T.image (· / n'),
                (eVariationOn (kS P H tw X0m v y m) univ).toReal / V m := by
            rw [Finset.sum_image, Finset.mul_sum]
            · refine Finset.sum_congr rfl fun n hn => ?_
              obtain ⟨hn1, hd⟩ := Finset.mem_filter.mp hn
              obtain ⟨hn0, -, -⟩ := (mem_NW P hu0).mp hn1
              have hVn : V n = V n' * V (n / n') := valN_div_mul hval hd hn0
              rw [hVn]
              have := hV n'; have := hV (n / n')
              field_simp
            · intro a ha b hb hab
              obtain ⟨-, ⟨ka, rfl⟩⟩ := Finset.mem_filter.mp ha
              obtain ⟨-, ⟨kb, rfl⟩⟩ := Finset.mem_filter.mp hb
              simp only at hab
              rw [Nat.mul_div_cancel_left ka (by omega),
                Nat.mul_div_cancel_left kb (by omega)] at hab
              rw [hab]
          rw [hreidx]
          have hsub : T.image (· / n') ⊆ NW P y u := by
            intro m hm
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
            obtain ⟨hn1, ⟨k, rfl⟩⟩ := Finset.mem_filter.mp hn
            obtain ⟨hn0, h1, h2⟩ := (mem_NW P hu0).mp hn1
            rw [Nat.mul_div_cancel_left k (by omega)]
            have hk0 : k ≠ 0 := by rintro rfl; simp at hn0
            have e : x / V (n' * k) = y / V k := by
              simp only [y, posn, V]
              rw [LemmaM.valN_mul _ (by omega) hk0, div_div]
            rw [mem_NW P hu0]
            exact ⟨hk0, e ▸ h1, e ▸ h2⟩
          have hWS := WS_le P h hXm hP hp2 ht htv hlam hlam1 hy hyZ hv hX0 hX0m (hSc1 u hu)
            (hSc u hu)
          calc 1 / V n' * ∑ m ∈ T.image (· / n'),
                (eVariationOn (kS P H tw X0m v y m) univ).toReal / V m
              ≤ 1 / V n' * WS P H tw X0m v y u := by
                apply mul_le_mul_of_nonneg_left _ (by have := hV n'; positivity)
                exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
                  div_nonneg ENNReal.toReal_nonneg (hV m).le
            _ ≤ 1 / V n' * K := mul_le_mul_of_nonneg_left hWS (by have := hV n'; positivity)
            _ = K / V n' := by ring
  -- assembly in `ℝ≥0∞`
  have hfin_f : ∫⁻ v, ‖f v‖ₑ ≠ ⊤ := hfi.2.ne
  have hENN : ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) *
      ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≤
      ENNReal.ofReal (K / V n') * ∫⁻ v, ‖f v‖ₑ := by
    calc ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) *
          ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ
        ≤ ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * ∫⁻ v, ‖f v‖ₑ * E v n :=
          Finset.sum_le_sum fun n hn => mul_le_mul_right (hlev n hn) _
      _ = ∑ n ∈ NW P x u, ∫⁻ v, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) :=
          Finset.sum_congr rfl fun n _ =>
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ v, ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) :=
          sum_lintegral_le _ _
      _ ≤ ∫⁻ v, ‖f v‖ₑ * ENNReal.ofReal (K / V n') := by
          refine lintegral_mono fun v => ?_
          have e : ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) =
              ‖f v‖ₑ * ∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) * E v n := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
          rw [e]
          by_cases hfv : f v = 0
          · simp [hfv]
          · exact mul_le_mul_right (hstart v hfv) _
      _ = ENNReal.ofReal (K / V n') * ∫⁻ v, ‖f v‖ₑ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  -- back to `ℝ`
  have hTfin : ∀ n, ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≠ ⊤ :=
    fun n => ((integrable_Tch hP.reg _ n' hfi hfm) n).1.2.ne
  have hlhs : ∑ n ∈ NW P x u, tauPart P H tw X0m x n' n / Vl P n =
      (∑ n ∈ NW P x u, ENNReal.ofReal (1 / V n) *
        ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ).toReal := by
    rw [ENNReal.toReal_sum (fun n _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin n))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := hV n; positivity)]
    unfold tauPart
    simp only [f, V, Vl]
    ring
  rw [hlhs]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_f) hENN).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := hV n'; positivity)]
  have hlam0 : 1 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hS0 : 0 ≤ (∫⁻ t, ‖f t‖ₑ).toReal := ENNReal.toReal_nonneg
  have hVn' := hV n'
  have e : lam0 * ((∫⁻ t, ‖f t‖ₑ).toReal / Vl P n') *
      (CN * Real.log (2 * u) / Real.log y) = lam0 * (K / V n' * (∫⁻ t, ‖f t‖ₑ).toReal) := by
    simp only [K, Vl, V]; ring
  show K / V n' * (∫⁻ v, ‖f v‖ₑ).toReal ≤
    lam0 * ((∫⁻ t, ‖f t‖ₑ).toReal / Vl P n') * (CN * Real.log (2 * u) / Real.log y)
  rw [e]
  have h0 : 0 ≤ K / V n' * (∫⁻ t, ‖f t‖ₑ).toReal := by positivity
  nlinarith

end KR

end
