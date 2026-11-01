module

public import RequestProject.Beurling.Noise.KRNormC

/-!
# The transfers of Proposition 5.18 without scale weights

For a `τ`-source at the level `n'` (`n' ≥ 2`, `y := x/n' ≥ X₀⁻`) and any finite set `T` of
levels,

* `transferInf` : `∑_{n ∈ T} TV(𝒯^nom_{n'→n} S^τ_{n'})/n ≤ 2.04 (log(x/n') + B₁) TV(S^τ_{n'})/n'`
  (the transfer of the `∞`-norm part of the proof: Corollary 5.17(c) in place of (b));
* `transferBlock` : for `T` the levels of one dyadic block `[u, 2u)`,
  `∑ TV(𝒯^nom_{n'→n} S^τ_{n'})/n ≤ 2.04 TV(S^τ_{n'})/n'` (the transfer of the block bound: no
  Saias bound, as `W^sh ≤ 1`).

The proof is that of `transferBound`: the chain from the source is the superposition of the
shifted kernels `C^{v,y}`, `v ≥ 0.85 y` (`Tch_rep`), and the per-start sums are bounded by
`sum_kS_le` (Corollary 5.17(c)) resp. by Corollary 5.17(a) with `W^sh ≤ 1`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- **The general transfer**: if for every start `v ≥ 0.85 y` and every finite family of levels
`M` of the start `y`, `∑_{m ∈ M} TV(C^{v,y}_m)/m ≤ K`, then for every finite set `T` of levels
`∑_{n ∈ T} TV(𝒯_{n'→n} S^τ_{n'})/n ≤ K TV(S^τ_{n'})/n'`, where only the levels `m = n/n'`
with `n ∈ T` enter (`Mset`). -/
theorem transfer_gen {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (hlam : 1 + 2 * θ ≤ lam0) {n' : ℕ} (hn'2 : 2 ≤ n') (hpos : X0m ≤ posn P.labelVal x n')
    (T : Finset ℕ) (hT : ∀ n ∈ T, n ≠ 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v, 0.85 * posn P.labelVal x n' ≤ v →
      ∑ m ∈ (T.filter (n' ∣ ·)).image (· / n'),
        (eVariationOn (kS P H tw X0m v (posn P.labelVal x n') m) univ).toReal /
          LemmaM.valN P.labelVal m ≤ K) :
    ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n ≤
      K * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hκ : ∀ d n, 0 ≤ kapN tw X0m P.labelVal x d n ∧ kapN tw X0m P.labelVal x d n ≤ 1 :=
    fun d n => kapN_mem P.labelVal x d n
  set y := posn P.labelVal x n'
  set f := Stau P.labelVal x H tw X0m n'
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  obtain ⟨hfi, hfm⟩ := integrable_Stau (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m)
    hP.reg n'
  have hn'1 : 1 ≤ n' := by omega
  have hy : X0m ≤ y := hpos
  set E : ℝ → ℕ → ℝ≥0∞ := fun v n =>
    if n' ∣ n then eVariationOn (kS P H tw X0m v y (n / n')) univ else 0
  have hlev : ∀ n ∈ T, ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≤
      ∫⁻ v, ‖f v‖ₑ * E v n := by
    intro n hn
    have hn0 := hT n hn
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
  have hstart : ∀ v, f v ≠ 0 → ∑ n ∈ T, ENNReal.ofReal (1 / V n) * E v n ≤
      ENNReal.ofReal (K / V n') := by
    intro v hfv
    have hv : 0.85 * y ≤ v := Stau_lower hP hval2 hpos hfv
    set T' := T.filter (n' ∣ ·)
    have hfin : ∀ n ∈ T', E v n = ENNReal.ofReal
        ((eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal) := by
      intro n hn
      obtain ⟨hn1, hd⟩ := Finset.mem_filter.mp hn
      have hn0 := hT n hn1
      have hm0 : n / n' ≠ 0 := by
        obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left m (by omega)]; rintro rfl; simp at hn0
      simp only [E, if_pos hd]
      rw [ENNReal.ofReal_toReal (eVariationOn_kS_ne_top P hP hp2 hlam hy hv hm0)]
    calc ∑ n ∈ T, ENNReal.ofReal (1 / V n) * E v n
        = ∑ n ∈ T', ENNReal.ofReal (1 / V n) * E v n := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          split_ifs with hd
          · rfl
          · simp only [E, if_neg hd, mul_zero]
      _ = ENNReal.ofReal (∑ n ∈ T',
            (eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal / V n) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => div_nonneg ENNReal.toReal_nonneg
            (hV n).le)]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hfin n hn, ← ENNReal.ofReal_mul (by have := hV n; positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (K / V n') := by
          apply ENNReal.ofReal_le_ofReal
          have hreidx : ∑ n ∈ T', (eVariationOn (kS P H tw X0m v y (n / n')) univ).toReal /
              V n = 1 / V n' * ∑ m ∈ T'.image (· / n'),
                (eVariationOn (kS P H tw X0m v y m) univ).toReal / V m := by
            rw [Finset.sum_image, Finset.mul_sum]
            · refine Finset.sum_congr rfl fun n hn => ?_
              obtain ⟨hn1, hd⟩ := Finset.mem_filter.mp hn
              have hn0 := hT n hn1
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
          calc 1 / V n' * ∑ m ∈ T'.image (· / n'),
                (eVariationOn (kS P H tw X0m v y m) univ).toReal / V m
              ≤ 1 / V n' * K := mul_le_mul_of_nonneg_left (hK v hv)
                (by have := hV n'; positivity)
            _ = K / V n' := by ring
  have hfin_f : ∫⁻ v, ‖f v‖ₑ ≠ ⊤ := hfi.2.ne
  have hENN : ∑ n ∈ T, ENNReal.ofReal (1 / V n) *
      ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≤
      ENNReal.ofReal (K / V n') * ∫⁻ v, ‖f v‖ₑ := by
    calc ∑ n ∈ T, ENNReal.ofReal (1 / V n) *
          ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ
        ≤ ∑ n ∈ T, ENNReal.ofReal (1 / V n) * ∫⁻ v, ‖f v‖ₑ * E v n :=
          Finset.sum_le_sum fun n hn => mul_le_mul_right (hlev n hn) _
      _ = ∑ n ∈ T, ∫⁻ v, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) :=
          Finset.sum_congr rfl fun n _ =>
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ v, ∑ n ∈ T, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) :=
          sum_lintegral_le _ _
      _ ≤ ∫⁻ v, ‖f v‖ₑ * ENNReal.ofReal (K / V n') := by
          refine lintegral_mono fun v => ?_
          have e : ∑ n ∈ T, ENNReal.ofReal (1 / V n) * (‖f v‖ₑ * E v n) =
              ‖f v‖ₑ * ∑ n ∈ T, ENNReal.ofReal (1 / V n) * E v n := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
          rw [e]
          by_cases hfv : f v = 0
          · simp [hfv]
          · exact mul_le_mul_right (hstart v hfv) _
      _ = ENNReal.ofReal (K / V n') * ∫⁻ v, ‖f v‖ₑ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  have hTfin : ∀ n, ∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n' f n t‖ₑ ≠ ⊤ :=
    fun n => ((integrable_Tch hP.reg _ n' hfi hfm) n).1.2.ne
  have hlhs : ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n =
      (∑ n ∈ T, ENNReal.ofReal (1 / V n) *
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
  show K / V n' * (∫⁻ v, ‖f v‖ₑ).toReal ≤ K * ((∫⁻ t, ‖f t‖ₑ).toReal / Vl P n')
  simp only [Vl, V]
  ring_nf
  exact le_rfl

/-- The levels `m = n/n'` of a family `T` that carry mass lie in `NAll P y X₀⁻`. -/
lemma sum_image_le_NAll {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {n' : ℕ} (hn'1 : 1 ≤ n')
    {v y : ℝ} (hy : X0m ≤ y) (T : Finset ℕ) (hT : ∀ n ∈ T, n ≠ 0) :
    ∑ m ∈ (T.filter (n' ∣ ·)).image (· / n'),
        (eVariationOn (kS P H tw X0m v y m) univ).toReal / LemmaM.valN P.labelVal m ≤
      ∑ m ∈ NAll P y X0m,
        (eVariationOn (kS P H tw X0m v y m) univ).toReal / LemmaM.valN P.labelVal m := by
  classical
  have hX := hP.X0m_pos
  set g : ℕ → ℝ := fun m =>
    (eVariationOn (kS P H tw X0m v y m) univ).toReal / LemmaM.valN P.labelVal m
  have hg : ∀ m, 0 ≤ g m := fun m =>
    div_nonneg ENNReal.toReal_nonneg (KR.valN_labelVal_pos P m).le
  rw [← Finset.sum_filter_of_ne (p := fun m => m ∈ NAll P y X0m)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.mp hm).2)
      fun m _ _ => hg m
  · intro m hm hne
    by_contra hnot
    apply hne
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hnT, ⟨k, rfl⟩⟩ := Finset.mem_filter.mp hn
    have hn0 := hT _ hnT
    rw [Nat.mul_div_cancel_left k (by omega)] at hnot ⊢
    have hk0 : k ≠ 0 := by rintro rfl; simp at hn0
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      exfalso; apply hnot
      apply KR.mem_image_iota P one_ne_zero
      rw [LemmaM.valN_one, le_div_iff₀ hX]; linarith
    · have hlow : y / LemmaM.valN P.labelVal k < X0m := by
        by_contra hc; push_neg at hc
        apply hnot
        apply KR.mem_image_iota P hk0
        have hVk := KR.valN_labelVal_pos P k
        rw [le_div_iff₀ hX]; rw [le_div_iff₀ hVk] at hc; linarith
      rw [kS_eq_zero_low P hk2 hlow, eVariationOn_zero_fun, ENNReal.toReal_zero, zero_div]

/-- **The transfer of the `∞`-norm part**: `∑_{n ∈ T} TV(𝒯_{n'→n} S^τ_{n'})/n ≤
2.04 (log(x/n') + B₁) TV(S^τ_{n'})/n'` (`B₁ = 1`). -/
theorem transferInf {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hxZ : 2 * x / X0m ≤ Z) {n' : ℕ} (hn'2 : 2 ≤ n')
    (hpos : X0m ≤ posn P.labelVal x n') (T : Finset ℕ) (hT : ∀ n ∈ T, n ≠ 0) :
    ∑ n ∈ T, tauPart P H tw X0m x n' n / Vl P n ≤
      2.04 * (Real.log (posn P.labelVal x n') + 1) *
        ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') := by
  have hX := h.X0m_pos
  have hy := hpos
  set y := posn P.labelVal x n'
  have hV1 := KR.one_le_valN_label P n'
  have hyx : y ≤ x := by
    have hx0 : 0 ≤ x := by
      by_contra hc; push_neg at hc
      have : y < 0 := div_neg_of_neg_of_pos hc (KR.valN_labelVal_pos P n')
      linarith
    exact div_le_self hx0 hV1
  have hyZ : y / X0m ≤ Z := by
    refine le_trans ?_ hxZ
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  have hly : 0 ≤ Real.log y + 1 := by
    have : 0 ≤ Real.log y := Real.log_nonneg (by have := h.X0m_ge; norm_num at this; linarith)
    linarith
  refine transfer_gen hP hp2 hlam hn'2 hpos T hT (by positivity) fun v hv => ?_
  exact (sum_image_le_NAll hP (by omega) hy T hT).trans
    (sum_kS_le h hXm hP hp2 ht hlam hlam1 hy hv hyZ)

/-- `W^sh_y(u) ≤ 1` under (HBS) (`u > 0`, `y/u ≤ Z`). -/
lemma Wsh_le_one {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (ht : ∀ r, r.Prime → 0 < tw r) {y u : ℝ} (hy : X0m ≤ y) (hu : 0 < u) (hZ : y / u ≤ Z) :
    P.Wsh tw X0m y u ≤ 1 := by
  refine (P.Wsh_le_harmBlock ht h.X0m_pos.le hy hu).trans (h.harmBlock_le_one ?_)
  have : 2 * (y / (2 * u)) = y / u := by field_simp
  rw [this]; exact hZ

/-- **The block bound for the shifted kernels**: `∑_{y/m ∈ [u, 2u)} TV(C^{v,y}_m)/m ≤ 2.04`
(Corollary 5.17(a) with `W^sh ≤ 1` and `1 + ½λ₀A₀ ≤ 2.04`; no Saias bound). -/
theorem WS_le_block {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) {v y u : ℝ} (hy : X0m ≤ y) (hyZ : 2 * y / X0m ≤ Z)
    (hv : 0.85 * y ≤ v) (hu0 : 0 < u) :
    WS P H tw X0m v y u ≤ 2.04 := by
  have hX := h.X0m_pos
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  rcases lt_or_ge u (X0m / 2) with hlow | hhigh
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
    rw [this]; norm_num
  have hyZ' : y / u ≤ Z := by
    refine le_trans ?_ hyZ
    rw [div_le_div_iff₀ hu0 hX]; nlinarith
  have ha := cor_5_17_a_sh (lam0 := lam0) hP hp2 ht hlam hy hv hhigh
  have hε : ε ≤ 0.03 := by have := hP.eps_le; linarith
  have hHS := hordSumsB P h hXm hε hyZ'
  have hMS : ∀ m ∈ MS P y u, 2 ≤ m ∧ V m ≤ y / u := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    refine ⟨hm2, ?_⟩
    simp only [V]; rw [P.valN_iota]; exact P.mem_elems.mp he
  obtain ⟨hA0, -⟩ := hHS (MS P y u) hMS
  have hW0 := Wsh_le_one h ht hy hu0 hyZ'
  have hWm : ∀ m ∈ MS P y u, P.Wsh tw X0m y (u * V m) ≤ 1 := by
    intro m hm
    have hVm1 := KR.one_le_valN_label P m
    refine Wsh_le_one h ht hy (by positivity) ?_
    refine le_trans ?_ hyZ'
    apply div_le_div_of_nonneg_left (by linarith) hu0
    nlinarith
  have hsum : ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
      P.Wsh tw X0m y (u * V m) ≤ ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) :=
    Finset.sum_le_sum fun m hm => by
      have h0 : 0 ≤ (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) := by
        have := hV m; positivity
      have hW := hWm m hm
      have hWnn : 0 ≤ P.Wsh tw X0m y (u * V m) :=
        Finset.sum_nonneg fun e _ => div_nonneg (abs_nonneg _) (P.val_pos e).le
      nlinarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have : 1 / 2 * lam0 * ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
      P.Wsh tw X0m y (u * V m) ≤ 1 / 2 * lam0 * 2.0674 :=
    mul_le_mul_of_nonneg_left (hsum.trans hA0) (by positivity)
  nlinarith

/-- **The block transfer** (Proposition 5.18, proof, `∞`-norm part): for the levels of one block,
`∑_{x/n ∈ [u, 2u)} TV(𝒯_{n'→n} S^τ_{n'})/n ≤ 2.04 TV(S^τ_{n'})/n'` (Corollary 5.17(a) and
`W^sh ≤ 1`; no Saias bound). -/
theorem transferBlock {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hxZ : 2 * x / X0m ≤ Z) {n' : ℕ} (hn'2 : 2 ≤ n')
    (hpos : X0m ≤ posn P.labelVal x n') {u : ℝ} (hu0 : 0 < u) :
    ∑ n ∈ NW P x u, tauPart P H tw X0m x n' n / Vl P n ≤
      2.04 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') := by
  have hX := h.X0m_pos
  have hy := hpos
  set y := posn P.labelVal x n'
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  have hV1 := KR.one_le_valN_label P n'
  have hyx : y ≤ x := by
    have hx0 : 0 ≤ x := by
      by_contra hc; push_neg at hc
      have : y < 0 := div_neg_of_neg_of_pos hc (KR.valN_labelVal_pos P n')
      linarith
    exact div_le_self hx0 hV1
  have hyZ : 2 * y / X0m ≤ Z :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hX.le) hxZ
  have hT : ∀ n ∈ NW P x u, n ≠ 0 := fun n hn => ((mem_NW P hu0).mp hn).1
  refine transfer_gen hP hp2 hlam hn'2 hpos _ hT (by norm_num) fun v hv => ?_
  have hsub : ((NW P x u).filter (n' ∣ ·)).image (· / n') ⊆ NW P y u := by
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
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
    div_nonneg ENNReal.toReal_nonneg (hV m).le).trans ?_
  exact WS_le_block h hXm hP hp2 ht hlam hlam1 hy hyZ hv hu0

end KR

end
