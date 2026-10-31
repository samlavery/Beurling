module

public import RequestProject.Beurling.Model.E3Comp
public import RequestProject.Beurling.Model.Bookkeep
public import RequestProject.Beurling.Noise.MarginR1
public import RequestProject.Beurling.Noise.KptDefs

/-!
# The margin objects of §5.3 for the construction, and `R1Ident` from Proposition 5.38

For the constructed model `CM θ X₀ ω` (= `Mcl`), with the realised system `P(ω)`:

* `PhiA` : the non-absorbed cofactor count of the prime decided at relative slot `k + 1`;
* `compTerm`, `compDen` : the **compensator density** `c(y) = ∑_q H(s_q)⁻¹ ∑_{w} w⁻¹
  1[y/w ∈ box(s_q)] 1[τ_w < s_q, y ∉ 𝒜]` (the integrand of `Comp(I)` in §5.3, "`Comp` is the
  predictable compensator of `C⁽¹⁾`");
* `compSum_le` : **the compensator identification**: the partial sums of the conditional means
  of Queue6's truncated counts `X̃_q(I)` are at most `Comp(I) = ∫_I c`;
* `TpCont` : `T'_cont = 1 - ρ_det - ρ̄_A + R'` on `[X₀, ∞)`, `0` below, with
  `∫_a^b T'_cont = C(b) - C(max(a, X₀))`;
* `marginM` : the margin density `m = T'_cont - c`, which is `T̃' - K_pt ρ̃ - NT_pt` with
  `T̃' = T'_cont + K_𝒜 ρ̃` and `NT_pt := c - K_pt ρ̃ + K_𝒜 ρ̃` (`marginM_eq`; `ρ̃ = rhoT`,
  `K_pt = KR.Sharp.Kpt` at `P(ω)` with the decision times `twR`, `K_𝒜 = KAbs`);
* `bookkeeping_m` : **the §5.3 bookkeeping identity** `|ℓ_jit(I) - Comp(I) - ∫_I m| ≤ 2`;
* `r1Ident_of_margin` : `Margin.R1Ident` on every admissible window, a.s. on `Good(< b)`, from
  `PointwiseMargin m X₀` (Proposition 5.38, the §5 front).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed Queue6
  SlotModel AbsorbEmpty Target
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

open Classical in
variable (θ X₀) in
/-- `Φᴬ_k(ω, t) = #{m ∈ cofP k : α ≤ m t < β, m t ∉ 𝒜}` for `t ≥ X₀⁻` (`0` below `X₀⁻`): the
non-absorbed cofactor count, absorption read from the value `m t` and the latest prime `t`. -/
noncomputable def PhiA (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' e : PIdx X₀ →₀ ℕ, if e ∈ cofP θ X₀ k p.1 ∧
    α ≤ eval (DD θ X₀ p.1) e * p.2 ∧ eval (DD θ X₀ p.1) e * p.2 < β ∧
    ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ p.1) e * p.2) ∧
      p.2 < absorbY X₀ (eval (DD θ X₀ p.1) e * p.2)) then 1 else 0 else 0


section Meas

variable (hc : Cond θ X₀)
include hc

lemma PhiA_jmeas (k : ℕ) (α β : ℝ) (S : Set JitterΩ) (hS : MeasurableSet[jitterFiltration k] S) :
    RankFull.JMeas (jitterFiltration k) (fun p => S.indicator 1 p.1 * PhiA θ X₀ k α β p) := by
  classical
  unfold RankFull.JMeas
  letI mP : MeasurableSpace (JitterΩ × ℝ) :=
    @Prod.instMeasurableSpace JitterΩ ℝ (jitterFiltration k) _
  have hfst : @Measurable _ _ mP (jitterFiltration k) Prod.fst :=
    @measurable_fst _ _ (jitterFiltration k) _
  have hsnd : @Measurable _ _ mP _ Prod.snd := @measurable_snd _ _ (jitterFiltration k) _
  refine Measurable.mul (m := mP) ?_ ?_
  · exact (measurable_const.indicator hS).comp hfst
  · unfold PhiA
    refine Measurable.ite (m := mP) (measurableSet_le measurable_const hsnd) ?_ measurable_const
    refine Measurable.ennreal_tsum (mα := mP) fun e => ?_
    by_cases he : ∀ j, e (Sum.inr j) ≠ 0 → j < k
    · have hev : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ => eval (DD θ X₀ p.1) e * p.2 :=
        ((eval_meas_lt hc e he).comp hfst).mul hsnd
      have hy : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ =>
          absorbY X₀ (eval (DD θ X₀ p.1) e * p.2) :=
        (absorbY_monotone hc.hX).measurable.comp hev
      have hl : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ =>
          Real.log (eval (DD θ X₀ p.1) e * p.2) := Real.measurable_log.comp hev
      have hset : @MeasurableSet _ mP {p : JitterΩ × ℝ | p.1 ∈ {ω | e ∈ cofP θ X₀ k ω} ∧
          α ≤ eval (DD θ X₀ p.1) e * p.2 ∧ eval (DD θ X₀ p.1) e * p.2 < β ∧
          ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ p.1) e * p.2) ∧
            p.2 < absorbY X₀ (eval (DD θ X₀ p.1) e * p.2))} :=
        (hfst (cofP_meas hc k e)).inter
          ((measurableSet_le measurable_const hev).inter
            ((measurableSet_lt hev measurable_const).inter
              ((measurableSet_le measurable_const hl).inter (measurableSet_lt hsnd hy)).compl))
      exact Measurable.ite (m := mP) hset measurable_const measurable_const
    · have : (fun p : JitterΩ × ℝ => if e ∈ cofP θ X₀ k p.1 ∧ α ≤ eval (DD θ X₀ p.1) e * p.2 ∧
          eval (DD θ X₀ p.1) e * p.2 < β ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ p.1) e * p.2) ∧
            p.2 < absorbY X₀ (eval (DD θ X₀ p.1) e * p.2)) then (1 : ℝ≥0∞) else 0) =
          fun _ => 0 := by
        funext p
        rw [if_neg]
        rintro ⟨⟨-, -, h⟩, -⟩; exact he h
      rw [this]; exact measurable_const

end Meas

section Dom

variable (hc : Cond θ X₀)
include hc

/-- **`X̃_q(I) ≤ Φᴬ_k(ω, q)`** on the good stage: every non-absorbed composite counted by
`X_q(I)` is `q m` with a cofactor `m ∈ cofP k`, and `q m ∉ 𝒜`. -/
theorem Xt_le_PhiA (m : ℕ) (a b : ℤ) (k : ℕ) {ω : JitterΩ} (hω : ω ∈ stageGood θ X₀ k) :
    ENNReal.ofReal (Xt θ X₀ m a b k ω) ≤
      (lawA θ X₀ k).indicator (fun ω => PhiA θ X₀ k a b (ω, valF θ X₀ k ω)) ω := by
  classical
  set Xs := xsetP θ X₀ (a : ℝ) (b : ℝ) k (· = 1) ω with hXs
  have hX3 : Xt θ X₀ m a b k ω ≤ (Xs.ncard : ℝ) := by
    unfold Xt
    refine (min_le_left _ _).trans (le_of_eq ?_)
    unfold Xcount xset
    exact_mod_cast ncard_xset (θ := θ) (X₀ := X₀) a b k (· = 1) ω
  have hval : valF θ X₀ k ω = (DD θ X₀ ω).v k := rfl
  have hq0 : 0 < valF θ X₀ k ω := valF_pos hc k ω
  set S : Set (PIdx X₀ →₀ ℕ) := {e' | e' ∈ cofP θ X₀ k ω ∧
    (a : ℝ) ≤ eval (DD θ X₀ ω) e' * valF θ X₀ k ω ∧ eval (DD θ X₀ ω) e' * valF θ X₀ k ω < b ∧
    ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e' * valF θ X₀ k ω) ∧
      valF θ X₀ k ω < absorbY X₀ (eval (DD θ X₀ ω) e' * valF θ X₀ k ω))}
  have hSfin : S.Finite := by
    refine (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
      (b / valF θ X₀ k ω)).subset fun e' he' => ?_
    refine ⟨he'.1.1, pval_gt_one hc he'.1.1, ?_⟩
    rw [le_div_iff₀ hq0]; exact he'.2.2.1.le
  by_cases hne : Xs.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty] at hX3
    push_cast at hX3
    rw [ENNReal.ofReal_eq_zero.mpr hX3]; exact zero_le
  obtain ⟨e0, he0⟩ := hne
  have hplaced : placedAt (CM θ X₀ ω) k := by
    have h1 := he0.1 k (by rw [he0.2.2.2.2.2.2.2]; norm_num)
    exact h1
  have hA : ω ∈ lawA θ X₀ k := ⟨hplaced, hω⟩
  rw [indicator_of_mem hA]
  have hPhi : PhiA θ X₀ k a b (ω, valF θ X₀ k ω) = (S.ncard : ℝ≥0∞) := by
    unfold PhiA
    rw [if_pos (valF_ge_Xm hc k ω)]
    rw [← tsum_ite_eq_ncard hSfin]
    exact tsum_congr fun e => by
      by_cases h : e ∈ S
      · rw [if_pos h]; exact if_pos h
      · rw [if_neg h]; exact if_neg h
  rw [hPhi]
  -- the injection `e ↦ e - q`
  set f : (PIdx X₀ →₀ ℕ) → (PIdx X₀ →₀ ℕ) := fun e => e - Finsupp.single (Sum.inr k) 1
  have hsplit : ∀ e ∈ Xs, e = f e + Finsupp.single (Sum.inr k) 1 := by
    intro e he
    have hk : e (Sum.inr k) = 1 := he.2.2.2.2.2.2.2
    ext i
    simp only [f, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hi : i = Sum.inr k
    · subst hi; simp [hk]
    · simp [Finsupp.single_apply, Ne.symm hi]
  have hmaps : Set.MapsTo f Xs S := by
    intro e he
    have hk : e (Sum.inr k) = 1 := he.2.2.2.2.2.2.2
    have heq := hsplit e he
    have hev : eval (DD θ X₀ ω) e = eval (DD θ X₀ ω) (f e) * valF θ X₀ k ω := by
      conv_lhs => rw [heq]
      rw [eval_add_single, pow_one]; rfl
    refine ⟨⟨fun j hj => he.1 j ?_, ?_, fun j hj => ?_⟩, ?_, ?_⟩
    · intro h0; apply hj
      simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
    · intro h0
      have hs := he.2.1
      rw [heq, h0, zero_add, Finsupp.sum_single_index rfl] at hs
      omega
    · have hj' : e (Sum.inr j) ≠ 0 := by
        intro h0; apply hj
        simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
      have hle := latP_le hj'
      rw [he.2.2.2.2.2.2.1] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · subst h
        exfalso; apply hj
        simp [f, hk]
    · rw [← hev]; exact he.2.2.1
    · refine ⟨by rw [← hev]; exact he.2.2.2.1, ?_⟩
      rw [← hev]
      have h6 := he.2.2.2.2.2.1
      rwa [he.2.2.2.2.2.2.1] at h6
  have hinj : Set.InjOn f Xs := by
    intro e1 h1 e2 h2 h12
    rw [hsplit e1 h1, hsplit e2 h2, h12]
  have hcard := Set.ncard_le_ncard_of_injOn f hmaps hinj hSfin
  calc ENNReal.ofReal (Xt θ X₀ m a b k ω) ≤ ENNReal.ofReal (Xs.ncard : ℝ) :=
        ENNReal.ofReal_le_ofReal hX3
    _ = (Xs.ncard : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast]
    _ ≤ (S.ncard : ℝ≥0∞) := by exact_mod_cast hcard

end Dom

lemma PhiA_le_PhiBar (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) :
    PhiA θ X₀ k α β p ≤ PhiBar θ X₀ α β p := by
  classical
  unfold PhiA PhiBar
  split_ifs with h
  · refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases h1 : e ∈ cofP θ X₀ k p.1 ∧ α ≤ eval (DD θ X₀ p.1) e * p.2 ∧
        eval (DD θ X₀ p.1) e * p.2 < β ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ p.1) e * p.2) ∧
          p.2 < absorbY X₀ (eval (DD θ X₀ p.1) e * p.2))
    · rw [if_pos h1, if_pos ⟨⟨h1.1.1, h1.1.2.1⟩, h1.2.1, h1.2.2.1⟩]
    · rw [if_neg h1]; exact zero_le
  · exact le_rfl


section Bar

variable (hc : Cond θ X₀)
include hc

lemma boxMean_PhiA_ne_top (hev : Even X₀) {a b : ℝ} (hab : a ≤ b) (k : ℕ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiA θ X₀ k a b) ω ≠ ∞ := by
  unfold boxMean
  by_cases hA : ω ∈ (constructionLaw hc hev).A k
  · rw [indicator_of_mem hA]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := (b - a) *
        ∑ e ∈ (cof_finite hc b ω).toFinset, 1 / eval (DD θ X₀ ω) e)) ?_)
    calc ∫⁻ t in RankFull.box _ _, PhiA θ X₀ k a b (ω, t)
        ≤ ∫⁻ t, PhiA θ X₀ k a b (ω, t) := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ t, PhiBar θ X₀ a b (ω, t) := lintegral_mono fun t => PhiA_le_PhiBar k a b _
      _ ≤ _ := lintegral_PhiBar_le hc hab ω
  · rw [indicator_of_notMem hA]; exact ENNReal.zero_ne_top

end Bar

/-! ### The compensator density -/

open Classical in
variable (θ X₀) in
/-- The contribution of the prime decided at relative slot `k + 1` to the compensator density:
`c_k(y) = 1_{A_k} H_k⁻¹ ∑_{w ∈ cofP k} w⁻¹ 1[y/w ∈ box_k] 1[y/w ≥ X₀⁻, y ∉ 𝒜 via y/w]`. -/
noncomputable def compTerm (k : ℕ) (ω : JitterΩ) (y : ℝ) : ℝ≥0∞ :=
  (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
    ∑' w : PIdx X₀ →₀ ℕ, if w ∈ cofP θ X₀ k ω ∧ Xm X₀ ≤ y / eval (DD θ X₀ ω) w ∧
      ¬ (10 ^ 7 ≤ Real.log y ∧ y / eval (DD θ X₀ ω) w < absorbY X₀ y) then
      (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (y / eval (DD θ X₀ ω) w) *
        ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0) ω

variable (θ X₀) in
/-- **The compensator density** `c(y) = ∑_k c_k(y)` of `Comp(I) = ∫_I c` (§5.3). -/
noncomputable def compDen (ω : JitterΩ) (y : ℝ) : ℝ≥0∞ := ∑' k, compTerm θ X₀ k ω y

/-- `∫ g(e t) dt = e⁻¹ ∫ g` for `e > 0`. -/
lemma lintegral_comp_mul {e : ℝ} (he : 0 < e) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g (e * t) = ENNReal.ofReal e⁻¹ * ∫⁻ y, g y := by
  have hmap := Real.map_volume_mul_left he.ne'
  have hmeas : Measurable fun t : ℝ => e * t := measurable_const.mul measurable_id
  rw [← lintegral_map hg hmeas, hmap, lintegral_smul_measure, abs_of_pos (inv_pos.mpr he)]
  rfl

section Comp

variable (hc : Cond θ X₀)
include hc

lemma compTerm_meas (k : ℕ) (ω : JitterΩ) : Measurable (compTerm θ X₀ k ω) := by
  classical
  unfold compTerm
  by_cases hA : ω ∈ lawA θ X₀ k
  · simp only [indicator_of_mem hA]
    refine measurable_const.mul (Measurable.ennreal_tsum fun w => ?_)
    have hd : Measurable fun y : ℝ => y / eval (DD θ X₀ ω) w := measurable_id.div_const _
    refine Measurable.ite ?_ ((measurable_one.indicator measurableSet_Ico).comp hd |>.mul
      measurable_const) measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl)
  · simp only [indicator_of_notMem hA]; exact measurable_const

/-- **The (F2) bound of one slot is its compensator mass on `[a, b)`**:
`G_k ≤ ∫_{[a,b)} c_k` (substituting `y = w t`). -/
theorem boxMean_le_compTerm (hev : Even X₀) (k : ℕ) (a b : ℝ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiA θ X₀ k a b) ω ≤
      ∫⁻ y in Ico a b, compTerm θ X₀ k ω y := by
  classical
  unfold boxMean compTerm
  by_cases hA : ω ∈ lawA θ X₀ k
  swap
  · show (lawA θ X₀ k).indicator _ ω ≤ _
    rw [indicator_of_notMem hA]; exact zero_le
  show (lawA θ X₀ k).indicator _ ω ≤ _
  simp only [indicator_of_mem hA]
  set H := HF θ X₀ k ω
  set B := RankFull.box (slotF θ X₀ k ω) H
  have hB : MeasurableSet B := measurableSet_Ico
  rw [lintegral_const_mul _ (by
    refine Measurable.ennreal_tsum fun w => ?_
    have hd : Measurable fun y : ℝ => y / eval (DD θ X₀ ω) w := measurable_id.div_const _
    refine Measurable.ite ?_ ((measurable_one.indicator hB).comp hd |>.mul measurable_const)
      measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl))]
  refine mul_le_mul_right ?_ _
  -- expand both sides over the cofactors
  have hL : ∫⁻ t in B, PhiA θ X₀ k a b (ω, t) = ∑' w : PIdx X₀ →₀ ℕ, ∫⁻ t, B.indicator
      (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧ a ≤ eval (DD θ X₀ ω) w * t ∧
        eval (DD θ X₀ ω) w * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
          t < absorbY X₀ (eval (DD θ X₀ ω) w * t))) then (1 : ℝ≥0∞) else 0) t := by
    rw [← lintegral_indicator hB, ← lintegral_tsum]
    · refine lintegral_congr fun t => ?_
      unfold PhiA
      by_cases ht : t ∈ B
      · simp only [indicator_of_mem ht]
        by_cases hX : Xm X₀ ≤ t
        · rw [if_pos hX]
          exact tsum_congr fun w => by
            by_cases h : w ∈ cofP θ X₀ k ω ∧ a ≤ eval (DD θ X₀ ω) w * t ∧
                eval (DD θ X₀ ω) w * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
                  t < absorbY X₀ (eval (DD θ X₀ ω) w * t))
            · rw [if_pos h, if_pos ⟨hX, h⟩]
            · rw [if_neg h, if_neg fun h' => h h'.2]
        · rw [if_neg hX]
          symm; exact ENNReal.tsum_eq_zero.mpr fun w => if_neg fun h' => hX h'.1
      · simp only [indicator_of_notMem ht, tsum_zero]
    · intro w
      refine (Measurable.indicator ?_ hB).aemeasurable
      have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) w * t := measurable_const.mul measurable_id
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_le measurable_const measurable_id).inter ((MeasurableSet.const _).inter
        ((measurableSet_le measurable_const hm).inter ((measurableSet_lt hm measurable_const).inter
          ((measurableSet_le measurable_const (Real.measurable_log.comp hm)).inter
            (measurableSet_lt measurable_id ((absorbY_monotone hc.hX).measurable.comp hm))).compl)))
  change ∫⁻ t in B, PhiA θ X₀ k a b (ω, t) ≤ _
  rw [hL, lintegral_tsum]
  swap
  · intro w
    have hd : Measurable fun y : ℝ => y / eval (DD θ X₀ ω) w := measurable_id.div_const _
    refine (Measurable.ite ?_ ((measurable_one.indicator hB).comp hd |>.mul measurable_const)
      measurable_const).aemeasurable
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl)
  refine ENNReal.tsum_le_tsum fun w => ?_
  by_cases hw : w ∈ cofP θ X₀ k ω
  swap
  · have : (fun t => B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧
        a ≤ eval (DD θ X₀ ω) w * t ∧ eval (DD θ X₀ ω) w * t < b ∧
        ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
          t < absorbY X₀ (eval (DD θ X₀ ω) w * t))) then (1 : ℝ≥0∞) else 0) t) = 0 := by
      funext t
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, if_neg fun h => hw h.2.1]; rfl
      · rw [indicator_of_notMem ht]; rfl
    rw [this, lintegral_zero_fun]; exact zero_le
  set e := eval (DD θ X₀ ω) w with he
  have he0 : 0 < e := eval_pos hc hw.1
  set h : ℝ → ℝ≥0∞ := (Ico a b).indicator fun y => if Xm X₀ ≤ y / e ∧
    ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y) then B.indicator 1 (y / e) else 0 with hh
  have hhm : Measurable h := by
    have hd : Measurable fun y : ℝ => y / e := measurable_id.div_const _
    refine Measurable.indicator (Measurable.ite ?_ ((measurable_one.indicator hB).comp hd)
      measurable_const) measurableSet_Ico
    exact (measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl
  have hpt : ∀ t, B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧
      a ≤ e * t ∧ e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))) then
        (1 : ℝ≥0∞) else 0) t = h (e * t) := by
    intro t
    have hdiv : e * t / e = t := by field_simp
    rw [hh]
    by_cases hI : e * t ∈ Ico a b
    · rw [indicator_of_mem hI]
      simp only [hdiv]
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        by_cases hc' : Xm X₀ ≤ t ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))
        · rw [if_pos ⟨hc'.1, hw, hI.1, hI.2, hc'.2⟩, if_pos hc']; rfl
        · rw [if_neg fun h' => hc' ⟨h'.1, h'.2.2.2.2⟩, if_neg hc']
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]; split_ifs <;> rfl
    · rw [indicator_of_notMem hI]
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, if_neg fun h' => hI ⟨h'.2.2.1, h'.2.2.2.1⟩]
      · rw [indicator_of_notMem ht]
  calc ∫⁻ t, B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧ a ≤ e * t ∧
        e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))) then
          (1 : ℝ≥0∞) else 0) t
      = ∫⁻ t, h (e * t) := lintegral_congr hpt
    _ = ENNReal.ofReal e⁻¹ * ∫⁻ y, h y := lintegral_comp_mul he0 hhm
    _ = ∫⁻ y in Ico a b, (if w ∈ cofP θ X₀ k ω ∧ Xm X₀ ≤ y / e ∧
          ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y) then
          B.indicator 1 (y / e) * ENNReal.ofReal e⁻¹ else 0) := by
        rw [← lintegral_const_mul _ hhm, hh, ← lintegral_indicator measurableSet_Ico]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ Ico a b
        · rw [indicator_of_mem hy, indicator_of_mem hy]
          by_cases hc' : Xm X₀ ≤ y / e ∧ ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y)
          · rw [if_pos hc', if_pos ⟨hw, hc'⟩, mul_comm]
          · rw [if_neg hc', if_neg fun h' => hc' h'.2, mul_zero]
        · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
    _ ≤ _ := le_rfl

set_option maxHeartbeats 4000000 in
/-- **The compensator density is bounded below the window's top**: for `y ≤ b`,
`c(y) ≤ 2 ∑_{1 < m ≤ b/X₀⁻} 1/m` ((F1), `law_slots`). -/
theorem compDen_le (hev : Even X₀) (ω : JitterΩ) {y b : ℝ} (hyb : y ≤ b) :
    compDen θ X₀ ω y ≤ 2 * ∑ w ∈ (cof_finite hc b ω).toFinset,
      ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ := by
  classical
  have hXm := Queue6.Xm_pos hc
  set F := (cof_finite hc b ω).toFinset
  set g : (PIdx X₀ →₀ ℕ) → ℝ≥0∞ := fun w => if (Live (DD θ X₀ ω) w ∧ w ≠ 0) ∧
    Xm X₀ ≤ y / eval (DD θ X₀ ω) w then 2 * ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0
  have hstep : ∀ k, compTerm θ X₀ k ω y ≤ ∑' w : PIdx X₀ →₀ ℕ, (lawA θ X₀ k).indicator (fun ω =>
      ENNReal.ofReal (HF θ X₀ k ω)⁻¹ * (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1
        (y / eval (DD θ X₀ ω) w)) ω * (if (Live (DD θ X₀ ω) w ∧ w ≠ 0) ∧
          Xm X₀ ≤ y / eval (DD θ X₀ ω) w then ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0) := by
    intro k
    unfold compTerm
    by_cases hA : ω ∈ lawA θ X₀ k
    · simp only [indicator_of_mem hA]
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun w => ?_
      by_cases h1 : w ∈ cofP θ X₀ k ω ∧ Xm X₀ ≤ y / eval (DD θ X₀ ω) w ∧
          ¬ (10 ^ 7 ≤ Real.log y ∧ y / eval (DD θ X₀ ω) w < absorbY X₀ y)
      · rw [if_pos h1, if_pos ⟨⟨h1.1.1, h1.1.2.1⟩, h1.2.1⟩, mul_assoc]
      · rw [if_neg h1, mul_zero]; exact zero_le
    · simp only [indicator_of_notMem hA, zero_mul, tsum_zero]; exact le_rfl
  have hsum : compDen θ X₀ ω y ≤ ∑' w, g w := by
    unfold compDen
    refine (ENNReal.tsum_le_tsum hstep).trans ?_
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [ENNReal.tsum_mul_right]
    simp only [g]
    split_ifs with h
    · exact mul_le_mul_left (law_slots hc hev ω _) _
    · rw [mul_zero]
  refine hsum.trans ?_
  rw [tsum_eq_sum (s := F) (fun w hw => by
    simp only [g]
    refine if_neg fun h => ?_
    rw [Set.Finite.mem_toFinset] at hw
    apply hw
    refine ⟨h.1, ?_⟩
    have he := eval_pos hc h.1.1
    rw [le_div_iff₀ he] at h
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h.2])]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  show (if (Live (DD θ X₀ ω) w ∧ w ≠ 0) ∧ Xm X₀ ≤ y / eval (DD θ X₀ ω) w then
    2 * ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹ else 0) ≤ 2 * ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  by_cases h : (Live (DD θ X₀ ω) w ∧ w ≠ 0) ∧ Xm X₀ ≤ y / eval (DD θ X₀ ω) w
  · rw [if_pos h]
  · rw [if_neg h]; exact zero_le

/-- **The compensator identification** (§5.3, "`Comp` is the predictable compensator of
`C⁽¹⁾`"): a.s., every partial sum of the conditional means of Queue6's truncated counts
`X̃_q(I)` is at most `Comp(I) = ∫_I c`. -/
theorem compSum_le (hev : Even X₀) (m : ℕ) {a b : ℤ} (hab : a ≤ b) :
    ∀ᵐ ω ∂jitterMeasure, ∀ n,
      ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω ≤
        ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := by
  classical
  set J := constructionLaw hc hev with hJ
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hMq : 0 ≤ 2 * Mq X₀ (uS X₀ m) := by
    have := QueueBound.one_le_capM1 hX0 hc.hX (Queue6.uq_ge (X₀ := X₀) (u := uS X₀ m))
    unfold Mq; linarith
  set C := 2 * Mq X₀ (uS X₀ m)
  have hk : ∀ k, jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k] ≤ᵐ[jitterMeasure]
      fun ω => min C (boxMean J k (PhiA θ X₀ k a b) ω).toReal := by
    intro k
    have h0 : ∀ ω, 0 ≤ Xt θ X₀ m a b k ω := fun ω => le_min (Nat.cast_nonneg _) hMq
    have hC : ∀ ω, Xt θ X₀ m a b k ω ≤ C := fun ω => min_le_right _ _
    have hm : Measurable (Xt θ X₀ m a b k) :=
      (((xcount_adapted hc a b k 1).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    have hfΦ : ∀ᵐ ω ∂jitterMeasure, ENNReal.ofReal (Xt θ X₀ m a b k ω) ≤
        (J.A k).indicator (fun ω => PhiA θ X₀ k a b (ω, J.q k ω)) ω := by
      filter_upwards [ae_stageGood hc] with ω hω
      exact Xt_le_PhiA hc m a b k (hω k)
    exact condExp_le_boxMean J k hMq h0 hC hm (fun S hS => PhiA_jmeas hc k a b S hS) hfΦ
      (fun ω => boxMean_PhiA_ne_top hc hev hab' k ω)
  filter_upwards [ae_all_iff.mpr hk] with ω hω n
  have hfin : ∀ k, boxMean J k (PhiA θ X₀ k a b) ω ≠ ∞ := fun k =>
    boxMean_PhiA_ne_top hc hev hab' k ω
  set K := 2 * ∑ w ∈ (cof_finite hc (b : ℝ) ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  have hden : ∀ y ∈ Ico (a : ℝ) b, compDen θ X₀ ω y ≤ K := fun y hy =>
    compDen_le hc hev ω hy.2.le
  have hint_fin : ∫⁻ y in Ico (a : ℝ) b, compDen θ X₀ ω y ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ico (a : ℝ) b, K) ?_
      (setLIntegral_mono measurable_const (fun y hy => hden y hy))
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top hK (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hdm : Measurable (compDen θ X₀ ω) :=
    Measurable.ennreal_tsum fun k => compTerm_meas hc k ω
  calc ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
      ≤ ∑ k ∈ Finset.range n, (boxMean J k (PhiA θ X₀ k a b) ω).toReal :=
        Finset.sum_le_sum fun k _ => (hω k).trans (min_le_right _ _)
    _ = (∑ k ∈ Finset.range n, boxMean J k (PhiA θ X₀ k a b) ω).toReal :=
        (ENNReal.toReal_sum fun k _ => hfin k).symm
    _ ≤ (∫⁻ y in Ico (a : ℝ) b, compDen θ X₀ ω y).toReal := by
        refine ENNReal.toReal_mono hint_fin ?_
        refine (ENNReal.sum_le_tsum _).trans ?_
        unfold compDen
        rw [lintegral_tsum fun k => (compTerm_meas hc k ω).aemeasurable]
        exact ENNReal.tsum_le_tsum fun k => boxMean_le_compTerm hc hev k a b ω
    _ = ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := by
        rw [intervalIntegral.integral_of_le hab', ← setIntegral_congr_set Ico_ae_eq_Ioc,
          integral_toReal hdm.aemeasurable.restrict]
        refine (ae_restrict_iff' measurableSet_Ico).mpr (Filter.Eventually.of_forall
          fun y hy => lt_of_le_of_lt (hden y hy) (lt_top_iff_ne_top.mpr hK))

end Comp
/-! ### `T'_cont` and the margin density -/

variable (θ X₀) in
/-- `T'_cont = 1 - ρ_det - ρ̄_A + R'` on `[X₀, ∞)` (the density of the continuous part `C` of the
target (6)), `0` below `X₀`. -/
noncomputable def TpCont (ω : JitterΩ) (y : ℝ) : ℝ :=
  if (X₀ : ℝ) ≤ y then 1 - rhoDet X₀ (kappaParam X₀) y -
    absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) y +
    deriv (Oscillation.osc θ (alphaD θ X₀ (DF θ X₀ ω)) (gammaD θ X₀ (DF θ X₀ ω)) (switchOn X₀)) y
  else 0

variable (θ X₀) in
/-- **The pointwise margin density** `m = T'_cont - c` (§5.3: `m = T̃' - K_pt ρ̃ - NT_pt`,
`marginM_eq`). -/
noncomputable def marginM (ω : JitterΩ) (y : ℝ) : ℝ := TpCont θ X₀ ω y - (compDen θ X₀ ω y).toReal

section Tp

variable (hc : Cond θ X₀)
include hc

/-- **`∫_a^b T'_cont = C(b) - C(max(a, X₀))`** (and `T'_cont` is interval integrable). -/
theorem integral_TpCont (ω : JitterΩ) {a b : ℝ} (hab : a ≤ b) (hb : (X₀ : ℝ) ≤ b) :
    IntervalIntegrable (TpCont θ X₀ ω) volume a b ∧
      ∫ y in a..b, TpCont θ X₀ ω y =
        contD θ X₀ (DF θ X₀ ω) b - contD θ X₀ (DF θ X₀ ω) (max a X₀) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  have hb2 : 0 < thetaB θ := thetaB_pos (by linarith [hc.hθ.1])
  set D := DF θ X₀ ω
  have hD : LocFinD D := locFinD_DM hX (fun j => clamp01_mem (ω j)) _
  have hA := absSet_locFin (X₀ := X₀) hD
  set R := Oscillation.osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)
  set g : ℝ → ℝ := fun y => 1 - rhoDet X₀ (kappaParam X₀) y -
    absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) y + deriv R y
  set a' := max a (X₀ : ℝ)
  have ha'b : a' ≤ b := max_le hab hb
  have hXa' : (X₀ : ℝ) ≤ a' := le_max_right _ _
  -- the pieces of `g` on `[a', b]`
  have hρ : IntervalIntegrable (rhoDet X₀ (kappaParam X₀)) volume a' b :=
    (intervalIntegrable_rhoDet X₀ hκ0 hX1n hb).mono_set (by
      rw [uIcc_of_le ha'b, uIcc_of_le hb]; exact Icc_subset_Icc hXa' le_rfl)
  have hρA : IntervalIntegrable (absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ)) volume a' b :=
    (intervalIntegrable_absorbedDensityCap _ hA hb2 hX1 hb).mono_set (by
      rw [uIcc_of_le ha'b, uIcc_of_le hb]; exact Icc_subset_Icc hXa' le_rfl)
  have hγ := gammaD_range (θ := θ) hX D
  have hdR : ∀ x ∈ uIcc a' b, DifferentiableAt ℝ R x := fun x hx => by
    rw [uIcc_of_le ha'b] at hx
    exact (hasDerivAt_osc _ _ hX1.le (by linarith [hx.1])).differentiableAt
  have hRint : IntervalIntegrable (deriv R) volume a' b := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
      (measurable_deriv R).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le ha'b] at hx
    show ‖deriv R x‖ ≤ 1
    rw [Real.norm_eq_abs]
    refine (abs_deriv_osc_le hc.hθ hX hγ (by linarith [hx.1])).trans ?_
    have : (10 ^ 8 : ℝ) ≤ Real.log x :=
      hX.trans (Real.log_le_log (by linarith) (by linarith [hx.1]))
    rw [div_le_one (by linarith)]; linarith
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a' b := intervalIntegrable_const
  have hgint : IntervalIntegrable g volume a' b :=
    ((hc1.sub hρ).sub hρA).add hRint
  have hEq : EqOn (TpCont θ X₀ ω) g (uIcc a' b) := by
    intro y hy
    rw [uIcc_of_le ha'b] at hy
    simp only [TpCont, if_pos (hXa'.trans hy.1), g]
    rfl
  have hint2 : IntervalIntegrable (TpCont θ X₀ ω) volume a' b :=
    hgint.congr (hEq.symm.mono Set.uIoc_subset_uIcc)
  -- below `X₀`, `T'_cont = 0`
  have hzero : ∀ y : ℝ, y < (X₀ : ℝ) → TpCont θ X₀ ω y = 0 := fun y hy => by
    simp only [TpCont, if_neg (not_le.mpr hy)]
  have hae : ∀ᵐ y ∂(volume.restrict (uIoc a a')), TpCont θ X₀ ω y = 0 := by
    have hns : ∀ᵐ y ∂(volume.restrict (uIoc a a')), y ≠ (X₀ : ℝ) :=
      ae_restrict_of_ae (by
        rw [Filter.eventually_iff, mem_ae_iff]
        rw [show {x : ℝ | x ≠ (X₀ : ℝ)}ᶜ = {(X₀ : ℝ)} by ext x; simp]
        exact measure_singleton _)
    refine ((ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall
      fun y hy => hy)).mp (hns.mono fun y hy hyI => ?_)
    rcases le_or_gt (X₀ : ℝ) a with ha | ha
    · have : a' = a := max_eq_left ha
      rw [this, uIoc_of_le le_rfl, Ioc_self] at hyI; exact absurd hyI (Set.notMem_empty y)
    · have : a' = X₀ := max_eq_right ha.le
      rw [this, uIoc_of_le ha.le] at hyI
      exact hzero y (lt_of_le_of_ne hyI.2 hy)
  have hint1 : IntervalIntegrable (TpCont θ X₀ ω) volume a a' := by
    have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a a' := intervalIntegrable_const
    rw [intervalIntegrable_iff] at h0 ⊢
    exact h0.congr_fun_ae (Filter.EventuallyEq.symm (hae.mono fun y hy => hy))
  have haa : a ≤ a' := le_max_left _ _
  refine ⟨hint1.trans hint2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h1 : ∫ y in a..a', TpCont θ X₀ ω y = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      ((ae_restrict_iff' measurableSet_uIoc).mp hae)]
    simp
  have h2 : ∫ y in a'..b, TpCont θ X₀ ω y = ∫ y in a'..b, g y :=
    intervalIntegral.integral_congr hEq
  rw [h1, h2, zero_add]
  have hFTC := intervalIntegral.integral_deriv_eq_sub hdR hRint
  have hsplit : ∫ y in a'..b, g y = (b - a') - (∫ y in a'..b, rhoDet X₀ (kappaParam X₀) y) -
      (∫ y in a'..b, absorbedDensityCap (thetaB θ) (absSet X₀ D) (uA θ) y) +
      ∫ y in a'..b, deriv R y := by
    simp only [g]
    rw [intervalIntegral.integral_add ((hc1.sub hρ).sub hρA) hRint,
      intervalIntegral.integral_sub (hc1.sub hρ) hρA,
      intervalIntegral.integral_sub hc1 hρ, intervalIntegral.integral_const]
    simp
  rw [hsplit, hFTC]
  unfold contD
  rw [show uA θ = (fun n => solveU (thetaB θ) n) from rfl]
  rw [contPart_sub (fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy)
    (fun y hy => intervalIntegrable_absorbedDensityCap _ hA hb2 hX1 hy) hXa' ha'b]

end Tp

/-! ### The §5 objects at the realised system -/

variable (θ X₀) in
/-- `ρ̃(y) = ∑_q H(s_q)⁻¹ 1[y ∈ box(s_q)]`, the jitter-smoothed slot density of the decided
primes (§5.1). -/
noncomputable def rhoT (ω : JitterΩ) (y : ℝ) : ℝ :=
  (∑' k, (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
    (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 y) ω).toReal

variable (θ X₀) in
/-- The realised system `P(ω)`. -/
noncomputable abbrev PR (ω : JitterΩ) : BeurlingSystem :=
  realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)

open Classical in
variable (θ X₀) in
/-- The decision times of the prime labels of `P(ω)` (labels are the rational primes `r`, the
`r`-th prime of `P(ω)` having index `Nat.count Nat.Prime r`): `t(p) = p` for a rational prime,
`s_q` for the prime decided at relative slot `k + 1`. -/
noncomputable def twR (ω : JitterΩ) (r : ℕ) : ℝ :=
  if r.Prime then
    match realisedSrc (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (Nat.count Nat.Prime r) with
    | none => (PR θ X₀ ω).p (Nat.count Nat.Prime r)
    | some k => slotF θ X₀ k ω
  else 0

variable (θ X₀) in
/-- `K_pt` of §5 (`KR.Sharp.Kpt`) at the realised system, with the decision times `twR`. -/
noncomputable def KptR (ω : JitterΩ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  KR.Sharp.Kpt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) g y

open Classical in
variable (θ X₀) in
/-- `K_𝒜`: the part of `K_pt` whose landing is absorbed (`log y ≥ L_*`, `y/w < y(y)`). -/
noncomputable def KAbsR (ω : JitterΩ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ w ∈ (KR.NAll (PR θ X₀ ω) y (Xm X₀)).filter (2 ≤ ·),
    if (∀ p ∈ w.primeFactors, twR θ X₀ ω p * KR.Vl (PR θ X₀ ω) w < y) ∧
      (10 ^ 7 ≤ Real.log y ∧ y / KR.Vl (PR θ X₀ ω) w < absorbY X₀ y) then
      g (y / KR.Vl (PR θ X₀ ω) w) / KR.Vl (PR θ X₀ ω) w else 0

variable (θ X₀) in
/-- `NT_pt := c - K_pt ρ̃ + K_𝒜 ρ̃` (§5.3: `NT` replaces the slot filter `s_q > τ_w` by the
landing filter `y/w > τ_w` on the non-absorbed part). -/
noncomputable def NTpt (ω : JitterΩ) (y : ℝ) : ℝ :=
  (compDen θ X₀ ω y).toReal - KptR θ X₀ ω (rhoT θ X₀ ω) y + KAbsR θ X₀ ω (rhoT θ X₀ ω) y

/-- **`m = T̃' - K_pt ρ̃ - NT_pt`** with `T̃' = T'_cont + K_𝒜 ρ̃` (§5.3). -/
lemma marginM_eq (ω : JitterΩ) (y : ℝ) :
    marginM θ X₀ ω y = (TpCont θ X₀ ω y + KAbsR θ X₀ ω (rhoT θ X₀ ω) y) -
      KptR θ X₀ ω (rhoT θ X₀ ω) y - NTpt θ X₀ ω y := by
  unfold marginM NTpt; ring

/-! ### `R1Ident` from Proposition 5.38 -/

section R1

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- The compensator density is interval integrable on a window `[a, b]`. -/
lemma compR_intervalIntegrable (ω : JitterΩ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun y => (compDen θ X₀ ω y).toReal) volume a b := by
  set K := 2 * ∑ w ∈ (cof_finite hc b ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  have hdm : Measurable (compDen θ X₀ ω) :=
    Measurable.ennreal_tsum fun k => compTerm_meas hc k ω
  refine (intervalIntegrable_const (c := K.toReal)).mono_fun'
    (ENNReal.measurable_toReal.comp hdm).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  rw [uIoc_of_le hab] at hy
  show ‖(compDen θ X₀ ω y).toReal‖ ≤ K.toReal
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hK (compDen_le hc hev ω hy.2)

/-- **The §5.3 bookkeeping identity** `|ℓ_jit(I) - Comp(I) - ∫_I m| ≤ 2` for a window
`I = [a, b)` with `b ≥ X₀`, off the null set `NiceEv`ᶜ. -/
theorem bookkeeping_m {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {a b : ℤ} (hab : a ≤ b)
    (hb : (X₀ : ℝ) ≤ b) :
    |(ellIo θ X₀ a b ω : ℝ) - (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) -
      ∫ y in (a : ℝ)..(b : ℝ), marginM θ X₀ ω y| ≤ 2 := by
  obtain ⟨hU, -, hnt⟩ := hN
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨hTi, hTe⟩ := integral_TpCont hc ω hab' hb
  have hcR := compR_intervalIntegrable hc hev ω hab'
  have hm : ∫ y in (a : ℝ)..(b : ℝ), marginM θ X₀ ω y =
      (∫ y in (a : ℝ)..(b : ℝ), TpCont θ X₀ ω y) -
        ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal :=
    intervalIntegral.integral_sub hTi hcR
  rw [hm, hTe]
  -- the bookkeeping of the slot model
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
  have ht : TieFree h0.limModel ω := by
    rw [← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have F := excFacts_of h0 hev ht
  have hB := bookkeeping F hab' hb
  have hM : CM θ X₀ ω = h0.limModel := Mcl_eq_lim hc h0
  have hDF : DF θ X₀ ω = DM h0.limModel ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hell : (ellIo θ X₀ a b ω : ℝ) = ellI θ h0.limModel ω a b := by
    unfold ellIo; rw [hM, Ucl_eq hU]
  rw [hell, hDF]
  have e : ∀ x y z : ℝ, x - z - (y - z) = x - y := fun x y z => by ring
  rw [e]
  exact hB

/-- **`R1Ident` from Proposition 5.38** (the §5 front): if the margin density `m = T'_cont - c`
of the construction satisfies `PointwiseMargin m X₀` a.s. on `Good(< b)` for every admissible
window, then `Margin.R1Ident` holds on every admissible window a.s. on `Good(< b)`, with
`Comp(I) = ∫_I c`. -/
theorem r1Ident_of_margin (D : Sec5Family)
    (hPM : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      Margin.PointwiseMargin (marginM θ X₀ ω) X₀) :
    ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ D (tE2 b) →
      Margin.R1Ident θ X₀ m a b ω := by
  intro m a b hadm
  have hadm' := hadm
  obtain ⟨hub, -, hab, -⟩ := hadm'
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    exact ae_iff.mpr this
  filter_upwards [hPM m a b hadm, compSum_le hc hev m hab, hnice] with ω hP hS hN hG
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hb : (X₀ : ℝ) ≤ b := (X₀_le_uS (X₀ := X₀) (by
    linarith [one_lt_of_logX hX0 hc.hX]) m).trans hub
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨hTi, -⟩ := integral_TpCont hc ω hab' hb
  refine ⟨marginM θ X₀ ω, ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal, hP hG,
    hTi.sub (compR_intervalIntegrable hc hev ω hab'), bookkeeping_m hc hev hN hab hb, hS⟩

end R1

end BModel
