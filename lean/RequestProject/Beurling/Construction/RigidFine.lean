module

public import RequestProject.Beurling.Construction.HBSLag

/-!
# A fine bound on the rigid error

`E_rig(x) = Ψ(x, X₀) - Ψ(X₀, X₀) - ∫_{X₀}^x ρ_det` (`Target.rigidErr`). Each `X₀`-smooth integer
`d` carries ramp mass `∫ 1[u ≤ d ≤ (1+κ)u]/(κu) du ≤ 1`, and exactly the full mass
`≥ 1/(1+κ)` when its ramp `[d/(1+κ), d]` lies inside `[X₀, x]`. Hence

* `rigidErr_ge`: `E_rig(x) ≥ -(Ψ((1+κ)x) - Ψ(x)) ≥ -(κx + 1)`;
* `rigidErr_le`: `E_rig(x) ≤ κx + κX₀ + 1`;

so `|E_rig(x)| ≤ κx + κX₀ + 1` (`abs_rigidErr_le_fine`), which is much smaller than the crude bound
`Ψ(2x, X₀)` (`Target.abs_rigidErr_le`) near `X₀`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Target Rankin

namespace Construction

/-- Smooth numbers in a window: `Ψ(b) - Ψ(a) ≤ b - a + 1` for `0 ≤ a ≤ b`. -/
lemma smoothCount_sub_le (X₀ : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (smoothCount X₀ b : ℝ) - smoothCount X₀ a ≤ b - a + 1 := by
  classical
  unfold smoothCount
  have hsub : Nat.smoothNumbersUpTo ⌊b⌋₊ X₀ ⊆
      Nat.smoothNumbersUpTo ⌊a⌋₊ X₀ ∪ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    rw [Finset.mem_union, Nat.mem_smoothNumbersUpTo, Finset.mem_Ioc]
    by_cases h : n ≤ ⌊a⌋₊
    · exact Or.inl ⟨h, hn.2⟩
    · exact Or.inr ⟨by omega, hn.1⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Ioc] at h1
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have h2 : ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) ≤ b - a + 1 := by
    rw [Nat.cast_sub hfl]
    have := Nat.floor_le (ha.trans hab)
    have := Nat.lt_floor_add_one a
    linarith
  have h3 : ((Nat.smoothNumbersUpTo ⌊b⌋₊ X₀).card : ℝ) ≤
      (Nat.smoothNumbersUpTo ⌊a⌋₊ X₀).card + ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

/-- **Ramp mass of the rigid integers, upper bound**: only smooth `d ∈ (X₀, (1+κ)x]` carry ramp
mass on `(X₀, x]`, each at most `1`, so `∫_{X₀}^x ρ_det ≤ Ψ((1+κ)x) - Ψ(X₀)`. -/
lemma integral_rhoDet_le_window (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) :
    ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u ≤
      (smoothCount X₀ ((1 + κ) * x) : ℝ) - smoothCount X₀ (X₀ : ℝ) := by
  classical
  set S := (Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀).filter (fun n : ℕ => (X₀ : ℝ) < n)
    with hS
  have hX01 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX0
  have hS0 : ∀ n ∈ S, (0 : ℝ) < n := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    linarith [hn.2]
  set c : ℕ → ℝ := fun n => (1 + κ) / (κ * n) with hc
  set G : ℝ → ℝ := fun u => ∑ n ∈ S, (Icc ((n : ℝ) / (1 + κ)) n).indicator (fun _ => c n) u
    with hG
  have hpt : ∀ u ∈ Ioc (X₀ : ℝ) x, rhoDet X₀ κ u ≤ G u := by
    intro u hu
    have hu1 : 1 ≤ u := le_trans hX01 hu.1.le
    have hu0 : 0 < u := by linarith
    have hκu : 0 < κ * u := mul_pos hκ hu0
    set P : ℕ → Prop := fun n => u ≤ n ∧ (n : ℝ) ≤ (1 + κ) * u with hP
    have hsub : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)) ⊆
        S.filter P := by
      intro n hn
      rw [Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
      have h1 : (n : ℝ) ≤ (1 + κ) * u :=
        (Nat.cast_le.mpr hn.1.1).trans (Nat.floor_le (by positivity))
      rw [Finset.mem_filter, hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨⟨Nat.le_floor ?_, hn.1.2⟩, by linarith [hu.1, hn.2]⟩, hn.2, h1⟩
      nlinarith [hu.2]
    have hcard := Finset.card_le_card hsub
    unfold rhoDet rigidCount
    calc (((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)).card : ℝ)
          / (κ * u)
        ≤ ((S.filter P).card : ℝ) / (κ * u) := by
          gcongr
      _ = ∑ n ∈ S, if P n then 1 / (κ * u) else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ G u := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hPn : P n
          · rw [if_pos hPn]
            have hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n :=
              ⟨by rw [div_le_iff₀ (by linarith)]; linarith [hPn.2], hPn.1⟩
            rw [Set.indicator_of_mem hmem, hc]
            simp only
            rw [div_le_div_iff₀ hκu (mul_pos hκ (hS0 n hn))]
            nlinarith [hPn.2]
          · rw [if_neg hPn]
            exact Set.indicator_nonneg (fun _ _ => by
              simp only [hc]; exact div_nonneg (by linarith) (mul_nonneg hκ.le (hS0 n hn).le)) _
  have hind : ∀ n : ℕ, IntegrableOn (fun u => (Icc ((n : ℝ) / (1 + κ)) n).indicator
      (fun _ => c n) u) (Ioc (X₀ : ℝ) x) := fun n =>
    (integrableOn_const (C := c n) measure_Ioc_lt_top.ne).indicator measurableSet_Icc
  have hGint : IntegrableOn G (Ioc (X₀ : ℝ) x) := by
    simp only [hG]
    exact integrable_finset_sum _ fun n _ => hind n
  have hint_le : ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u ≤ ∫ u in Ioc (X₀ : ℝ) x, G u := by
    rw [intervalIntegral.integral_of_le hX]
    refine integral_mono_of_nonneg ?_ hGint ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg _) hu.1.le
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hu0)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
  have hG_le : ∫ u in Ioc (X₀ : ℝ) x, G u ≤ (S.card : ℝ) := by
    simp only [hG]
    rw [integral_finset_sum _ fun n _ => hind n]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 := hS0 n hn
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    have hvol : (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((n : ℝ) / (1 + κ)) n) ≤
        n - n / (1 + κ) := by
      unfold Measure.real
      apply ENNReal.toReal_le_of_le_ofReal
      · have : (n : ℝ) / (1 + κ) ≤ n := div_le_self hn0.le (by linarith)
        linarith
      · refine (Measure.restrict_le_self _).trans ?_
        rw [Real.volume_Icc]
    have hc0 : 0 ≤ c n := div_nonneg (by linarith) (mul_nonneg hκ.le hn0.le)
    calc (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((n : ℝ) / (1 + κ)) n) * c n
        ≤ (n - n / (1 + κ)) * c n := mul_le_mul_of_nonneg_right hvol hc0
      _ = 1 := by
          simp only [hc]
          field_simp
          ring
  -- `#S = Ψ((1+κ)x) - Ψ(X₀)`
  have hcardS : (S.card : ℝ) = (smoothCount X₀ ((1 + κ) * x) : ℝ) - smoothCount X₀ (X₀ : ℝ) := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀) (fun n : ℕ => (X₀ : ℝ) < n)
    have hneg : (Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀).filter (fun n : ℕ => ¬ (X₀ : ℝ) < n) =
        Nat.smoothNumbersUpTo ⌊(X₀ : ℝ)⌋₊ X₀ := by
      ext n
      rw [Finset.mem_filter, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbersUpTo,
        Nat.floor_natCast, not_lt, Nat.cast_le]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1.trans (Nat.le_floor ?_), h2⟩, h1⟩
        have : (X₀ : ℝ) ≤ (1 + κ) * x := by nlinarith
        exact this
    rw [hneg] at hsplit
    unfold smoothCount
    rw [← hsplit]
    push_cast
    ring
  rw [← hcardS]
  exact hint_le.trans hG_le

/-- **Lower bound on the rigid error**: `E_rig(x) ≥ -(κx + 1)` for `x ≥ X₀`. -/
theorem rigidErr_ge (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀) (hX : (X₀ : ℝ) ≤ x) :
    -(κ * x + 1) ≤ rigidErr X₀ κ x := by
  have h1 := integral_rhoDet_le_window X₀ hκ hX0 hX
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hX
  have h2 := smoothCount_sub_le X₀ hx0 (show x ≤ (1 + κ) * x by nlinarith)
  unfold rigidErr
  nlinarith

/-- **Lower bound on the ramp mass**: every smooth `d ∈ [(1+κ)X₀, x]` carries ramp mass at least
`1/(1+κ)` on `[X₀, x]`, so `∫_{X₀}^x ρ_det ≥ #{d smooth, (1+κ)X₀ ≤ d ≤ x}/(1+κ)`. -/
lemma integral_rhoDet_ge (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀) (hX : (X₀ : ℝ) ≤ x) :
    (((Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).filter (fun n : ℕ => (1 + κ) * X₀ ≤ (n : ℝ))).card : ℝ) /
      (1 + κ) ≤ ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u := by
  classical
  set S := (Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).filter (fun n : ℕ => (1 + κ) * X₀ ≤ (n : ℝ)) with hS
  set Sb := Nat.smoothNumbersUpTo ⌊(1 + κ) * x⌋₊ X₀ with hSb
  have hX01 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX0
  have hx0 : 0 < x := by linarith
  have hS0 : ∀ n ∈ S, (X₀ : ℝ) * (1 + κ) ≤ n ∧ (n : ℝ) ≤ x := by
    intro n hn
    rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
    exact ⟨by linarith [hn.2], (Nat.cast_le.mpr hn.1.1).trans (Nat.floor_le hx0.le)⟩
  -- `ρ_det` as a finite sum of indicator functions on `(X₀, x]`
  set F : ℝ → ℝ := fun u => ∑ n ∈ Sb, (Icc ((n : ℝ) / (1 + κ)) n).indicator
    (fun u => 1 / (κ * u)) u with hF
  have hFeq : ∀ u ∈ Ioc (X₀ : ℝ) x, rhoDet X₀ κ u = F u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hκu : 0 < κ * u := mul_pos hκ hu0
    have hset : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)) =
        Sb.filter (fun n : ℕ => u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u) := by
      ext n
      simp only [Finset.mem_filter, hSb, Nat.mem_smoothNumbersUpTo]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h4 : (n : ℝ) ≤ (1 + κ) * u :=
          (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
        refine ⟨⟨Nat.le_floor ?_, h2⟩, h3, h4⟩
        nlinarith [hu.2]
      · rintro ⟨⟨-, h2⟩, h3, h4⟩
        exact ⟨⟨Nat.le_floor h4, h2⟩, h3⟩
    unfold rhoDet rigidCount
    rw [hset, hF]
    simp only
    rw [div_eq_mul_one_div, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + κ) * u
    · have hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n :=
        ⟨by rw [div_le_iff₀ (by linarith)]; linarith [h.2], h.1⟩
      rw [if_pos h, Set.indicator_of_mem hmem]; simp
    · have hmem : u ∉ Icc ((n : ℝ) / (1 + κ)) n := by
        rintro ⟨h1, h2⟩
        apply h
        refine ⟨h2, ?_⟩
        rw [div_le_iff₀ (by linarith)] at h1; linarith
      rw [if_neg h, Set.indicator_of_notMem hmem]; simp
  have hcont : ContinuousOn (fun u : ℝ => 1 / (κ * u)) (Icc (X₀ : ℝ) x) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
    intro u hu
    have : (0 : ℝ) < u := by linarith [hu.1]
    exact (mul_pos hκ this).ne'
  have hFint : IntegrableOn F (Ioc (X₀ : ℝ) x) := by
    simp only [hF]
    refine integrable_finset_sum _ fun n _ => ?_
    have h1 : IntegrableOn (fun u : ℝ => 1 / (κ * u)) (Ioc (X₀ : ℝ) x) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    exact h1.indicator measurableSet_Icc
  have hρint : IntegrableOn (rhoDet X₀ κ) (Ioc (X₀ : ℝ) x) :=
    hFint.congr_fun (fun u hu => (hFeq u hu).symm) measurableSet_Ioc
  -- the minorant
  set g : ℝ → ℝ := fun u => ∑ d ∈ S, (Icc ((d : ℝ) / (1 + κ)) d).indicator
    (fun _ => 1 / (κ * d)) u with hg
  have hind : ∀ d : ℕ, IntegrableOn (fun u => (Icc ((d : ℝ) / (1 + κ)) d).indicator
      (fun _ => 1 / (κ * d)) u) (Ioc (X₀ : ℝ) x) := fun d =>
    (integrableOn_const (C := 1 / (κ * d)) measure_Ioc_lt_top.ne).indicator measurableSet_Icc
  have hgint : IntegrableOn g (Ioc (X₀ : ℝ) x) := by
    simp only [hg]; exact integrable_finset_sum _ fun d _ => hind d
  have hSsub : S ⊆ Sb := by
    intro n hn
    rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
    rw [hSb, Nat.mem_smoothNumbersUpTo]
    refine ⟨hn.1.1.trans (Nat.floor_mono ?_), hn.1.2⟩
    nlinarith
  have hpt : ∀ u ∈ Ioc (X₀ : ℝ) x, g u ≤ rhoDet X₀ κ u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [hFeq u hu, hg, hF]
    simp only
    calc ∑ d ∈ S, (Icc ((d : ℝ) / (1 + κ)) d).indicator (fun _ => 1 / (κ * d)) u
        ≤ ∑ d ∈ S, (Icc ((d : ℝ) / (1 + κ)) d).indicator (fun u => 1 / (κ * u)) u := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hmem : u ∈ Icc ((d : ℝ) / (1 + κ)) d
          · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
            apply one_div_le_one_div_of_le (mul_pos hκ hu0)
            exact mul_le_mul_of_nonneg_left hmem.2 hκ.le
          · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      _ ≤ ∑ n ∈ Sb, (Icc ((n : ℝ) / (1 + κ)) n).indicator (fun u => 1 / (κ * u)) u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
          intro n _ _
          by_cases hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n
          · rw [Set.indicator_of_mem hmem]; exact div_nonneg zero_le_one (mul_nonneg hκ.le hu0.le)
          · rw [Set.indicator_of_notMem hmem]
  have hint_ge : ∫ u in Ioc (X₀ : ℝ) x, g u ≤ ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u := by
    rw [intervalIntegral.integral_of_le hX]
    exact setIntegral_mono_on hgint hρint measurableSet_Ioc hpt
  have hg_ge : (S.card : ℝ) / (1 + κ) ≤ ∫ u in Ioc (X₀ : ℝ) x, g u := by
    simp only [hg]
    rw [integral_finset_sum _ fun d _ => hind d]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_div]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hd1, hd2⟩ := hS0 d hd
    have hd0 : (0 : ℝ) < d := by nlinarith
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    have hlo : (d : ℝ) / (1 + κ) ≥ X₀ := by rw [ge_iff_le, le_div_iff₀ (by linarith)]; linarith
    have hvol : (d : ℝ) - d / (1 + κ) ≤
        (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((d : ℝ) / (1 + κ)) d) := by
      rw [Measure.real, Measure.restrict_apply measurableSet_Icc]
      have hsub : Ioo ((d : ℝ) / (1 + κ)) d ⊆ Icc ((d : ℝ) / (1 + κ)) d ∩ Ioc (X₀ : ℝ) x := by
        intro v hv
        exact ⟨⟨hv.1.le, hv.2.le⟩, by linarith [hv.1], by linarith [hv.2]⟩
      have hle := measure_mono (μ := volume) hsub
      rw [Real.volume_Ioo] at hle
      have hfin : volume (Icc ((d : ℝ) / (1 + κ)) d ∩ Ioc (X₀ : ℝ) x) ≠ ⊤ :=
        ((measure_mono Set.inter_subset_right).trans_lt measure_Ioc_lt_top).ne
      have := ENNReal.toReal_mono hfin hle
      rwa [ENNReal.toReal_ofReal (by
        have : (d : ℝ) / (1 + κ) ≤ d := div_le_self hd0.le (by linarith)
        linarith)] at this
    calc (1 : ℝ) / (1 + κ) = (d - d / (1 + κ)) * (1 / (κ * d)) := by
          field_simp; ring
      _ ≤ (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((d : ℝ) / (1 + κ)) d) *
          (1 / (κ * d)) :=
          mul_le_mul_of_nonneg_right hvol (by positivity)
  exact hg_ge.trans hint_ge

/-- **Upper bound on the rigid error**: `E_rig(x) ≤ κx + κX₀ + 1` for `x ≥ X₀`. -/
theorem rigidErr_le (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀) (hX : (X₀ : ℝ) ≤ x) :
    rigidErr X₀ κ x ≤ κ * x + κ * X₀ + 1 := by
  classical
  have hX01 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX0
  have hx0 : 0 < x := by linarith
  set S := (Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).filter (fun n : ℕ => (1 + κ) * X₀ ≤ (n : ℝ)) with hS
  have h1 := integral_rhoDet_ge X₀ hκ hX0 hX
  rw [← hS] at h1
  have hsub : Nat.smoothNumbersUpTo ⌊x⌋₊ X₀ ⊆
      (Nat.smoothNumbersUpTo X₀ X₀ ∪ Finset.Ioc X₀ ⌊(1 + κ) * X₀⌋₊) ∪ S := by
    intro n hn
    have hn' := hn
    rw [Nat.mem_smoothNumbersUpTo] at hn'
    rw [Finset.mem_union, Finset.mem_union, Nat.mem_smoothNumbersUpTo, Finset.mem_Ioc, hS,
      Finset.mem_filter]
    by_cases h1 : n ≤ X₀
    · exact Or.inl (Or.inl ⟨h1, hn'.2⟩)
    · by_cases h2 : (1 + κ) * X₀ ≤ (n : ℝ)
      · exact Or.inr ⟨hn, h2⟩
      · push_neg at h2
        exact Or.inl (Or.inr ⟨by omega, Nat.le_floor h2.le⟩)
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Nat.card_Ioc] at hc
  have hfl : X₀ ≤ ⌊(1 + κ) * X₀⌋₊ := Nat.le_floor (by nlinarith)
  have hIoc : ((⌊(1 + κ) * X₀⌋₊ - X₀ : ℕ) : ℝ) ≤ κ * X₀ := by
    rw [Nat.cast_sub hfl]
    have := Nat.floor_le (show (0 : ℝ) ≤ (1 + κ) * X₀ by positivity)
    linarith
  have hcR : (smoothCount X₀ x : ℝ) ≤ smoothCount X₀ (X₀ : ℝ) + κ * X₀ + S.card := by
    unfold smoothCount
    rw [Nat.floor_natCast]
    have : ((Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).card : ℝ) ≤
        (Nat.smoothNumbersUpTo X₀ X₀).card + ((⌊(1 + κ) * X₀⌋₊ - X₀ : ℕ) : ℝ) + S.card := by
      exact_mod_cast hc
    linarith
  have hSx : (S.card : ℝ) ≤ x := by
    have : S.card ≤ ⌊x⌋₊ := by
      have hsub2 : S ⊆ Finset.Icc 1 ⌊x⌋₊ := by
        intro n hn
        rw [hS, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
        rw [Finset.mem_Icc]
        refine ⟨?_, hn.1.1⟩
        have : (1 : ℝ) ≤ n := by nlinarith [hn.2]
        exact_mod_cast this
      simpa using Finset.card_le_card hsub2
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hx0.le)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hdiv : (S.card : ℝ) - S.card / (1 + κ) ≤ κ * S.card := by
    have : (S.card : ℝ) - κ * S.card ≤ S.card / (1 + κ) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg hS0 (sq_nonneg κ)]
    linarith
  unfold rigidErr
  nlinarith

/-- **The fine rigid bound**: `|E_rig(x)| ≤ κx + κX₀ + 1` for `x ≥ X₀`, `κ > 0`. -/
theorem abs_rigidErr_le_fine (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) : |rigidErr X₀ κ x| ≤ κ * x + κ * X₀ + 1 := by
  have h1 := rigidErr_ge X₀ hκ hX0 hX
  have h2 := rigidErr_le X₀ hκ hX0 hX
  have : 0 ≤ κ * (X₀ : ℝ) := mul_nonneg hκ.le (Nat.cast_nonneg _)
  rw [abs_le]; constructor <;> linarith

end Construction

end
