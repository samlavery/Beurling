module

public import RequestProject.Beurling.Noise.RML8EBnd
public import RequestProject.Beurling.Noise.KRWidthReal
public import RequestProject.Beurling.Noise.MarginInt
public import RequestProject.Beurling.Noise.BridgeG1Resp

/-!
# The boundary term of Proposition 5.35(B), Step 2, for the realised width

`KR.RML9.whyp_Hc` : `KR.RML8E.WHyp` for `H = H_c = Queue6.Hc X₀` on the window
`J = [y(1-2δ), y(1-δ)]`, with `H_* = H_c(2y)`, `h_l = 1` and the *ratio* constant
`κ = ε H_*/(y(1-2δ) - H_*)` obtained from (RH) (`CapHSlope X₀ ε`, proved by the Model agent as
`BModel.capHSlope` with `ε = 4·10⁻⁶`) and the monotonicity of `H_c`
(`Hc_incr_ratio`: `H_c(t) - H_c(s) ≤ ε (t-s)/max(s, X₀) · H_c(s)` for `s ≤ t`).

`KR.RML9.size_ok` : the size check `M (3κ(b-a) + 8H_*) ≤ 40√y` with `M = 3(log(2y/X₀⁻) + 1)`,
for `log y ≥ 20` and `δ ≤ 1/4`.

`KR.RML9.hbd_full` : the three inputs `hbd`, `hBnd0`, `hBnd` of `KR.RML6.G1BInputs` for
`Bρs z = B(ρ^sh T')(z)`, with `Bnd = M(3κ(b-a) + 8H_*)`, from (HBS), `2y/X₀⁻ ≤ Z`,
`|T'| ≤ 3` and measurability of `T'` below `2y`.
-/

@[expose] public section

open Real MeasureTheory Set BeurlingSystem CaplLink

namespace KR.RML9

variable {X₀ : ℕ}

/-- **(RH) in ratio form**: `H_c(t) - H_c(s) ≤ ε (t - s)/max(s, X₀) · H_c(s)` for `s ≤ t`. -/
lemma Hc_incr_ratio (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hS : KR.WidthReal.CapHSlope X₀ ε) {s t : ℝ} (hst : s ≤ t) :
    Queue6.Hc X₀ t - Queue6.Hc X₀ s ≤
      ε * (t - s) / max s (X₀ : ℝ) * Queue6.Hc X₀ s := by
  unfold Queue6.Hc
  set a := max s (X₀ : ℝ)
  set b := max t (X₀ : ℝ)
  have ha : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hab : a ≤ b := max_le_max hst le_rfl
  have ha0 : 0 < a := lt_of_lt_of_le (KR.WidthReal.X0_pos hX) ha
  have hba : b - a ≤ t - s := by
    simp only [a, b]
    rcases le_total t X₀ with h1 | h1
    · rw [max_eq_right h1, max_eq_right (hst.trans h1)]; linarith
    · rw [max_eq_left h1]
      rcases le_total s X₀ with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]
  have h1 := hS a b ha hab
  have hbern : (b / a) ^ ε ≤ 1 + ε * (b / a - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := b / a - 1)
      (by have : 0 ≤ b / a := div_nonneg (by linarith) ha0.le; linarith) hε0 hε1
    simpa using this
  have hHa1 := KR.WidthReal.capH_one_le hX ha
  have hq : b / a - 1 = (b - a) / a := by field_simp
  calc capH X₀ b - capH X₀ a ≤ (b / a) ^ ε * capH X₀ a - capH X₀ a := by linarith
    _ ≤ (1 + ε * (b / a - 1)) * capH X₀ a - capH X₀ a := by
        have := mul_le_mul_of_nonneg_right hbern (by linarith : 0 ≤ capH X₀ a)
        linarith
    _ = ε * (b - a) / a * capH X₀ a := by rw [hq]; field_simp; ring
    _ ≤ ε * (t - s) / a * capH X₀ a := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply div_le_div_of_nonneg_right _ ha0.le
        exact mul_le_mul_of_nonneg_left hba hε0

lemma Hc_ge_one (hX : 10 ^ 8 ≤ Real.log X₀) (z : ℝ) : 1 ≤ Queue6.Hc X₀ z :=
  KR.WidthReal.capH_one_le hX (le_max_right _ _)

/-- `H_c(2y) ≤ (2y)^{1/8}` and `≤ 2y/40` for `y ≥ X₀`. -/
lemma Hc_two_le (hX : 10 ^ 8 ≤ Real.log X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    Queue6.Hc X₀ (2 * y) ≤ (2 * y) ^ (1 / 8 : ℝ) ∧ Queue6.Hc X₀ (2 * y) ≤ 2 * y / 40 := by
  have hX0 := KR.WidthReal.X0_pos hX
  have h2 : (X₀ : ℝ) ≤ 2 * y := by linarith
  have he : Queue6.Hc X₀ (2 * y) = capH X₀ (2 * y) := by
    unfold Queue6.Hc; rw [max_eq_left h2]
  rw [he]
  exact ⟨InitialRange.capH_le_rpow (Nat.cast_nonneg _) hX h2,
    KR.WidthReal.capH_le_tenth hX h2⟩

/-- The window constants. -/
noncomputable def aW (y δ : ℝ) : ℝ := y * (1 - 2 * δ)
noncomputable def bW (y δ : ℝ) : ℝ := y * (1 - δ)
noncomputable def HsW (X₀ : ℕ) (y : ℝ) : ℝ := Queue6.Hc X₀ (2 * y)
noncomputable def κW (X₀ : ℕ) (ε y δ : ℝ) : ℝ := ε * HsW X₀ y / (aW y δ - HsW X₀ y)

lemma window_sizes (hX : 10 ^ 8 ≤ Real.log X₀) {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    0 < y ∧ y / 2 ≤ aW y δ ∧ aW y δ ≤ bW y δ ∧ bW y δ ≤ y ∧ 1 ≤ HsW X₀ y ∧
      HsW X₀ y ≤ y / 20 ∧ 9 * y / 20 ≤ aW y δ - HsW X₀ y := by
  have hX0 := KR.WidthReal.X0_pos hX
  have hy0 : 0 < y := lt_of_lt_of_le hX0 hy
  obtain ⟨-, h2⟩ := Hc_two_le hX hy
  have h1 := Hc_ge_one hX (2 * y)
  unfold aW bW HsW
  refine ⟨hy0, by nlinarith, by nlinarith, by nlinarith, h1, by linarith, by nlinarith⟩

/-- **`WHyp` for the realised width** on the window `J = [y(1-2δ), y(1-δ)]`. -/
theorem whyp_Hc (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hS : KR.WidthReal.CapHSlope X₀ ε) {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    KR.RML8E.WHyp (Queue6.Hc X₀) (aW y δ) (bW y δ) (HsW X₀ y) (κW X₀ ε y δ) 1 := by
  obtain ⟨hy0, ha2, hab, hby, hHs1, hHs, hden⟩ := window_sizes hX hy hδ0 hδ
  have hden0 : 0 < aW y δ - HsW X₀ y := by linarith
  have hmono := KR.WidthReal.Hc_mono (X₀ := X₀) hX
  refine ⟨hmono.measurable, KR.WidthReal.Hc_pos hX, hab, by linarith, ?_, ?_, ?_,
    one_pos, fun z _ _ => Hc_ge_one hX z, ?_⟩
  · unfold κW; positivity
  · unfold κW
    rw [div_le_iff₀ hden0]
    nlinarith
  · intro s _ hs
    exact hmono (by linarith)
  · intro s hs1 hs2 z hz1 hz2 hzs
    have hHs0 : 0 < Queue6.Hc X₀ s := KR.WidthReal.Hc_pos hX s
    rcases le_total s z with h | h
    · -- `s ≤ z`
      have hinc := Hc_incr_ratio hX hε0 (by linarith) hS h
      have hm : aW y δ - HsW X₀ y ≤ max s (X₀ : ℝ) := le_max_of_le_left (by linarith)
      have hzs' : z - s ≤ HsW X₀ y := by rw [abs_le] at hzs; linarith [hzs.1]
      rw [abs_of_nonneg (by linarith [hmono h])]
      calc Queue6.Hc X₀ z - Queue6.Hc X₀ s
          ≤ ε * (z - s) / max s (X₀ : ℝ) * Queue6.Hc X₀ s := hinc
        _ ≤ ε * HsW X₀ y / (aW y δ - HsW X₀ y) * Queue6.Hc X₀ s := by
          apply mul_le_mul_of_nonneg_right _ hHs0.le
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hzs' hε0) hden0 hm
    · -- `z ≤ s`
      have hinc := Hc_incr_ratio hX hε0 (by linarith) hS h
      have hm : aW y δ - HsW X₀ y ≤ max z (X₀ : ℝ) := le_max_of_le_left (by linarith)
      have hzs' : s - z ≤ HsW X₀ y := by rw [abs_le] at hzs; linarith [hzs.2]
      have hzle := hmono h
      have hHz0 : 0 < Queue6.Hc X₀ z := KR.WidthReal.Hc_pos hX z
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      calc Queue6.Hc X₀ s - Queue6.Hc X₀ z
          ≤ ε * (s - z) / max z (X₀ : ℝ) * Queue6.Hc X₀ z := hinc
        _ ≤ ε * HsW X₀ y / (aW y δ - HsW X₀ y) * Queue6.Hc X₀ s := by
          apply mul_le_mul _ hzle hHz0.le (div_nonneg (mul_nonneg hε0 (by linarith)) hden0.le)
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hzs' hε0) hden0 hm

/-- `κ (b - a) ≤ H_*` on the window. -/
lemma κ_mul_le (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    κW X₀ ε y δ * (bW y δ - aW y δ) ≤ HsW X₀ y := by
  obtain ⟨hy0, -, -, -, hHs1, -, hden⟩ := window_sizes hX hy hδ0 hδ
  have hden0 : 0 < aW y δ - HsW X₀ y := by linarith
  have hba : bW y δ - aW y δ = δ * y := by unfold aW bW; ring
  unfold κW
  rw [hba, div_mul_eq_mul_div, div_le_iff₀ hden0]
  have : ε * HsW X₀ y * (δ * y) ≤ HsW X₀ y * (y / 8) := by
    have h1 : ε * δ ≤ 1 / 8 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ HsW X₀ y * y)
    nlinarith
  nlinarith

/-- `36 (L + 2) ≤ 40 e^{3L/8}` for `L ≥ 20`. -/
lemma lin_le_exp {L : ℝ} (hL : 20 ≤ L) : 36 * (L + 2) ≤ 40 * Real.exp (3 * L / 8) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 3 * L / 8) (by linarith)
  nlinarith

/-- **The size check** `M (3κ(b-a) + 8H_*) ≤ 40√y`, `M = 3(log(2y/X₀⁻) + 1)`. -/
theorem size_ok (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    {X0m y δ : ℝ} (hXm : 1 ≤ X0m) (hy : (X₀ : ℝ) ≤ y) (hL : 20 ≤ Real.log y)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    3 * (Real.log (2 * y / X0m) + 1) *
        (3 * κW X₀ ε y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y) ≤ 40 * √y := by
  obtain ⟨hy0, -, hab, -, hHs1, -, hden⟩ := window_sizes hX hy hδ0 hδ
  have hκ := κ_mul_le hX hε0 hε1 hy hδ0 hδ
  have hκ0 : 0 ≤ κW X₀ ε y δ * (bW y δ - aW y δ) := by
    apply mul_nonneg _ (by linarith)
    unfold κW
    exact div_nonneg (mul_nonneg hε0 (by linarith)) (by linarith)
  have hHs8 := (Hc_two_le hX hy).1
  set L := Real.log y
  -- `log(2y/X₀⁻) ≤ L + 1`
  have hlog : Real.log (2 * y / X0m) ≤ L + 1 := by
    have h1 : 2 * y / X0m ≤ 2 * y := div_le_self (by linarith) hXm
    have h2 : Real.log (2 * y / X0m) ≤ Real.log (2 * y) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hy0.ne'] at h2
    have := Real.log_two_lt_d9; linarith
  -- `(2y)^{1/8} ≤ (9/8) y^{1/8}`
  have h28 : (2 * y) ^ (1 / 8 : ℝ) ≤ 9 / 8 * y ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hy0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy0.le _)
    have : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ (9 / 8 : ℝ) := by
      rw [show (9 / 8 : ℝ) = ((9 / 8 : ℝ) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) by
        rw [← Real.rpow_mul (by norm_num)]; norm_num]
      exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    exact this
  -- `√y = y^{1/8} e^{3L/8}`
  have hsq : √y = y ^ (1 / 8 : ℝ) * Real.exp (3 * L / 8) := by
    rw [Real.sqrt_eq_rpow, show Real.exp (3 * L / 8) = y ^ (3 / 8 : ℝ) by
      rw [Real.rpow_def_of_pos hy0]; simp only [L]; ring_nf, ← Real.rpow_add hy0]
    norm_num
  have hy8 : 0 < y ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hexp := lin_le_exp hL
  calc 3 * (Real.log (2 * y / X0m) + 1) *
        (3 * κW X₀ ε y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y)
      ≤ 3 * (L + 2) * (11 * (9 / 8 * y ^ (1 / 8 : ℝ))) := by
        apply mul_le_mul (by linarith) _ (by nlinarith) (by linarith)
        have : HsW X₀ y ≤ 9 / 8 * y ^ (1 / 8 : ℝ) := hHs8.trans h28
        nlinarith
    _ = 37.125 * (L + 2) * y ^ (1 / 8 : ℝ) := by ring
    _ ≤ 40 * √y := by
        rw [hsq]
        have : 37.125 * (L + 2) ≤ 40 * Real.exp (3 * L / 8) := by
          have := Real.quadratic_le_exp_of_nonneg (x := 3 * L / 8) (by linarith)
          nlinarith
        nlinarith

/-- **The boundary-term inputs** `hbd`, `hBnd0`, `hBnd` of `G1BInputs` (Prop 5.35(B),
Step 2) for the realised width, with `Bρs z = B(ρ^sh T')(z)` and
`Bnd = 3(log(2y/X₀⁻) + 1)(3κ(b-a) + 8H_*)`. -/
theorem hbd_full (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hS : KR.WidthReal.CapHSlope X₀ ε) {P : BeurlingSystem} {tw : ℕ → ℝ}
    {X0m X0m' Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m' Z η1 η2 ε1)
    (ht : ∀ r, r.Prime → 0 < tw r) (hXm : 1 ≤ X0m) {Tp : ℝ → ℝ} (hTm : Measurable Tp)
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyX : 3 * X0m ≤ y) (hL : 20 ≤ Real.log y)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (hZ : 2 * y / X0m ≤ Z)
    (hTb : ∀ u, X0m ≤ u → u ≤ 2 * y → |Tp u| ≤ 3) :
    (∫ z in aW y δ..bW y δ, (Margin.Bavg (Queue6.Hc X₀ z)
        (fun s => rhoSh P tw X0m s Tp) z - rhoSh P tw X0m z Tp)) ≤
      3 * (Real.log (2 * y / X0m) + 1) *
        (3 * κW X₀ ε y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y) ∧
    0 ≤ 3 * (Real.log (2 * y / X0m) + 1) *
        (3 * κW X₀ ε y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y) ∧
    3 * (Real.log (2 * y / X0m) + 1) *
        (3 * κW X₀ ε y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y) ≤ 40 * √y := by
  classical
  have hW := whyp_Hc hX hε0 hε1 hS hy hδ0 hδ
  obtain ⟨hy0, ha2, hab, hby, hHs1, hHs, hden⟩ := window_sizes hX hy hδ0 hδ
  have hX0 : 0 < X0m := by linarith
  set B := 2 * y
  set Nb := NAll P B X0m
  set G : ℝ → ℝ := fun s => ∑ n ∈ Nb.filter (fun _ => True),
    (if Vl P n ≤ s / X0m then
      (LemmaM.coeff tw P.labelVal X0m s n : ℝ) * Tp (s / Vl P n) / Vl P n else 0)
  have hGm : Measurable G := by
    refine Finset.measurable_sum _ fun n _ => Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le measurable_const (measurable_id.div_const _)
    · exact ((KR.Int.measurable_coeff tw P.labelVal X0m n).mul
        (hTm.comp (measurable_id.div_const _))).div_const _
  have hcN : ∀ s n, cN P tw X0m s n = (LemmaM.coeff tw P.labelVal X0m s n : ℝ) :=
    fun s n => mass_eq_coeff _ _ _ _ _
  have hGeq : ∀ s, s ≤ B → G s = rhoSh P tw X0m s Tp := by
    intro s hs
    show _ = ∑ n ∈ NAll P s X0m, cN P tw X0m s n * Tp (posn P.labelVal s n) / Vl P n
    have hfil : NAll P s X0m = (NAll P s X0m).filter (fun _ => True) := by simp
    rw [hfil, KR.Int.sum_NAll_eq P hX0 hs]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold posn
    rw [hcN]
  -- the window lies below `B`
  have hwin : ∀ s, s ≤ bW y δ + HsW X₀ y → s ≤ B := fun s hs => by
    simp only [B]; linarith
  set M := 3 * (Real.log (2 * y / X0m) + 1)
  have hlog0 : 0 ≤ Real.log (2 * y / X0m) := Real.log_nonneg (by
    rw [le_div_iff₀ hX0]; linarith)
  have hM0 : 0 ≤ M := by positivity
  have hGM : ∀ s, aW y δ - HsW X₀ y ≤ s → s ≤ bW y δ + HsW X₀ y → |G s| ≤ M := by
    intro s hs1 hs2
    rw [hGeq s (hwin s hs2)]
    have hXs : X0m ≤ s := by linarith
    have hsZ : s / X0m ≤ Z := (div_le_div_of_nonneg_right (by linarith) hX0.le).trans hZ
    have hb := KR.G1.abs_rhoSh_le_harm h ht hX0 hXs hsZ (M := 3)
      (fun u hu1 hu2 => hTb u hu1 (by linarith))
    have hls : Real.log (s / X0m) ≤ Real.log (2 * y / X0m) :=
      Real.log_le_log (div_pos (by linarith) hX0)
        (div_le_div_of_nonneg_right (by linarith) hX0.le)
    calc |rhoSh P tw X0m s Tp| ≤ (Real.log (s / X0m) + 1) * 3 := hb
      _ ≤ M := by simp only [M]; nlinarith
  have hbd := KR.RML8E.hbd_of hW hGm hM0 hGM (size_ok hX hε0 hε1 hXm hy hL hδ0 hδ)
  -- transfer from `G` to `ρ^sh` on `[a, b]`
  have hcongr : (∫ z in aW y δ..bW y δ, (Margin.Bavg (Queue6.Hc X₀ z)
      (fun s => rhoSh P tw X0m s Tp) z - rhoSh P tw X0m z Tp)) =
      ∫ z in aW y δ..bW y δ, (Margin.Bavg (Queue6.Hc X₀ z) G z - G z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hab] at hz
    have hHz : Queue6.Hc X₀ z ≤ HsW X₀ y := hW.le_Hs z (by linarith [hz.1]) (by linarith [hz.2])
    have hHz0 := KR.WidthReal.Hc_pos (X₀ := X₀) hX z
    simp only
    rw [hGeq z (hwin z (by linarith [hz.2]))]
    congr 1
    unfold Margin.Bavg
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    exact (hGeq s (hwin s (by linarith [hs.2, hz.2]))).symm
  rw [hcongr]
  exact hbd

end KR.RML9

end
