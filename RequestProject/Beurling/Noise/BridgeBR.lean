module

public import RequestProject.Beurling.Noise.KRTrueTerm

/-!
# Proposition 5.26 (the bridge: operator versus sharp)

The long operator and the sharp reference, for a start `x` (levels `n = iota e`, values
`V n = P.val e`, as in `KRWeights.lean`; the true kernels `C_n` of §5.9.4 have the densities
`gK … (phiT tw X₀⁻) n` for `n ≥ 2`, and `C_1 = δ_x`):

* `Rres P H tw X0m x g = (R_res g)(x) = ∑_n n⁻¹ ∫ g dC_n^x` (eq. (R-kernels)); the true kernels
  vanish at the levels with `x/n < X₀⁻/2` (`gK_support`), so the sum is over the levels with
  `x/n ≥ X₀⁻/2` (`levels`);
* `rhoSh P tw X0m x g = ∑_n c_n(x) g(x/n)/n`, `c_n(x) = μ(n) χ^t_x(n) 1[x/n ≥ X₀⁻]` (Lemma 5.5);
* `BRc = R_res T_c - ∑_n c_n T_c(·/n)/n`.

`prop_5_26` : **Proposition 5.26**:
`log x · |BR_c(x)| ≤ (5.1 C_N + C_S) ∑_u log(2u) o_u + 8.4 C_N E_θ`.

Proved here: the Kantorovich–Rubinstein part of the proof. For the nominal kernels
`∫ T_c dC_n^nom - c_n T_c(x/n) = ∫ (T_c - T_c(x/n)) dC_n^nom` (the mass of `C_n^nom` is `c_n`,
`nom_mass`), the kernel is supported in `[x/n ± 1.02 H(x/n)]` (`nom_support`), so the term is at
most `o_u TV(C_n^nom)` (`kr_part_level`), and summing with Corollary 5.17(b) (`NomWeights`)
gives `C_N ∑_u log(2u) o_u/log x` (`kr_part_sum`). The input that is not proved here is the
near-threshold part of the proof (the second bullet, `BRNearPart`): the contribution of
`C_n - C_n^nom`, bounded there by the Duhamel form of Proposition 5.18, `|T_c| ≤ 2`,
Lemma 5.20 (`τ`-near steps, `≤ 8.4 C_N E_θ/log x`) and the terminal levels (`X₀`-near steps,
`≤ o_{X₀} · 2C_N · 1.52 log(2X₀)/log x`).

The oscillation `o_u` enters through the property it is defined by (`OscBound`): every point of
`[x/n ± 1.02 H(x/n)]` lies in a window of length `≤ 2.04 H(u)` meeting `[u, 2u)` together with
`x/n`, so `|T_c(s) - T_c(x/n)| ≤ o_u` there.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem Filter Topology
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

/-- The levels `n ≥ 2` with `x/n ≥ X₀⁻/2`. -/
noncomputable def levels : Finset ℕ := (NAll P x (X0m / 2)).filter (2 ≤ ·)

/-- **The long operator** `(R_res g)(x) = ∑_n n⁻¹ ∫ g dC_n^x`. -/
noncomputable def Rres (g : ℝ → ℝ) : ℝ :=
  g x + ∑ n ∈ levels P X0m x,
    (∫ t, g t * gK P.labelVal x H (phiT tw X0m) n t) / Vl P n

/-- **The sharp reference** `∑_n c_n(x) g(x/n)/n`. -/
noncomputable def rhoSh (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ NAll P x X0m, cN P tw X0m x n * g (posn P.labelVal x n) / Vl P n

/-- `BR_c(x) = (R_res T_c)(x) - ∑_n c_n T_c(x/n)/n`. -/
noncomputable def BRc (Tc : ℝ → ℝ) : ℝ := Rres P H tw X0m x Tc - rhoSh P tw X0m x Tc

/-- The density of the nominal kernel `C_n^nom` (`n ≥ 2`). -/
noncomputable abbrev gNom (n : ℕ) : ℝ → ℝ :=
  gK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) n

/-- **The oscillation property defining `o_u`** (for `T_c`): at the levels `n ≥ 2` of the scale
`u`, `|T_c(s) - T_c(x/n)| ≤ o_u` for `|s - x/n| ≤ 1.02 H(x/n)`. -/
def OscBound (Tc : ℝ → ℝ) (Sc : Finset ℝ) (o : ℝ → ℝ) : Prop :=
  ∀ u ∈ Sc, 0 ≤ o u ∧ ∀ n ∈ NW P x u, 2 ≤ n → ∀ s,
    |s - posn P.labelVal x n| ≤ 1.02 * H (posn P.labelVal x n) →
      |Tc s - Tc (posn P.labelVal x n)| ≤ o u

/-- **The near-threshold part of the proof of Proposition 5.26** (its second bullet): the
contribution of the true-minus-nominal kernels,
`|∑_n n⁻¹ ∫ T_c d(C_n - C_n^nom)| ≤ (8.4 C_N E_θ + o_{X₀} · 2C_N · 1.52 log(2X₀))/log x`. -/
def BRNearPart (Tc : ℝ → ℝ) (o : ℝ → ℝ) (X0 CN Eθ : ℝ) : Prop :=
  |∑ n ∈ levels P X0m x, (∫ t, Tc t * (gK P.labelVal x H (phiT tw X0m) n t -
      gNom P H tw X0m x n t)) / Vl P n| ≤
    (8.4 * CN * Eθ + o X0 * (2 * CN) * (1.52 * Real.log (2 * X0))) / Real.log x

/-! ## The nominal kernels: mass, support, and the KR part -/

variable {P H tw X0m x}

lemma integrable_gNom (hH : WidthReg H) (n : ℕ) :
    Integrable (gNom P H tw X0m x n) ∧ Measurable (gNom P H tw X0m x n) :=
  integrable_gK hH (constF_ok (kapN_mem (tw := tw) (X0m := X0m) P.labelVal x)) n

/-- Off `[x/n ± 1.02 H(x/n)]` the distribution function of `C_n^nom` is `c_n 1[x/n ≤ ·]`. -/
lemma nom_cdf_eq {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 1.02 * H (posn P.labelVal x n) < |t - posn P.labelVal x n|) :
    cdf (gNom P H tw X0m x n) t = cN P tw X0m x n * stepF (posn P.labelVal x n) t := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p hp => by linarith [hval2 p hp]
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
  have hc := kerV_eq_cdf (x := x) hval hP.reg hκ n hn
  have hs := kerV_support (x := x) hval hP.reg (fun d n => by
    rw [abs_le]; constructor <;> linarith [(hκ d n).1, (hκ d n).2]) (by norm_num)
    (radiusCond_nominal (tw := tw) hP hval2) n (by omega) t ht
  unfold DkerV at hs
  rw [← hc]
  unfold cN
  linarith

/-- The density of `C_n^nom` vanishes a.e. off `[x/n ± 1.02 H(x/n)]`. -/
lemma nom_ae_zero {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p) {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ t, 1.02 * H (posn P.labelVal x n) < |t - posn P.labelVal x n| →
      gNom P H tw X0m x n t = 0 := by
  have hg := (integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hP.reg n).1
  filter_upwards [ae_hasDerivAt_cdf hg] with t hd ht
  set a := posn P.labelVal x n
  set R := 1.02 * H a
  have hR : 0 < R := by have := hP.reg.pos a; positivity
  -- `cdf` is locally constant at `t`
  have hloc : cdf (gNom P H tw X0m x n) =ᶠ[𝓝 t]
      fun _ => cN P tw X0m x n * stepF a t := by
    rcases lt_or_gt_of_ne (show t - a ≠ 0 by intro h; rw [h, abs_zero] at ht; linarith) with
      hneg | hpos
    · have hta : t < a - R := by rw [abs_of_neg hneg] at ht; linarith
      filter_upwards [Iio_mem_nhds hta] with s hs
      rw [Set.mem_Iio] at hs
      have hs' : R < |s - a| := by rw [abs_of_neg (by linarith)]; linarith
      rw [nom_cdf_eq hP hval2 hn hs']
      unfold stepF; rw [if_neg (by linarith), if_neg (by linarith)]
    · have hta : a + R < t := by rw [abs_of_pos hpos] at ht; linarith
      filter_upwards [Ioi_mem_nhds hta] with s hs
      rw [Set.mem_Ioi] at hs
      have hs' : R < |s - a| := by rw [abs_of_pos (by linarith)]; linarith
      rw [nom_cdf_eq hP hval2 hn hs']
      unfold stepF; rw [if_pos (by linarith), if_pos (by linarith)]
  have h0 : HasDerivAt (cdf (gNom P H tw X0m x n)) 0 t :=
    (hasDerivAt_const t _).congr_of_eventuallyEq hloc
  exact hd.unique h0

/-- **The mass of `C_n^nom`** is `c_n`. -/
lemma nom_mass {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p)
    {n : ℕ} (hn : 2 ≤ n) : ∫ t, gNom P H tw X0m x n t = cN P tw X0m x n := by
  have hg := (integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hP.reg n).1
  set a := posn P.labelVal x n
  set R := 1.02 * H a
  have hR : 0 < R := by have := hP.reg.pos a; positivity
  rw [← integral_add_compl (s := Iic (a + R + 1)) measurableSet_Iic hg, compl_Iic]
  have h1 : ∫ t in Iic (a + R + 1), gNom P H tw X0m x n t = cN P tw X0m x n := by
    have := nom_cdf_eq (tw := tw) hP hval2 hn (t := a + R + 1) (by
      show R < |a + R + 1 - a|
      rw [abs_of_pos (by linarith)]; linarith)
    unfold cdf at this
    rw [this]; unfold stepF; rw [if_pos (by linarith), mul_one]
  have h2 : ∫ t in Ioi (a + R + 1), gNom P H tw X0m x n t = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards [nom_ae_zero (tw := tw) (x := x) hP hval2 hn] with t ht htT
    rw [Set.mem_Ioi] at htT
    exact ht (by
      show R < |t - a|
      rw [abs_of_pos (by linarith)]; linarith)
  rw [h1, h2, add_zero]

/-- `TV(C_n^nom) = ∫ |g_n|` (as real numbers). -/
lemma nom_TV_eq (hH : WidthReg H) (hval : ∀ p, p.Prime → 1 ≤ P.labelVal p) {n : ℕ}
    (hn : 2 ≤ n) :
    (eVariationOn (kN P H tw X0m x n) univ).toReal =
      (∫⁻ t, ‖gNom P H tw X0m x n t‖ₑ).toReal := by
  have hg := (integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hH n).1
  have hc := kerV_eq_cdf (x := x) hval hH (kapN_mem (tw := tw) (X0m := X0m) P.labelVal x) n hn
  unfold kN
  rw [show nomFilter P.labelVal x tw X0m = kapN tw X0m P.labelVal x from rfl, hc]
  congr 1
  exact le_antisymm (eVariationOn_cdf_le hg) (lintegral_enorm_le_eVariationOn hg)

/-- **The KR part at one level**: `|∫ T_c dC_n^nom - c_n T_c(x/n)| ≤ o · TV(C_n^nom)` when
`|T_c - T_c(x/n)| ≤ o` on `[x/n ± 1.02 H(x/n)]`. -/
lemma kr_part_level {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p) {n : ℕ} (hn : 2 ≤ n) {Tc : ℝ → ℝ}
    (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) {o : ℝ} (ho : 0 ≤ o)
    (hosc : ∀ s, |s - posn P.labelVal x n| ≤ 1.02 * H (posn P.labelVal x n) →
      |Tc s - Tc (posn P.labelVal x n)| ≤ o) :
    |(∫ t, Tc t * gNom P H tw X0m x n t) - cN P tw X0m x n * Tc (posn P.labelVal x n)| ≤
      o * (eVariationOn (kN P H tw X0m x n) univ).toReal := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p hp => by linarith [hval2 p hp]
  obtain ⟨hg, hgm⟩ := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hP.reg n
  set g := gNom P H tw X0m x n
  set a := posn P.labelVal x n
  have hTg : Integrable (fun t => Tc t * g t) :=
    hg.bdd_mul (c := 2) hTm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hTb t)
  have hdiff : (∫ t, Tc t * g t) - cN P tw X0m x n * Tc a = ∫ t, (Tc t - Tc a) * g t := by
    rw [← nom_mass (tw := tw) (x := x) hP hval2 hn]
    rw [show (fun t => (Tc t - Tc a) * g t) = fun t => Tc t * g t - Tc a * g t by
      funext t; ring]
    rw [integral_sub hTg (hg.const_mul _), integral_const_mul]
    ring
  rw [hdiff, nom_TV_eq hP.reg hval hn]
  calc |∫ t, (Tc t - Tc a) * g t| ≤ ∫ t, |(Tc t - Tc a) * g t| := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans (le_of_eq (by simp [Real.norm_eq_abs]))
    _ ≤ ∫ t, o * |g t| := by
        apply integral_mono_ae
        · refine (hTg.sub (hg.const_mul (Tc a))).abs.congr
            (Filter.Eventually.of_forall fun t => ?_)
          simp only [Pi.sub_apply]
          congr 1; ring
        · exact (hg.abs.const_mul o)
        · filter_upwards [nom_ae_zero (tw := tw) (x := x) hP hval2 hn] with t ht
          by_cases hs : |t - a| ≤ 1.02 * H a
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hosc t hs) (abs_nonneg _)
          · have hg0 : g t = 0 := ht (not_le.mp hs)
            simp [hg0]
    _ = o * (∫⁻ t, ‖g t‖ₑ).toReal := by
        rw [integral_const_mul]
        congr 1
        have := integral_norm_eq_lintegral_enorm hgm.aestronglyMeasurable (μ := volume)
        simp only [Real.norm_eq_abs] at this
        exact this

/-! ## The KR part, summed, and Proposition 5.26 -/

/-- **The KR part of the proof of Proposition 5.26**, summed over the levels:
`∑_n n⁻¹ |∫ T_c dC_n^nom - c_n T_c(x/n)| ≤ C_N ∑_u log(2u) o_u/log x`. -/
theorem kr_part_sum {ε θ CN : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p) {Tc : ℝ → ℝ} (hTm : Measurable Tc)
    (hTb : ∀ t, |Tc t| ≤ 2) {Sc : Finset ℝ} {o : ℝ → ℝ} (hSc : ∀ u ∈ Sc, 0 < u)
    (hosc : OscBound P H x Tc Sc o) (hnom : NomWeights P H tw X0m x Sc CN)
    (hcov : ∀ n ∈ levels P X0m x, ∃ u ∈ Sc, n ∈ NW P x u) :
    ∑ n ∈ levels P X0m x, |(∫ t, Tc t * gNom P H tw X0m x n t) -
        cN P tw X0m x n * Tc (posn P.labelVal x n)| / Vl P n ≤
      ∑ u ∈ Sc, o u * (CN * Real.log (2 * u) / Real.log x) := by
  classical
  set w : ℕ → ℝ := fun n => (eVariationOn (kN P H tw X0m x n) univ).toReal / Vl P n
  have hw0 : ∀ n, 0 ≤ w n := fun n => div_nonneg ENNReal.toReal_nonneg
    (KR.valN_labelVal_pos P n).le
  have hstep : ∀ n ∈ levels P X0m x, |(∫ t, Tc t * gNom P H tw X0m x n t) -
      cN P tw X0m x n * Tc (posn P.labelVal x n)| / Vl P n ≤
      ∑ u ∈ Sc.filter (fun u => n ∈ NW P x u), o u * w n := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2
    obtain ⟨u, hu, hnu⟩ := hcov n hn
    have hmem : u ∈ Sc.filter (fun u => n ∈ NW P x u) := Finset.mem_filter.mpr ⟨hu, hnu⟩
    obtain ⟨hou, hou'⟩ := hosc u hu
    have hl := kr_part_level (tw := tw) hP hval2 hn2 hTm hTb hou (hou' n hnu hn2)
    have hV := KR.valN_labelVal_pos P n
    calc _ ≤ o u * (eVariationOn (kN P H tw X0m x n) univ).toReal / Vl P n :=
          div_le_div_of_nonneg_right hl hV.le
      _ = o u * w n := by simp only [w]; ring
      _ ≤ _ := Finset.single_le_sum (f := fun u => o u * w n)
          (fun v hv => mul_nonneg (hosc v (Finset.mem_filter.mp hv).1).1 (hw0 n)) hmem
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_comm' (t' := Sc) (s' := fun u => (levels P X0m x).filter (fun n => n ∈ NW P x u))]
  · refine Finset.sum_le_sum fun u hu => ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hosc u hu).1
    refine le_trans ?_ (hnom u hu)
    unfold Wnom
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; exact (Finset.mem_filter.mp hn).2
    · intro n _ _; exact hw0 n
  · intro n u
    simp only [Finset.mem_filter]
    tauto

/-- `c_n = 0` at the levels with `x/n < X₀⁻`. -/
lemma cN_eq_zero_low (ht : ∀ r, r.Prime → 0 < tw r) (hX0 : 0 ≤ X0m) (hx : X0m ≤ x) {n : ℕ}
    (hn : 1 ≤ n) (hlow : posn P.labelVal x n < X0m) : cN P tw X0m x n = 0 := by
  unfold cN
  rw [mass_eq_moebius P.labelVal x ht (fun r _ => P.one_le_labelVal r) hX0 hx hn]
  unfold posn at hlow
  rw [if_neg (not_le.mpr hlow), mul_zero]

/-- The sharp reference split off its `n = 1` term: `∑_n c_n g(x/n)/n = g(x) + ∑_{n ≥ 2} …`
over the levels with `x/n ≥ X₀⁻/2`. -/
lemma rhoSh_eq (ht : ∀ r, r.Prime → 0 < tw r) (hX0 : 0 < X0m) (hx : X0m ≤ x) (g : ℝ → ℝ) :
    rhoSh P tw X0m x g = g x + ∑ n ∈ levels P X0m x,
      cN P tw X0m x n * g (posn P.labelVal x n) / Vl P n := by
  classical
  unfold rhoSh
  have h1 : (1 : ℕ) ∈ NAll P x X0m := by
    apply mem_NAll_of_posn (P := P) one_ne_zero hX0
    unfold posn; rw [LemmaM.valN_one, div_one]; exact hx
  have hsplit : NAll P x X0m = insert 1 ((NAll P x X0m).filter (2 ≤ ·)) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hn
      rcases Nat.lt_or_ge n 2 with h | h
      · left
        have hn0 : n ≠ 0 := by
          obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hn
          exact (iota_pos e).ne'
        omega
      · right; exact ⟨hn, h⟩
    · rintro (rfl | ⟨hn, -⟩)
      · exact h1
      · exact hn
  rw [hsplit, Finset.sum_insert (by simp)]
  unfold cN
  have hV1 : Vl P 1 = 1 := by unfold Vl; exact LemmaM.valN_one _
  rw [mass_one, hV1, show posn P.labelVal x 1 = x by
    unfold posn; rw [LemmaM.valN_one, div_one], one_mul, div_one]
  congr 1
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨?_, hn2⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn1
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rw [mem_elems] at he ⊢
    exact he.trans (div_le_div_of_nonneg_left (show (0:ℝ) ≤ x by linarith) (half_pos hX0)
      (half_le_self hX0.le))
  · intro n hn hnot
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    have hlow : posn P.labelVal x n < X0m := by
      by_contra hc; push_neg at hc
      exact hnot (Finset.mem_filter.mpr ⟨mem_NAll_of_posn (P := P) (by omega) hX0 hc, hn2⟩)
    have := cN_eq_zero_low (P := P) (x := x) ht hX0.le hx (by omega) hlow
    unfold cN at this
    rw [this, zero_mul, zero_div]

/-- **Proposition 5.26 (the bridge: operator versus sharp).** For a start `x ≥ X₀⁻`, with
`o_u` the oscillation of `T_c` at the scales `u ∈ Sc` (`OscBound`), Corollary 5.17(b) at these
scales (`NomWeights`), and the near-threshold part of the proof (`BRNearPart`),
`log x · |BR_c(x)| ≤ (5.1 C_N + C_S) ∑_u log(2u) o_u + 8.4 C_N E_θ`. -/
theorem prop_5_26 {ε θ CN CS Eθ X0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p) (ht : ∀ r, r.Prime → 0 < tw r)
    (hx : X0m ≤ x) (hlx : 0 < Real.log x) {Tc : ℝ → ℝ} (hTm : Measurable Tc)
    (hTb : ∀ t, |Tc t| ≤ 2) {Sc : Finset ℝ} {o : ℝ → ℝ} (hSc : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hosc : OscBound P H x Tc Sc o) (hnom : NomWeights P H tw X0m x Sc CN)
    (hcov : ∀ n ∈ levels P X0m x, ∃ u ∈ Sc, n ∈ NW P x u)
    (hnear : BRNearPart P H tw X0m x Tc o X0 CN Eθ) (hX0 : X0 ∈ Sc) (hCN : 0 ≤ CN)
    (hCS : 0 ≤ CS) :
    Real.log x * |BRc P H tw X0m x Tc| ≤
      (5.1 * CN + CS) * ∑ u ∈ Sc, Real.log (2 * u) * o u + 8.4 * CN * Eθ := by
  have hXm := hP.X0m_pos
  have hSc0 : ∀ u ∈ Sc, 0 < u := fun u hu => by linarith [hSc u hu]
  have hlog2 : ∀ u ∈ Sc, 0 ≤ Real.log (2 * u) := fun u hu =>
    Real.log_nonneg (by linarith [hSc u hu])
  -- the decomposition
  set L := levels P X0m x
  have hdec : BRc P H tw X0m x Tc =
      ∑ n ∈ L, ((∫ t, Tc t * gNom P H tw X0m x n t) -
        cN P tw X0m x n * Tc (posn P.labelVal x n)) / Vl P n +
      ∑ n ∈ L, (∫ t, Tc t * (gK P.labelVal x H (phiT tw X0m) n t -
        gNom P H tw X0m x n t)) / Vl P n := by
    unfold BRc Rres
    rw [rhoSh_eq (P := P) (x := x) ht hXm hx, ← Finset.sum_add_distrib]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hgt := (integrable_gKT (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m) hP.reg n)
    have hgn := integrable_gNom (P := P) (tw := tw) (X0m := X0m) (x := x) hP.reg n
    have hb : ∀ᵐ t ∂volume, ‖Tc t‖ ≤ 2 :=
      Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hTb t
    have i1 := hgt.1.bdd_mul (c := 2) hTm.aestronglyMeasurable hb
    have i2 := hgn.1.bdd_mul (c := 2) hTm.aestronglyMeasurable hb
    rw [show (fun t => Tc t * (gK P.labelVal x H (phiT tw X0m) n t - gNom P H tw X0m x n t)) =
      fun t => Tc t * gK P.labelVal x H (phiT tw X0m) n t - Tc t * gNom P H tw X0m x n t by
        funext t; ring, integral_sub i1 i2]
    ring
  have hkr := kr_part_sum (tw := tw) hP hval2 hTm hTb hSc0 hosc hnom hcov
  have hkr' : |∑ n ∈ L, ((∫ t, Tc t * gNom P H tw X0m x n t) -
        cN P tw X0m x n * Tc (posn P.labelVal x n)) / Vl P n| ≤
      ∑ u ∈ Sc, o u * (CN * Real.log (2 * u) / Real.log x) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le ?_ hkr)
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [abs_div, abs_of_pos (KR.valN_labelVal_pos P n)]
  rw [hdec]
  have htri := abs_add_le
    (∑ n ∈ L, ((∫ t, Tc t * gNom P H tw X0m x n t) -
        cN P tw X0m x n * Tc (posn P.labelVal x n)) / Vl P n)
    (∑ n ∈ L, (∫ t, Tc t * (gK P.labelVal x H (phiT tw X0m) n t -
        gNom P H tw X0m x n t)) / Vl P n)
  have hsum_eq : ∑ u ∈ Sc, o u * (CN * Real.log (2 * u) / Real.log x) =
      CN * (∑ u ∈ Sc, Real.log (2 * u) * o u) / Real.log x := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => by ring
  have hS0 : 0 ≤ ∑ u ∈ Sc, Real.log (2 * u) * o u :=
    Finset.sum_nonneg fun u hu => mul_nonneg (hlog2 u hu) (hosc u hu).1
  have hX0term : Real.log (2 * X0) * o X0 ≤ ∑ u ∈ Sc, Real.log (2 * u) * o u :=
    Finset.single_le_sum (f := fun u => Real.log (2 * u) * o u)
      (fun u hu => mul_nonneg (hlog2 u hu) (hosc u hu).1) hX0
  have hbound : |BRc P H tw X0m x Tc| ≤
      (CN * (∑ u ∈ Sc, Real.log (2 * u) * o u) +
        (8.4 * CN * Eθ + o X0 * (2 * CN) * (1.52 * Real.log (2 * X0)))) / Real.log x := by
    rw [hdec, add_div]
    refine htri.trans (add_le_add (hkr'.trans (le_of_eq hsum_eq)) hnear)
  rw [hdec] at hbound
  calc Real.log x * |_| ≤ Real.log x * ((CN * (∑ u ∈ Sc, Real.log (2 * u) * o u) +
        (8.4 * CN * Eθ + o X0 * (2 * CN) * (1.52 * Real.log (2 * X0)))) / Real.log x) :=
        mul_le_mul_of_nonneg_left hbound hlx.le
    _ = CN * (∑ u ∈ Sc, Real.log (2 * u) * o u) + 8.4 * CN * Eθ +
          3.04 * CN * (Real.log (2 * X0) * o X0) := by field_simp; ring
    _ ≤ (5.1 * CN + CS) * ∑ u ∈ Sc, Real.log (2 * u) * o u + 8.4 * CN * Eθ := by
        have := mul_le_mul_of_nonneg_left hX0term (show 0 ≤ 3.04 * CN by positivity)
        nlinarith [mul_nonneg hCS hS0, mul_nonneg hCN hS0]

end KR

end
