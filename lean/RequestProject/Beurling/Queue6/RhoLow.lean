module

public import RequestProject.Beurling.Queue6.RhoNoise

/-!
# Lemma 5.22 at a point below `X₀`: `|ρ̃(y) - (B m)(y)| ≤ ν̄(y)` for `X₀⁻ ≤ y < X₀`

`rho_noise` covers `X₀ ≤ y`. For `X₀⁻ = X₀ - H(X₀)/2 ≤ y < X₀` (`H(y) = H(X₀)`), the slot `X₀`
still lies in `B_y`, so `B_y ∩ [X₀, ∞)` is an interval `[X₀, b⟩` with
`|b - (y + H/2)| ≤ 5/8`; the window of `B m` is `[X₀, y + H/2]` (`m = 0` below `X₀`), so only the
upper end strip is paid (`rho_noise_low`). Step 1 on `B_y` is `set_margin_t`, the proof of
`set_margin` with its horizon `max(z, X₀) + 2H(z) ≤ t` replaced by the one it reads,
`Q + 25 log(2Q) + 4 ≤ t`, `Q = P + s + 7/4` (for `z < X₀` the former exceeds `z + 2H(z)`).

* `set_margin_t` : Step 1 on a set near `z` with the horizon actually read;
* `mem_Bset_low` : `x ∈ B_y` for `y < X₀ ≤ x ≤ y + H(y)/2 - 3/8`;
* `rho_noise_low` : the bound for `X₀⁻ ≤ y < X₀`, `y + 2H(y) ≤ t`;
* `rho_noise_Xm` : `rho_noise` and `rho_noise_low` together: all `X₀⁻ ≤ y`, `y + 2H(y) ≤ t`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed
  SlotModel AbsorbEmpty QueueBound

namespace Queue6

open BModel

variable {X₀ : ℕ} {θ : ℝ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 3200000 in
/-- **Step 1 on a set near `z` with the horizon actually read** (`set_margin` with
`max(z, X₀) + 2H(z) ≤ t` replaced by `Q + 25 log(2Q) + 4 ≤ t`, `Q = P + s + 7/4`: the physical
windows of the proof end below `Q`). -/
theorem set_margin_t {ω : JitterΩ} {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) (hE : E3Good θ X₀ ω t) {z s P : ℝ} {A : Set ℝ}
    (hs : s ≤ 1.01 * Hc X₀ z)
    (ht : P + s + 7 / 4 + 25 * Real.log (2 * (P + s + 7 / 4)) + 4 ≤ t)
    (hP1 : z - Hc X₀ z ≤ P) (hP2 : P ≤ z + Hc X₀ z / 2) (hAm : MeasurableSet A)
    (hAo : (A ∩ Ici (X₀ : ℝ)).OrdConnected)
    (hAb : ∀ x ∈ A, (X₀ : ℝ) ≤ x → P < x ∧ x ≤ P + s + 3 / 4) :
    |(sigA (CM θ X₀ ω) A : ℝ) - ∫ r in A, marginM θ X₀ ω r| ≤ s2ε X₀ z := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hbig := X₀_ge_two_pow hc.hX
  obtain ⟨F, hs1, hjit⟩ := model_facts hc hev hN
  set M := CM θ X₀ ω
  set A' := A ∩ Ici (X₀ : ℝ) with hA'
  set w := max z (X₀ : ℝ) with hw
  set H := Hc X₀ z with hH
  have hH0 : 0 ≤ H := Hc_nonneg z
  have hHw : H ≤ w / 10 ^ 7 := Hc_le hc z
  have hHg : 200 * Real.log w + 200 ≤ H := Hc_ge hc z
  have hlw : 10 ^ 8 ≤ Real.log w := (logs_of_ge hX0 hc.hX (le_max_right z (X₀ : ℝ))).1
  have hwX : (X₀ : ℝ) ≤ w := le_max_right _ _
  have hzw : z ≤ w := le_max_left _ _
  have hε0 := s2ε_ge hc z
  -- slots lie above `X₀`
  have hslot : ∀ k, (X₀ : ℝ) ≤ M.slot (k + 1) := fun k => hslot_CM hc ω (k + 1) (by omega)
  have hsigA : sigA M A = sigA M A' := by
    unfold sigA; congr 1; ext k
    simp only [mem_setOf_eq, hA', mem_inter_iff, mem_Ici]
    exact ⟨fun h => ⟨h.1, h.2, hslot k⟩, fun h => ⟨h.1, h.2.1⟩⟩
  -- the margin vanishes below `X₀`
  have hint : ∫ r in A, marginM θ X₀ ω r = ∫ r in A', marginM θ X₀ ω r :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hAm inter_subset_left fun x hx => by
      have : x < X₀ := by
        by_contra h; push_neg at h; exact hx.2 ⟨hx.1, h⟩
      exact RML6.marginM_eq_zero_low hc ω this
  rw [hsigA, hint]
  rcases A'.eq_empty_or_nonempty with h0 | hne
  · rw [h0]
    have : sigA M ∅ = 0 := by unfold sigA; simp
    rw [this]; simp only [Measure.restrict_empty, integral_zero_measure, Nat.cast_zero, sub_zero,
      abs_zero]; linarith
  -- the interval `⟨a, b⟩`
  have hbb : BddBelow A' := ⟨X₀, fun x hx => hx.2⟩
  have hba : BddAbove A' := ⟨P + s + 3 / 4, fun x hx => (hAb x hx.1 hx.2).2⟩
  set a := sInf A'
  set b := sSup A'
  have haX : (X₀ : ℝ) ≤ a := le_csInf hne fun x hx => hx.2
  have haP : P ≤ a := le_csInf hne fun x hx => (hAb x hx.1 hx.2).1.le
  have hbP : b ≤ P + s + 3 / 4 := csSup_le hne fun x hx => (hAb x hx.1 hx.2).2
  have hab : a ≤ b := csInf_le_csSup hbb hba hne
  have hIoo : Ioo a b ⊆ A' := fun x hx => by
    obtain ⟨p, hp, hpx⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨q, hq, hxq⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hAo.out hp hq ⟨hpx.le, hxq.le⟩
  have hIcc : A' ⊆ Icc a b := subset_Icc_csInf_csSup hbb hba
  -- `∫_{A'} m = ∫_a^b m`
  have hae : A' =ᵐ[volume] Icc a b := by
    refine Filter.EventuallyLE.antisymm hIcc.eventuallyLE ?_
    exact (Ioo_ae_eq_Icc (μ := volume)).symm.le.trans hIoo.eventuallyLE
  have hintI : ∫ r in A', marginM θ X₀ ω r = ∫ r in a..b, marginM θ X₀ ω r := by
    rw [setIntegral_congr_set hae, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  rw [hintI]
  -- the geometry
  set m1 := m1z X₀ z
  set u := uS X₀ m1
  obtain ⟨hm1a, hm1b⟩ := mB_spec hX0p (le_max_right (z - Hc X₀ z) (X₀ : ℝ))
  have hu1 : u ≤ max (z - H) X₀ := hm1a
  have hu2 : max (z - H) X₀ < 2 * u := by
    have := hm1b; rw [uS_succ] at this; exact this
  have hua : u ≤ a := hu1.trans (max_le (by linarith) haX)
  have hHb : H ≤ 1.00001 * capH X₀ u := Hc_le_block hc z
  have hHu : 1 ≤ capH X₀ u := (uS_facts hc m1).2.2.1
  have hHu200 : 200 ≤ capH X₀ u := by
    have := log_le_capH hX0 hc.hX (uS_facts hc m1).1
    have : 0 ≤ Real.log u := Real.log_nonneg (by linarith [(uS_facts hc m1).1])
    linarith
  have hlenB : s + 7 / 4 ≤ LenB X₀ m1 - 2 := by unfold LenB; nlinarith
  have hb2u : b + 1 ≤ 2 * uS X₀ (m1 + 1) := by
    rw [uS_succ]
    rcases le_total z (X₀ : ℝ) with h | h
    · have : max (z - H) (X₀ : ℝ) = X₀ := max_eq_right (by linarith [capH_nonneg (X₀ : ℝ) w])
      rw [this] at hu2
      have : w = X₀ := max_eq_right h
      rw [this] at hHw
      nlinarith
    · have : w = z := max_eq_left h
      rw [this] at hHw
      have := le_max_left (z - H) (X₀ : ℝ)
      nlinarith
  have hlog3 : Real.log (2 * (b + 1)) ≤ Real.log w + 1.2 := by
    have h1 : 2 * (b + 1) ≤ 3 * w := by nlinarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (show (3 : ℝ) ≠ 0 by norm_num) (show w ≠ 0 by linarith)] at h2
    have : Real.log 3 ≤ 1.2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.add_one_le_exp (0.2 : ℝ)
      have h2 := Real.exp_one_gt_d9
      have h3 : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  have htime : ∀ β : ℝ, X₀ ≤ β → β ≤ b + 1 → β + 25 * Real.log (2 * β) + 4 ≤ t := by
    intro β hβ1 hβ2
    have : Real.log (2 * β) ≤ Real.log (2 * (P + s + 7 / 4)) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hKb : ∀ β : ℝ, X₀ ≤ β → β ≤ b + 1 → β + 2 ≤ 4 * w := by
    intro β hβ1 hβ2
    nlinarith
  -- the margin on the end strips: `∫_x^{x+1} m ≤ 1.01`
  have hstrip : ∀ x : ℝ, (X₀ : ℝ) ≤ x → ∫ r in x..(x + 1), marginM θ X₀ ω r ≤ 1.01 := by
    intro x hx
    obtain ⟨hTi, hTe⟩ := integral_TpCont hc ω (by linarith : x ≤ x + 1) (by linarith)
    have hcR := compR_intervalIntegrable hc hev ω (by linarith : x ≤ x + 1)
    have hm : (∫ r in x..(x + 1), marginM θ X₀ ω r) =
        (∫ r in x..(x + 1), TpCont θ X₀ ω r) -
          ∫ r in x..(x + 1), (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_sub hTi hcR
    have hc0 : 0 ≤ ∫ r in x..(x + 1), (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => ENNReal.toReal_nonneg
    rw [max_eq_left hx] at hTe
    have hcup := F.win.cup x (x + 1) hx (by linarith)
    have hDF : DF θ X₀ ω = DM M (Ucl ω) := rfl
    rw [hDF] at hTe
    rw [hm, hTe]; linarith
  have hmi : ∀ p q : ℝ, (X₀ : ℝ) ≤ q →  p ≤ q →
      IntervalIntegrable (marginM θ X₀ ω) volume p q := fun p q hq hpq =>
    (integral_TpCont hc ω hpq hq).1.sub (compR_intervalIntegrable hc hev ω hpq)
  -- the upper bound: `σ(A') ≤ σ([a, b + 1))`
  have hup : (sigA M A' : ℝ) ≤ (∫ r in a..b, marginM θ X₀ ω r) + 1.01 + (s2ε X₀ z - 1.01) := by
    have hle : sigA M A' ≤ sigA M (Ico a (b + 1)) :=
      sigA_mono (b := b + 1) (fun x hx => ⟨(hIcc hx).1, by linarith [(hIcc hx).2]⟩)
        (fun x hx => by simp only [mem_Iic]; linarith [hx.2])
    rw [sigA_Ico] at hle
    have hPM := phys_margin hc hev hG hN hE haX hua (by linarith) hb2u (by linarith)
      (htime (b + 1) (by linarith) le_rfl) (hKb (b + 1) (by linarith) le_rfl)
    rw [abs_le] at hPM
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hmi a b (by linarith) hab) (hmi b (b + 1) (by linarith) (by linarith))
    have hs3 := hstrip b (by linarith)
    have : (sigA M A' : ℝ) ≤ sigP M a (b + 1) := by exact_mod_cast hle
    unfold s2ε
    linarith [hPM.2]
  -- the lower bound: `σ([a + 1, b)) ≤ σ(A')`
  have hlo : (∫ r in a..b, marginM θ X₀ ω r) - 1.01 - (s2ε X₀ z - 1.01) ≤ (sigA M A' : ℝ) := by
    rcases le_or_gt (a + 1) b with h1 | h1
    · have hle : sigA M (Ico (a + 1) b) ≤ sigA M A' :=
        sigA_mono (b := b) (fun x hx => hIoo ⟨by linarith [hx.1], hx.2⟩)
          (fun x hx => by simp only [mem_Iic]; exact (hIcc hx).2)
      rw [sigA_Ico] at hle
      have hPM := phys_margin hc hev hG hN hE (m := m1) (by linarith) (by linarith) h1
        (by linarith) (by linarith) (htime b (by linarith) (by linarith))
        (hKb b (by linarith) (by linarith))
      rw [abs_le] at hPM
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hmi a (a + 1) (by linarith) (by linarith)) (hmi (a + 1) b (by linarith) h1)
      have hs3 := hstrip a haX
      have : (sigP M (a + 1) b : ℝ) ≤ sigA M A' := by exact_mod_cast hle
      unfold s2ε
      linarith [hPM.1]
    · -- a short interval: `∫_a^b m ≤ 1.01`
      have hTi := integral_TpCont hc ω hab (by linarith)
      have hcR := compR_intervalIntegrable hc hev ω hab
      have hm : (∫ r in a..b, marginM θ X₀ ω r) =
          (∫ r in a..b, TpCont θ X₀ ω r) - ∫ r in a..b, (compDen θ X₀ ω r).toReal :=
        intervalIntegral.integral_sub hTi.1 hcR
      have hc0 : 0 ≤ ∫ r in a..b, (compDen θ X₀ ω r).toReal :=
        intervalIntegral.integral_nonneg hab fun _ _ => ENNReal.toReal_nonneg
      have hTe := hTi.2
      rw [max_eq_left haX] at hTe
      have hcup := F.win.cup a b haX hab
      have hDF : DF θ X₀ ω = DM M (Ucl ω) := rfl
      rw [hDF] at hTe
      have : (0 : ℝ) ≤ sigA M A' := Nat.cast_nonneg _
      rw [hm, hTe]; linarith
  rw [abs_le]; constructor <;> linarith


omit hev in
/-- **The inner part of `B_y` below `X₀`**: `x ∈ B_y` for `y < X₀ ≤ x ≤ y + H(y)/2 - 3/8`. -/
lemma mem_Bset_low {y x : ℝ} (hy : y < X₀) (hx : (X₀ : ℝ) ≤ x)
    (h2 : x ≤ y + Hc X₀ y / 2 - 3 / 8) : x ∈ Bset X₀ y := by
  have hm : Hc X₀ y ≤ Hc X₀ x := KR.WidthReal.Hc_mono hc.hX (by linarith)
  have h0 := Hc_nonneg (X₀ := X₀) x
  show x - Hc X₀ x / 2 ≤ y ∧ y < x + Hc X₀ x / 2
  constructor <;> linarith

set_option maxHeartbeats 3200000 in
/-- **The noise at a point below `X₀`** (Lemma 5.22 at `X₀⁻ ≤ y < X₀`): a.s., for every `t`, on
`Good(< t) ∩ NiceEv`, with `y + 2H(y) ≤ t`, `|ρ̃(y) - (B m)(y)| ≤ ν̄(y)`. -/
theorem rho_noise_low : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ y : ℝ, Xm X₀ ≤ y → y < X₀ → y + 2 * Hc X₀ y ≤ t →
      |rhoT θ X₀ ω y - Margin.Bavg (Hc X₀ y) (marginM θ X₀ ω) y| ≤ nuB X₀ y := by
  classical
  filter_upwards [e3Good_ae hc hev] with ω hω
  intro t hG hN y hy hyX ht
  have hE := hω t hG hN
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hbig := X₀_ge_two_pow hc.hX
  obtain ⟨F, hs1, hjit⟩ := model_facts hc hev hN
  set M := CM θ X₀ ω
  set H := Hc X₀ y with hHdef
  have hwmax : max y (X₀ : ℝ) = X₀ := max_eq_right hyX.le
  have hHy : H = capH X₀ X₀ := by rw [hHdef]; unfold Hc; rw [hwmax]
  have hHX : Hc X₀ X₀ = H := by rw [hHy]; exact Hc_eq le_rfl
  have hXm : Xm X₀ = X₀ - H / 2 := by rw [hHy]; rfl
  have hHg : 200 * Real.log X₀ + 200 ≤ H := by
    have := Hc_ge hc y; rwa [hwmax] at this
  have hlX : (10 : ℝ) ^ 8 ≤ Real.log X₀ := hc.hX
  have hHle : H ≤ X₀ / 10 ^ 7 := by have := Hc_le hc y; rwa [hwmax] at this
  have hH200 : 200 ≤ H := by linarith
  have hy0 : 0 < y := by linarith
  have hε := s2ε_ge hc y
  -- `ρ̃(y)` as a weighted slot count
  set Q := s2Q θ X₀ ω y 0
  set sl := s2sl θ X₀ ω y 0
  have hrep : rhoT θ X₀ ω y = Margin.Exact.rhoTilde Q sl (Hc X₀) y :=
    hS2rep_R hc ω y 0 y (by linarith)
  set QB := Q.filter fun q => sl q ∈ Bset X₀ y
  have hslX : ∀ q, (X₀ : ℝ) ≤ sl q := fun q => slotF_ge hc q ω
  have hrho : H * rhoT θ X₀ ω y = ∑ q ∈ QB, H / Hc X₀ (sl q) := by
    rw [hrep]; unfold Margin.Exact.rhoTilde
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : sl q - Hc X₀ (sl q) / 2 ≤ y ∧ y < sl q + Hc X₀ (sl q) / 2
    · rw [if_pos hq, if_pos (show sl q ∈ Bset X₀ y from hq), div_eq_mul_inv]
    · rw [if_neg hq, if_neg (show sl q ∉ Bset X₀ y from hq), mul_zero]
  have hσ : Margin.Exact.sigmaS Q sl (Bset X₀ y) = (QB.card : ℝ) := rfl
  -- the weights
  have hw : ∀ q ∈ QB, |H / Hc X₀ (sl q) - 1| ≤ 3.2 / H := by
    intro q hq
    have hB := (Finset.mem_filter.mp hq).2
    obtain ⟨k1, k2, -, -⟩ := Bset_near hc hB (hslX q)
    rw [Hc_eq (hslX q)]
    have hHs : 0 < capH X₀ (sl q) := by linarith
    rw [abs_le, div_sub_one hHs.ne']
    constructor
    · rw [le_div_iff₀ hHs]
      have : 3.2 / H * capH X₀ (sl q) ≤ 3.2 / H * (H + 5 / 4) := by gcongr
      have e : 3.2 / H * (H + 5 / 4) = 3.2 + 4 / H := by field_simp; ring
      have h4 : 0 ≤ 4 / H := by positivity
      nlinarith
    · rw [div_le_iff₀ hHs]
      have : 3.2 / H * (H - 1 / 4) ≤ 3.2 / H * capH X₀ (sl q) := by gcongr
      have e : 3.2 / H * (H - 1 / 4) = 3.2 - 0.8 / H := by field_simp; ring
      have h4 : 0.8 / H ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
  -- the count
  have hcard : (QB.card : ℝ) ≤ 1.03 * H := by
    refine (slot_window_card hc hev (ω := ω) QB (a₀ := y - H / 2 - 5 / 8)
      (b := y + H / 2 + 5 / 8) (ℓ := H + 5 / 4) (fun k hk => ?_) (by linarith)
      (by linarith)).trans (by nlinarith)
    obtain ⟨hkQ, hkB⟩ := Finset.mem_filter.mp hk
    obtain ⟨-, -, k3, k4⟩ := Bset_near hc hkB (hslX k)
    exact ⟨(mem_s2Q.mp hkQ).2, k3, k4⟩
  have hgran : |H * rhoT θ X₀ ω y - QB.card| ≤ 3.3 := by
    rw [hrho]
    have e : ∑ q ∈ QB, H / Hc X₀ (sl q) - (QB.card : ℝ) = ∑ q ∈ QB, (H / Hc X₀ (sl q) - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hw).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (QB.card : ℝ) * (3.2 / H) ≤ 1.03 * H * (3.2 / H) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have e2 : 1.03 * H * (3.2 / H) = 3.296 := by field_simp; ring
    linarith
  -- Step 1 on `B_y`
  have hHm := measurable_Hc hc (X₀ := X₀)
  have hfm : Measurable fun x : ℝ => x - Hc X₀ x / 2 := measurable_id.sub (hHm.div_const 2)
  have hfp : Measurable fun x : ℝ => x + Hc X₀ x / 2 := measurable_id.add (hHm.div_const 2)
  have hBm : MeasurableSet (Bset X₀ y) :=
    (measurableSet_le hfm measurable_const).inter (measurableSet_lt measurable_const hfp)
  have hBo : (Bset X₀ y ∩ Ici (X₀ : ℝ)).OrdConnected := by
    refine ⟨fun x hx w hw v hv => ⟨⟨?_, ?_⟩, hx.2.trans hv.1⟩⟩
    · exact (phiMinus_mono hc hv.2).trans hw.1.1
    · exact lt_of_lt_of_le hx.1.2 (phiPlus_mono hc hv.1)
  have hlog4 : Real.log (2 * (y - H / 2 - 5 / 8 + (H + 1 / 2) + 7 / 4)) ≤
      Real.log X₀ + 2 := by
    have h1 : 2 * (y - H / 2 - 5 / 8 + (H + 1 / 2) + 7 / 4) ≤ 4 * X₀ := by linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (x := 4) (y := (X₀ : ℝ)) (by norm_num) (by linarith)] at h2
    have h4 : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have hSM := set_margin_t hc hev hG hN hE (z := y) (s := H + 1 / 2)
    (P := y - H / 2 - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith) hBm hBo (fun x hx hxX => by
      obtain ⟨-, -, k3, k4⟩ := Bset_near hc hx hxX
      constructor <;> linarith)
  have hsigA : Margin.Exact.sigmaS Q sl (Bset X₀ y) = (sigA M (Bset X₀ y) : ℝ) :=
    sigmaS_eq hc hN (fun x hx hxX => by
      obtain ⟨-, -, -, k4⟩ := Bset_near hc hx hxX
      linarith)
  rw [← hsigA, hσ] at hSM
  -- `B_y ∩ [X₀, ∞)` is an interval `[X₀, b⟩` near `[X₀, y + H/2]`
  set B' := Bset X₀ y ∩ Ici (X₀ : ℝ)
  have hXB : (X₀ : ℝ) ∈ B' := by
    refine ⟨?_, mem_Ici.mpr le_rfl⟩
    show (X₀ : ℝ) - Hc X₀ X₀ / 2 ≤ y ∧ y < X₀ + Hc X₀ X₀ / 2
    rw [hHX]; constructor <;> linarith
  have hbb : BddBelow B' := ⟨X₀, fun x hx => hx.2⟩
  have hba : BddAbove B' := ⟨y + H / 2 + 5 / 8, fun x hx =>
    (Bset_near hc hx.1 hx.2).2.2.2⟩
  obtain ⟨hab, hIoo, hIcc, hint⟩ := ordconn_interval (f := marginM θ X₀ ω) hBo ⟨X₀, hXB⟩ hbb hba
  set a := sInf B'
  set b := sSup B'
  have haX : (X₀ : ℝ) ≤ a := le_csInf ⟨X₀, hXB⟩ fun x hx => hx.2
  have haX' : a ≤ X₀ := csInf_le hbb hXB
  have ha : a = X₀ := le_antisymm haX' haX
  have hb1 : b ≤ y + H / 2 + 5 / 8 := csSup_le ⟨X₀, hXB⟩ fun x hx =>
    (Bset_near hc hx.1 hx.2).2.2.2
  have hbX : (X₀ : ℝ) ≤ b := le_csSup hba hXB
  have hb2 : y + H / 2 - 3 / 8 ≤ b := by
    rcases le_total (X₀ : ℝ) (y + H / 2 - 3 / 8) with h | h
    · exact le_csSup hba ⟨mem_Bset_low hc hyX h (by linarith), mem_Ici.mpr h⟩
    · linarith
  -- the integrals
  have hmi : ∀ p q : ℝ, (X₀ : ℝ) ≤ q → p ≤ q →
      IntervalIntegrable (marginM θ X₀ ω) volume p q := fun p q hq hpq =>
    (integral_TpCont hc ω hpq hq).1.sub (compR_intervalIntegrable hc hev ω hpq)
  have hmi' : ∀ p q : ℝ, (X₀ : ℝ) ≤ p → (X₀ : ℝ) ≤ q →
      IntervalIntegrable (marginM θ X₀ ω) volume p q := fun p q hp hq => by
    rcases le_total p q with h | h
    · exact hmi p q hq h
    · exact (hmi q p hp h).symm
  -- the block of `y`: `u₁ ≤ X₀ < 2u₁`
  set m1 := m1z X₀ y
  obtain ⟨hm1a, hm1b⟩ := mB_spec (by linarith : (0 : ℝ) < X₀)
    (le_max_right (y - Hc X₀ y) (X₀ : ℝ))
  have hmx : max (y - H) (X₀ : ℝ) = X₀ := max_eq_right (by linarith)
  have hm1e : m1 = mB X₀ X₀ := by
    show mB X₀ (max (y - Hc X₀ y) X₀) = _; rw [← hHdef, hmx]
  have hu1 : uS X₀ m1 ≤ X₀ := by have := hm1a; rw [← hHdef, hmx] at this; rw [hm1e]; exact this
  have hu2 : (X₀ : ℝ) < 2 * uS X₀ m1 := by
    have := hm1b; rw [← hHdef, hmx, uS_succ] at this; rw [hm1e]; exact this
  have hU := uS_succ (X₀ := X₀) m1
  have hlogU : Real.log (2 * uS X₀ (m1 + 1)) ≤ 2 * Real.log (4 * y) := by
    have h1 : 2 * uS X₀ (m1 + 1) ≤ (4 * y) ^ 2 := by rw [hU]; nlinarith
    have := (uS_facts hc (m1 + 1)).1
    have h2 := Real.log_le_log (by linarith) h1
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  -- `|∫_p^q m| ≤ 1.01 + 300 log(4y)` on short pieces above `X₀`
  have hshort : ∀ p q : ℝ, (X₀ : ℝ) ≤ p → p ≤ q → q ≤ p + 1 →
      q ≤ y + H / 2 + 5 / 8 → |∫ r in p..q, marginM θ X₀ ω r| ≤ 1.01 + 300 * Real.log (4 * y) := by
    intro p q hpX hpq hq1 hq2
    obtain ⟨hTi, hTe⟩ := integral_TpCont hc ω hpq (by linarith)
    have hcR := compR_intervalIntegrable hc hev ω hpq
    have hm : (∫ r in p..q, marginM θ X₀ ω r) =
        (∫ r in p..q, TpCont θ X₀ ω r) - ∫ r in p..q, (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_sub hTi hcR
    have hc0 : 0 ≤ ∫ r in p..q, (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_nonneg hpq fun _ _ => ENNReal.toReal_nonneg
    have hcs := intc_short hc hev hE (m := m1) (hu1.trans hpX) hpq hq1
      (by rw [hU]; linarith) (by linarith)
    rw [max_eq_left hpX] at hTe
    have hcup := F.win.cup p q hpX hpq
    have hcm := F.win.cmono p q hpX hpq
    have hDF : DF θ X₀ ω = DM M (Ucl ω) := rfl
    rw [hDF] at hTe
    have hl0 : 0 ≤ Real.log (4 * y) := Real.log_nonneg (by linarith)
    rw [hm, hTe, abs_le]
    constructor <;> nlinarith
  have hp2 : |∫ r in (y + H / 2)..b, marginM θ X₀ ω r| ≤ 1.01 + 300 * Real.log (4 * y) := by
    rcases le_total (y + H / 2) b with h | h
    · exact hshort _ _ (by linarith) h (by linarith) hb1
    · rw [intervalIntegral.integral_symm, abs_neg]
      exact hshort _ _ hbX h (by linarith) (by linarith)
  -- `∫_W m = ∫_{X₀}^{y+H/2} m`
  have hW : (∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r) =
      ∫ r in (X₀ : ℝ)..(y + H / 2), marginM θ X₀ ω r := by
    have h : y - H / 2 ≤ (X₀ : ℝ) := by linarith
    have hz : (∫ r in (y - H / 2)..(X₀ : ℝ), marginM θ X₀ ω r) = 0 := by
      rw [intervalIntegral.integral_of_le h]
      refine setIntegral_eq_zero_of_ae_eq_zero ?_
      have hX : ∀ᵐ r ∂volume, r ≠ (X₀ : ℝ) := by
        have : volume ({(X₀ : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
        rw [ae_iff]; simp [this]
      filter_upwards [hX] with r hr hrI
      exact RML6.marginM_eq_zero_low hc ω (lt_of_le_of_ne hrI.2 hr)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hmi (y - H / 2) X₀ le_rfl h) (hmi X₀ (y + H / 2) (by linarith) (by linarith))
    rw [← hsplit, hz, zero_add]
  have hsplit2 : (∫ r in a..b, marginM θ X₀ ω r) =
      (∫ r in (X₀ : ℝ)..(y + H / 2), marginM θ X₀ ω r) +
        ∫ r in (y + H / 2)..b, marginM θ X₀ ω r := by
    rw [ha, intervalIntegral.integral_add_adjacent_intervals
      (hmi' X₀ (y + H / 2) le_rfl (by linarith)) (hmi' (y + H / 2) b (by linarith) hbX)]
  -- the final bound
  have hBav : Margin.Bavg H (marginM θ X₀ ω) y =
      H⁻¹ * ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r := rfl
  have hH0 : 0 < H := by linarith
  have key : |H * rhoT θ X₀ ω y - ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r| ≤
      s2ε X₀ y + 300 * Real.log (4 * y) + 6.4 := by
    rw [hW]
    have hint0 : ∫ r in Bset X₀ y, marginM θ X₀ ω r = ∫ r in B', marginM θ X₀ ω r :=
      setIntegral_eq_of_subset_of_forall_diff_eq_zero hBm inter_subset_left fun x hx => by
        have : x < X₀ := by
          by_contra h; push_neg at h; exact hx.2 ⟨hx.1, h⟩
        exact RML6.marginM_eq_zero_low hc ω this
    rw [hint0, hint, hsplit2] at hSM
    rw [abs_le] at hgran hSM hp2 ⊢
    constructor <;> linarith
  rw [hBav]
  unfold nuB
  rw [le_div_iff₀ hH0]
  have e : rhoT θ X₀ ω y - H⁻¹ * ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r =
      (H * rhoT θ X₀ ω y - ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r) / H := by
    field_simp
  rw [e, abs_div, abs_of_pos hH0, div_mul_cancel₀ _ hH0.ne']
  exact key

/-- **The noise at a point for `X₀⁻ ≤ y`** (`rho_noise` and `rho_noise_low`). -/
theorem rho_noise_Xm : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ y : ℝ, Xm X₀ ≤ y → y + 2 * Hc X₀ y ≤ t →
      |rhoT θ X₀ ω y - Margin.Bavg (Hc X₀ y) (marginM θ X₀ ω) y| ≤ nuB X₀ y := by
  filter_upwards [rho_noise hc hev, rho_noise_low hc hev] with ω h1 h2
  intro t hG hN y hy ht
  rcases lt_or_ge y X₀ with h | h
  · exact h2 t hG hN y hy h ht
  · exact h1 t hG hN y h ht

end Queue6

end
