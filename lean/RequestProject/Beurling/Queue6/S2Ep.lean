module

public import RequestProject.Beurling.Queue6.PhysMargin
public import RequestProject.Beurling.Queue6.Step2Count
public import RequestProject.Beurling.Noise.RML6Var
public import RequestProject.Beurling.Model.CapHSlope

/-!
# Proposition 5.38(a), Step 1 on the slot sets `A±`: the fields `hS2Ep`, `hS2Em`

For `ω ∈ Good(< t) ∩ NiceEv` (a.s.), `z` and `0 ≤ s ≤ 1.01 H(z)` with
`max(z, X₀) + 2 H(z) ≤ t`, the slot sets `A₊ = φ₋⁻¹((z, z+s])`, `A₋ = φ₊⁻¹((z, z+s])`
(`φ±(x) = x ± H(x)/2`) satisfy

`|σ(A±) - ∫_{A±} m| ≤ ε_z` (`hS2Epm_R`),

with `σ = sigmaS (s2Q z s) (s2sl z s)` (the slot measure of Step 2, `Queue6.Step2Count`) and

`ε_z = B(4 max(z, X₀)) + 6 + e(u₁) + e(2u₁)` (`s2ε`),

`u₁ = 2^{m₁} X₀` the dyadic block of `max(z - H(z), X₀)` (`mB`), `e` the block error of
`E3Real` (Freedman bounds (F1), (F2) at the maximal window length, `s₂(u) L_u`, and
`100 log(2u)` for the two partial unit windows), `B` the queue bound (75) (`queueB`).

The proof: `φ±` are non-decreasing (`H` is `4·10⁻⁷`-Lipschitz, `CapHSlope`), so
`A± ∩ [X₀, ∞)` is an interval `⟨a, b⟩` of length `≤ s + 3/4` near `z ± H(z)/2` (Step 2,
`H_near`); below `X₀` there are neither slots nor margin (`marginM_eq_zero_low`). Then
`σ([a + 1, b)) ≤ σ(A±) ≤ σ([a, b + 1))`, and `phys_margin` on these physical windows, with
`∫_{[b, b+1)} m, ∫_{[a, a+1)} m ≤ 1.01` (`T'_cont ≤ 1.01` on average, `c ≥ 0`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed
  SlotModel AbsorbEmpty QueueBound

namespace Queue6

open BModel

/-! ### The dyadic block of a height -/

section Block

variable (X₀ : ℕ)

open Classical in
/-- The dyadic block `m` of `x`: the least `m` with `x < 2^{m+1} X₀`. -/
noncomputable def mB (x : ℝ) : ℕ :=
  if h : ∃ m, x < uS X₀ (m + 1) then Nat.find h else 0

variable {X₀}

lemma mB_spec (hX0 : (0 : ℝ) < X₀) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    uS X₀ (mB X₀ x) ≤ x ∧ x < uS X₀ (mB X₀ x + 1) := by
  classical
  have hex : ∃ m, x < uS X₀ (m + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / X₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hX0] at hn
    unfold uS
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hm : mB X₀ x = Nat.find hex := by unfold mB; rw [dif_pos hex]
  rw [hm]
  refine ⟨?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; unfold uS; simpa using hx
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at this
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this

end Block

/-! ### The error `ε_z` -/

variable (X₀ : ℕ)

/-- The block `m₁(z)` of `max(z - H(z), X₀)`. -/
noncomputable def m1z (z : ℝ) : ℕ := mB X₀ (max (z - Hc X₀ z) X₀)

/-- **The error `ε_z` of Step 1 on `A±`**: `B(4 max(z, X₀)) + 6 + e(u₁) + e(2u₁)`. -/
noncomputable def s2ε (z : ℝ) : ℝ :=
  queueB X₀ (4 * max z X₀) + 6 + (eB X₀ (m1z X₀ z) + eB X₀ (m1z X₀ z + 1))

variable {X₀}

/-! ### The slot count of a set -/

/-- `σ(A)`: the primes placed at slots starting in `A`. -/
noncomputable def sigA {X₀ : ℕ} (M : SlotModel X₀) (A : Set ℝ) : ℕ :=
  {k | placedAt M k ∧ M.slot (k + 1) ∈ A}.ncard

lemma sigA_mono {X₀ : ℕ} {M : SlotModel X₀} {A B : Set ℝ} (hAB : A ⊆ B) {b : ℝ}
    (hB : B ⊆ Iic b) : sigA M A ≤ sigA M B :=
  Set.ncard_le_ncard (fun _ hk => ⟨hk.1, hAB hk.2⟩)
    ((finite_slot_succ_le (M := M) b).subset fun _ hk => hB hk.2)

lemma sigA_Ico {X₀ : ℕ} (M : SlotModel X₀) (α β : ℝ) : sigA M (Ico α β) = sigP M α β := by
  unfold sigA sigP; rfl

section Main

variable {θ : ℝ} (hc : Cond θ X₀) (hev : Even X₀)
include hc

omit hc in
lemma Hc_eq {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : Hc X₀ x = capH X₀ x := by
  unfold Hc; rw [max_eq_left hx]

omit hc in
lemma Hc_nonneg (z : ℝ) : 0 ≤ Hc X₀ z := capH_nonneg _ _

lemma Hc_le (z : ℝ) : Hc X₀ z ≤ max z X₀ / 10 ^ 7 := capH_le_div hc.hX (le_max_right _ _)

lemma Hc_ge (z : ℝ) : 200 * Real.log (max z X₀) + 200 ≤ Hc X₀ z :=
  log_le_capH (Nat.cast_nonneg _) hc.hX (le_max_right _ _)

/-- `H(max(z, X₀)) ≤ 1.00001 H(u₁)`. -/
lemma Hc_le_block (z : ℝ) : Hc X₀ z ≤ 1.00001 * capH X₀ (uS X₀ (m1z X₀ z)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set w := max z (X₀ : ℝ)
  set z1 := max (z - Hc X₀ z) (X₀ : ℝ)
  obtain ⟨h1, h2⟩ := mB_spec hX0p (le_max_right (z - Hc X₀ z) (X₀ : ℝ))
  set u := uS X₀ (m1z X₀ z)
  have hu1 : u ≤ z1 := h1
  have hu2 : z1 < 2 * u := by
    have := h2; unfold m1z at *; rw [uS_succ] at this; exact this
  have hHw : Hc X₀ z ≤ w / 10 ^ 7 := Hc_le hc z
  have hH0 := Hc_nonneg (X₀ := X₀) z
  have hz1w : z1 ≤ w := max_le_max (by linarith) le_rfl
  have hwz1 : w ≤ z1 + Hc X₀ z := by
    rcases le_total z (X₀ : ℝ) with h | h
    · have : w = X₀ := max_eq_right h
      rw [this]; have := le_max_right (z - Hc X₀ z) (X₀ : ℝ); linarith
    · have : w = z := max_eq_left h
      rw [this]; have := le_max_left (z - Hc X₀ z) (X₀ : ℝ); linarith
  have huX : (X₀ : ℝ) ≤ u := X₀_le_uS hX0p _
  have hu0 : 0 < u := by linarith
  have huw : u ≤ w := hu1.trans hz1w
  have hw3 : w ≤ 3 * u := by
    have : w ≤ 2 * u + w / 10 ^ 7 := by linarith
    linarith
  have hS := CapHSlopeProof.capHSlope hc.hX u w huX huw
  have hr : (w / u) ^ (4 / 1000000 : ℝ) ≤ 1 + 4 / 1000000 * (w / u - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := w / u - 1)
      (by have : 0 ≤ w / u := div_nonneg (by linarith) hu0.le; linarith)
      (by norm_num : (0 : ℝ) ≤ 4 / 1000000) (by norm_num : (4 / 1000000 : ℝ) ≤ 1)
    simpa using this
  have hwu : w / u ≤ 3 := by rw [div_le_iff₀ hu0]; linarith
  have hH0 := capH_nonneg (X₀ : ℝ) u
  have hcoef : (w / u) ^ (4 / 1000000 : ℝ) ≤ 1.00001 := by linarith
  have : Hc X₀ z = capH X₀ w := rfl
  rw [this]
  calc capH X₀ w ≤ (w / u) ^ (4 / 1000000 : ℝ) * capH X₀ u := hS
    _ ≤ 1.00001 * capH X₀ u := mul_le_mul_of_nonneg_right hcoef hH0

lemma s2ε_ge (z : ℝ) : 6 ≤ s2ε X₀ z := by
  have h1 := eB_nonneg hc (m1z X₀ z)
  have h2 := eB_nonneg hc (m1z X₀ z + 1)
  have h3 : 0 ≤ queueB X₀ (4 * max z X₀) := queueB_nonneg (Nat.cast_nonneg _) hc.hX (by
    have := le_max_right z (X₀ : ℝ); have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _; linarith)
  unfold s2ε; linarith

include hev

set_option maxHeartbeats 3200000 in
/-- **Step 1 on a set near `z`**: if `A` is measurable, `A ∩ [X₀, ∞)` is order-connected and
lies in `(P, P + s + 3/4]` with `z - H(z) ≤ P ≤ z + H(z)/2`, then `|σ(A) - ∫_A m| ≤ ε_z`. -/
theorem set_margin {ω : JitterΩ} {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) (hE : E3Good θ X₀ ω t) {z s P : ℝ} {A : Set ℝ}
    (hs : s ≤ 1.01 * Hc X₀ z) (ht : max z X₀ + 2 * Hc X₀ z ≤ t)
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
    have : Real.log (2 * β) ≤ Real.log (2 * (b + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    nlinarith
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

/-! ### The sets `A±` -/

omit hev in
/-- `φ₋(x) = x - H(x)/2` is non-decreasing. -/
lemma phiMinus_mono {x y : ℝ} (hxy : x ≤ y) : x - Hc X₀ x / 2 ≤ y - Hc X₀ y / 2 := by
  have h := KR.WidthReal.Hc_incr hc.hX (by norm_num : (0 : ℝ) ≤ 4 / 1000000)
    (by norm_num) (CapHSlopeProof.capHSlope hc.hX) hxy
  linarith

omit hev in
/-- `φ₊(x) = x + H(x)/2` is non-decreasing. -/
lemma phiPlus_mono {x y : ℝ} (hxy : x ≤ y) : x + Hc X₀ x / 2 ≤ y + Hc X₀ y / 2 := by
  have h := KR.WidthReal.Hc_mono hc.hX hxy
  linarith

omit hev in
lemma measurable_Hc : Measurable (Hc X₀) := measurable_capH_max hc.hX

omit hev in
/-- The bounds of `A₊ ∩ [X₀, ∞)`: `(z + H/2 - 1/8, z + s + H/2 + 5/8]`. -/
lemma Aplus_bounds {z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * Hc X₀ z) :
    ∀ x ∈ Margin.Exact.Aplus (Hc X₀) z s, (X₀ : ℝ) ≤ x →
      z + Hc X₀ z / 2 - 1 / 8 < x ∧ x ≤ z + Hc X₀ z / 2 - 1 / 8 + s + 3 / 4 := by
  intro x hx hxX
  obtain ⟨h1, h2⟩ := A_near hs0 hs hxX (Or.inl hx)
  obtain ⟨hup, hlo⟩ := H_near hc hxX h1
  have hlo' := hlo h2
  have hHx := Hc_eq (X₀ := X₀) hxX
  obtain ⟨k1, k2⟩ := hx
  rw [hHx] at k1 k2
  constructor <;> linarith

omit hev in
/-- The bounds of `A₋ ∩ [X₀, ∞)`: `(z - H/2 - 5/8, z + s - H/2 + 1/8]`. -/
lemma Aminus_bounds {z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * Hc X₀ z) :
    ∀ x ∈ Margin.Exact.Aminus (Hc X₀) z s, (X₀ : ℝ) ≤ x →
      z - Hc X₀ z / 2 - 5 / 8 < x ∧ x ≤ z - Hc X₀ z / 2 - 5 / 8 + s + 3 / 4 := by
  intro x hx hxX
  obtain ⟨h1, h2⟩ := A_near hs0 hs hxX (Or.inr hx)
  obtain ⟨hup, hlo⟩ := H_near hc hxX h1
  have hlo' := hlo h2
  have hHx := Hc_eq (X₀ := X₀) hxX
  obtain ⟨k1, k2⟩ := hx
  rw [hHx] at k1 k2
  constructor <;> linarith

omit hev in
/-- The slot measure of Step 2 is `sigA` on the sets near `z` (on `NiceEv`). -/
lemma sigmaS_eq {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {z s : ℝ} {A : Set ℝ}
    (hA : ∀ x ∈ A, (X₀ : ℝ) ≤ x → x ≤ 2 * (z + s) + 2) :
    Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) A = (sigA (CM θ X₀ ω) A : ℝ) := by
  classical
  unfold Margin.Exact.sigmaS sigA
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext k
  simp only [Finset.coe_filter, mem_setOf_eq, mem_s2Q, s2sl]
  have hsg : ω ∈ stageGood θ X₀ k := by
    have := hN.2.1; simp only [SG, mem_iInter] at this; exact this k
  have hX := slotF_ge hc k ω
  constructor
  · rintro ⟨⟨-, hA'⟩, hk⟩
    exact ⟨hA'.1, hk⟩
  · rintro ⟨hp, hk⟩
    exact ⟨⟨hA _ hk hX, ⟨hp, hsg⟩⟩, hk⟩

include hev

set_option maxHeartbeats 1600000 in
/-- **The fields `hS2Ep`, `hS2Em`** (Proposition 5.38(a), Step 1 on `A±`): a.s., for every `t`,
on `Good(< t) ∩ NiceEv`, for every `z` and `0 ≤ s ≤ 1.01 H(z)` with `max(z, X₀) + 2H(z) ≤ t`,
`|σ(A±) - ∫_{A±} m| ≤ ε_z`. -/
theorem hS2Epm_R : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ z s : ℝ, 0 ≤ s → s ≤ 1.01 * Hc X₀ z → max z X₀ + 2 * Hc X₀ z ≤ t →
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aplus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z ∧
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aminus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z := by
  filter_upwards [e3Good_ae hc hev] with ω hω
  intro t hG hN z s hs0 hs ht
  have hE := hω t hG hN
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hHw : Hc X₀ z ≤ max z X₀ / 10 ^ 7 := Hc_le hc z
  have hHg := Hc_ge hc z
  have hlw : 10 ^ 8 ≤ Real.log (max z X₀) :=
    (logs_of_ge hX0 hc.hX (le_max_right z (X₀ : ℝ))).1
  have hHm := measurable_Hc hc (X₀ := X₀)
  have hfm : Measurable fun x : ℝ => x - Hc X₀ x / 2 := measurable_id.sub (hHm.div_const 2)
  have hfp : Measurable fun x : ℝ => x + Hc X₀ x / 2 := measurable_id.add (hHm.div_const 2)
  -- the slots of a set near `z` are counted by `s2Q`
  have hnear : ∀ P : ℝ, P ≤ z + Hc X₀ z / 2 → ∀ x : ℝ, (X₀ : ℝ) ≤ x → x ≤ P + s + 3 / 4 →
      x ≤ 2 * (z + s) + 2 := by
    intro P hP x hx1 hx2
    rcases le_total z (X₀ : ℝ) with h | h
    · rw [max_eq_right h] at hHw; nlinarith
    · rw [max_eq_left h] at hHw; nlinarith
  constructor
  · have hb := Aplus_bounds hc hs0 hs
    rw [sigmaS_eq hc hN (fun x hx hxX => hnear _ le_rfl x hxX (by
      have := (hb x hx hxX).2; linarith))]
    refine set_margin hc hev hG hN hE hs ht (P := z + Hc X₀ z / 2 - 1 / 8) (by linarith)
      (by linarith) ((measurableSet_lt measurable_const hfm).inter
        (measurableSet_le hfm measurable_const)) ?_ hb
    refine ⟨fun x hx y hy w hw => ⟨⟨?_, ?_⟩, hx.2.trans hw.1⟩⟩
    · exact lt_of_lt_of_le hx.1.1 (phiMinus_mono hc hw.1)
    · exact (phiMinus_mono hc hw.2).trans hy.1.2
  · have hb := Aminus_bounds hc hs0 hs
    rw [sigmaS_eq hc hN (fun x hx hxX => hnear (z - Hc X₀ z / 2 - 5 / 8) (by linarith) x hxX (by
      have := (hb x hx hxX).2; linarith))]
    refine set_margin hc hev hG hN hE hs ht (P := z - Hc X₀ z / 2 - 5 / 8) (by linarith)
      (by linarith) ((measurableSet_lt measurable_const hfp).inter
        (measurableSet_le hfp measurable_const)) ?_ hb
    refine ⟨fun x hx y hy w hw => ⟨⟨?_, ?_⟩, hx.2.trans hw.1⟩⟩
    · exact lt_of_lt_of_le hx.1.1 (phiPlus_mono hc hw.1)
    · exact (phiPlus_mono hc hw.2).trans hy.1.2

end Main

end Queue6

end
