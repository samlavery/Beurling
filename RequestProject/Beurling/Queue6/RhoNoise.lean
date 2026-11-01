module

public import RequestProject.Beurling.Queue6.S2Err

/-!
# Lemma 5.22, the noise at a point: `|ρ̃(y) - (B m)(y)| ≤ ν̄(y)`

For `ω ∈ Good(< t) ∩ NiceEv` (a.s.) and `X₀ ≤ y` with `y + 2H(y) ≤ t`:

`|ρ̃(y) - H(y)⁻¹ ∫_{y-H/2}^{y+H/2} m| ≤ ν̄(y) = (ε_y + 150 log(4y) · 2 + 6.4)/H(y)` (`rho_noise`).

This is the slot granularity of the margin identity: `H(y) ρ̃(y) = ∑_{s_q ∈ B_y} H(y)/H(s_q)`
over the slots whose box contains `y`, `B_y = {x : x - H(x)/2 ≤ y < x + H(x)/2}`; the weights
are `1 + O(1/H)` (`H_near`), so `H(y) ρ̃(y) = σ(B_y) ± 3.3`; `σ(B_y) = ∫_{B_y} m ± ε_y`
(`set_margin`, Step 1 on the physical interval `B_y`); and `B_y ∩ [X₀, ∞)` is an interval whose
ends are within `5/8` of `y ± H(y)/2`, where `|∫ m| ≤ 1.01 + ∫ c` and `∫ c ≤ 150 log(4y)` on a
piece of length `≤ 1` (`intc_short`, from `E3Good`).

* `rho_noise` : the bound above (the `|ν| ≤ ν̄` input of Lemma 5.22 for `ν = ρ̃ - B m + …`);
* `nu_of_dec` : with any decomposition `ρ̃ + ν + NT = B m + B_t` (the field `hdec`),
  `|ν| ≤ ν̄ + |NT| + |B_t|`;
* `nuB_le` : `ν̄(y) ≤ 1.1 s₂(u₁) + 1.1 s₂(2u₁) + 106 L₁^{-6}`, `L₁ = log u₁` (`s2ε_le`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable (X₀ : ℕ)

/-- The slots whose box contains `y`: `B_y = {x : x - H(x)/2 ≤ y < x + H(x)/2}`. -/
def Bset (y : ℝ) : Set ℝ := {x | x - Hc X₀ x / 2 ≤ y ∧ y < x + Hc X₀ x / 2}

/-- **The noise bound** `ν̄(y) = (ε_y + 300 log(4y) + 6.4)/H(y)`. -/
noncomputable def nuB (y : ℝ) : ℝ :=
  (s2ε X₀ y + 300 * Real.log (4 * y) + 6.4) / Hc X₀ y

variable {X₀}

/-- **An order-connected set**: its integral is the interval integral between its ends. -/
lemma ordconn_interval {f : ℝ → ℝ} {A : Set ℝ} (hA : A.OrdConnected) (hne : A.Nonempty)
    (hbb : BddBelow A) (hba : BddAbove A) :
    sInf A ≤ sSup A ∧ Ioo (sInf A) (sSup A) ⊆ A ∧ A ⊆ Icc (sInf A) (sSup A) ∧
      ∫ r in A, f r = ∫ r in (sInf A)..(sSup A), f r := by
  have hab : sInf A ≤ sSup A := csInf_le_csSup hne hbb hba
  have hIoo : Ioo (sInf A) (sSup A) ⊆ A := fun x hx => by
    obtain ⟨p, hp, hpx⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨q, hq, hxq⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hA.out hp hq ⟨hpx.le, hxq.le⟩
  have hIcc : A ⊆ Icc (sInf A) (sSup A) := subset_Icc_csInf_csSup hbb hba
  refine ⟨hab, hIoo, hIcc, ?_⟩
  have hae : A =ᵐ[volume] Icc (sInf A) (sSup A) := by
    refine Filter.EventuallyLE.antisymm hIcc.eventuallyLE ?_
    exact (Ioo_ae_eq_Icc (μ := volume)).symm.le.trans hIoo.eventuallyLE
  rw [setIntegral_congr_set hae, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

variable {θ : ℝ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1600000 in
/-- **`∫ c` on a short piece**: `∫_p^q c ≤ 150 log(2u₂)` for `u ≤ p ≤ q ≤ p + 1`,
`q + 2 ≤ 2u₂`, `u₂ = 2u`, on `E3Good ω t`, `q + 3 ≤ t`. -/
theorem intc_short {ω : JitterΩ} {t : ℕ} (hE : E3Good θ X₀ ω t) {m : ℕ} {p q : ℝ}
    (hp : uS X₀ m ≤ p) (hpq : p ≤ q) (hq1 : q ≤ p + 1) (hq2 : q + 2 ≤ 2 * uS X₀ (m + 1))
    (ht : q + 3 ≤ t) :
    ∫ r in p..q, (compDen θ X₀ ω r).toReal ≤ 150 * Real.log (2 * uS X₀ (m + 1)) := by
  set c : ℝ → ℝ := fun r => (compDen θ X₀ ω r).toReal
  have hc0 : ∀ r, 0 ≤ c r := fun r => ENNReal.toReal_nonneg
  have hint : ∀ a b : ℝ, IntervalIntegrable c volume a b := fun a b => by
    rcases le_total a b with h | h
    · exact compR_intervalIntegrable hc hev ω h
    · exact (compR_intervalIntegrable hc hev ω h).symm
  have hmono : ∀ a b r s : ℝ, a ≤ b → b ≤ r → r ≤ s → (∫ y in b..r, c y) ≤ ∫ y in a..s, c y :=
    fun a b r s h1 h2 h3 => intervalIntegral.integral_mono_interval h1 h2 h3
      (Filter.Eventually.of_forall fun y => hc0 y) (hint a s)
  obtain ⟨huX, hl, -, -⟩ := uS_facts hc m
  obtain ⟨huX', hl', -, -⟩ := uS_facts hc (m + 1)
  have hU := uS_succ (X₀ := X₀) m
  have hX1 := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hlog1 : Real.log (2 * uS X₀ m) ≤ Real.log (2 * uS X₀ (m + 1)) :=
    Real.log_le_log (by linarith) (by rw [hU]; linarith)
  have hlog0 : 0 < Real.log (2 * uS X₀ m) := Real.log_pos (by linarith)
  set nU : ℤ := ((2 ^ m * X₀ : ℕ) : ℤ)
  have hnU : (nU : ℝ) = uS X₀ m := (uS_int m).symm
  set nU' : ℤ := ((2 ^ (m + 1) * X₀ : ℕ) : ℤ)
  have hnU' : (nU' : ℝ) = uS X₀ (m + 1) := (uS_int (m + 1)).symm
  set n := ⌊p⌋
  have hn1 : (n : ℝ) ≤ p := Int.floor_le p
  have hn2 : p < (n : ℝ) + 1 := Int.lt_floor_add_one p
  have hUn : nU ≤ n := Int.le_floor.mpr (by rw [hnU]; exact hp)
  have hcast : ∀ a b : ℤ, ((b - a : ℤ) : ℝ) = (b : ℝ) - a := fun a b => by push_cast; ring
  have hLen : ∀ k : ℕ, (2 : ℝ) ≤ LenB X₀ k := fun k => by
    unfold LenB; have := (uS_facts hc k).2.2.1; linarith
  have htn : ∀ b : ℤ, (b : ℝ) ≤ n + 2 → b.toNat < t := fun b hb => by
    have h1 : (b : ℝ) < t := by linarith
    have h2 : b < (t : ℤ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < t := by linarith
    have h4 : (0 : ℤ) < t := by exact_mod_cast h3
    omega
  have hqn : q ≤ (n : ℝ) + 2 := by linarith
  have hpos : 0 ≤ ∫ y in (n : ℝ)..((n : ℝ) + 2), c y :=
    intervalIntegral.integral_nonneg (by linarith) fun y _ => hc0 y
  have hle : (∫ y in p..q, c y) ≤ ∫ y in (n : ℝ)..((n : ℝ) + 2), c y :=
    hmono _ _ _ _ hn1 hpq hqn
  refine hle.trans ?_
  -- the integer window `[n, n + 2)` is covered by at most two windows of `𝒲'`
  rcases le_or_gt (n + 2) nU' with h1 | h1
  · have hW := (hE m n (n + 2) (by rw [← hnU]; exact_mod_cast hUn) (by omega)
      (by have : ((n + 2 : ℤ) : ℝ) ≤ nU' := by exact_mod_cast h1
          rw [hnU', hU] at this; push_cast at this ⊢; linarith)
      (by rw [hcast]; push_cast; linarith [hLen m]) (htn _ (by push_cast; linarith))).1
    rw [hcast] at hW; push_cast at hW
    have : (∫ y in (n : ℝ)..((n : ℝ) + 2), c y) ≤ 50 * Real.log (2 * uS X₀ m) * 2 := by
      have e : (n : ℝ) + 2 - n = 2 := by ring
      rw [e] at hW; exact hW
    nlinarith
  · rcases le_or_gt nU' n with h2 | h2
    · have hW := (hE (m + 1) n (n + 2) (by rw [← hnU']; exact_mod_cast h2) (by omega)
        (by have : (n : ℝ) + 2 ≤ 2 * uS X₀ (m + 1) := by linarith
            push_cast; linarith)
        (by rw [hcast]; push_cast; linarith [hLen (m + 1)]) (htn _ (by push_cast; linarith))).1
      rw [hcast] at hW; push_cast at hW
      have e : (n : ℝ) + 2 - n = 2 := by ring
      rw [e] at hW
      have : 0 < Real.log (2 * uS X₀ (m + 1)) := by linarith
      nlinarith
    · -- `n < U < n + 2`
      have hW1 := (hE m n nU' (by rw [← hnU]; exact_mod_cast hUn) h2.le
        (by rw [hnU', hU])
        (by rw [hcast]
            have : ((nU' - n : ℤ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : nU' - n ≤ 2)
            push_cast at this ⊢; linarith [hLen m])
        (htn _ (by have : ((nU' : ℤ) : ℝ) ≤ n + 2 := by exact_mod_cast h1.le
                   exact this))).1
      have hW2 := (hE (m + 1) nU' (n + 2) (by rw [hnU']) h1.le
        (by have : (n : ℝ) + 2 ≤ 2 * uS X₀ (m + 1) := by linarith
            push_cast; linarith)
        (by rw [hcast]
            have : ((n + 2 - nU' : ℤ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : n + 2 - nU' ≤ 2)
            push_cast at this ⊢; linarith [hLen (m + 1)])
        (htn _ (by push_cast; linarith))).1
      rw [hcast] at hW1 hW2
      push_cast at hW1 hW2
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint (n : ℝ) (nU' : ℝ)) (hint (nU' : ℝ) ((n : ℝ) + 2))
      have hd1 : ((nU' : ℝ) - n) ≤ 2 := by
        have : ((nU' - n : ℤ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : nU' - n ≤ 2)
        push_cast at this; linarith
      have hd2 : ((n : ℝ) + 2 - nU') ≤ 2 := by
        have : ((n + 2 - nU' : ℤ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : n + 2 - nU' ≤ 2)
        push_cast at this; linarith
      have hd10 : (0 : ℝ) ≤ (nU' : ℝ) - n := by
        have : (n : ℝ) < nU' := by exact_mod_cast h2
        linarith
      have hd20 : (0 : ℝ) ≤ (n : ℝ) + 2 - nU' := by
        have : ((nU' : ℤ) : ℝ) < n + 2 := by exact_mod_cast h1
        linarith
      have hsum : ((nU' : ℝ) - n) + ((n : ℝ) + 2 - nU') = 2 := by ring
      have : 0 < Real.log (2 * uS X₀ (m + 1)) := by linarith
      rw [← hsplit]
      nlinarith

omit hev in
/-- **The weights of `B_y`**: `|H(y)/H(s) - 1| ≤ 3.2/H(y)` for `s ∈ B_y`, `s ≥ X₀`, and
`B_y ∩ [X₀, ∞) ⊂ (y - H/2 - 5/8, y + H/2 + 5/8]`. -/
lemma Bset_near {y : ℝ} {s : ℝ} (hs : s ∈ Bset X₀ y) (hsX : (X₀ : ℝ) ≤ s) :
    Hc X₀ y - 1 / 4 ≤ capH X₀ s ∧ capH X₀ s ≤ Hc X₀ y + 5 / 4 ∧
      y - Hc X₀ y / 2 - 5 / 8 < s ∧ s ≤ y + Hc X₀ y / 2 + 5 / 8 := by
  have hHs : Hc X₀ s = capH X₀ s := Hc_eq hsX
  obtain ⟨h1, h2⟩ := hs
  rw [hHs] at h1 h2
  have hH0 := capH_nonneg (X₀ : ℝ) s
  have hHy0 := Hc_nonneg (X₀ := X₀) y
  obtain ⟨hup, hlo⟩ := H_near hc hsX (z := y)
    (by have := le_max_left y (X₀ : ℝ); nlinarith)
  have hlo' := hlo (by linarith)
  refine ⟨hlo', hup, by linarith, by linarith⟩

omit hev in
/-- **The inner part of `B_y`**: `x ∈ B_y` for `X₀ ≤ x`, `|x - y| ≤ H(y)/2 - 3/8`. -/
lemma mem_Bset {y x : ℝ} (hy : (X₀ : ℝ) ≤ y) (hx : (X₀ : ℝ) ≤ x)
    (h1 : y - Hc X₀ y / 2 + 3 / 8 ≤ x) (h2 : x ≤ y + Hc X₀ y / 2 - 3 / 8) : x ∈ Bset X₀ y := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hHx : Hc X₀ x = capH X₀ x := Hc_eq hx
  have hHy : Hc X₀ y = capH X₀ y := Hc_eq hy
  rw [hHy] at h1 h2
  show x - Hc X₀ x / 2 ≤ y ∧ y < x + Hc X₀ x / 2
  rw [hHx]
  rcases le_total x y with h | h
  · have hm := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hx) (mem_Ici.mpr hy) h
    have hr := JitterRegular.capH_regular hX0 hc.hX hx h (by linarith)
    constructor <;> linarith
  · have hm := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hy) (mem_Ici.mpr hx) h
    have hr := JitterRegular.capH_regular hX0 hc.hX hy h (by linarith)
    constructor <;> linarith

set_option maxHeartbeats 3200000 in
/-- **The noise at a point** (Lemma 5.22): a.s., for every `t`, on `Good(< t) ∩ NiceEv`, for
`X₀ ≤ y` with `y + 2H(y) ≤ t`, `|ρ̃(y) - (B m)(y)| ≤ ν̄(y)`. -/
theorem rho_noise : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ y : ℝ, (X₀ : ℝ) ≤ y → y + 2 * Hc X₀ y ≤ t →
      |rhoT θ X₀ ω y - Margin.Bavg (Hc X₀ y) (marginM θ X₀ ω) y| ≤ nuB X₀ y := by
  classical
  filter_upwards [e3Good_ae hc hev] with ω hω
  intro t hG hN y hy ht
  have hE := hω t hG hN
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hbig := X₀_ge_two_pow hc.hX
  obtain ⟨F, hs1, hjit⟩ := model_facts hc hev hN
  set M := CM θ X₀ ω
  set H := Hc X₀ y with hHdef
  have hHy : H = capH X₀ y := Hc_eq hy
  have hHg : 200 * Real.log y + 200 ≤ H := by
    have := Hc_ge hc y; rwa [max_eq_left hy] at this
  have hly : 10 ^ 8 ≤ Real.log y := (logs_of_ge hX0 hc.hX hy).1
  have hHle : H ≤ y / 10 ^ 7 := by have := Hc_le hc y; rwa [max_eq_left hy] at this
  have hH200 : 200 ≤ H := by linarith
  have hε := s2ε_ge hc y
  have hwmax : max y (X₀ : ℝ) = y := max_eq_left hy
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
  have hSM := set_margin hc hev hG hN hE (z := y) (s := H + 1 / 2)
    (P := y - H / 2 - 5 / 8) (by linarith) (by rw [hwmax]; linarith) (by linarith)
    (by linarith) hBm hBo (fun x hx hxX => by
      obtain ⟨-, -, k3, k4⟩ := Bset_near hc hx hxX
      constructor <;> linarith)
  have hsigA : Margin.Exact.sigmaS Q sl (Bset X₀ y) = (sigA M (Bset X₀ y) : ℝ) :=
    sigmaS_eq hc hN (fun x hx hxX => by
      obtain ⟨-, -, -, k4⟩ := Bset_near hc hx hxX
      linarith)
  rw [← hsigA, hσ] at hSM
  -- `B_y ∩ [X₀, ∞)` is an interval near `[y - H/2, y + H/2]`
  set B' := Bset X₀ y ∩ Ici (X₀ : ℝ)
  have hyB : y ∈ B' := ⟨mem_Bset hc hy hy (by linarith) (by linarith), hy⟩
  have hbb : BddBelow B' := ⟨X₀, fun x hx => hx.2⟩
  have hba : BddAbove B' := ⟨y + H / 2 + 5 / 8, fun x hx =>
    (Bset_near hc hx.1 hx.2).2.2.2⟩
  obtain ⟨hab, hIoo, hIcc, hint⟩ := ordconn_interval (f := marginM θ X₀ ω) hBo ⟨y, hyB⟩ hbb hba
  set a := sInf B'
  set b := sSup B'
  have haX : (X₀ : ℝ) ≤ a := le_csInf ⟨y, hyB⟩ fun x hx => hx.2
  have ha1 : y - H / 2 - 5 / 8 ≤ a := le_csInf ⟨y, hyB⟩ fun x hx =>
    (Bset_near hc hx.1 hx.2).2.2.1.le
  have hb1 : b ≤ y + H / 2 + 5 / 8 := csSup_le ⟨y, hyB⟩ fun x hx =>
    (Bset_near hc hx.1 hx.2).2.2.2
  set c1 := max (y - H / 2 + 3 / 8) (X₀ : ℝ)
  have hc1 : c1 ∈ B' := ⟨mem_Bset hc hy (le_max_right _ _) (le_max_left _ _)
    (max_le (by linarith) (by linarith)), mem_Ici.mpr (le_max_right _ _)⟩
  have ha2 : a ≤ c1 := csInf_le hbb hc1
  have hc1le : c1 ≤ y := max_le (by linarith) hy
  have hc2 : y + H / 2 - 3 / 8 ∈ B' := ⟨mem_Bset hc hy (by linarith) (by linarith)
    (by linarith), mem_Ici.mpr (by linarith)⟩
  have hb2 : y + H / 2 - 3 / 8 ≤ b := le_csSup hba hc2
  -- the integrals
  have hmi : ∀ p q : ℝ, (X₀ : ℝ) ≤ q → p ≤ q →
      IntervalIntegrable (marginM θ X₀ ω) volume p q := fun p q hq hpq =>
    (integral_TpCont hc ω hpq hq).1.sub (compR_intervalIntegrable hc hev ω hpq)
  have hmi' : ∀ p q : ℝ, (X₀ : ℝ) ≤ p → (X₀ : ℝ) ≤ q →
      IntervalIntegrable (marginM θ X₀ ω) volume p q := fun p q hp hq => by
    rcases le_total p q with h | h
    · exact hmi p q hq h
    · exact (hmi q p hp h).symm
  -- the block of `y`
  set m1 := m1z X₀ y
  obtain ⟨hm1a, hm1b⟩ := mB_spec (by linarith : (0 : ℝ) < X₀)
    (le_max_right (y - Hc X₀ y) (X₀ : ℝ))
  have hu1 : uS X₀ m1 ≤ max (y - H) X₀ := hm1a
  have hu2 : max (y - H) X₀ < 2 * uS X₀ m1 := by
    have := hm1b; rw [uS_succ] at this; exact this
  have hU := uS_succ (X₀ := X₀) m1
  have hUy : 2 * uS X₀ (m1 + 1) ≤ 4 * y := by
    rw [hU]
    have : uS X₀ m1 ≤ y := hu1.trans (max_le (by linarith) hy)
    linarith
  have hlogU : Real.log (2 * uS X₀ (m1 + 1)) ≤ Real.log (4 * y) := by
    have := (uS_facts hc (m1 + 1)).1
    exact Real.log_le_log (by linarith) hUy
  have hUbig : y + H / 2 + 5 / 8 + 3 ≤ 2 * uS X₀ (m1 + 1) := by
    rw [hU]
    have : max (y - H) (X₀ : ℝ) ≥ y - H := le_max_left _ _
    nlinarith
  -- `|∫_p^q m| ≤ 1.01 + 150 log(4y)` on short pieces
  have hshort : ∀ p q : ℝ, max (y - H / 2 - 5 / 8) X₀ ≤ p → p ≤ q → q ≤ p + 1 →
      q ≤ y + H / 2 + 5 / 8 → |∫ r in p..q, marginM θ X₀ ω r| ≤ 1.01 + 150 * Real.log (4 * y) := by
    intro p q hp hpq hq1 hq2
    have hpX : (X₀ : ℝ) ≤ p := le_trans (le_max_right _ _) hp
    obtain ⟨hTi, hTe⟩ := integral_TpCont hc ω hpq (by linarith)
    have hcR := compR_intervalIntegrable hc hev ω hpq
    have hm : (∫ r in p..q, marginM θ X₀ ω r) =
        (∫ r in p..q, TpCont θ X₀ ω r) - ∫ r in p..q, (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_sub hTi hcR
    have hc0 : 0 ≤ ∫ r in p..q, (compDen θ X₀ ω r).toReal :=
      intervalIntegral.integral_nonneg hpq fun _ _ => ENNReal.toReal_nonneg
    have hcs := intc_short hc hev hE (m := m1) (le_trans (hu1.trans (max_le_max (by linarith)
      le_rfl)) hp) hpq hq1 (by linarith) (by linarith)
    rw [max_eq_left hpX] at hTe
    have hcup := F.win.cup p q hpX hpq
    have hcm := F.win.cmono p q hpX hpq
    have hDF : DF θ X₀ ω = DM M (Ucl ω) := rfl
    rw [hDF] at hTe
    have hl0 : 0 ≤ Real.log (4 * y) := Real.log_nonneg (by linarith)
    rw [hm, hTe, abs_le]
    constructor <;> nlinarith
  have hshort' : ∀ p q : ℝ, max (y - H / 2 - 5 / 8) X₀ ≤ p → max (y - H / 2 - 5 / 8) X₀ ≤ q →
      |p - q| ≤ 1 → p ≤ y + H / 2 + 5 / 8 → q ≤ y + H / 2 + 5 / 8 →
      |∫ r in p..q, marginM θ X₀ ω r| ≤ 1.01 + 150 * Real.log (4 * y) := by
    intro p q hp hq hpq h1 h2
    rw [abs_le] at hpq
    rcases le_total p q with h | h
    · exact hshort p q hp h (by linarith) h2
    · rw [intervalIntegral.integral_symm, abs_neg]
      exact hshort q p hq h (by linarith) h1
  -- assemble: `∫_W m = ∫_{w₁}^{y+H/2} m`, `w₁ = max(y - H/2, X₀)`
  set w1 := max (y - H / 2) (X₀ : ℝ)
  have hw1X : (X₀ : ℝ) ≤ w1 := le_max_right _ _
  have hW : (∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r) =
      ∫ r in w1..(y + H / 2), marginM θ X₀ ω r := by
    rcases le_total (y - H / 2) (X₀ : ℝ) with h | h
    · have hw : w1 = X₀ := max_eq_right h
      rw [hw]
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
    · rw [show w1 = y - H / 2 from max_eq_left h]
  have hsplit3 : (∫ r in a..b, marginM θ X₀ ω r) = (∫ r in a..w1, marginM θ X₀ ω r) +
      (∫ r in w1..(y + H / 2), marginM θ X₀ ω r) +
        ∫ r in (y + H / 2)..b, marginM θ X₀ ω r := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hmi' a w1 haX hw1X)
        (hmi' w1 (y + H / 2) hw1X (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals (hmi' a (y + H / 2) haX (by linarith))
        (hmi' (y + H / 2) b (by linarith) (by linarith))]
  have hlo : max (y - H / 2 - 5 / 8) (X₀ : ℝ) ≤ a := max_le ha1 haX
  have hlo1 : max (y - H / 2 - 5 / 8) (X₀ : ℝ) ≤ w1 :=
    max_le_max (by linarith) le_rfl
  have hmm : max (y - H / 2 + 3 / 8) (X₀ : ℝ) ≤ max (y - H / 2 - 5 / 8) (X₀ : ℝ) + 1 :=
    max_le (by linarith [le_max_left (y - H / 2 - 5 / 8) (X₀ : ℝ)])
      (by linarith [le_max_right (y - H / 2 - 5 / 8) (X₀ : ℝ)])
  have hw1le : w1 ≤ max (y - H / 2 + 3 / 8) (X₀ : ℝ) := max_le_max (by linarith) le_rfl
  have hp1 := hshort' a w1 hlo hlo1 (by rw [abs_le]; constructor <;> linarith)
    (by linarith) (max_le (by linarith) (by linarith))
  have hp2 := hshort' (y + H / 2) b (le_trans (max_le (by linarith) (by linarith)) le_rfl)
    (le_trans (max_le (by linarith) (by linarith)) hb2)
    (by rw [abs_le]; constructor <;> linarith) (by linarith) hb1
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
    rw [hint0, hint, hsplit3] at hSM
    rw [abs_le] at hgran hSM hp1 hp2 ⊢
    constructor <;> linarith
  rw [hBav]
  unfold nuB
  rw [le_div_iff₀ hH0]
  have e : rhoT θ X₀ ω y - H⁻¹ * ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r =
      (H * rhoT θ X₀ ω y - ∫ r in (y - H / 2)..(y + H / 2), marginM θ X₀ ω r) / H := by
    field_simp
  rw [e, abs_div, abs_of_pos hH0, div_mul_cancel₀ _ hH0.ne']
  exact key

omit hc hev in
/-- **`|ν| ≤ ν̄ + |NT| + |B_t|`** from a decomposition `ρ̃ + ν + NT = B m + B_t` (the field
`hdec`) and the noise bound `|ρ̃ - B m| ≤ ν̄`. -/
lemma nu_of_dec {ρ ν NT Bm Bt nb : ℝ} (hdec : ρ + ν + NT = Bm + Bt) (hn : |ρ - Bm| ≤ nb) :
    |ν| ≤ nb + |NT| + |Bt| := by
  have : ν = -(ρ - Bm) - NT + Bt := by linarith
  rw [this]
  calc |-(ρ - Bm) - NT + Bt| ≤ |-(ρ - Bm) - NT| + |Bt| := abs_add_le _ _
    _ ≤ |-(ρ - Bm)| + |NT| + |Bt| := by gcongr; exact abs_sub _ _
    _ = |ρ - Bm| + |NT| + |Bt| := by rw [abs_neg]
    _ ≤ nb + |NT| + |Bt| := by gcongr

omit hev in
/-- **The size of `ν̄`**: `ν̄(y) ≤ 1.1 s₂(u₁) + 1.1 s₂(2u₁) + 106 L₁^{-6}`. -/
theorem nuB_le {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    nuB X₀ y ≤ 1.1 * s2E3 X₀ (uS X₀ (m1z X₀ y)) + 1.1 * s2E3 X₀ (uS X₀ (m1z X₀ y + 1)) +
      106 / Real.log (uS X₀ (m1z X₀ y)) ^ 6 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  set m1 := m1z X₀ y
  set u1 := uS X₀ m1
  obtain ⟨hu1X, hl1, -, -⟩ := uS_facts hc m1
  obtain ⟨hm1a, -⟩ := mB_spec (by linarith : (0 : ℝ) < X₀)
    (le_max_right (y - Hc X₀ y) (X₀ : ℝ))
  have hH0 := Hc_nonneg (X₀ := X₀) y
  have hu1y : u1 ≤ y := hm1a.trans (max_le (by linarith) hy)
  have hHy : Hc X₀ y = capH X₀ y := Hc_eq hy
  have hHH : capH X₀ u1 ≤ Hc X₀ y := by
    rw [hHy]; exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hu1X) (mem_Ici.mpr hy) hu1y
  obtain ⟨h32, -⟩ := capH_big hc hu1X
  set L1 := Real.log u1
  have hL1p : 0 < L1 := by linarith
  have hL6 : 0 < L1 ^ 6 := by positivity
  have hHpos : 0 < Hc X₀ y := by
    have : 0 < L1 ^ 32 := by positivity
    linarith
  have hs := s2ε_le hc y
  -- `300 log(4y) + 6.4 ≤ H(y)/L₁⁶`
  have hlog : 300 * Real.log (4 * y) + 6.4 ≤ Hc X₀ y / L1 ^ 6 := by
    obtain ⟨h32y, -⟩ := capH_big hc hy
    have hly := (logs_of_ge hX0 hc.hX hy).1
    have hl4 : Real.log (4 * y) ≤ Real.log y + 2 := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith
      linarith
    have hLL : L1 ≤ Real.log y := Real.log_le_log (by linarith) hu1y
    rw [le_div_iff₀ hL6]
    set Ly := Real.log y
    have h6 : L1 ^ 6 ≤ Ly ^ 6 := pow_le_pow_left₀ hL1p.le hLL 6
    have : (300 * Ly + 606.4) * Ly ^ 6 ≤ Ly ^ 32 := by
      have e : Ly ^ 32 = Ly ^ 7 * Ly ^ 25 := by ring
      have h25 : (1000 : ℝ) ≤ Ly ^ 25 := le_trans (by norm_num) (hly.trans (le_self_pow₀
        (by linarith) (by norm_num)))
      have h7 : 0 ≤ Ly ^ 6 := by positivity
      have hA : 1000 * Ly ^ 7 ≤ Ly ^ 7 * Ly ^ 25 :=
        by nlinarith [pow_nonneg (show (0 : ℝ) ≤ Ly by linarith) 7]
      have hB : Ly ^ 7 = Ly * Ly ^ 6 := by ring
      rw [e]
      nlinarith
    rw [hHy]
    nlinarith
  unfold nuB
  rw [div_le_iff₀ hHpos]
  have e : (1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ (uS X₀ (m1 + 1)) + 106 / L1 ^ 6) * Hc X₀ y =
      Hc X₀ y * (1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ (uS X₀ (m1 + 1)) + 105 / L1 ^ 6) +
        Hc X₀ y / L1 ^ 6 := by
    field_simp; ring
  rw [e]
  linarith

end Queue6

end
