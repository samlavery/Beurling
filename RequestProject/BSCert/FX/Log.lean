module

public import RequestProject.BSCert.FX.Exp

/-!
# Fixed-point enclosures of `log` and `sqrt`

* `log`: for `x = n / 2^128 > 0`, write `x = 2^e m` with `m ∈ [1, 2)` (rounded down for the
  lower bound and up for the upper bound), `m = c (1+t)/(1-t)` with `c = 1 + i/16` and
  `0 ≤ t ≤ 1/33`, and use `log((1+t)/(1-t)) = 2 ∑ t^(2k+1)/(2k+1)` (13 terms, each rounded
  down / up; the tail is below `2^-128`). The constants `log 2` and `log(1 + i/16)` are
  literals, certified once through the fixed-point `exp` (`lnConstsOK`).
* `sqrt`: an integer square root by Newton's method, checked by squaring.
-/

@[expose] public section

namespace BSCert.FX

open Finset

/-! ## Constants -/

def ln2Lo : ℤ := 235865763225513294137944142764154483375
def ln2Hi : ℤ := 235865763225513294137944142764154485424
def lnTab : List (ℤ × ℤ) :=
  [(-1024, 1024),
   (20629489805383211981841882725542884504, 20629489805383211981841882725542886553),
   (40079490156287452793155941028478194013, 40079490156287452793155941028478196062),
   (58477612182975000213432619324857086460, 58477612182975000213432619324857088509),
   (75931815804343184391506054410983915669, 75931815804343184391506054410983917718),
   (92534248350378670093033413010462047807, 92534248350378670093033413010462049856),
   (108364189379819075341293841424333999191, 108364189379819075341293841424334001240),
   (123490340361229994020203365888201449898, 123490340361229994020203365888201451947),
   (137972626690900373465550041896316338694, 137972626690900373465550041896316340743),
   (151863631608686368783012108821967832363, 151863631608686368783012108821967834412),
   (165209748712812112248363405789911013621, 165209748712812112248363405789911015670),
   (178052116847187826258705982924794533732, 178052116847187826258705982924794535781),
   (190427384884991590765427513878300192487, 190427384884991590765427513878300194536),
   (202368342248750201110067636447317191192, 202368342248750201110067636447317193241),
   (213904442495243557857056096307300255388, 213904442495243557857056096307300257437),
   (225062241016369099520457096561691632574, 225062241016369099520457096561691634623)]

/-- `2^124`: the table step `1/16` in fixed point. -/
def T16 : ℕ := 21267647932558653966460912964485513216

lemma T16_eq : T16 = 2 ^ 124 := by norm_num [T16]

/-- `lo ≤ 2^128 log (c / 2^128) ≤ hi`, checked through `exp`. -/
def checkLn (lo hi : ℤ) (c : ℕ) : Bool :=
  (match expHi lo with
   | some h => decide (h ≤ (c : ℤ))
   | none => false) && decide ((c : ℤ) ≤ expLo hi)

/-- Check the table entries `i, i+1, …`. -/
def tabOK : ℕ → List (ℤ × ℤ) → Bool
  | _, [] => true
  | i, p :: ps => checkLn p.1 p.2 (ZN + i * T16) && tabOK (i + 1) ps

/-- All the logarithm constants are correct. -/
def lnConstsOK : Bool := checkLn ln2Lo ln2Hi (2 * ZN) && tabOK 0 lnTab && decide (lnTab.length = 16)

lemma toR_natCast_div (c : ℕ) : toR (c : ℤ) = (c : ℝ) / (ZI : ℝ) := by
  unfold toR; push_cast; rfl

lemma checkLn_sound {lo hi : ℤ} {c : ℕ} (h : checkLn lo hi c = true) (hc : 0 < c) :
    toR lo ≤ Real.log ((c : ℝ) / ZI) ∧ Real.log ((c : ℝ) / ZI) ≤ toR hi := by
  unfold checkLn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : 0 < (c : ℝ) / ZI := div_pos (by exact_mod_cast hc) ZR_pos
  constructor
  · split at h1
    · rename_i e he
      have hE := le_expHi he
      have : toR e ≤ toR (c : ℤ) := toR_le_toR.mpr (of_decide_eq_true h1)
      rw [toR_natCast_div] at this
      rw [Real.le_log_iff_exp_le hc']
      exact hE.trans this
    · cases h1
  · have hL := expLo_le hi
    have : toR (c : ℤ) ≤ toR (expLo hi) := toR_le_toR.mpr h2
    rw [toR_natCast_div] at this
    rw [Real.log_le_iff_le_exp hc']
    exact this.trans hL

lemma tabOK_get : ∀ (L : List (ℤ × ℤ)) (i0 : ℕ), tabOK i0 L = true →
    ∀ j < L.length, checkLn (L.getD j (0, 0)).1 (L.getD j (0, 0)).2 (ZN + (i0 + j) * T16) = true := by
  intro L
  induction L with
  | nil => intro i0 _ j hj; simp at hj
  | cons p ps ih =>
    intro i0 h j hj
    simp only [tabOK, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih (i0 + 1) h.2 j (by simpa using hj)
      simpa [show i0 + 1 + j = i0 + (j + 1) by omega] using this

lemma lnConsts_ok : lnConstsOK = true := by decide +kernel

lemma ln2_bounds : toR ln2Lo ≤ Real.log 2 ∧ Real.log 2 ≤ toR ln2Hi := by
  have h := lnConsts_ok
  unfold lnConstsOK at h
  simp only [Bool.and_eq_true] at h
  have := checkLn_sound h.1.1 (by norm_num [ZN])
  have e : (((2 * ZN : ℕ) : ℝ)) / ZI = 2 := by
    rw [← ZI_natCast]; push_cast; field_simp [show ((ZN : ℕ) : ℝ) ≠ 0 by norm_num [ZN]]
  rwa [e] at this

lemma lnTab_bounds {i : ℕ} (hi : i < 16) :
    toR (lnTab.getD i (0, 0)).1 ≤ Real.log (((ZN + i * T16 : ℕ) : ℝ) / ZI) ∧
      Real.log (((ZN + i * T16 : ℕ) : ℝ) / ZI) ≤ toR (lnTab.getD i (0, 0)).2 := by
  have h := lnConsts_ok
  unfold lnConstsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have := tabOK_get lnTab 0 h.1.2 i (by rw [h.2]; exact hi)
  rw [zero_add] at this
  exact checkLn_sound this (by norm_num [ZN])

/-! ## The `atanh` series -/

/-- `s + ∑_{k=j}^{j+n-1} ⌊p_k / (2k+1)⌋`, `p_{k+1} = ⌊p_k u / 2^128⌋`. -/
def atLo (u : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, _, s => s
  | n + 1, j, pw, s =>
    forceI (s + fdiv pw ((2 * j + 1 : ℕ) : ℤ)) fun s' => forceI (fl (pw * u)) fun pw' =>
      atLo u n (j + 1) pw' s'

/-- As `atLo`, rounded up. -/
def atHi (u : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, _, s => s
  | n + 1, j, pw, s =>
    forceI (s + cdiv pw ((2 * j + 1 : ℕ) : ℤ)) fun s' => forceI (cl (pw * u)) fun pw' =>
      atHi u n (j + 1) pw' s'

lemma toR_fdivN (a : ℤ) {d : ℕ} (hd : 0 < d) : toR (fdiv a (d : ℤ)) ≤ toR a / d := by
  have := fdiv_le (a := a) (d := d) (by exact_mod_cast hd)
  unfold toR
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right this ZR_pos.le

lemma le_toR_cdivN (a : ℤ) {d : ℕ} (hd : 0 < d) : toR a / d ≤ toR (cdiv a (d : ℤ)) := by
  have := le_cdiv (a := a) (d := d) (by exact_mod_cast hd)
  unfold toR
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right this ZR_pos.le

lemma atLo_spec {u : ℤ} {τ : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ) (huτ : toR u ≤ τ ^ 2) :
    ∀ n j pw s, 0 ≤ pw → toR pw ≤ τ ^ (2 * j + 1) →
      toR (atLo u n j pw s) ≤ toR s + ∑ k ∈ Ico j (j + n), τ ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  intro n
  induction n with
  | zero => intro j pw s _ _; simp [atLo]
  | succ n ih =>
    intro j pw s hpw hpwτ
    simp only [atLo, forceI_eq]
    have hpw' : 0 ≤ fl (pw * u) := fdiv_nonneg (mul_nonneg hpw hu) ZI_pos
    have hpwτ' : toR (fl (pw * u)) ≤ τ ^ (2 * (j + 1) + 1) := by
      refine fl_mul_le.trans ?_
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]
      exact mul_le_mul hpwτ huτ (toR_nonneg.mpr hu) (by positivity)
    have h1 := ih (j + 1) _ (s + fdiv pw ((2 * j + 1 : ℕ) : ℤ)) hpw' hpwτ'
    refine h1.trans ?_
    rw [Finset.sum_eq_sum_Ico_succ_bot (show j < j + (n + 1) by omega), toR_add,
      show j + (n + 1) = j + 1 + n by omega]
    have h2 : toR (fdiv pw ((2 * j + 1 : ℕ) : ℤ)) ≤ τ ^ (2 * j + 1) / (2 * j + 1 : ℕ) :=
      (toR_fdivN pw (by omega)).trans (div_le_div_of_nonneg_right hpwτ (by positivity))
    linarith

lemma atHi_spec {u : ℤ} {τ : ℝ} (hτ : 0 ≤ τ) (huτ : τ ^ 2 ≤ toR u) :
    ∀ n j pw s, τ ^ (2 * j + 1) ≤ toR pw →
      toR s + ∑ k ∈ Ico j (j + n), τ ^ (2 * k + 1) / (2 * k + 1 : ℕ) ≤ toR (atHi u n j pw s) := by
  intro n
  induction n with
  | zero => intro j pw s _; simp [atHi]
  | succ n ih =>
    intro j pw s hpwτ
    simp only [atHi, forceI_eq]
    have hpwτ' : τ ^ (2 * (j + 1) + 1) ≤ toR (cl (pw * u)) := by
      refine le_trans ?_ le_cl_mul
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]
      exact mul_le_mul hpwτ huτ (by positivity) ((by positivity : (0:ℝ) ≤ τ ^ (2 * j + 1)).trans hpwτ)
    have h1 := ih (j + 1) _ (s + cdiv pw ((2 * j + 1 : ℕ) : ℤ)) hpwτ'
    refine le_trans ?_ h1
    rw [Finset.sum_eq_sum_Ico_succ_bot (show j < j + (n + 1) by omega), toR_add,
      show j + (n + 1) = j + 1 + n by omega]
    have h2 : τ ^ (2 * j + 1) / (2 * j + 1 : ℕ) ≤ toR (cdiv pw ((2 * j + 1 : ℕ) : ℤ)) :=
      (div_le_div_of_nonneg_right hpwτ (by positivity)).trans (le_toR_cdivN pw (by omega))
    linarith

/-- The series bounds for `log((1+τ)/(1-τ))`, `0 ≤ τ ≤ 1/33`, 13 terms. -/
lemma log_ratio_bounds {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 33) :
    2 * ∑ k ∈ range 13, τ ^ (2 * k + 1) / (2 * k + 1 : ℕ) ≤ Real.log ((1 + τ) / (1 - τ)) ∧
      Real.log ((1 + τ) / (1 - τ)) ≤
        2 * ∑ k ∈ range 13, τ ^ (2 * k + 1) / (2 * k + 1 : ℕ) + 1 / (ZI : ℝ) := by
  have habs : |τ| < 1 := by rw [abs_of_nonneg h0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have e : Real.log ((1 + τ) / (1 - τ)) = Real.log (1 + τ) - Real.log (1 - τ) :=
    Real.log_div (by linarith) (by linarith)
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * k + 1)) * τ ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have esum : 2 * ∑ k ∈ range 13, τ ^ (2 * k + 1) / (2 * k + 1 : ℕ) = ∑ k ∈ range 13, f k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]; push_cast; ring
  rw [e, esum]
  constructor
  · exact sum_le_hasSum (range 13) (fun k _ => hf0 k) hs
  · rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add 13]
    have hq : τ ^ 2 < 1 := by nlinarith
    have hg : Summable (fun k : ℕ => 2 * τ ^ 27 * (τ ^ 2) ^ k) :=
      (summable_geometric_of_lt_one (by positivity) hq).mul_left _
    have hle : ∀ k : ℕ, f (k + 13) ≤ 2 * τ ^ 27 * (τ ^ 2) ^ k := by
      intro k
      simp only [hf]
      have e2 : τ ^ (2 * ((k + 13 : ℕ) : ℝ) + 1) = τ ^ 27 * (τ ^ 2) ^ k := by
        rw [← pow_mul]
        rw [show (2 * ((k + 13 : ℕ) : ℝ) + 1) = ((2 * k + 27 : ℕ) : ℝ) by push_cast; ring]
        rw [Real.rpow_natCast, ← pow_add]; ring_nf
      push_cast
      have hd : (1 : ℝ) ≤ 2 * ((k : ℝ) + 13) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
      have : (1 : ℝ) / (2 * ((k : ℝ) + 13) + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hd
      have hp : 0 ≤ τ ^ (2 * (k + 13) + 1) := by positivity
      calc 2 * (1 / (2 * ((k : ℝ) + 13) + 1)) * τ ^ (2 * (k + 13) + 1)
          ≤ 2 * 1 * τ ^ (2 * (k + 13) + 1) := by gcongr
        _ = 2 * τ ^ 27 * (τ ^ 2) ^ k := by ring
    have htail : ∑' k, f (k + 13) ≤ 2 * τ ^ 27 * (1 - τ ^ 2)⁻¹ := by
      refine (Summable.tsum_le_tsum hle (hs.summable.comp_injective (add_left_injective 13)) hg).trans
        (le_of_eq ?_)
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq]
    have hb : 2 * τ ^ 27 * (1 - τ ^ 2)⁻¹ ≤ 1 / (ZI : ℝ) := by
      have h27 : τ ^ 27 ≤ (1 / 33) ^ 27 := pow_le_pow_left₀ h0 h1 27
      have hq2 : τ ^ 2 ≤ 1 / 1089 := by nlinarith
      have hinv : (1 - τ ^ 2)⁻¹ ≤ 1089 / 1088 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      calc 2 * τ ^ 27 * (1 - τ ^ 2)⁻¹ ≤ 2 * (1 / 33) ^ 27 * (1089 / 1088) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h27 (by norm_num)) hinv
              (inv_nonneg.mpr (by linarith)) (by positivity)
        _ ≤ 1 / (ZI : ℝ) := by rw [ZI]; norm_num
    linarith

/-! ## `log` -/

/-- `e log 2`, rounded down. -/
def eLo (e : ℤ) : ℤ := if 0 ≤ e then e * ln2Lo else e * ln2Hi
/-- `e log 2`, rounded up. -/
def eHi (e : ℤ) : ℤ := if 0 ≤ e then e * ln2Hi else e * ln2Lo

/-- Lower bound for `2^128 (e log 2 + log (m / 2^128))` (`none` if `m` is out of range). -/
def logLoCore (e : ℤ) (m : ℕ) : Option ℤ :=
  if ZN ≤ m then
    let i := (m - ZN) / T16
    if i < 16 then
      if 33 * (m - (ZN + i * T16)) ≤ m + (ZN + i * T16) then
        let t := fdiv (((m - (ZN + i * T16) : ℕ) : ℤ) * ZI) ((m + (ZN + i * T16) : ℕ) : ℤ)
        let S := atLo (fl (t * t)) 13 0 t 0
        some (eLo e + (lnTab.getD i (0, 0)).1 + 2 * S)
      else none
    else none
  else none

/-- Upper bound for `2^128 (e log 2 + log (m / 2^128))`. -/
def logHiCore (e : ℤ) (m : ℕ) : Option ℤ :=
  if ZN ≤ m then
    let i := (m - ZN) / T16
    if i < 16 then
      if 33 * (m - (ZN + i * T16)) ≤ m + (ZN + i * T16) then
        let t := cdiv (((m - (ZN + i * T16) : ℕ) : ℤ) * ZI) ((m + (ZN + i * T16) : ℕ) : ℤ)
        let S := atHi (cl (t * t)) 13 0 t 0
        some (eHi e + (lnTab.getD i (0, 0)).2 + 2 * S + 1)
      else none
    else none
  else none

/-- The splitting `m = c (1+τ)/(1-τ)`. -/
lemma log_split {m c : ℕ} (hc : 0 < c) (hcm : c ≤ m) :
    Real.log ((m : ℝ) / ZI) = Real.log ((c : ℝ) / ZI) +
      Real.log ((1 + ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ)) /
        (1 - ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ))) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hc hcm)
  have hc0 : (c : ℝ) ≠ 0 := hc'.ne'
  have hmc : (m : ℝ) + c ≠ 0 := by linarith
  have e : (1 + ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ)) / (1 - ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ))
      = (m : ℝ) / c := by
    rw [Nat.cast_sub hcm]; push_cast
    have h2 : (m : ℝ) + c - (m - c) ≠ 0 := by linarith
    field_simp
    ring
  rw [e, ← Real.log_mul (div_pos hc' ZR_pos).ne' (div_pos hm' hc').ne']
  congr 1
  field_simp

lemma tau_bounds {m c : ℕ} (hcm : c ≤ m) (h33 : 33 * (m - c) ≤ m + c) (hc : 0 < c) :
    0 ≤ ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ) ∧ ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ) ≤ 1 / 33 := by
  have hmc : (0 : ℝ) < ((m + c : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + c)
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hmc (by norm_num)]
  have : ((33 * (m - c) : ℕ) : ℝ) ≤ ((m + c : ℕ) : ℝ) := by exact_mod_cast h33
  push_cast at this ⊢
  linarith

lemma toR_tLo {a b : ℕ} (hb : 0 < b) :
    toR (fdiv ((a : ℤ) * ZI) (b : ℤ)) ≤ (a : ℝ) / b := by
  have := fdiv_le (a := (a : ℤ) * ZI) (d := b) (by exact_mod_cast hb)
  unfold toR
  rw [div_le_iff₀ ZR_pos]
  refine this.trans (le_of_eq ?_)
  push_cast; ring

lemma le_toR_tHi {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b ≤ toR (cdiv ((a : ℤ) * ZI) (b : ℤ)) := by
  have := le_cdiv (a := (a : ℤ) * ZI) (d := b) (by exact_mod_cast hb)
  unfold toR
  rw [le_div_iff₀ ZR_pos]
  refine le_trans (le_of_eq ?_) this
  push_cast; ring

lemma e_log2_lo (e : ℤ) : toR (eLo e) ≤ (e : ℝ) * Real.log 2 := by
  unfold eLo
  obtain ⟨h1, h2⟩ := ln2_bounds
  have hm : ∀ a : ℤ, toR (e * a) = (e : ℝ) * toR a := fun a => by unfold toR; push_cast; ring
  split_ifs with he
  · rw [hm]; exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast he)
  · rw [hm]; exact mul_le_mul_of_nonpos_left h2 (by exact_mod_cast (le_of_lt (not_le.mp he)))

lemma e_log2_hi (e : ℤ) : (e : ℝ) * Real.log 2 ≤ toR (eHi e) := by
  unfold eHi
  obtain ⟨h1, h2⟩ := ln2_bounds
  have hm : ∀ a : ℤ, toR (e * a) = (e : ℝ) * toR a := fun a => by unfold toR; push_cast; ring
  split_ifs with he
  · rw [hm]; exact mul_le_mul_of_nonneg_left h2 (by exact_mod_cast he)
  · rw [hm]; exact mul_le_mul_of_nonpos_left h1 (by exact_mod_cast (le_of_lt (not_le.mp he)))

lemma toR_two_mul (a : ℤ) : toR (2 * a) = 2 * toR a := by unfold toR; push_cast; ring

lemma logLoCore_sound {e : ℤ} {m : ℕ} {l : ℤ} (h : logLoCore e m = some l) :
    0 < m ∧ toR l ≤ (e : ℝ) * Real.log 2 + Real.log ((m : ℝ) / ZI) := by
  unfold logLoCore at h
  simp only at h
  split_ifs at h with hZ hi h33
  simp only [Option.some.injEq] at h
  subst h
  set i := (m - ZN) / T16
  set c := ZN + i * T16 with hcdef
  have hc : 0 < c := by simp only [hcdef]; norm_num [ZN]
  have hcm : c ≤ m := by
    have := Nat.div_mul_le_self (m - ZN) T16
    change ZN + (m - ZN) / T16 * T16 ≤ m
    omega
  refine ⟨lt_of_lt_of_le hc hcm, ?_⟩
  obtain ⟨hτ0, hτ1⟩ := tau_bounds hcm h33 hc
  set τ := ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ) with hτdef
  set t := fdiv (((m - c : ℕ) : ℤ) * ZI) ((m + c : ℕ) : ℤ)
  have hmc : 0 < m + c := by omega
  have ht0 : 0 ≤ t := fdiv_nonneg (mul_nonneg (by positivity) ZI_pos.le) (by exact_mod_cast hmc)
  have htτ : toR t ≤ τ := toR_tLo hmc
  have hu0 : 0 ≤ fl (t * t) := fdiv_nonneg (mul_self_nonneg t) ZI_pos
  have huτ : toR (fl (t * t)) ≤ τ ^ 2 := by
    refine fl_mul_le.trans ?_
    rw [pow_two]; exact mul_le_mul htτ htτ (toR_nonneg.mpr ht0) hτ0
  have hS := atLo_spec hu0 hτ0 huτ 13 0 t 0 ht0 (by simpa using htτ)
  rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hS
  have hser := (log_ratio_bounds hτ0 hτ1).1
  have htab : toR (lnTab.getD i (0, 0)).1 ≤ Real.log ((c : ℝ) / ZI) := (lnTab_bounds hi).1
  have he := e_log2_lo e
  rw [log_split hc hcm, ← hτdef]
  rw [toR_add, toR_add, toR_two_mul]
  linarith

lemma logHiCore_sound {e : ℤ} {m : ℕ} {l : ℤ} (h : logHiCore e m = some l) :
    0 < m ∧ (e : ℝ) * Real.log 2 + Real.log ((m : ℝ) / ZI) ≤ toR l := by
  unfold logHiCore at h
  simp only at h
  split_ifs at h with hZ hi h33
  simp only [Option.some.injEq] at h
  subst h
  set i := (m - ZN) / T16
  set c := ZN + i * T16 with hcdef
  have hc : 0 < c := by simp only [hcdef]; norm_num [ZN]
  have hcm : c ≤ m := by
    have := Nat.div_mul_le_self (m - ZN) T16
    change ZN + (m - ZN) / T16 * T16 ≤ m
    omega
  refine ⟨lt_of_lt_of_le hc hcm, ?_⟩
  obtain ⟨hτ0, hτ1⟩ := tau_bounds hcm h33 hc
  set τ := ((m - c : ℕ) : ℝ) / ((m + c : ℕ) : ℝ) with hτdef
  set t := cdiv (((m - c : ℕ) : ℤ) * ZI) ((m + c : ℕ) : ℤ)
  have hmc : 0 < m + c := by omega
  have htτ : τ ≤ toR t := le_toR_tHi hmc
  have huτ : τ ^ 2 ≤ toR (cl (t * t)) := by
    refine le_trans ?_ le_cl_mul
    rw [pow_two]; exact mul_le_mul htτ htτ hτ0 (hτ0.trans htτ)
  have hS := atHi_spec hτ0 huτ 13 0 t 0 (by simpa using htτ)
  rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico] at hS
  have hser := (log_ratio_bounds hτ0 hτ1).2
  have htab : Real.log ((c : ℝ) / ZI) ≤ toR (lnTab.getD i (0, 0)).2 := (lnTab_bounds hi).2
  have he := e_log2_hi e
  rw [log_split hc hcm, ← hτdef]
  have h1 : toR 1 = 1 / (ZI : ℝ) := by simp [toR]
  rw [toR_add, toR_add, toR_add, toR_two_mul, h1]
  linarith

/-- Lower bound for `2^128 log (X / 2^128)` (`X > 0`). -/
def logLo (X : ℤ) : Option ℤ :=
  let n := X.toNat
  let b := blen n
  if 129 ≤ b then logLoCore ((b - 129 : ℕ) : ℤ) (n / 2 ^ (b - 129))
  else logLoCore (-((129 - b : ℕ) : ℤ)) (n * 2 ^ (129 - b))

/-- Upper bound for `2^128 log (X / 2^128)` (`X > 0`). -/
def logHi (X : ℤ) : Option ℤ :=
  let n := X.toNat
  let b := blen n
  if 129 ≤ b then logHiCore ((b - 129 : ℕ) : ℤ) ((n + 2 ^ (b - 129) - 1) / 2 ^ (b - 129))
  else logHiCore (-((129 - b : ℕ) : ℤ)) (n * 2 ^ (129 - b))

lemma toR_toNat {X : ℤ} (hX : 0 < X) : toR X = ((X.toNat : ℕ) : ℝ) / ZI := by
  unfold toR
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hX.le).symm

lemma le_mul_ceil (n d : ℕ) (hd : 0 < d) : n ≤ d * ((n + d - 1) / d) := by
  have h1 := Nat.div_add_mod (n + d - 1) d
  have h3 := Nat.mod_lt (n + d - 1) hd
  omega

lemma sqrt_max_zero (x : ℝ) : Real.sqrt (Max.max x 0) = Real.sqrt x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
  · rw [max_eq_left h]

/-- `log (2^s m / Z) = s log 2 + log (m / Z)`. -/
lemma log_pow_mul {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Real.log (((2 ^ s * m : ℕ) : ℝ) / ZI) = (s : ℝ) * Real.log 2 + Real.log ((m : ℝ) / ZI) := by
  push_cast
  rw [mul_div_assoc, Real.log_mul (by positivity) (div_pos (by exact_mod_cast hm) ZR_pos).ne',
    Real.log_pow]

lemma logLo_le {X : ℤ} (hX : 0 < X) {l : ℤ} (h : logLo X = some l) : toR l ≤ Real.log (toR X) := by
  unfold logLo at h
  simp only at h
  rw [toR_toNat hX]
  set n := X.toNat
  have hn : 0 < n := by omega
  split_ifs at h with hb
  · obtain ⟨hm, hl⟩ := logLoCore_sound h
    set s := blen n - 129
    have hle : 2 ^ s * (n / 2 ^ s) ≤ n := Nat.mul_div_le n (2 ^ s)
    refine hl.trans ?_
    push_cast
    rw [← log_pow_mul hm s]
    exact Real.log_le_log (div_pos (by exact_mod_cast (by positivity : 0 < 2 ^ s * (n / 2 ^ s)))
      ZR_pos) (div_le_div_of_nonneg_right (by exact_mod_cast hle) ZR_pos.le)
  · obtain ⟨hm, hl⟩ := logLoCore_sound h
    set s := 129 - blen n
    refine hl.trans (le_of_eq ?_)
    have e : (n : ℝ) / ZI = 2 ^ (-(s : ℤ)) * (((n * 2 ^ s : ℕ) : ℝ) / ZI) := by
      push_cast
      rw [zpow_neg, zpow_natCast]
      field_simp
    rw [e, Real.log_mul (by positivity) (div_pos (by exact_mod_cast hm) ZR_pos).ne',
      Real.log_zpow]

lemma le_logHi {X : ℤ} (hX : 0 < X) {l : ℤ} (h : logHi X = some l) : Real.log (toR X) ≤ toR l := by
  unfold logHi at h
  simp only at h
  rw [toR_toNat hX]
  set n := X.toNat
  have hn : 0 < n := by omega
  split_ifs at h with hb
  · obtain ⟨hm, hl⟩ := logHiCore_sound h
    set s := blen n - 129
    have hle : n ≤ 2 ^ s * ((n + 2 ^ s - 1) / 2 ^ s) := le_mul_ceil n _ (by positivity)
    refine le_trans ?_ hl
    push_cast
    rw [← log_pow_mul hm s]
    exact Real.log_le_log (div_pos (by exact_mod_cast hn) ZR_pos)
      (div_le_div_of_nonneg_right (by exact_mod_cast hle) ZR_pos.le)
  · obtain ⟨hm, hl⟩ := logHiCore_sound h
    set s := 129 - blen n
    refine le_trans (le_of_eq ?_) hl
    have e : (n : ℝ) / ZI = 2 ^ (-(s : ℤ)) * (((n * 2 ^ s : ℕ) : ℝ) / ZI) := by
      push_cast
      rw [zpow_neg, zpow_natCast]
      field_simp
    rw [e, Real.log_mul (by positivity) (div_pos (by exact_mod_cast hm) ZR_pos).ne',
      Real.log_zpow]

/-! ## `sqrt` -/

/-- Newton's iteration for `⌊√N⌋` from above (any result is checked afterwards). -/
def newton : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, N, g => forceN ((g + N / g) / 2) fun g' => if g' < g then newton f N g' else g

/-- Integer square root (unverified; the bounds below check it). -/
def isqrt (N : ℕ) : ℕ := if N = 0 then 0 else newton 40 N (2 ^ ((blen N + 1) / 2))

/-- Lower bound for `2^128 √(X / 2^128)`. -/
def sqrtLo (X : ℤ) : ℤ :=
  let N := X.toNat * ZN
  let s := isqrt N
  if s * s ≤ N then s else 0

/-- Upper bound for `2^128 √(X / 2^128)`. -/
def sqrtHi (X : ℤ) : ℤ :=
  let N := X.toNat * ZN
  let s := isqrt N
  if N ≤ s * s then s else if N ≤ (s + 1) * (s + 1) then s + 1 else Max.max X ZI

lemma toNat_mul_ZN (X : ℤ) : (((X.toNat * ZN : ℕ) : ℝ)) = Max.max (toR X) 0 * ((ZI : ℝ) * ZI) := by
  rw [← ZI_natCast]
  unfold toR
  rw [← ZI_natCast]
  push_cast
  have hZ : (0 : ℝ) < (ZN : ℝ) := by norm_num [ZN]
  rcases le_total 0 X with h | h
  · rw [max_eq_left (div_nonneg (by exact_mod_cast h) hZ.le)]
    rw [show ((X.toNat : ℕ) : ℝ) = (X : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
    field_simp
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hZ.le)]
    rw [Int.toNat_eq_zero.mpr h]; simp

lemma sqrtLo_le (X : ℤ) : toR (sqrtLo X) ≤ Real.sqrt (toR X) := by
  unfold sqrtLo
  simp only
  split_ifs with h
  · have hN := toNat_mul_ZN X
    have h' : ((isqrt (X.toNat * ZN) * isqrt (X.toNat * ZN) : ℕ) : ℝ) ≤ ((X.toNat * ZN : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hN] at h'
    push_cast at h'
    have hs0 : (0 : ℝ) ≤ toR (isqrt (X.toNat * ZN) : ℤ) := toR_nonneg.mpr (by positivity)
    rw [← sqrt_max_zero, Real.le_sqrt hs0 (le_max_right _ _)]
    have e : toR (isqrt (X.toNat * ZN) : ℤ) ^ 2 =
        ((isqrt (X.toNat * ZN) : ℝ) * isqrt (X.toNat * ZN)) / ((ZI : ℝ) * ZI) := by
      unfold toR; push_cast; ring
    rw [e, div_le_iff₀ (mul_pos ZR_pos ZR_pos)]
    exact h'
  · rw [toR_zero]; exact Real.sqrt_nonneg _

lemma le_sqrtHi (X : ℤ) : Real.sqrt (toR X) ≤ toR (sqrtHi X) := by
  unfold sqrtHi
  simp only
  have hN := toNat_mul_ZN X
  have key : ∀ s : ℕ, X.toNat * ZN ≤ s * s → Real.sqrt (toR X) ≤ toR (s : ℤ) := by
    intro s hs
    have h' : ((X.toNat * ZN : ℕ) : ℝ) ≤ ((s * s : ℕ) : ℝ) := by exact_mod_cast hs
    rw [hN] at h'
    push_cast at h'
    have hs0 : (0 : ℝ) ≤ toR (s : ℤ) := toR_nonneg.mpr (by positivity)
    rw [← sqrt_max_zero, Real.sqrt_le_left hs0]
    have e : toR (s : ℤ) ^ 2 = ((s : ℝ) * s) / ((ZI : ℝ) * ZI) := by
      unfold toR; push_cast; ring
    rw [e, le_div_iff₀ (mul_pos ZR_pos ZR_pos)]
    exact h'
  split_ifs with h1 h2
  · exact key _ h1
  · have := key _ h2
    push_cast at this ⊢
    exact this
  · rw [FI.toR_max, toR_ZI]
    rcases le_total (toR X) 1 with h | h
    · refine le_trans ?_ (le_max_right _ _)
      rw [Real.sqrt_le_one]; exact h
    · refine le_trans ?_ (le_max_left _ _)
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith

namespace FI

/-- Interval `log`; `none` unless the interval is positive. -/
def log (a : FI) : Option FI :=
  if 0 < a.lo then
    match logLo a.lo, logHi a.hi with
    | some l, some h => some ⟨l, h⟩
    | _, _ => none
  else none

/-- Interval `sqrt` (`Real.sqrt` is monotone on all of `ℝ`). -/
def sqrt (a : FI) : FI := ⟨sqrtLo a.lo, sqrtHi a.hi⟩

lemma mem_log {x : ℝ} {a I : FI} (hx : Mem x a) (h : log a = some I) :
    Mem (Real.log x) I ∧ 0 < x := by
  unfold log at h
  split_ifs at h with h0
  split at h
  · rename_i l hh hl hh2
    simp only [Option.some.injEq] at h
    subst h
    have hl0 : 0 < toR a.lo := toR_pos.mpr h0
    have hx0 : 0 < x := lt_of_lt_of_le hl0 hx.1
    have hhi : 0 < a.hi := toR_pos.mp (lt_of_lt_of_le hx0 hx.2)
    refine ⟨⟨(logLo_le h0 hl).trans (Real.log_le_log hl0 hx.1),
      (Real.log_le_log hx0 hx.2).trans (le_logHi hhi hh2)⟩, hx0⟩
  · cases h

lemma mem_sqrt {x : ℝ} {a : FI} (hx : Mem x a) : Mem (Real.sqrt x) (sqrt a) :=
  ⟨(sqrtLo_le _).trans (Real.sqrt_le_sqrt hx.1), (Real.sqrt_le_sqrt hx.2).trans (le_sqrtHi _)⟩

end FI

end BSCert.FX
