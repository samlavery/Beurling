module

public import RequestProject.Beurling.Queue6.WinCount
public import RequestProject.Beurling.Model.MarginObjects
public import RequestProject.Beurling.Noise.MarginExact

/-!
# Proposition 5.38(a), Step 2: the slot representation, the weights and the slot counts

For the realised construction (`ω` fixed, `H = Hc X₀`) and a point `z` with a shift
`0 ≤ s ≤ 1.01 H(z)`:

* `s2Q z s` : the decisions `k` (placed, good stage: `lawA`) with slot start `s_{k+1} ≤ 2(z+s)+2`;
  `s2sl k = s_{k+1}` (`slotF`); `s2δ z = 2/H(z)`;
* `hS2rep_R` : **the slot representation** `ρ̃(y) = rhoTilde (s2Q z s) s2sl H y` for every
  `y ≤ z + s` (in particular `y = z, z + s`): the boxes of the other decisions lie above `z + s`;
* `hS2w_R` : **the weights**: for `s_q ∈ A₊ ∪ A₋`, `|H(z)/H(s_q) - 1| ≤ 1.6 δ_z = 3.2/H(z)`
  (`|s_q - z| ≤ 1.01H(z) + H(s_q)/2`, and `H` moves by at most `1/4` per step `H/2`:
  `JitterRegular.capH_regular`, `capH_steps`, `capH_lip`);
* `hS2c_R` : **the slot counts** `σ(A±) ≤ 1.03 H(z)`, for every `ω`: the slots of `A±` lie
  in a window of length `≤ s + 3/4`, and placed slots of good stages have unit jumps
  (`window_count_sharp`: `≤ (1 + 0.02/log)ℓ + 1`).
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono SlotModel

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The data -/

open Classical in
/-- The decisions entering `ρ̃` on `(-∞, z + s]`: placed, good stage, `s_{k+1} ≤ 2(z+s)+2`. -/
noncomputable def s2Q (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (z s : ℝ) : Finset ℕ :=
  (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * (z + s) + 2)).toFinset.filter
    (fun k => ω ∈ lawA θ X₀ k)

/-- The slot of the decision `k`. -/
noncomputable def s2sl (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (_z _s : ℝ) (k : ℕ) : ℝ := slotF θ X₀ k ω

/-- `δ_z = 2/H(z)`. -/
noncomputable def s2δ (X₀ : ℕ) (z : ℝ) : ℝ := 2 / Hc X₀ z

lemma mem_s2Q {ω : JitterΩ} {z s : ℝ} {k : ℕ} :
    k ∈ s2Q θ X₀ ω z s ↔ slotF θ X₀ k ω ≤ 2 * (z + s) + 2 ∧ ω ∈ lawA θ X₀ k := by
  classical
  unfold s2Q
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  rfl

section Facts

variable (hc : Cond θ X₀)
include hc

lemma Hc_slot (ω : JitterΩ) (k : ℕ) : Hc X₀ (slotF θ X₀ k ω) = HF θ X₀ k ω := by
  unfold Hc HF; rw [max_eq_left (slotF_ge hc k ω)]

/-- **The slot representation of `ρ̃`** on `(-∞, z + s]`. -/
theorem hS2rep_R (ω : JitterΩ) (z s y : ℝ) (hy : y ≤ z + s) :
    rhoT θ X₀ ω y = Margin.Exact.rhoTilde (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Hc X₀) y := by
  classical
  set f : ℕ → ENNReal := fun k => (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal
    (HF θ X₀ k ω)⁻¹ * (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 y) ω with hf
  have hzero : ∀ k ∉ s2Q θ X₀ ω z s, f k = 0 := by
    intro k hk
    rw [mem_s2Q, not_and_or] at hk
    simp only [hf]
    rcases hk with hk | hk
    · by_cases hA : ω ∈ lawA θ X₀ k
      · rw [Set.indicator_of_mem hA]
        push_neg at hk
        have hH := capH_le_div hc.hX (slotF_ge hc k ω)
        have hsX := slotF_ge hc k ω
        have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
        have hnot : y ∉ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω) := by
          unfold RankFull.box HF
          simp only [Set.mem_Ico, not_and_or, not_le]
          left; linarith
        simp [Set.indicator_of_notMem hnot]
      · exact Set.indicator_of_notMem hA _
    · exact Set.indicator_of_notMem hk _
  unfold rhoT
  rw [← hf, tsum_eq_sum (s := s2Q θ X₀ ω z s) (fun k hk => hzero k hk),
    ENNReal.toReal_sum (fun k _ => by
      simp only [hf]
      by_cases hA : ω ∈ lawA θ X₀ k
      · rw [Set.indicator_of_mem hA]
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        unfold Set.indicator; split_ifs <;> simp
      · rw [Set.indicator_of_notMem hA]; simp)]
  unfold Margin.Exact.rhoTilde
  refine Finset.sum_congr rfl fun k hk => ?_
  have hA := (mem_s2Q.mp hk).2
  simp only [hf, Set.indicator_of_mem hA, s2sl, Hc_slot hc ω k]
  have hH0 := HF_pos hc k ω
  by_cases hb : slotF θ X₀ k ω - HF θ X₀ k ω / 2 ≤ y ∧ y < slotF θ X₀ k ω + HF θ X₀ k ω / 2
  · have hmem : y ∈ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω) := hb
    rw [Set.indicator_of_mem hmem, if_pos hb]
    simp [ENNReal.toReal_ofReal (inv_nonneg.mpr hH0.le)]
  · have hmem : y ∉ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω) := hb
    rw [Set.indicator_of_notMem hmem, if_neg hb]
    simp

/-- `H(s) ≤ H(z) + 5/4` and, when `z - H(s)/2 ≤ s`, `H(z) - 1/4 ≤ H(s)`, for a slot height
`s ≥ X₀` with `s ≤ max(z, X₀) + 1.01 H(z) + H(s)/2`. -/
lemma H_near {z sl : ℝ} (hsl : (X₀ : ℝ) ≤ sl)
    (h1 : sl ≤ max z X₀ + 1.01 * Hc X₀ z + capH X₀ sl / 2) :
    capH X₀ sl ≤ Hc X₀ z + 5 / 4 ∧ (z - capH X₀ sl / 2 ≤ sl → Hc X₀ z - 1 / 4 ≤ capH X₀ sl) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  set x := max z (X₀ : ℝ) with hxdef
  have hxX : (X₀ : ℝ) ≤ x := le_max_right _ _
  have hHz : Hc X₀ z = capH X₀ x := rfl
  rw [hHz] at h1 ⊢
  have hH200 : 200 ≤ capH X₀ x := by
    have := log_le_capH hX0 hX hxX
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith [X₀_ge_two_pow hX])
    linarith
  have hHs0 := capH_nonneg (X₀ : ℝ) sl
  constructor
  · rcases le_or_gt sl x with h | h
    · have := capH_monotoneOn hX0 hX (mem_Ici.mpr hsl) (mem_Ici.mpr hxX) h; linarith
    · have hlip := capH_lip hX0 hX hxX h.le
      have hHs : capH X₀ sl ≤ 2.01 * capH X₀ x := by linarith
      have hstep := capH_steps hX0 hX hxX 5 sl h.le (by push_cast; linarith)
      push_cast at hstep; linarith
  · intro h3
    rcases le_or_gt x sl with h | h
    · have := capH_monotoneOn hX0 hX (mem_Ici.mpr hxX) (mem_Ici.mpr hsl) h; linarith
    · have hzx : x = z := by
        rcases le_total z (X₀ : ℝ) with h' | h'
        · rw [hxdef, max_eq_right h'] at h; linarith
        · rw [hxdef, max_eq_left h']
      rw [hzx] at h hxX ⊢
      have hmono := capH_monotoneOn hX0 hX (mem_Ici.mpr hsl) (mem_Ici.mpr hxX) h.le
      have := JitterRegular.capH_regular hX0 hX hsl h.le (by linarith)
      linarith

omit hc in
/-- The slots of `A₊ ∪ A₋` are near `z`. -/
lemma A_near {z s sl : ℝ} (_hs0 : 0 ≤ s) (hs : s ≤ 1.01 * Hc X₀ z) (hsl : (X₀ : ℝ) ≤ sl)
    (hA : sl ∈ Margin.Exact.Aplus (Hc X₀) z s ∨ sl ∈ Margin.Exact.Aminus (Hc X₀) z s) :
    sl ≤ max z X₀ + 1.01 * Hc X₀ z + capH X₀ sl / 2 ∧ z - capH X₀ sl / 2 ≤ sl := by
  have hHsl : Hc X₀ sl = capH X₀ sl := by unfold Hc; rw [max_eq_left hsl]
  have hzx : z ≤ max z (X₀ : ℝ) := le_max_left _ _
  have hH0 := capH_nonneg (X₀ : ℝ) sl
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hHsl] at h1 h2 <;> constructor <;> linarith

/-- **The weights** (Step 2, third bullet): `|H(z)/H(s_q) - 1| ≤ 1.6 δ_z` on `A₊ ∪ A₋`. -/
theorem hS2w_R (ω : JitterΩ) {z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * Hc X₀ z) :
    ∀ q ∈ s2Q θ X₀ ω z s, (s2sl θ X₀ ω z s q ∈ Margin.Exact.Aplus (Hc X₀) z s ∨
      s2sl θ X₀ ω z s q ∈ Margin.Exact.Aminus (Hc X₀) z s) →
      |Hc X₀ z / Hc X₀ (s2sl θ X₀ ω z s q) - 1| ≤ 1.6 * s2δ X₀ z := by
  intro q _ hA
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set sl := s2sl θ X₀ ω z s q
  have hsl : (X₀ : ℝ) ≤ sl := slotF_ge hc q ω
  obtain ⟨h1, h2⟩ := A_near hs0 hs hsl hA
  obtain ⟨hup, hlo⟩ := H_near hc hsl h1
  have hlo' := hlo h2
  have hHsl : Hc X₀ sl = capH X₀ sl := by unfold Hc; rw [max_eq_left hsl]
  have hH200 : 200 ≤ Hc X₀ z := by
    have hxX : (X₀ : ℝ) ≤ max z X₀ := le_max_right _ _
    have := log_le_capH hX0 hc.hX hxX
    have : 0 ≤ Real.log (max z (X₀ : ℝ)) := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    show 200 ≤ capH X₀ (max z X₀)
    linarith
  rw [hHsl]
  have hHs : 0 < capH X₀ sl := by linarith
  unfold s2δ
  rw [abs_le, div_sub_one hHs.ne']
  constructor
  · rw [le_div_iff₀ hHs]
    have : 1.6 * (2 / Hc X₀ z) * capH X₀ sl ≤ 1.6 * (2 / Hc X₀ z) * (Hc X₀ z + 5 / 4) := by
      gcongr
    have e : 1.6 * (2 / Hc X₀ z) * (Hc X₀ z + 5 / 4) = 3.2 + 4 / Hc X₀ z := by
      field_simp; ring
    have h4 : 0 ≤ 4 / Hc X₀ z := by positivity
    nlinarith
  · rw [div_le_iff₀ hHs]
    have : 1.6 * (2 / Hc X₀ z) * (Hc X₀ z - 1 / 4) ≤ 1.6 * (2 / Hc X₀ z) * capH X₀ sl := by
      gcongr
    have e : 1.6 * (2 / Hc X₀ z) * (Hc X₀ z - 1 / 4) = 3.2 - 0.8 / Hc X₀ z := by
      field_simp; ring
    have h4 : 0.8 / Hc X₀ z ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith

variable (hev : Even X₀)
include hev

/-- **The slot count of a window** (`window_count_sharp`): decisions of good stages whose slots lie
in `(a₀, b]`, `b - a₀ ≤ ℓ`, number at most `1.0001 ℓ + 1`. -/
theorem slot_window_card {ω : JitterΩ} (Q' : Finset ℕ)
    {a₀ b ℓ : ℝ} (hQ' : ∀ k ∈ Q', ω ∈ lawA θ X₀ k ∧ a₀ < slotF θ X₀ k ω ∧ slotF θ X₀ k ω ≤ b)
    (hℓ : b - a₀ ≤ ℓ) (hℓ0 : 0 ≤ ℓ) : (Q'.card : ℝ) ≤ 1.0001 * ℓ + 1 := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  rcases Q'.eq_empty_or_nonempty with he | ⟨k0, hk0⟩
  · rw [he, Finset.card_empty]; push_cast; linarith
  set a := max a₀ (X₀ : ℝ)
  have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hslotX : ∀ k : ℕ, (X₀ : ℝ) < slotF θ X₀ k ω := by
    intro k
    have h1 := (limModel_slot_one h hev).1
    have h2 : h.limModel.slot 1 ≤ h.limModel.slot (k + 1) := h.limModel.slot_mono (by omega)
    show (X₀ : ℝ) < (Mcl θ X₀ ω).slot (k + 1)
    rw [hMe]; linarith
  have hab : a ≤ b := by
    obtain ⟨-, h1, h2⟩ := hQ' k0 hk0
    exact max_le (by linarith) (by linarith [hslotX k0])
  set S₀ := {m | placedAt h.limModel m ∧
    UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1))}
  have hsub : (Q' : Set ℕ) ⊆ {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b} := by
    intro k hk
    obtain ⟨hA, h1, h2⟩ := hQ' k hk
    have hX := hslotX k
    have hp := hA.1
    have hg : ω ∈ stageGood θ X₀ k := hA.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at hp hg h1 h2 hX
    rw [hMe] at hp hg h1 h2 hX
    exact ⟨⟨hp, hg⟩, max_lt h1 hX, h2⟩
  have hwin := window_count_sharp h S₀ (fun m hm => hm) haX hab
  have hWfin : {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hc1 : (Q'.card : ℝ) ≤ ({m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b}.ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]; exact_mod_cast Set.ncard_le_ncard hsub hWfin
  have hla : Real.log X₀ ≤ Real.log a :=
    Real.log_le_log (by linarith [X₀_ge_two_pow hc.hX]) haX
  have hlga : 10 ^ 8 ≤ Real.log a := le_trans hc.hX hla
  have hcoef : 0.02 / Real.log a ≤ 0.0001 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hba : b - a ≤ ℓ := by have := le_max_left a₀ (X₀ : ℝ); linarith
  have hba0 : 0 ≤ b - a := by linarith
  have : (1 + 0.02 / Real.log a) * (b - a) ≤ 1.0001 * ℓ := by
    have h0 : 0 ≤ 0.02 / Real.log a := div_nonneg (by norm_num) (by linarith)
    calc (1 + 0.02 / Real.log a) * (b - a) ≤ 1.0001 * (b - a) :=
          mul_le_mul_of_nonneg_right (by linarith) hba0
      _ ≤ 1.0001 * ℓ := by linarith
  linarith

/-- **The slot counts** `σ(A±) ≤ 1.03 H(z)` (Step 2). -/
theorem hS2c_R {ω : JitterΩ} {z s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 1.01 * Hc X₀ z) :
    Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s)
        (Margin.Exact.Aplus (Hc X₀) z s) ≤ 1.03 * Hc X₀ z ∧
      Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s)
        (Margin.Exact.Aminus (Hc X₀) z s) ≤ 1.03 * Hc X₀ z := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hH200 : 200 ≤ Hc X₀ z := by
    have hxX : (X₀ : ℝ) ≤ max z X₀ := le_max_right _ _
    have := log_le_capH hX0 hc.hX hxX
    have : 0 ≤ Real.log (max z (X₀ : ℝ)) := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    show 200 ≤ capH X₀ (max z X₀)
    linarith
  have hnear : ∀ k : ℕ, (slotF θ X₀ k ω ∈ Margin.Exact.Aplus (Hc X₀) z s ∨
      slotF θ X₀ k ω ∈ Margin.Exact.Aminus (Hc X₀) z s) →
      Hc X₀ z - 1 / 4 ≤ HF θ X₀ k ω ∧ HF θ X₀ k ω ≤ Hc X₀ z + 5 / 4 := by
    intro k hA
    have hsl := slotF_ge hc k ω
    obtain ⟨h1, h2⟩ := A_near hs0 hs hsl hA
    obtain ⟨hup, hlo⟩ := H_near hc hsl h1
    exact ⟨hlo h2, hup⟩
  constructor
  · unfold Margin.Exact.sigmaS
    refine (slot_window_card hc hev (ω := ω) _ (a₀ := z + Hc X₀ z / 2 - 1 / 8)
      (b := z + s + Hc X₀ z / 2 + 5 / 8) (ℓ := s + 3 / 4) (fun k hk => ?_) (by linarith)
      (by linarith)).trans (by nlinarith)
    obtain ⟨hkQ, hkA⟩ := Finset.mem_filter.mp hk
    have hA := hnear k (Or.inl hkA)
    have hHsl : Hc X₀ (slotF θ X₀ k ω) = HF θ X₀ k ω := Hc_slot hc ω k
    obtain ⟨h1, h2⟩ := hkA
    simp only [s2sl] at h1 h2
    rw [hHsl] at h1 h2
    exact ⟨(mem_s2Q.mp hkQ).2, by linarith, by linarith⟩
  · unfold Margin.Exact.sigmaS
    refine (slot_window_card hc hev (ω := ω) _ (a₀ := z - Hc X₀ z / 2 - 5 / 8)
      (b := z + s - Hc X₀ z / 2 + 1 / 8) (ℓ := s + 3 / 4) (fun k hk => ?_) (by linarith)
      (by linarith)).trans (by nlinarith)
    obtain ⟨hkQ, hkA⟩ := Finset.mem_filter.mp hk
    have hA := hnear k (Or.inr hkA)
    have hHsl : Hc X₀ (slotF θ X₀ k ω) = HF θ X₀ k ω := Hc_slot hc ω k
    obtain ⟨h1, h2⟩ := hkA
    simp only [s2sl] at h1 h2
    rw [hHsl] at h1 h2
    exact ⟨(mem_s2Q.mp hkQ).2, by linarith, by linarith⟩

end Facts

end Queue6

end
