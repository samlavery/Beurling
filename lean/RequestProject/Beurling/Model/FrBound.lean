module

public import RequestProject.Beurling.Model.RestG
public import RequestProject.Beurling.Noise.RML6BridgeLoc
public import RequestProject.Beurling.Model.MarginTail

/-!
# The bounds of `F_r` in Lemma 5.34 from Lemma 5.22 (the fields `S`, `FbK`, `hFr`, `FrB`,
`hFrB0`, `hFrB` of `RestRes`)

`F_r = (B - 1)T_c - ν - NT` (`Frx`, at `ϑ = 0`). The paper (04f-bridge.tex, `lem:predictable`)
bounds `|F_r| ≤ F̄_r(v) = o_v + 6/H(v) + ν̄(v) + 54 sup_{[v,2v)} η` on `[v, 2v)`:

* `(B - 1)T_c`: the oscillation of `T_c` on a window, `≤ Bsc v` (`oscWin_le`, eq. (osc));
* `ν`: the Model's `ν` (the residual `nuRes` at `ϑ = 0`) is the paper's `ν` of Lemma 5.22
  minus `ϑ/H` (eq. (Ttilde), `|ϑ| ≤ 6`). The input **`Nu522`** (Queue6) is Lemma 5.22 for the
  paper's `ν = ν_Model + ϑ/H` on the dyadic blocks; the `6/H` is paid here;
* `NT = B NT_pt`: `|NT_pt| ≤ 2η` (eq. (NT), `NTpt_abs_le_eta`) and `η ≤ s_η(v)` on `[v, 2v)`
  (Lemma 5.20's block majorant `sEta0`, `etaG_le_etaS`); `NT_pt = 0` below `X₀`.

Blocks are `[v_i, 2v_i)`, `v_i = X₀⁻2ⁱ`, block `0` taken as `(-∞, 2X₀⁻)`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `r` lies in the block `i` (block `0` is `(-∞, 2X₀⁻)`). -/
def InBlk (X₀ : ℕ) (i : ℕ) (r : ℝ) : Prop :=
  r < 2 * (Xm X₀ * 2 ^ i) ∧ (i = 0 ∨ Xm X₀ * 2 ^ i ≤ r)

variable (θ X₀) in
/-- **Lemma 5.22 for the paper's `ν`** (Queue6): there is `ϑ` with `|ϑ| ≤ 6` (eq. (Ttilde))
such that the paper's noise `ν = ν_Model + ϑ/H` (Proposition 5.11; `ν_Model = nuRes` at the
Model data with `ϑ = 0`) is bounded by `ν̄_i` on the block `i`, at heights `≤ b`. -/
def Nu522 (ω : JitterΩ) (b : ℝ) (nb : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ nb i) ∧ ∃ ϑ : ℝ → ℝ, (∀ z, |ϑ z| ≤ 6) ∧
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ i r, r ≤ b → InBlk X₀ i r →
      |(nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) :
        ℝ → ℝ) r + ϑ r / Queue6.Hc X₀ r| ≤ nb i

open Classical in
variable (X₀) in
/-- The block index `K_i` of Lemma 5.20 at `v_i`: `√(2v_i) < P_{K_i}`. -/
noncomputable def Keta (i : ℕ) : ℕ :=
  if h : 0 < Xm X₀ then Classical.choose (exists_K h (√(2 * (Xm X₀ * 2 ^ i)) + 1)) else 0

lemma Keta_spec (h : 0 < Xm X₀) (i : ℕ) :
    √(2 * (Xm X₀ * 2 ^ i)) < Pk (Xm X₀) (Keta X₀ i) := by
  have := Classical.choose_spec (exists_K h (√(2 * (Xm X₀ * 2 ^ i)) + 1))
  unfold Keta; rw [dif_pos h]; linarith

variable (θ X₀) in
/-- `s_η(v_i)`: Lemma 5.20's block majorant of `η` on `[v_i, 2v_i)`. -/
noncomputable def etaS (ω : JitterΩ) (i : ℕ) : ℝ :=
  KR.TNP.sEta0 (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (Keta X₀ i) (Xm X₀ * 2 ^ i)

section

variable (hc : Cond θ X₀)
include hc

lemma etaS_nonneg {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    (i : ℕ) : 0 ≤ etaS θ X₀ ω i :=
  KR.TNP.blk_nonneg hT.width _ (fun _ => zero_le_one) _

/-- **`η ≤ s_η(v_i)` on `[v_i, 2v_i)`** (Lemma 5.20, block form). -/
lemma etaG_le_etaS {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    {i : ℕ} {q : ℝ} (h1 : Xm X₀ * 2 ^ i ≤ q) (h2 : q < 2 * (Xm X₀ * 2 ^ i)) :
    KR.etaG (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (fun _ => 1) q ≤ etaS θ X₀ ω i := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) h1
  have hK : √q < Pk (Xm X₀) (Keta X₀ i) :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) (Keta_spec hXm i)
  refine (KR.TNP.etaG_le_blocks hT hq0 hK (Ψ := fun _ => 1) (fun _ => zero_le_one)
    (fun _ _ _ _ _ => le_rfl)).trans ?_
  unfold etaS KR.TNP.sEta0 KR.TNP.blk
  refine Finset.sum_le_sum fun k _ => ?_
  have hk := Pk_pos hT.width.X0m_pos k
  have hH := (hT.width.reg.pos (Pk (Xm X₀) k)).le
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
    (Sm_subset_SmB hT.width.X0m_pos h1 h2) fun e _ _ => ?_) (by positivity)
  exact div_nonneg zero_le_one ((PR θ X₀ ω).val_pos e).le

/-- `NT_pt = 0` below `X₀`. -/
lemma NTpt_low (ω : JitterΩ) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j) {q : ℝ} (hq : q < X₀) :
    NTpt θ X₀ ω q = 0 := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hXmh := Xm_half hc
  unfold NTpt KptR
  rw [BModel.RML6.compDen_eq_zero_low hc ω hq, KAbsR_eq_zero_low hc ω _ hq.le,
    KR.Ops.Kpt_zero_low hXm hp2 _ (by linarith)]
  simp

end

/-- `|B f(t) - f(t)| ≤ M` if `|f - f(t)| ≤ M` on the window. -/
lemma abs_Bavg_sub_le {h t M : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hint : IntervalIntegrable f volume (t - h / 2) (t + h / 2))
    (hf : ∀ q, t - h / 2 ≤ q → q ≤ t + h / 2 → |f q - f t| ≤ M) :
    |Margin.Bavg h f t - f t| ≤ M := by
  have e : Margin.Bavg h f t - f t = Margin.Bavg h (fun q => f q - f t) t := by
    unfold Margin.Bavg
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, show t + h / 2 - (t - h / 2) = h by ring]
    field_simp
  rw [e]
  exact abs_Bavg_le hh hf

lemma Hc_vi_le (hX : 10 ^ 8 ≤ Real.log X₀) {i : ℕ} {r : ℝ} (hr : InBlk X₀ i r) :
    Queue6.Hc X₀ (Xm X₀ * 2 ^ i) ≤ Queue6.Hc X₀ r := by
  rcases hr.2 with h | h
  · subst h
    rcases le_total (Xm X₀) r with h' | h'
    · simpa using KR.WidthReal.Hc_mono hX h'
    · have hXmX : Xm X₀ ≤ X₀ := by
        have := capH_ge_one (Nat.cast_nonneg (α := ℝ) X₀) hX le_rfl; unfold Xm; linarith
      unfold Queue6.Hc
      simp only [pow_zero, mul_one]
      rw [max_eq_right hXmX, max_eq_right (h'.trans hXmX)]
  · exact KR.WidthReal.Hc_mono hX h

section Pt

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- The oscillation of `T_c` between two points whose clamps `max(·, X₀)` lie in `[u/2, 4u]`
below `2(b + H(b))` at distance `≤ 2.04 H(2u)`: `≤ Bsc u` (eq. (osc)). -/
lemma oscWin_le {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {u : ℝ} (hu4 : (X₀ : ℝ) ≤ 4 * u) {r q : ℝ} (h1 : u / 2 ≤ max r X₀)
    (h2 : u / 2 ≤ max q X₀) (h3 : max r X₀ ≤ 4 * u) (h4 : max q X₀ ≤ 4 * u)
    (h5 : max r X₀ ≤ 2 * (b + Queue6.Hc X₀ b)) (h6 : max q X₀ ≤ 2 * (b + Queue6.Hc X₀ b))
    (h7 : |q - r| ≤ 2.04 * Queue6.Hc X₀ (2 * u)) :
    |TcR θ X₀ ω (jzX X₀) q - TcR θ X₀ ω (jzX X₀) r| ≤ Bsc X₀ u := by
  rw [TcR_eq_max hc ω q, TcR_eq_max hc ω r]
  have hd : |max q (X₀ : ℝ) - max r X₀| ≤ 2.04 * Queue6.Hc X₀ (2 * u) :=
    (abs_max_sub_max_le_abs _ _ _).trans h7
  rcases le_total (max r (X₀ : ℝ)) (max q X₀) with h | h
  · rw [abs_sub_comm]
    exact Tc_pair_le_Bsc hc hev hb hbt hQC hE1 hN hT hu4 (le_max_right _ _) h h1 h4 h6
      (by linarith [(abs_le.mp hd).2])
  · exact Tc_pair_le_Bsc hc hev hb hbt hQC hE1 hN hT hu4 (le_max_right _ _) h h2 h3 h5
      (by linarith [(abs_le.mp hd).1])

end Pt

variable (θ X₀) in
/-- **`F̄_r` on the block `i`**: `o + 6/H + ν̄ + 2 · (s_η of the neighbouring blocks)`
(`lem:predictable`: `F̄_r(v) = o_v + 6/H(v) + ν̄(v) + 54 sup_{[v,2v)} η`). -/
noncomputable def FrBv (ω : JitterΩ) (nb : ℕ → ℝ) (i : ℕ) : ℝ :=
  Bsc X₀ (Xm X₀ * 2 ^ i) + 6 / Queue6.Hc X₀ (Xm X₀ * 2 ^ i) + nb i +
    2 * ((if i = 0 then 0 else etaS θ X₀ ω (i - 1)) + etaS θ X₀ ω i + etaS θ X₀ ω (i + 1))

section Pt2

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma FrBv_nonneg {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    {nb : ℕ → ℝ} (hnb : ∀ i, 0 ≤ nb i) (i : ℕ) : 0 ≤ FrBv θ X₀ ω nb i := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have h1 := Bsc_nonneg hc (u := Xm X₀ * 2 ^ i) (by positivity)
  have h2 := (KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) (Xm X₀ * 2 ^ i))
  have h3 := etaS_nonneg hc hT i
  have h4 := etaS_nonneg hc hT (i + 1)
  have h5 : 0 ≤ (if i = 0 then 0 else etaS θ X₀ ω (i - 1)) := by
    split_ifs
    · exact le_rfl
    · exact etaS_nonneg hc hT _
  have := hnb i
  unfold FrBv
  positivity

set_option maxHeartbeats 4000000 in
/-- **`|F_r| ≤ F̄_r` on the blocks** at heights `≤ b`, on `Good(< t)`, from `Nu522`. -/
theorem Fr_pt {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {nb : ℕ → ℝ} (hnu : Nu522 θ X₀ ω b nb)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) {i : ℕ} {r : ℝ} (hrb : r ≤ b)
    (hr : InBlk X₀ i r) :
    |((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
      ℝ → ℝ) r| ≤ FrBv θ X₀ ω nb i := by
  obtain ⟨hnb0, ϑ, hϑ, hν⟩ := hnu
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hXmX := Xm_le_X0 hc
  have hXmh := Xm_half hc
  have hHr := hO.pos r
  have hp2 := hO.p2
  set v := Xm X₀ * 2 ^ i with hv
  have hv1 : Xm X₀ ≤ v := le_mul_of_one_le_right hXm.le (one_le_pow₀ (by norm_num))
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  -- the window of `r`
  have hHrX : r < Xm X₀ → Queue6.Hc X₀ r = capH X₀ X₀ := fun h => by
    unfold Queue6.Hc; rw [max_eq_right (by linarith)]
  have hXmd : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
  have hW : ∀ q, r - Queue6.Hc X₀ r / 2 ≤ q → q ≤ r + Queue6.Hc X₀ r / 2 →
      v / 2 ≤ max q X₀ ∧ max q X₀ ≤ 4 * v ∧ max q X₀ ≤ 2 * (b + Queue6.Hc X₀ b) ∧
      (r < Xm X₀ → q < X₀) ∧ (Xm X₀ ≤ r → 0.95 * r ≤ q ∧ q ≤ 1.05 * r) := by
    intro q hq1 hq2
    have hA : r < Xm X₀ → q < X₀ := fun h => by rw [hHrX h] at hq2; linarith
    have hB : Xm X₀ / 2 ≤ r → 0.95 * r ≤ q ∧ q ≤ 1.05 * r := fun h => by
      have := hO.small r h; constructor <;> linarith
    refine ⟨?_, ?_, ?_, hA, fun h => hB (by linarith)⟩
    · rcases hr.2 with h | h
      · have : v = Xm X₀ := by rw [hv, h]; simp
        rw [this]; exact le_trans (by linarith) (le_max_right _ _)
      · have := (hB (by linarith)).1
        exact le_trans (by linarith) (le_max_left _ _)
    · refine max_le ?_ (by linarith)
      rcases le_or_gt (Xm X₀ / 2) r with h | h
      · linarith [(hB h).2, hr.1]
      · have := hO.low r h; linarith
    · refine max_le ?_ (by linarith)
      rcases le_or_gt (Xm X₀ / 2) r with h | h
      · have := hO.small r h; linarith
      · have := hO.low r h; linarith
  -- the oscillation part
  have hosc : |Margin.Bavg (Queue6.Hc X₀ r) (TcLd θ X₀ ω : ℝ → ℝ) r -
      (TcLd θ X₀ ω : ℝ → ℝ) r| ≤ Bsc X₀ v := by
    refine abs_Bavg_sub_le hHr ((TcLd θ X₀ ω).2 _ _) fun q hq1 hq2 => ?_
    rw [TcLd_coe hc hev ω]
    obtain ⟨a1, a2, a3, -, -⟩ := hW q hq1 hq2
    obtain ⟨b1, b2, b3, -, -⟩ := hW r (by linarith) (by linarith)
    refine oscWin_le hc hev hb hbt hQC hE1 hN hT (by linarith) b1 a1 b2 a2 b3 a3 ?_
    have hm : Queue6.Hc X₀ r ≤ Queue6.Hc X₀ (2 * v) := KR.WidthReal.Hc_mono hX hr.1.le
    rw [abs_le]; constructor <;> linarith
  -- the noise part
  have hνr : |(nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0
      (NTd θ X₀ ω) : ℝ → ℝ) r| ≤ nb i + 6 / Queue6.Hc X₀ v := by
    have h1 := hν hO i r hrb hr
    have h2 : |ϑ r / Queue6.Hc X₀ r| ≤ 6 / Queue6.Hc X₀ v := by
      rw [abs_div, abs_of_pos hHr]
      calc |ϑ r| / Queue6.Hc X₀ r ≤ 6 / Queue6.Hc X₀ r :=
            div_le_div_of_nonneg_right (hϑ r) hHr.le
        _ ≤ 6 / Queue6.Hc X₀ v :=
            div_le_div_of_nonneg_left (by norm_num) (KR.WidthReal.Hc_pos hX _)
              (Hc_vi_le hX hr)
    have := abs_sub (((nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0
      (NTd θ X₀ ω) : ℝ → ℝ) r) + ϑ r / Queue6.Hc X₀ r) (ϑ r / Queue6.Hc X₀ r)
    simp only [add_sub_cancel_right] at this
    linarith
  -- the `NT` part
  set E := 2 * ((if i = 0 then 0 else etaS θ X₀ ω (i - 1)) + etaS θ X₀ ω i +
    etaS θ X₀ ω (i + 1)) with hE
  have hE0 : 0 ≤ E := by
    have h3 := etaS_nonneg hc hT i
    have h4 := etaS_nonneg hc hT (i + 1)
    have h5 : 0 ≤ (if i = 0 then 0 else etaS θ X₀ ω (i - 1)) := by
      split_ifs
      · exact le_rfl
      · exact etaS_nonneg hc hT _
    positivity
  have hNT : |(NTd θ X₀ ω : ℝ → ℝ) r| ≤ E := by
    rw [NTd_eq ω hO]
    show |Margin.Bavg (Queue6.Hc X₀ r) (NTptLd θ X₀ ω : ℝ → ℝ) r| ≤ E
    rw [NTptLd_coe hc hev ω]
    refine abs_Bavg_le hHr fun q hq1 hq2 => ?_
    obtain ⟨-, -, -, hA, hB⟩ := hW q hq1 hq2
    rcases lt_or_ge q X₀ with hq | hq
    · rw [NTpt_low hc ω hp2 hq, abs_zero]; exact hE0
    have hrXm : Xm X₀ ≤ r := by
      by_contra h; push_neg at h; exact absurd (hA h) (not_lt.mpr hq)
    obtain ⟨c1, c2⟩ := hB hrXm
    have hrv : v ≤ r := by
      rcases hr.2 with h | h
      · rw [hv, h]; simpa using hrXm
      · exact h
    have hN2 := NTpt_abs_le_eta hc hev ω q
    have hs3 := etaS_nonneg hc hT i
    have hs4 := etaS_nonneg hc hT (i + 1)
    have hs5 : 0 ≤ (if i = 0 then 0 else etaS θ X₀ ω (i - 1)) := by
      split_ifs
      · exact le_rfl
      · exact etaS_nonneg hc hT _
    have hr2 := hr.1
    rcases lt_or_ge q v with h1 | h1
    · -- the block `i - 1`
      have hi : i ≠ 0 := by
        rintro rfl; simp [hv] at h1; linarith
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have e : Xm X₀ * 2 ^ (k + 1) = 2 * (Xm X₀ * 2 ^ k) := by ring
      have hv' : v = 2 * (Xm X₀ * 2 ^ k) := by rw [hv, e]
      have hk0 : 0 < Xm X₀ * 2 ^ k := by positivity
      have := etaG_le_etaS hc hT (i := k) (q := q) (by linarith) (by linarith)
      simp only [hE, if_neg hi, Nat.add_sub_cancel]
      linarith
    · rcases lt_or_ge q (2 * v) with h2 | h2
      · have := etaG_le_etaS hc hT (i := i) h1 h2
        simp only [hE]; linarith
      · have e : Xm X₀ * 2 ^ (i + 1) = 2 * v := by rw [hv]; ring
        have := etaG_le_etaS hc hT (i := i + 1) (q := q) (by rw [e]; exact h2)
          (by rw [e]; linarith)
        simp only [hE]; linarith
  -- assemble
  have eF : ((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
      ℝ → ℝ) r = (Margin.Bavg (Queue6.Hc X₀ r) (TcLd θ X₀ ω : ℝ → ℝ) r -
        (TcLd θ X₀ ω : ℝ → ℝ) r) + 0 -
      (nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0
        (NTd θ X₀ ω) : ℝ → ℝ) r - (NTd θ X₀ ω : ℝ → ℝ) r := rfl
  rw [eF]
  unfold FrBv
  rw [← hv, ← hE]
  have t1 := abs_sub (Margin.Bavg (Queue6.Hc X₀ r) (TcLd θ X₀ ω : ℝ → ℝ) r -
      (TcLd θ X₀ ω : ℝ → ℝ) r + 0 - (nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω)
        (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) : ℝ → ℝ) r) ((NTd θ X₀ ω : ℝ → ℝ) r)
  have t2 := abs_sub (Margin.Bavg (Queue6.Hc X₀ r) (TcLd θ X₀ ω : ℝ → ℝ) r -
      (TcLd θ X₀ ω : ℝ → ℝ) r + 0) ((nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω)
        (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) : ℝ → ℝ) r)
  simp only [add_zero] at t1 t2 ⊢
  linarith

end Pt2

variable (θ X₀) in
/-- **`F̄_r` at the scale `u`** (Lemma 5.34, first bullet): the sum of `F̄_r` over the blocks
meeting `[0.79u, 2.21u]`, which contains the windows of the levels of the scale `u`. -/
noncomputable def GK (ω : JitterΩ) (nb : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ i ∈ range (⌈2.21 * u / Xm X₀⌉₊ + 1),
    if (i = 0 ∨ Xm X₀ * 2 ^ i ≤ 2.21 * u) ∧ 0.79 * u < 2 * (Xm X₀ * 2 ^ i) then
      FrBv θ X₀ ω nb i else 0

variable (θ X₀) in
/-- `S(x) = ∑_{u ≤ x + H(x)/2} log(2u) F̄_r(u)`, over the dyadic scales `u = X₀2ᵏ/4`. -/
noncomputable def SK (ω : JitterΩ) (nb : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (Jc X₀ x + 3), Real.log (2 * ((X₀ : ℝ) * 2 ^ k / 4)) *
    GK θ X₀ ω nb ((X₀ : ℝ) * 2 ^ k / 4)

section Fields

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma GK_nonneg {ω : JitterΩ} {Z η1 η2 εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    {nb : ℕ → ℝ} (hnb : ∀ i, 0 ≤ nb i) (u : ℝ) : 0 ≤ GK θ X₀ ω nb u :=
  Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact FrBv_nonneg hc hev hT hnb i
    · exact le_rfl

omit hc hev in
/-- The block of a point: every `r` lies in some block `i`. -/
lemma exists_blk (hXm : 0 < Xm X₀) (r : ℝ) :
    ∃ i, InBlk X₀ i r ∧ (i = 0 ∨ Xm X₀ * 2 ^ i ≤ r) := by
  rcases lt_or_ge r (2 * Xm X₀) with h | h
  · exact ⟨0, ⟨by simpa using h, Or.inl rfl⟩, Or.inl rfl⟩
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := r / Xm X₀) (y := (2 : ℝ))
      (by rw [le_div_iff₀ hXm]; linarith) (by norm_num)
    rw [le_div_iff₀ hXm] at hn1
    rw [div_lt_iff₀ hXm, pow_succ] at hn2
    exact ⟨n, ⟨by linarith, Or.inr (by linarith)⟩, Or.inr (by linarith)⟩

set_option maxHeartbeats 4000000 in
/-- **The field `hFr`** of `RestRes` at `S = SK`, `FbK = GK` (Lemma 5.34, first bullet). -/
theorem hFr_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {nb : ℕ → ℝ} (hnu : Nu522 θ X₀ ω b nb) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      KR.TNP.FrScaleBound (PR θ X₀ ω) (Queue6.Hc X₀) X₀
        ((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
          ℝ → ℝ) x (SK θ X₀ ω nb x) (fun y => (NKc X₀ y).1)
        (fun _ u => GK θ X₀ ω nb u) := by
  intro hO x hx hxb y hy1 hy2
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hXmX := Xm_le_X0 hc
  have hXmh := Xm_half hc
  have hxX := htX_c hc hx
  have hHx : Queue6.Hc X₀ x ≤ x / 40 := by
    unfold Queue6.Hc; rw [max_eq_left hxX]; exact KR.WidthReal.capH_le_tenth hX hxX
  have hHx0 := (KR.WidthReal.Hc_pos hX (X₀ := X₀) x).le
  have hyX : (X₀ : ℝ) ≤ y := by
    have : 2 * (X₀ : ℝ) ≤ x := by
      have := htlog_c hc hx
      by_contra h; push_neg at h
      have h2 : Real.log x ≤ Real.log (2 * X₀) := Real.log_le_log (by linarith) h.le
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.log x ≥ 1.01 * Real.log X₀ := by
        have := Real.log_le_log (by positivity) hx
        rwa [Real.log_rpow (by linarith)] at this
      have := Real.log_two_lt_d9
      nlinarith
    linarith
  have hHy : Queue6.Hc X₀ y ≤ y / 40 := by
    unfold Queue6.Hc; rw [max_eq_left hyX]; exact KR.WidthReal.capH_le_tenth hX hyX
  have hnb0 := hnu.1
  refine ⟨fun u hu => ⟨GK_nonneg hc hev hT hnb0 u, fun n hn hn2 s hs => ?_⟩, ?_⟩
  · obtain ⟨k, -, rfl, huy⟩ := KR.TNP.mem_dyScales.mp hu
    set u := (X₀ : ℝ) * 2 ^ k / 4 with hudef
    have hu4 : (X₀ : ℝ) ≤ 4 * u := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      rw [hudef]; nlinarith
    have hu0 : 0 < u := by linarith
    obtain ⟨-, hp1, hp2⟩ := (KR.mem_NW (PR θ X₀ ω) hu0).mp hn
    set p := y / LemmaM.valN (PR θ X₀ ω).labelVal n with hpdef
    have hpp : posn (PR θ X₀ ω).labelVal y n = p := rfl
    rw [hpp] at hs
    have hHp : Queue6.Hc X₀ p ≤ 0.2 * u := by
      rcases le_or_gt (Xm X₀ / 2) p with h | h
      · have := hO.small p h; linarith
      · have := hO.low p h; linarith
    have hs' := abs_le.mp hs
    have hs1 : 0.79 * u < s := by linarith
    have hs2 : s ≤ 2.21 * u := by linarith
    have hsb : s ≤ b := by
      have h := (KR.TcLoc.osc_point_half (y := y) (n := n) hO (KR.WidthReal.Hc_mono hX)
        (by linarith) hn2 (s := s) (by rw [hpp]; exact hs)).2
      have hy3 : y ≤ 1.0125 * x := by linarith [hy2]
      linarith
    obtain ⟨i, hi, hi2⟩ := exists_blk hXm s
    have hFi := Fr_pt hc hev hb hbt hQC hE1 hN hT hnu hO hsb hi
    have hirange : i ∈ range (⌈2.21 * u / Xm X₀⌉₊ + 1) := by
      rw [Finset.mem_range]
      rcases hi2 with h | h
      · omega
      · have h1 : (2 : ℝ) ^ i ≤ 2.21 * u / Xm X₀ := by
          rw [le_div_iff₀ hXm]; linarith
        have h2 : (i : ℝ) < 2 ^ i := by exact_mod_cast Nat.lt_two_pow_self
        have h3 := Nat.le_ceil (2.21 * u / Xm X₀)
        have : (i : ℝ) < ⌈2.21 * u / Xm X₀⌉₊ := by linarith
        exact_mod_cast Nat.lt_succ_of_lt (by exact_mod_cast this)
    have hcond : (i = 0 ∨ Xm X₀ * 2 ^ i ≤ 2.21 * u) ∧ 0.79 * u < 2 * (Xm X₀ * 2 ^ i) := by
      refine ⟨?_, by linarith [hi.1]⟩
      rcases hi2 with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    refine hFi.trans ?_
    unfold GK
    refine le_trans ?_ (Finset.single_le_sum (f := fun i =>
      if (i = 0 ∨ Xm X₀ * 2 ^ i ≤ 2.21 * u) ∧ 0.79 * u < 2 * (Xm X₀ * 2 ^ i) then
        FrBv θ X₀ ω nb i else 0) (fun j _ => by
          dsimp only
          split_ifs
          · exact FrBv_nonneg hc hev hT hnb0 j
          · exact le_rfl) hirange)
    simp only [if_pos hcond, le_refl]
  · -- the scale sum
    set f : ℕ → ℝ := fun k => (X₀ : ℝ) * 2 ^ k / 4 with hf
    have hinj : Set.InjOn f ↑(Finset.range (Jc X₀ x + 3)) := by
      intro i _ j _ hij
      simp only [hf] at hij
      have h2 : (2 : ℝ) ^ i = 2 ^ j := by
        have := hij; field_simp at this; linarith
      exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2)
    set g : ℝ → ℝ := fun u => Real.log (2 * u) * GK θ X₀ ω nb u with hg
    have hS : SK θ X₀ ω nb x = ∑ u ∈ (Finset.range (Jc X₀ x + 3)).image f, g u := by
      rw [Finset.sum_image hinj]; rfl
    rw [hS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro u hu
      obtain ⟨k, -, rfl, huy⟩ := KR.TNP.mem_dyScales.mp hu
      refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr ?_, rfl⟩
      have hJ := Jc_spec hXm x
      have h1 : (X₀ : ℝ) * 2 ^ k / 4 ≤ X₀ * 2 ^ Jc X₀ x := by
        have : Xm X₀ * 2 ^ Jc X₀ x ≤ X₀ * 2 ^ Jc X₀ x :=
          mul_le_mul_of_nonneg_right hXmX (by positivity)
        linarith
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ (Jc X₀ x + 2) := by
        rw [pow_add]; nlinarith
      have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h2
      omega
    · intro u hu _
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact mul_nonneg (Real.log_nonneg (by simp only [hf]; nlinarith))
        (GK_nonneg hc hev hT hnb0 _)

/-- **The field `hFrB`** of `RestRes` at `FrB = FrBv` (Lemma 5.34, second bullet). -/
theorem hFrB_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {nb : ℕ → ℝ} (hnu : Nu522 θ X₀ ω b nb) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → ∀ i r, r ≤ x → r < 2 * (Xm X₀ * 2 ^ i) →
        (i = 0 ∨ Xm X₀ * 2 ^ i ≤ r) →
        |((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
          ℝ → ℝ) r| ≤ (fun _ i => FrBv θ X₀ ω nb i) x i :=
  fun hO _ _ hxb i _ hr hr1 hr2 =>
    Fr_pt hc hev hb hbt hQC hE1 hN hT hnu hO (hr.trans hxb) ⟨hr1, hr2⟩

end Fields

end BModel

end
