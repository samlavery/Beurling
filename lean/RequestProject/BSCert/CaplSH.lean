module

public import RequestProject.BSCert.Capl
meta import RequestProject.BSCert.Capl

/-!
# The break point `s_H = 5.9745…`

`analytic_capl.py`, `caplw_check_independent.py` and `raise_max.py` all compute `s_H`, the root
of `γ*(s_H) = 1/3 - 10⁻⁵`, by bisection on `[0, 10]`, and report `s_H = 5.9745…`
(Theorem 6.23 of the paper). We prove that this root exists, is unique in `[0, 10]`, and lies
in `(5.9745, 5.9746)`.
-/

@[expose] public section

namespace BSCert.Capl

open Real Set

/-- The target value `1/3 - 10⁻⁵`. -/
noncomputable def gTarget : ℝ := 1 / 3 - 1 / 100000

lemma log1e8_bounds : (18.42 : ℝ) ≤ Real.log 100000000 ∧ Real.log 100000000 ≤ 18.43 := by
  have h1 := logLoPt_le (a := 100000000) (by norm_num)
  have h2 := le_logHiPt (a := 100000000) (by norm_num)
  have c1 : (1842 / 100 : ℚ) ≤ logLoPt 100000000 := by native_decide
  have c2 : logHiPt 100000000 ≤ (1843 / 100 : ℚ) := by native_decide
  have c1' : ((1842 / 100 : ℚ) : ℝ) ≤ ((logLoPt 100000000 : ℚ) : ℝ) := by exact_mod_cast c1
  have c2' : ((logHiPt 100000000 : ℚ) : ℝ) ≤ ((1843 / 100 : ℚ) : ℝ) := by exact_mod_cast c2
  push_cast at h1 h2 c1' c2'
  constructor <;> linarith

lemma LamS_of_nonneg {s : ℝ} (hs : 0 ≤ s) : LamS s = 100000000 := by
  unfold LamS
  apply max_eq_left
  have : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- The pieces of `A(10⁸, s)` on `[0, 10]`. -/
lemma A8_eq {s : ℝ} (hs : 0 ≤ s) :
    A 100000000 s = Real.log 2 + 3 * Real.log 100000000 + 2 * s
      - Real.log (2 * Real.log 100000000 + s) :=
  A_eq (by norm_num) (by linarith [log1e8_bounds.1])

lemma A8_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 10) :
    0 < A 100000000 s ∧ A 100000000 s < 100000000 - 1 := by
  obtain ⟨h1, h2⟩ := log1e8_bounds
  rw [A8_eq hs0]
  have hl : 0 < 2 * Real.log 100000000 + s := by linarith
  have hl1 := Real.log_le_sub_one_of_pos hl
  have hl2 : 0 ≤ Real.log (2 * Real.log 100000000 + s) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  constructor <;> linarith

lemma A8_strictMono {s t : ℝ} (hs0 : 0 ≤ s) (hst : s < t) :
    A 100000000 s + (t - s) < A 100000000 t := by
  obtain ⟨h1, h2⟩ := log1e8_bounds
  rw [A8_eq hs0, A8_eq (by linarith)]
  have hl : 1 < 2 * Real.log 100000000 + s := by linarith
  have hl0 : 0 < 2 * Real.log 100000000 + s := by linarith
  have key : Real.log (2 * Real.log 100000000 + t) - Real.log (2 * Real.log 100000000 + s)
      < t - s := by
    rw [← Real.log_div (by linarith) hl0.ne']
    have := Real.log_le_sub_one_of_pos (x := (2 * Real.log 100000000 + t) /
      (2 * Real.log 100000000 + s)) (div_pos (by linarith) hl0)
    have e : (2 * Real.log 100000000 + t) / (2 * Real.log 100000000 + s) - 1
        = (t - s) / (2 * Real.log 100000000 + s) := by field_simp; ring
    have : (t - s) / (2 * Real.log 100000000 + s) < t - s := by
      rw [div_lt_iff₀ hl0]; nlinarith
    linarith
  linarith

lemma G8_strictMonoOn : StrictMonoOn (G 100000000) (Icc 0 10) := by
  intro s hs t ht hst
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hA0s, hA1s⟩ := A8_bounds hs0 hs1
  obtain ⟨hA0t, hA1t⟩ := A8_bounds ht0 ht1
  have hA := A8_strictMono hs0 hst
  unfold G
  set a := A 100000000 s
  set b := A 100000000 t
  have hab : a ≤ b := by linarith
  have hn1 : 0 < Real.sqrt (a * (a + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hn2 : Real.sqrt (a * (a + 1)) ≤ Real.sqrt (b * (b + 1)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have he : Real.exp (s / 2) < Real.exp (t / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hd1 : 0 < Real.sqrt (100000000 - b - 1) := Real.sqrt_pos.mpr (by linarith)
  have hd2 : Real.sqrt (100000000 - b - 1) ≤ Real.sqrt (100000000 - a - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hnum : 2 * Real.sqrt (a * (a + 1)) * Real.exp (s / 2)
      < 2 * Real.sqrt (b * (b + 1)) * Real.exp (t / 2) := by
    have := Real.exp_pos (s / 2)
    nlinarith
  calc 2 * Real.sqrt (a * (a + 1)) * Real.exp (s / 2) / Real.sqrt (100000000 - a - 1)
      ≤ 2 * Real.sqrt (a * (a + 1)) * Real.exp (s / 2) / Real.sqrt (100000000 - b - 1) := by
        apply div_le_div_of_nonneg_left (by positivity) hd1 hd2
    _ < 2 * Real.sqrt (b * (b + 1)) * Real.exp (t / 2) / Real.sqrt (100000000 - b - 1) := by
        apply div_lt_div_of_pos_right hnum hd1

lemma G8_continuousOn : ContinuousOn (G 100000000) (Icc 0 10) := by
  have hl : ∀ s ∈ Icc (0 : ℝ) 10, 0 < 2 * Real.log 100000000 + s := fun s hs => by
    linarith [log1e8_bounds.1, hs.1]
  have hAc : ContinuousOn (fun s => A 100000000 s) (Icc 0 10) := by
    unfold A
    apply ContinuousOn.log
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro s hs; exact (hl s hs).ne'
    · intro s hs; exact (div_pos (by positivity) (hl s hs)).ne'
  unfold G
  apply ContinuousOn.div
  · apply ContinuousOn.mul _ (by fun_prop)
    apply ContinuousOn.mul continuousOn_const
    exact (hAc.mul (hAc.add continuousOn_const)).sqrt
  · exact ((continuousOn_const.sub hAc).sub continuousOn_const).sqrt
  · intro s hs
    have := (A8_bounds hs.1 hs.2).2
    exact (Real.sqrt_pos.mpr (by linarith)).ne'

/-! ## Interval evaluation of `γ*` at the two ends -/

/-- `γ*(s)` for `s ≥ 0` as an expression in `s = var 0`. -/
def gEx : Ex :=
  .lett (.log (.cst 100000000))
    (.lett (.log (.cst 2) + .cst 3 * .var 1 + .cst 2 * .var 0 - .log (.cst 2 * .var 1 + .var 0))
      (.cst (13 / 10) * (.cst 2 * .sqrt (.var 2 * (.var 2 + .cst 1)) * .exp (.var 0 / .cst 2)
        / .sqrt (.cst 100000000 - .var 2 - .cst 1))))

lemma gEx_eval {s : ℝ} (hs0 : 0 ≤ s) : Ex.eval gEx [s] = gstar s := by
  unfold gstar
  rw [LamS_of_nonneg hs0]
  unfold G
  rw [A8_eq hs0]
  simp [gEx, Ex.eval]
  norm_num

/-- Upper check: `iHi e ienv < t`. -/
def checkHi (e : Ex) (ienv : List Itv) (t : ℚ) : Bool :=
  match Ex.iHi e ienv with
  | some q => decide (q < t)
  | none => false

/-- Lower check: `t < iLo e ienv`. -/
def checkLo (e : Ex) (ienv : List Itv) (t : ℚ) : Bool :=
  match Ex.iLo e ienv with
  | some q => decide (t < q)
  | none => false

lemma checkHi_sound {e : Ex} {env : List ℝ} {ienv : List Itv} {t : ℚ} (h : Ex.EnvMem env ienv)
    (hc : checkHi e ienv t = true) : Ex.eval e env < t := by
  unfold checkHi at hc
  split at hc
  · rename_i q hq
    have := Ex.iHi_sound h hq
    have : (q : ℝ) < t := by exact_mod_cast of_decide_eq_true hc
    linarith
  · cases hc

lemma checkLo_sound {e : Ex} {env : List ℝ} {ienv : List Itv} {t : ℚ} (h : Ex.EnvMem env ienv)
    (hc : checkLo e ienv t = true) : (t : ℝ) < Ex.eval e env := by
  unfold checkLo at hc
  split at hc
  · rename_i q hq
    have := Ex.iLo_sound h hq
    have : (t : ℝ) < q := by exact_mod_cast of_decide_eq_true hc
    linarith
  · cases hc

lemma envMem_pt (q : ℚ) : Ex.EnvMem [(q : ℝ)] [Itv.pt q] :=
  List.Forall₂.cons (Itv.mem_pt q) List.Forall₂.nil

lemma gstar_at_lo : gstar 5.9745 < gTarget := by
  have hc : checkHi gEx [Itv.pt (59745 / 10000)] (1 / 3 - 1 / 100000) = true := by native_decide
  have h := checkHi_sound (envMem_pt _) hc
  rw [gEx_eval (by norm_num)] at h
  unfold gTarget
  norm_num at h ⊢
  exact h

lemma gstar_at_hi : gTarget < gstar 5.9746 := by
  have hc : checkLo gEx [Itv.pt (59746 / 10000)] (1 / 3 - 1 / 100000) = true := by native_decide
  have h := checkLo_sound (envMem_pt _) hc
  rw [gEx_eval (by norm_num)] at h
  unfold gTarget
  norm_num at h ⊢
  exact h

lemma gstar_eq_on {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 10) : gstar s = 1.3 * G 100000000 s := by
  unfold gstar; rw [LamS_of_nonneg hs.1]

/-- **The break point `s_H`.** The equation `γ*(s) = 1/3 - 10⁻⁵` has exactly one solution in
`[0, 10]`, and it lies in `(5.9745, 5.9746)`. -/
theorem sH_spec : ∃ sH ∈ Ioo (5.9745 : ℝ) 5.9746, gstar sH = gTarget ∧
    ∀ s ∈ Icc (0 : ℝ) 10, gstar s = gTarget → s = sH := by
  have hmono : StrictMonoOn gstar (Icc 0 10) := by
    intro s hs t ht hst
    rw [gstar_eq_on hs, gstar_eq_on ht]
    have := G8_strictMonoOn hs ht hst
    linarith
  have hcont : ContinuousOn gstar (Icc 5.9745 5.9746) := by
    have : ContinuousOn (fun s => 1.3 * G 100000000 s) (Icc 5.9745 5.9746) :=
      continuousOn_const.mul (G8_continuousOn.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    refine this.congr (fun s hs => ?_)
    exact gstar_eq_on ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨sH, hsH, hval⟩ := intermediate_value_Icc (by norm_num) hcont
    ⟨gstar_at_lo.le, gstar_at_hi.le⟩
  have hsH' : sH ∈ Icc (0 : ℝ) 10 := ⟨by linarith [hsH.1], by linarith [hsH.2]⟩
  refine ⟨sH, ⟨?_, ?_⟩, hval, fun s hs hs' => ?_⟩
  · rcases eq_or_lt_of_le hsH.1 with h | h
    · rw [← h] at hval; linarith [gstar_at_lo]
    · exact h
  · rcases eq_or_lt_of_le hsH.2 with h | h
    · rw [h] at hval; linarith [gstar_at_hi]
    · exact h
  · exact hmono.injOn hs hsH' (hs'.trans hval.symm)

end BSCert.Capl
