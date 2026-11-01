module

public import RequestProject.Beurling.Noise.KRVarStep
public import RequestProject.Beurling.Noise.KRBound

/-!
# Theorem 5.15 (KR bound, nominal filters, varying widths)

The nominal kernels of §5.9.1 with the width `H(v/w)` taken at the actual landing centre:

  `C_1 = δ_x`,  `C_n = -∑_{d ∣ n, d < n} κ_{d→n} 𝒬_{n/d} C_d`,
  `𝒬_w ν = ∫ bx_{H(v/w)}(· - v/w) dν(v)`,

in the distribution-function model, with the step `Qv` of `KRVarStep.lean` (`kerV`). Write
`p_n = x/n` (`posn`) and `H_n = H(x/n)`.

* `kerV_kr` : the KR bound `‖C_n - c_n δ_{x/n}‖_KR ≤ ¼ ∑_{e ∣ n, e > 1} |c_e| H_e H_ord(n/e) e/n`
  for every `n ≥ 1`. This is the paper's KR bound with `λ₀` replaced by `1`: our (Q1) has the
  exact factor `1/w` (see `KRn_Qv_le`). Since `λ₀ ≥ 1`, it implies the paper's.
* `kerV_support` : `C_n - c_n δ_{x/n}` lives in `[x/n - ρ H_n, x/n + ρ H_n]`, under the
  radius condition `hW1` (paper, §5.9.1: `R_n ≤ 1.02 H(x/n)`).
* `theorem_5_15` : **Theorem 5.15**,
  `TV(C_n) ≤ |c_n| + ½ λ₀ ∑_{e ∣ n, 1<e<n} |c_e| (H_e/H_n) H_ord(n/e) e/n` and the KR bound with
  `¼ λ₀`, under the width condition `hW2` on the supports (`(2 + |H'|)/H ≤ 2λ₀/H_n`), which is
  where the paper's `(1 + 3ϑ)` factors enter. `KRVarWidth.lean` derives `hW1`, `hW2` from the
  paper's hypotheses on `H`.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

variable (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (κ : ℕ → ℕ → ℝ)

/-- The position `x/n` of the level `n`. -/
noncomputable def posn (n : ℕ) : ℝ := x / LemmaM.valN val n

/-- The distribution function of the nominal kernel `C_n` with varying widths. -/
noncomputable def kerV (n : ℕ) : ℝ → ℝ :=
  if n ≤ 1 then (if n = 1 then stepF x else fun _ => 0) else
    fun t => - ∑ d ∈ n.properDivisors.attach,
      κ d.1 n * Qv H (LemmaM.valN val (n / d.1)) (kerV d.1) t
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

lemma kerV_zero : kerV val x H κ 0 = fun _ => 0 := by rw [kerV]; simp

lemma kerV_one : kerV val x H κ 1 = stepF x := by rw [kerV]; simp

lemma kerV_eq {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    kerV val x H κ n t = - ∑ d ∈ n.properDivisors,
      κ d n * Qv H (LemmaM.valN val (n / d)) (kerV val x H κ d) t := by
  rw [kerV, if_neg (by omega)]
  congr 1
  exact Finset.sum_attach n.properDivisors
    (fun d => κ d n * Qv H (LemmaM.valN val (n / d)) (kerV val x H κ d) t)

/-- `D_n = C_n - c_n δ_{x/n}`. -/
noncomputable def DkerV (n : ℕ) (t : ℝ) : ℝ :=
  kerV val x H κ n t - mass κ n * stepF (posn val x n) t

/-- The frozen widths `H_e = H(x/e)`. -/
noncomputable def Hlev (e : ℕ) : ℝ := H (posn val x e)

variable {val x H κ}

lemma posn_div (hval : ∀ p, p.Prime → 1 ≤ val p) {d n : ℕ} (hdn : d ∣ n) (hn : n ≠ 0) :
    posn val x d / LemmaM.valN val (n / d) = posn val x n := by
  unfold posn
  rw [valN_div_mul hval hdn hn]
  have h1 := LemmaM.valN_pos val hval (n := d)
  have h2 := LemmaM.valN_pos val hval (n := n / d)
  field_simp

/-- The representation behind (Dn-rec), varying widths:
`C_n = c_n bx_{H_n}(· - x/n) - ∑ κ_{d→n} 𝒬_{n/d} D_d`. -/
lemma kerV_rep (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H) {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ d ∈ n.properDivisors, BM (kerV val x H κ d)) (t : ℝ) :
    kerV val x H κ n t = mass κ n * boxAvg (Hlev val x H n) (stepF (posn val x n)) t -
      ∑ d ∈ n.properDivisors, κ d n *
        Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t := by
  have hn0 : n ≠ 0 := by omega
  rw [kerV_eq val x H κ hn, mass_eq κ hn]
  have hterm : ∀ d ∈ n.properDivisors,
      κ d n * Qv H (LemmaM.valN val (n / d)) (kerV val x H κ d) t =
        κ d n * Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t +
          κ d n * mass κ d * boxAvg (Hlev val x H n) (stepF (posn val x n)) t := by
    intro d hd
    have hdn := (Nat.mem_properDivisors.mp hd).1
    have hw := LemmaM.valN_pos val hval (n := n / d)
    have hBMD : BM (DkerV val x H κ d) := (ih d hd).sub ((BM_stepF _).const_mul _)
    have e1 : ∀ v, kerV val x H κ d v = DkerV val x H κ d v +
        mass κ d * stepF (posn val x d) v := fun v => by unfold DkerV; ring
    rw [Qv_congr e1, Qv_add hH hw hBMD ((BM_stepF _).const_mul _), Qv_const_mul,
      Qv_stepF hH hw, Kv_eq_boxAvg hH, posn_div hval hdn hn0]
    unfold Hlev
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

lemma one_le_of_mem_pd {d n : ℕ} (hd : d ∈ n.properDivisors) : 1 ≤ d :=
  one_le_of_mem_properDivisors hd

/-- **The KR bound of Theorem 5.15** (with `λ₀` replaced by `1`), and boundedness. -/
theorem kerV_kr (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H)
    (hκ : ∀ d n, |κ d n| ≤ 1) :
    ∀ n, BM (kerV val x H κ n) ∧
      (1 ≤ n → KRn (DkerV val x H κ n) ≤ ENNReal.ofReal (KRB val (Hlev val x H) κ n)) := by
  have hHl : ∀ n, 0 < Hlev val x H n := fun n => hH.pos _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [kerV_zero]; exact ⟨BM_zero, fun h => absurd h (by norm_num)⟩
    · refine ⟨by rw [kerV_one]; exact BM_stepF x, fun _ => ?_⟩
      rw [KRB_one]
      have : DkerV val x H κ 1 = fun _ => 0 := by
        funext t; unfold DkerV posn
        rw [kerV_one, mass_one, LemmaM.valN_one, div_one]; ring
      rw [this]; simp [KRn]
  have ihBM : ∀ d ∈ n.properDivisors, BM (kerV val x H κ d) :=
    fun d hd => (ih d (Nat.mem_properDivisors.mp hd).2).1
  have ihKR : ∀ d ∈ n.properDivisors,
      KRn (DkerV val x H κ d) ≤ ENNReal.ofReal (KRB val (Hlev val x H) κ d) :=
    fun d hd => (ih d (Nat.mem_properDivisors.mp hd).2).2 (one_le_of_mem_pd hd)
  have hBMD : ∀ d ∈ n.properDivisors, BM (DkerV val x H κ d) :=
    fun d hd => (ihBM d hd).sub ((BM_stepF _).const_mul _)
  set h := Hlev val x H n
  have hh : 0 < h := hHl n
  set a := posn val x n
  set Sf : ℝ → ℝ := fun t => ∑ d ∈ n.properDivisors, κ d n *
    Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t
  have hBMS : BM Sf := BM.finset_sum _ fun d hd =>
    (BM.Qv hH (LemmaM.valN_pos val hval) (hBMD d hd)).const_mul _
  have hrep := kerV_rep (κ := κ) hval hH hn ihBM
  refine ⟨?_, fun _ => ?_⟩
  · have : kerV val x H κ n = fun t => mass κ n * boxAvg h (stepF a) t - Sf t := funext hrep
    rw [this]
    exact (((BM_stepF a).boxAvg hh).const_mul _).sub hBMS
  have hD : DkerV val x H κ n = fun t =>
      mass κ n * (boxAvg h (stepF a) t - stepF a t) + -Sf t := by
    funext t; unfold DkerV; rw [hrep]; ring
  rw [hD]
  have hm1 : Measurable fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t) :=
    measurable_const.mul ((continuous_boxAvg (BM_stepF a) h).measurable.sub (measurable_stepF a))
  have hKRB : ∀ d ∈ n.properDivisors,
      0 ≤ (LemmaM.valN val (n / d))⁻¹ * KRB val (Hlev val x H) κ d :=
    fun d _ => mul_nonneg (inv_pos.mpr (LemmaM.valN_pos val hval)).le (KRB_nonneg κ hval hHl d)
  have hKRS : KRn (fun t => -Sf t) ≤ ∑ d ∈ n.properDivisors,
      ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val (Hlev val x H) κ d) := by
    rw [KRn_neg]
    refine (KRn_sum_le _ fun d hd => ?_).trans (Finset.sum_le_sum fun d hd => ?_)
    · exact measurable_const.mul (BM.Qv hH (LemmaM.valN_pos val hval) (hBMD d hd)).1
    · rw [KRn_const_mul]
      have hw := LemmaM.valN_pos val hval (n := n / d)
      calc ENNReal.ofReal |κ d n| * KRn (Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d))
          ≤ 1 * (ENNReal.ofReal (LemmaM.valN val (n / d))⁻¹ *
              ENNReal.ofReal (KRB val (Hlev val x H) κ d)) := by
            gcongr
            · exact ENNReal.ofReal_le_one.mpr (hκ d n)
            · exact (KRn_Qv_le hH hw (hBMD d hd).1).trans (by gcongr; exact ihKR d hd)
        _ = _ := by rw [one_mul, ENNReal.ofReal_mul (inv_pos.mpr hw).le]
  calc KRn (fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t) + -Sf t)
      ≤ KRn (fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t)) + KRn (fun t => -Sf t) :=
        KRn_add_le hm1
    _ ≤ ENNReal.ofReal |mass κ n| * ENNReal.ofReal (h / 4) +
          ∑ d ∈ n.properDivisors,
            ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val (Hlev val x H) κ d) := by
        gcongr
        rw [KRn_const_mul]
        gcongr
        exact KRn_box_sub_step_le hh a
    _ = ENNReal.ofReal (KRB val (Hlev val x H) κ n) := by
        rw [KRB_rec val (Hlev val x H) κ hval hn, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_sum_of_nonneg hKRB,
          ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (by positivity))
            (Finset.sum_nonneg hKRB)]
        congr 1; ring

/-! ## Total variation of combinations -/

lemma eVariationOn_add_le (f g : ℝ → ℝ) :
    eVariationOn (fun t => f t + g t) univ ≤ eVariationOn f univ + eVariationOn g univ := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hs⟩ := p
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le (f := f) (n := n) hu hs) (eVariationOn.sum_le (f := g) (n := n) hu hs)

lemma eVariationOn_const_mul_le (c : ℝ) (f : ℝ → ℝ) :
    eVariationOn (fun t => c * f t) univ ≤ ENNReal.ofReal |c| * eVariationOn f univ := by
  conv_rhs => unfold eVariationOn
  unfold eVariationOn
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => le_iSup_of_le p ?_
  obtain ⟨n, u, hu, hs⟩ := p
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => le_of_eq ?_
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub, ← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs]

lemma eVariationOn_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ) :
    eVariationOn (fun t => ∑ i ∈ s, c i * f i t) univ ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * eVariationOn (f i) univ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : eVariationOn (fun _ : ℝ => (0 : ℝ)) univ = 0 :=
      eVariationOn.constant_on (by simp)
    rw [this]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (eVariationOn_add_le _ _).trans (add_le_add (eVariationOn_const_mul_le _ _) ih)

lemma eVariationOn_box_step_le {h : ℝ} (hh : 0 < h) (a : ℝ) :
    eVariationOn (boxAvg h (stepF a)) univ ≤ 1 := by
  refine (eVariationOn_boxAvg_le (BM_stepF a) hh).trans (le_of_eq ?_)
  rw [lintegral_step_shift_sub a hh, ← ENNReal.ofReal_mul (inv_pos.mpr hh).le,
    inv_mul_cancel₀ hh.ne', ENNReal.ofReal_one]

/-! ## Supports and Theorem 5.15 -/

/-- The radius condition of §5.9.1 (`R_n ≤ ρ H(x/n)`, `ρ = 1.02` in the paper): for a step
`d → n` with `κ_{d→n} ≠ 0`, every `y` with `|y - x/n| ≤ ρ H_d/(n/d)` has
`ρ H_d/(n/d) + H(y)/2 ≤ ρ H_n`. -/
def RadiusCond (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (κ : ℕ → ℕ → ℝ) (ρ : ℝ) : Prop :=
  ∀ n, 2 ≤ n → ∀ d ∈ n.properDivisors, κ d n ≠ 0 → ∀ y,
    |y - posn val x n| ≤ ρ * Hlev val x H d / LemmaM.valN val (n / d) →
      ρ * Hlev val x H d / LemmaM.valN val (n / d) + H y / 2 ≤ ρ * Hlev val x H n

/-- The width condition on the supports (where the paper's `(1 + 3ϑ)` enters): for a step
`d → n` with `κ_{d→n} ≠ 0` and `|v - x/d| ≤ ρ H_d`, `(2 + |H'(v/w)|)/H(v/w) ≤ 2λ₀/H_n`,
`w = n/d`. -/
def WidthCond (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (κ : ℕ → ℕ → ℝ) (ρ lam0 : ℝ) : Prop :=
  ∀ n, 2 ≤ n → ∀ d ∈ n.properDivisors, κ d n ≠ 0 → ∀ v,
    |v - posn val x d| ≤ ρ * Hlev val x H d →
      (2 + |deriv H (v / LemmaM.valN val (n / d))|) / H (v / LemmaM.valN val (n / d)) ≤
        2 * lam0 / Hlev val x H n

/-- **Support of the kernels**: `D_n = C_n - c_n δ_{x/n}` vanishes off `[x/n ± ρ H_n]`. -/
theorem kerV_support (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H)
    (hκ : ∀ d n, |κ d n| ≤ 1) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hW1 : RadiusCond val x H κ ρ) :
    ∀ n, 1 ≤ n → ∀ t, ρ * Hlev val x H n < |t - posn val x n| → DkerV val x H κ n t = 0 := by
  have hmain := kerV_kr (x := x) hval hH hκ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn1 t ht
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    unfold DkerV posn
    rw [kerV_one, mass_one, LemmaM.valN_one, div_one]; ring
  have hn0 : n ≠ 0 := by omega
  have ihBM : ∀ d ∈ n.properDivisors, BM (kerV val x H κ d) := fun d _ => (hmain d).1
  have hh := hH.pos (posn val x n)
  unfold DkerV
  rw [kerV_rep (κ := κ) hval hH hn ihBM]
  have h1 : boxAvg (Hlev val x H n) (stepF (posn val x n)) t - stepF (posn val x n) t = 0 := by
    have := abs_boxAvg_step_sub_le hh (posn val x n) t
    rw [Set.indicator_of_notMem] at this
    · exact abs_nonpos_iff.mp this
    · intro hm
      have : |t - posn val x n| ≤ Hlev val x H n / 2 := by
        rw [abs_le]; unfold Hlev at *; constructor <;> linarith [hm.1, hm.2]
      unfold Hlev at *
      nlinarith
  have h2 : ∀ d ∈ n.properDivisors, κ d n *
      Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t = 0 := by
    intro d hd
    by_cases hk : κ d n = 0
    · rw [hk, zero_mul]
    have hdn := (Nat.mem_properDivisors.mp hd).1
    have hdlt := (Nat.mem_properDivisors.mp hd).2
    have hw := LemmaM.valN_pos val hval (n := n / d)
    rw [Qv_eq_zero_of_support hw (p := posn val x d) (R := ρ * Hlev val x H d)
      (R' := ρ * Hlev val x H n) (fun v hv => ih d hdlt (one_le_of_mem_pd hd) v hv) ?_ ?_,
      mul_zero]
    · intro y hy
      rw [posn_div hval hdn hn0] at hy
      exact hW1 n hn d hd hk y hy
    · rw [posn_div hval hdn hn0]; exact ht
  have : mass κ n * boxAvg (Hlev val x H n) (stepF (posn val x n)) t -
      ∑ d ∈ n.properDivisors, κ d n * Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t -
      mass κ n * stepF (posn val x n) t =
      mass κ n * (boxAvg (Hlev val x H n) (stepF (posn val x n)) t -
        stepF (posn val x n) t) -
      ∑ d ∈ n.properDivisors, κ d n * Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t := by
    ring
  rw [this, h1, Finset.sum_eq_zero h2]; ring

/-- **Theorem 5.15 (KR bound, nominal filters, varying widths)**: for every start `x` and every
`n ≥ 2`, under the radius and width conditions,
* `TV(C_n) ≤ |c_n| + ½ λ₀ ∑_{e ∣ n, 1<e<n} |c_e| (H_e/H_n) H_ord(n/e) e/n`;
* `‖C_n - c_n δ_{x/n}‖_KR ≤ ¼ λ₀ ∑_{e ∣ n, e>1} |c_e| H_e H_ord(n/e) e/n` (`λ₀ ≥ 1`). -/
theorem theorem_5_15 (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H)
    (hκ : ∀ d n, |κ d n| ≤ 1) {ρ lam0 : ℝ} (hρ : 1 / 2 ≤ ρ) (hlam : 1 ≤ lam0)
    (hW1 : RadiusCond val x H κ ρ) (hW2 : WidthCond val x H κ ρ lam0) {n : ℕ} (hn : 2 ≤ n) :
    eVariationOn (kerV val x H κ n) univ ≤ ENNReal.ofReal (|mass κ n| + 1 / 2 * lam0 *
      ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n),
        |mass κ e| * (Hlev val x H e / Hlev val x H n) * (BSCert.X0Band.Hord (n / e) : ℝ) *
          (LemmaM.valN val e / LemmaM.valN val n)) ∧
    KRn (DkerV val x H κ n) ≤ ENNReal.ofReal (1 / 4 * lam0 *
      ∑ e ∈ n.divisors.filter (1 < ·), |mass κ e| * Hlev val x H e *
        (BSCert.X0Band.Hord (n / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val n)) := by
  have hmain := kerV_kr (x := x) hval hH hκ
  have hsupp := kerV_support (x := x) hval hH hκ hρ hW1
  have hHl : ∀ n, 0 < Hlev val x H n := fun n => hH.pos _
  have hKRB0 := KRB_nonneg κ hval hHl
  constructor
  swap
  · refine ((hmain n).2 (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 := hKRB0 n
    unfold KRB at h0 ⊢
    nlinarith
  have ihBM : ∀ d ∈ n.properDivisors, BM (kerV val x H κ d) := fun d _ => (hmain d).1
  have hBMD : ∀ d ∈ n.properDivisors, BM (DkerV val x H κ d) :=
    fun d hd => (ihBM d hd).sub ((BM_stepF _).const_mul _)
  set h := Hlev val x H n
  have hh : 0 < h := hHl n
  set a := posn val x n
  have hrep : kerV val x H κ n = fun t => mass κ n * boxAvg h (stepF a) t +
      ∑ d ∈ n.properDivisors, (-κ d n) *
        Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d) t := by
    funext t; rw [kerV_rep (κ := κ) hval hH hn ihBM]
    simp only [neg_mul, Finset.sum_neg_distrib]; ring
  -- each step term
  have hterm : ∀ d ∈ n.properDivisors, ENNReal.ofReal |-κ d n| *
      eVariationOn (Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d)) univ ≤
      ENNReal.ofReal (lam0 * (h⁻¹ * (2 * ((LemmaM.valN val (n / d))⁻¹ *
        KRB val (Hlev val x H) κ d)))) := by
    intro d hd
    by_cases hk : κ d n = 0
    · rw [hk, neg_zero, abs_zero, ENNReal.ofReal_zero, zero_mul]; exact zero_le
    have hw := LemmaM.valN_pos val hval (n := n / d)
    have hq := eVariationOn_Qv_le hH hw (hBMD d hd)
    have hpt : ∀ v, ‖DkerV val x H κ d v‖ₑ *
        ENNReal.ofReal ((2 + |deriv H (v / LemmaM.valN val (n / d))|) /
          (LemmaM.valN val (n / d) * H (v / LemmaM.valN val (n / d)))) ≤
        ‖DkerV val x H κ d v‖ₑ *
          ENNReal.ofReal (2 * lam0 / h * (LemmaM.valN val (n / d))⁻¹) := by
      intro v
      by_cases hv : ρ * Hlev val x H d < |v - posn val x d|
      · rw [hsupp d (one_le_of_mem_pd hd) v hv]; simp
      push_neg at hv
      gcongr
      have := hW2 n hn d hd hk v hv
      have hp := hH.pos (v / LemmaM.valN val (n / d))
      rw [mul_comm (LemmaM.valN val (n / d)), ← div_div]
      exact div_le_div_of_nonneg_right this hw.le |>.trans_eq (by ring)
    have hint := lintegral_mono (μ := volume) hpt
    rw [lintegral_mul_const _ (hBMD d hd).1.enorm] at hint
    calc ENNReal.ofReal |-κ d n| *
          eVariationOn (Qv H (LemmaM.valN val (n / d)) (DkerV val x H κ d)) univ
        ≤ 1 * ((∫⁻ v, ‖DkerV val x H κ d v‖ₑ) *
            ENNReal.ofReal (2 * lam0 / h * (LemmaM.valN val (n / d))⁻¹)) := by
          gcongr
          · rw [abs_neg]; exact ENNReal.ofReal_le_one.mpr (hκ d n)
          · exact hq.trans hint
      _ ≤ ENNReal.ofReal (KRB val (Hlev val x H) κ d) *
            ENNReal.ofReal (2 * lam0 / h * (LemmaM.valN val (n / d))⁻¹) := by
          rw [one_mul]; gcongr; exact (hmain d).2 (one_le_of_mem_pd hd)
      _ = ENNReal.ofReal (lam0 * (h⁻¹ * (2 * ((LemmaM.valN val (n / d))⁻¹ *
            KRB val (Hlev val x H) κ d)))) := by
          rw [← ENNReal.ofReal_mul (hKRB0 d)]; congr 1; field_simp
  have hnn : ∀ d ∈ n.properDivisors, 0 ≤ lam0 * (h⁻¹ * (2 * ((LemmaM.valN val (n / d))⁻¹ *
      KRB val (Hlev val x H) κ d))) := fun d _ => by
    have := hKRB0 d
    have := LemmaM.valN_pos val hval (n := n / d)
    positivity
  rw [hrep]
  refine (eVariationOn_add_le _ _).trans ?_
  refine (add_le_add (eVariationOn_const_mul_le _ _)
    ((eVariationOn_sum_le _ _ _).trans (Finset.sum_le_sum hterm))).trans ?_
  refine (add_le_add (mul_le_of_le_one_right (zero_le) (eVariationOn_box_step_le hh a))
    le_rfl).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (abs_nonneg _)
    (Finset.sum_nonneg hnn)]
  congr 1
  have hT := TVB_eq val (Hlev val x H) κ hval hHl hn
  unfold TVB at hT
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have : (∑ d ∈ n.properDivisors, 2 * ((LemmaM.valN val (n / d))⁻¹ *
      KRB val (Hlev val x H) κ d)) = h * (1 / 2 *
      ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n),
        |mass κ e| * (Hlev val x H e / h) * (BSCert.X0Band.Hord (n / e) : ℝ) *
          (LemmaM.valN val e / LemmaM.valN val n)) := by
    set S := ∑ d ∈ n.properDivisors, 2 * ((LemmaM.valN val (n / d))⁻¹ *
      KRB val (Hlev val x H) κ d)
    set X := 1 / 2 * ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n),
        |mass κ e| * (Hlev val x H e / h) * (BSCert.X0Band.Hord (n / e) : ℝ) *
          (LemmaM.valN val e / LemmaM.valN val n)
    calc S = h * (h⁻¹ * (|mass κ n| * h + S)) - |mass κ n| * h := by
          field_simp; ring
      _ = h * (|mass κ n| + X) - |mass κ n| * h := by rw [← hT]
      _ = h * X := by ring
  rw [this]
  field_simp

end KR

end
