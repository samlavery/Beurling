module

public import RequestProject.Beurling.Noise.KRTrueStep
public import RequestProject.Beurling.Noise.KRVar

/-!
# The kernels with filters at the actual centre (§5.9.4), in density form

Fix a start `x`, a width function `H` and, for every step `d → n` (`w = n/d`), a filter
`φ_{d→n}(c)` evaluated at the actual centre `c` of the window (for the true kernels of
Proposition 5.18, `φ_{d→n}(c) = 1[τ_w < c] 1[c ≥ X₀⁻]`; for the nominal kernels it is the constant
`κ_{d→n}`). The kernels are given by the last-step recursion (kernel-rec):

  `C_1 = δ_x`,  `C_n = -∑_{d ∣ n, d < n} ∫ φ_{d→n}(v/w) bx_{H(v/w)}(· - v/w) dC_d(v)`.

For `n ≥ 2`, `C_n` is absolutely continuous; `gK φ n` is its density (`C_1 = δ_x` is treated
explicitly: its step lands at the nominal point `x/n`). We prove:

* `integrable_gK` : the densities are integrable and measurable (`|φ| ≤ 1`, `φ` measurable);
* `kerV_eq_cdf` : for constant filters `κ`, `kerV` (the nominal kernels of Theorem 5.15, in
  distribution-function form) is the distribution function of `gK κ`; hence
  `lintegral_gK_nom_le` : `TV(C_n^nom) = ∫ |g_n| ≤ eVariationOn (kerV n)` (`KRTrueTV.lean`);
* the **Duhamel form** of Proposition 5.18: `Ẽ_n = C_n - C_n^nom` satisfies
  `Ẽ_n = S_n + ∑_{d<n} P^nom_{d→n} Ẽ_d` (`Etil_eq`), with the source
  `S_n = ∑_{d<n} (P_{d→n} - P^nom_{d→n}) C_d` (`Ssrc`), and by induction
  `Ẽ_n = ∑_{n' ∣ n, n' ≥ 2} 𝒯^nom_{n'→n} S_{n'}` (`Etil_eq_chain`), where `𝒯^nom` is the signed sum
  over nominal chains (`Tch`);
* `lintegral_Ssrc_le` : (K5) `TV(S_n) ≤ ∑_{d<n} ∫ |φ_{d→n}(v/w) - κ_{d→n}| |dC_d(v)|`.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

variable (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ)

/-- The density of the kernel `C_n` (`n ≥ 2`; `0` for `n ≤ 1`, `C_1 = δ_x` being treated
explicitly in the recursion) with the filters `φ_{d→n}(c)` at the actual centre. -/
noncomputable def gK (φ : ℕ → ℕ → ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  if n ≤ 1 then fun _ => 0 else
    fun t => - ∑ d ∈ n.properDivisors.attach,
      (if d.1 = 1 then φ 1 n (posn val x n) * kd H (posn val x n) t else
        Qd H (LemmaM.valN val (n / d.1))
          (fun v => φ d.1 n (v / LemmaM.valN val (n / d.1)) * gK φ d.1 v) t)
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

/-- The step from `d` to `n` (density at `t`). -/
noncomputable def stepK (φ : ℕ → ℕ → ℝ → ℝ) (d n : ℕ) (t : ℝ) : ℝ :=
  if d = 1 then φ 1 n (posn val x n) * kd H (posn val x n) t else
    Qd H (LemmaM.valN val (n / d)) (fun v => φ d n (v / LemmaM.valN val (n / d)) *
      gK val x H φ d v) t

lemma gK_le_one {φ : ℕ → ℕ → ℝ → ℝ} {n : ℕ} (hn : n ≤ 1) : gK val x H φ n = fun _ => 0 := by
  rw [gK, if_pos hn]

lemma gK_eq {φ : ℕ → ℕ → ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    gK val x H φ n t = - ∑ d ∈ n.properDivisors, stepK val x H φ d n t := by
  rw [gK, if_neg (by omega)]
  congr 1
  exact Finset.sum_attach n.properDivisors (fun d => stepK val x H φ d n t)

/-- The filters are measurable with values in `[0, 1]`. -/
def FilterOK (φ : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∀ d n, Measurable (φ d n) ∧ ∀ c, 0 ≤ φ d n c ∧ φ d n c ≤ 1

/-- The constant (nominal) filters `κ_{d→n}`. -/
def constF (κ : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ := fun d n _ => κ d n

lemma constF_ok {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) : FilterOK (constF κ) :=
  fun d n => ⟨measurable_const, fun _ => hκ d n⟩

variable {val x H}

lemma measurable_mul_comp {φ : ℝ → ℝ} (hφ : Measurable φ) {g : ℝ → ℝ} (hg : Measurable g)
    (w : ℝ) : Measurable fun v => φ (v / w) * g v :=
  (hφ.comp (measurable_id.div_const w)).mul hg

lemma integrable_mul_comp {φ : ℝ → ℝ} (hφ : Measurable φ) (hb : ∀ c, |φ c| ≤ 1) {g : ℝ → ℝ}
    (hg : Integrable g) (w : ℝ) : Integrable fun v => φ (v / w) * g v := by
  refine hg.bdd_mul (c := 1) (hφ.comp (measurable_id.div_const w)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]; exact hb _

/-- The densities are integrable and measurable. -/
theorem integrable_gK (hH : WidthReg H)
    {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ) :
    ∀ n, Integrable (gK val x H φ n) ∧ Measurable (gK val x H φ n) := by
  have hb : ∀ d n c, |φ d n c| ≤ 1 := fun d n c => by
    rw [abs_le]; constructor <;> linarith [(hφ d n).2 c]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [gK_le_one val x H (by omega)]; exact ⟨integrable_zero _ _ _, measurable_const⟩
  have hstep : ∀ d ∈ n.properDivisors, Integrable (stepK val x H φ d n) ∧
      Measurable (stepK val x H φ d n) := by
    intro d hd
    have hdl := (Nat.mem_properDivisors.mp hd).2
    by_cases h1 : d = 1
    · have e : stepK val x H φ d n = fun t => φ 1 n (posn val x n) * kd H (posn val x n) t := by
        funext t; unfold stepK; rw [if_pos h1]
      rw [e]
      exact ⟨(integrable_kd hH _).const_mul _, (measurable_kd_left hH _).const_mul _⟩
    · have e : stepK val x H φ d n = Qd H (LemmaM.valN val (n / d))
          (fun v => φ d n (v / LemmaM.valN val (n / d)) * gK val x H φ d v) := by
        funext t; unfold stepK; rw [if_neg h1]
      rw [e]
      obtain ⟨hi, hm⟩ := ih d hdl
      exact ⟨integrable_Qd hH _ (integrable_mul_comp (hφ d n).1 (hb d n) hi _)
          (measurable_mul_comp (hφ d n).1 hm _),
        measurable_Qd hH _ (measurable_mul_comp (hφ d n).1 hm _)⟩
  have e : gK val x H φ n = fun t => - ∑ d ∈ n.properDivisors, stepK val x H φ d n t :=
    funext (gK_eq val x H hn)
  rw [e]
  exact ⟨(integrable_finset_sum _ fun d hd => (hstep d hd).1).neg,
    (Finset.measurable_sum _ fun d hd => (hstep d hd).2).neg⟩

/-! ## The nominal kernels -/

lemma cdf_neg_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, Integrable (f i))
    (t : ℝ) : cdf (fun v => - ∑ i ∈ s, f i v) t = - ∑ i ∈ s, cdf (f i) t := by
  unfold cdf
  rw [integral_neg, integral_finset_sum _ fun i hi => (hf i hi).integrableOn]

lemma cdf_const_mul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    cdf (fun v => c * f v) t = c * cdf f t := by
  unfold cdf; rw [integral_const_mul]

/-- **The nominal kernels of Theorem 5.15 are absolutely continuous**: for constant filters
`κ`, `kerV n` is the distribution function of `gK κ n` (`n ≥ 2`). -/
theorem kerV_eq_cdf (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) :
    ∀ n, 2 ≤ n → kerV val x H κ n = cdf (gK val x H (constF κ) n) := by
  have hint := integrable_gK (x := x) (val := val) hH (constF_ok hκ)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  funext t
  have hn0 : n ≠ 0 := by omega
  have hsteps : ∀ d ∈ n.properDivisors, Integrable (stepK val x H (constF κ) d n) := by
    intro d hd
    by_cases h1 : d = 1
    · have e : stepK val x H (constF κ) d n = fun t => κ 1 n * kd H (posn val x n) t := by
        funext t; unfold stepK; rw [if_pos h1]; rfl
      rw [e]; exact (integrable_kd hH _).const_mul _
    · have e : stepK val x H (constF κ) d n = Qd H (LemmaM.valN val (n / d))
          (fun v => κ d n * gK val x H (constF κ) d v) := by
        funext t; unfold stepK; rw [if_neg h1]; rfl
      rw [e]
      exact integrable_Qd hH _ ((hint d).1.const_mul _) ((hint d).2.const_mul _)
  have e : gK val x H (constF κ) n = fun t => - ∑ d ∈ n.properDivisors,
      stepK val x H (constF κ) d n t := funext (gK_eq val x H hn)
  rw [kerV_eq val x H κ hn, e, cdf_neg_sum _ hsteps]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hdl := (Nat.mem_properDivisors.mp hd).2
  have hw := LemmaM.valN_pos val hval (n := n / d)
  by_cases h1 : d = 1
  · subst h1
    have e1 : stepK val x H (constF κ) 1 n = fun t => κ 1 n * kd H (posn val x n) t := by
      funext t; unfold stepK; rw [if_pos rfl]; rfl
    rw [e1, cdf_const_mul, kerV_one, Qv_stepF hH hw, ← cdf_kd_eq_Kv hH]
    congr 2
    unfold posn; rw [Nat.div_one]
  · have hd2 : 2 ≤ d := by
      have := one_le_of_mem_pd hd; omega
    have e1 : stepK val x H (constF κ) d n = Qd H (LemmaM.valN val (n / d))
        (fun v => κ d n * gK val x H (constF κ) d v) := by
      funext t; unfold stepK; rw [if_neg h1]; rfl
    have e2 : Qd H (LemmaM.valN val (n / d)) (fun v => κ d n * gK val x H (constF κ) d v) =
        fun t => κ d n * Qd H (LemmaM.valN val (n / d)) (gK val x H (constF κ) d) t := by
      funext t; unfold Qd; rw [← integral_const_mul]; congr 1; funext v; ring
    rw [e1, e2, cdf_const_mul, ih d hdl hd2, cdf_Qd hH hw (hint d).1 (hint d).2]

/-- `TV(C_n^nom) = ∫ |g_n| ≤ eVariationOn (kerV n)`. -/
theorem lintegral_gK_nom_le (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : WidthReg H)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ t, ‖gK val x H (constF κ) n t‖ₑ ≤ eVariationOn (kerV val x H κ n) univ := by
  rw [kerV_eq_cdf hval hH hκ n hn]
  exact lintegral_enorm_le_eVariationOn
    ((integrable_gK hH (constF_ok hκ)) n).1

/-! ## The Duhamel form -/

variable (val x H)

/-- `Ẽ_n = C_n - C_n^nom` (densities). -/
noncomputable def Etil (φ : ℕ → ℕ → ℝ → ℝ) (κ : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  gK val x H φ n t - gK val x H (constF κ) n t

/-- The source term of the step `d → n`: `(P_{d→n} - P^nom_{d→n}) C_d` (with the sign of the
recursion). -/
noncomputable def srcStep (φ : ℕ → ℕ → ℝ → ℝ) (κ : ℕ → ℕ → ℝ) (d n : ℕ) (t : ℝ) : ℝ :=
  if d = 1 then (φ 1 n (posn val x n) - κ 1 n) * kd H (posn val x n) t else
    Qd H (LemmaM.valN val (n / d)) (fun v => (φ d n (v / LemmaM.valN val (n / d)) - κ d n) *
      gK val x H φ d v) t

/-- `S_n = ∑_{d<n} (P_{d→n} - P^nom_{d→n}) C_d`. -/
noncomputable def Ssrc (φ : ℕ → ℕ → ℝ → ℝ) (κ : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  - ∑ d ∈ n.properDivisors, srcStep val x H φ κ d n t

/-- The nominal step operator on densities, `P^nom_{d→n} f = -κ_{d→n} Qd f`, and the chains:
`𝒯_{n'→n'} f = f`, `𝒯_{n'→n} f = ∑_{d<n} P^nom_{d→n} 𝒯_{n'→d} f` (`n > n'`), `0` otherwise. -/
noncomputable def Tch (κ : ℕ → ℕ → ℝ) (n' : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  if n = n' then f else if n' < n then fun t => - ∑ d ∈ n.properDivisors.attach,
    κ d.1 n * Qd H (LemmaM.valN val (n / d.1)) (Tch κ n' f d.1) t else fun _ => 0
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

variable {val x H}

lemma Tch_self (κ : ℕ → ℕ → ℝ) (n' : ℕ) (f : ℝ → ℝ) : Tch val H κ n' f n' = f := by
  rw [Tch, if_pos rfl]

lemma Tch_eq {κ : ℕ → ℕ → ℝ} {n' n : ℕ} (f : ℝ → ℝ) (hn : n' < n) (t : ℝ) :
    Tch val H κ n' f n t = - ∑ d ∈ n.properDivisors,
      κ d n * Qd H (LemmaM.valN val (n / d)) (Tch val H κ n' f d) t := by
  rw [Tch, if_neg (by omega), if_pos hn]
  congr 1
  exact Finset.sum_attach n.properDivisors
    (fun d => κ d n * Qd H (LemmaM.valN val (n / d)) (Tch val H κ n' f d) t)

lemma Tch_lt {κ : ℕ → ℕ → ℝ} {n' n : ℕ} (f : ℝ → ℝ) (hn : n < n') :
    Tch val H κ n' f n = fun _ => 0 := by
  rw [Tch, if_neg (by omega), if_neg (by omega)]

/-- The chains preserve integrability and measurability. -/
lemma integrable_Tch (hH : WidthReg H) (κ : ℕ → ℕ → ℝ) (n' : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f) (hfm : Measurable f) :
    ∀ n, Integrable (Tch val H κ n' f n) ∧ Measurable (Tch val H κ n' f n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases lt_trichotomy n n' with h | h | h
  · rw [Tch_lt f h]; exact ⟨integrable_zero _ _ _, measurable_const⟩
  · subst h; rw [Tch_self]; exact ⟨hf, hfm⟩
  · have e : Tch val H κ n' f n = fun t => - ∑ d ∈ n.properDivisors,
        κ d n * Qd H (LemmaM.valN val (n / d)) (Tch val H κ n' f d) t :=
      funext (Tch_eq f h)
    rw [e]
    refine ⟨(integrable_finset_sum _ fun d hd => ?_).neg,
      (Finset.measurable_sum _ fun d hd => ?_).neg⟩
    · obtain ⟨hi, hm⟩ := ih d (Nat.mem_properDivisors.mp hd).2
      exact (integrable_Qd hH _ hi hm).const_mul _
    · obtain ⟨-, hm⟩ := ih d (Nat.mem_properDivisors.mp hd).2
      exact (measurable_Qd hH _ hm).const_mul _

lemma Qd_add (hH : WidthReg H) (w : ℝ) {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (t : ℝ) : Qd H w (fun v => f v + g v) t = Qd H w f t + Qd H w g t := by
  unfold Qd
  have hk : ∀ {f : ℝ → ℝ}, Integrable f → Integrable fun v => f v * kd H (v / w) t := by
    intro f hf
    refine hf.mul_bdd (c := 3 / 2 * (H t)⁻¹)
      (((measurable_kd hH).comp ((measurable_id.div_const w).prodMk
        measurable_const)).aestronglyMeasurable) (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (kd_nonneg hH _ _)]
    exact kd_le_window hH _ _
  rw [← integral_add (hk hf) (hk hg)]
  congr 1; funext v; ring

lemma Qd_const_mul (c : ℝ) (w : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    Qd H w (fun v => c * f v) t = c * Qd H w f t := by
  unfold Qd; rw [← integral_const_mul]; congr 1; funext v; ring

lemma Tch_not_dvd {κ : ℕ → ℕ → ℝ} {n' : ℕ} (f : ℝ → ℝ) :
    ∀ n, ¬ n' ∣ n → Tch val H κ n' f n = fun _ => 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnd
  rcases lt_trichotomy n n' with h | h | h
  · exact Tch_lt f h
  · subst h; exact absurd (dvd_refl _) hnd
  · funext t
    rw [Tch_eq f h]
    rw [Finset.sum_eq_zero fun d hd => ?_, neg_zero]
    have hdn := (Nat.mem_properDivisors.mp hd).1
    rw [ih d (Nat.mem_properDivisors.mp hd).2 (fun h' => hnd (h'.trans hdn))]
    unfold Qd; simp

lemma stepK_sub (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) (d n : ℕ) (t : ℝ) :
    stepK val x H φ d n t - stepK val x H (constF κ) d n t =
      srcStep val x H φ κ d n t + (if d = 1 then 0 else
        κ d n * Qd H (LemmaM.valN val (n / d)) (Etil val x H φ κ d) t) := by
  have hb : ∀ d n c, |φ d n c| ≤ 1 := fun d n c => by
    rw [abs_le]; constructor <;> linarith [(hφ d n).2 c]
  unfold stepK srcStep
  by_cases h1 : d = 1
  · simp only [if_pos h1, constF]; ring
  · simp only [if_neg h1, constF]
    set w := LemmaM.valN val (n / d)
    obtain ⟨hi, hm⟩ := integrable_gK (val := val) (x := x) hH hφ d
    obtain ⟨hi', hm'⟩ := integrable_gK (val := val) (x := x) hH (constF_ok hκ) d
    have hA : Integrable fun v => (φ d n (v / w) - κ d n) * gK val x H φ d v := by
      have hb' : ∀ c, |φ d n c - κ d n| ≤ 1 := fun c => by
        rw [abs_le]; constructor <;> linarith [(hφ d n).2 c, hκ d n]
      exact integrable_mul_comp (φ := fun c => φ d n c - κ d n) (((hφ d n).1).sub measurable_const)
        hb' hi w
    have hE : Integrable (Etil val x H φ κ d) := hi.sub hi'
    have e : (fun v => φ d n (v / w) * gK val x H φ d v) = fun v =>
        ((φ d n (v / w) - κ d n) * gK val x H φ d v + κ d n * Etil val x H φ κ d v) +
          κ d n * gK val x H (constF κ) d v := by
      funext v; unfold Etil; ring
    have h1 := Qd_add hH w
      (f := fun v => (φ d n (v / w) - κ d n) * gK val x H φ d v + κ d n * Etil val x H φ κ d v)
      (g := fun v => κ d n * gK val x H (constF κ) d v) (hA.add (hE.const_mul _))
      (hi'.const_mul _) t
    have h2 := Qd_add hH w (f := fun v => (φ d n (v / w) - κ d n) * gK val x H φ d v)
      (g := fun v => κ d n * Etil val x H φ κ d v) hA (hE.const_mul _) t
    have h3 := Qd_const_mul (H := H) (κ d n) w (Etil val x H φ κ d) t
    beta_reduce at h1 h2
    rw [e, h1, h2, h3]
    ring

/-- **The Duhamel recursion**: `Ẽ_n = S_n + ∑_{d<n} P^nom_{d→n} Ẽ_d` (`n ≥ 2`). -/
theorem Etil_eq (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    Etil val x H φ κ n t = Ssrc val x H φ κ n t + - ∑ d ∈ n.properDivisors,
      (if d = 1 then 0 else κ d n * Qd H (LemmaM.valN val (n / d)) (Etil val x H φ κ d) t) := by
  unfold Etil Ssrc
  rw [gK_eq val x H hn, gK_eq val x H hn, ← neg_add, ← Finset.sum_add_distrib]
  rw [show -∑ d ∈ n.properDivisors, stepK val x H φ d n t -
      -∑ d ∈ n.properDivisors, stepK val x H (constF κ) d n t =
      -∑ d ∈ n.properDivisors, (stepK val x H φ d n t - stepK val x H (constF κ) d n t) by
    rw [Finset.sum_sub_distrib]; ring]
  congr 1
  exact Finset.sum_congr rfl fun d _ => stepK_sub hH hφ hκ d n t

lemma integrable_Ssrc (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) (n : ℕ) :
    Integrable (Ssrc val x H φ κ n) ∧ Measurable (Ssrc val x H φ κ n) := by
  have hst : ∀ d, Integrable (srcStep val x H φ κ d n) ∧ Measurable (srcStep val x H φ κ d n) := by
    intro d
    by_cases h1 : d = 1
    · have e : srcStep val x H φ κ d n = fun t =>
          (φ 1 n (posn val x n) - κ 1 n) * kd H (posn val x n) t := by
        funext t; unfold srcStep; rw [if_pos h1]
      rw [e]; exact ⟨(integrable_kd hH _).const_mul _, (measurable_kd_left hH _).const_mul _⟩
    · have e : srcStep val x H φ κ d n = Qd H (LemmaM.valN val (n / d))
          (fun v => (φ d n (v / LemmaM.valN val (n / d)) - κ d n) * gK val x H φ d v) := by
        funext t; unfold srcStep; rw [if_neg h1]
      rw [e]
      obtain ⟨hi, hm⟩ := integrable_gK (val := val) (x := x) hH hφ d
      have hb' : ∀ c, |φ d n c - κ d n| ≤ 1 := fun c => by
        rw [abs_le]; constructor <;> linarith [(hφ d n).2 c, hκ d n]
      have hm2 := measurable_mul_comp (φ := fun c => φ d n c - κ d n)
        (((hφ d n).1).sub measurable_const) hm (LemmaM.valN val (n / d))
      exact ⟨integrable_Qd hH _ (integrable_mul_comp (φ := fun c => φ d n c - κ d n)
        (((hφ d n).1).sub measurable_const) hb' hi _) hm2, measurable_Qd hH _ hm2⟩
  have e : Ssrc val x H φ κ n = fun t => - ∑ d ∈ n.properDivisors, srcStep val x H φ κ d n t :=
    rfl
  rw [e]
  exact ⟨(integrable_finset_sum _ fun d _ => (hst d).1).neg,
    (Finset.measurable_sum _ fun d _ => (hst d).2).neg⟩

/-- **The Duhamel form, unrolled**: `Ẽ_n = ∑_{n' ∣ n, n' ≥ 2} 𝒯^nom_{n'→n} S_{n'}`. -/
theorem Etil_eq_chain (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {κ : ℕ → ℕ → ℝ} (hκ : ∀ d n, 0 ≤ κ d n ∧ κ d n ≤ 1) :
    ∀ n, 2 ≤ n → Etil val x H φ κ n = fun t => ∑ n' ∈ n.divisors.filter (2 ≤ ·),
      Tch val H κ n' (Ssrc val x H φ κ n') n t := by
  have hS := integrable_Ssrc (val := val) (x := x) hH hφ hκ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  funext t
  have hn0 : n ≠ 0 := by omega
  -- split off `n' = n`
  have hsplit : n.divisors.filter (2 ≤ ·) =
      insert n (n.properDivisors.filter (2 ≤ ·)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hm, -⟩, h2⟩
      rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hm) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨hm, h⟩, h2⟩
    · rintro (rfl | ⟨⟨hm, -⟩, h2⟩)
      · exact ⟨⟨dvd_refl _, hn0⟩, hn⟩
      · exact ⟨⟨hm, hn0⟩, h2⟩
  have hnot : n ∉ n.properDivisors.filter (2 ≤ ·) := by simp
  rw [hsplit, Finset.sum_insert hnot, Tch_self, Etil_eq hH hφ hκ hn]
  congr 1
  -- the chain terms
  have hT : ∀ n' ∈ n.properDivisors.filter (2 ≤ ·),
      Tch val H κ n' (Ssrc val x H φ κ n') n t = - ∑ d ∈ n.properDivisors,
        κ d n * Qd H (LemmaM.valN val (n / d)) (Tch val H κ n' (Ssrc val x H φ κ n') d) t := by
    intro n' hn'
    exact Tch_eq _ (Nat.mem_properDivisors.mp (Finset.mem_filter.mp hn').1).2 t
  rw [Finset.sum_congr rfl hT, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hdl := (Nat.mem_properDivisors.mp hd).2
  by_cases h1 : d = 1
  · subst h1
    rw [if_pos rfl]
    symm
    refine Finset.sum_eq_zero fun n' hn' => ?_
    have h2 := (Finset.mem_filter.mp hn').2
    rw [Tch_lt _ (by omega)]
    unfold Qd; simp
  · rw [if_neg h1]
    have hd2 : 2 ≤ d := by have := one_le_of_mem_pd hd; omega
    rw [ih d hdl hd2, ← Finset.mul_sum]
    congr 1
    -- `Qd` of the sum over `n' ∣ d` is the sum over `n' ∣ n`, `n' < n` (the others vanish)
    have hint : ∀ n' ∈ d.divisors.filter (2 ≤ ·),
        Integrable (Tch val H κ n' (Ssrc val x H φ κ n') d) :=
      fun n' _ => (integrable_Tch hH κ n' (hS n').1 (hS n').2 d).1
    have hQsum : Qd H (LemmaM.valN val (n / d)) (fun t => ∑ n' ∈ d.divisors.filter (2 ≤ ·),
        Tch val H κ n' (Ssrc val x H φ κ n') d t) t =
        ∑ n' ∈ d.divisors.filter (2 ≤ ·),
          Qd H (LemmaM.valN val (n / d)) (Tch val H κ n' (Ssrc val x H φ κ n') d) t := by
      unfold Qd
      rw [← integral_finset_sum]
      · congr 1; funext v; rw [Finset.sum_mul]
      · intro n' hn'
        refine (hint n' hn').mul_bdd (c := 3 / 2 * (H t)⁻¹)
          (((measurable_kd hH).comp ((measurable_id.div_const _).prodMk
            measurable_const)).aestronglyMeasurable) (Filter.Eventually.of_forall fun v => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (kd_nonneg hH _ _)]
        exact kd_le_window hH _ _
    rw [hQsum]
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_properDivisors] at hm ⊢
      obtain ⟨⟨hmd, hd0⟩, h2⟩ := hm
      exact ⟨⟨hmd.trans hdn, lt_of_le_of_lt (Nat.le_of_dvd (by omega) hmd) hdl⟩, h2⟩
    · intro m hm hm'
      have hnd : ¬ m ∣ d := by
        intro hmd
        apply hm'
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hmd, by omega⟩, (Finset.mem_filter.mp hm).2⟩
      rw [Tch_not_dvd _ d hnd]
      unfold Qd; simp

/-- **(K5)** for the source: `∫ |S_n| ≤ ∑_{d<n} ∫ |φ_{d→n}(v/w) - κ_{d→n}| |dC_d(v)|` (for
`d = 1`, `C_1 = δ_x` and the centre is `x/n`). -/
theorem lintegral_Ssrc_le (hH : WidthReg H) {φ : ℕ → ℕ → ℝ → ℝ} (hφ : FilterOK φ)
    {κ : ℕ → ℕ → ℝ} (n : ℕ) :
    ∫⁻ t, ‖Ssrc val x H φ κ n t‖ₑ ≤ ∑ d ∈ n.properDivisors,
      (if d = 1 then ‖φ 1 n (posn val x n) - κ 1 n‖ₑ else
        ∫⁻ v, ‖(φ d n (v / LemmaM.valN val (n / d)) - κ d n) * gK val x H φ d v‖ₑ) := by
  have hmst : ∀ d, Measurable (srcStep val x H φ κ d n) := by
    intro d
    by_cases h1 : d = 1
    · have e : srcStep val x H φ κ d n = fun t =>
          (φ 1 n (posn val x n) - κ 1 n) * kd H (posn val x n) t := by
        funext t; unfold srcStep; rw [if_pos h1]
      rw [e]; exact (measurable_kd_left hH _).const_mul _
    · have e : srcStep val x H φ κ d n = Qd H (LemmaM.valN val (n / d))
          (fun v => (φ d n (v / LemmaM.valN val (n / d)) - κ d n) * gK val x H φ d v) := by
        funext t; unfold srcStep; rw [if_neg h1]
      rw [e]
      exact measurable_Qd hH _ (measurable_mul_comp (φ := fun c => φ d n c - κ d n)
        (((hφ d n).1).sub measurable_const) (integrable_gK (val := val) (x := x) hH hφ d).2 _)
  calc ∫⁻ t, ‖Ssrc val x H φ κ n t‖ₑ
      ≤ ∫⁻ t, ∑ d ∈ n.properDivisors, ‖srcStep val x H φ κ d n t‖ₑ := by
        refine lintegral_mono fun t => ?_
        unfold Ssrc; rw [enorm_neg]; exact enorm_sum_le _ _
    _ = ∑ d ∈ n.properDivisors, ∫⁻ t, ‖srcStep val x H φ κ d n t‖ₑ :=
        lintegral_finset_sum _ fun d _ => (hmst d).enorm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun d _ => ?_
        by_cases h1 : d = 1
        · rw [if_pos h1]
          have e : srcStep val x H φ κ d n = fun t =>
              (φ 1 n (posn val x n) - κ 1 n) * kd H (posn val x n) t := by
            funext t; unfold srcStep; rw [if_pos h1]
          rw [e]
          simp_rw [enorm_mul]
          rw [lintegral_const_mul _ (measurable_kd_left hH _).enorm, lintegral_kd hH, mul_one]
        · rw [if_neg h1]
          have e : srcStep val x H φ κ d n = Qd H (LemmaM.valN val (n / d))
              (fun v => (φ d n (v / LemmaM.valN val (n / d)) - κ d n) * gK val x H φ d v) := by
            funext t; unfold srcStep; rw [if_neg h1]
          rw [e]
          exact lintegral_Qd_le hH _ (measurable_mul_comp (φ := fun c => φ d n c - κ d n)
            (((hφ d n).1).sub measurable_const) (integrable_gK (val := val) (x := x) hH hφ d).2 _)

end KR

end
