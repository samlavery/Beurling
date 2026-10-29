module

public import RequestProject.Beurling.Noise.KRTrue
public import RequestProject.Beurling.Noise.KRVarWidth

/-!
# Lemma 5.12 (structure of the near-threshold steps) and the support of the true kernels

For a step `d → n` with cofactor `w = n/d` (value `V(n/d)`), the true filter at a centre `c` is
`φ_{d→n}(c) = 1[τ_w < c] 1[c ≥ X₀⁻]` (`trueFilter`), with `τ_w = max_{p ∣ w} t(p)` (`tauW`);
the nominal filter is its value at the nominal landing point `x/n`
(`nomFilter_eq_trueFilter`). Definition 5.11's notions:

* the step is `τ`-near if `|τ_w - x/n| ≤ 2H_n` (`TauNear`), `X₀`-near if
  `|x/n - X₀⁻| ≤ R_d/w` with `R_d = 1.02 H(x/d)` (`X0Near`); the level `n` is terminal if
  `x/n < X₀⁻ + 0.6 H(X₀)` (`Terminal`).

**Lemma 5.12**, with the paper's hypotheses on `H` (`PaperWidth`), `X₀⁻ = X₀ - H(X₀)/2`:

* (i) `near_i` : on a step that is neither `τ`-near nor `X₀`-near, the true filter equals the
  nominal one at every centre `v/w` with `|v - x/d| ≤ R_d`;
* (ii) `near_ii` : `R_d/w ≤ 0.52 H(X₀)` on every `X₀`-near step, which lands at a terminal level;
* (iii) `near_iii` : a terminal level has no children in either family: every child centre
  `v/w'` (`|v - x/n| ≤ 1.02 H_n`, `w' ≥ 2`) and every nominal child point `x/(nw')` lie below
  `X₀⁻`.

`gK_support` : the true kernels live where Theorem 5.15's do: `C_n` vanishes off
`[x/n ± 1.02 H(x/n)]`, and `x/n ≥ X₀⁻/2` wherever `C_n ≠ 0` (§5.9.1, `R_n ≤ 1.02 H(x/n)`).

(The paper also uses `H(X₀)/X₀ < 10⁻¹⁰` here; the Lipschitz bound in `PaperWidth` suffices.)
-/

@[expose] public section

open Finset MeasureTheory Set

namespace KR

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ}

/-- `τ_w = max_{p ∣ w} t(p)` (`τ_1 = 0`). -/
noncomputable def tauW (tw : ℕ → ℝ) (m : ℕ) : ℝ :=
  if h : m.primeFactors.Nonempty then m.primeFactors.sup' h tw else 0

/-- The true filter of the step `d → n` at the centre `c`: `1[τ_w < c] 1[c ≥ X₀⁻]`. -/
noncomputable def trueFilter (tw : ℕ → ℝ) (X0m : ℝ) (d n : ℕ) (c : ℝ) : ℝ :=
  open scoped Classical in
  if (∀ p ∈ (n / d).primeFactors, tw p < c) ∧ X0m ≤ c then 1 else 0

lemma trueFilter_ok (tw : ℕ → ℝ) (X0m : ℝ) : FilterOK (trueFilter tw X0m) := by
  intro d n
  refine ⟨?_, fun c => ?_⟩
  · classical
    unfold trueFilter
    refine Measurable.ite ?_ measurable_const measurable_const
    refine MeasurableSet.inter ?_ measurableSet_Ici
    have : {c : ℝ | ∀ p ∈ (n / d).primeFactors, tw p < c} =
        ⋂ p ∈ (n / d).primeFactors, Ioi (tw p) := by ext c; simp
    change MeasurableSet {c : ℝ | ∀ p ∈ (n / d).primeFactors, tw p < c}
    rw [this]
    exact Finset.measurableSet_biInter _ fun p _ => measurableSet_Ioi
  · unfold trueFilter; split_ifs <;> norm_num

lemma trueFilter_ne_zero {tw : ℕ → ℝ} {X0m : ℝ} {d n : ℕ} {c : ℝ}
    (h : trueFilter tw X0m d n c ≠ 0) : X0m ≤ c := by
  unfold trueFilter at h; split_ifs at h with hc
  · exact hc.2
  · exact absurd rfl h

/-- The nominal filter is the true filter at the nominal landing point `x/n`. -/
lemma nomFilter_eq_trueFilter (hval : ∀ p, p.Prime → 1 ≤ val p) (tw : ℕ → ℝ) (X0m : ℝ)
    (d n : ℕ) : nomFilter val x tw X0m d n = trueFilter tw X0m d n (posn val x n) := by
  classical
  have hV := LemmaM.valN_pos val hval (n := n)
  unfold nomFilter trueFilter LemmaM.filt posn
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => by rw [lt_div_iff₀ hV]; exact h1 p hp, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => by have := h1 p hp; rwa [lt_div_iff₀ hV] at this, h2⟩

lemma forall_lt_iff_tauW {tw : ℕ → ℝ} {m : ℕ} (hm : m.primeFactors.Nonempty) (c : ℝ) :
    (∀ p ∈ m.primeFactors, tw p < c) ↔ tauW tw m < c := by
  unfold tauW
  rw [dif_pos hm, Finset.sup'_lt_iff]

/-- The step `d → n` is `τ`-near: `|τ_w - x/n| ≤ 2 H(x/n)`. -/
def TauNear (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (tw : ℕ → ℝ) (d n : ℕ) : Prop :=
  |tauW tw (n / d) - posn val x n| ≤ 2 * H (posn val x n)

/-- The step `d → n` is `X₀`-near: `|x/n - X₀⁻| ≤ R_d/w`, `R_d = 1.02 H(x/d)`. -/
def X0Near (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (X0m : ℝ) (d n : ℕ) : Prop :=
  |posn val x n - X0m| ≤ 1.02 * H (posn val x d) / LemmaM.valN val (n / d)

/-- The level `n` is terminal: `x/n < X₀⁻ + 0.6 H(X₀)`. -/
def Terminal (val : ℕ → ℝ) (x : ℝ) (H : ℝ → ℝ) (X0m X0 : ℝ) (n : ℕ) : Prop :=
  posn val x n < X0m + 0.6 * H X0

lemma primeFactors_nonempty_of_mem {d n : ℕ} (hd : d ∈ n.properDivisors) :
    (n / d).primeFactors.Nonempty :=
  Nat.nonempty_primeFactors.mpr (by have := two_le_div_of_mem hd; omega)

/-- `R_d/w ≤ 0.5106 H_n` (for `x/n ≥ X₀⁻/2`). -/
lemma radius_step {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {d n : ℕ} (hd : d ∈ n.properDivisors)
    (hpos : X0m / 2 ≤ posn val x n) :
    1.02 * H (posn val x d) / LemmaM.valN val (n / d) ≤ 0.5106 * H (posn val x n) := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  rw [posn_mul hval hdn hn0]
  have hst := hP.step_le (v := posn val x n) hpos hw
  have hHn := hP.reg.pos (posn val x n)
  rw [mul_div_assoc]; nlinarith

/-- **Lemma 5.12(i)**: on a step that is neither `τ`-near nor `X₀`-near (with `x/n ≥ X₀⁻/2`),
`1[τ_w < v/w] 1[v/w ≥ X₀⁻] = κ_{d→n}` for every `v` with `|v - x/d| ≤ R_d`. -/
theorem near_i {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ val p)
    {tw : ℕ → ℝ} {d n : ℕ} (hd : d ∈ n.properDivisors) (hpos : X0m / 2 ≤ posn val x n)
    (hτ : ¬ TauNear val x H tw d n) (hX : ¬ X0Near val x H X0m d n) {v : ℝ}
    (hv : |v - posn val x d| ≤ 1.02 * H (posn val x d)) :
    trueFilter tw X0m d n (v / LemmaM.valN val (n / d)) = nomFilter val x tw X0m d n := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  rw [nomFilter_eq_trueFilter hval]
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
  set w := LemmaM.valN val (n / d)
  set p := posn val x n
  have hR := radius_step hP hval2 hd hpos
  have hc : |v / w - p| ≤ 1.02 * H (posn val x d) / w := by
    have e : v / w - p = (v - posn val x d) / w := by
      rw [posn_mul hval hdn hn0]; field_simp; simp only [w, p]; ring
    rw [e, abs_div, abs_of_pos hw0]
    exact div_le_div_of_nonneg_right hv hw0.le
  have hHp := hP.reg.pos p
  unfold TauNear at hτ
  unfold X0Near at hX
  push_neg at hτ hX
  have hne := primeFactors_nonempty_of_mem hd
  unfold trueFilter
  simp only [forall_lt_iff_tauW hne]
  have h1 : (tauW tw (n / d) < v / w) ↔ (tauW tw (n / d) < p) := by
    rcases lt_or_gt_of_ne (show tauW tw (n / d) ≠ p by
      intro h; rw [h, sub_self, abs_zero] at hτ; linarith) with h | h
    · rw [abs_of_neg (by linarith)] at hτ
      constructor <;> intro _ <;> linarith [(abs_le.mp hc).1, h]
    · rw [abs_of_pos (by linarith)] at hτ
      constructor <;> intro h' <;> linarith [(abs_le.mp hc).2]
  have h2 : (X0m ≤ v / w) ↔ (X0m ≤ p) := by
    rcases le_or_gt X0m p with h | h
    · rw [abs_of_nonneg (by linarith)] at hX
      constructor <;> intro _ <;> linarith [(abs_le.mp hc).1]
    · rw [abs_of_neg (by linarith)] at hX
      constructor <;> intro h' <;> linarith [(abs_le.mp hc).2]
  simp only [h1, h2]

/-- **Lemma 5.12(ii)**: on an `X₀`-near step (with `x/n ≥ X₀⁻/2`), `R_d/w ≤ 0.52 H(X₀)` and the
level `n` is terminal. Here `X₀⁻ = X₀ - H(X₀)/2`. -/
theorem near_ii {X0m X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {d n : ℕ} (hd : d ∈ n.properDivisors)
    (hpos : X0m / 2 ≤ posn val x n) (hX : X0Near val x H X0m d n) :
    1.02 * H (posn val x d) / LemmaM.valN val (n / d) ≤ 0.52 * H X0 ∧
      Terminal val x H X0m X0 n := by
  have hR := radius_step hP hval2 hd hpos
  set p := posn val x n
  have hHp := hP.reg.pos p
  have hHX := hP.reg.pos X0
  have hXm := hP.X0m_pos
  have hX0ge : X0m / 2 ≤ X0 := by linarith
  unfold X0Near at hX
  have hnear := hX.trans hR
  have hpX : |p - X0| ≤ 0.5 * H X0 + 0.5106 * H p := by
    rw [abs_le] at hnear ⊢; constructor <;> linarith [hnear.1, hnear.2]
  have hlip := hP.lip p X0 hpos hX0ge
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hHle : H p ≤ 1.0102 * H X0 := by
    have h1 : H p ≤ H X0 + θ * (0.5 * H X0 + 0.5106 * H p) := by
      have := (abs_le.mp hlip).2
      nlinarith [mul_le_mul_of_nonneg_left hpX hθ0]
    nlinarith
  refine ⟨by linarith, ?_⟩
  unfold Terminal
  have := (abs_le.mp hnear).2
  linarith

/-- **Lemma 5.12(iii)**: at a terminal level `n` (with `x/n ≥ X₀⁻/2`), every child centre
`v/w'` with `|v - x/n| ≤ 1.02 H_n`, `w' ≥ 2`, and every nominal child point `(x/n)/w'`, lie
below `X₀⁻`; so both the true and the nominal filters of all children vanish. -/
theorem near_iii {X0m X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    {n : ℕ} (hpos : X0m / 2 ≤ posn val x n) (hT : Terminal val x H X0m X0 n) {v w' : ℝ}
    (hw' : 2 ≤ w') (hv : |v - posn val x n| ≤ 1.02 * H (posn val x n)) :
    v / w' < X0m ∧ posn val x n / w' < X0m := by
  set p := posn val x n
  have hXm := hP.X0m_pos
  have hsm := hP.small p hpos
  have hHX : H X0 ≤ X0 / 10 := hP.small X0 (by linarith [hP.reg.pos X0])
  have hX0le : X0 ≤ 1.06 * X0m := by linarith
  unfold Terminal at hT
  have hp : p < X0m + 0.6 * (0.106 * X0m) := by nlinarith
  have hw0 : 0 < w' := by linarith
  have hvle : v ≤ 1.102 * p := by linarith [(abs_le.mp hv).2]
  have hp0 : 0 ≤ p := by linarith
  constructor
  · rw [div_lt_iff₀ hw0]; nlinarith
  · rw [div_lt_iff₀ hw0]; nlinarith

/-! ## The support of the true kernels -/

/-- **Support**: if the filters vanish at centres below `X₀⁻`, then
`C_n ≠ 0` at `t` forces `x/n ≥ X₀⁻/2` and `|t - x/n| ≤ 1.02 H(x/n)`. -/
theorem gK_support {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {φ : ℕ → ℕ → ℝ → ℝ}
    (hφX : ∀ d n c, φ d n c ≠ 0 → X0m ≤ c) :
    ∀ n, ∀ t, gK val x H φ n t ≠ 0 →
      X0m / 2 ≤ posn val x n ∧ |t - posn val x n| ≤ 1.02 * H (posn val x n) := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  have hXm := hP.X0m_pos
  have hH := hP.reg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ht
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [gK_le_one val x H (by omega)] at ht; exact absurd rfl ht
  have hn0 : n ≠ 0 := by omega
  rw [gK_eq val x H hn] at ht
  obtain ⟨d, hd, hdt⟩ : ∃ d ∈ n.properDivisors, stepK val x H φ d n t ≠ 0 := by
    by_contra hc; push_neg at hc
    exact ht (by rw [Finset.sum_eq_zero hc, neg_zero])
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hdl := (Nat.mem_properDivisors.mp hd).2
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
  set w := LemmaM.valN val (n / d)
  set p := posn val x n
  by_cases h1 : d = 1
  · subst h1
    unfold stepK at hdt
    rw [if_pos rfl] at hdt
    have hφ0 : φ 1 n p ≠ 0 := fun h => hdt (by rw [h, zero_mul])
    have hk : kd H p t ≠ 0 := fun h => hdt (by rw [h, mul_zero])
    have hpX := hφX 1 n p hφ0
    refine ⟨by linarith, ?_⟩
    unfold kd Set.indicator at hk
    split_ifs at hk with hm
    · have hHp := hH.pos p
      rw [abs_le]; constructor <;> linarith [hm.1, hm.2]
    · simp at hk
  · unfold stepK at hdt
    rw [if_neg h1] at hdt
    unfold Qd at hdt
    obtain ⟨v, hv⟩ : ∃ v, φ d n (v / w) * gK val x H φ d v * kd H (v / w) t ≠ 0 := by
      by_contra hc; push_neg at hc
      have hz : (fun v => φ d n (v / w) * gK val x H φ d v * kd H (v / w) t) = fun _ => 0 :=
        funext hc
      beta_reduce at hdt
      simp only [w] at hz
      exact hdt (by rw [hz]; simp)
    have hφv : φ d n (v / w) ≠ 0 := fun h => hv (by rw [h]; ring)
    have hgv : gK val x H φ d v ≠ 0 := fun h => hv (by rw [h]; ring)
    have hkv : kd H (v / w) t ≠ 0 := fun h => hv (by rw [h]; ring)
    obtain ⟨hposd, hvd⟩ := ih d hdl v hgv
    have hcX := hφX d n (v / w) hφv
    have hpd : posn val x d = p * w := posn_mul hval hdn hn0
    have hsmd := hP.small (posn val x d) hposd
    -- `x/n ≥ X₀⁻/2`
    have hc : |v / w - p| ≤ 1.02 * H (posn val x d) / w := by
      have e : v / w - p = (v - posn val x d) / w := by rw [hpd]; field_simp
      rw [e, abs_div, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right hvd hw0.le
    have hpos : X0m / 2 ≤ p := by
      have h3 : 1.02 * H (posn val x d) / w ≤ 0.102 * p := by
        rw [div_le_iff₀ hw0, hpd]; rw [hpd] at hsmd; nlinarith
      linarith [(abs_le.mp hc).2]
    refine ⟨hpos, ?_⟩
    have hR := radius_step hP hval2 hd hpos
    have hwin : |t - v / w| ≤ H (v / w) / 2 := by
      unfold kd Set.indicator at hkv
      split_ifs at hkv with hm
      · rw [abs_le]; constructor <;> linarith [hm.1, hm.2]
      · simp at hkv
    have hy : |v / w - p| ≤ 0.5106 * H p := hc.trans hR
    have hlip := hP.lip (v / w) p (by linarith) hpos
    have hθ := hP.theta_le
    have hθ0 := hP.theta_nonneg
    have hHp := hH.pos p
    have hHv : H (v / w) ≤ H p + θ * (0.5106 * H p) := by
      have := (abs_le.mp hlip).2
      nlinarith [mul_le_mul_of_nonneg_left hy hθ0]
    have htri : |t - p| ≤ |t - v / w| + |v / w - p| := abs_sub_le _ _ _
    nlinarith

end KR

end
