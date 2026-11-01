module

public import RequestProject.Beurling.Noise.RML12M
public import RequestProject.Beurling.Noise.RML13Kap
public import RequestProject.Beurling.Noise.RML7GPt
public import RequestProject.Beurling.Queue6.WinS4

/-!
# Proposition 5.38, Step 4: the grouping of the Step 3 errors into scales

With `m*(z) ≤ Mf z := 3.1 log(max z 1) + 4.2` (04g-margin.tex, Step 2, "Strips"), the Step 3
weight is bounded by Queue6's per-scale noise: `fE12 z ≤ 2ν(u_{m₁(z)}) + δ(u_{m₁(z)})`
(`fE12_le_gS`, from `Queue6.fE_le_nuQ`; also below `X₀`). On the strip of a point `s` of the
dyadic block `[v, 2v)` (`v = X₀⁻ 2^j/2`) the block index `m₁(z)` takes at most the three
values `k₀(v), k₀(v)+1, k₀(v)+2` (`m1z_mem`), so

  `e(t, w) ≤ 2ν'(v) + δ'(v)`,  `ν'(v) = ∑_{i=k₀(v)}^{k₀(v)+2} ν(u_i)`, `δ' ` likewise.

The cofactors that pass the filter are counted by `ω_t(v)` (`KR.RML7G.abs_Kpt_le`):

* `hS_kap` : `∑_{w ∈ F} κ_w(t) e(t, w)/w ≤ ∑_j ω_t(v_j) (2ν'(v_j) + δ'(v_j))`.

The filter `κ_w(t)` is essential: without it the sum is not controlled by `ω`
(see `RML13Kap.lean`).
-/

@[expose] public section

open Finset Real Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML13

variable {θ : ℝ} {X₀ : ℕ}

/-- The paper's bound for `m*`: `3.1 log(max z 1) + 4.2` (`= 3.1 log z + 4.2` for `z ≥ 1`). -/
noncomputable def MfP (z : ℝ) : ℝ := 3.1 * Real.log (max z 1) + 4.2

lemma MfP_nonneg (z : ℝ) : 0 ≤ MfP z := by
  unfold MfP
  have := Real.log_nonneg (le_max_right z 1)
  linarith

lemma MfP_mono : Monotone (MfP) := by
  intro x y hxy
  unfold MfP
  have := Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right x 1)) (max_le_max hxy le_rfl)
  linarith

variable (X₀) in
/-- The per-scale weight `g(m) = 2ν(u_m) + δ(u_m)`. -/
noncomputable def gS (m : ℕ) : ℝ := 2 * nuQ X₀ (uS X₀ m) + dQ X₀ (uS X₀ m)

variable (X₀) in
/-- The lower end `max(0.848 v, X₀)` of the block arguments on the strips of `[v, 2v)`. -/
noncomputable def loB (v : ℝ) : ℝ := max (0.848 * v) X₀

variable (X₀) in
/-- The first block index `k₀(v)` met by the strips of `[v, 2v)`. -/
noncomputable def k0 (v : ℝ) : ℕ := mB X₀ (loB X₀ v)

variable (X₀) in
/-- `ν'(v) = ∑_{i=k₀(v)}^{k₀(v)+2} ν(u_i)`. -/
noncomputable def nu13 (v : ℝ) : ℝ := ∑ i ∈ Icc (k0 X₀ v) (k0 X₀ v + 2), nuQ X₀ (uS X₀ i)

variable (X₀) in
/-- `δ'(v) = ∑_{i=k₀(v)}^{k₀(v)+2} δ(u_i)`. -/
noncomputable def dl13 (v : ℝ) : ℝ := ∑ i ∈ Icc (k0 X₀ v) (k0 X₀ v + 2), dQ X₀ (uS X₀ i)

variable (X₀) in
/-- The Step 3 weight as a function of the point `s = t/w`: `sup_{z ∈ strip(s)} fE12(z)`. -/
noncomputable def Fe (Mf : ℝ → ℝ) (s : ℝ) : ℝ := sSup (RML12M.fE12 X₀ Mf '' RML10.strip X₀ s)

variable (X₀) in
/-- The dyadic scales `v_j = X₀⁻ 2^j/2`. -/
noncomputable def bS (j : ℕ) : ℝ := Xm X₀ / 2 * 2 ^ j

/-! ## Blocks -/

section Blocks

variable (hc : Cond θ X₀)
include hc

lemma X0_pos : (0 : ℝ) < X₀ := by
  have := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith

lemma Xm_bounds : 0.99 * (X₀ : ℝ) ≤ Xm X₀ ∧ Xm X₀ ≤ X₀ := by
  have hX0 := X0_pos hc
  have h1 : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
  have h0 := capH_nonneg (X₀ : ℝ) (X₀ : ℝ)
  unfold Xm
  constructor <;> linarith

omit hc in
lemma uS_mono {a b : ℕ} (h : a ≤ b) : uS X₀ a ≤ uS X₀ b := by
  unfold uS
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (Nat.cast_nonneg _)

omit hc in
lemma uS_add (m k : ℕ) : uS X₀ (m + k) = 2 ^ k * uS X₀ m := by
  unfold uS; rw [pow_add]; ring

lemma mB_mono {x y : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxy : x ≤ y) : mB X₀ x ≤ mB X₀ y := by
  have hX0 := X0_pos hc
  obtain ⟨h1, -⟩ := mB_spec hX0 hx
  obtain ⟨-, h2⟩ := mB_spec hX0 (hx.trans hxy)
  by_contra hcon
  push_neg at hcon
  have := uS_mono (X₀ := X₀) (show mB X₀ y + 1 ≤ mB X₀ x by omega)
  linarith

lemma mB_le_add2 {x y : ℝ} (hx : (X₀ : ℝ) ≤ x) (hy : (X₀ : ℝ) ≤ y) (hyx : y ≤ 4 * x) :
    mB X₀ y ≤ mB X₀ x + 2 := by
  have hX0 := X0_pos hc
  obtain ⟨-, h1⟩ := mB_spec hX0 hx
  obtain ⟨h2, -⟩ := mB_spec hX0 hy
  by_contra hcon
  push_neg at hcon
  have h3 := uS_mono (X₀ := X₀) (show mB X₀ x + 1 + 2 ≤ mB X₀ y by omega)
  rw [uS_add] at h3
  norm_num at h3
  linarith

lemma mB_self : mB X₀ X₀ = 0 := by
  have hX0 := X0_pos hc
  obtain ⟨h1, -⟩ := mB_spec hX0 (le_refl (X₀ : ℝ))
  by_contra hcon
  have h2 := uS_mono (X₀ := X₀) (show 0 + 1 ≤ mB X₀ X₀ by omega)
  rw [uS_add] at h2
  have : uS X₀ 0 = X₀ := by unfold uS; simp
  rw [this] at h2
  linarith

lemma Hc_small {s : ℝ} (hs : (X₀ : ℝ) / 4 ≤ s) : Queue6.Hc X₀ s ≤ s / 10 := by
  have hX0 := X0_pos hc
  have h := Queue6.Hc_le hc s
  have hm : max s X₀ ≤ 4 * s := max_le (by linarith) (by linarith)
  have : max s X₀ / 10 ^ 7 ≤ 4 * s / 10 ^ 7 := div_le_div_of_nonneg_right hm (by norm_num)
  linarith

/-- **The block indices on a strip**: for `s ∈ [v, 2v)`, `v ≥ X₀/4`, and `z` in the strip of
`s`, `m₁(z) ∈ [k₀(v), k₀(v) + 2]`. -/
lemma m1z_mem {v s z : ℝ} (hv : (X₀ : ℝ) / 4 ≤ v) (hs1 : v ≤ s) (hs2 : s < 2 * v)
    (hz : z ∈ RML10.strip X₀ s) : m1z X₀ z ∈ Finset.Icc (k0 X₀ v) (k0 X₀ v + 2) := by
  have hX0 := X0_pos hc
  obtain ⟨hz1, hz2⟩ := hz
  have hHz : Queue6.Hc X₀ z ≤ Queue6.Hc X₀ s := KR.WidthReal.Hc_mono hc.hX hz2
  have hHs := Hc_small hc (show (X₀ : ℝ) / 4 ≤ s by linarith)
  have hH0 := Queue6.Hc_nonneg (X₀ := X₀) z
  have hH0s := Queue6.Hc_nonneg (X₀ := X₀) s
  set a := max (z - Queue6.Hc X₀ z) (X₀ : ℝ) with ha
  have hlo : loB X₀ v ≤ a := by
    unfold loB
    refine max_le_max ?_ le_rfl
    nlinarith
  have hhi : a ≤ max (2 * v) X₀ := max_le_max (by linarith) le_rfl
  have hloX : (X₀ : ℝ) ≤ loB X₀ v := le_max_right _ _
  have hm1 : m1z X₀ z = mB X₀ a := rfl
  rw [Finset.mem_Icc, hm1]
  refine ⟨mB_mono hc hloX hlo, ?_⟩
  have h1 := mB_mono hc (hloX.trans hlo) hhi
  have h2 := mB_le_add2 hc hloX (le_max_right _ _)
    (show max (2 * v) (X₀ : ℝ) ≤ 4 * loB X₀ v by
      unfold loB
      refine max_le ?_ ?_
      · have := le_max_left (0.848 * v) (X₀ : ℝ); nlinarith
      · have := le_max_right (0.848 * v) (X₀ : ℝ); linarith)
  exact h1.trans h2

lemma gS_nonneg (m : ℕ) : 0 ≤ gS X₀ m := by
  unfold gS
  have h1 := Queue6.nuQ_nonneg hc (uS_facts hc m).1
  have h2 := Queue6.dQ_nonneg (X₀ := X₀) (show (1 : ℝ) ≤ uS X₀ m by
    have := (uS_facts hc m).1; have := X0_pos hc
    have := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith)
  linarith

variable {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z) (hMm : Monotone Mf) {B : ℝ}
  (hMB : ∀ z, z ≤ B → Mf z ≤ 3.1 * Real.log (max z X₀) + 4.2)

omit hc in
include hc in
/-- `MfP` satisfies the bound `hMB` at every `B`. -/
lemma MfP_le (z : ℝ) : MfP z ≤ 3.1 * Real.log (max z X₀) + 4.2 := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  unfold MfP
  have := Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right z 1))
    (max_le_max (le_refl z) hX1.le)
  linarith

include hM0 hMB in
/-- **The Step 3 weight is the per-scale noise** (Queue6's `fE_le_nuQ`, and its analogue below
`X₀`, where `m₁(z) = 0` and `H(z) = H(X₀)`): `fE12(z) ≤ 2ν(u_{m₁(z)}) + δ(u_{m₁(z)})`. -/
lemma fE12_le_gS {z : ℝ} (hzB : z ≤ B) : RML12M.fE12 X₀ Mf z ≤ gS X₀ (m1z X₀ z) := by
  have hX0 := X0_pos hc
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  rcases le_or_gt (X₀ : ℝ) z with hz | hz
  · have hm : Mf z ≤ 3.1 * Real.log z + 4.2 := by
      have := hMB z hzB; rwa [max_eq_left hz] at this
    exact Queue6.fE_le_nuQ hc hz (hM0 z) hm
  · have hH0 := Queue6.Hc_nonneg (X₀ := X₀) z
    have hm0 : m1z X₀ z = 0 := by
      show mB X₀ (max (z - Queue6.Hc X₀ z) X₀) = 0
      rw [max_eq_right (by linarith)]
      exact mB_self hc
    have hu0 : uS X₀ 0 = X₀ := by unfold uS; simp
    have hu1 : uS X₀ (0 + 1) = 2 * uS X₀ 0 := uS_succ 0
    have hHz : Queue6.Hc X₀ z = capH X₀ (uS X₀ 0) := by
      unfold Queue6.Hc; rw [max_eq_right hz.le, hu0]
    have hcap := (uS_facts hc 0).2.2.1
    have hMf : Mf z ≤ 3.1 * Real.log X₀ + 4.2 := by
      have := hMB z hzB; rwa [max_eq_right hz.le] at this
    have hl4 : Real.log (4 * (X₀ : ℝ)) = Real.log 4 + Real.log X₀ :=
      Real.log_mul (by norm_num) hX0.ne'
    have hl4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hnum : 6.6 + 4.2 * Mf z ≤ 30 * Real.log (4 * uS X₀ 0) := by
      rw [hu0, hl4]; have := hc.hX; nlinarith
    have hfrac : (6.6 + 4.2 * Mf z) / Queue6.Hc X₀ z ≤
        30 * Real.log (4 * uS X₀ 0) / capH X₀ (uS X₀ 0) := by
      rw [hHz]; exact div_le_div_of_nonneg_right hnum (by linarith)
    unfold RML12M.fE12 gS nuQ dQ
    rw [hm0, hu1]
    have h6 : 2 * (105 / Real.log (uS X₀ 0) ^ 6) = 210 / Real.log (uS X₀ 0) ^ 6 := by ring
    linarith

omit hc in
lemma sum_gS_eq (v : ℝ) :
    ∑ i ∈ Icc (k0 X₀ v) (k0 X₀ v + 2), gS X₀ i = 2 * nu13 X₀ v + dl13 X₀ v := by
  unfold gS nu13 dl13
  rw [Finset.sum_add_distrib, Finset.mul_sum]

lemma nu13_nonneg (v : ℝ) : 0 ≤ nu13 X₀ v :=
  Finset.sum_nonneg fun i _ => Queue6.nuQ_nonneg hc (uS_facts hc i).1

lemma dl13_nonneg (v : ℝ) : 0 ≤ dl13 X₀ v :=
  Finset.sum_nonneg fun i _ => Queue6.dQ_nonneg (X₀ := X₀) (by
    have := (uS_facts hc i).1
    have := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith)

omit hc in
lemma strip_self (s : ℝ) : s ∈ RML10.strip X₀ s :=
  ⟨by have := Queue6.Hc_nonneg (X₀ := X₀) s; linarith, le_rfl⟩

include hM0 hMm in
lemma Fe_nonneg (s : ℝ) : 0 ≤ Fe X₀ Mf s :=
  (RML12M.fE12_nonneg hc.hX hM0 s).trans
    (le_csSup (RML12M.bdd_fE12 hc.hX hM0 hMm s) ⟨s, strip_self (X₀ := X₀) s, rfl⟩)

include hM0 hMB in
/-- **`e(t, w) ≤ 2ν'(v) + δ'(v)`** at a point `s = t/w ∈ [v, 2v)`, `v ≥ X₀/4`. -/
lemma Fe_le {v s : ℝ} (hv : (X₀ : ℝ) / 4 ≤ v) (hs1 : v ≤ s) (hs2 : s < 2 * v)
    (hsB : s ≤ B) : Fe X₀ Mf s ≤ 2 * nu13 X₀ v + dl13 X₀ v := by
  rw [← sum_gS_eq]
  unfold Fe
  refine csSup_le ⟨_, s, strip_self (X₀ := X₀) s, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (fE12_le_gS hc hM0 hMB (hz.2.trans hsB)).trans
    (Finset.single_le_sum (fun i _ => gS_nonneg hc i)
    (m1z_mem hc hv hs1 hs2 hz))

lemma bS_ge (j : ℕ) : Xm X₀ / 2 ≤ bS X₀ j := by
  unfold bS
  have := (Xm_bounds hc).1; have := X0_pos hc
  have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

lemma bS_pos (j : ℕ) : 0 < bS X₀ j := by
  have := bS_ge hc j; have := (Xm_bounds hc).1; have := X0_pos hc; linarith

include hM0 hMm hMB in
/-- **The grouping of Step 4** (filtered cofactors, by block): at a height `t`, with
`t ≤ X₀⁻ 2^J/2`,
`∑_{w ∈ F} κ_w(t) e(t, w)/w ≤ ∑_{j<J} ω_t(v_j) (2ν'(v_j) + δ'(v_j))`. -/
theorem hS_kap (ω : JitterΩ) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j) {t : ℝ} {J : ℕ}
    (hJ : t ≤ Xm X₀ / 2 * 2 ^ J) (htB : t / 2 ≤ B) (ES jP : ℝ) :
    ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
        Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
          (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w) ≤
      ∑ j ∈ range J, (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t (bS X₀ j) *
        (2 * nu13 X₀ (bS X₀ j) + dl13 X₀ (bS X₀ j)) := by
  classical
  have hXm : 0 < Xm X₀ / 2 := by have := (Xm_bounds hc).1; have := X0_pos hc; linarith
  have heq : ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
      Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
        (RML12M.e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w) =
      KR.Sharp.Kpt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀ / 2) (Fe X₀ Mf) t := by
    unfold KR.Sharp.Kpt Margin.Rec.Fset
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold Margin.Rec.kap
    split_ifs
    · simp only [one_mul]; rfl
    · simp
  rw [heq]
  refine (le_abs_self _).trans ?_
  have := KR.RML7G.abs_Kpt_le (PR θ X₀ ω) (twR θ X₀ ω) hXm hp2 (Fe X₀ Mf) hJ
    (fun j => 2 * nu13 X₀ (bS X₀ j) + dl13 X₀ (bS X₀ j))
    (fun j => by have := nu13_nonneg hc (bS X₀ j); have := dl13_nonneg hc (bS X₀ j); linarith)
    (fun j _ s hs1 hs2 hst => by
      rw [abs_of_nonneg (Fe_nonneg hc hM0 hMm s)]
      have hv : (X₀ : ℝ) / 4 ≤ bS X₀ j := by
        have := bS_ge hc j; have := (Xm_bounds hc).1; linarith
      exact Fe_le hc hM0 hMB hv (by unfold bS; linarith) (by unfold bS; linarith)
        (by linarith))
  exact this

end Blocks

end BModel.RML13

end
