module

public import RequestProject.Beurling.Defs

/-!
# Auxiliary lemmas

* bounds on the iterated logarithm `logStar`;
* uniqueness of the analytic continuation of `ζ_P` to a punctured half-plane.
-/

@[expose] public section

open Complex Filter Topology

/-! ### The iterated logarithm -/

lemma iterate_log_gt_aux : ∀ (n : ℕ) (y : ℝ), (∀ k ≤ n, 1 < Real.log^[k] y) → (n : ℝ) + 1 < y := by
  intro n
  induction n with
  | zero => intro y h; simpa using h 0 le_rfl
  | succ n ih =>
    intro y h
    have h1 : (n : ℝ) + 1 < Real.log y := ih (Real.log y) fun k hk => by
      have := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have h2 := Real.add_one_le_exp (Real.log y)
    have hy : 0 < y := by
      have := h 0 (Nat.zero_le _); simp at this; linarith
    rw [Real.exp_log hy] at h2
    push_cast; linarith

lemma not_mem_logStar_set {x : ℝ} {k : ℕ} (hk : k < logStar x) : 1 < Real.log^[k] x := by
  have := Nat.notMem_of_lt_sInf hk
  simpa using this

lemma logStar_le_log_add_one {x : ℝ} (hx : 1 ≤ x) : (logStar x : ℝ) ≤ Real.log x + 1 := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases hm : logStar x ≤ 1
  · have : (logStar x : ℝ) ≤ 1 := by exact_mod_cast hm
    linarith
  · push_neg at hm
    have := iterate_log_gt_aux (logStar x - 2) (Real.log x) fun k hk => by
      have := not_mem_logStar_set (x := x) (k := k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have h2 : ((logStar x - 2 : ℕ) : ℝ) = (logStar x : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [h2] at this
    linarith

lemma one_le_logStar {x : ℝ} (hx : 1 < x) : 1 ≤ logStar x := by
  have hne : {n : ℕ | Real.log^[n] x ≤ 1}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨n, hn⟩ := exists_nat_gt x
    have := iterate_log_gt_aux n x fun k _ => by
      by_contra hk
      push_neg at hk
      have : k ∈ {n : ℕ | Real.log^[n] x ≤ 1} := hk
      rw [h] at this
      exact this
    linarith
  by_contra h
  push_neg at h
  have h0 : logStar x = 0 := by omega
  have := Nat.sInf_mem hne
  rw [show sInf {n : ℕ | Real.log^[n] x ≤ 1} = 0 from h0] at this
  simp at this
  linarith

/-- `log* x = O(x^δ)` for every `δ > 0`, in the explicit form `log* x ≤ (1/δ + 1) x^δ`. -/
lemma logStar_le_rpow {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    (logStar x : ℝ) ≤ (1 / δ + 1) * x ^ δ := by
  have h1 := logStar_le_log_add_one hx
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
  have h3 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
  nlinarith

/-- If `|(1 - r_k) log x_k - 3 log log x_k| ≤ C` along `x_k → ∞`, then `r_k → 1`. -/
lemma tendsto_one_of_log_asymptotic (r : ℕ → ℝ) (xk : ℕ → ℝ) (C : ℝ)
    (hx : Tendsto xk atTop atTop)
    (hb : ∀ k, |(1 - r k) * Real.log (xk k) - 3 * Real.log (Real.log (xk k))| ≤ C) :
    Tendsto r atTop (𝓝 1) := by
  have hy : Tendsto (fun k => Real.log (xk k)) atTop atTop := Real.tendsto_log_atTop.comp hx
  have hg : Tendsto (fun y : ℝ => (3 * Real.log y + |C|) / y) atTop (𝓝 0) := by
    have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 : Tendsto (fun y : ℝ => |C| / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (h1.const_mul 3).add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with y hy
    simp only [id]
    field_simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (hg.comp hy)
  filter_upwards [hy.eventually_ge_atTop 1] with k hk
  have hlog : 0 ≤ Real.log (Real.log (xk k)) := Real.log_nonneg hk
  have hpos : 0 < Real.log (xk k) := by linarith
  simp only [Function.comp, Real.norm_eq_abs]
  rw [le_div_iff₀ hpos]
  have := hb k
  have e : |r k - 1| * Real.log (xk k) = |(1 - r k) * Real.log (xk k)| := by
    rw [abs_mul, abs_of_pos hpos, abs_sub_comm]
  rw [e]
  have := abs_sub_abs_le_abs_sub ((1 - r k) * Real.log (xk k)) (3 * Real.log (Real.log (xk k)))
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * Real.log (Real.log (xk k)))] at this
  have := le_abs_self C
  linarith

/-! ### Uniqueness of the continuation of `ζ_P` -/

namespace BeurlingSystem

lemma isOpen_puncturedHalfPlane (a : ℝ) : IsOpen (puncturedHalfPlane a) :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

lemma isPreconnected_puncturedHalfPlane (a : ℝ) :
    IsPreconnected (puncturedHalfPlane a) := by
  rcases le_or_gt 1 a with ha | ha
  · convert! (convex_halfSpace_re_gt a).isPreconnected using 1
    ext s
    simp only [puncturedHalfPlane, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, fun e => by subst e; simp at h; linarith⟩⟩
  have hA := ((convex_halfSpace_re_gt a).inter (convex_halfSpace_im_gt 0)).isPreconnected.union
    (2 + I) (by simp; linarith) (by simp) (convex_halfSpace_re_gt 1).isPreconnected
  have hB := hA.union (((a+1)/2 : ℝ) + I) (by left; simp; linarith)
    (by simp; constructor <;> linarith)
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hC := hB.union (2 - I) (by left; right; simp) (by simp; linarith)
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_im_lt 0)).isPreconnected
  convert! hC using 1
  ext s
  simp only [puncturedHalfPlane, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy s.im 0 with h | h | h
    · right; exact ⟨h1, h⟩
    · rcases lt_trichotomy s.re 1 with h' | h' | h'
      · left; right; exact ⟨h1, h'⟩
      · exact absurd (Complex.ext (by simp [h']) (by simp [h])) h2
      · left; left; right; exact h'
    · left; left; left; exact ⟨h1, h⟩
  · rintro (((⟨h1, h⟩ | h) | ⟨h1, h⟩) | ⟨h1, h⟩)
    · exact ⟨h1, fun e => by subst e; simp at h⟩
    · exact ⟨by linarith, fun e => by subst e; simp at h⟩
    · exact ⟨h1, fun e => by subst e; simp at h⟩
    · exact ⟨h1, fun e => by subst e; simp at h⟩

lemma puncturedHalfPlane_mono {a b : ℝ} (h : a ≤ b) :
    puncturedHalfPlane b ⊆ puncturedHalfPlane a := by
  intro s hs
  exact ⟨lt_of_le_of_lt h hs.1, hs.2⟩

/-- Two analytic continuations of `ζ_P` to punctured half-planes agree on the common
punctured half-plane (identity theorem). -/
lemma IsZetaContinuation.eqOn {P : BeurlingSystem} {a b : ℝ} {F G : ℂ → ℂ}
    (hF : P.IsZetaContinuation a F) (hG : P.IsZetaContinuation b G) :
    Set.EqOn F G (puncturedHalfPlane (max a b)) := by
  set U := puncturedHalfPlane (max a b)
  have hU : IsOpen U := isOpen_puncturedHalfPlane _
  have hFU : DifferentiableOn ℂ F U :=
    hF.1.mono (puncturedHalfPlane_mono (le_max_left a b))
  have hGU : DifferentiableOn ℂ G U :=
    hG.1.mono (puncturedHalfPlane_mono (le_max_right a b))
  set z₀ : ℂ := ((max (max a b) 1 + 1 : ℝ) : ℂ)
  have hz₀re : z₀.re = max (max a b) 1 + 1 := by simp [z₀]
  have hz₀ : z₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · show max a b < z₀.re
      rw [hz₀re]; linarith [le_max_left (max a b) 1]
    · intro h
      have : z₀.re = 1 := by rw [Set.mem_singleton_iff.mp h]; simp
      rw [hz₀re] at this; linarith [le_max_right (max a b) 1]
  refine (hFU.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hGU.analyticOnNhd hU)
    (isPreconnected_puncturedHalfPlane _) hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z₀ ∈ {s : ℂ | 1 < s.re} := by
    show 1 < z₀.re
    rw [hz₀re]; linarith [le_max_right (max a b) 1]
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [hF.2 s hs, hG.2 s hs]

end BeurlingSystem

end
