module

public import RequestProject.Beurling.Noise.RML6Var2Misc
public import RequestProject.Beurling.Noise.RML6PredOps
public import RequestProject.Beurling.Noise.KRNormFix
public import RequestProject.Beurling.Noise.MarginRecSuper
public import RequestProject.Beurling.Noise.MarginRecStep

/-!
# Filter switching costs at most `2η(t+h)` (Proposition 5.38, Step 3)

`sw_le` : `|∑_{w ∈ F} (κ_w(t+h) - κ_w(t)) ρ̃((t+h)/w)/w| ≤ 2 η(t+h)`, where
`η(y) = ∑_{w τ-near at y} 1/w` (`KR.etaG … (fun _ => 1)`), for `|h| ≤ 1.01 H(t)`,
`0 ≤ ρ̃ ≤ 2` and `ρ̃ = 0` below `X₀⁻`: a cofactor whose filter switches between `t` and `t+h`
has `τ_w` between `t/w` and `(t+h)/w`, so it is `τ`-near at `t+h` by (RH).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML14

/-- `supW F c ≤ C` if `F h ≤ C` for `|h| ≤ c` (`c ≥ 0`). -/
lemma supW_le {F : ℝ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hb : ∀ h, |h| ≤ c → F h ≤ C) :
    Margin.RML6.supW F c ≤ C := by
  unfold Margin.RML6.supW
  haveI : Nonempty {h : ℝ // |h| ≤ c} := ⟨⟨0, by simpa using hc⟩⟩
  exact ciSup_le fun h => hb h.1 h.2

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m ε : ℝ}

/-- A cofactor whose filter switches between `t` and `s` has `|τ_w - s/w| ≤ |s - t|/w`. -/
lemma tau_near_of_switch {w : ℕ} (hw : 2 ≤ w) {t s : ℝ}
    (hk : Margin.Rec.kap P tw s w ≠ Margin.Rec.kap P tw t w) :
    |tauW tw w - s / Vl P w| ≤ |s - t| / Vl P w := by
  have hV : 0 < Vl P w := KR.Sharp.Vl_pos P w
  have hne : w.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hiff : ∀ y, (∀ p ∈ w.primeFactors, tw p * Vl P w < y) ↔ tauW tw w < y / Vl P w := by
    intro y
    rw [← forall_lt_iff_tauW hne]
    exact forall₂_congr fun p _ => (lt_div_iff₀ hV).symm
  have key : ∀ y, Margin.Rec.kap P tw y w = if tauW tw w < y / Vl P w then 1 else 0 := by
    intro y
    unfold Margin.Rec.kap
    by_cases hq : tauW tw w < y / Vl P w
    · rw [if_pos ((hiff y).mpr hq), if_pos hq]
    · rw [if_neg (mt (hiff y).mp hq), if_neg hq]
  rw [key, key] at hk
  have e1 : t / Vl P w - s / Vl P w = (t - s) / Vl P w := by ring
  have hA : 0 ≤ |s - t| / Vl P w := div_nonneg (abs_nonneg _) hV.le
  have a1 : -(|s - t| / Vl P w) ≤ (t - s) / Vl P w := by
    rw [← neg_div, div_le_div_iff_of_pos_right hV]
    have := neg_abs_le (t - s); rw [abs_sub_comm] at this; linarith
  have a3 : (t - s) / Vl P w ≤ |s - t| / Vl P w := by
    rw [div_le_div_iff_of_pos_right hV]
    have := le_abs_self (t - s); rw [abs_sub_comm] at this; linarith
  rw [abs_le]
  by_cases h1 : tauW tw w < s / Vl P w <;> by_cases h2 : tauW tw w < t / Vl P w
  · simp only [h1, h2, if_true, ne_eq, not_true_eq_false] at hk
  · push_neg at h2
    constructor <;> linarith
  · push_neg at h1
    constructor <;> linarith
  · simp only [h1, h2, if_false, ne_eq, not_true_eq_false] at hk


/-- `|h|/w ≤ 2 H((t+h)/w)` for `|h| ≤ 1.01 H(t)`, `t ≤ 2(t+h)`, `w ≥ 2`, by (RH). -/
lemma shift_le_twoH (hRH : ∀ v w, X0m / 2 ≤ v → 1 ≤ w → H (v * w) ≤ w ^ ε * H v)
    (hε : ε ≤ 1 / 2) (hmono : Monotone H) (hX : 0 < X0m)
    {V t h : ℝ} (hV : 2 ≤ V) (ht : t ≤ 2 * (t + h)) (hs : X0m ≤ (t + h) / V)
    (hh : |h| ≤ 1.01 * H t) : |h| / V ≤ 2 * H ((t + h) / V) := by
  have hV0 : 0 < V := by linarith
  set v := (t + h) / V with hv
  have hv0 : 0 < v := by linarith
  have htv : t ≤ v * (2 * V) := by
    have : v * (2 * V) = 2 * (t + h) := by rw [hv]; field_simp
    linarith
  have h1 : H t ≤ (2 * V) ^ ε * H v :=
    (hmono htv).trans (hRH v (2 * V) (by linarith) (by linarith))
  have hH0 : 0 ≤ H v := by
    have hp : 0 < (2 * V) ^ ε := Real.rpow_pos_of_pos (by linarith) _
    have : 0 ≤ (2 * V) ^ ε * H v := by linarith [abs_nonneg h]
    by_contra hn; push_neg at hn; nlinarith [mul_neg_of_pos_of_neg hp hn]
  have h2 : (2 * V) ^ ε ≤ (2 * V) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hε
  have hsq : (2 * V) ^ (1 / 2 : ℝ) = √(2 * V) := (Real.sqrt_eq_rpow _).symm
  have hs2 : 2 ≤ √(2 * V) := by
    have h4 := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ 2 * V by linarith)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
  have hss : √(2 * V) * √(2 * V) = 2 * V := Real.mul_self_sqrt (by linarith)
  have h3 : 1.01 * (2 * V) ^ ε ≤ 2 * V := by
    rw [hsq] at h2; nlinarith
  rw [div_le_iff₀ hV0]
  calc |h| ≤ 1.01 * H t := hh
    _ ≤ 1.01 * ((2 * V) ^ ε * H v) := by linarith
    _ = (1.01 * (2 * V) ^ ε) * H v := by ring
    _ ≤ (2 * V) * H v := mul_le_mul_of_nonneg_right h3 hH0
    _ = 2 * H v * V := by ring

/-- **Filter switching** (Proposition 5.38, Step 3): for `|h| ≤ 1.01 H(t)` and `t ≤ 2(t+h)`,
`|∑_{w ∈ F} (κ_w(t+h) - κ_w(t)) ρ̃((t+h)/w)/w| ≤ 2 η(t+h)`. -/
theorem sw_le (hRH : ∀ v w, X0m / 2 ≤ v → 1 ≤ w → H (v * w) ≤ w ^ ε * H v)
    (hε : ε ≤ 1 / 2) (hmono : Monotone H) (hX : 0 < X0m)
    (hp2 : ∀ j, 2 ≤ P.p j) {ρ : ℝ → ℝ} (hρ0 : ∀ z, z < X0m → ρ z = 0)
    (hρ : ∀ z, 0 ≤ ρ z ∧ ρ z ≤ 2) (F : Finset ℕ)
    (hF : ∀ w ∈ F, 2 ≤ w ∧ ∃ e, iota e = w) {t h : ℝ} (ht : t ≤ 2 * (t + h))
    (hh : |h| ≤ 1.01 * H t) :
    |∑ w ∈ F, (Margin.Rec.kap P tw (t + h) w - Margin.Rec.kap P tw t w) *
        (ρ ((t + h) / Vl P w) / Vl P w)| ≤
      2 * etaG P H tw X0m (fun _ => 1) (t + h) := by
  classical
  set s := t + h with hs
  set g : ℕ → ℝ := fun w => |(Margin.Rec.kap P tw s w - Margin.Rec.kap P tw t w) *
      (ρ (s / Vl P w) / Vl P w)| with hg
  set S := (Cof P X0m s).filter (fun m => TauNearAt P H tw X0m s m) with hS
  have hg0 : ∀ w, 0 ≤ g w := fun w => abs_nonneg _
  have hgle : ∀ w, g w ≤ 2 / Vl P w := by
    intro w
    have hV := KR.Sharp.Vl_pos P w
    have k1 := Margin.Rec.kap_mem P tw s w
    have k2 := Margin.Rec.kap_mem P tw t w
    have hk : |Margin.Rec.kap P tw s w - Margin.Rec.kap P tw t w| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [k1.1, k1.2, k2.1, k2.2]
    simp only [hg]
    rw [abs_mul, abs_div, abs_of_pos hV, abs_of_nonneg (hρ _).1]
    calc _ ≤ 1 * (2 / Vl P w) :=
          mul_le_mul hk (div_le_div_of_nonneg_right (hρ _).2 hV.le) (div_nonneg (hρ _).1 hV.le)
            (by norm_num)
      _ = 2 / Vl P w := one_mul _
  have hsub : F.filter (fun w => g w ≠ 0) ⊆ S := by
    intro w hw
    obtain ⟨hwF, hgw⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw2, e, rfl⟩ := hF _ hwF
    have hV := KR.Sharp.Vl_pos P (iota e)
    have hV2 : 2 ≤ Vl P (iota e) := KR.Ops.Vl_ge_two hp2 hw2
    have hk : Margin.Rec.kap P tw s (iota e) ≠ Margin.Rec.kap P tw t (iota e) := by
      intro heq; apply hgw; simp only [hg, heq, sub_self, zero_mul, abs_zero]
    have hρs : X0m ≤ s / Vl P (iota e) := by
      by_contra hlt; push_neg at hlt
      apply hgw; simp only [hg, hρ0 _ hlt, zero_div, mul_zero, abs_zero]
    have htau := tau_near_of_switch (P := P) (tw := tw) hw2 hk
    have hsh := shift_le_twoH hRH hε hmono hX hV2 ht hρs hh
    have e1 : |s - t| = |h| := by rw [hs]; ring_nf
    rw [e1] at htau
    simp only [hS, Finset.mem_filter]
    refine ⟨?_, htau.trans hsh, hρs⟩
    unfold Cof
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e, ?_, rfl⟩, hw2⟩
    rw [mem_elems]
    have hval : Vl P (iota e) = P.val e := P.valN_iota e
    rw [hval] at hρs
    rw [le_div_iff₀ hX]
    rw [le_div_iff₀ (P.val_pos e)] at hρs
    linarith
  calc |∑ w ∈ F, (Margin.Rec.kap P tw (t + h) w - Margin.Rec.kap P tw t w) *
        (ρ ((t + h) / Vl P w) / Vl P w)| ≤ ∑ w ∈ F, g w := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ F.filter (fun w => g w ≠ 0), g w := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ w ∈ F.filter (fun w => g w ≠ 0), 2 / Vl P w := Finset.sum_le_sum fun w _ => hgle w
    _ ≤ ∑ w ∈ S, 2 / Vl P w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
          div_nonneg (by norm_num) (KR.Sharp.Vl_pos P w).le
    _ = 2 * etaG P H tw X0m (fun _ => 1) s := by
        unfold etaG; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => by ring

end KR.RML14

end
