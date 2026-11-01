module

public import Mathlib

/-!
# Proposition 5.38, Steps 3 and 5: the variation recursion and its solution

Step 3 of the proof of Proposition 5.38 (04g-margin.tex) gives, for the variation
`v(t) = sup_{|h| ≤ 1.01H(t)} |m(t+h) - m(t)|`, the recursion

  `v(t) ≤ S(t) + ∑_{w ≥ 2} 1.01 κ_w w^{ε-2} sup{v(t') : |t' - t/w| ≤ 2.1 H(t/w)}`,

which reads `v` only at points `≤ t/2 + 2.1H(t/2) < t` (a well-founded induction on `t`), with
the base case `t < 2X₀⁻`. We state it abstractly: at each `t ≥ T₀` there is a finite family of
cofactors `i ∈ F t` with weights `c t i ≥ 0` and neighbourhoods `N t i` of points `≤ t - 1`, and
the recursion is written without suprema, as

  `RecIneq` : whenever `v ≤ b i` on `N t i` for every `i`, `v t ≤ S t + ∑ c t i · b i`.

* `Margin.Var.le_of_super` : a super-solution `V` (`S t + ∑ c t i b_i ≤ V t` whenever `V ≤ b_i`
  on `N t i`, and `v ≤ V` below `T₀`) dominates `v` everywhere (the induction of Step 3);
* `Margin.Var.step5_split` : **Step 5**, the split at `M = √t`: if
  `v(t) ≤ ∑_M a_M E_S/log(t/M) + v_{X₀}(t)` over a finite set of chain products `M ≥ 1`
  (`a_1 = 1`, `∑_{2 ≤ M ≤ √t} a_M ≤ A₀`, and the tail `M > √t` contributes at most
  `τ E_S/log t`), then `v(t) log t ≤ (2(1 + A₀) + τ) E_S + v_{X₀}(t) log t`; with
  `A₀ = A₀(0.045) ≤ 2.218` and `τ ≤ X₀^{-0.09} ≤ 0.06` this is `≤ 6.5 E_S + V_{X₀}(t)`
  (`step5_hv`).
-/

@[expose] public section

open Finset

namespace Margin.Var

variable {ι : Type*}

/-- The recursion of Step 3, without suprema. -/
def RecIneq (T0 : ℝ) (v S : ℝ → ℝ) (F : ℝ → Finset ι) (c : ℝ → ι → ℝ)
    (N : ℝ → ι → Set ℝ) : Prop :=
  ∀ t, T0 ≤ t → ∀ b : ι → ℝ, (∀ i ∈ F t, ∀ t' ∈ N t i, v t' ≤ b i) →
    v t ≤ S t + ∑ i ∈ F t, c t i * b i

/-- `V` is a super-solution of the recursion. -/
def Super (T0 : ℝ) (V S : ℝ → ℝ) (F : ℝ → Finset ι) (c : ℝ → ι → ℝ)
    (N : ℝ → ι → Set ℝ) : Prop :=
  ∀ t, T0 ≤ t → ∃ b : ι → ℝ, (∀ i ∈ F t, ∀ t' ∈ N t i, V t' ≤ b i) ∧
    S t + ∑ i ∈ F t, c t i * b i ≤ V t

/-- **The induction of Step 3**: the recursion, a super-solution, the base case and the
well-foundedness (`N t i ⊆ (-∞, t - 1]`) give `v ≤ V`. -/
theorem le_of_super {T0 : ℝ} {v V S : ℝ → ℝ} {F : ℝ → Finset ι} {c : ℝ → ι → ℝ}
    {N : ℝ → ι → Set ℝ} (hrec : RecIneq T0 v S F c N) (hsup : Super T0 V S F c N)
    (hbase : ∀ t, t < T0 → v t ≤ V t)
    (hN : ∀ t, T0 ≤ t → ∀ i ∈ F t, ∀ t' ∈ N t i, t' ≤ t - 1) : ∀ t, v t ≤ V t := by
  -- induction on `n` with the claim `∀ t < n, v t ≤ V t` (shifted so that it starts at `T₀`)
  have key : ∀ n : ℕ, ∀ t, t < T0 + n → v t ≤ V t := by
    intro n
    induction n with
    | zero => intro t ht; exact hbase t (by simpa using ht)
    | succ n ih =>
      intro t ht
      rcases lt_or_ge t T0 with h0 | h0
      · exact hbase t h0
      obtain ⟨b, hb, hle⟩ := hsup t h0
      have hv : ∀ i ∈ F t, ∀ t' ∈ N t i, v t' ≤ b i := by
        intro i hi t' ht'
        have h1 := hN t h0 i hi t' ht'
        have h2 : t' < T0 + n := by push_cast at ht; linarith
        exact (ih t' h2).trans (hb i hi t' ht')
      exact (hrec t h0 b hv).trans hle
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t - T0)
  exact key n t (by linarith)

/-- **Step 5, the split at `M = √t`.** `P` is the finite set of chain products (values `M ≥ 1`),
`a M ≥ 0` the chain weights (`a 1 = 1` for the trivial chain, `∑_{2 ≤ M ≤ √t} a M ≤ A₀`), and
the tail `M > √t` is bounded by `τ E_S/log t` (Rankin's trick in the paper). Then
`v(t) log t ≤ (2(1 + A₀) + τ) E_S + v_{X₀}(t) log t`. -/
theorem step5_split {t ES A0 τ vX : ℝ} {v : ℝ} (P : Finset ℝ) (a : ℝ → ℝ)
    (ht : 1 < t) (hES : 0 ≤ ES) (ha : ∀ M ∈ P, 0 ≤ a M) (hP1 : ∀ M ∈ P, 1 ≤ M)
    (hv : v ≤ ∑ M ∈ P, a M * ES / Real.log (t / M) + vX)
    (hhead : ∑ M ∈ P.filter (fun M => M ≤ √t), a M ≤ 1 + A0)
    (htail : ∑ M ∈ P.filter (fun M => ¬ M ≤ √t), a M * ES / Real.log (t / M) ≤
      τ * ES / Real.log t) :
    v * Real.log t ≤ (2 * (1 + A0) + τ) * ES + vX * Real.log t := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  -- head terms: `log(t/M) ≥ log t/2`
  have hhead' : ∑ M ∈ P.filter (fun M => M ≤ √t), a M * ES / Real.log (t / M) ≤
      2 * (1 + A0) * ES / Real.log t := by
    have hpt : ∀ M ∈ P.filter (fun M => M ≤ √t),
        a M * ES / Real.log (t / M) ≤ a M * (2 * ES / Real.log t) := by
      intro M hM
      obtain ⟨hMP, hMs⟩ := Finset.mem_filter.mp hM
      have hM1 := hP1 M hMP
      have hsq : √t * √t = t := Real.mul_self_sqrt (by linarith)
      have hlog : Real.log t / 2 ≤ Real.log (t / M) := by
        have h1 : √t ≤ t / M := by
          rw [le_div_iff₀ (by linarith)]; nlinarith [Real.sqrt_nonneg t]
        have h2 : Real.log √t = Real.log t / 2 := Real.log_sqrt (by linarith)
        rw [← h2]
        exact Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) h1
      have hpos : 0 < Real.log (t / M) := by linarith
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (ha M hMP)
      rw [div_le_div_iff₀ hpos hlt]
      nlinarith
    calc ∑ M ∈ P.filter (fun M => M ≤ √t), a M * ES / Real.log (t / M)
        ≤ ∑ M ∈ P.filter (fun M => M ≤ √t), a M * (2 * ES / Real.log t) :=
          Finset.sum_le_sum hpt
      _ = (∑ M ∈ P.filter (fun M => M ≤ √t), a M) * (2 * ES / Real.log t) := by
          rw [Finset.sum_mul]
      _ ≤ (1 + A0) * (2 * ES / Real.log t) :=
          mul_le_mul_of_nonneg_right hhead (by positivity)
      _ = 2 * (1 + A0) * ES / Real.log t := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun M => M ≤ √t)
    (fun M => a M * ES / Real.log (t / M))
  have htot : v ≤ (2 * (1 + A0) + τ) * ES / Real.log t + vX := by
    have : (2 * (1 + A0) + τ) * ES / Real.log t =
        2 * (1 + A0) * ES / Real.log t + τ * ES / Real.log t := by ring
    linarith
  have := mul_le_mul_of_nonneg_right htot hlt.le
  have e : ((2 * (1 + A0) + τ) * ES / Real.log t + vX) * Real.log t =
      (2 * (1 + A0) + τ) * ES + vX * Real.log t := by field_simp
  linarith

/-- **Step 5, numerical form**: with `A₀ ≤ 2.218` and `τ ≤ 0.06`,
`v(t) log t ≤ 6.5 E_S + V_{X₀}(t)` where `V_{X₀}(t) ≥ v_{X₀}(t) log t`. -/
theorem step5_hv {t ES A0 τ vX VX : ℝ} {v : ℝ} (P : Finset ℝ) (a : ℝ → ℝ)
    (ht : 1 < t) (hES : 0 ≤ ES) (ha : ∀ M ∈ P, 0 ≤ a M) (hP1 : ∀ M ∈ P, 1 ≤ M)
    (hv : v ≤ ∑ M ∈ P, a M * ES / Real.log (t / M) + vX)
    (hhead : ∑ M ∈ P.filter (fun M => M ≤ √t), a M ≤ 1 + A0)
    (htail : ∑ M ∈ P.filter (fun M => ¬ M ≤ √t), a M * ES / Real.log (t / M) ≤
      τ * ES / Real.log t)
    (hA0 : A0 ≤ 2.218) (hτ : τ ≤ 0.06) (hVX : vX * Real.log t ≤ VX) :
    v * Real.log t ≤ 6.5 * ES + VX := by
  have h := step5_split P a ht hES ha hP1 hv hhead htail
  have : (2 * (1 + A0) + τ) * ES ≤ 6.5 * ES :=
    mul_le_mul_of_nonneg_right (by linarith) hES
  linarith

end Margin.Var

end
