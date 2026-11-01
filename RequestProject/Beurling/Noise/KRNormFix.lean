module

public import RequestProject.Beurling.Noise.KRNormTrans
public import RequestProject.Beurling.Noise.KRTrueTerm

/-!
# Proposition 5.18, the `∞`-norm bound: regrouping and the fixed points

* `etaG ψ v = ∑_{w τ-near at v} ψ(v/w)/w`; with `ψ = log + B₁` this is the paper's
  `θ(v) = ∑_{w τ-near at v} (log(v/w) + B₁)/w`, with `ψ = 1` it is `η(v)` (Lemma 5.20);
* `regroupG` : regrouping the `τ`-sources by their parents with a general weight;
* `regroupX0T` : `regroupX0` (step (iii)) over an arbitrary finite set of levels;
* `fixed_point_const` : the scalar fixed point `A ≤ a + b ∑ A s`, `b ∑ s ≤ q < 1` ⟹
  `A ≤ a/(1 - q)`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

/-- `∑_{w τ-near at v} ψ(v/w)/w`. -/
noncomputable def etaG (ψ : ℝ → ℝ) (v : ℝ) : ℝ :=
  open scoped Classical in
  ∑ m ∈ (Cof P X0m v).filter (fun m => TauNearAt P H tw X0m v m), ψ (v / Vl P m) / Vl P m

/-- **Lemma 5.20, `θ_*`**: `θ(v) = ∑_{w τ-near at v} (log(v/w) + B₁)/w ≤ θ_*` for every `v`
(`B₁ = 1`), `θ_* ≥ 0`. -/
def ThetaStar (θs : ℝ) : Prop :=
  0 ≤ θs ∧ ∀ v, etaG P H tw X0m (fun y => Real.log y + 1) v ≤ θs

/-- **Lemma 5.20, the block sums of `η`**: `η(v) = ∑_{w τ-near at v} 1/w ≤ s_v` on `[v, 2v)`,
`s_v ≥ 0` (the paper bounds `∑_v sup η ≤ E⁰_η/log X₀`). -/
def EtaBlk (Sc : Finset ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → etaG P H tw X0m (fun _ => 1) y ≤ s v

variable {P H tw X0m x}

/-- **Regrouping by the parents with a weight**: with `n' = d w`,
`∑_{n'} (∑_{d → n' τ-near} a(d)) ψ(x/n')/n' ≤ ∑_d (a(d)/d) ∑_{w τ-near at x/d} ψ(x/(dw))/w`,
for `ψ ≥ 0` above `X₀⁻`. -/
theorem regroupG {X0 : ℝ} (_hp2 : ∀ j, 2 ≤ P.p j) (hXm1 : 1 < X0m) (ψ : ℝ → ℝ)
    (hψ : ∀ y, X0m ≤ y → 0 ≤ ψ y) :
    ∑ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
        (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
          (ψ (posn P.labelVal x n') / Vl P n') ≤
      ∑ d ∈ NAll P x X0m,
        aLev P H tw X0m x d / Vl P d * etaG P H tw X0m ψ (posn P.labelVal x d) := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX : 0 < X0m := by linarith
  set Src := (NAll P x X0m).filter (2 ≤ ·)
  set F : ℕ → ℕ → ℝ := fun n' d =>
    aLev P H tw X0m x d * (ψ (posn P.labelVal x n') / Vl P n')
  have e1 : ∀ n' ∈ Src, (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) *
      (ψ (posn P.labelVal x n') / Vl P n') = ∑ d ∈ Dset P H tw X0m x X0 n', F n' d := by
    intro n' _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := NAll P x X0m)
    (s' := fun d => Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n'))]
  · refine Finset.sum_le_sum fun d hd => ?_
    have hVd := KR.valN_labelVal_pos P d
    set T := (Cof P X0m (posn P.labelVal x d)).filter
      (fun m => TauNearAt P H tw X0m (posn P.labelVal x d) m)
    set g : ℕ → ℝ := fun m => ψ (posn P.labelVal x d / Vl P m) / Vl P m
    have hS : ∀ n' ∈ Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n'),
        F n' d = aLev P H tw X0m x d / Vl P d * g (n' / d) ∧ n' / d ∈ T ∧ d ∣ n' := by
      intro n' hn'
      obtain ⟨hn'S, hdD⟩ := Finset.mem_filter.mp hn'
      obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'S
      unfold Dset at hdD
      obtain ⟨hdm, hτ, -⟩ := Finset.mem_filter.mp hdD
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n' ≠ 0 := by omega
      have hm2 := two_le_div_of_mem hdm
      have hpp : posn P.labelVal x d / Vl P (n' / d) = posn P.labelVal x n' :=
        posn_div hval hdn hn0
      have hVV : Vl P n' = Vl P d * Vl P (n' / d) := valN_div_mul hval hdn hn0
      have hposn := posn_ge_of_mem_NAll hn'A hX
      have hVm := KR.valN_labelVal_pos P (n' / d)
      refine ⟨?_, ?_, hdn⟩
      · simp only [F, g]; rw [hpp, hVV]; field_simp
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hm2⟩, ?_⟩
        · apply KR.mem_image_iota P (by omega)
          rw [le_div_iff₀ hX]
          rw [← hpp, le_div_iff₀ hVm] at hposn
          linarith
        · unfold TauNearAt; rw [hpp]
          exact ⟨hτ, hposn⟩
    calc ∑ n' ∈ Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n'), F n' d
        = ∑ n' ∈ Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n'),
            aLev P H tw X0m x d / Vl P d * g (n' / d) :=
          Finset.sum_congr rfl fun n' hn' => (hS n' hn').1
      _ = ∑ m ∈ (Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n')).image (· / d),
            aLev P H tw X0m x d / Vl P d * g m := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only at hab
          have ha' := (hS a ha).2.2
          have hb' := (hS b hb).2.2
          rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
      _ ≤ ∑ m ∈ T, aLev P H tw X0m x d / Vl P d * g m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨n', hn', rfl⟩ := Finset.mem_image.mp hm
            exact (hS n' hn').2.1
          · intro m hm _
            have hmT := Finset.mem_filter.mp hm
            have hVm := KR.valN_labelVal_pos P m
            exact mul_nonneg (div_nonneg (aLev_nonneg d) hVd.le)
              (div_nonneg (hψ _ hmT.2.2) hVm.le)
      _ = aLev P H tw X0m x d / Vl P d * etaG P H tw X0m ψ (posn P.labelVal x d) := by
          rw [← Finset.mul_sum]; rfl
  · intro n' d
    constructor
    · rintro ⟨hn', hd⟩
      refine ⟨Finset.mem_filter.mpr ⟨hn', hd⟩, ?_⟩
      unfold Dset at hd
      obtain ⟨hdm, -⟩ := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn'A := (Finset.mem_filter.mp hn').1
      have hn0 : n' ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
      apply mem_NAll_of_posn hd0 hX
      have h1 := posn_ge_of_mem_NAll hn'A hX
      rw [posn_mul hval hdn hn0]
      have hw := LemmaM.one_le_valN P.labelVal hval (n := n' / d)
      have : 0 ≤ posn P.labelVal x n' := by linarith
      nlinarith
    · rintro ⟨h, -⟩
      exact Finset.mem_filter.mp h

/-- `regroupX0` over an arbitrary finite set `T` of levels. -/
theorem regroupX0T {X0 : ℝ} (hp2 : ∀ j, 2 ≤ P.p j) (hXm : 0 < X0m) (T : Finset ℕ) :
    ∑ n ∈ T, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n ≤
      ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  set F : ℕ → ℕ → ℝ := fun n d => aLev P H tw X0m x d / Vl P n
  have e1 : ∀ n ∈ T, (∑ d ∈ D0 P H X0m x X0 n, aLev P H tw X0m x d) / Vl P n =
      ∑ d ∈ D0 P H X0m x X0 n, F n d := fun n _ => by rw [Finset.sum_div]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := NAll P x X0m)
    (s' := fun d => T.filter (fun n => d ∈ D0 P H X0m x X0 n))]
  · refine Finset.sum_le_sum fun d hd => ?_
    have hVd := KR.valN_labelVal_pos P d
    set T' := (CofH P X0m (posn P.labelVal x d)).filter
      (fun m => |posn P.labelVal x d - Vl P m * X0m| ≤ 1.02 * H (posn P.labelVal x d))
    have hS : ∀ n ∈ T.filter (fun n => d ∈ D0 P H X0m x X0 n),
        F n d = aLev P H tw X0m x d / Vl P d * (1 / Vl P (n / d)) ∧ n / d ∈ T' ∧ d ∣ n := by
      intro n hn
      obtain ⟨-, hdD⟩ := Finset.mem_filter.mp hn
      unfold D0 at hdD
      obtain ⟨hdm, hXd, -, hpos⟩ := Finset.mem_filter.mp hdD
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hm2 := two_le_div_of_mem hdm
      have hVm := KR.valN_labelVal_pos P (n / d)
      have hpd : posn P.labelVal x d = posn P.labelVal x n * Vl P (n / d) := posn_mul hval hdn hn0
      have hVV : Vl P n = Vl P d * Vl P (n / d) := valN_div_mul hval hdn hn0
      refine ⟨?_, ?_, hdn⟩
      · simp only [F]; rw [hVV]; field_simp
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hm2⟩, ?_⟩
        · apply KR.mem_image_iota P (by omega)
          rw [le_div_iff₀ hXm, hpd]
          nlinarith
        · unfold X0Near at hXd
          rw [hpd]
          have e : posn P.labelVal x n * Vl P (n / d) - Vl P (n / d) * X0m =
              (posn P.labelVal x n - X0m) * Vl P (n / d) := by ring
          rw [e, abs_mul, abs_of_pos hVm, ← hpd]
          rw [le_div_iff₀ hVm] at hXd
          exact hXd
    calc ∑ n ∈ T.filter (fun n => d ∈ D0 P H X0m x X0 n), F n d
        = ∑ n ∈ T.filter (fun n => d ∈ D0 P H X0m x X0 n),
            aLev P H tw X0m x d / Vl P d * (1 / Vl P (n / d)) :=
          Finset.sum_congr rfl fun n hn => (hS n hn).1
      _ = ∑ m ∈ (T.filter (fun n => d ∈ D0 P H X0m x X0 n)).image (· / d),
            aLev P H tw X0m x d / Vl P d * (1 / Vl P m) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only at hab
          have ha' := (hS a ha).2.2
          have hb' := (hS b hb).2.2
          rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
      _ ≤ ∑ m ∈ T', aLev P H tw X0m x d / Vl P d * (1 / Vl P m) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
            exact (hS n hn).2.1
          · intro m _ _
            exact mul_nonneg (div_nonneg (aLev_nonneg d) hVd.le)
              (one_div_nonneg.mpr (KR.valN_labelVal_pos P m).le)
      _ = aLev P H tw X0m x d / Vl P d * etaX0 P H X0m (posn P.labelVal x d) := by
          rw [← Finset.mul_sum]; rfl
  · intro n d
    constructor
    · rintro ⟨hn, hd⟩
      refine ⟨Finset.mem_filter.mpr ⟨hn, hd⟩, ?_⟩
      unfold D0 at hd
      obtain ⟨hdm, -, -, hpos⟩ := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_properDivisors.mp hdm).1
      have hn0 : n ≠ 0 := by have := two_le_div_of_mem hdm; intro h; subst h; simp at this
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
      apply mem_NAll_of_posn hd0 hXm
      rw [posn_mul hval hdn hn0]
      have hw := two_le_valN hval2 (two_le_div_of_mem hdm)
      nlinarith
    · rintro ⟨h, -⟩
      exact Finset.mem_filter.mp h

/-- **The scalar fixed point**: if `A u ≤ a + b ∑_v A v s_v` for every `u ∈ Sc`, with
`A, s ≥ 0`, `a, b ≥ 0` and `b ∑_v s_v ≤ q < 1`, then `A u ≤ a/(1 - q)`. -/
theorem fixed_point_const (Sc : Finset ℝ) (A s : ℝ → ℝ) {a b q : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hq : q < 1) (hA : ∀ v ∈ Sc, 0 ≤ A v) (hs : ∀ v ∈ Sc, 0 ≤ s v)
    (hS : b * ∑ v ∈ Sc, s v ≤ q)
    (hrec : ∀ u ∈ Sc, A u ≤ a + b * ∑ v ∈ Sc, A v * s v) :
    ∀ u ∈ Sc, A u ≤ a / (1 - q) := by
  set S := ∑ v ∈ Sc, s v
  set B := ∑ v ∈ Sc, A v * s v
  have hS0 : 0 ≤ S := Finset.sum_nonneg hs
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun v hv => mul_nonneg (hA v hv) (hs v hv)
  have hB : B ≤ (a + b * B) * S := by
    calc B ≤ ∑ v ∈ Sc, (a + b * B) * s v :=
          Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hrec v hv) (hs v hv)
      _ = (a + b * B) * S := by rw [← Finset.mul_sum]
  have hq0 : 0 < 1 - q := by linarith
  have hbB : b * B ≤ q * a / (1 - q) := by
    -- `b B (1 - bS) ≤ a b S ≤ a q`
    have h1 : b * B * (1 - b * S) ≤ a * (b * S) := by nlinarith
    have h2 : b * B * (1 - q) ≤ b * B * (1 - b * S) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hb hB0)
    rw [le_div_iff₀ hq0]
    nlinarith
  intro u hu
  have := hrec u hu
  rw [le_div_iff₀ hq0]
  have e : a / (1 - q) * (1 - q) = a := by field_simp
  have h3 : q * a / (1 - q) * (1 - q) = q * a := by field_simp
  nlinarith

end KR

end
