module

public import RequestProject.Beurling.Noise.RML7XBJ
public import RequestProject.Beurling.Noise.RML8EEps
public import RequestProject.Beurling.Noise.BridgeSI
public import RequestProject.Beurling.Noise.KRHordMain
public import RequestProject.Beurling.Noise.RML6Var2Head
public import RequestProject.Beurling.Noise.KRNormHarm
public import RequestProject.Beurling.Noise.KRTrueX0Aux

/-!
# Proposition 5.31(iii) (the `X₀` band, huge range): definitions and the window

For a start `y` with `N = y/X₀` and `δ = H(X₀)/X₀`, every level `n` that carries mass in
`𝔅(y)` (`KR.xbB`) has `|y/n - X₀| ≤ 1.6 H(X₀)` (`Win`), hence `V(n) ∈ N[1 - a, 1 + a]` with
`a = 1.7δ` (`win_val`).

* `ShortRecip P Y` : **Lemma 5.29** (reciprocal sums over short intervals), the input of the
  short-interval counts: `∑_{e ∈ 𝒩 ∩ M[1-a,1+a]} 1/e ≤ 28a + 7M^{-3/4}` for `1 ≤ M ≤ Y/2`,
  `0 < a ≤ 0.01` (on `Good(<y)` with `Y = y`; a construction fact, owner: Queue6).
* `Dset` : the labels `2 ≤ e` with `V(e) ≤ 2y/X₀⁻` (all levels and all their divisors).
* `SD … a M = ∑_{e ∈ Dset, V(e) ∈ M[1-a,1+a]} |c_e(y)|/V(e)`, the density-weighted short sums.
* `sum_labels_le_SR` : the label form of Lemma 5.29.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

/-- **Lemma 5.29 (Reciprocal sums over short intervals)** for the system `P` up to the
height `Y` (on `Good(<y)`, `Y = y`; owner: the Queue6 agent, from Corollary 6.3). -/
def ShortRecip (P : BeurlingSystem) (Y : ℝ) : Prop :=
  ∀ M a : ℝ, 1 ≤ M → M ≤ Y / 2 → 0 < a → a ≤ 0.01 →
    ∑ e ∈ (P.elems (M * (1 + a))).filter (fun e => M * (1 - a) ≤ P.val e), 1 / P.val e ≤
      28 * a + 7 * M ^ (-(3 / 4 : ℝ))

/-- The labels `2 ≤ e` with `V(e) ≤ 2y/X₀⁻`. -/
noncomputable def Dset (P : BeurlingSystem) (X0m y : ℝ) : Finset ℕ :=
  ((P.elems (2 * y / X0m)).image iota).filter (2 ≤ ·)

open scoped Classical in
/-- `S(M) = ∑_{e ∈ Dset, V(e) ∈ M[1-a,1+a]} |c_e(y)|/V(e)`. -/
noncomputable def SD (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m y a M : ℝ) : ℝ :=
  ∑ e ∈ Dset P X0m y, if M * (1 - a) ≤ LemmaM.valN P.labelVal e ∧
      LemmaM.valN P.labelVal e ≤ M * (1 + a)
    then |cN P tw X0m y e| / LemmaM.valN P.labelVal e else 0

/-- The window of the levels of `𝔅`: `|y/n - X₀| ≤ 1.6 H(X₀)`. -/
def Win (P : BeurlingSystem) (H : ℝ → ℝ) (y X0 : ℝ) (n : ℕ) : Prop :=
  |posn P.labelVal y n - X0| ≤ 1.6 * H X0

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma mem_Dset {n : ℕ} : n ∈ Dset P X0m y ↔ n ∈ (P.elems (2 * y / X0m)).image iota ∧ 2 ≤ n :=
  Finset.mem_filter

lemma SD_nonneg (a M : ℝ) : 0 ≤ SD P tw X0m y a M := by
  classical
  unfold SD
  refine Finset.sum_nonneg fun e _ => ?_
  split_ifs
  · exact div_nonneg (abs_nonneg _) (KR.valN_labelVal_pos P e).le
  · exact le_rfl

/-- **Label form of Lemma 5.29**: for a finite set `T` of non-zero labels with values in
`M[1-a,1+a]`, `∑_{w ∈ T} 1/V(w) ≤ 28a + 7M^{-3/4}`. -/
lemma sum_labels_le_SR {Y : ℝ} (hSR : ShortRecip P Y) {M a : ℝ} (hM1 : 1 ≤ M)
    (hMY : M ≤ Y / 2) (ha0 : 0 < a) (ha : a ≤ 0.01) (T : Finset ℕ) (hT0 : ∀ w ∈ T, w ≠ 0)
    (hTw : ∀ w ∈ T, M * (1 - a) ≤ LemmaM.valN P.labelVal w ∧
      LemmaM.valN P.labelVal w ≤ M * (1 + a)) :
    ∑ w ∈ T, 1 / LemmaM.valN P.labelVal w ≤ 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) := by
  classical
  set E := (P.elems (M * (1 + a))).filter (fun e => M * (1 - a) ≤ P.val e)
  have hsub : T ⊆ E.image iota := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (KR.mem_image_iota P (hT0 w hw) (hTw w hw).2)
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    have := (hTw (iota e) hw).1
    rwa [P.valN_iota] at this
  calc ∑ w ∈ T, 1 / LemmaM.valN P.labelVal w
      ≤ ∑ w ∈ E.image iota, 1 / LemmaM.valN P.labelVal w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
          (one_div_pos.mpr (KR.valN_labelVal_pos P w)).le
    _ = ∑ e ∈ E, 1 / P.val e := by
        rw [Finset.sum_image (fun a _ b _ h => iota_injective h)]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [P.valN_iota]
    _ ≤ 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) := hSR M a hM1 hMY ha0 ha

/-- If `M(1+a) < 2`, there is no label `e ≥ 2` with `V(e) ≤ M(1+a)`. -/
lemma not_val_le_of_small (hp2 : ∀ j, 2 ≤ P.p j) {e : ℕ} (he : 2 ≤ e) {B : ℝ} (hB : B < 2) :
    ¬ LemmaM.valN P.labelVal e ≤ B := by
  have := two_le_valN (fun p _ => hp2 _) (val := P.labelVal) he
  intro h; linarith

/-- **The window in values**: `|y/n - X₀| ≤ 1.6 H(X₀)` with `δ = H(X₀)/X₀ ≤ 1/1000` gives
`V(n) ∈ (y/X₀)[1 - 1.7δ, 1 + 1.7δ]`. -/
lemma win_val {X0 : ℝ} (hX0 : 0 < X0) (hH0 : 0 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hy : 0 < y)
    {n : ℕ} (hw : Win P H y X0 n) :
    y / X0 * (1 - 1.7 * (H X0 / X0)) ≤ LemmaM.valN P.labelVal n ∧
      LemmaM.valN P.labelVal n ≤ y / X0 * (1 + 1.7 * (H X0 / X0)) := by
  set δ := H X0 / X0 with hδdef
  have hV := KR.valN_labelVal_pos P n
  have hδ0 : 0 ≤ δ := div_nonneg hH0 hX0.le
  unfold Win posn at hw
  rw [abs_le] at hw
  obtain ⟨h1, h2⟩ := hw
  have hH : H X0 = δ * X0 := by rw [hδdef]; field_simp
  rw [hH] at h1 h2
  set V := LemmaM.valN P.labelVal n
  -- `y/V ∈ X₀[1 - 1.6δ, 1 + 1.6δ]`
  have hlo : X0 * (1 - 1.6 * δ) ≤ y / V := by nlinarith
  have hhi : y / V ≤ X0 * (1 + 1.6 * δ) := by nlinarith
  have hpos : 0 < X0 * (1 - 1.6 * δ) := by nlinarith
  constructor
  · -- `V ≥ y/(X₀(1+1.6δ)) ≥ (y/X₀)(1-1.7δ)`
    have h3 : y ≤ X0 * (1 + 1.6 * δ) * V := by rwa [div_le_iff₀ hV] at hhi
    have h4 : y / X0 * (1 - 1.7 * δ) * (X0 * (1 + 1.6 * δ)) ≤ y := by
      have e : y / X0 * (1 - 1.7 * δ) * (X0 * (1 + 1.6 * δ)) =
          y * ((1 - 1.7 * δ) * (1 + 1.6 * δ)) := by field_simp
      rw [e]
      have : (1 - 1.7 * δ) * (1 + 1.6 * δ) ≤ 1 := by nlinarith
      nlinarith
    have hq : 0 < X0 * (1 + 1.6 * δ) := by positivity
    nlinarith
  · have h3 : X0 * (1 - 1.6 * δ) * V ≤ y := by rwa [le_div_iff₀ hV] at hlo
    have h4 : y ≤ y / X0 * (1 + 1.7 * δ) * (X0 * (1 - 1.6 * δ)) := by
      have e : y / X0 * (1 + 1.7 * δ) * (X0 * (1 - 1.6 * δ)) =
          y * ((1 + 1.7 * δ) * (1 - 1.6 * δ)) := by field_simp
      rw [e]
      have : 1 ≤ (1 + 1.7 * δ) * (1 - 1.6 * δ) := by nlinarith
      nlinarith
    nlinarith

end KR.RML9

end
