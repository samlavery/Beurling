module

public import RequestProject.Beurling.Noise.BridgeBR
public import RequestProject.Beurling.Noise.KRNormHarm
public import RequestProject.Beurling.Noise.BSL57Final

/-!
# Responses of the sharp resolvent (used in Proposition 5.35)

For a start `x`, the sharp resolvent is `((1 + K_pt)⁻¹ g)(x) = ∑_n c_n(x) g(x/n)/n`
(§5.5, first display; `KR.rhoSh`), with the coefficients `c_n(x)` of Lemma 5.5. Two bounds
on the response `(1 + K_pt)⁻¹ g` are used in the proof of Proposition 5.35, range (A):

* `G1.abs_rhoSh_le_harm` ("by Lemma M, `|c_n| ≤ 1` and `∑ |c_n|/n ≤ log x + B₁`, `B₁ = 1`"):
  `|(1 + K_pt)⁻¹ g (x)| ≤ (log(x/X₀⁻) + 1) M` if `|g| ≤ M` on `[X₀⁻, x]`;
* `G1.abs_rhoSh_le_dyadic` and `G1.log_mul_abs_rhoSh_le` ("by Corollary 5.9"): if `g = 0`
  below `X₀` and `|g| ≤ b_j` on the dyadic block `[2ʲX₀, 2^{j+1}X₀]`, then
  `log x · |(1 + K_pt)⁻¹ g (x)| ≤ C_S ∑_{j : 2ʲX₀ ≤ x} log(2^{j+1}X₀) b_j`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.G1

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- The sharp resolvent as a sum over the elements `e` with `x/e ≥ X₀⁻`. -/
lemma rhoSh_eq_elems (g : ℝ → ℝ) :
    rhoSh P tw X0m x g = ∑ e ∈ P.elems (x / X0m),
      cN P tw X0m x (iota e) * g (x / P.val e) / P.val e := by
  unfold rhoSh NAll
  rw [Finset.sum_image (fun a _ b _ hab => iota_injective hab)]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [posn, Vl, P.valN_iota]

lemma abs_cN_le_one (ht : ∀ r, r.Prime → 0 < tw r) (hX0 : 0 ≤ X0m) (hx : X0m ≤ x) (n : ℕ)
    (hn : 1 ≤ n) : |cN P tw X0m x n| ≤ 1 := by
  unfold cN
  rw [mass_eq_coeff]
  exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht (fun r _ => P.one_le_labelVal r)
    hX0 hx hn

/-- **Response bound through Lemma M**: `|∑_n c_n g(x/n)/n| ≤ (log(x/X₀⁻) + 1) M` if
`|g| ≤ M` on `[X₀⁻, x]` (with (HBS) on `[1, Z]`, `x/X₀⁻ ≤ Z`). -/
theorem abs_rhoSh_le_harm {X0m' Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m' Z η1 η2 ε1)
    (ht : ∀ r, r.Prime → 0 < tw r) (hX0 : 0 < X0m) (hx : X0m ≤ x) (hZ : x / X0m ≤ Z)
    {g : ℝ → ℝ} {M : ℝ} (hg : ∀ u, X0m ≤ u → u ≤ x → |g u| ≤ M) :
    |rhoSh P tw X0m x g| ≤ (Real.log (x / X0m) + 1) * M := by
  have hx0 : 0 < x := lt_of_lt_of_le hX0 hx
  have hX1 : 1 ≤ x / X0m := by rw [le_div_iff₀ hX0]; linarith
  have hM : 0 ≤ M := by
    have := hg x hx le_rfl; linarith [abs_nonneg (g x)]
  rw [rhoSh_eq_elems]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ e ∈ P.elems (x / X0m),
      |cN P tw X0m x (iota e) * g (x / P.val e) / P.val e| ≤ M * (1 / P.val e) := by
    intro e he
    rw [mem_elems] at he
    have hv := P.val_pos e
    have hu1 : X0m ≤ x / P.val e := by
      rw [le_div_iff₀ hv]; rw [le_div_iff₀ hX0] at he; linarith
    have hu2 : x / P.val e ≤ x := div_le_self hx0.le (P.one_le_val e)
    have hc := abs_cN_le_one (P := P) ht hX0.le hx (iota e) (iota_pos e)
    rw [abs_div, abs_mul, abs_of_pos hv, mul_one_div]
    apply div_le_div_of_nonneg_right _ hv.le
    calc |cN P tw X0m x (iota e)| * |g (x / P.val e)| ≤ 1 * M :=
          mul_le_mul hc (hg _ hu1 hu2) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right (h.harm_le hX1 hZ) hM

/-- Every `t ∈ [X₀, 2^J X₀)` lies in some dyadic block `[2ʲX₀, 2^{j+1}X₀)`, `j < J`. -/
lemma exists_block {X0 t : ℝ} (ht1 : X0 ≤ t) :
    ∀ J : ℕ, t < 2 ^ J * X0 → ∃ j < J, 2 ^ j * X0 ≤ t ∧ t < 2 * (2 ^ j * X0) := by
  intro J
  induction J with
  | zero => intro h; simp at h; linarith
  | succ J ih =>
    intro hJ
    by_cases hJt : t < 2 ^ J * X0
    · obtain ⟨j, hj, h⟩ := ih hJt
      exact ⟨j, by omega, h⟩
    · push_neg at hJt
      refine ⟨J, by omega, hJt, ?_⟩
      rw [pow_succ] at hJ; linarith

/-- **The dyadic response bound**: if `g = 0` below `X₀` and `|g| ≤ b_j` on
`[2ʲX₀, 2^{j+1}X₀]`, then `|∑_n c_n g(x/n)/n| ≤ ∑_{j<J} b_j W^sh_x(2ʲX₀)` for every `J` with
`x < 2^J X₀` (the weights of Corollary 5.9). -/
theorem abs_rhoSh_le_dyadic {X0 : ℝ} (hX0 : 0 < X0) (hX0m : 0 < X0m) (hx : X0m ≤ x)
    {g : ℝ → ℝ} (hg0 : ∀ u, u < X0 → g u = 0) {b : ℕ → ℝ} (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ j u, 2 ^ j * X0 ≤ u → u ≤ 2 * (2 ^ j * X0) → |g u| ≤ b j)
    {J : ℕ} (hJ : x < 2 ^ J * X0) :
    |rhoSh P tw X0m x g| ≤ ∑ j ∈ range J, b j * P.Wsh tw X0m x (2 ^ j * X0) := by
  classical
  have hx0 : 0 < x := lt_of_lt_of_le hX0m hx
  set E := P.elems (x / X0m)
  set f : (ℕ →₀ ℕ) → ℝ := fun e =>
    |cN P tw X0m x (iota e)| * |g (x / P.val e)| / P.val e
  set S : ℕ → Finset (ℕ →₀ ℕ) := fun j =>
    E.filter (fun e => 2 ^ j * X0 ≤ x / P.val e ∧ x / P.val e < 2 * (2 ^ j * X0))
  have hf0 : ∀ e, 0 ≤ f e := fun e => div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (P.val_pos e).le
  -- each nonzero term lies in some block
  have hcover : ∀ e ∈ E, f e ≤ ∑ j ∈ range J, if e ∈ S j then f e else 0 := by
    intro e he
    by_cases hlow : x / P.val e < X0
    · have : f e = 0 := by simp only [f, hg0 _ hlow, abs_zero, mul_zero, zero_div]
      rw [this]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp
    · push_neg at hlow
      have hlt : x / P.val e < 2 ^ J * X0 :=
        lt_of_le_of_lt (div_le_self hx0.le (P.one_le_val e)) hJ
      obtain ⟨j, hj, h1, h2⟩ := exists_block hlow J hlt
      have hmem : e ∈ S j := Finset.mem_filter.mpr ⟨he, h1, h2⟩
      have := Finset.single_le_sum (f := fun j => if e ∈ S j then f e else 0)
        (fun j _ => by dsimp only; split_ifs <;> simp [hf0 e]) (Finset.mem_range.mpr hj)
      simpa [hmem] using this
  rw [rhoSh_eq_elems]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have habs : ∀ e ∈ E, |cN P tw X0m x (iota e) * g (x / P.val e) / P.val e| = f e := by
    intro e _
    rw [abs_div, abs_mul, abs_of_pos (P.val_pos e)]
  rw [Finset.sum_congr rfl habs]
  refine (Finset.sum_le_sum hcover).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_filter]
  -- the block `j`
  set v := 2 ^ j * X0
  have hv : 0 < v := by positivity
  have hblock : ∀ e ∈ S j, f e ≤ b j * (|((LemmaM.coeff tw P.labelVal X0m x (iota e) : ℤ) : ℝ)| /
      P.val e) := by
    intro e he
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp he
    have hgb := hb j _ h1 h2.le
    simp only [f]
    have hc : cN P tw X0m x (iota e) = (LemmaM.coeff tw P.labelVal X0m x (iota e) : ℝ) :=
      mass_eq_coeff _ _ _ _ _
    rw [hc, mul_div_assoc', mul_comm (b j)]
    apply div_le_div_of_nonneg_right _ (P.val_pos e).le
    exact mul_le_mul_of_nonneg_left hgb (abs_nonneg _)
  rw [show E.filter (fun a => a ∈ S j) = S j from
    Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))]
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hb0 j)
  unfold Wsh
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_, h1, h2⟩
    rw [mem_elems]
    have hve := P.val_pos e
    rw [le_div_iff₀ hve] at h1
    rw [le_div_iff₀ hv]; linarith
  · intro e _ _
    exact div_nonneg (abs_nonneg _) (P.val_pos e).le

/-- **The response bound through Corollary 5.9**: under (HBS) with `log X₀⁻ ≥ 10⁸`, if `g = 0`
below `X₀` (`X₀⁻ ≤ X₀`) and `|g| ≤ b_j` on `[2ʲX₀, 2^{j+1}X₀]`, then
`log x · |∑_n c_n g(x/n)/n| ≤ C_S ∑_{j<J, 2ʲX₀ ≤ x} log(2^{j+1}X₀) b_j`. -/
theorem log_mul_abs_rhoSh_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) {X0 : ℝ} (hX0m : X0m ≤ X0)
    (hx : X0m ≤ x) (hZ : 2 * x / X0m ≤ Z)
    {g : ℝ → ℝ} (hg0 : ∀ u, u < X0 → g u = 0) {b : ℕ → ℝ} (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ j u, 2 ^ j * X0 ≤ u → u ≤ 2 * (2 ^ j * X0) → |g u| ≤ b j)
    {J : ℕ} (hJ : x < 2 ^ J * X0) :
    Real.log x * |rhoSh P tw X0m x g| ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 *
        ∑ j ∈ (range J).filter (fun j => 2 ^ j * X0 ≤ x),
          Real.log (2 * (2 ^ j * X0)) * b j := by
  classical
  have hX := h.X0m_pos
  have hX0 : 0 < X0 := lt_of_lt_of_le hX hX0m
  have hx0 : 0 < x := lt_of_lt_of_le hX hx
  have hlx : 100000000 ≤ Real.log x := hXm.trans (Real.log_le_log hX hx)
  have hlx0 : 0 < Real.log x := by linarith
  set CS := max (2.01 * BSaias.PhiInf 100000000) 1.4
  have hCS : 0 ≤ CS := le_trans (by norm_num) (le_max_right _ _)
  have hd := abs_rhoSh_le_dyadic (P := P) (tw := tw) hX0 hX hx hg0 hb0 hb hJ
  have hW : ∀ j ∈ range J, b j * P.Wsh tw X0m x (2 ^ j * X0) ≤
      if 2 ^ j * X0 ≤ x then b j * (CS * Real.log (2 * (2 ^ j * X0)) / Real.log x) else 0 := by
    intro j _
    split_ifs with hjx
    · apply mul_le_mul_of_nonneg_left _ (hb0 j)
      have h2 : X0m / 2 ≤ 2 ^ j * X0 := by
        have : X0 ≤ 2 ^ j * X0 := le_mul_of_one_le_left hX0.le (one_le_pow₀ (by norm_num))
        linarith
      exact P.cor_5_9_full h hXm ht htv hx h2 hjx hZ
    · -- the block is empty
      push_neg at hjx
      have : P.Wsh tw X0m x (2 ^ j * X0) = 0 := by
        unfold Wsh
        apply Finset.sum_eq_zero
        intro e he
        obtain ⟨-, h1, -⟩ := Finset.mem_filter.mp he
        have : x / P.val e ≤ x := div_le_self hx0.le (P.one_le_val e)
        linarith
      rw [this, mul_zero]
  have hsum := hd.trans (Finset.sum_le_sum hW)
  rw [← Finset.sum_filter] at hsum
  calc Real.log x * |rhoSh P tw X0m x g|
      ≤ Real.log x * ∑ j ∈ (range J).filter (fun j => 2 ^ j * X0 ≤ x),
          b j * (CS * Real.log (2 * (2 ^ j * X0)) / Real.log x) :=
        mul_le_mul_of_nonneg_left hsum hlx0.le
    _ = CS * ∑ j ∈ (range J).filter (fun j => 2 ^ j * X0 ≤ x),
          Real.log (2 * (2 ^ j * X0)) * b j := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp

end KR.G1

end
