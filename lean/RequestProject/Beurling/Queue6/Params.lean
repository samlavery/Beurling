module

public import RequestProject.Beurling.Queue6.Blocks
public import RequestProject.Beurling.Construction.YBounds
public import RequestProject.Beurling.Model.Width

/-!
# The parameters of §6.3 at a dyadic scale, and their sizes

At a scale `u ≥ X₀` (the dyadic scale of the slot start `s_j`), the proof of Theorem 6.6 uses
(the bound `B(s_j) = queueB X₀ u` of the Lean formalization being `queueBound75` at
`M̄₁(u)`, `L = log(2u + 12 log u + 2)`, `Λ = log X₀`):

* `Queue6.uq u = max(X₀, u/2)`: the dyadic block below `u` (the composites of a window of `𝓘_u`
  below `u` lie in `[u/2, u)`, whose threshold is `y(u/2)`, correction #79);
* `Queue6.Mq u = M̄₁(uq)` (`≤ M̄₁(u)`, so the bound at slot `j` is still at most `B(s_j)`);
  the cluster threshold and the truncation `2M₁` of Theorem 6.6 are taken at this level;
* `Queue6.Lq u = log(2u + 12 log u + 2)`, `Queue6.K0 u = ⌊48 M_q L_q³/c'²⌋`;
* `Queue6.Wlen u = 13 (K₀ + 1) log(3u) + 2`, the length bound of the windows of `𝓘_u`;
* `Queue6.yq u = y(uq)`, the absorption threshold of the block below.

Facts (`log X₀ ≥ 10⁸`, `u ≥ X₀`):
* `Lq_sq_le_Mq` : `L_q² ≤ M_q` (`M_q ≥ c ≥ e^{4ℓ²}/4`);
* `Wlen_le`, `len_div_yq_lt_one`, `len_div_yq_le`, `div_yq_le_Z` : the cofactor windows of
  Corollary 6.12 are shorter than `2 (log(b/y))^{-6}` and lie below the cluster horizon
  `4u/(log u)^{11}`.
-/

@[expose] public section

open Real CaplLink QueueBound QueueMono Absorbed AbsorbEmpty Construction

namespace Queue6

variable (X₀ : ℝ)

/-- The height of the block below `u`: `max(X₀, u/2)`. -/
noncomputable def uq (u : ℝ) : ℝ := max X₀ (u / 2)

/-- The cluster bound and truncation level at scale `u`: `M̄₁(max(X₀, u/2))`. -/
noncomputable def Mq (u : ℝ) : ℝ := capM1 X₀ (uq X₀ u)

/-- `L = log(2u + 12 log u + 2)`. -/
noncomputable def Lq (u : ℝ) : ℝ := Real.log (2 * u + 12 * Real.log u + 2)

/-- The integer block length at scale `u`. -/
noncomputable def K0 (u : ℝ) : ℕ := blockK (Mq X₀ u) (Lq u)

/-- The length bound of the windows of `𝓘_u`. -/
noncomputable def Wlen (u : ℝ) : ℝ := 13 * ((K0 X₀ u : ℝ) + 1) * Real.log (3 * u) + 2

/-- The absorption threshold of the block below `u`. -/
noncomputable def yq (u : ℝ) : ℝ := absorbYAt X₀ (uq X₀ u)

variable {X₀}

section Facts

variable (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu : X₀ ≤ u)
include hX0 hX hu

omit hX0 hX hu in
lemma uq_ge : X₀ ≤ uq X₀ u := le_max_left _ _

omit hX in
lemma uq_le : uq X₀ u ≤ u := max_le hu (by linarith)

omit hX0 hX hu in
lemma u_le_two_uq : u ≤ 2 * uq X₀ u := by unfold uq; have := le_max_right X₀ (u / 2); linarith

lemma Mq_le : Mq X₀ u ≤ capM1 X₀ u := capM1_mono hX0 hX uq_ge (uq_le hX0 hu)

lemma Mq_ge_one : 1 ≤ Mq X₀ u := QueueBound.one_le_capM1 hX0 hX uq_ge

lemma logu_ge : 10 ^ 8 ≤ Real.log u := (logs_of_ge hX0 hX hu).1

lemma u_pos : 0 < u := by have := one_lt_of_logX hX0 hX; linarith

omit hX0 hX hu in
/-- `t ≥ log t ^ 2 / 2`. -/
lemma sq_log_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 / 2 ≤ t := by
  have h := Real.pow_div_factorial_le_exp (Real.log t) (Real.log_nonneg ht) 2
  rw [Real.exp_log (by linarith)] at h; simpa [Nat.factorial] using h

omit hX0 hX hu in
lemma log3_le : Real.log 3 ≤ 1.4 := by
  have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_two_lt_d9
  linarith

/-- `2u + 12 log u + 2 ≤ 3u`. -/
lemma lin_le : 2 * u + 12 * Real.log u + 2 ≤ 3 * u := by
  have hu0 := u_pos hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have := sq_log_le (show (1 : ℝ) ≤ u by have := one_lt_of_logX hX0 hX; linarith)
  nlinarith

/-- `log u ≤ L_q ≤ log(3u) ≤ log u + 1.4`. -/
lemma Lq_bounds : Real.log u ≤ Lq u ∧ Lq u ≤ Real.log (3 * u) ∧
    Real.log (3 * u) ≤ Real.log u + 1.4 := by
  have hu0 := u_pos hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have hpos : 0 < 2 * u + 12 * Real.log u + 2 := by linarith
  refine ⟨Real.log_le_log hu0 (by linarith), Real.log_le_log hpos (lin_le hX0 hX hu), ?_⟩
  rw [Real.log_mul (by norm_num) hu0.ne']
  linarith [log3_le]

lemma loguq_ge : Real.log u - 0.7 ≤ Real.log (uq X₀ u) := by
  have hu0 := u_pos hX0 hX hu
  have h1 : u / 2 ≤ uq X₀ u := le_max_right _ _
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_div hu0.ne' (by norm_num)] at h2
  have := Real.log_two_lt_d9
  linarith

lemma loguq_big : 10 ^ 8 ≤ Real.log (uq X₀ u) := (logs_of_ge hX0 hX uq_ge).1

/-- `M_q ≥ c(uq) ≥ e^{4ℓ²}/4`. -/
lemma Mq_ge_exp : Real.exp (4 * Real.log (Real.log (uq X₀ u)) ^ 2 - Real.log 4) ≤ Mq X₀ u := by
  obtain ⟨-, -, h3, hell⟩ := height_facts hX0 hX (uq_ge (u := u))
  have hc := logcAt_ge hX0 hX (uq_ge (u := u))
  unfold Mq capM1 BSCert.Capl.Mbar1
  simp only
  have hr := BSCert.Capl.rbar0_nonneg (Λ := Real.log X₀) (s := capS X₀ (uq X₀ u))
    (by rw [hell]; linarith)
  set c := Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ (uq X₀ u)))
  have hc' : Real.exp (4 * Real.log (Real.log (uq X₀ u)) ^ 2 - Real.log 4) ≤ c :=
    Real.exp_le_exp.mpr hc
  have : 0 ≤ BSCert.Capl.rbar0 (Real.log X₀) (capS X₀ (uq X₀ u)) * Real.sqrt c := by positivity
  nlinarith

/-- **`L_q² ≤ M_q`** (used for the full blocks, inequality (76)). -/
theorem Lq_sq_le_Mq : Lq u ^ 2 ≤ Mq X₀ u := by
  obtain ⟨h1, h2, h3⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have hq := loguq_ge hX0 hX hu
  have hqb := loguq_big hX0 hX hu
  set L := Real.log (uq X₀ u)
  have hL0 : 0 < L := by linarith
  have hLq : Lq u ≤ 2 * L := by linarith
  have hℓ : 18 ≤ Real.log L := by
    have := BSCert.Capl.log_ge_18 (Λ := L) (by linarith); linarith
  -- `(2L)² = e^{2 log L + log 4} ≤ e^{4 (log L)² - log 4}`
  have he : (2 * L) ^ 2 = Real.exp (2 * Real.log L + Real.log 4) := by
    rw [Real.exp_add, show 2 * Real.log L = Real.log (L ^ 2) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), Real.exp_log (by norm_num)]
    ring
  have h4 := log4_bounds
  have hexp : Real.exp (2 * Real.log L + Real.log 4) ≤
      Real.exp (4 * Real.log L ^ 2 - Real.log 4) := Real.exp_le_exp.mpr (by nlinarith)
  have hLq0 : 0 ≤ Lq u := by linarith
  calc Lq u ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hLq0 hLq 2
    _ ≤ _ := by rw [he]; exact hexp.trans (Mq_ge_exp hX0 hX hu)

lemma K0_le : (K0 X₀ u : ℝ) ≤ 48 * Mq X₀ u * Lq u ^ 3 / 0.15 ^ 2 := by
  unfold K0 blockK
  have hM := Mq_ge_one hX0 hX hu
  have hL := (Lq_bounds hX0 hX hu).1
  have := logu_ge hX0 hX hu
  exact Nat.floor_le (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
    (pow_nonneg (by linarith) 3)) (by norm_num))

/-- `W_len ≤ 28000 M_q L_q⁴`. -/
lemma Wlen_le : Wlen X₀ u ≤ 28000 * Mq X₀ u * Lq u ^ 4 := by
  have hK := K0_le hX0 hX hu
  obtain ⟨h1, h2, h3⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have hM := Mq_ge_one hX0 hX hu
  set L := Lq u
  set M := Mq X₀ u
  have hL : 10 ^ 8 ≤ L := by linarith
  have hK' : (K0 X₀ u : ℝ) + 1 ≤ 2134 * M * L ^ 3 := by
    have hML : 0 ≤ M * L ^ 3 := mul_nonneg (by linarith) (pow_nonneg (by linarith) 3)
    have : 48 * M * L ^ 3 / 0.15 ^ 2 ≤ 2133.34 * M * L ^ 3 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have h2 : (1 : ℝ) ≤ 0.66 * M * L ^ 3 := by
      have h5 : (2 : ℝ) ≤ L ^ 3 := by
        have : (2 : ℝ) ≤ L := by linarith
        calc (2 : ℝ) ≤ L := this
          _ ≤ L ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      have h6 : L ^ 3 ≤ M * L ^ 3 := le_mul_of_one_le_left (by linarith) hM
      linarith
    have h3 := add_le_add (hK.trans this) h2
    have e : 2133.34 * M * L ^ 3 + 0.66 * M * L ^ 3 = 2134 * M * L ^ 3 := by ring
    linarith
  have hlog : Real.log (3 * u) ≤ 1.0001 * L := by nlinarith
  unfold Wlen
  have hK0 : 0 ≤ (K0 X₀ u : ℝ) + 1 := by positivity
  have hL3 : 0 ≤ L ^ 3 := by positivity
  calc 13 * ((K0 X₀ u : ℝ) + 1) * Real.log (3 * u) + 2
      ≤ 13 * (2134 * M * L ^ 3) * (1.0001 * L) + 2 := by
        have h0 : 0 ≤ Real.log (3 * u) := by linarith
        have := mul_le_mul hK' hlog h0 (by positivity)
        nlinarith
    _ ≤ 28000 * M * L ^ 4 := by
        have : (1 : ℝ) ≤ M * L ^ 4 := by
          have : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ (by linarith)
          nlinarith
        nlinarith

/-- `y_q ≥ 2000 H(uq) M_q L_q⁹`. -/
lemma yq_ge : 2000 * capH X₀ (uq X₀ u) * Mq X₀ u * Lq u ^ 9 ≤ yq X₀ u := by
  have hq := loguq_ge hX0 hX hu
  obtain ⟨h1, h2, h3⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have hH := BModel.capH_ge_one hX0 hX (uq_ge (u := u))
  have hM := Mq_ge_one hX0 hX hu
  set Lu := Real.log (uq X₀ u)
  set L := Lq u
  set M := Mq X₀ u
  set H := capH X₀ (uq X₀ u)
  have hLu : 0.99999 * L ≤ Lu := by nlinarith
  have hL0 : absorbL0 X₀ (uq X₀ u) ≥ 48 * M * Lu ^ 3 / 0.15 ^ 2 := le_max_right _ _
  unfold yq absorbYAt
  have hLu0 : 0 ≤ Lu := by linarith
  have h9 : (0.99999 * L) ^ 9 ≤ Lu ^ 9 := pow_le_pow_left₀ (by nlinarith) hLu 9
  have hHM : 0 ≤ H * M := mul_nonneg (by linarith) (by linarith)
  have hLu9 : 0 ≤ Lu ^ 9 := pow_nonneg hLu0 9
  have e1 : 2133 * H * M * Lu ^ 9 ≤ H * absorbL0 X₀ (uq X₀ u) * Lu ^ 6 := by
    have h48 : 2133 * M * Lu ^ 3 ≤ 48 * M * Lu ^ 3 / 0.15 ^ 2 := by
      rw [le_div_iff₀ (by norm_num)]
      have : 0 ≤ M * Lu ^ 3 := mul_nonneg (by linarith) (pow_nonneg hLu0 3)
      nlinarith
    have h2 := h48.trans hL0
    have hH0 : 0 ≤ H := by linarith
    have hL6 : 0 ≤ Lu ^ 6 := pow_nonneg hLu0 6
    calc 2133 * H * M * Lu ^ 9 = H * (2133 * M * Lu ^ 3) * Lu ^ 6 := by ring
      _ ≤ H * absorbL0 X₀ (uq X₀ u) * Lu ^ 6 := by
        apply mul_le_mul_of_nonneg_right _ hL6
        exact mul_le_mul_of_nonneg_left h2 hH0
  have e2 : 2000 * H * M * L ^ 9 ≤ 2133 * H * M * Lu ^ 9 := by
    have : (0.99999 * L) ^ 9 = 0.99999 ^ 9 * L ^ 9 := by ring
    rw [this] at h9
    have hL9 : 0 ≤ L ^ 9 := pow_nonneg (by linarith) 9
    have hc : (0.99999 : ℝ) ^ 9 ≥ 0.9999 := by norm_num
    have : 2000 * L ^ 9 ≤ 2133 * Lu ^ 9 := by nlinarith
    calc 2000 * H * M * L ^ 9 = (H * M) * (2000 * L ^ 9) := by ring
      _ ≤ (H * M) * (2133 * Lu ^ 9) := mul_le_mul_of_nonneg_left this hHM
      _ = 2133 * H * M * Lu ^ 9 := by ring
  linarith

omit hu in
lemma yq_ge_one : 1 ≤ yq X₀ u := one_le_absorbYAt hX0 hX uq_ge

lemma capH_uq_ge : 199 * Lq u ≤ capH X₀ (uq X₀ u) := by
  have := BModel.log_le_capH hX0 hX (uq_ge (u := u))
  have hq := loguq_ge hX0 hX hu
  obtain ⟨-, h2, h3⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  nlinarith

/-- **The cofactor windows of Corollary 6.12 are short**: for a window of length
`len ≤ W_len(u)`, `len / y_q ≤ 14/(199 L_q⁶)`. -/
lemma len_div_yq {len : ℝ} (hlen : len ≤ Wlen X₀ u) :
    len / yq X₀ u ≤ 14 / (199 * Lq u ^ 6) := by
  have hW := Wlen_le hX0 hX hu
  have hy := yq_ge hX0 hX hu
  have hH := capH_uq_ge hX0 hX hu
  have hM := Mq_ge_one hX0 hX hu
  obtain ⟨h1, -, -⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  set L := Lq u
  set M := Mq X₀ u
  set H := capH X₀ (uq X₀ u)
  have hL : 0 < L := by linarith
  have hy0 : 0 < yq X₀ u := by linarith [yq_ge_one (u := u) hX0 hX]
  rw [div_le_div_iff₀ hy0 (by positivity)]
  have h2 : 2000 * (199 * L) * M * L ^ 9 ≤ yq X₀ u := by
    have : 2000 * (199 * L) * M * L ^ 9 ≤ 2000 * H * M * L ^ 9 := by
      have : 0 ≤ M * L ^ 9 := by positivity
      nlinarith
    linarith
  have hlenM : len ≤ 28000 * M * L ^ 4 := hlen.trans hW
  have : len * (199 * L ^ 6) ≤ 28000 * M * L ^ 4 * (199 * L ^ 6) :=
    mul_le_mul_of_nonneg_right hlenM (by positivity)
  have e : 28000 * M * L ^ 4 * (199 * L ^ 6) = 14 * (2000 * (199 * L) * M * L ^ 9) := by ring
  nlinarith

lemma Lq_big : 10 ^ 8 ≤ Lq u := (logu_ge hX0 hX hu).trans (Lq_bounds hX0 hX hu).1

lemma yq_le_sqrt : yq X₀ u ≤ u ^ (1 / 2 : ℝ) :=
  (BModel.absorbYAt_le_sqrt hX0 hX uq_ge).trans
    (Real.rpow_le_rpow (by linarith [uq_ge (X₀ := X₀) (u := u)]) (uq_le hX0 hu) (by norm_num))

/-- `y_q ≥ 3·10⁵ L_q^{12}`. -/
lemma yq_ge_pow : 300000 * Lq u ^ 12 ≤ yq X₀ u := by
  have hy := yq_ge hX0 hX hu
  have hH := capH_uq_ge hX0 hX hu
  have hM := Lq_sq_le_Mq hX0 hX hu
  have hL := Lq_big hX0 hX hu
  set L := Lq u
  have h9 : 0 ≤ L ^ 9 := by positivity
  have : 300000 * L ^ 12 ≤ 2000 * capH X₀ (uq X₀ u) * Mq X₀ u * L ^ 9 := by
    have h1 : 300000 * L ^ 12 ≤ 2000 * (199 * L) * L ^ 2 * L ^ 9 := by
      have : L ^ 12 = L * L ^ 2 * L ^ 9 := by ring
      rw [this]
      have : 0 ≤ L * L ^ 2 * L ^ 9 := by positivity
      nlinarith
    have h2 : 2000 * (199 * L) * L ^ 2 * L ^ 9 ≤ 2000 * capH X₀ (uq X₀ u) * Mq X₀ u * L ^ 9 := by
      have hL2 : 0 ≤ L ^ 2 := by positivity
      have hHL : 0 ≤ 199 * L := by linarith
      have := mul_le_mul hH hM hL2 (by linarith)
      have := mul_le_mul_of_nonneg_right this h9
      nlinarith
    linarith
  linarith

/-- **The cofactor windows of Corollary 6.12** for a window of `𝓘_u`: `len/y_q < 1`,
`len/y_q ≤ 2 (log(b/y_q))^{-6}` and `b/y_q ≤ 4u/(log u)^{11}`. -/
theorem cofactor_facts {len b : ℝ} (hlen0 : 0 ≤ len) (hlen : len ≤ Wlen X₀ u) (hub : u ≤ b)
    (hb3 : b ≤ 3 * u) :
    len / yq X₀ u < 1 ∧ len / yq X₀ u ≤ 2 / Real.log (b / yq X₀ u) ^ 6 ∧
      b / yq X₀ u ≤ 4 * u / Real.log u ^ 11 := by
  have h1 := len_div_yq hX0 hX hu hlen
  have hL := Lq_big hX0 hX hu
  obtain ⟨hL1, hL2, hL3⟩ := Lq_bounds hX0 hX hu
  have hl := logu_ge hX0 hX hu
  have hu0 := u_pos hX0 hX hu
  have hy1 := yq_ge_one (u := u) hX0 hX
  have hy0 : 0 < yq X₀ u := by linarith
  have hysq := yq_le_sqrt hX0 hX hu
  have hyp := yq_ge_pow hX0 hX hu
  set L := Lq u
  set y := yq X₀ u
  have hu1 : 1 < u := by have := one_lt_of_logX hX0 hX; linarith
  have hL6 : 0 < L ^ 6 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine lt_of_le_of_lt h1 ?_
    rw [div_lt_one (by positivity)]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ L by linarith) (n := 6)]
  · -- `0 < log(b/y) ≤ L + 1.4`
    have hsq1 : 1 < u ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
    have hby : 1 < b / y := by
      rw [lt_div_iff₀ hy0]
      have : u ^ (1 / 2 : ℝ) < u := by
        have := Real.rpow_lt_rpow_of_exponent_lt hu1 (show (1 / 2 : ℝ) < 1 by norm_num)
        rwa [Real.rpow_one] at this
      nlinarith
    have hlb0 : 0 < Real.log (b / y) := Real.log_pos hby
    have hlb : Real.log (b / y) ≤ L + 1.4 := by
      have h' : Real.log (b / y) ≤ Real.log b := by
        rw [Real.log_div (by linarith) hy0.ne']
        have := Real.log_nonneg hy1; linarith
      have h'' : Real.log b ≤ Real.log (3 * u) := Real.log_le_log (by linarith) hb3
      linarith
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : Real.log (b / y) ^ 6 ≤ (L + 1.4) ^ 6 := pow_le_pow_left₀ hlb0.le hlb 6
    have hq : (L + 1.4) ^ 6 ≤ 2 * L ^ 6 := by
      have : L + 1.4 ≤ 1.1 * L := by linarith
      calc (L + 1.4) ^ 6 ≤ (1.1 * L) ^ 6 := pow_le_pow_left₀ (by linarith) this 6
        _ = 1.1 ^ 6 * L ^ 6 := by ring
        _ ≤ 2 * L ^ 6 := by nlinarith
    nlinarith
  · rw [div_le_div_iff₀ hy0 (by positivity)]
    have hlu : Real.log u ^ 11 ≤ L ^ 11 := pow_le_pow_left₀ (by linarith) hL1 11
    have : b * Real.log u ^ 11 ≤ 3 * u * L ^ 11 :=
      mul_le_mul hb3 hlu (by positivity) (by positivity)
    have h12 : 3 * u * L ^ 11 ≤ 4 * u * y := by
      have : 3 * L ^ 11 ≤ 4 * y := by
        have : L ^ 11 ≤ L ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
      nlinarith
    linarith

/-- `W_len(u) ≤ u/4`. -/
lemma Wlen_le_quarter : Wlen X₀ u ≤ u / 4 := by
  have hW := Wlen_le hX0 hX hu
  have hyq := yq_ge hX0 hX hu
  have hu1 : 1 < u := by have := one_lt_of_logX hX0 hX; linarith
  have hH := capH_uq_ge hX0 hX hu
  have hL := Lq_big hX0 hX hu
  have hM := Mq_ge_one hX0 hX hu
  have hysq := yq_le_sqrt hX0 hX hu
  have hu0 := u_pos hX0 hX hu
  set L := Lq u
  set M := Mq X₀ u
  -- `28000 M L⁴ ≤ y_q ≤ √u ≤ u/4`
  have h1 : 28000 * M * L ^ 4 ≤ yq X₀ u := by
    have h2 : 28000 * M * L ^ 4 ≤ 2000 * (199 * L) * M * L ^ 9 := by
      have : 0 ≤ M * L ^ 4 := by positivity
      have : L ^ 4 ≤ L ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    have h3 : 2000 * (199 * L) * M * L ^ 9 ≤ 2000 * capH X₀ (uq X₀ u) * M * L ^ 9 := by
      have : 0 ≤ M * L ^ 9 := by positivity
      nlinarith
    linarith
  have hsq : u ^ (1 / 2 : ℝ) ≤ u / 4 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    have : (16 : ℝ) ≤ u := by
      have h1 := sq_log_le (show (1 : ℝ) ≤ u by linarith)
      have h2 := logu_ge hX0 hX hu
      nlinarith
    nlinarith
  linarith


omit hX0 hX hu in
/-- `log(1 - δ) ≥ -2δ` for `0 ≤ δ ≤ 1/4`. -/
lemma log_one_sub_ge {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 4) : -(2 * δ) ≤ Real.log (1 - δ) := by
  have h3 : Real.exp (-(2 * δ)) ≤ 1 - δ := by
    have h4 : Real.exp (-(2 * δ)) ≤ 1 / (1 + 2 * δ) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp (2 * δ)])
    have h5 : 1 / (1 + 2 * δ) ≤ 1 - δ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have := Real.log_le_log (Real.exp_pos _) h3
  rwa [Real.log_exp] at this

omit hX0 hX hu in
lemma exp_neg_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (c : ℝ) (hc : 1 / 8 ≤ c) :
    Real.exp (-(c * Λ)) ≤ 1 / 100 := by
  have : Real.exp (-(c * Λ)) ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by nlinarith)
  have h5 : Real.exp (-5) ≤ 1 / 100 := by
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos 5) (by norm_num)]
    have he := Real.exp_one_gt_d9
    have e5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he.le 5
    nlinarith
  linarith

omit hX0 hX hu in
/-- `2δ(L + 1.4 + Λ) ≤ 1` for `δ = e^{-7Λ/8}`, `L ≤ e^{√Λ} + 3`. -/
lemma delta_small {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : L ≤ Real.exp (Real.sqrt Λ) + 3) :
    2 * Real.exp (-(7 / 8 * Λ)) * (L + 1.4 + Λ) ≤ 1 := by
  have hΛ0 : 0 < Λ := by linarith
  have hsq : Real.sqrt Λ ≤ Λ / 4 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hΛe : Λ ≤ Real.exp (Λ / 4) := by
    have := Real.pow_div_factorial_le_exp (Λ / 4) (by positivity) 2
    simp [Nat.factorial] at this
    nlinarith
  set δ := Real.exp (-(7 / 8 * Λ))
  have hδ0 : 0 < δ := Real.exp_pos _
  have h1 : δ * Real.exp (Real.sqrt Λ) ≤ Real.exp (-(5 / 8 * Λ)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h2 : δ * Λ ≤ Real.exp (-(5 / 8 * Λ)) := by
    calc δ * Λ ≤ δ * Real.exp (Λ / 4) := mul_le_mul_of_nonneg_left hΛe hδ0.le
      _ = Real.exp (-(5 / 8 * Λ)) := by rw [← Real.exp_add]; ring_nf
  have h3 := exp_neg_le hΛ (5 / 8) (by norm_num)
  have h4 : δ ≤ 1 / 100 := exp_neg_le hΛ (7 / 8) (by norm_num)
  have : δ * L ≤ δ * (Real.exp (Real.sqrt Λ) + 3) := mul_le_mul_of_nonneg_left hL hδ0.le
  nlinarith

/-- A jittered prime `q ≥ X₀ - X₀^{1/8}/2 - 1/8` has `log q ≥ Λ - 2 e^{-7Λ/8}`. -/
lemma log_q_ge {q : ℝ} (hq2 : X₀ - X₀ ^ (1 / 8 : ℝ) / 2 - 1 / 8 ≤ q) :
    Real.log X₀ - 2 * Real.exp (-(7 / 8 * Real.log X₀)) ≤ Real.log q := by
  have hX1 := one_lt_of_logX hX0 hX
  have hX0' : 0 < X₀ := by linarith
  have hX18 : X₀ ^ (1 / 8 : ℝ) = Real.exp (Real.log X₀ / 8) := by
    rw [Real.rpow_def_of_pos hX0']; ring_nf
  have hδX : X₀ * Real.exp (-(7 / 8 * Real.log X₀)) = Real.exp (Real.log X₀ / 8) := by
    nth_rewrite 1 [← Real.exp_log hX0']
    rw [← Real.exp_add]; ring_nf
  have hδ0 := Real.exp_pos (-(7 / 8 * Real.log X₀))
  have hδs : Real.exp (-(7 / 8 * Real.log X₀)) ≤ 1 / 4 := by
    have := exp_neg_le hX (7 / 8) (by norm_num); linarith
  have hqδ : X₀ * (1 - Real.exp (-(7 / 8 * Real.log X₀))) ≤ q := by
    have : X₀ ^ (1 / 8 : ℝ) / 2 + 1 / 8 ≤ X₀ * Real.exp (-(7 / 8 * Real.log X₀)) := by
      rw [hX18, hδX]
      have : (1 : ℝ) ≤ Real.exp (Real.log X₀ / 8) := Real.one_le_exp (by positivity)
      linarith
    nlinarith
  have h1 := Real.log_le_log (by nlinarith) hqδ
  rw [Real.log_mul hX0'.ne' (by linarith)] at h1
  have := log_one_sub_ge hδ0.le hδs
  linarith

/-- **`a_max ≤ L/Λ + 1`** (proof of Theorem 6.6(ii)): a jittered prime `q ≥ y_q` with
`q ≥ X₀ - X₀^{1/8}/2 - 1/8` (box-centred placement, `H(X₀) ≤ X₀^{1/8}`) and `q^n < 3u` has
`n ≤ L_q/Λ + 1`. -/
theorem amax_le {q : ℝ} (hq1 : yq X₀ u ≤ q)
    (hq2 : X₀ - X₀ ^ (1 / 8 : ℝ) / 2 - 1 / 8 ≤ q) {n : ℕ} (hn : q ^ n < 3 * u) :
    (n : ℝ) ≤ Lq u / Real.log X₀ + 1 := by
  have hu0 := u_pos hX0 hX hu
  have hL := Lq_big hX0 hX hu
  obtain ⟨hL1, hL2, hL3⟩ := Lq_bounds hX0 hX hu
  have hX1 := one_lt_of_logX hX0 hX
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hy1 := yq_ge_one (u := u) hX0 hX
  have hq0 : 1 ≤ q := hy1.trans hq1
  have hnl : (n : ℝ) * Real.log q < Lq u + 1.4 := by
    have : Real.log (q ^ n) < Real.log (3 * u) :=
      Real.log_lt_log (pow_pos (by linarith) n) hn
    rw [Real.log_pow] at this; linarith
  rw [div_add_one hΛ0.ne', le_div_iff₀ hΛ0]
  by_cases hyX : X₀ ≤ yq X₀ u
  · have hlq : Real.log X₀ ≤ Real.log q := Real.log_le_log (by linarith) (hyX.trans hq1)
    have := mul_le_mul_of_nonneg_left hlq (Nat.cast_nonneg n)
    linarith
  · push_neg at hyX
    have hlog := log_absorbYAt_ge hX0 hX (uq_ge (X₀ := X₀) (u := u))
    have hlogy : Real.log (yq X₀ u) < Real.log X₀ := Real.log_lt_log (by linarith) hyX
    have hq := loguq_ge hX0 hX hu
    have hLu : 10 ^ 8 ≤ Real.log (uq X₀ u) := loguq_big hX0 hX hu
    have hll : Real.log (Real.log (uq X₀ u)) < Real.sqrt (Real.log X₀) := by
      have h8 : 8 * Real.log (Real.log (uq X₀ u)) ^ 2 < Real.log X₀ := by
        unfold yq at hlogy; linarith
      have hl0 : 0 ≤ Real.log (Real.log (uq X₀ u)) := Real.log_nonneg (by linarith)
      rw [Real.lt_sqrt hl0]; nlinarith
    have hLu' : Real.log (uq X₀ u) < Real.exp (Real.sqrt (Real.log X₀)) := by
      rw [← Real.exp_log (by linarith : 0 < Real.log (uq X₀ u))]
      exact Real.exp_lt_exp.mpr hll
    have hlq := log_q_ge hX0 hX hu hq2
    have hδ := delta_small hX (L := Lq u) (by linarith)
    set δ := Real.exp (-(7 / 8 * Real.log X₀))
    have hδ0 : 0 < δ := Real.exp_pos _
    have hpos : 1 ≤ Real.log X₀ - 2 * δ := by
      have := exp_neg_le hX (7 / 8) (by norm_num); linarith
    have hn' : (n : ℝ) * (Real.log X₀ - 2 * δ) < Lq u + 1.4 := by
      have := mul_le_mul_of_nonneg_left hlq (Nat.cast_nonneg n); linarith
    have hnb : (n : ℝ) ≤ Lq u + 1.4 := by
      have : (n : ℝ) ≤ (n : ℝ) * (Real.log X₀ - 2 * δ) :=
        le_mul_of_one_le_right (Nat.cast_nonneg n) hpos
      linarith
    have h2 : (n : ℝ) * (2 * δ) ≤ (Lq u + 1.4) * (2 * δ) :=
      mul_le_mul_of_nonneg_right hnb (by positivity)
    nlinarith

omit hX0 hX hu in
lemma exp_neg_four_log {t : ℝ} (ht : 0 < t) : Real.exp (-(4 * Real.log t)) = 1 / t ^ 4 := by
  have h4 : 4 * Real.log t = Real.log (t ^ 4) := by rw [Real.log_pow]; push_cast; ring
  rw [Real.exp_neg, h4, Real.exp_log (by positivity)]; ring

/-- **The count of Theorem 6.6(i)**: `(W_len + 1)(2u + 1)(K₀ + 7) e^{-4L} ≤ u^{-2}`. -/
theorem count_numeric :
    (Wlen X₀ u + 1) * (2 * u + 1) * ((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * Lq u)) ≤
      1 / u ^ 2 := by
  have hu0 := u_pos hX0 hX hu
  have hu1 : 1 < u := by have := one_lt_of_logX hX0 hX; linarith
  have hW := Wlen_le hX0 hX hu
  have hK := K0_le hX0 hX hu
  have hM := Mq_ge_one hX0 hX hu
  have hL := Lq_big hX0 hX hu
  obtain ⟨hL1, -, -⟩ := Lq_bounds hX0 hX hu
  have hy := yq_ge hX0 hX hu
  have hysq := yq_le_sqrt hX0 hX hu
  have hHM : Mq X₀ u ^ 2 ≤ capH X₀ (uq X₀ u) := (capH_conditions hX0 hX uq_ge).1
  set L := Lq u
  set M := Mq X₀ u
  set H := capH X₀ (uq X₀ u)
  have hL0 : 0 < L := by linarith
  -- `e^{-4L} ≤ u^{-4}`
  have he : Real.exp (-(4 * L)) ≤ 1 / u ^ 4 := by
    have : Real.exp (-(4 * L)) ≤ Real.exp (-(4 * Real.log u)) := Real.exp_le_exp.mpr (by linarith)
    have e : Real.exp (-(4 * Real.log u)) = 1 / u ^ 4 := exp_neg_four_log hu0
    linarith
  -- the polynomial factor
  have hML4 : 1 ≤ M * L ^ 4 := by
    have : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hML3 : 1 ≤ M * L ^ 3 := by
    have : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have h1 : Wlen X₀ u + 1 ≤ 28001 * M * L ^ 4 := by linarith
  have h2 : (K0 X₀ u : ℝ) + 7 ≤ 2141 * M * L ^ 3 := by
    have : 48 * M * L ^ 3 / 0.15 ^ 2 ≤ 2134 * M * L ^ 3 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have h3 : 2 * u + 1 ≤ 3 * u := by linarith
  -- `M² L⁷ ≤ √u / 2000`
  have h4 : 2000 * M ^ 2 * L ^ 9 ≤ u ^ (1 / 2 : ℝ) := by
    have : 2000 * M ^ 2 * L ^ 9 ≤ 2000 * H * M * L ^ 9 := by
      have hL9 : 0 ≤ L ^ 9 := by positivity
      have : M ^ 2 ≤ H * M := by nlinarith
      nlinarith
    linarith
  have hsq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  have hs0 : 0 < u ^ (1 / 2 : ℝ) := by positivity
  have hs1 : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu1.le (by norm_num)
  have hpoly : (Wlen X₀ u + 1) * (2 * u + 1) * ((K0 X₀ u : ℝ) + 7) ≤ u ^ 2 := by
    have hW0 : 0 ≤ Wlen X₀ u + 1 := by
      unfold Wlen; have : (0 : ℝ) ≤ Real.log (3 * u) := Real.log_nonneg (by linarith)
      positivity
    have hK0 : 0 ≤ (K0 X₀ u : ℝ) + 7 := by positivity
    calc (Wlen X₀ u + 1) * (2 * u + 1) * ((K0 X₀ u : ℝ) + 7)
        ≤ (28001 * M * L ^ 4) * (3 * u) * (2141 * M * L ^ 3) := by
          apply mul_le_mul (mul_le_mul h1 h3 (by linarith) (by positivity)) h2 hK0
          positivity
      _ = 28001 * 2141 * 3 * (M ^ 2 * L ^ 7) * u := by ring
      _ ≤ 28001 * 2141 * 3 * (u ^ (1 / 2 : ℝ) / (2000 * L ^ 2)) * u := by
          apply mul_le_mul_of_nonneg_right _ hu0.le
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ u ^ (1 / 2 : ℝ) * u := by
          apply mul_le_mul_of_nonneg_right _ hu0.le
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          have : (10 ^ 16 : ℝ) ≤ L ^ 2 := by nlinarith
          nlinarith
      _ ≤ u * u := mul_le_mul_of_nonneg_right (by nlinarith) hu0.le
      _ = u ^ 2 := by ring
  calc (Wlen X₀ u + 1) * (2 * u + 1) * ((K0 X₀ u : ℝ) + 7) * Real.exp (-(4 * L))
      ≤ u ^ 2 * (1 / u ^ 4) := mul_le_mul hpoly he (Real.exp_pos _).le (by positivity)
    _ = 1 / u ^ 2 := by field_simp

/-- **The count of Lemma 6.1**: `(12 H(u) + 1)(6u + 3) · 2 e^{-4 log u} ≤ u^{-2}`. -/
theorem land_numeric :
    (12 * capH X₀ u + 1) * (6 * u + 3) * (2 * Real.exp (-(4 * Real.log u))) ≤ 1 / u ^ 2 := by
  have hu0 := u_pos hX0 hX hu
  have hu1 : 1 < u := by have := one_lt_of_logX hX0 hX; linarith
  have hH := InitialRange.capH_le_rpow hX0 hX hu
  have hH1 := BModel.capH_ge_one hX0 hX hu
  have e : Real.exp (-(4 * Real.log u)) = 1 / u ^ 4 := exp_neg_four_log hu0
  rw [e]
  have hr : u ^ (1 / 8 : ℝ) ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_le hu1.le (show (1 / 8 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h16 : (10 ^ 6 : ℝ) ≤ u := by
    have := sq_log_le (show (1 : ℝ) ≤ u by linarith)
    have := logu_ge hX0 hX hu
    nlinarith
  -- `H ≤ u^{1/8}` and `u^{1/8} ≤ u / 1000` are enough: use `H ≤ u^{1/2} ≤ u/1000`
  have hHs : capH X₀ u ≤ u / 1000 := by
    have h8 : u ^ (1 / 8 : ℝ) ≤ u ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
    have hsq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
      rw [← Real.rpow_add hu0]; norm_num
    have hs1 : (1000 : ℝ) ≤ u ^ (1 / 2 : ℝ) := by
      by_contra hc; push_neg at hc
      have : u < 1000 * 1000 := by
        have h0 : 0 ≤ u ^ (1 / 2 : ℝ) := by positivity
        nlinarith
      linarith
    nlinarith
  rw [show (12 * capH X₀ u + 1) * (6 * u + 3) * (2 * (1 / u ^ 4)) =
    2 * (12 * capH X₀ u + 1) * (6 * u + 3) / u ^ 4 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 2 * (12 * capH X₀ u + 1) * (6 * u + 3) ≤ u ^ 2 := by nlinarith
  nlinarith [pow_pos hu0 2]

end Facts

end Queue6

end
