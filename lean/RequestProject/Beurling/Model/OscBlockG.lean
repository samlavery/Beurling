module

public import RequestProject.Beurling.Model.OscBound
public import RequestProject.Beurling.Noise.RML8GField

/-!
# The block oscillation `o_v` of the second bullet of Lemma 5.34, and its sizes

For the block bound `|(1 - B)F_c| ≤ o_j + 2(F̄_{j-1} + F̄_j + F̄_{j+1})` on the dyadic blocks
`[v_j, 2v_j)`, `v_j = X₀⁻ 2ʲ` (04f-bridge.tex, `lem:predictable`, correction #110), the part
`o_j` is the oscillation of `T_c` over the windows `[s - H(s)/2, s + H(s)/2]`, `s ∈ [v_j, 2v_j)`.

* `obG X₀ j := Bsc X₀ v_j` (the three parts of the proof of eq. (osc): rigid, `R'`, `𝒜`);
* `oscG_le` : `|T_c(r) - T_c(s)| ≤ obG X₀ j` on `Good(< t)`, for `s ≤ (x + H(x)/2)/2`, `x ≤ b`;
* `sum_oscG_le` : `∑_j (log 3v_j)² obG X₀ j ≤ e^{-41}` (eq. (osc), second display);
* `sum_sixH_le` : `∑_j (log 3v_j)² · 6/H(v_j) ≤ 5·10⁻²³` (the `6/H` part of `F̄_r`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP Absorbed
  AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (X₀) in
/-- **The block oscillation bound** `o_j` at `v_j = X₀⁻ 2ʲ`. -/
noncomputable def obG (j : ℕ) : ℝ := Bsc X₀ (Xm X₀ * 2 ^ j)

/-! ### Telescoping -/

/-- `∑_{i<n} f_i ≤ C φ₀` if `f_i ≤ C(φ_i - φ_{i+1})`, `φ ≥ 0`. -/
lemma tele_le {f φ : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ i, 0 ≤ φ i)
    (hT : ∀ i, f i ≤ C * (φ i - φ (i + 1))) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i ≤ C * φ 0 := by
  calc ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, C * (φ i - φ (i + 1)) :=
        Finset.sum_le_sum fun i _ => hT i
    _ = C * (φ 0 - φ n) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ C * φ 0 := mul_le_mul_of_nonneg_left (by linarith [hφ n]) hC

/-- `ψ(ℓ) = max(ℓ, M)⁻¹`. -/
noncomputable def psi1 (M ℓ : ℝ) : ℝ := (max ℓ M)⁻¹

lemma psi1_anti {M : ℝ} (hM : 0 < M) {a c : ℝ} (hac : a ≤ c) : psi1 M c ≤ psi1 M a := by
  unfold psi1
  exact inv_anti₀ (lt_of_lt_of_le hM (le_max_right _ _)) (max_le_max hac le_rfl)

lemma psi1_nonneg {M : ℝ} (hM : 0 < M) (ℓ : ℝ) : 0 ≤ psi1 M ℓ := by
  unfold psi1; exact inv_nonneg.mpr (hM.le.trans (le_max_right _ _))

/-- `δ/ℓ² ≤ ψ(ℓ - δ) - ψ(ℓ)` when `ℓ - δ ≥ M`. -/
lemma psi1_gap {M ℓ δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) (h : M ≤ ℓ - δ) :
    δ / ℓ ^ 2 ≤ psi1 M (ℓ - δ) - psi1 M ℓ := by
  unfold psi1
  rw [max_eq_left h, max_eq_left (by linarith)]
  have h1 : 0 < ℓ - δ := by linarith
  have h2 : 0 < ℓ := by linarith
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ h1.ne' h2.ne',
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h1 h2, mul_pos hδ h2]

/-! ### The block bound -/

section Pair

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- The pair bound by `B(u)` (as in `oscR_le_Bsc`): for `X₀ ≤ s ≤ v`, `u/2 ≤ s`, `v ≤ 4u`,
`v ≤ 2(b + H(b))`, `v - s ≤ 2.04 H(2u)`. -/
lemma Tc_pair_le_Bsc {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {u : ℝ} (hu4 : (X₀ : ℝ) ≤ 4 * u) {s v : ℝ} (hs : (X₀ : ℝ) ≤ s) (hsv : s ≤ v)
    (hs2 : u / 2 ≤ s) (hv4 : v ≤ 4 * u) (hvb : v ≤ 2 * (b + Queue6.Hc X₀ b))
    (hvs : v - s ≤ 2.04 * Queue6.Hc X₀ (2 * u)) :
    |TcR θ X₀ ω (jzX X₀) s - TcR θ X₀ ω (jzX X₀) v| ≤ Bsc X₀ u := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hu0 : 0 < u := by linarith
  have hκ := (kappa_facts hX).1
  set H := Queue6.Hc X₀ with hHdef
  have hP := Tc_pair_le hc hev hb hbt hQC hE1 hN hT hs hsv hvb
  refine hP.trans ?_
  unfold Bsc
  have hs0 : 0 < s := by linarith
  have hW0 : 0 ≤ 2.04 * H (2 * u) := by linarith [KR.WidthReal.Hc_pos hX (X₀ := X₀) (2 * u)]
  have t1 : (5 * (v - s) + 3) / (kappaParam X₀ * s) ≤
      (10 * (2.04 * H (2 * u)) + 6) / (kappaParam X₀ * u) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hks : kappaParam X₀ * u / 2 ≤ kappaParam X₀ * s := by
      have := mul_le_mul_of_nonneg_left hs2 hκ.le; linarith
    have e1 : (5 * (v - s) + 3) * (kappaParam X₀ * u) ≤
        (5 * (2.04 * H (2 * u)) + 3) * (kappaParam X₀ * u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 := mul_le_mul_of_nonneg_left hks (show 0 ≤ 10 * (2.04 * H (2 * u)) + 6 by linarith)
    nlinarith
  have t2 : (v - s) * s ^ (-(1 / 20 : ℝ)) ≤ 2.04 * H (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) :=
    mul_le_mul hvs (Real.rpow_le_rpow_of_nonpos (by linarith) hs2 (by norm_num))
      (Real.rpow_nonneg hs0.le _) hW0
  have t3 : (if Lstar X₀ < Real.log v then (Real.log s ^ 4)⁻¹ else 0) ≤
      (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0) := by
    split_ifs with h1 h2
    · have hl : 0 < Real.log (u / 2) := Real.log_pos (by
        have := X₀_ge_two_pow hX; linarith)
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hl.le
        (Real.log_le_log (by linarith) hs2) 4)
    · exact absurd (lt_of_lt_of_le h1 (Real.log_le_log (by linarith) hv4)) h2
    · exact inv_nonneg.mpr (by positivity)
    · exact le_rfl
  linarith

set_option maxHeartbeats 2000000 in
/-- **The block oscillation of `T_c`** (the `o_v` of `lem:predictable`, 04f-bridge.tex; the
three parts of the proof of eq. (osc)): on `Good(< t)`, for `X₀^{1.01} ≤ x ≤ b`,
`s ∈ [v_j, 2v_j)` with `s ≤ (x + H(x)/2)/2` and `|r - s| ≤ H(s)/2`,
`|T_c(r) - T_c(s)| ≤ obG X₀ j`. -/
theorem oscG_le {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {x : ℝ} (hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x) (hxb : x ≤ b) (j : ℕ) {s r : ℝ}
    (hs1 : Xm X₀ * 2 ^ j ≤ s) (hs2 : s < 2 * (Xm X₀ * 2 ^ j))
    (hsx : s ≤ (x + Queue6.Hc X₀ x / 2) / 2) (hr : |r - s| ≤ Queue6.Hc X₀ s / 2) :
    |TcR θ X₀ ω (jzX X₀) r - TcR θ X₀ ω (jzX X₀) s| ≤ obG X₀ j := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  set u := Xm X₀ * 2 ^ j with hu
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hu1 : Xm X₀ ≤ u := by
    rw [hu]; have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hu4 : (X₀ : ℝ) ≤ 4 * u := by linarith
  have hu0 : 0 < u := by linarith
  set H := Queue6.Hc X₀ with hHdef
  have hH2u : H (2 * u) ≤ u / 10 := by
    simp only [hHdef]; unfold Queue6.Hc
    have h1 := KR.WidthReal.capH_le_tenth hX (le_max_right (2 * u) (X₀ : ℝ))
    have h2 : max (2 * u) (X₀ : ℝ) ≤ 4 * u := max_le (by linarith) hu4
    linarith
  have hHs : H s ≤ H (2 * u) := KR.WidthReal.Hc_mono hX hs2.le
  have hHs0 : 0 ≤ H s := (KR.WidthReal.Hc_pos hX s).le
  have hHb : 0 ≤ H b := (KR.WidthReal.Hc_pos hX b).le
  have hxX : (X₀ : ℝ) ≤ x := le_trans (Real.self_le_rpow_of_one_le hX1'.le (by norm_num)) hx
  have hHx : H x ≤ x / 40 := by
    simp only [hHdef]; unfold Queue6.Hc; rw [max_eq_left hxX]
    exact KR.WidthReal.capH_le_tenth hX hxX
  have hr' := abs_le.mp hr
  rw [TcR_eq_max hc ω r, TcR_eq_max hc ω s]
  set a := max r (X₀ : ℝ)
  set c := max s (X₀ : ℝ)
  have hac : |a - c| ≤ 2.04 * H (2 * u) := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    linarith [abs_le.mpr hr']
  have ha1 : u / 2 ≤ a := le_trans (by linarith) (le_max_left r (X₀ : ℝ))
  have hc1 : u / 2 ≤ c := le_trans (by linarith) (le_max_left s (X₀ : ℝ))
  have ha2 : a ≤ 4 * u := max_le (by linarith) hu4
  have hc2 : c ≤ 4 * u := max_le (by linarith) hu4
  have ha3 : a ≤ 2 * (b + H b) := max_le (by linarith) (by linarith)
  have hc3 : c ≤ 2 * (b + H b) := max_le (by linarith) (by linarith)
  have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hcX : (X₀ : ℝ) ≤ c := le_max_right _ _
  unfold obG
  rcases le_total a c with h | h
  · exact Tc_pair_le_Bsc hc hev hb hbt hQC hE1 hN hT hu4 haX h ha1 hc2 hc3
      (by linarith [(abs_le.mp hac).1])
  · rw [abs_sub_comm]
    exact Tc_pair_le_Bsc hc hev hb hbt hQC hE1 hN hT hu4 hcX h hc1 ha2 ha3
      (by linarith [(abs_le.mp hac).2])

end Pair

/-! ### The sizes -/

/-- `2^{-1/50} ≤ 72/73`. -/
lemma two_rpow_neg_twentieth_le : (2 : ℝ) ^ (-(1 / 50 : ℝ)) ≤ 72 / 73 := by
  have h : (73 / 72 : ℝ) ≤ (2 : ℝ) ^ (1 / 50 : ℝ) := by
    have h1 : ((73 / 72 : ℝ) ^ (50 : ℕ)) ≤ 2 := by norm_num
    have h2 := Real.rpow_le_rpow (by norm_num) h1 (show (0 : ℝ) ≤ 1 / 50 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), show ((50 : ℕ) : ℝ) * (1 / 50) = 1
      by norm_num, Real.rpow_one] at h2
  rw [Real.rpow_neg (by norm_num)]
  calc ((2 : ℝ) ^ (1 / 50 : ℝ))⁻¹ ≤ (73 / 72 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 72 / 73 := by norm_num

/-- `∑_{k<N} (c 2ᵏ)^{-1/50} ≤ 73 c^{-1/50}`. -/
lemma sum_geom_twentieth {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ k ∈ Finset.range N, (c * 2 ^ k) ^ (-(1 / 50 : ℝ)) ≤ 73 * c ^ (-(1 / 50 : ℝ)) := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 50 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 := two_rpow_neg_twentieth_le
  have e : ∀ k : ℕ, (c * 2 ^ k) ^ (-(1 / 50 : ℝ)) = c ^ (-(1 / 50 : ℝ)) * r ^ k := by
    intro k
    rw [Real.mul_rpow hc.le (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ), mul_comm]
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hc0 : 0 ≤ c ^ (-(1 / 50 : ℝ)) := Real.rpow_nonneg hc.le _
  have hgs : ∑ k ∈ Finset.range N, r ^ k ≤ 73 := by
    have hr1' : r < 1 := by linarith
    rw [geom_sum_eq (show r ≠ 1 by linarith) N, div_le_iff_of_neg (by linarith)]
    have : 0 ≤ r ^ N := pow_nonneg hr0 N
    nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- `(log 3u)² (B(u) - 𝒜-part) ≤ u^{-1/50}` for `u ≥ X₀/4`. -/
lemma nonA3_le (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu4 : (X₀ : ℝ) ≤ 4 * u) :
    Real.log (3 * u) ^ 2 * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) +
      2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ))) ≤ u ^ (-(1 / 50 : ℝ)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hu0 : 0 < u := by linarith
  set NA := (10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) +
      2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) with hNA
  have hκ := (kappa_facts hX).1
  have hH0 := (KR.WidthReal.Hc_pos hX (X₀ := X₀) (2 * u)).le
  have hNA0 : 0 ≤ NA := by
    have : 0 ≤ (u / 2) ^ (-(1 / 20 : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  have h1 := nonA_le hX hu4
  rw [← hNA] at h1
  -- logs
  have hlu : Real.log X₀ - 2 ≤ Real.log u := by
    have h1 : Real.log X₀ ≤ Real.log (4 * u) := Real.log_le_log (by linarith) hu4
    rw [Real.log_mul (by norm_num) hu0.ne'] at h1
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have h2u : 1 ≤ Real.log (2 * u) := by
    rw [Real.log_mul (by norm_num) hu0.ne']; linarith [Real.log_two_gt_d9]
  have h3u : Real.log (3 * u) ≤ 2 * Real.log (2 * u) := by
    have : Real.log (3 * u) = Real.log (2 * u) + Real.log 1.5 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
    have : Real.log 1.5 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.5 by norm_num); linarith
    linarith
  have h3u0 : 0 ≤ Real.log (3 * u) := Real.log_nonneg (by linarith)
  have step1 : Real.log (3 * u) ^ 2 * NA ≤ 2 * Real.log (3 * u) * u ^ (-(1 / 40 : ℝ)) := by
    have : Real.log (3 * u) ^ 2 * NA ≤ Real.log (3 * u) * (2 * Real.log (2 * u)) * NA := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3u h3u0) hNA0
    have h4 : Real.log (2 * u) * NA ≤ u ^ (-(1 / 40 : ℝ)) := h1
    nlinarith
  -- `log(3u) ≤ 800 u^{1/400}`
  have hlog : Real.log (3 * u) ≤ 800 * u ^ (1 / 400 : ℝ) := by
    have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 3 * u by positivity)
      (show (0 : ℝ) < 1 / 400 by norm_num)
    rw [Real.mul_rpow (by norm_num) hu0.le] at h
    have : (3 : ℝ) ^ (1 / 400 : ℝ) ≤ 2 := by
      calc (3 : ℝ) ^ (1 / 400 : ℝ) ≤ (4 : ℝ) ^ (1 / 400 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    have hp : 0 ≤ u ^ (1 / 400 : ℝ) := Real.rpow_nonneg hu0.le _
    have : (3 : ℝ) ^ (1 / 400 : ℝ) * u ^ (1 / 400 : ℝ) / (1 / 400) ≤ 800 * u ^ (1 / 400 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- `u^{1/400} ≥ 1600`
  have hbig : (1600 : ℝ) ≤ u ^ (1 / 400 : ℝ) := by
    rw [Real.rpow_def_of_pos hu0]
    have := Real.add_one_le_exp (Real.log u * (1 / 400))
    nlinarith
  have hpos : 0 < u ^ (1 / 400 : ℝ) := Real.rpow_pos_of_pos hu0 _
  have e1 : u ^ (-(1 / 40 : ℝ)) = u ^ (-(1 / 50 : ℝ)) * (u ^ (1 / 400 : ℝ))⁻¹ *
      (u ^ (1 / 400 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hu0.le, mul_assoc, ← Real.rpow_add hu0, ← Real.rpow_add hu0]
    norm_num
  have hq0 : 0 ≤ u ^ (-(1 / 50 : ℝ)) := Real.rpow_nonneg hu0.le _
  calc Real.log (3 * u) ^ 2 * NA ≤ 2 * Real.log (3 * u) * u ^ (-(1 / 40 : ℝ)) := step1
    _ ≤ 2 * (800 * u ^ (1 / 400 : ℝ)) * u ^ (-(1 / 40 : ℝ)) := by
        have : 0 ≤ u ^ (-(1 / 40 : ℝ)) := Real.rpow_nonneg hu0.le _
        nlinarith
    _ = 1600 * (u ^ (1 / 400 : ℝ))⁻¹ * u ^ (-(1 / 50 : ℝ)) := by
        rw [e1]; field_simp; norm_num
    _ ≤ 1 * u ^ (-(1 / 50 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hq0
        rw [← div_eq_mul_inv, div_le_one hpos]; exact hbig
    _ = u ^ (-(1 / 50 : ℝ)) := one_mul _

/-- `X₀⁻^{-1/50} ≤ 10⁻⁴³`. -/
lemma Xm_rpow_le (hX : 10 ^ 8 ≤ Real.log X₀) : Xm X₀ ^ (-(1 / 50 : ℝ)) ≤ 1 / 10 ^ 43 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hc0 : 0 < Xm X₀ := by linarith
  have hl : 10 ^ 8 - 1 ≤ Real.log (Xm X₀) := by
    have h1 : Real.log ((X₀ : ℝ) / 2) ≤ Real.log (Xm X₀) := Real.log_le_log (by linarith) hXm
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [Real.log_two_lt_d9]
  rw [Real.rpow_def_of_pos hc0]
  have h100 : (10 : ℝ) ^ 43 ≤ Real.exp 100 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 100 = Real.exp 1 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 43 ≤ 2.7182818283 ^ 100 := by norm_num
      _ ≤ Real.exp 1 ^ 100 := by gcongr
  have h1 : Real.exp (Real.log (Xm X₀) * -(1 / 50)) ≤ Real.exp (-100) :=
    Real.exp_le_exp.mpr (by linarith)
  refine h1.trans ?_
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h100

/-- `e^{-41} ≥ 10⁻¹⁸`. -/
lemma exp_neg41_ge : (1 : ℝ) / 10 ^ 18 ≤ Real.exp (-41) := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 41 = Real.exp 1 ^ 41 := by rw [← Real.exp_nat_mul]; norm_num
  have h41 : Real.exp 41 ≤ 10 ^ 18 := by
    rw [e]
    calc Real.exp 1 ^ 41 ≤ 2.7182818286 ^ 41 := by gcongr
      _ ≤ 10 ^ 18 := by norm_num
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (Real.exp_pos _) h41

/-- The logarithms at the blocks: `ℓ_i = log(v_i/2) = log(X₀⁻/2) + iδ`. -/
lemma logs_blk (hX : 10 ^ 8 ≤ Real.log X₀) (i : ℕ) :
    Real.log (Xm X₀ * 2 ^ i / 2) = Real.log (Xm X₀ / 2) + i * Real.log 2 ∧
    Real.log (3 * (Xm X₀ * 2 ^ i)) = Real.log (Xm X₀ * 2 ^ i / 2) + Real.log 6 ∧
    Real.log (4 * (Xm X₀ * 2 ^ i)) = Real.log (Xm X₀ * 2 ^ i / 2) + 3 * Real.log 2 := by
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hXm0 : 0 < Xm X₀ := by linarith
  have h0 : 0 < Xm X₀ * 2 ^ i / 2 := by positivity
  have h8 : (0 : ℝ) < Xm X₀ / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [show Xm X₀ * 2 ^ i / 2 = Xm X₀ / 2 * 2 ^ i by ring, Real.log_mul h8.ne' (by positivity),
      Real.log_pow]
  · rw [show 3 * (Xm X₀ * 2 ^ i) = Xm X₀ * 2 ^ i / 2 * 6 by ring,
      Real.log_mul h0.ne' (by norm_num)]
  · rw [show 4 * (Xm X₀ * 2 ^ i) = Xm X₀ * 2 ^ i / 2 * 2 ^ 3 by ring,
      Real.log_mul h0.ne' (by positivity), Real.log_pow]; push_cast; ring

set_option maxHeartbeats 2000000 in
/-- **eq. (osc), second display**: `∑_j (log 3v_j)² o_j ≤ e^{-41}` (04f-bridge.tex,
paragraph "Oscillation of the target", and `lem:predictable`). -/
theorem sum_oscG_le (hX : 10 ^ 8 ≤ Real.log X₀) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i ≤
      Real.exp (-41) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hXm0 : 0 < Xm X₀ := by linarith
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlog6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  have hlog60 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  set Λ := Real.log (Xm X₀ / 2) with hΛ
  have hΛ1 : 10 ^ 8 - 2 ≤ Λ := by
    have h1 : Real.log ((X₀ : ℝ) / 4) ≤ Λ := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hLs : (3.9 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  set M := Lstar X₀ - 4 * δ with hM
  have hM0 : 3.8 * 10 ^ 18 ≤ M := by linarith
  have hMp : 0 < M := by linarith
  set φ : ℕ → ℝ := fun i => psi1 M (Λ + i * δ - δ) with hφ
  -- split each term
  have hsplit : ∀ i : ℕ, Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i ≤
      (Xm X₀ * 2 ^ i) ^ (-(1 / 50 : ℝ)) + 2.0001 / δ * (φ i - φ (i + 1)) := by
    intro i
    obtain ⟨e1, e2, e3⟩ := logs_blk hX i
    set u := Xm X₀ * 2 ^ i with hu
    have hu1 : Xm X₀ ≤ u := by
      rw [hu]; have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hu4 : (X₀ : ℝ) ≤ 4 * u := by linarith
    have hn := nonA3_le hX hu4
    set ℓ := Λ + i * δ with hℓ
    have hℓ1 : 10 ^ 8 - 2 ≤ ℓ := by
      have : (0 : ℝ) ≤ i * δ := by positivity
      linarith
    have hlℓ : Real.log (u / 2) = ℓ := by rw [e1]
    have hA : Real.log (3 * u) ^ 2 * (2 * (if Lstar X₀ < Real.log (4 * u) then
        (Real.log (u / 2) ^ 4)⁻¹ else 0)) ≤ 2.0001 / δ * (φ i - φ (i + 1)) := by
      have e4 : Λ + ((i + 1 : ℕ) : ℝ) * δ - δ = ℓ := by push_cast; ring
      simp only [hφ, e4]
      rw [e3, e2, hlℓ]
      split_ifs with hL
      · have hgap := psi1_gap hMp (by linarith) (show M ≤ ℓ - δ by linarith)
        have hℓ0 : 0 < ℓ := by linarith
        have key : (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) ≤ 2.0001 / ℓ ^ 2 := by
          rw [show (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) = 2 * (ℓ + Real.log 6) ^ 2 / ℓ ^ 4 by
            field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (ℓ + Real.log 6) ^ 2 ≤ 1.00005 * ℓ ^ 2 := by nlinarith
          have : 0 < ℓ ^ 2 := by positivity
          nlinarith
        calc (ℓ + Real.log 6) ^ 2 * (2 * (ℓ ^ 4)⁻¹) ≤ 2.0001 / ℓ ^ 2 := key
          _ = 2.0001 / δ * (δ / ℓ ^ 2) := by field_simp
          _ ≤ 2.0001 / δ * (psi1 M (ℓ - δ) - psi1 M ℓ) :=
              mul_le_mul_of_nonneg_left hgap (by positivity)
      · have := psi1_anti hMp (show ℓ - δ ≤ ℓ by linarith)
        have : 0 ≤ psi1 M (ℓ - δ) - psi1 M ℓ := by linarith
        simp only [mul_zero]
        positivity
    unfold obG Bsc
    rw [← hu]
    have e : Real.log (3 * u) ^ 2 * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) /
        (kappaParam X₀ * u) + 2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) +
        2 * (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0)) =
        Real.log (3 * u) ^ 2 * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) /
        (kappaParam X₀ * u) + 2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ))) +
        Real.log (3 * u) ^ 2 * (2 * (if Lstar X₀ < Real.log (4 * u) then
          (Real.log (u / 2) ^ 4)⁻¹ else 0)) := by ring
    rw [e]
    linarith
  have hφ0 : ∀ i, 0 ≤ φ i := fun i => psi1_nonneg hMp _
  have hT := tele_le (f := fun i => 2.0001 / δ * (φ i - φ (i + 1))) (C := 2.0001 / δ)
    (by positivity) hφ0 (fun i => le_rfl) (J + 1)
  have hg := sum_geom_twentieth hXm0 (J + 1)
  have hq := Xm_rpow_le hX
  have hφ00 : φ 0 ≤ M⁻¹ := by
    simp only [hφ]; unfold psi1
    exact inv_anti₀ hMp (le_max_right _ _)
  have hA : 2.0001 / δ * φ 0 ≤ 8 / 10 ^ 19 := by
    calc 2.0001 / δ * φ 0 ≤ 2.0001 / δ * M⁻¹ :=
          mul_le_mul_of_nonneg_left hφ00 (by positivity)
      _ ≤ 8 / 10 ^ 19 := by
          rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have he := exp_neg41_ge
  calc ∑ i ∈ Finset.range (J + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * obG X₀ i
      ≤ ∑ i ∈ Finset.range (J + 1), ((Xm X₀ * 2 ^ i) ^ (-(1 / 50 : ℝ)) +
          2.0001 / δ * (φ i - φ (i + 1))) := Finset.sum_le_sum fun i _ => hsplit i
    _ = ∑ i ∈ Finset.range (J + 1), (Xm X₀ * 2 ^ i) ^ (-(1 / 50 : ℝ)) +
          ∑ i ∈ Finset.range (J + 1), 2.0001 / δ * (φ i - φ (i + 1)) :=
        Finset.sum_add_distrib
    _ ≤ 73 * (1 / 10 ^ 43) + 8 / 10 ^ 19 := by nlinarith
    _ ≤ Real.exp (-41) := by linarith

set_option maxHeartbeats 2000000 in
/-- **The `6/H` part of `F̄_r`**: `∑_j (log 3v_j)² · 6/H(v_j) ≤ 5·10⁻²³` (`lem:predictable`;
`H ≥ e^{8(log log v)²}`, Theorem 6.23). -/
theorem sum_sixH_le (hX : 10 ^ 8 ≤ Real.log X₀) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 *
      (6 / Queue6.Hc X₀ (Xm X₀ * 2 ^ i)) ≤ 5 / 10 ^ 23 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlog6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  have hlog60 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  set Λ := Real.log (Xm X₀ / 2) with hΛ
  have hΛ1 : 10 ^ 8 - 2 ≤ Λ := by
    have h1 : Real.log ((X₀ : ℝ) / 4) ≤ Λ := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hlog10 : 16 ≤ Real.log (10 ^ 8 : ℝ) := by
    rw [Real.log_pow]
    have : 3 * Real.log 2 ≤ Real.log 10 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    push_cast; linarith [Real.log_two_gt_d9]
  set φ : ℕ → ℝ := fun i => psi1 1 (Λ + i * δ - δ) with hφ
  have hT : ∀ i : ℕ, Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 * (6 / Queue6.Hc X₀ (Xm X₀ * 2 ^ i)) ≤
      1 / 10 ^ 16 * (φ i - φ (i + 1)) := by
    intro i
    obtain ⟨e1, e2, -⟩ := logs_blk hX i
    set u := Xm X₀ * 2 ^ i with hu
    have hu1 : Xm X₀ ≤ u := by
      rw [hu]; have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    set ℓ := Λ + i * δ with hℓ
    have hℓ1 : 10 ^ 8 - 2 ≤ ℓ := by
      have : (0 : ℝ) ≤ i * δ := by positivity
      linarith
    have hℓ0 : 0 < ℓ := by linarith
    -- `H(u) ≥ L^{100}`, `L = log max(u, X₀) ≥ ℓ`
    set m := max u (X₀ : ℝ) with hm
    have hmX : (X₀ : ℝ) ≤ m := le_max_right _ _
    have hm0 : 0 < m := by linarith
    set L := Real.log m with hL
    have hLX : Real.log X₀ ≤ L := Real.log_le_log (by linarith) hmX
    have hLℓ : ℓ ≤ L := by
      have : Real.log (u / 2) ≤ Real.log m :=
        Real.log_le_log (by linarith) (by linarith [le_max_left u (X₀ : ℝ)])
      rw [e1] at this; exact this
    have hL0 : 0 < L := by linarith
    have hlogL : 16 ≤ Real.log L := hlog10.trans (Real.log_le_log (by norm_num) (by linarith))
    have hH : L ^ 100 ≤ Queue6.Hc X₀ u := by
      unfold Queue6.Hc capH
      refine le_trans ?_ (le_max_left _ _)
      rw [← hm, ← hL]
      have : L ^ 100 = Real.exp ((100 : ℕ) * Real.log L) := by
        rw [Real.exp_nat_mul, Real.exp_log hL0]
      rw [this]
      exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
    have hH0 : 0 < L ^ 100 := by positivity
    have e4 : Λ + ((i + 1 : ℕ) : ℝ) * δ - δ = ℓ := by push_cast; ring
    simp only [hφ, e4]
    have hgap := psi1_gap (M := 1) one_pos (by linarith) (show (1 : ℝ) ≤ ℓ - δ by linarith)
    rw [e2, e1]
    have hl3 : (ℓ + Real.log 6) ^ 2 ≤ 2 * ℓ ^ 2 := by nlinarith
    have hℓL : ℓ ^ 100 ≤ L ^ 100 := pow_le_pow_left₀ hℓ0.le hLℓ 100
    have hℓ5 : ℓ ^ 25 ≤ ℓ ^ 100 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hℓ3 : (10 : ℝ) ^ 21 ≤ ℓ ^ 3 := by
      have : (10 : ℝ) ^ 7 ≤ ℓ := by linarith
      calc (10 : ℝ) ^ 21 = (10 ^ 7) ^ 3 := by norm_num
        _ ≤ ℓ ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
    calc (ℓ + Real.log 6) ^ 2 * (6 / Queue6.Hc X₀ u) ≤ 2 * ℓ ^ 2 * (6 / ℓ ^ 25) := by
          apply mul_le_mul hl3 _ (div_nonneg (by norm_num) (KR.WidthReal.Hc_pos hX u).le)
            (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (hℓ5.trans (hℓL.trans hH))
      _ ≤ 1 / 10 ^ 16 * (δ / ℓ ^ 2) := by
          have hℓ21 : ℓ ^ 3 ≤ ℓ ^ 21 := pow_le_pow_right₀ (by linarith) (by norm_num)
          rw [show 2 * ℓ ^ 2 * (6 / ℓ ^ 25) = 12 / ℓ ^ 23 by field_simp; ring,
            show 1 / 10 ^ 16 * (δ / ℓ ^ 2) = δ / (10 ^ 16 * ℓ ^ 2) by field_simp,
            div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 < ℓ ^ 2 := by positivity
          have e5 : ℓ ^ 23 = ℓ ^ 21 * ℓ ^ 2 := by ring
          rw [e5]
          nlinarith [mul_le_mul_of_nonneg_right (hℓ3.trans hℓ21) this.le]
      _ ≤ 1 / 10 ^ 16 * (psi1 1 (ℓ - δ) - psi1 1 ℓ) :=
          mul_le_mul_of_nonneg_left hgap (by norm_num)
  have hφ0 : ∀ i, 0 ≤ φ i := fun i => psi1_nonneg one_pos _
  have h := tele_le (C := 1 / 10 ^ 16) (by norm_num) hφ0 hT (J + 1)
  have hφ00 : φ 0 ≤ 1 / 10 ^ 7 := by
    simp only [hφ]; unfold psi1
    rw [← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    push_cast
    exact le_trans (by linarith) (le_max_left _ _)
  calc _ ≤ 1 / 10 ^ 16 * φ 0 := h
    _ ≤ 1 / 10 ^ 16 * (1 / 10 ^ 7) := mul_le_mul_of_nonneg_left hφ00 (by norm_num)
    _ ≤ 5 / 10 ^ 23 := by norm_num

end BModel

end
