module

public import RequestProject.Beurling.Model.SigmaResp
public import RequestProject.Beurling.Model.T0Mono
public import RequestProject.Beurling.Model.HBSGood
public import RequestProject.Beurling.Model.TBoundE1

/-!
# The window parameter `δ` and Theorem 5.24 at `y(1-δ)` (Proposition 5.35(B), Model fields)

Proof of Proposition 5.35 for range (B) (04f-bridge.tex): `γ_j` is *resolvable at `y`* if
`γ_j ≤ Γ(y) := e^{c_LP √(log y)/4}`; `γ_*` is the largest resolvable `γ_j` (`1` if there is
none), and `δ := min(γ_*⁻² log⁻⁴ y, X₀^{-1/2})`.

* `gStar`, `GammaRes`, `deltaB` : `γ_*`, `Γ(y)` and `δ` for the realised heights
  `γ = gammaD θ X₀ (DF θ X₀ ω)`; `le_gStar` : every resolvable `γ_j` is `≤ γ_*`;
* `deltaB_pos`, `deltaB_le`, `deltaB_low`, `deltaB_L` : the fields `hδ0`, `hδ`, `hδlow`, `hδL`
  of `KR.RML6.G1BInputs`;
* `deltaB_gap` : `y(1-δ) + 26 log y + 2 < y - y^{1/8}` ("the window `J` ends `δx ≥ x^{0.98} > H(x)`
  before `x`");
* `hT_c` : **Theorem 5.24 at `y(1-δ)`** on `QC(< t) ∩ {E1 of time < t} ∩ NiceEv`, `b ≤ t`,
  `y ≤ b + H(b)` (the field `hT`): `theorem_5_24_data` with the queue-lag bound (Corollary 3.8,
  `lag_local`, from the queue bound `queue_of_QE` at heights `u` with `u + 26 log u + 2 < t`) and
  Lemma 3.4 for the capped absorbed density (`absorbed_target_error_cap_loc`, with Lemma 6.27(a),
  `rhoA_le_QE`), all below the certified horizon (Remark *horizon*);
* `G1BDeltaPart`, `g1BDelta_c` : the package.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed AbsorbEmpty Queue6
  SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### `γ_*` and `δ` -/

/-- `γ_* = max({1} ∪ {γ_j : γ_j ≤ G})`, the largest resolvable height (`1` if none). -/
noncomputable def gStar (γ : ℕ → ℝ) (G : ℝ) : ℝ := sSup (insert 1 {g | ∃ j, γ j = g ∧ g ≤ G})

lemma gStar_bdd (γ : ℕ → ℝ) {G : ℝ} (hG : 1 ≤ G) :
    BddAbove (insert (1 : ℝ) {g | ∃ j, γ j = g ∧ g ≤ G}) := by
  refine ⟨G, fun g hg => ?_⟩
  rcases hg with rfl | ⟨j, -, hj⟩
  · exact hG
  · exact hj

lemma one_le_gStar (γ : ℕ → ℝ) {G : ℝ} (hG : 1 ≤ G) : 1 ≤ gStar γ G :=
  le_csSup (gStar_bdd γ hG) (mem_insert _ _)

lemma gStar_le (γ : ℕ → ℝ) {G : ℝ} (hG : 1 ≤ G) : gStar γ G ≤ G := by
  refine csSup_le ⟨1, mem_insert _ _⟩ fun g hg => ?_
  rcases hg with rfl | ⟨j, -, hj⟩
  · exact hG
  · exact hj

/-- Every resolvable height is at most `γ_*`. -/
lemma le_gStar (γ : ℕ → ℝ) {G : ℝ} (hG : 1 ≤ G) {j : ℕ} (hj : γ j ≤ G) : γ j ≤ gStar γ G :=
  le_csSup (gStar_bdd γ hG) (mem_insert_of_mem _ ⟨j, rfl, hj⟩)

/-- `Γ(y) = e^{c_LP √(log y)/4}` (proof of Proposition 5.35, range (B)). -/
noncomputable def GammaRes (X₀ : ℕ) (y : ℝ) : ℝ :=
  Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 4)

variable (θ X₀) in
/-- **The window parameter** `δ = min(γ_*⁻² log⁻⁴ y, X₀^{-1/2})` (proof of Proposition 5.35,
range (B)), for the realised heights `γ = gammaD θ X₀ (DF θ X₀ ω)`. -/
noncomputable def deltaB (ω : JitterΩ) (y : ℝ) : ℝ :=
  min (1 / (gStar (gammaD θ X₀ (DF θ X₀ ω)) (GammaRes X₀ y) ^ 2 * Real.log y ^ 4))
    ((X₀ : ℝ) ^ (-(1 / 2) : ℝ))

lemma cLP_mem {Λ : ℝ} (hΛ : 1 ≤ Λ) : 0 ≤ LocalPNT.cLP Λ ∧ LocalPNT.cLP Λ ≤ 1 := by
  unfold LocalPNT.cLP LocalPNT.cZF
  have h0 : 0 ≤ 0.088 / Λ := by positivity
  have h1 : 0.088 / Λ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  constructor <;> linarith

lemma one_le_GammaRes (hX : 10 ^ 8 ≤ Real.log X₀) (y : ℝ) : 1 ≤ GammaRes X₀ y := by
  unfold GammaRes
  have := (cLP_mem (Λ := Real.log X₀) (by linarith)).1
  exact Real.one_le_exp (by positivity)

section Delta

variable (hc : Cond θ X₀)
include hc

lemma one_lt_X0 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hc.hX

lemma logy_pos {y : ℝ} (hy : (X₀ : ℝ) ≤ y) : 0 < Real.log y :=
  Real.log_pos (by linarith [one_lt_X0 hc])

lemma gStarR_ge (ω : JitterΩ) (y : ℝ) :
    1 ≤ gStar (gammaD θ X₀ (DF θ X₀ ω)) (GammaRes X₀ y) :=
  one_le_gStar _ (one_le_GammaRes hc.hX y)

/-- The field `hδ0`. -/
lemma deltaB_pos (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) : 0 < deltaB θ X₀ ω y := by
  have hL := logy_pos hc hy
  have hg := gStarR_ge hc ω y
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
  unfold deltaB
  refine lt_min (by positivity) (Real.rpow_pos_of_pos hX0 _)

omit hc in
/-- The field `hδ`. -/
lemma deltaB_le (ω : JitterΩ) (y : ℝ) : deltaB θ X₀ ω y ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ) :=
  min_le_right _ _

/-- The field `hδL`: `δ ≤ log⁻⁴ y`. -/
lemma deltaB_L (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    deltaB θ X₀ ω y ≤ 1 / Real.log y ^ 4 := by
  have hL := logy_pos hc hy
  have hg := gStarR_ge hc ω y
  refine (min_le_left _ _).trans ?_
  have hL4 : 0 < Real.log y ^ 4 := by positivity
  apply one_div_le_one_div_of_le hL4
  have : 1 ≤ gStar (gammaD θ X₀ (DF θ X₀ ω)) (GammaRes X₀ y) ^ 2 := one_le_pow₀ hg
  nlinarith

/-- The field `hδlow`: `1/δ ≤ e^{c_LP √(log y)/2} log⁴ y + X₀^{1/2}` (as `γ_* ≤ Γ(y)`). -/
lemma deltaB_low (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    1 / deltaB θ X₀ ω y ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
  have hL := logy_pos hc hy
  have hG1 := one_le_GammaRes hc.hX y
  set g := gStar (gammaD θ X₀ (DF θ X₀ ω)) (GammaRes X₀ y) with hgdef
  have hg := gStarR_ge hc ω y
  have hgG : g ≤ GammaRes X₀ y := gStar_le _ hG1
  have hX0 : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
  set a := 1 / (g ^ 2 * Real.log y ^ 4) with ha
  set c := (X₀ : ℝ) ^ (-(1 / 2) : ℝ) with hcdef
  have ha0 : 0 < a := by positivity
  have hc0 : 0 < c := Real.rpow_pos_of_pos hX0 _
  have h1 : 1 / min a c ≤ 1 / a + 1 / c := by
    rcases le_total a c with h | h
    · rw [min_eq_left h]; have : 0 < 1 / c := by positivity
      linarith
    · rw [min_eq_right h]; have : 0 < 1 / a := by positivity
      linarith
  have h2 : 1 / a ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 := by
    rw [ha, one_div_one_div]
    have hΓ2 : GammaRes X₀ y ^ 2 =
        Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) := by
      unfold GammaRes; rw [sq, ← Real.exp_add]; ring_nf
    rw [← hΓ2]
    have : g ^ 2 ≤ GammaRes X₀ y ^ 2 := pow_le_pow_left₀ (by linarith) hgG 2
    have hL4 : 0 < Real.log y ^ 4 := by positivity
    nlinarith
  have h3 : 1 / c = (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hcdef, Real.rpow_neg hX0.le, one_div, inv_inv]
  show 1 / min a c ≤ _
  linarith

end Delta

/-! ### The gap below `y` -/

/-- `(e^{L/8} + 26L + 2)(e^{c√L/2} L⁴ + e^{Λ/2}) < e^L` for `L ≥ e^{Λ/100}`, `Λ ≥ 10⁸`,
`0 ≤ c ≤ 1`. -/
lemma gap_num {Λ L c : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : Real.exp (Λ / 100) ≤ L) (_hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) :
    (Real.exp (L / 8) + 26 * L + 2) * (Real.exp (c * √L / 2) * L ^ 4 + Real.exp (Λ / 2)) <
      Real.exp L := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Λ / 100 by positivity)
  have hL2 : 2 * Λ ≤ L := by nlinarith
  have hL8 : (2 * 10 ^ 8 : ℝ) ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  -- `26 L + 2 ≤ e^{L/8}`
  have hq8 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ L / 8 by positivity)
  have h26 : 26 * L + 2 ≤ Real.exp (L / 8) := by nlinarith
  -- `L⁴ ≤ e^{L/8}`
  have hp := Real.pow_div_factorial_le_exp (L / 8) (by positivity) 8
  have e8 : ((8 : ℕ).factorial : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [e8, div_pow] at hp
  have hL4 : L ^ 4 ≤ Real.exp (L / 8) := by
    have hL4b : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hL8 4; nlinarith
    have : L ^ 8 = L ^ 4 * L ^ 4 := by ring
    have h8 : (8 : ℝ) ^ 8 * 40320 ≤ 10 ^ 32 := by norm_num
    have hp' : L ^ 8 / 8 ^ 8 / 40320 = L ^ 8 / (8 ^ 8 * 40320) := by ring
    rw [hp', div_le_iff₀ (by norm_num)] at hp
    nlinarith
  -- `e^{c√L/2} ≤ e^{L/8}`
  have hs : c * √L / 2 ≤ L / 8 := by
    have hsq := Real.sq_sqrt hL0.le
    have hs0 := Real.sqrt_nonneg L
    have hs4 : 4 ≤ √L := by
      rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
    have : c * √L ≤ √L := by nlinarith
    nlinarith
  have hE1 : Real.exp (c * √L / 2) * L ^ 4 ≤ Real.exp (L / 4) := by
    have : Real.exp (L / 4) = Real.exp (L / 8) * Real.exp (L / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact mul_le_mul (Real.exp_le_exp.mpr hs) hL4 (by positivity) (Real.exp_pos _).le
  have hE2 : Real.exp (Λ / 2) ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
  have hA : Real.exp (L / 8) + 26 * L + 2 ≤ 2 * Real.exp (L / 8) := by linarith
  have hB : Real.exp (c * √L / 2) * L ^ 4 + Real.exp (Λ / 2) ≤ 2 * Real.exp (L / 4) := by
    linarith
  have hprod : (Real.exp (L / 8) + 26 * L + 2) *
      (Real.exp (c * √L / 2) * L ^ 4 + Real.exp (Λ / 2)) ≤
      4 * Real.exp (3 * L / 8) := by
    have e : Real.exp (3 * L / 8) = Real.exp (L / 8) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h0 : 0 ≤ Real.exp (L / 8) + 26 * L + 2 := by positivity
    calc _ ≤ (2 * Real.exp (L / 8)) * (2 * Real.exp (L / 4)) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = _ := by ring
  have h4 : 4 * Real.exp (3 * L / 8) < Real.exp L := by
    have e : Real.exp L = Real.exp (3 * L / 8) * Real.exp (5 * L / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have : (4 : ℝ) < Real.exp (5 * L / 8) := by
      have := Real.add_one_le_exp (5 * L / 8); linarith
    have := Real.exp_pos (3 * L / 8)
    nlinarith
  linarith

section Gap

variable (hc : Cond θ X₀)
include hc

/-- **The window ends well before `y`**: `y(1-δ) + 26 log y + 2 < y - y^{1/8}` for
`log y > X₀^{1/100}` (proof of Proposition 5.35, range (B): `δx ≥ x^{0.98} > H(x)`). -/
lemma deltaB_gap (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    y * (1 - deltaB θ X₀ ω y) + 26 * Real.log y + 2 < y - y ^ (1 / 8 : ℝ) := by
  have hX1 := one_lt_X0 hc
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  have hδ0 := deltaB_pos hc ω hy
  have hlow := deltaB_low hc ω hy
  have hLe : Real.exp (Real.log X₀ / 100) ≤ Real.log y := by
    rw [Real.rpow_def_of_pos hX0] at hyL
    have : Real.log X₀ * (1 / 100) = Real.log X₀ / 100 := by ring
    rw [this] at hyL; exact hyL.le
  set L := Real.log y with hLdef
  set δ := deltaB θ X₀ ω y
  have hcl := cLP_mem (Λ := Real.log X₀) (by linarith [hc.hX])
  have hnum := gap_num hc.hX hLe hcl.1 hcl.2
  have hy8 : y ^ (1 / 8 : ℝ) = Real.exp (L / 8) := by
    rw [Real.rpow_def_of_pos hy0]; congr 1; ring
  have hX2 : (X₀ : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Real.log X₀ / 2) := by
    rw [Real.rpow_def_of_pos hX0]; congr 1; ring
  have hye : y = Real.exp L := (Real.exp_log hy0).symm
  rw [hX2] at hlow
  set D := Real.exp (LocalPNT.cLP (Real.log X₀) * √L / 2) * L ^ 4 + Real.exp (Real.log X₀ / 2)
    with hD
  have hD0 : 0 < D := by positivity
  -- `δ y ≥ y / D > y^{1/8} + 26L + 2`
  have hδD : 1 / D ≤ δ := by
    rw [div_le_iff₀ hD0]
    rw [div_le_iff₀ hδ0] at hlow
    linarith
  have hkey : y ^ (1 / 8 : ℝ) + 26 * L + 2 < δ * y := by
    rw [hy8]
    have h1 : (Real.exp (L / 8) + 26 * L + 2) * D < y := by rw [hye]; exact hnum
    have h2 : y / D ≤ δ * y := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hδD hy0.le
    have h3 : Real.exp (L / 8) + 26 * L + 2 < y / D := by rw [lt_div_iff₀ hD0]; exact h1
    linarith
  nlinarith

end Gap

/-! ### Lemma 6.27(a) for the uncapped density below `2(b + H(b))` -/

section Dens

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **`ρ_𝒜(u) ≤ L_u⁻⁴` on `Good(< t)`** at `X₀ ≤ u ≤ 2(b + H(b))`, `b ≤ t` (Lemma 6.27(a); the
uncapped form of `rhoCap_le_L4`). -/
lemma rhoA_le_L4 {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {u : ℝ} (huX : (X₀ : ℝ) ≤ u)
    (hu2 : u ≤ 2 * (b + Queue6.Hc X₀ b)) :
    absorbedDensity (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) u ≤ Real.log u ^ (-4 : ℤ) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hu0 : 0 < u := by linarith
  have hLu0 : 0 < Real.log u := by linarith [Real.log_le_log hXp huX]
  have hHb : Queue6.Hc X₀ b ≤ b / 4 := by
    unfold Queue6.Hc; rw [max_eq_left hb]
    have := four_capH_le hX0 hX hb; linarith
  set Λ := Real.log X₀ with hΛdef
  by_cases hsmall : Real.log u ≤ Lstar X₀
  · rw [rhoA_eq_zero_of_small hc ω hsmall]; positivity
  push_neg at hsmall
  have hLs : (10 : ℝ) ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  set L := Real.log u with hLdef
  have hbu : u ≤ 3 * b := by linarith
  have hlog3 : Real.log 3 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  have hlogb : L - 2 < Real.log b := by
    have h3 : L ≤ Real.log 3 + Real.log b := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log hu0 hbu
    linarith
  have hbX : 4 * (X₀ : ℝ) + 2 ≤ b := by
    have h5 : Real.log (6 * (X₀ : ℝ)) ≤ 2 + Λ := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 6 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith
      linarith
    have hΛb : 2 + Λ < Real.log b := by
      have : Λ ≤ Λ ^ 2 := by nlinarith
      have : Λ ^ 2 ≤ Lstar X₀ + 1 := by
        unfold Lstar
        have h2 := exp_sH_ge
        nlinarith
      nlinarith
    have h6 : 6 * (X₀ : ℝ) < b := (Real.log_lt_log_iff (by positivity) (by linarith)).mp
      (lt_of_le_of_lt h5 hΛb)
    linarith
  have hZb : Zc X₀ b = (b - 2) / 4 := by unfold Zc; rw [if_pos hbX]
  have hZX : (X₀ : ℝ) ≤ Zc X₀ b := by rw [hZb]; linarith
  have hZt : 4 * Zc X₀ b + 2 ≤ t := by rw [hZb]; linarith
  have hbig2 : Λ ^ 2 < Real.log (2 * u) := by
    have : L ≤ Real.log (2 * u) := Real.log_le_log hu0 (by linarith)
    have : Λ ^ 2 ≤ Lstar X₀ := by
      unfold Lstar
      have h2 := exp_sH_ge
      nlinarith
    linarith
  have hY := AbsorbSize.log_three_absorbYAt_le hX0 hX (show (X₀ : ℝ) ≤ 2 * u by linarith) hbig2
  have hY0 := absorbYAt_pos' hc hev (show (X₀ : ℝ) ≤ 2 * u by linarith)
  have hl2u : Real.log (2 * u) ≤ L + 1 := by
    rw [Real.log_mul (by norm_num) hu0.ne']; have := Real.log_two_lt_d9; linarith
  have hL18 : (10 : ℝ) ^ 18 ≤ L := by linarith
  have hsq : Real.sqrt (Real.log (2 * u)) ≤ L / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hlog3y : Real.log (3 * AbsorbEmpty.absorbYAt X₀ (2 * u)) ≤ L - 10 := by linarith
  have h3y : 3 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Real.exp (L - 10) := by
    rw [← Real.exp_log (show 0 < 3 * AbsorbEmpty.absorbYAt X₀ (2 * u) by positivity)]
    exact Real.exp_le_exp.mpr hlog3y
  have hexp : Real.exp (L - 10) ≤ u / 1000 := by
    rw [Real.exp_sub, Real.exp_log hu0, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have : (1000 : ℝ) ≤ Real.exp 10 := by
      have h := Real.exp_one_gt_d9
      have e : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc (1000 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
        _ ≤ Real.exp 1 ^ 10 := by gcongr
    nlinarith
  have hu1000 : (1000 : ℝ) ≤ u := by linarith [X₀_ge_two_pow hX]
  have h2y : 2 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Zc X₀ b := by
    rw [hZb]; linarith
  have hut : 20 * u / L ^ 11 + 5 ≤ t := by
    have hL11 : (1000 : ℝ) ≤ L ^ 11 := by
      have : L ≤ L ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
      linarith
    have : 20 * u / L ^ 11 ≤ u / 50 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  exact rhoA_le_QE hc hev hQC hE1 hN hZX hZt huX h2y hut

end Dens

/-! ### Theorem 5.24 at `y(1-δ)` -/

section T524

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **The field `hT`** (proof of Proposition 5.35, range (B), Step 1): Theorem 5.24 holds at
`y(1-δ)` on `QC(< t) ∩ {E1 of time < t} ∩ NiceEv` for every start `X₀ ≤ y ≤ b + H(b)` with
`log y > X₀^{1/100}`, `b ≤ t`. `theorem_5_24_data` is applied with the horizon `ž = y(1-δ)`;
its inputs below `ž` are the queue-lag bound (Corollary 3.8 at each height `u ≤ ž`, from the
queue bound at the slot of `u`, which is decided before `u + 26 log u + 2 < t`) and Lemma 3.4 for
the capped absorbed density (with Lemma 6.27(a) below `ž`), so only events before `t` are read
(Remark *horizon*). -/
theorem hT_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    LocalPNT.Theorem524Concl (PR θ X₀ ω) X₀ (y * (1 - deltaB θ X₀ ω y)) := by
  classical
  have hNice := hN
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hy0 : 0 < y := by linarith
  set δ := deltaB θ X₀ ω y with hδdef
  set zc := y * (1 - δ) with hzc
  have hδ0 := deltaB_pos hc ω hy
  have hgap := deltaB_gap hc ω hy hyL
  -- `y - y^{1/8} ≤ t`
  have hyt : y - y ^ (1 / 8 : ℝ) ≤ t := by
    have h8 : 0 ≤ y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hy0.le _
    rcases le_total y b with h | h
    · linarith
    · have hH : Queue6.Hc X₀ b ≤ y ^ (1 / 8 : ℝ) := by
        unfold Queue6.Hc; rw [max_eq_left hb]
        exact (InitialRange.capH_le_rpow hX0 hX hb).trans
          (Real.rpow_le_rpow (by linarith) h (by norm_num))
      linarith
  have hzcy : zc ≤ y := by
    have : 0 ≤ y * δ := by positivity
    simp only [hzc]; nlinarith
  have hzcX : (X₀ : ℝ) ≤ zc := by
    have hL0 : 0 < Real.log y := logy_pos hc hy
    have h8 : 0 ≤ y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hy0.le _
    -- `y^{1/8} ≤ y/2` and `y ≥ 2X₀` give `zc ≥ X₀`
    have hδ1 : δ ≤ 1 / 2 := by
      refine (deltaB_le ω y).trans ?_
      rw [Real.rpow_neg hX0, ← one_div]
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)]
      have : (2 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) hX0]
        linarith [X₀_ge_two_pow hX]
      linarith
    have hy2 : 2 * (X₀ : ℝ) ≤ y := by
      have hLe : Real.exp (Real.log X₀ / 100) ≤ Real.log y := by
        rw [Real.rpow_def_of_pos (by linarith)] at hyL
        have : Real.log X₀ * (1 / 100) = Real.log X₀ / 100 := by ring
        rw [this] at hyL; exact hyL.le
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log X₀ / 100 by positivity)
      have hl : Real.log X₀ + 1 ≤ Real.log y := by nlinarith
      have := Real.add_one_le_exp (Real.log X₀ + 1)
      have e : Real.exp (Real.log X₀ + 1) = X₀ * Real.exp 1 := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have : (X₀ : ℝ) * Real.exp 1 ≤ y := by
        rw [← e, ← Real.exp_log hy0]; exact Real.exp_le_exp.mpr hl
      nlinarith
    simp only [hzc]; nlinarith
  -- the realised model
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := h0.limModel_low
  have hPR : PR θ X₀ ω = realisedSystem M (capH X₀) ω := by
    show realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω) = _
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hDF : DF θ X₀ ω = DM M ω := by
    unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hAeq : realisedA M (capH X₀) ω = absSet X₀ (DF θ X₀ ω) := by
    rw [realisedA_eq hok hnc, hDF]
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  -- the queue bound below `ž`
  have hut : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → u + 26 * Real.log u + 2 < t := by
    intro u hu huz
    have : Real.log u ≤ Real.log y := Real.log_le_log (by linarith) (huz.trans hzcy)
    linarith
  -- the floor
  have hfl : ∀ u, u < Xm X₀ → (PR θ X₀ ω).N u = ⌊u⌋₊ := by
    intro u hu
    rcases lt_or_ge u 1 with h1 | h1
    · rw [(PR θ X₀ ω).N_eq_zero h1, Nat.floor_eq_zero.mpr h1]; simp
    · rw [hPR]
      exact realised_floor_eq hok hU hX hTlow h1 (by unfold Xm at hu; exact hu)
  have hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ Xm X₀ := by
    unfold Xm
    have h1 := InitialRange.capH_le_rpow hX0 hX (le_refl (X₀ : ℝ))
    have h2 : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    have h3 : 0 ≤ capH X₀ X₀ := by linarith [capH_ge_one hX0 hX (le_refl (X₀ : ℝ))]
    linarith
  -- the lag
  have hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |(PR θ X₀ ω).N u - targetD θ X₀ (DF θ X₀ ω) u| ≤ u ^ lagExponent θ := by
    intro u hu huz
    have hQ := queue_of_QE hc hQC h0 hu (hut u hu huz)
    have hl := lag_local M hc.hθ.1 hc.hθ.2 hX (realisedSystem M (capH X₀) ω).N Real.log
      (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
      (fun x hx _ => landing_of_linked L S hreg hok hx)
      (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hu hQ
    rw [h0.limModel_T_eq u, ← hDF, ← hPR] at hl
    exact hl
  -- Lemma 3.4 for the capped absorbed density
  have hAu := realisedU_spec hok hU hX hTlow (θ := θ) (by linarith [hc.hθ.1])
    (by linarith [hc.hθ.2])
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C : AbsorbedCoupling (realisedSystem M (capH X₀) ω) R.M R.H R.U
      (realisedA M (capH X₀) ω) (realisedLatest M (capH X₀) ω) := realisedCoupling hok
  have hb2 : 0 < θ / 2 := by linarith [hc.hθ.1]
  have hW : AbsorbedWindowHyp (θ / 2) X₀ (absSet X₀ (DF θ X₀ ω)) (uA θ) := by
    rw [← hAeq]
    exact ⟨hb2, by linarith [hc.hθ.2], hX1.le, fun a ha => (hAu a ha).1,
      fun a ha => (hAu a ha).2, C.locFin⟩
  have hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |countA (absSet X₀ (DF θ X₀ ω)) u - ∫ v in (X₀ : ℝ)..u,
        absorbedDensityCap (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) v| ≤ 2 * u ^ (θ / 2) := by
    intro u hu huz
    refine absorbed_target_error_cap_loc hW (by linarith) hu fun v hv hvu => ?_
    refine rhoA_le_L4 hc hev hb hbt hQC hE1 hNice hv ?_
    have : 0 ≤ Queue6.Hc X₀ b := (KR.WidthReal.Hc_pos hX b).le
    linarith
  exact theorem_5_24_data (DF θ X₀ ω) hc.hθ hX hev hc.hHB
    (countA (absSet X₀ (DF θ X₀ ω)))
    (absorbedDensityCap (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ)) hXm (Xm_le_X0 hc) hfl hlag hA
    hzcX le_rfl

end T524

/-! ### The package -/

variable (θ X₀) in
/-- **The Model fields `δ, hδ0, hδ, hδlow, hδL, hT` of `KR.RML6.G1BInputs`** at a start `y`
(proof of Proposition 5.35, range (B)), for `P = PR θ X₀ ω`. -/
structure G1BDeltaPart (ω : JitterΩ) (y : ℝ) where
  δ : ℝ
  hδ0 : 0 < δ
  hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)
  hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
    Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)
  hδL : δ ≤ 1 / Real.log y ^ 4
  hT : LocalPNT.Theorem524Concl (PR θ X₀ ω) X₀ (y * (1 - δ))
  /-- `δ γ_j² ≤ log⁻⁴ y` for every resolvable `γ_j` (used for the resolvable `R'_j`) -/
  hres : ∀ j, gammaD θ X₀ (DF θ X₀ ω) j ≤ GammaRes X₀ y →
    δ * gammaD θ X₀ (DF θ X₀ ω) j ^ 2 ≤ 1 / Real.log y ^ 4

/-- `δ γ_j² ≤ log⁻⁴ y` for resolvable `γ_j`. -/
lemma deltaB_res (hc : Cond θ X₀) (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) {j : ℕ}
    (hj : gammaD θ X₀ (DF θ X₀ ω) j ≤ GammaRes X₀ y) :
    deltaB θ X₀ ω y * gammaD θ X₀ (DF θ X₀ ω) j ^ 2 ≤ 1 / Real.log y ^ 4 := by
  have hL := logy_pos hc hy
  have hG1 := one_le_GammaRes hc.hX y
  set g := gStar (gammaD θ X₀ (DF θ X₀ ω)) (GammaRes X₀ y)
  have hg := gStarR_ge hc ω y
  have hjg : gammaD θ X₀ (DF θ X₀ ω) j ≤ g := le_gStar _ hG1 hj
  have hδ0 := deltaB_pos hc ω hy
  have hδ1 : deltaB θ X₀ ω y ≤ 1 / (g ^ 2 * Real.log y ^ 4) := min_le_left _ _
  have hL4 : 0 < Real.log y ^ 4 := by positivity
  have hγ0 : 0 ≤ gammaD θ X₀ (DF θ X₀ ω) j :=
    le_trans (heightScale_switchOn_pos θ (one_lt_X0 hc).le j).le
      ((gammaD_range (θ := θ) hc.hX (DF θ X₀ ω)) j).1
  have hγ2 : gammaD θ X₀ (DF θ X₀ ω) j ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hγ0 hjg 2
  have hg0 : g ≠ 0 := by linarith
  calc deltaB θ X₀ ω y * gammaD θ X₀ (DF θ X₀ ω) j ^ 2
      ≤ 1 / (g ^ 2 * Real.log y ^ 4) * g ^ 2 :=
        mul_le_mul hδ1 hγ2 (sq_nonneg _) (by positivity)
    _ = 1 / Real.log y ^ 4 := by field_simp

/-- **The package** on `QC(< t) ∩ {E1 of time < t} ∩ NiceEv`, `b ≤ t`, at `X₀ ≤ y ≤ b + H(b)`
with `log y > X₀^{1/100}`. -/
noncomputable def g1BDelta_c (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b)
    {t : ℕ} (hbt : b ≤ t) (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {y : ℝ}
    (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) : G1BDeltaPart θ X₀ ω y where
  δ := deltaB θ X₀ ω y
  hδ0 := deltaB_pos hc ω hy
  hδ := deltaB_le ω y
  hδlow := deltaB_low hc ω hy
  hδL := deltaB_L hc ω hy
  hT := hT_c hc hev hb hbt hQC hE1 hN hy hyb hyL
  hres := fun _ hj => deltaB_res hc ω hy hj

end BModel

end
