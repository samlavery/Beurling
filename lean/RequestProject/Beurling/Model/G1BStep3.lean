module

public import RequestProject.Beurling.Model.SigmaResp
public import RequestProject.Beurling.Model.G1BThresh
public import RequestProject.Beurling.Queue6.Thresh6

/-!
# Proposition 5.35(B), Step 3: the decomposition `hdec34` of `ρ^sh(z) - ρ^sh(y)`

04f-bridge.tex, proof of Proposition 5.35 for range (B), Step 3 ("pointwise against average").
For a start `y`, `z ∈ J = [y(1-2δ), y(1-δ)]`, `r = z/y`, write `ρ^sh(x) = ∑_n c_n(x) T'(x/n)/n`
(Lemma 5.5) over the elements `e` with `y/e ≥ X₀⁻`. Then, exactly (`rhoSh_sub_eq`),

  `ρ^sh(z) - ρ^sh(y) = A(z) + ρ^sh_y(detF_r) + ρ^sh_y(oscF_r) + ρ^sh_y(sigF_r) - j₀ ρ^sh_y(jF_r)`,

* `A(z) = ∑_e (c_e(z) - c_e(y)) T'(z/e)/e`: the **threshold changes**; `c_e(z) ≠ c_e(y)` with
  `z/e ≥ X₀` forces `τ(e) ∈ [y(1-2δ), y)` (`tauIn_of_chi`), so `A(z) ≤ 3 thrS` with
  `thrS = threshSum t y (2δ)` the mass of Lemma 5.23 at `2δ` (`t = tJ`; `|T'| ≤ 3`);
* with `v = y/e`, `v' = max(rv, X₀)` and `T' = 1 - ρ_det + R' + σ_𝒜` on `[X₀, ∞)`, `T' = 0`
  below `X₀`, `R'(X₀) = σ_𝒜(X₀) = 0`:
  `T'(rv) - T'(v) = (ρ_det(v) - ρ_det(v')) + (R'(v') - R'(v)) + (σ_𝒜(v') - σ_𝒜(v)) - j₀ 1[rv < X₀]`
  for `v ≥ X₀` (`TpR_sub`): the **`ρ_det` smooth change** `detF`, the **`R'` change** `oscF`, the
  **`σ_𝒜` change** `sigF`, and the **jump at `X₀`** `jF` (only `n ∈ [z/X₀, y/X₀]` see it).

Hence (`hdec34_R`) `ρ^sh(z) - ρ^sh(y) ≤ 4 thrS + j₀ jS + detS + othS` with
`jS = ∑_{y(1-2δ)/X₀ < e ≤ y/X₀} 1/e`, `detS = sup_{z ∈ J} |ρ^sh_y(detF_{z/y})|`,
`othS = oscS + sigS` (the same suprema for `oscF`, `sigF`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The objects -/

variable (θ X₀) in
/-- `T' = T_c + j₀ 1_{[X₀,∞)}`, the source of `ρ^sh` in `G1BInputs`. -/
noncomputable def TpR (ω : JitterΩ) (t : ℝ) : ℝ :=
  TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t

variable (θ X₀) in
/-- `R'`, the derivative of the designed oscillation. -/
noncomputable def RpR (ω : JitterΩ) (u : ℝ) : ℝ :=
  deriv (Oscillation.osc θ (alphaD θ X₀ (DF θ X₀ ω)) (gammaD θ X₀ (DF θ X₀ ω)) (switchOn X₀)) u

variable (θ X₀) in
/-- `σ_𝒜 = K_𝒜 ρ̃ - ρ̄_𝒜`. -/
noncomputable def sigR (ω : JitterΩ) (u : ℝ) : ℝ :=
  KAbsR θ X₀ ω (rhoT θ X₀ ω) u - absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u

variable (X₀) in
/-- The `ρ_det` smooth change `ρ_det(v) - ρ_det(max(rv, X₀))` (`v ≥ X₀`). -/
noncomputable def detF (r v : ℝ) : ℝ :=
  if (X₀ : ℝ) ≤ v then Target.rhoDet X₀ (kappaParam X₀) v -
    Target.rhoDet X₀ (kappaParam X₀) (max (r * v) X₀) else 0

variable (θ X₀) in
/-- The `R'` change `R'(max(rv, X₀)) - R'(v)` (`v ≥ X₀`). -/
noncomputable def oscF (ω : JitterΩ) (r v : ℝ) : ℝ :=
  if (X₀ : ℝ) ≤ v then RpR θ X₀ ω (max (r * v) X₀) - RpR θ X₀ ω v else 0

variable (θ X₀) in
/-- The `σ_𝒜` change `σ_𝒜(max(rv, X₀)) - σ_𝒜(v)` (`v ≥ X₀`). -/
noncomputable def sigF (ω : JitterΩ) (r v : ℝ) : ℝ :=
  if (X₀ : ℝ) ≤ v then sigR θ X₀ ω (max (r * v) X₀) - sigR θ X₀ ω v else 0

variable (X₀) in
/-- The jump indicator `1[rv < X₀ ≤ v]`. -/
noncomputable def jF (r v : ℝ) : ℝ := if (X₀ : ℝ) ≤ v ∧ r * v < X₀ then 1 else 0

variable (θ X₀) in
/-- The threshold part `A(z) = ∑_e (c_e(z) - c_e(y)) T'(z/e)/e`. -/
noncomputable def thrPart (ω : JitterΩ) (y z : ℝ) : ℝ :=
  ∑ e ∈ (PR θ X₀ ω).elems (y / Xm X₀),
    (cN (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) z (iota e) -
      cN (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (iota e)) *
      TpR θ X₀ ω (z / (PR θ X₀ ω).val e) / (PR θ X₀ ω).val e

/-! ### The Step 3 quantities -/

variable (θ X₀) in
/-- **`thrS`**: the threshold mass of Lemma 5.23 at `2δ`, for `t = tJ` (the field `hthr`). -/
noncomputable def thrS (ω : JitterΩ) (y δ : ℝ) : ℝ :=
  (PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * δ)

open Classical in
variable (θ X₀) in
/-- **`jS`**: `∑_{y(1-2δ)/X₀ < e ≤ y/X₀} 1/e`, the levels that see the jump at `X₀`. -/
noncomputable def jS (ω : JitterΩ) (y δ : ℝ) : ℝ :=
  ∑ e ∈ ((PR θ X₀ ω).elems (y / Xm X₀)).filter (fun e => (X₀ : ℝ) ≤ y / (PR θ X₀ ω).val e ∧
      (1 - 2 * δ) * (y / (PR θ X₀ ω).val e) < X₀), 1 / (PR θ X₀ ω).val e

variable (θ X₀) in
/-- **`detS`**: `sup_{z ∈ J} |∑_n c_n(y) (ρ_det(y/n) - ρ_det(max(z/n, X₀)))/n|`. -/
noncomputable def detS (ω : JitterΩ) (y δ : ℝ) : ℝ :=
  ⨆ z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ (z / y))|

variable (θ X₀) in
/-- `sup_{z ∈ J} |∑_n c_n(y) (R'(max(z/n, X₀)) - R'(y/n))/n|`. -/
noncomputable def oscS (ω : JitterΩ) (y δ : ℝ) : ℝ :=
  ⨆ z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y))|

variable (θ X₀) in
/-- `sup_{z ∈ J} |∑_n c_n(y) (σ_𝒜(max(z/n, X₀)) - σ_𝒜(y/n))/n|`. -/
noncomputable def sigS (ω : JitterΩ) (y δ : ℝ) : ℝ :=
  ⨆ z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω (z / y))|

variable (θ X₀) in
/-- **`othS`** = the `R'` part plus the `σ_𝒜` part. -/
noncomputable def othS (ω : JitterΩ) (y δ : ℝ) : ℝ := oscS θ X₀ ω y δ + sigS θ X₀ ω y δ

/-! ### Generic facts on `ρ^sh` -/

section Gen

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ}

/-- `ρ^sh_z g` as a sum over the elements with `y/e ≥ X₀⁻`, for `z ≤ y`, if `g = 0` below
`X₀⁻`. -/
lemma rhoSh_eq_elems_of_le (hX : 0 < X0m) {y z : ℝ} (hzy : z ≤ y) {g : ℝ → ℝ}
    (hg : ∀ u, u < X0m → g u = 0) :
    rhoSh P tw X0m z g = ∑ e ∈ P.elems (y / X0m),
      cN P tw X0m z (iota e) * g (z / P.val e) / P.val e := by
  rw [G1.rhoSh_eq_elems]
  refine Finset.sum_subset (P.elems_mono (div_le_div_of_nonneg_right hzy hX.le)) ?_
  intro e _ hnot
  rw [mem_elems, not_le] at hnot
  have hv := P.val_pos e
  have : z / P.val e < X0m := by
    rw [div_lt_iff₀ hv]; rw [div_lt_iff₀ hX] at hnot; linarith
  rw [hg _ this]; ring

/-- `|ρ^sh_y g| ≤ M ∑_e 1/e` if `|g(y/e)| ≤ M` at every element with `y/e ≥ X₀⁻`. -/
lemma abs_rhoSh_le_of (ht : ∀ r, r.Prime → 0 < tw r) (hX : 0 < X0m) {y : ℝ} (hy : X0m ≤ y)
    {g : ℝ → ℝ} {M : ℝ} (hg : ∀ e ∈ P.elems (y / X0m), |g (y / P.val e)| ≤ M) :
    |rhoSh P tw X0m y g| ≤ M * ∑ e ∈ P.elems (y / X0m), 1 / P.val e := by
  rw [G1.rhoSh_eq_elems, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  have hv := P.val_pos e
  have hc := G1.abs_cN_le_one (P := P) ht hX.le hy (iota e) (iota_pos e)
  rw [abs_div, abs_mul, abs_of_pos hv, mul_one_div]
  apply div_le_div_of_nonneg_right _ hv.le
  calc |cN P tw X0m y (iota e)| * |g (y / P.val e)| ≤ 1 * M :=
        mul_le_mul hc (hg e he) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

end Gen

/-! ### The pointwise decomposition of `T'` -/

section Dec

variable (hc : Cond θ X₀)
include hc

lemma TpR_low (ω : JitterΩ) {u : ℝ} (hu : u < X₀) : TpR θ X₀ ω u = 0 := by
  unfold TpR
  rw [TcR_low hc ω hu.le]
  have : KR.Chain.ind X₀ u = 0 :=
    Set.indicator_of_notMem (by simpa using hu) _
  rw [this]; ring

lemma TpR_high (ω : JitterΩ) {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    TpR θ X₀ ω u = 1 - Target.rhoDet X₀ (kappaParam X₀) u + RpR θ X₀ ω u + sigR θ X₀ ω u := by
  have hi : KR.Chain.ind X₀ u = 1 := Set.indicator_of_mem (by simpa using hu) _
  unfold TpR TcR TpCont RpR sigR
  rw [if_pos hu, hi]
  unfold jzX; ring

lemma RpR_X0 (ω : JitterΩ) : RpR θ X₀ ω X₀ = 0 :=
  deriv_osc_X0 (QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hc.hX) _ _

lemma sigR_X0 (ω : JitterΩ) : sigR θ X₀ ω X₀ = 0 := by
  unfold sigR
  rw [KAbsR_eq_zero_low hc ω _ le_rfl, rhoCap_X0 hc ω]; ring

/-- **The level change of `T'`** (Step 3): for `0 ≤ r ≤ 1`,
`T'(rv) - T'(v) = detF + oscF + sigF - j₀ jF` at `v`. -/
lemma TpR_sub (ω : JitterΩ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (v : ℝ) :
    TpR θ X₀ ω (r * v) - TpR θ X₀ ω v = detF X₀ r v + oscF θ X₀ ω r v + sigF θ X₀ ω r v -
      jzX X₀ * jF X₀ r v := by
  unfold detF oscF sigF jF
  by_cases hv : (X₀ : ℝ) ≤ v
  · rw [if_pos hv, if_pos hv, if_pos hv, TpR_high hc ω hv]
    by_cases hrv : r * v < X₀
    · rw [if_pos ⟨hv, hrv⟩, TpR_low hc ω hrv, max_eq_right hrv.le, RpR_X0 hc, sigR_X0 hc]
      unfold jzX; ring
    · push_neg at hrv
      rw [if_neg (fun h => absurd h.2 (not_lt.mpr hrv)), max_eq_left hrv, TpR_high hc ω hrv]
      ring
  · push_neg at hv
    have hrv : r * v < X₀ := by
      rcases le_or_gt 0 v with h0 | h0
      · nlinarith
      · have : r * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 h0.le
        have : (0 : ℝ) < X₀ := by linarith [QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hc.hX]
        linarith
    rw [if_neg (not_le.mpr hv), if_neg (not_le.mpr hv), if_neg (not_le.mpr hv),
      if_neg (fun h => absurd h.1 (not_le.mpr hv)), TpR_low hc ω hv, TpR_low hc ω hrv]
    ring

/-- **The decomposition of Step 3** (exact): for `0 ≤ z ≤ y`, `y > 0`, `r = z/y`. -/
theorem rhoSh_sub_eq (ω : JitterΩ) {y z : ℝ} (hy0 : 0 < y) (hz0 : 0 ≤ z) (hzy : z ≤ y) :
    rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) z (TpR θ X₀ ω) -
        rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (TpR θ X₀ ω) =
      thrPart θ X₀ ω y z + rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ (z / y)) +
        rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y)) +
        rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω (z / y)) -
        jzX X₀ * rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (jF X₀ (z / y)) := by
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  rw [rhoSh_eq_elems_of_le hXm hzy (fun u hu => TpR_low hc ω (lt_of_lt_of_le hu hXmX)),
    G1.rhoSh_eq_elems, G1.rhoSh_eq_elems, G1.rhoSh_eq_elems, G1.rhoSh_eq_elems,
    G1.rhoSh_eq_elems]
  unfold thrPart
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  set P := PR θ X₀ ω
  have hv := P.val_pos e
  have hr0 : 0 ≤ z / y := div_nonneg hz0 hy0.le
  have hr1 : z / y ≤ 1 := (div_le_one hy0).mpr hzy
  have key := TpR_sub hc ω hr0 hr1 (y / P.val e)
  have hz : z / y * (y / P.val e) = z / P.val e := by field_simp
  rw [hz] at key
  set cz := cN P (twR θ X₀ ω) (Xm X₀) z (iota e)
  set cy := cN P (twR θ X₀ ω) (Xm X₀) y (iota e)
  have e1 : cz * TpR θ X₀ ω (z / P.val e) / P.val e - cy * TpR θ X₀ ω (y / P.val e) / P.val e
      = (cz - cy) * TpR θ X₀ ω (z / P.val e) / P.val e +
        cy * (TpR θ X₀ ω (z / P.val e) - TpR θ X₀ ω (y / P.val e)) / P.val e := by ring
  rw [e1, key]
  ring

end Dec

end BModel

end
