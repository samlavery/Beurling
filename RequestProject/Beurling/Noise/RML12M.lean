module

public import RequestProject.Beurling.Noise.RML11S4
public import RequestProject.Beurling.Noise.KRNormHarm

/-!
# Proposition 5.38, Steps 2–4 with a height-dependent bound `m*(z)` on the margin density

The paper (04g-margin.tex, Step 2, "Strips") uses the **local** bound
`m*(z) := sup_{|y - z| ≤ 2H} |m(y)| ≤ 3.1 log z + 4.2` (from `|T'| ≤ 2`,
`0 ≤ K_pt ρ̃(y) ≤ 1.01 ∑_{2 ≤ w ≤ y/X₀⁻} 1/w ≤ 1.01 log y` and `|NT_pt(y)| ≤ 2.02(log y + 1)`).
It is a function of `z`, not of the event time `b`. `RML10` instantiated the field `s2mst` by a
constant `M`; a constant valid on the whole range `z ≤ b` grows like `log b`, which makes the
Step 3 weight `(6.6 + 4.2 m*)/H(z)` non-uniform in `b`.

This file restates the Step 2–4 field theorems of `RML10`/`RML11` for an arbitrary
height-dependent bound `Mf : ℝ → ℝ` (`s2mst := Mf`), assumed non-negative and non-decreasing:

* `fE12`, `e12` : the Step 3 weight and its supremum over the strip of `(t, w)`;
* `hS2e_12`, `he0_12` : the fields `hS2e`, `he0` at `s2mst = Mf`, `e = e12 X₀ P Mf`;
* `hS2sp_12`, `hS2sm_12` : the fields `hS2sp`, `hS2sm` from `|m| ≤ Mf z` on `[z ± 3H(z)]`;
* `hS4_12` : the field `hS4` at `e = e12` (from the Step 4 bound), and `S4At12`, `hS4_12'` (the
  `RML11.hS4_11` form, through `Margin.RML6.hS4_of`);
* `Mterm_le`, `Mterm_div_le` : for the paper-type bound `Mf z ≤ 4 + 2 log(2(z + 3H(z))/X₀⁻)`,
  `(6.6 + 4.2 Mf z)/H(z) ≤ (23.4 + 8.4 log(8z))/H(z)`, uniformly in `b`;
* `harmBound_le`, `harmBound_mono` : `2 + 2 ∑_{n ∈ 𝒩, n ≤ X} 1/n ≤ 2 + 2(log X + 1)` for
  `1 ≤ X ≤ Z` under (HBS) (`HBS.harm_le`), and monotonicity in `X`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML12M

variable {X₀ : ℕ}

variable (X₀) in
/-- The Step 3 weight of the field `hS2e` at `s2mst = Mf`. -/
noncomputable def fE12 (Mf : ℝ → ℝ) (z : ℝ) : ℝ :=
  2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) +
    210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 + (6.6 + 4.2 * Mf z) / Queue6.Hc X₀ z

variable (X₀) in
/-- **The recursion weight** `e(t, w) = sup_{z' ∈ strip(t/w)} fE12(z')`. -/
noncomputable def e12 (P : BeurlingSystem) (Mf : ℝ → ℝ) (t : ℝ) (w : ℕ) : ℝ :=
  sSup (fE12 X₀ Mf '' RML10.strip X₀ (t / KR.Vl P w))

section Bounds

variable (hX : 10 ^ 8 ≤ Real.log X₀) {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z) (hMm : Monotone Mf)
include hX hM0

lemma fE12_nonneg (z : ℝ) : 0 ≤ fE12 X₀ Mf z := by
  unfold fE12
  have h1 := RML10.s2E3_nonneg (X₀ := X₀) (RML10.one_le_uS hX (m1z X₀ z))
  have h2 := RML10.s2E3_nonneg (X₀ := X₀) (RML10.one_le_uS hX (m1z X₀ z + 1))
  have h3 : 0 ≤ 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 := by positivity
  have h4 : 0 ≤ (6.6 + 4.2 * Mf z) / Queue6.Hc X₀ z :=
    div_nonneg (by linarith [hM0 z]) (by linarith [RML10.Hc_ge_one hX z])
  linarith

include hMm in
lemma fE12_le {z c : ℝ} (hzc : z ≤ c) :
    fE12 X₀ Mf z ≤ 4.4 * (9 * Real.log (2 * max c X₀)) + 210 / Real.log X₀ ^ 6 +
      (6.6 + 4.2 * Mf c) := by
  have h0 := RML10.fE_le hX (hM0 z) hzc
  unfold RML10.fE at h0
  unfold fE12
  have hm := hMm hzc
  linarith

include hMm in
lemma bdd_fE12 (c : ℝ) : BddAbove (fE12 X₀ Mf '' RML10.strip X₀ c) := by
  refine ⟨4.4 * (9 * Real.log (2 * max c X₀)) + 210 / Real.log X₀ ^ 6 + (6.6 + 4.2 * Mf c), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact fE12_le hX hM0 hMm hz.2

include hMm in
lemma fE12_le_e12 (P : BeurlingSystem) (t : ℝ) (w : ℕ) {z : ℝ}
    (hz : z ∈ RML10.strip X₀ (t / KR.Vl P w)) : fE12 X₀ Mf z ≤ e12 X₀ P Mf t w :=
  le_csSup (bdd_fE12 hX hM0 hMm _) (mem_image_of_mem _ hz)

include hMm in
lemma e12_nonneg (P : BeurlingSystem) (t : ℝ) (w : ℕ) : 0 ≤ e12 X₀ P Mf t w := by
  have hc : t / KR.Vl P w ∈ RML10.strip X₀ (t / KR.Vl P w) := by
    refine ⟨?_, le_rfl⟩
    have := RML10.Hc_ge_one hX (t / KR.Vl P w); linarith
  exact (fE12_nonneg hX hM0 _).trans (fE12_le_e12 hX hM0 hMm P t w hc)

end Bounds

variable {θ : ℝ}

/-- **The field `hS2e`** of `RestMargin`, at `s2mst = Mf` and `e = e12 X₀ (PR θ X₀ ω) Mf`. -/
theorem hS2e_12 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z)
    (hMm : Monotone Mf) (ES jP b : ℝ) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω)
        (RML7.canonP X₀ epsH ES jP) t, ∀ z',
      t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
        z' ≤ t / KR.Vl (PR θ X₀ ω) w → (fun z => 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀
          (uS X₀ (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 +
            (6.6 + 4.2 * Mf z) / Queue6.Hc X₀ z) z' ≤
          e12 X₀ (PR θ X₀ ω) Mf t w := by
  intro t _ _ w _ z' h1 h2
  exact fE12_le_e12 hX hM0 hMm _ t w ⟨h1, h2⟩

/-- **The field `he0`** of `RestMargin`, at `e = e12 X₀ (PR θ X₀ ω) Mf`. -/
theorem he0_12 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z)
    (hMm : Monotone Mf) (ES jP b : ℝ) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω)
        (RML7.canonP X₀ epsH ES jP) t, 0 ≤ e12 X₀ (PR θ X₀ ω) Mf t w :=
  fun t _ _ w _ => e12_nonneg hX hM0 hMm _ t w

/-- **The field `hS2sp`** of `RestMargin` at `s2mst = Mf`, from integrability of `m` and
`|m| ≤ Mf z` on `[z - 3H(z), z + 3H(z)]` at the strip points (Model: the local bound on the
margin density, the paper's `m*(z) ≤ 3.1 log z + 4.2`). -/
theorem hS2sp_12 (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hS : KR.WidthReal.CapHSlope X₀ ε) (ω : JitterΩ) {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z)
    (ES jP b : ℝ)
    (hm : ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z →
      IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z), |marginM θ X₀ ω x| ≤ Mf z) :
    ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
      |(∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
        ∫ r in (z + Queue6.Hc X₀ z / 2)..(z + Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
        1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * Mf z := by
  intro z hz s hs0 hs
  obtain ⟨hi, hb⟩ := hm z hz
  exact ((RML10.widthH_Hc hX hε0 hε1 hS).strip_cmp_plus hs0 hs hi hb).trans
    (RML10.s2δ_mul z (Mf z) hX (hM0 z))

/-- **The field `hS2sm`** of `RestMargin` at `s2mst = Mf` (as `hS2sp_12`). -/
theorem hS2sm_12 (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hS : KR.WidthReal.CapHSlope X₀ ε) (ω : JitterΩ) {Mf : ℝ → ℝ} (hM0 : ∀ z, 0 ≤ Mf z)
    (ES jP b : ℝ)
    (hm : ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z →
      IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z), |marginM θ X₀ ω x| ≤ Mf z) :
    ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
      |(∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
        ∫ r in (z - Queue6.Hc X₀ z / 2)..(z - Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
        1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * Mf z := by
  intro z hz s hs0 hs
  obtain ⟨hi, hb⟩ := hm z hz
  exact ((RML10.widthH_Hc hX hε0 hε1 hS).strip_cmp_minus hs0 hs hi hb).trans
    (RML10.s2δ_mul z (Mf z) hX (hM0 z))

/-- **The field `hS4`** of `RestMargin` at `e = e12 X₀ (PR θ X₀ ω) Mf`, from the Step 4 bound
at every `t ∈ [T₀, b]`. -/
theorem hS4_12 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {Mf : ℝ → ℝ} (ES jP b : ℝ)
    (h4 : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t +
        ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
          e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w) ≤ ES) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t + ∑ w ∈ Margin.Rec.Fset
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t, e12 X₀ (PR θ X₀ ω) Mf t w /
          KR.Vl (PR θ X₀ ω) w ≤ (RML7.canonP X₀ epsH ES jP).ES / Real.log t := by
  intro t ht htb
  have h1 := RML10.T0_gt_one hX ES jP
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  rw [show (RML7.canonP X₀ epsH ES jP).ES = ES from rfl, le_div_iff₀ hl, mul_comm]
  exact h4 t ht htb

/-- **The Step 4 data at a height `t`**, as `RML11.S4At`, with the weights `e12` at
`s2mst = Mf`. -/
structure S4At12 (ω : JitterΩ) (Mf : ℝ → ℝ) (ES jP Z t : ℝ) : Type where
  Vs : Finset ℝ
  ν : ℝ → ℝ
  δ : ℝ → ℝ
  o : ℝ
  η : ℝ
  so : ℝ
  sη : ℝ
  /-- the scales: `v > 0`, `log 3v ≥ 10⁸`, `t/v ≤ Z` (the (HBS) horizon of Lemma 5.21) -/
  hv : ∀ v ∈ Vs, 0 < v ∧ 100000000 ≤ Real.log (3 * v) ∧ t / v ≤ Z
  hν : ∀ v ∈ Vs, 0 ≤ ν v
  hδ : ∀ v ∈ Vs, 0 ≤ δ v
  ho : Real.log t * o ≤ so
  hη : Real.log t * η ≤ sη
  /-- the Step 4 decomposition (Queue6: Lemma 5.22 on the windows) -/
  hS : (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t +
      ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
        e12 X₀ (PR θ X₀ ω) Mf t w / KR.Vl (PR θ X₀ ω) w ≤
      o + 2 * η + 4 * ∑ v ∈ Vs, (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v * ν v +
        1.0001 * ∑ v ∈ Vs, (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v * δ v
  /-- the size of Step 4 -/
  hES : so + 2 * sη + 27 * ∑ v ∈ Vs, Real.log (3 * v) * ν v +
      4.3 * ∑ v ∈ Vs, Real.log (3 * v) * δ v ≤ ES

/-- **The field `hS4`** of `RestMargin` at `e = e12 X₀ (PR θ X₀ ω) Mf`, through
`Margin.RML6.hS4_of` (Lemma 5.21 proved: `Margin.Var.logt_omega_le`). -/
theorem hS4_12' (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {Mf : ℝ → ℝ} (ES jP b : ℝ)
    {Z η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT)
    (D : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → S4At12 (θ := θ) (X₀ := X₀) ω Mf ES jP Z t) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t + ∑ w ∈ Margin.Rec.Fset
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t, e12 X₀ (PR θ X₀ ω) Mf t w /
          KR.Vl (PR θ X₀ ω) w ≤ (RML7.canonP X₀ epsH ES jP).ES / Real.log t := by
  intro t ht htb
  have h1 := RML10.T0_gt_one hX ES jP
  have ht1 : 1 < t := by linarith
  set d := D t ht htb
  have hω : ∀ v ∈ d.Vs, Real.log t *
      (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v ≤ 2.9 * Real.log (3 * v) := by
    intro v hv
    obtain ⟨hv0, hL, hZ⟩ := d.hv v hv
    exact Margin.Var.logt_omega_le htnp.hbs (KR.RML7G.decidedSmall_of htnp hv0) hv0 hL
      (by linarith) hZ
  exact Margin.RML6.hS4_of d.Vs
    (fun v => (PR θ X₀ ω).omegaW (KR.RML7G.tI (twR θ X₀ ω)) t v) d.ν d.δ ht1 d.ho d.hη
    d.hν d.hδ (fun v _ => RML11.omegaW_nonneg _ _ _ _) hω d.hS d.hES

/-! ## Uniformity in `b` of the `m*`-term -/

/-- For the paper-type bound `Mf z ≤ 4 + 2 log(2(z + 3H(z))/X₀⁻)` (with `1 ≤ X₀⁻`,
`H(z) ≤ z`): `6.6 + 4.2 Mf z ≤ 23.4 + 8.4 log(8z)`, independent of the event time. -/
lemma Mterm_le {X0m z H m : ℝ} (hXm : 1 ≤ X0m) (hz : 1 ≤ z) (hH0 : 0 ≤ H) (hHz : H ≤ z)
    (hm : m ≤ 4 + 2 * Real.log (2 * (z + 3 * H) / X0m)) :
    6.6 + 4.2 * m ≤ 23.4 + 8.4 * Real.log (8 * z) := by
  have hpos : 0 < 2 * (z + 3 * H) / X0m := by positivity
  have hle : 2 * (z + 3 * H) / X0m ≤ 8 * z := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hlog := Real.log_le_log hpos hle
  nlinarith

/-- The `m*`-term of the Step 3 weight, `(6.6 + 4.2 Mf z)/H(z) ≤ (23.4 + 8.4 log(8z))/H(z)` for
the paper-type bound, uniformly in the event time `b`. -/
lemma Mterm_div_le {X0m z H m : ℝ} (hXm : 1 ≤ X0m) (hz : 1 ≤ z) (hH1 : 1 ≤ H) (hHz : H ≤ z)
    (hm : m ≤ 4 + 2 * Real.log (2 * (z + 3 * H) / X0m)) :
    (6.6 + 4.2 * m) / H ≤ (23.4 + 8.4 * Real.log (8 * z)) / H :=
  div_le_div_of_nonneg_right (Mterm_le hXm hz (by linarith) hHz hm) (by linarith)

/-! ## The harmonic bound for a candidate `m*` -/

/-- Monotonicity of `X ↦ ∑_{n ∈ 𝒩, n ≤ X} 1/n`. -/
lemma harmBound_mono (P : BeurlingSystem) {X Y : ℝ} (hXY : X ≤ Y) :
    2 + 2 * ∑ e ∈ P.elems X, 1 / P.val e ≤ 2 + 2 * ∑ e ∈ P.elems Y, 1 / P.val e := by
  have : ∑ e ∈ P.elems X, 1 / P.val e ≤ ∑ e ∈ P.elems Y, 1 / P.val e :=
    Finset.sum_le_sum_of_subset_of_nonneg (P.elems_mono hXY)
      (fun e _ _ => (one_div_pos.mpr (P.val_pos e)).le)
  linarith

/-- **The candidate `m*` under (HBS)**: `2 + 2 ∑_{n ∈ 𝒩, n ≤ X} 1/n ≤ 2 + 2(log X + 1)` for
`1 ≤ X ≤ Z` (`HBS.harm_le`); with `X = 2(z + 3H(z))/X₀⁻` this is `≤ 4 + 2 log(2(z+3H)/X₀⁻)`,
the hypothesis of `Mterm_le`. -/
lemma harmBound_le {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) :
    2 + 2 * ∑ e ∈ P.elems X, 1 / P.val e ≤ 4 + 2 * Real.log X := by
  have := h.harm_le hX hXZ
  linarith

end BModel.RML12M

end
