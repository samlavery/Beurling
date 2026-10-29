module

public import RequestProject.Beurling.Noise.KRTrueSplit
public import RequestProject.Beurling.Noise.KRWeights

/-!
# Proposition 5.18 (true kernels): the dyadic weights

Setting: a Beurling system `P` (levels `n = iota e`, values `V n = val e`, as in
`KRWeights.lean`), a start `x ≥ X₀⁻`, the jitter width `H` with the paper's hypotheses
(`PaperWidth`, `X₀⁻ = X₀ - H(X₀)/2`), a positive decision order `tw`. The true kernels `C_n` use
the filters `1[τ_w < c] 1[c ≥ X₀⁻]` at the actual centre `c` (`gK … (phiT tw X₀⁻)`), the nominal
kernels the same filters at the nominal point (`kapN`). With

  `W^op_x(u) = ∑_{x/n ∈ [u, 2u)} TV(C_n)/n`  (`Wop`; `TV(C_1) = TV(δ_x)`, `TV(C_n) = ∫ |g_n|`),
  `W^{op,nt}_x(u)` the same over non-terminal levels (`WopNT`),

`prop_5_18` proves the first two bounds of Proposition 5.18,

  `W^{op,nt}_x(u) ≤ 2 C_N log(2u)/log x` and `W^op_x(u) ≤ 2 C_N log(2u)/log x` (`u ≥ 2X₀`),

for every scale `u` of a finite family of scales `Sc` covering the levels, by the paper's proof:
the Duhamel form (`Etil_split`), the vanishing of the sources off near steps (Lemma 5.12), the
regrouping of the `τ`-sources by their parents (giving the weight `η̃(x/d)`, `etaT`), and the
fixed point (`fixed_point`). The inputs that are not proved here are named hypotheses:

* `NomWeights` : Corollary 5.17(b) in the form `W^nom_x(u) ≤ C_N log(2u)/log x` at the scales
  (`cor_5_17_b`, `cor_5_17_b_CN` prove it from Corollary 5.9 and the `H_ord` sums);
* `TransferBound` : the first display of step (ii) of the proof: for a `τ`-source at the level
  `n'`, `∑_{x/n ∈ [u,2u)} TV(𝒯^nom_{n'→n} S^τ_{n'})/n ≤ λ₀ TV(S^τ_{n'})/n' · C_N log(2u)/log(x/n')`
  (Theorem 5.15 from the start `v` near `x/n'`, and Corollary 5.17(b) at the start `x/n'`);
* `EtaBound` : the scale upper bounds `η̃ ≤ s_v` on `[v, 2v)`, with `E_η = ∑_v log(2v) s_v` and
  `λ₀ C_N E_η ≤ ½` (Lemma 5.20 and its consequence).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ)

/-- `V n`. -/
noncomputable abbrev Vl (n : ℕ) : ℝ := LemmaM.valN P.labelVal n

/-- `TV(C_n)` of the true kernels. -/
noncomputable def TVt (n : ℕ) : ℝ :=
  if n = 1 then (eVariationOn (stepF x) univ).toReal else
    (∫⁻ t, ‖gK P.labelVal x H (phiT tw X0m) n t‖ₑ).toReal

/-- `TV(C_n^nom)` of the nominal kernels (densities). -/
noncomputable def TVn (n : ℕ) : ℝ :=
  if n = 1 then (eVariationOn (stepF x) univ).toReal else
    (∫⁻ t, ‖gK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) n t‖ₑ).toReal

/-- `TV(𝒯^nom_{n'→n} S^τ_{n'})`. -/
noncomputable def tauPart (n' n : ℕ) : ℝ :=
  (∫⁻ t, ‖Tch P.labelVal H (kapN tw X0m P.labelVal x) n'
    (Stau P.labelVal x H tw X0m n') n t‖ₑ).toReal

/-- The non-`X₀` part of the level `n`: `TV(C_n^nom) + ∑_{n' ∣ n} TV(𝒯_{n'→n} S^τ_{n'})`. -/
noncomputable def aLev (n : ℕ) : ℝ :=
  TVn P H tw X0m x n + ∑ n' ∈ n.divisors.filter (2 ≤ ·), tauPart P H tw X0m x n' n

/-- `W^op_x(u)`. -/
noncomputable def Wop (u : ℝ) : ℝ := ∑ n ∈ NW P x u, TVt P H tw X0m x n / Vl P n

/-- `W^{op,nt}_x(u)`, the non-terminal levels. -/
noncomputable def WopNT (X0 u : ℝ) : ℝ :=
  open scoped Classical in
  ∑ n ∈ (NW P x u).filter (fun n => ¬ Terminal P.labelVal x H X0m X0 n),
    TVt P H tw X0m x n / Vl P n

/-- `A(u) = ∑_{x/n ∈ [u,2u)} a(n)/n`. -/
noncomputable def Aw (u : ℝ) : ℝ := ∑ n ∈ NW P x u, aLev P H tw X0m x n / Vl P n

/-- The cofactors `w ≥ 2` with `v/w ≥ X₀⁻`. -/
noncomputable def Cof (v : ℝ) : Finset ℕ := ((P.elems (v / X0m)).image iota).filter (2 ≤ ·)

/-- `w` is `τ`-near at `v`: `|τ_w - v/w| ≤ 2H(v/w)` and `v/w ≥ X₀⁻`. -/
def TauNearAt (v : ℝ) (m : ℕ) : Prop :=
  |tauW tw m - v / Vl P m| ≤ 2 * H (v / Vl P m) ∧ X0m ≤ v / Vl P m

/-- `η̃(v) = ∑_{w τ-near at v} 1/(w log(v/w))` (Lemma 5.20). -/
noncomputable def etaT (v : ℝ) : ℝ :=
  open scoped Classical in
  ∑ m ∈ (Cof P X0m v).filter (fun m => TauNearAt P H tw X0m v m),
    1 / (Vl P m * Real.log (v / Vl P m))

/-! ## The named inputs -/

/-- **Corollary 5.17(b)** at the scales: `W^nom_x(u) ≤ C_N log(2u)/log x`. -/
def NomWeights (Sc : Finset ℝ) (CN : ℝ) : Prop :=
  ∀ u ∈ Sc, Wnom P H tw X0m x u ≤ CN * Real.log (2 * u) / Real.log x

/-- **The transfer bound** (Proposition 5.18, proof, step (ii), first display): for every
`τ`-source level `n'` (`n' ≥ 2`, `x/n' ≥ X₀⁻`) and scale `u`,
`∑_{x/n ∈ [u,2u)} TV(𝒯^nom_{n'→n} S^τ_{n'})/n ≤ λ₀ TV(S^τ_{n'})/n' · C_N log(2u)/log(x/n')`. -/
def TransferBound (Sc : Finset ℝ) (lam0 CN : ℝ) : Prop :=
  ∀ n', 2 ≤ n' → X0m ≤ posn P.labelVal x n' → ∀ u ∈ Sc,
    ∑ n ∈ NW P x u, tauPart P H tw X0m x n' n / Vl P n ≤
      lam0 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') *
        (CN * Real.log (2 * u) / Real.log (posn P.labelVal x n'))

/-- **Lemma 5.20 at the scales**: `η̃ ≤ s_v` on `[v, 2v)`, `s_v ≥ 0`. -/
def EtaBound (Sc : Finset ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ v ∈ Sc, 0 ≤ s v ∧ ∀ y, v ≤ y → y < 2 * v → etaT P H tw X0m y ≤ s v

/-! ## The fixed point -/

/-- **The fixed point** of step (ii): if `A(u) ≤ C_N L_u/log x + λ₀ C_N L_u ∑_v A(v) s_v` for
every scale `u` (`L_u = log(2u) ≥ 0`), `A, s ≥ 0` and `λ₀ C_N E_η ≤ ½` with
`E_η = ∑_v L_v s_v`, then `A(u) ≤ 2 C_N L_u/log x`. -/
theorem fixed_point (Sc : Finset ℝ) (A s L : ℝ → ℝ) {CN lam0 lx : ℝ} (hCN : 0 ≤ CN)
    (hlam : 0 ≤ lam0) (hlx : 0 < lx) (hA : ∀ v ∈ Sc, 0 ≤ A v) (hs : ∀ v ∈ Sc, 0 ≤ s v)
    (hL : ∀ v ∈ Sc, 0 ≤ L v)
    (hE : lam0 * CN * ∑ v ∈ Sc, L v * s v ≤ 1 / 2)
    (hrec : ∀ u ∈ Sc, A u ≤ CN * L u / lx + lam0 * CN * L u * ∑ v ∈ Sc, A v * s v) :
    ∀ u ∈ Sc, A u ≤ 2 * CN * L u / lx := by
  set E := ∑ v ∈ Sc, L v * s v
  set B := ∑ v ∈ Sc, A v * s v
  have hB : B ≤ CN * E / lx + lam0 * CN * E * B := by
    calc B ≤ ∑ v ∈ Sc, (CN * L v / lx + lam0 * CN * L v * B) * s v :=
          Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hrec v hv) (hs v hv)
      _ = CN * E / lx + lam0 * CN * E * B := by
          simp only [add_mul, Finset.sum_add_distrib]
          have e1 : ∑ v ∈ Sc, CN * L v / lx * s v = CN * E / lx := by
            simp only [E]; rw [Finset.mul_sum, Finset.sum_div]
            exact Finset.sum_congr rfl fun v _ => by ring
          have e2 : ∑ v ∈ Sc, lam0 * CN * L v * B * s v = lam0 * CN * E * B := by
            have : lam0 * CN * E * B = ∑ v ∈ Sc, lam0 * CN * B * (L v * s v) := by
              simp only [E]; rw [← Finset.mul_sum]; ring
            rw [this]; exact Finset.sum_congr rfl fun v _ => by ring
          rw [e1, e2]
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun v hv => mul_nonneg (hA v hv) (hs v hv)
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun v hv => mul_nonneg (hL v hv) (hs v hv)
  have hBle : B ≤ 2 * (CN * E / lx) := by
    have : lam0 * CN * E * B ≤ B / 2 := by nlinarith
    linarith
  intro u hu
  have h1 := hrec u hu
  have h2 : lam0 * CN * L u * B ≤ CN * L u / lx := by
    have hLu := hL u hu
    have : lam0 * CN * L u * B ≤ lam0 * CN * L u * (2 * (CN * E / lx)) :=
      mul_le_mul_of_nonneg_left hBle (by positivity)
    have e : lam0 * CN * L u * (2 * (CN * E / lx)) = 2 * (lam0 * CN * E) * (CN * L u / lx) := by
      ring
    have h3 : 2 * (lam0 * CN * E) * (CN * L u / lx) ≤ 1 * (CN * L u / lx) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have e : 2 * CN * L u / lx = CN * L u / lx + CN * L u / lx := by ring
  rw [e]; linarith

/-! ## The level bounds -/

variable {P H tw X0m x}

lemma toReal_lintegral_le {f g : ℝ → ℝ} {ι : Type*} (s : Finset ι) {h : ι → ℝ → ℝ}
    (hg : Integrable g) (hgm : Measurable g) (hh : ∀ i ∈ s, Integrable (h i))
    (hhm : ∀ i ∈ s, Measurable (h i)) (hf : ∀ t, ‖f t‖ₑ ≤ ‖g t‖ₑ + ∑ i ∈ s, ‖h i t‖ₑ) :
    (∫⁻ t, ‖f t‖ₑ).toReal ≤ (∫⁻ t, ‖g t‖ₑ).toReal + ∑ i ∈ s, (∫⁻ t, ‖h i t‖ₑ).toReal := by
  have hgf : ∫⁻ t, ‖g t‖ₑ ≠ ⊤ := hg.2.ne
  have hhf : ∀ i ∈ s, ∫⁻ t, ‖h i t‖ₑ ≠ ⊤ := fun i hi => (hh i hi).2.ne
  have hle : ∫⁻ t, ‖f t‖ₑ ≤ (∫⁻ t, ‖g t‖ₑ) + ∑ i ∈ s, ∫⁻ t, ‖h i t‖ₑ := by
    calc ∫⁻ t, ‖f t‖ₑ ≤ ∫⁻ t, (‖g t‖ₑ + ∑ i ∈ s, ‖h i t‖ₑ) := lintegral_mono hf
      _ = (∫⁻ t, ‖g t‖ₑ) + ∫⁻ t, ∑ i ∈ s, ‖h i t‖ₑ := lintegral_add_left hgm.enorm _
      _ = (∫⁻ t, ‖g t‖ₑ) + ∑ i ∈ s, ∫⁻ t, ‖h i t‖ₑ := by
          rw [lintegral_finset_sum _ fun i hi => (hhm i hi).enorm]
  have hfin : (∫⁻ t, ‖g t‖ₑ) + ∑ i ∈ s, ∫⁻ t, ‖h i t‖ₑ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hgf, ENNReal.sum_ne_top.mpr hhf⟩
  refine (ENNReal.toReal_mono hfin hle).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hgf (ENNReal.sum_ne_top.mpr hhf), ENNReal.toReal_sum hhf]

lemma tauPart_nonneg (n' n : ℕ) : 0 ≤ tauPart P H tw X0m x n' n := ENNReal.toReal_nonneg

lemma TVn_nonneg (n : ℕ) : 0 ≤ TVn P H tw X0m x n := by
  unfold TVn; split_ifs <;> exact ENNReal.toReal_nonneg

lemma aLev_nonneg (n : ℕ) : 0 ≤ aLev P H tw X0m x n :=
  add_nonneg (TVn_nonneg n) (Finset.sum_nonneg fun _ _ => tauPart_nonneg _ _)

/-- **At non-terminal levels**, `TV(C_n) ≤ TV(C_n^nom) + ∑_{n'} TV(𝒯_{n'→n} S^τ_{n'})`. -/
theorem TVt_le_aLev {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) {n : ℕ} (hT : ¬ Terminal P.labelVal x H X0m X0 n) :
    TVt P H tw X0m x n ≤ aLev P H tw X0m x n := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hH := hP.reg
  unfold TVt aLev TVn
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [if_neg (by norm_num), if_neg (by norm_num), gK_le_one _ _ _ (by norm_num),
        gK_le_one _ _ _ (by norm_num)]
      simp only [enorm_zero, lintegral_zero, ENNReal.toReal_zero, zero_add]
      exact Finset.sum_nonneg fun _ _ => tauPart_nonneg _ _
    · rw [if_pos rfl, if_pos rfl]
      linarith [Finset.sum_nonneg (s := (Nat.divisors 1).filter (2 ≤ ·))
        (fun n' _ => tauPart_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x) n' 1)]
  rw [if_neg (by omega), if_neg (by omega)]
  unfold tauPart
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
  refine toReal_lintegral_le _ (integrable_gK hH (constF_ok hκ) n).1
    (integrable_gK hH (constF_ok hκ) n).2
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 n).1)
    (fun n' _ => (integrable_Tch hH _ n' (integrable_Stau hH n').1
      (integrable_Stau hH n').2 n).2) fun t => ?_
  have e := Etil_split (val := P.labelVal) (x := x) (tw := tw) hP hX0 hval2 hn t
  rw [SX0_eq_zero hP hX0 hval2 hT t, add_zero] at e
  have e2 : gK P.labelVal x H (phiT tw X0m) n t =
      gK P.labelVal x H (constF (kapN tw X0m P.labelVal x)) n t +
        Etil P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) n t := by
    unfold Etil; ring
  rw [e2, e]
  exact (enorm_add_le _ _).trans (add_le_add le_rfl (enorm_sum_le _ _))

/-- `TV(δ_x) ≥ 1`. -/
lemma one_le_eVariationOn_stepF (a : ℝ) : 1 ≤ eVariationOn (stepF a) univ := by
  have := eVariationOn.sum_le (stepF a) 1 (u := fun i => a - 1 + i) (s := univ)
    (fun i j hij => by have : (i : ℝ) ≤ j := by exact_mod_cast hij
                       linarith) (fun _ => mem_univ _)
  simp only [Finset.range_one, Finset.sum_singleton] at this
  norm_num at this
  refine le_trans (le_of_eq ?_) this
  unfold stepF
  rw [if_pos (by linarith), if_neg (by linarith), edist_dist, Real.dist_eq]
  norm_num

lemma toReal_eVariationOn_stepF (a : ℝ) : (eVariationOn (stepF a) univ).toReal = 1 := by
  have h1 := one_le_eVariationOn_stepF a
  have h2 := eVariationOn_stepF_le a
  rw [le_antisymm h2 h1, ENNReal.toReal_one]

/-- `∑_{x/n ∈ [u,2u)} TV(C_n^nom)/n ≤ W^nom_x(u)`. -/
theorem sum_TVn_le_Wnom {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (u : ℝ) :
    ∑ n ∈ NW P x u, TVn P H tw X0m x n / Vl P n ≤ Wnom P H tw X0m x u := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  refine Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_right ?_ (KR.valN_labelVal_pos P n).le
  unfold TVn
  by_cases h1 : n = 1
  · subst h1; rw [if_pos rfl, kN, kerV_one]
  rw [if_neg h1]
  have hn0 : n ≠ 0 := by
    intro h; subst h
    unfold NW at hn
    obtain ⟨e, -, he⟩ := Finset.mem_image.mp hn
    exact (iota_pos e).ne' he
  have hn2 : 2 ≤ n := by omega
  obtain ⟨⟨hTV, -⟩, -⟩ := theorem_5_15_nominal (x := x) hP hval2 ht hlam hx hn2
  have hκ := kapN_mem (tw := tw) (X0m := X0m) P.labelVal x
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTV)
    (lintegral_gK_nom_le hval hP.reg hκ hn2)

/-! ## The `τ`-sources -/

/-- A terminal parent has no source: its children vanish in both families (Lemma 5.12(iii)). -/
lemma srcStep_terminal {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) {d n' : ℕ} (hd : d ∈ n'.properDivisors) (hd1 : d ≠ 1)
    (hT : Terminal P.labelVal x H X0m X0 d) (t : ℝ) :
    srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n' t = 0 := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  unfold srcStep
  rw [if_neg hd1]
  unfold Qd
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n' ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
  simp only [Pi.zero_apply]
  by_cases hg : gK P.labelVal x H (phiT tw X0m) d v = 0
  · rw [hg]; ring
  obtain ⟨hposd, hvd⟩ := hsupp d v hg
  obtain ⟨h1, h2⟩ := near_iii hP hX0 hposd hT hw hvd
  have hφ : phiT tw X0m d n' (v / LemmaM.valN P.labelVal (n' / d)) = 0 := by
    unfold phiT trueFilter; rw [if_neg (fun h => absurd h.2 (not_le.mpr h1))]
  have hk : kapN tw X0m P.labelVal x d n' = 0 := by
    unfold kapN; rw [nomFilter_eq_trueFilter hval]
    unfold trueFilter
    rw [if_neg (fun h => absurd h.2 (not_le.mpr (by rwa [← posn_div hval hdn hn0])))]
  rw [hφ, hk]; ring

/-- The parents of the `τ`-sources: `τ`-near, non-terminal. -/
noncomputable def Dset (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x X0 : ℝ) (n' : ℕ) :
    Finset ℕ :=
  open scoped Classical in
  n'.properDivisors.filter (fun d => TauNear P.labelVal x H tw d n' ∧
    ¬ Terminal P.labelVal x H X0m X0 d)

/-- **The `τ`-source bound** (Proposition 5.18, proof, from (K5)): for `x/n' ≥ X₀⁻`,
`TV(S^τ_{n'}) ≤ ∑_{d → n' τ-near, d non-terminal} a(d)`; and `S^τ_{n'} = 0` if `x/n' < X₀⁻`. -/
theorem Stau_le {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (n' : ℕ) :
    (∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal ≤
      ∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hH := hP.reg
  have hterm : ∀ d ∈ n'.properDivisors.filter (fun d => ¬ X0Near P.labelVal x H X0m d n'),
      ∫⁻ t, ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n' t‖ₑ ≤
        if d ∈ Dset P H tw X0m x X0 n' then ENNReal.ofReal (aLev P H tw X0m x d) else 0 := by
    intro d hd
    obtain ⟨hdm, hXd⟩ := Finset.mem_filter.mp hd
    by_cases h1 : d = 1
    · subst h1
      simp only [srcStep_one hval, enorm_zero, lintegral_zero]; exact zero_le _
    by_cases hD : d ∈ Dset P H tw X0m x X0 n'
    · rw [if_pos hD]
      have hTd : ¬ Terminal P.labelVal x H X0m X0 d := by
        unfold Dset at hD; exact (Finset.mem_filter.mp hD).2.2
      refine (lintegral_srcStep_le hH h1).trans ?_
      have hfin := (integrable_gKT (val := P.labelVal) (x := x) (tw := tw) (X0m := X0m)
        hH d).1.2.ne
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      have := TVt_le_aLev (tw := tw) hP hX0 hp2 hTd
      unfold TVt at this; rwa [if_neg h1] at this
    · rw [if_neg hD]
      unfold Dset at hD
      simp only [Finset.mem_filter, not_and, not_not] at hD
      have hz : ∀ t,
          srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n' t = 0 := by
        intro t
        by_cases hτ : TauNear P.labelVal x H tw d n'
        · exact srcStep_terminal hP hX0 hp2 hdm h1 (hD hdm hτ) t
        · exact srcStep_eq_zero_far hP hval2 hdm hτ hXd t
      simp [hz]
  have hle : ∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ ≤
      ∑ d ∈ n'.properDivisors.filter (fun d => ¬ X0Near P.labelVal x H X0m d n'),
        if d ∈ Dset P H tw X0m x X0 n' then ENNReal.ofReal (aLev P H tw X0m x d) else 0 := by
    calc ∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ
        ≤ ∫⁻ t, ∑ d ∈ n'.properDivisors.filter (fun d => ¬ X0Near P.labelVal x H X0m d n'),
            ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n' t‖ₑ := by
          refine lintegral_mono fun t => ?_
          unfold Stau SsrcP
          rw [enorm_neg]
          convert enorm_sum_le _ _
      _ = ∑ d ∈ n'.properDivisors.filter (fun d => ¬ X0Near P.labelVal x H X0m d n'),
            ∫⁻ t, ‖srcStep P.labelVal x H (phiT tw X0m) (kapN tw X0m P.labelVal x) d n' t‖ₑ :=
          lintegral_finset_sum _ fun d _ => (integrable_srcStep hH d n').2.enorm
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsum : (∑ d ∈ n'.properDivisors.filter (fun d => ¬ X0Near P.labelVal x H X0m d n'),
      if d ∈ Dset P H tw X0m x X0 n' then ENNReal.ofReal (aLev P H tw X0m x d) else 0) ≤
      ENNReal.ofReal (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun d _ => aLev_nonneg d, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro _ _ _; exact zero_le _
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg fun d _ => aLev_nonneg d)
    (hle.trans hsum)

/-! ## Regrouping by the parents -/

lemma etaT_term_nonneg (hXm1 : 1 < X0m) {v : ℝ} {m : ℕ} (hm : m ∈ Cof P X0m v) :
    0 ≤ 1 / (Vl P m * Real.log (v / Vl P m)) := by
  have hV := KR.valN_labelVal_pos P m
  have hm' := (Finset.mem_filter.mp hm).1
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm'
  rw [mem_elems] at he
  have hX : 0 < X0m := by linarith
  have h1 : X0m ≤ v / Vl P (iota e) := by
    unfold Vl; rw [P.valN_iota, le_div_iff₀ (P.val_pos e)]
    rw [le_div_iff₀ hX] at he; linarith
  have h2 : 0 < Real.log (v / Vl P (iota e)) := Real.log_pos (by linarith)
  positivity

lemma etaT_nonneg (hXm1 : 1 < X0m) (v : ℝ) : 0 ≤ etaT P H tw X0m v := by
  classical
  unfold etaT
  exact Finset.sum_nonneg fun m hm => etaT_term_nonneg hXm1 (Finset.mem_filter.mp hm).1

lemma posn_ge_of_mem_NAll {n : ℕ} (hn : n ∈ NAll P x X0m) (hX : 0 < X0m) :
    X0m ≤ posn P.labelVal x n := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
  rw [mem_elems] at he
  unfold posn; rw [P.valN_iota, le_div_iff₀ (P.val_pos e)]
  rw [le_div_iff₀ hX] at he; linarith

lemma mem_NAll_of_posn {n : ℕ} (hn : n ≠ 0) (hX : 0 < X0m)
    (h : X0m ≤ posn P.labelVal x n) : n ∈ NAll P x X0m := by
  apply KR.mem_image_iota P hn
  have hV := KR.valN_labelVal_pos P n
  unfold posn at h
  rw [le_div_iff₀ hV] at h
  rw [le_div_iff₀ hX]; linarith

/-- **Regrouping by the parents**: with `n' = d w`,
`∑_{n'} (∑_{d → n' τ-near} a(d))/(n' log(x/n')) ≤ ∑_d (a(d)/d) η̃(x/d)`. -/
theorem regroup {X0 : ℝ} (hp2 : ∀ j, 2 ≤ P.p j) (hXm1 : 1 < X0m) :
    ∑ n' ∈ (NAll P x X0m).filter (2 ≤ ·),
        (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) / Vl P n' /
          Real.log (posn P.labelVal x n') ≤
      ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * etaT P H tw X0m (posn P.labelVal x d) := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX : 0 < X0m := by linarith
  set Src := (NAll P x X0m).filter (2 ≤ ·)
  set F : ℕ → ℕ → ℝ := fun n' d =>
    aLev P H tw X0m x d / (Vl P n' * Real.log (posn P.labelVal x n'))
  have e1 : ∀ n' ∈ Src, (∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) / Vl P n' /
      Real.log (posn P.labelVal x n') = ∑ d ∈ Dset P H tw X0m x X0 n', F n' d := by
    intro n' _
    rw [div_div, Finset.sum_div]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := NAll P x X0m)
    (s' := fun d => Src.filter (fun n' => d ∈ Dset P H tw X0m x X0 n'))]
  · refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : d ≠ 0 := by
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hd; exact (iota_pos e).ne'
    have hVd := KR.valN_labelVal_pos P d
    set T := (Cof P X0m (posn P.labelVal x d)).filter
      (fun m => TauNearAt P H tw X0m (posn P.labelVal x d) m)
    set g : ℕ → ℝ := fun m => 1 / (Vl P m * Real.log (posn P.labelVal x d / Vl P m))
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
      refine ⟨?_, ?_, hdn⟩
      · simp only [F, g]; rw [hpp, hVV]; field_simp
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hm2⟩, ?_⟩
        · apply KR.mem_image_iota P (by omega)
          have hVm := KR.valN_labelVal_pos P (n' / d)
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
            exact mul_nonneg (div_nonneg (aLev_nonneg d) hVd.le)
              (etaT_term_nonneg hXm1 (Finset.mem_filter.mp hm).1)
      _ = aLev P H tw X0m x d / Vl P d * etaT P H tw X0m (posn P.labelVal x d) := by
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

/-- **Covering by the scales**: `∑_d (a(d)/d) η̃(x/d) ≤ ∑_v A(v) s_v`. -/
theorem cover_sum {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hEta : EtaBound P H tw X0m Sc s) :
    ∑ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d * etaT P H tw X0m (posn P.labelVal x d) ≤
      ∑ v ∈ Sc, Aw P H tw X0m x v * s v := by
  classical
  set G : ℕ → ℝ → ℝ := fun d v => aLev P H tw X0m x d / Vl P d * s v
  have hstep : ∀ d ∈ NAll P x X0m, aLev P H tw X0m x d / Vl P d *
      etaT P H tw X0m (posn P.labelVal x d) ≤ ∑ v ∈ Sc.filter (fun v => d ∈ NW P x v), G d v := by
    intro d hd
    obtain ⟨v, hv, hdv⟩ := hcov d hd
    have hmem : v ∈ Sc.filter (fun v => d ∈ NW P x v) := Finset.mem_filter.mpr ⟨hv, hdv⟩
    have hVd := KR.valN_labelVal_pos P d
    have ha := div_nonneg (aLev_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (x := x) d)
      hVd.le
    calc aLev P H tw X0m x d / Vl P d * etaT P H tw X0m (posn P.labelVal x d) ≤ G d v := by
          simp only [G]
          apply mul_le_mul_of_nonneg_left _ ha
          obtain ⟨-, hy⟩ := hEta v hv
          obtain ⟨-, h1, h2⟩ := (mem_NW P (hSc v hv)).mp hdv
          exact hy _ h1 h2
      _ ≤ ∑ v ∈ Sc.filter (fun v => d ∈ NW P x v), G d v :=
          Finset.single_le_sum (f := fun v => G d v)
            (fun w hw => mul_nonneg ha (hEta w (Finset.mem_filter.mp hw).1).1) hmem
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_comm' (t' := Sc) (s' := fun v => (NAll P x X0m).filter (fun d => d ∈ NW P x v))]
  · refine Finset.sum_le_sum fun v hv => ?_
    unfold Aw
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd; exact (Finset.mem_filter.mp hd).2
    · intro d _ _
      exact mul_nonneg (div_nonneg (aLev_nonneg d) (KR.valN_labelVal_pos P d).le)
        (hEta v hv).1
  · intro d v
    simp only [Finset.mem_filter]
    tauto

/-! ## The recursion for `A(u)` and Proposition 5.18 -/

lemma Stau_eq_zero_low {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    {n' : ℕ} (hlow : posn P.labelVal x n' < X0m) (t : ℝ) :
    Stau P.labelVal x H tw X0m n' t = 0 := by
  classical
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  unfold Stau SsrcP
  rw [Finset.sum_eq_zero fun d hd => ?_, neg_zero]
  obtain ⟨hdm, hXd⟩ := Finset.mem_filter.mp hd
  exact srcStep_eq_zero_low hP hval2 hdm hXd hlow t

lemma tauPart_eq_zero_low {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    {n' : ℕ} (hlow : posn P.labelVal x n' < X0m) (n : ℕ) :
    tauPart P H tw X0m x n' n = 0 := by
  unfold tauPart
  rw [Tch_congr _ n' (fun t => Stau_eq_zero_low (tw := tw) hP hp2 hlow t), Tch_zero_fun]
  simp

/-- **The recursion** (Proposition 5.18, proof, step (ii)):
`A(u) ≤ W^nom_x(u) + λ₀ C_N log(2u) ∑_v A(v) s_v`. -/
theorem Aw_rec {X0 ε θ lam0 CN : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hx : X0m ≤ x) (hXm1 : 1 < X0m) (hCN : 0 ≤ CN) {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc : ∀ v ∈ Sc, 0 < v)
    (hEta : EtaBound P H tw X0m Sc s) (hTr : TransferBound P H tw X0m x Sc lam0 CN)
    {u : ℝ} (hu : u ∈ Sc) (hu1 : 1 / 2 ≤ u) :
    Aw P H tw X0m x u ≤ Wnom P H tw X0m x u +
      lam0 * CN * Real.log (2 * u) * ∑ v ∈ Sc, Aw P H tw X0m x v * s v := by
  classical
  have hX : 0 < X0m := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hLu : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  set Src := (NAll P x X0m).filter (2 ≤ ·)
  have hsplit : Aw P H tw X0m x u = ∑ n ∈ NW P x u, TVn P H tw X0m x n / Vl P n +
      ∑ n ∈ NW P x u, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
        tauPart P H tw X0m x n' n / Vl P n := by
    unfold Aw aLev
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_div, Finset.sum_div]
  rw [hsplit]
  refine add_le_add (sum_TVn_le_Wnom hP hp2 ht hlam hx u) ?_
  -- move the sources to `Src`
  have h1 : ∀ n ∈ NW P x u, ∑ n' ∈ n.divisors.filter (2 ≤ ·),
      tauPart P H tw X0m x n' n / Vl P n ≤
      ∑ n' ∈ Src, tauPart P H tw X0m x n' n / Vl P n := by
    intro n hn
    rw [← Finset.sum_filter_of_ne (p := fun n' => n' ∈ Src) (s := n.divisors.filter (2 ≤ ·))]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n' hn'; exact (Finset.mem_filter.mp hn').2
      · intro n' _ _
        exact div_nonneg (tauPart_nonneg _ _) (KR.valN_labelVal_pos P n).le
    · intro n' hn' hne
      refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hn').2⟩
      have hn'0 : n' ≠ 0 := by have := (Finset.mem_filter.mp hn').2; omega
      apply mem_NAll_of_posn hn'0 hX
      by_contra hlow; push_neg at hlow
      exact hne (by rw [tauPart_eq_zero_low hP hp2 hlow n, zero_div])
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_comm]
  -- the transfer bound, then the source bound
  have h2 : ∀ n' ∈ Src, ∑ n ∈ NW P x u, tauPart P H tw X0m x n' n / Vl P n ≤
      lam0 * CN * Real.log (2 * u) * ((∑ d ∈ Dset P H tw X0m x X0 n', aLev P H tw X0m x d) /
        Vl P n' / Real.log (posn P.labelVal x n')) := by
    intro n' hn'
    obtain ⟨hn'A, hn'2⟩ := Finset.mem_filter.mp hn'
    have hpos := posn_ge_of_mem_NAll hn'A hX
    have hlog : 0 < Real.log (posn P.labelVal x n') := Real.log_pos (by linarith)
    have hVn := KR.valN_labelVal_pos P n'
    refine (hTr n' hn'2 hpos u hu).trans ?_
    have hS := Stau_le (tw := tw) (x := x) hP hX0 hp2 n'
    have hS0 : 0 ≤ (∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal := ENNReal.toReal_nonneg
    have e : lam0 * ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n') *
        (CN * Real.log (2 * u) / Real.log (posn P.labelVal x n')) =
        lam0 * CN * Real.log (2 * u) *
          ((∫⁻ t, ‖Stau P.labelVal x H tw X0m n' t‖ₑ).toReal / Vl P n' /
            Real.log (posn P.labelVal x n')) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ hlog.le
    exact div_le_div_of_nonneg_right hS hVn.le
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (regroup hp2 hXm1).trans (cover_sum hcov hSc hEta)

/-- **The fixed point of Proposition 5.18**: `A(u) ≤ 2 C_N log(2u)/log x` at every scale. -/
theorem Aw_le {X0 ε θ lam0 CN : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hXm1 : 1 < X0m) (hCN : 0 ≤ CN)
    {Sc : Finset ℝ} {s : ℝ → ℝ} (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hSc : ∀ v ∈ Sc, 1 / 2 ≤ v) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hNom : NomWeights P H tw X0m x Sc CN) (hTr : TransferBound P H tw X0m x Sc lam0 CN) :
    ∀ u ∈ Sc, Aw P H tw X0m x u ≤ 2 * CN * Real.log (2 * u) / Real.log x := by
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc v hv]
  have hfix := fixed_point Sc (Aw P H tw X0m x) s (fun v => Real.log (2 * v)) hCN hlam0 hlx
    (fun v _ => Finset.sum_nonneg fun n _ =>
      div_nonneg (aLev_nonneg n) (KR.valN_labelVal_pos P n).le)
    (fun v hv => (hEta v hv).1) (fun v hv => Real.log_nonneg (by linarith [hSc v hv])) hE
    (fun u hu => by
      have := Aw_rec (X0 := X0) hP hX0 hp2 ht hlam hx hXm1 hCN hcov hSc0 hEta hTr hu (hSc u hu)
      have h2 := hNom u hu
      rw [mul_div_assoc] at h2 ⊢
      linarith)
  intro u hu
  simpa only [mul_div_assoc] using hfix u hu

lemma WopNT_le_Aw {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (u : ℝ) : WopNT P H tw X0m x X0 u ≤ Aw P H tw X0m x u := by
  classical
  unfold WopNT Aw
  calc ∑ n ∈ (NW P x u).filter (fun n => ¬ Terminal P.labelVal x H X0m X0 n),
        TVt P H tw X0m x n / Vl P n
      ≤ ∑ n ∈ (NW P x u).filter (fun n => ¬ Terminal P.labelVal x H X0m X0 n),
          aLev P H tw X0m x n / Vl P n :=
        Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_right
          (TVt_le_aLev hP hX0 hp2 (Finset.mem_filter.mp hn).2) (KR.valN_labelVal_pos P n).le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun n _ _ => div_nonneg (aLev_nonneg n) (KR.valN_labelVal_pos P n).le

/-- **Proposition 5.18 (true kernels), the first two bounds.** Under the paper's hypotheses on
`H` and the named inputs (`NomWeights`: Corollary 5.17(b); `TransferBound`: step (ii) of the
proof; `EtaBound` and `λ₀ C_N E_η ≤ ½`: Lemma 5.20), for every scale `u` of a family `Sc`
covering the levels with `x/n ≥ X₀⁻`,

* `W^{op,nt}_x(u) ≤ 2 C_N log(2u)/log x`, and
* `W^op_x(u) ≤ 2 C_N log(2u)/log x` if `u ≥ 2X₀` (there are no terminal levels there). -/
theorem prop_5_18 {X0 ε θ lam0 CN : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hXm1 : 1 < X0m) (hCN : 0 ≤ CN)
    {Sc : Finset ℝ} {s : ℝ → ℝ} (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hSc : ∀ v ∈ Sc, 1 / 2 ≤ v) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hNom : NomWeights P H tw X0m x Sc CN) (hTr : TransferBound P H tw X0m x Sc lam0 CN) :
    ∀ u ∈ Sc, WopNT P H tw X0m x X0 u ≤ 2 * CN * Real.log (2 * u) / Real.log x ∧
      (2 * X0 ≤ u → Wop P H tw X0m x u ≤ 2 * CN * Real.log (2 * u) / Real.log x) := by
  classical
  have hSc0 : ∀ v ∈ Sc, 0 < v := fun v hv => by linarith [hSc v hv]
  have hA := Aw_le hP hX0 hp2 ht hlam hx hXm1 hCN hcov hSc hEta hE hNom hTr
  intro u hu
  refine ⟨(WopNT_le_Aw hP hX0 hp2 u).trans (hA u hu), fun h2X => ?_⟩
  have heq : Wop P H tw X0m x u = WopNT P H tw X0m x X0 u := by
    unfold Wop WopNT
    rw [Finset.filter_true_of_mem]
    intro n hn
    obtain ⟨-, h1, -⟩ := (mem_NW P (hSc0 u hu)).mp hn
    unfold Terminal posn
    have hHX := hP.small X0 (by linarith [hP.reg.pos X0])
    have hH0 := hP.reg.pos X0
    push_neg
    linarith
  rw [heq]
  exact (WopNT_le_Aw hP hX0 hp2 u).trans (hA u hu)

end KR

end
