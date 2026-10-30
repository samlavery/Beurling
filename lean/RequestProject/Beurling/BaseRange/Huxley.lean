module

public import RequestProject.Beurling.Model.Slope

/-!
# §7.1: the short-interval prime number theorem and the threshold `X_Hux` (eq. (84))

The paper defines, for `q ≥ 2` (eq. (84), `eq:huxley`),

  `η_H(q) = sup {|π(I)/∫_I dt/log t - 1| : I ⊂ [q, 2q] an interval, |I| ≥ (2q)^{7/12}}`,
  `X_Hux = min {X ≥ e^{10⁸} : η_H(q) ≤ (log q)^{-3} for all q ≥ X}`,

and proves that `X_Hux` is finite from Heath-Brown's theorem [HB88, Theorem, (1.2)] (eq. (83),
`eq:HB`) and the de la Vallée Poussin error term. Neither theorem is in Mathlib, so the
finiteness of `X_Hux` is the **named hypothesis** `Huxley84` below, a statement about the
rational primes only. It is the full two-sided relative bound (84); the lower half is the
hypothesis `BModel.ShortIntervalPNT` already used by the construction (Lemma 3.3).

Intervals are closed, `I = [a, b]`.

* `etaH`, `XHux` : the paper's `η_H` and `X_Hux`;
* `HuxleyFrom X` : `η_H(q) ≤ (log q)^{-3}` for every `q ≥ X`, written interval by interval;
  `huxleyFrom_iff_etaH` : the two forms agree (for `X ≥ 2`);
* `Huxley84` : the named hypothesis `∃ X, HuxleyFrom X` (eq. (84), Heath-Brown + dVP);
* `huxleyFrom_of_XHux_lt`, `XHux_le`, `exp_le_XHux` : `X_Hux` is the threshold;
* `count_ge`, `count_le` : `(1 ∓ (log q)^{-3}) ∫_I dt/log t` bounds for `π(I)`;
* `shortIntervalPNTFrom_of_huxleyFrom`, `shortIntervalPNT_of_huxley84` : (84) implies the
  form `BModel.ShortIntervalPNT` used in Lemma 3.3.
-/

@[expose] public section

open Real MeasureTheory Set Filter

namespace BaseRange

/-- `π(I)` for `I = [a, b]`: the number of rational primes `p` with `a ≤ p ≤ b`. -/
noncomputable def primeCount (a b : ℝ) : ℕ := {p : ℕ | p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b}.ncard

/-- `∫_a^b dt/log t`. -/
noncomputable def liI (a b : ℝ) : ℝ := ∫ t in a..b, 1 / Real.log t

/-- The intervals `I = [a, b] ⊂ [q, 2q]` with `|I| ≥ (2q)^{7/12}` of (84). -/
def Admissible (q a b : ℝ) : Prop := q ≤ a ∧ b ≤ 2 * q ∧ (2 * q) ^ (7 / 12 : ℝ) ≤ b - a

/-- The relative error `|π(I)/∫_I dt/log t - 1|` of the interval `[a, b]`. -/
noncomputable def relErr (a b : ℝ) : ℝ := |(primeCount a b : ℝ) / liI a b - 1|

/-- `η_H(q)` of (84). -/
noncomputable def etaH (q : ℝ) : ℝ := sSup {e | ∃ a b, Admissible q a b ∧ e = relErr a b}

/-- (84) from `X` on: `η_H(q) ≤ (log q)^{-3}` for every `q ≥ X`, interval by interval. -/
def HuxleyFrom (X : ℝ) : Prop :=
  ∀ q a b : ℝ, X ≤ q → Admissible q a b → relErr a b ≤ Real.log q ^ (-3 : ℤ)

/-- **Named hypothesis (eq. (84)): `X_Hux` is finite.** For some `X`, every interval
`I ⊂ [q, 2q]` with `|I| ≥ (2q)^{7/12}` and `q ≥ X` has
`|π(I)/∫_I dt/log t - 1| ≤ (log q)^{-3}`. This is a statement about the rational primes; the
paper derives it (§7.1) from Heath-Brown's short-interval prime number theorem [HB88, (1.2)]
with `ε_HB ≡ 0` (eq. (83)) and the de la Vallée Poussin error term, neither of which is in
Mathlib. -/
def Huxley84 : Prop := ∃ X : ℝ, HuxleyFrom X

/-- The set of admissible thresholds in the definition of `X_Hux`. -/
def huxSet : Set ℝ := {X | Real.exp (10 ^ 8) ≤ X ∧ ∀ q, X ≤ q → etaH q ≤ Real.log q ^ (-3 : ℤ)}

/-- `X_Hux` of (84), without the paper's `1 +` (correction 105: the paper takes `1 + inf`).
The set is an up-ray, so every `X > XHux` is a threshold, `huxleyFrom_of_XHux_lt`. -/
noncomputable def XHux : ℝ := sInf huxSet

/-! ### `∫ dt/log t` -/

lemma continuousOn_inv_log {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Icc a b) := by
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

lemma intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b :=
  (continuousOn_inv_log ha).intervalIntegrable_of_Icc hab

/-- `(b - a)/log b ≤ ∫_a^b dt/log t`. -/
lemma liI_ge {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : (b - a) / Real.log b ≤ liI a b := by
  have hc : (b - a) / Real.log b = ∫ _ in a..b, 1 / Real.log b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hc, liI]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_inv_log ha hab)
  intro t ht
  have h1 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  exact one_div_le_one_div_of_le h1 (Real.log_le_log (by linarith [ht.1]) ht.2)

/-- `∫_a^b dt/log t ≤ (b - a)/log a`. -/
lemma liI_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : liI a b ≤ (b - a) / Real.log a := by
  have hc : (b - a) / Real.log a = ∫ _ in a..b, 1 / Real.log a := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hc, liI]
  apply intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log ha hab)
    intervalIntegrable_const
  intro t ht
  exact one_div_le_one_div_of_le (Real.log_pos ha) (Real.log_le_log (by linarith) ht.1)

lemma liI_pos {a b : ℝ} (ha : 1 < a) (hab : a < b) : 0 < liI a b := by
  refine lt_of_lt_of_le ?_ (liI_ge ha hab.le)
  exact div_pos (by linarith) (Real.log_pos (by linarith))

/-! ### Admissible intervals -/

lemma Admissible.lt {q a b : ℝ} (hq : 0 < q) (h : Admissible q a b) : a < b := by
  have : 0 < (2 * q) ^ (7 / 12 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  linarith [h.2.2]

lemma primeCount_le (a b : ℝ) (hb : 0 ≤ b) : (primeCount a b : ℝ) ≤ b + 1 := by
  classical
  have hsub : {p : ℕ | p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b} ⊆ ↑(Finset.range (⌊b⌋₊ + 1)) := by
    intro p hp
    simp only [Finset.coe_range, mem_Iio]
    exact Nat.lt_succ_of_le (Nat.le_floor hp.2.2)
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at h1
  unfold primeCount
  have h2 : ((⌊b⌋₊ + 1 : ℕ) : ℝ) ≤ b + 1 := by
    push_cast; linarith [Nat.floor_le hb]
  exact (Nat.cast_le.mpr h1).trans h2

/-- The relative errors of the admissible intervals at `q ≥ 2` are bounded. -/
lemma bddAbove_relErr {q : ℝ} (hq : 2 ≤ q) :
    BddAbove {e | ∃ a b, Admissible q a b ∧ e = relErr a b} := by
  refine ⟨(2 * q + 1) * Real.log (2 * q) / (2 * q) ^ (7 / 12 : ℝ) + 1, ?_⟩
  rintro e ⟨a, b, hadm, rfl⟩
  have hab := hadm.lt (by linarith)
  have ha : 1 < a := by linarith [hadm.1]
  have hli := liI_pos ha hab
  have hL : 0 < Real.log (2 * q) := Real.log_pos (by linarith)
  have hR : 0 < (2 * q) ^ (7 / 12 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hli2 : (2 * q) ^ (7 / 12 : ℝ) / Real.log (2 * q) ≤ liI a b := by
    refine le_trans ?_ (liI_ge ha hab.le)
    have : Real.log b ≤ Real.log (2 * q) := Real.log_le_log (by linarith) hadm.2.1
    calc (2 * q) ^ (7 / 12 : ℝ) / Real.log (2 * q) ≤ (b - a) / Real.log (2 * q) :=
          div_le_div_of_nonneg_right hadm.2.2 hL.le
      _ ≤ (b - a) / Real.log b :=
          div_le_div_of_nonneg_left (by linarith) (Real.log_pos (by linarith)) this
  have hpc := primeCount_le a b (by linarith)
  have hpc' : (primeCount a b : ℝ) ≤ 2 * q + 1 := by linarith [hadm.2.1]
  unfold relErr
  have h1 : |(primeCount a b : ℝ) / liI a b - 1| ≤ (primeCount a b : ℝ) / liI a b + 1 := by
    have : 0 ≤ (primeCount a b : ℝ) / liI a b := div_nonneg (Nat.cast_nonneg _) hli.le
    rw [abs_le]; constructor <;> linarith
  have h2 : (primeCount a b : ℝ) / liI a b ≤
      (2 * q + 1) * Real.log (2 * q) / (2 * q) ^ (7 / 12 : ℝ) := by
    rw [div_le_div_iff₀ hli hR]
    have : (primeCount a b : ℝ) * (2 * q) ^ (7 / 12 : ℝ) ≤
        (2 * q + 1) * ((2 * q) ^ (7 / 12 : ℝ)) := mul_le_mul_of_nonneg_right hpc' hR.le
    have h3 : (2 * q) ^ (7 / 12 : ℝ) ≤ liI a b * Real.log (2 * q) := by
      rwa [div_le_iff₀ hL] at hli2
    nlinarith
  linarith

/-- For `q ≥ 2` and `c ≥ 0`, `η_H(q) ≤ c` iff every admissible interval has relative error
`≤ c`. -/
lemma etaH_le_iff {q c : ℝ} (hq : 2 ≤ q) (hc : 0 ≤ c) :
    etaH q ≤ c ↔ ∀ a b, Admissible q a b → relErr a b ≤ c := by
  constructor
  · intro h a b hadm
    exact (le_csSup (bddAbove_relErr hq) ⟨a, b, hadm, rfl⟩).trans h
  · intro h
    apply Real.sSup_le _ hc
    rintro e ⟨a, b, hadm, rfl⟩
    exact h a b hadm

/-- `HuxleyFrom X` is the paper's condition `η_H(q) ≤ (log q)^{-3}` for all `q ≥ X`. -/
theorem huxleyFrom_iff_etaH {X : ℝ} (hX : 2 ≤ X) :
    HuxleyFrom X ↔ ∀ q, X ≤ q → etaH q ≤ Real.log q ^ (-3 : ℤ) := by
  constructor
  · intro h q hq
    have hq2 : 2 ≤ q := hX.trans hq
    have h0 : 0 ≤ Real.log q ^ (-3 : ℤ) := zpow_nonneg (Real.log_nonneg (by linarith)) _
    exact (etaH_le_iff hq2 h0).mpr fun a b hadm => h q a b hq hadm
  · intro h q a b hq hadm
    have hq2 : 2 ≤ q := hX.trans hq
    have h0 : 0 ≤ Real.log q ^ (-3 : ℤ) := zpow_nonneg (Real.log_nonneg (by linarith)) _
    exact (etaH_le_iff hq2 h0).mp (h q hq) a b hadm

lemma two_le_exp : (2 : ℝ) ≤ Real.exp (10 ^ 8) := by
  have := Real.add_one_le_exp (10 ^ 8 : ℝ)
  linarith

lemma huxleyFrom_mono {X Y : ℝ} (hXY : X ≤ Y) (h : HuxleyFrom X) : HuxleyFrom Y :=
  fun q a b hq hadm => h q a b (hXY.trans hq) hadm

lemma huxSet_nonempty (h : Huxley84) : huxSet.Nonempty := by
  obtain ⟨X, hX⟩ := h
  set Y := max X (Real.exp (10 ^ 8))
  refine ⟨Y, le_max_right _ _, ?_⟩
  exact (huxleyFrom_iff_etaH (two_le_exp.trans (le_max_right _ _))).mp
    (huxleyFrom_mono (le_max_left _ _) hX)

lemma bddBelow_huxSet : BddBelow huxSet := ⟨Real.exp (10 ^ 8), fun _ hX => hX.1⟩

/-- `X_Hux ≥ e^{10⁸}`. -/
theorem exp_le_XHux (h : Huxley84) : Real.exp (10 ^ 8) ≤ XHux :=
  le_csInf (huxSet_nonempty h) fun _ hX => hX.1

/-- Above `X_Hux`, (84) holds. -/
theorem huxleyFrom_of_XHux_lt (h : Huxley84) {X : ℝ} (hX : XHux < X) : HuxleyFrom X := by
  obtain ⟨Y, hY, hYX⟩ := exists_lt_of_csInf_lt (huxSet_nonempty h) hX
  have hY2 : 2 ≤ Y := two_le_exp.trans hY.1
  exact huxleyFrom_mono hYX.le ((huxleyFrom_iff_etaH hY2).mpr hY.2)

/-- Every admissible threshold is `≥ X_Hux`. -/
theorem XHux_le {X : ℝ} (hX : Real.exp (10 ^ 8) ≤ X) (h : HuxleyFrom X) : XHux ≤ X :=
  csInf_le bddBelow_huxSet ⟨hX, (huxleyFrom_iff_etaH (two_le_exp.trans hX)).mp h⟩

/-! ### The two-sided count -/

lemma log_zpow_neg3_le_one {q : ℝ} (hq : Real.exp 1 ≤ q) : Real.log q ^ (-3 : ℤ) ≤ 1 := by
  have hL : 1 ≤ Real.log q := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hq
  rw [zpow_neg, zpow_ofNat]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hL)

/-- (84), lower half: `π(I) ≥ (1 - (log q)^{-3}) ∫_I dt/log t`. -/
theorem count_ge {X q a b : ℝ} (h : HuxleyFrom X) (hX : 2 ≤ X) (hq : X ≤ q)
    (hadm : Admissible q a b) :
    (1 - Real.log q ^ (-3 : ℤ)) * liI a b ≤ primeCount a b := by
  have hab := hadm.lt (by linarith)
  have hli := liI_pos (by linarith [hadm.1]) hab
  have he := h q a b hq hadm
  unfold relErr at he
  rw [abs_le] at he
  have h1 : 1 - Real.log q ^ (-3 : ℤ) ≤ (primeCount a b : ℝ) / liI a b := by linarith [he.1]
  rwa [le_div_iff₀ hli] at h1

/-- (84), upper half: `π(I) ≤ (1 + (log q)^{-3}) ∫_I dt/log t`. -/
theorem count_le {X q a b : ℝ} (h : HuxleyFrom X) (hX : 2 ≤ X) (hq : X ≤ q)
    (hadm : Admissible q a b) :
    (primeCount a b : ℝ) ≤ (1 + Real.log q ^ (-3 : ℤ)) * liI a b := by
  have hab := hadm.lt (by linarith)
  have hli := liI_pos (by linarith [hadm.1]) hab
  have he := h q a b hq hadm
  unfold relErr at he
  rw [abs_le] at he
  have h1 : (primeCount a b : ℝ) / liI a b ≤ 1 + Real.log q ^ (-3 : ℤ) := by linarith [he.2]
  rwa [div_le_iff₀ hli] at h1

/-- (84) implies its lower half in the form `BModel.ShortIntervalPNTFrom` used in Lemma 3.3. -/
theorem shortIntervalPNTFrom_of_huxleyFrom {X : ℝ} (hX : Real.exp 1 ≤ X) (h : HuxleyFrom X) :
    BModel.ShortIntervalPNTFrom X := by
  intro q a b hq hqa hb hlen
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hadm : Admissible q a b := ⟨hqa, hb, hlen⟩
  have hab := hadm.lt (by linarith)
  have ha : 1 < a := by linarith
  have hc := count_ge h (he1.trans hX) hq hadm
  have h0 : 0 ≤ 1 - Real.log q ^ (-3 : ℤ) := by
    linarith [log_zpow_neg3_le_one (hX.trans hq)]
  have hL : (b - a) / Real.log (2 * q) ≤ liI a b := by
    refine le_trans ?_ (liI_ge ha hab.le)
    exact div_le_div_of_nonneg_left (by linarith) (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) hb)
  have := mul_le_mul_of_nonneg_left hL h0
  unfold primeCount at hc
  calc (1 - Real.log q ^ (-3 : ℤ)) * (b - a) / Real.log (2 * q)
      = (1 - Real.log q ^ (-3 : ℤ)) * ((b - a) / Real.log (2 * q)) := by ring
    _ ≤ _ := this.trans hc

/-- (84) implies `BModel.ShortIntervalPNT`. -/
theorem shortIntervalPNT_of_huxley84 (h : Huxley84) : BModel.ShortIntervalPNT := by
  obtain ⟨X, hX⟩ := h
  exact ⟨max X (Real.exp 1), shortIntervalPNTFrom_of_huxleyFrom (le_max_right _ _)
    (huxleyFrom_mono (le_max_left _ _) hX)⟩

end BaseRange
