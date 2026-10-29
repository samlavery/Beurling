module

public import RequestProject.Beurling.Noise.KRFacts
public import RequestProject.Beurling.LemmaM
public import RequestProject.BSCert.Finite.X0Band

/-!
# Theorem 5.14 (KR bound, nominal filters), and the nominal masses (eq. (nominal-mass))

The kernels of §5.9 are indexed by the elements `n` of the system, which (as in Lemma 5.5,
`LemmaM`) we write as positive integers with an arbitrary value map `val ≥ 1` on the prime
labels; `V n = LemmaM.valN val n` is the value of `n`. For a start `x`, frozen widths `H_n > 0`
and step filters `κ_{d→n}` with `|κ| ≤ 1`, the frozen-width nominal kernels are given by the
last-step recursion (kernel-rec)

  `C_1 = δ_x`,  `C_n = -∑_{d ∣ n, d < n} κ_{d→n} bx_{H_n} * D_{n/d} C_d`,

and their masses by `c_1 = 1`, `c_n = -∑ κ_{d→n} c_d`. Measures are represented by their
distribution functions (`KRFacts.lean`): `ker n` is the distribution function of `C_n`, `mass n`
is `c_n`; the total variation of `C_n` is `eVariationOn (ker n) univ`, and the KR norm of the
mass-zero measure `C_n - c_n δ_{x/n}` is `KRn (ker n - c_n 1[x/n ≤ ·])`.

* `KR.kr_bound` : **Theorem 5.14**, for every `n ≥ 2`:
  `TV(C_n) ≤ |c_n| + ½ ∑_{e ∣ n, 1<e<n} |c_e| (H_e/H_n) H_ord(n/e) e/n` and
  `‖C_n - c_n δ_{x/n}‖_KR ≤ ¼ ∑_{e ∣ n, e > 1} |c_e| H_e H_ord(n/e) e/n`.
* `KR.mass_eq_coeff`, `KR.mass_eq_moebius` : for the nominal filters
  `κ_{d→n} = 1[τ_{n/d} < x/n] 1[x/n ≥ X₀⁻]` the masses are the sharp coefficients, hence by
  **Lemma 5.5** `c_n = μ(n) χ^t_x(n) 1[x/n ≥ X₀⁻]` (nominal-mass).

The proof is the paper's: with `D_n = C_n - c_n δ_{x/n}`, (Dn-rec) and (K1)–(K4) give
`‖D_n‖_KR ≤ ¼|c_n|H_n + ∑_{d<n} (d/n)‖D_d‖_KR`, and the divisor-sum identity
`∑_{d ∣ n, d < n} ∑_{e ∣ d, e > 1} (…) H_ord(d/e) = ∑_{e ∣ n, 1<e<n} (…) H_ord(n/e)` closes the
induction; the TV bound follows from (K3).
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

variable (val : ℕ → ℝ) (x : ℝ) (H : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)

/-- The masses `c_n = C_n(ℝ)`: `c_1 = 1`, `c_n = -∑_{d ∣ n, d < n} κ_{d→n} c_d`. -/
noncomputable def mass (n : ℕ) : ℝ :=
  if n ≤ 1 then (if n = 1 then 1 else 0) else
    - ∑ d ∈ n.properDivisors.attach, κ d.1 n * mass d.1
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

/-- The distribution function of the frozen-width nominal kernel `C_n`:
`C_1 = δ_x`, `C_n = -∑_{d ∣ n, d < n} κ_{d→n} bx_{H_n} * D_{n/d} C_d`. -/
noncomputable def ker (n : ℕ) : ℝ → ℝ :=
  if n ≤ 1 then (if n = 1 then stepF x else fun _ => 0) else
    fun t => - ∑ d ∈ n.properDivisors.attach,
      κ d.1 n * boxAvg (H n) (fun s => ker d.1 (LemmaM.valN val (n / d.1) * s)) t
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

lemma mass_one : mass κ 1 = 1 := by rw [mass]; simp

lemma mass_eq {n : ℕ} (hn : 2 ≤ n) :
    mass κ n = - ∑ d ∈ n.properDivisors, κ d n * mass κ d := by
  rw [mass, if_neg (by omega)]
  congr 1
  exact Finset.sum_attach n.properDivisors (fun d => κ d n * mass κ d)

lemma ker_zero : ker val x H κ 0 = fun _ => 0 := by rw [ker]; simp

lemma ker_one : ker val x H κ 1 = stepF x := by rw [ker]; simp

lemma ker_eq {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    ker val x H κ n t = - ∑ d ∈ n.properDivisors,
      κ d n * boxAvg (H n) (fun s => ker val x H κ d (LemmaM.valN val (n / d) * s)) t := by
  rw [ker, if_neg (by omega)]
  congr 1
  exact Finset.sum_attach n.properDivisors
    (fun d => κ d n * boxAvg (H n) (fun s => ker val x H κ d (LemmaM.valN val (n / d) * s)) t)

/-- `D_n = C_n - c_n δ_{x/n}` (distribution function). -/
noncomputable def Dker (n : ℕ) (t : ℝ) : ℝ :=
  ker val x H κ n t - mass κ n * stepF (x / LemmaM.valN val n) t

/-- The bound of Theorem 5.14 for `‖D_n‖_KR`: `¼ ∑_{e ∣ n, e > 1} |c_e| H_e H_ord(n/e) e/n`. -/
noncomputable def KRB (n : ℕ) : ℝ :=
  1 / 4 * ∑ e ∈ n.divisors.filter (1 < ·),
    |mass κ e| * H e * (BSCert.X0Band.Hord (n / e) : ℝ) *
      (LemmaM.valN val e / LemmaM.valN val n)

/-- The bound of Theorem 5.14 for `TV(C_n)`. -/
noncomputable def TVB (n : ℕ) : ℝ :=
  |mass κ n| + 1 / 2 * ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n),
    |mass κ e| * (H e / H n) * (BSCert.X0Band.Hord (n / e) : ℝ) *
      (LemmaM.valN val e / LemmaM.valN val n)

/-! ## The divisor-sum identity -/

/-- `∑_{d ∣ n, d < n, e ∣ d} H_ord(d/e) = H_ord(n/e)` for `e ∣ n`, `e < n`. -/
lemma sum_Hord_div {n e : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hen : e < n) (he0 : 0 < e) :
    ∑ d ∈ n.properDivisors.filter (e ∣ ·), (BSCert.X0Band.Hord (d / e) : ℝ) =
      BSCert.X0Band.Hord (n / e) := by
  obtain ⟨k, rfl⟩ := he
  have hk : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp_all
    · exact h
  rw [Nat.mul_div_cancel_left k he0, BSCert.X0Band.Hord_eq k, if_neg (by omega)]
  push_cast
  refine Finset.sum_nbij' (fun d => d / e) (fun g => e * g) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_properDivisors] at hd ⊢
    obtain ⟨⟨hdn, hdlt⟩, g, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left g he0]
    refine ⟨(Nat.mul_dvd_mul_iff_left he0).mp hdn, ?_⟩
    exact (Nat.mul_lt_mul_left he0).mp hdlt
  · intro g hg
    simp only [Finset.mem_filter, Nat.mem_properDivisors] at hg ⊢
    exact ⟨⟨Nat.mul_dvd_mul_left e hg.1, (Nat.mul_lt_mul_left he0).mpr hg.2⟩, dvd_mul_right e g⟩
  · intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨g, rfl⟩ := hd.2
    show e * (e * g / e) = e * g
    rw [Nat.mul_div_cancel_left g he0]
  · intro g _
    simp only
    rw [Nat.mul_div_cancel_left g he0]
  · intro d _; rfl

variable {val} in
lemma valN_div_mul (hval : ∀ p, p.Prime → 1 ≤ val p) {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) :
    LemmaM.valN val n = LemmaM.valN val d * LemmaM.valN val (n / d) := by
  obtain ⟨k, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hn
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hn
  rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0), LemmaM.valN_mul val hd0 hk0]

/-- The divisor-sum identity of the proof of Theorem 5.14. -/
lemma divsum (hval : ∀ p, p.Prime → 1 ≤ val p) (f : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ *
        ∑ e ∈ d.divisors.filter (1 < ·), f e * (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN val e / LemmaM.valN val d) =
      ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n), f e *
        (BSCert.X0Band.Hord (n / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val n) := by
  have hn0 : n ≠ 0 := by omega
  have hV : ∀ m, 0 < LemmaM.valN val m := fun m => LemmaM.valN_pos val hval
  -- the weights combine to `e/n`
  have step1 : ∀ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ *
      ∑ e ∈ d.divisors.filter (1 < ·), f e * (BSCert.X0Band.Hord (d / e) : ℝ) *
        (LemmaM.valN val e / LemmaM.valN val d) =
      ∑ e ∈ d.divisors.filter (1 < ·), f e * (BSCert.X0Band.Hord (d / e) : ℝ) *
        (LemmaM.valN val e / LemmaM.valN val n) := by
    intro d hd
    have hdn := (Nat.mem_properDivisors.mp hd).1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [valN_div_mul hval hdn hn0]
    have h1 := hV d
    have h2 := hV (n / d)
    field_simp
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := n.divisors.filter (fun e => 1 < e ∧ e < n))
    (s' := fun e => n.properDivisors.filter (e ∣ ·))]
  · refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    rw [← Finset.sum_mul, ← Finset.mul_sum,
      sum_Hord_div hn0 he.1.1 he.2.2 (by omega)]
  · intro d e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hdn, hdlt⟩, ⟨hed, hd0⟩, he1⟩
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed
      exact ⟨⟨⟨hdn, hdlt⟩, hed⟩, ⟨dvd_trans hed hdn, hn0⟩, he1, by omega⟩
    · rintro ⟨⟨⟨hdn, hdlt⟩, hed⟩, ⟨-, -⟩, he1, -⟩
      refine ⟨⟨hdn, hdlt⟩, ⟨hed, ?_⟩, he1⟩
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hdn)

/-! ## The bounds -/

variable {val H} in
lemma KRB_nonneg (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : ∀ n, 0 < H n) (n : ℕ) :
    0 ≤ KRB val H κ n := by
  unfold KRB
  apply mul_nonneg (by norm_num)
  refine Finset.sum_nonneg fun e _ => ?_
  have := LemmaM.valN_pos val hval (n := e)
  have := LemmaM.valN_pos val hval (n := n)
  have := hH e
  positivity

lemma KRB_one : KRB val H κ 1 = 0 := by
  unfold KRB
  rw [Nat.divisors_one, Finset.filter_singleton, if_neg (lt_irrefl 1)]
  simp

lemma KRB_rec (hval : ∀ p, p.Prime → 1 ≤ val p) {n : ℕ} (hn : 2 ≤ n) :
    KRB val H κ n = |mass κ n| * H n / 4 +
      ∑ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ * KRB val H κ d := by
  have hsplit : n.divisors.filter (1 < ·) =
      insert n (n.divisors.filter (fun e => 1 < e ∧ e < n)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hen, hn0⟩, he1⟩
      rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hen) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨hen, hn0⟩, he1, h⟩
    · rintro (rfl | ⟨h1, h2, -⟩)
      · exact ⟨⟨dvd_refl _, by omega⟩, by omega⟩
      · exact ⟨h1, h2⟩
  have hnot : n ∉ n.divisors.filter (fun e => 1 < e ∧ e < n) := by simp
  have hV := LemmaM.valN_pos val hval (n := n)
  unfold KRB
  rw [hsplit, Finset.sum_insert hnot, Nat.div_self (by omega)]
  have hd := divsum val hval (fun e => |mass κ e| * H e) hn
  have e2 : ∑ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ *
      (1 / 4 * ∑ e ∈ d.divisors.filter (1 < ·), |mass κ e| * H e *
        (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val d)) =
      1 / 4 * ∑ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ *
        ∑ e ∈ d.divisors.filter (1 < ·), |mass κ e| * H e *
          (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [e2, hd, BSCert.X0Band.Hord_eq 1, if_pos le_rfl, div_self hV.ne']
  push_cast
  ring

lemma TVB_eq (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : ∀ n, 0 < H n) {n : ℕ} (hn : 2 ≤ n) :
    TVB val H κ n = (H n)⁻¹ * (|mass κ n| * H n +
      ∑ d ∈ n.properDivisors, 2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d)) := by
  have hd := divsum val hval (fun e => |mass κ e| * H e) hn
  have hHn := hH n
  have e2 : ∑ d ∈ n.properDivisors, 2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) =
      1 / 2 * ∑ d ∈ n.properDivisors, (LemmaM.valN val (n / d))⁻¹ *
        ∑ e ∈ d.divisors.filter (1 < ·), |mass κ e| * H e *
          (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold KRB; ring
  rw [e2, hd]
  unfold TVB
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun e _ => ?_
    field_simp

/-! ## The induction -/

variable {val x H κ}

lemma BM_Dker {n : ℕ} (h : BM (ker val x H κ n)) : BM (Dker val x H κ n) :=
  h.sub ((BM_stepF _).const_mul _)

/-- The representation `C_n = bx_{H_n} * G_n` behind (Dn-rec), with
`G_n = c_n δ_{x/n} - ∑_{d<n} κ_{d→n} D_{n/d} D_d`. -/
lemma ker_eq_boxAvg (hval : ∀ p, p.Prime → 1 ≤ val p) {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ d ∈ n.properDivisors, BM (ker val x H κ d)) (t : ℝ) :
    ker val x H κ n t = boxAvg (H n) (fun s => mass κ n * stepF (x / LemmaM.valN val n) s +
      ∑ d ∈ n.properDivisors, -κ d n * Dker val x H κ d (LemmaM.valN val (n / d) * s)) t := by
  have hn0 : n ≠ 0 := by omega
  set a := x / LemmaM.valN val n
  have hpt : ∀ d ∈ n.properDivisors, ∀ s,
      ker val x H κ d (LemmaM.valN val (n / d) * s) =
        Dker val x H κ d (LemmaM.valN val (n / d) * s) + mass κ d * stepF a s := by
    intro d hd s
    have hdn := (Nat.mem_properDivisors.mp hd).1
    have hw := LemmaM.valN_pos val hval (n := n / d)
    have hVd := LemmaM.valN_pos val hval (n := d)
    have ha : x / LemmaM.valN val d = LemmaM.valN val (n / d) * a := by
      simp only [a]; rw [valN_div_mul hval hdn hn0]; field_simp
    unfold Dker
    rw [ha, stepF_mul hw]; ring
  have hBMD : ∀ d ∈ n.properDivisors,
      BM (fun s => Dker val x H κ d (LemmaM.valN val (n / d) * s)) :=
    fun d hd => (BM_Dker (ih d hd)).comp_mul _
  rw [ker_eq val x H κ hn]
  rw [boxAvg_add ((BM_stepF a).const_mul _)
    (BM.finset_sum _ fun d hd => (hBMD d hd).const_mul _),
    boxAvg_const_mul, boxAvg_sum _ (fun d hd => (hBMD d hd).const_mul _)]
  have : ∀ d ∈ n.properDivisors, κ d n * boxAvg (H n)
      (fun s => ker val x H κ d (LemmaM.valN val (n / d) * s)) t =
      κ d n * boxAvg (H n) (fun s => Dker val x H κ d (LemmaM.valN val (n / d) * s)) t +
        κ d n * mass κ d * boxAvg (H n) (stepF a) t := by
    intro d hd
    rw [boxAvg_congr (hpt d hd), boxAvg_add (hBMD d hd) ((BM_stepF a).const_mul _),
      boxAvg_const_mul]
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, mass_eq κ hn]
  simp only [boxAvg_const_mul]
  rw [← Finset.sum_mul, neg_add]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

lemma one_le_of_mem_properDivisors {d n : ℕ} (hd : d ∈ n.properDivisors) : 1 ≤ d := by
  obtain ⟨hdn, hlt⟩ := Nat.mem_properDivisors.mp hd
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp at hdn; omega
  · exact h

/-- The term `ofReal|κ| · ‖D_{n/d} D_d‖_KR ≤ (d/n) KRB(d)` of the KR step. -/
lemma term_le (hval : ∀ p, p.Prime → 1 ≤ val p) (hκ : ∀ d n, |κ d n| ≤ 1) {d n : ℕ}
    (hD : Measurable (Dker val x H κ d))
    (hKR : KRn (Dker val x H κ d) ≤ ENNReal.ofReal (KRB val H κ d)) :
    ENNReal.ofReal |-κ d n| *
        KRn (fun t => Dker val x H κ d (LemmaM.valN val (n / d) * t)) ≤
      ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) := by
  have hw := LemmaM.valN_pos val hval (n := n / d)
  rw [KRn_comp_mul hD hw, abs_neg]
  calc ENNReal.ofReal |κ d n| * (ENNReal.ofReal (LemmaM.valN val (n / d))⁻¹ *
        KRn (Dker val x H κ d))
      ≤ 1 * (ENNReal.ofReal (LemmaM.valN val (n / d))⁻¹ * ENNReal.ofReal (KRB val H κ d)) := by
        gcongr
        · exact ENNReal.ofReal_le_one.mpr (hκ d n)
    _ = ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) := by
        rw [one_mul, ENNReal.ofReal_mul (inv_pos.mpr hw).le]

/-- The induction behind Theorem 5.14: each `C_n` is bounded and measurable, and
`‖C_n - c_n δ_{x/n}‖_KR ≤ ¼ ∑_{e ∣ n, e > 1} |c_e| H_e H_ord(n/e) e/n` for `n ≥ 1`. -/
theorem kr_main (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : ∀ n, 0 < H n)
    (hκ : ∀ d n, |κ d n| ≤ 1) :
    ∀ n, BM (ker val x H κ n) ∧
      (1 ≤ n → KRn (Dker val x H κ n) ≤ ENNReal.ofReal (KRB val H κ n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [ker_zero]; exact ⟨BM_zero, fun h => absurd h (by norm_num)⟩
    · refine ⟨by rw [ker_one]; exact BM_stepF x, fun _ => ?_⟩
      rw [KRB_one]
      have : Dker val x H κ 1 = fun _ => 0 := by
        funext t; unfold Dker; rw [ker_one, mass_one, LemmaM.valN_one, div_one]; ring
      rw [this]; simp [KRn]
  have ihBM : ∀ d ∈ n.properDivisors, BM (ker val x H κ d) :=
    fun d hd => (ih d (Nat.mem_properDivisors.mp hd).2).1
  have ihKR : ∀ d ∈ n.properDivisors,
      KRn (Dker val x H κ d) ≤ ENNReal.ofReal (KRB val H κ d) :=
    fun d hd => (ih d (Nat.mem_properDivisors.mp hd).2).2 (one_le_of_mem_properDivisors hd)
  set a := x / LemmaM.valN val n
  set h := H n
  have hh : 0 < h := hH n
  set Sf : ℝ → ℝ := fun s =>
    ∑ d ∈ n.properDivisors, -κ d n * Dker val x H κ d (LemmaM.valN val (n / d) * s)
  have hBMD : ∀ d ∈ n.properDivisors,
      BM (fun s => Dker val x H κ d (LemmaM.valN val (n / d) * s)) :=
    fun d hd => (BM_Dker (ihBM d hd)).comp_mul _
  have hBMS : BM Sf := BM.finset_sum _ fun d hd => (hBMD d hd).const_mul _
  have hrep := ker_eq_boxAvg hval hn ihBM
  have hBMG : BM (fun s => mass κ n * stepF a s + Sf s) :=
    ((BM_stepF a).const_mul _).add hBMS
  refine ⟨?_, fun _ => ?_⟩
  · have : ker val x H κ n = boxAvg h (fun s => mass κ n * stepF a s + Sf s) := funext hrep
    rw [this]; exact hBMG.boxAvg hh
  have hD : Dker val x H κ n = fun t =>
      mass κ n * (boxAvg h (stepF a) t - stepF a t) + boxAvg h Sf t := by
    funext t
    unfold Dker
    rw [hrep, boxAvg_add ((BM_stepF a).const_mul _) hBMS, boxAvg_const_mul]
    ring
  rw [hD]
  have hm1 : Measurable fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t) :=
    measurable_const.mul ((continuous_boxAvg (BM_stepF a) h).measurable.sub (measurable_stepF a))
  have hKRS : KRn Sf ≤ ∑ d ∈ n.properDivisors,
      ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) := by
    refine (KRn_sum_le _ fun d hd => (hBMD d hd).1.const_mul _).trans ?_
    refine Finset.sum_le_sum fun d hd => ?_
    rw [KRn_const_mul]
    exact term_le hval hκ (BM_Dker (ihBM d hd)).1 (ihKR d hd)
  have hKRB : ∀ d ∈ n.properDivisors, 0 ≤ (LemmaM.valN val (n / d))⁻¹ * KRB val H κ d :=
    fun d _ => mul_nonneg (inv_pos.mpr (LemmaM.valN_pos val hval)).le (KRB_nonneg κ hval hH d)
  calc KRn (fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t) + boxAvg h Sf t)
      ≤ KRn (fun t => mass κ n * (boxAvg h (stepF a) t - stepF a t)) + KRn (boxAvg h Sf) :=
        KRn_add_le hm1
    _ ≤ ENNReal.ofReal |mass κ n| * ENNReal.ofReal (h / 4) +
          ∑ d ∈ n.properDivisors,
            ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) := by
        gcongr
        · rw [KRn_const_mul]
          gcongr
          exact KRn_box_sub_step_le hh a
        · exact (KRn_boxAvg_le hBMS.1 hh).trans hKRS
    _ = ENNReal.ofReal (KRB val H κ n) := by
        rw [KRB_rec val H κ hval hn, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_sum_of_nonneg hKRB,
          ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (by positivity))
            (Finset.sum_nonneg hKRB)]
        congr 1; ring

/-- **Theorem 5.14 (KR bound, nominal filters)**, for the frozen-width nominal kernels: for every
`n ≥ 2`,
* `TV(C_n) ≤ |c_n| + ½ ∑_{e ∣ n, 1<e<n} |c_e| (H_e/H_n) H_ord(n/e) e/n`;
* `‖C_n - c_n δ_{x/n}‖_KR ≤ ¼ ∑_{e ∣ n, e>1} |c_e| H_e H_ord(n/e) e/n`.

Here `e/n` is the ratio of the values `V e / V n`, the filters are arbitrary with
`|κ_{d→n}| ≤ 1`, and the widths `H_e > 0` are arbitrary. -/
theorem kr_bound (hval : ∀ p, p.Prime → 1 ≤ val p) (hH : ∀ n, 0 < H n)
    (hκ : ∀ d n, |κ d n| ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    eVariationOn (ker val x H κ n) univ ≤ ENNReal.ofReal (TVB val H κ n) ∧
      KRn (fun t => ker val x H κ n t - mass κ n * stepF (x / LemmaM.valN val n) t) ≤
        ENNReal.ofReal (KRB val H κ n) := by
  have hmain := kr_main (x := x) hval hH hκ
  refine ⟨?_, (hmain n).2 (by omega)⟩
  have ihBM : ∀ d ∈ n.properDivisors, BM (ker val x H κ d) := fun d _ => (hmain d).1
  have ihKR : ∀ d ∈ n.properDivisors,
      KRn (Dker val x H κ d) ≤ ENNReal.ofReal (KRB val H κ d) :=
    fun d hd => (hmain d).2 (one_le_of_mem_properDivisors hd)
  set a := x / LemmaM.valN val n
  set h := H n
  have hh : 0 < h := hH n
  set Sf : ℝ → ℝ := fun s =>
    ∑ d ∈ n.properDivisors, -κ d n * Dker val x H κ d (LemmaM.valN val (n / d) * s)
  have hBMD : ∀ d ∈ n.properDivisors,
      BM (fun s => Dker val x H κ d (LemmaM.valN val (n / d) * s)) :=
    fun d hd => (BM_Dker (ihBM d hd)).comp_mul _
  have hBMS : BM Sf := BM.finset_sum _ fun d hd => (hBMD d hd).const_mul _
  have hBMG : BM (fun s => mass κ n * stepF a s + Sf s) :=
    ((BM_stepF a).const_mul _).add hBMS
  have hker : ker val x H κ n = boxAvg h (fun s => mass κ n * stepF a s + Sf s) :=
    funext (ker_eq_boxAvg hval hn ihBM)
  rw [hker]
  refine (eVariationOn_boxAvg_le hBMG hh).trans ?_
  -- the increment of `G_n` over a window
  have hinc : (fun t => ‖(mass κ n * stepF a (t + h / 2) + Sf (t + h / 2)) -
      (mass κ n * stepF a (t - h / 2) + Sf (t - h / 2))‖ₑ) = fun t =>
      ‖mass κ n * (stepF a (t + h / 2) - stepF a (t - h / 2)) +
        ∑ d ∈ n.properDivisors, -κ d n *
          (Dker val x H κ d (LemmaM.valN val (n / d) * (t + h / 2)) -
            Dker val x H κ d (LemmaM.valN val (n / d) * (t - h / 2)))‖ₑ := by
    funext t
    congr 1
    simp only [Sf, mul_sub, Finset.sum_sub_distrib]
    ring
  have hKRB : ∀ d ∈ n.properDivisors, 0 ≤ 2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) :=
    fun d _ => mul_nonneg (by norm_num)
      (mul_nonneg (inv_pos.mpr (LemmaM.valN_pos val hval)).le (KRB_nonneg κ hval hH d))
  have hm1 : Measurable fun t => mass κ n * (stepF a (t + h / 2) - stepF a (t - h / 2)) :=
    measurable_const.mul (((measurable_stepF a).comp (measurable_add_const _)).sub
      ((measurable_stepF a).comp (measurable_sub_const _)))
  have hI : ∫⁻ t, ‖(mass κ n * stepF a (t + h / 2) + Sf (t + h / 2)) -
      (mass κ n * stepF a (t - h / 2) + Sf (t - h / 2))‖ₑ ≤
      ENNReal.ofReal (|mass κ n| * h) + ∑ d ∈ n.properDivisors,
        ENNReal.ofReal (2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d)) := by
    rw [hinc]
    refine (KRn_add_le (G := fun t => ∑ d ∈ n.properDivisors, -κ d n *
          (Dker val x H κ d (LemmaM.valN val (n / d) * (t + h / 2)) -
            Dker val x H κ d (LemmaM.valN val (n / d) * (t - h / 2)))) hm1).trans ?_
    gcongr
    · rw [KRn_const_mul]
      unfold KRn
      rw [lintegral_step_shift_sub a hh, ← ENNReal.ofReal_mul (abs_nonneg _)]
    · refine (KRn_sum_le _ fun d hd => ?_).trans (Finset.sum_le_sum fun d hd => ?_)
      · exact measurable_const.mul
          ((((hBMD d hd).1).comp (measurable_add_const _)).sub
            (((hBMD d hd).1).comp (measurable_sub_const _)))
      · rw [KRn_const_mul]
        have h2 := lintegral_shift_sub_le (hBMD d hd).1 h
        have h3 := term_le hval hκ (n := n) (BM_Dker (ihBM d hd)).1 (ihKR d hd)
        calc ENNReal.ofReal |-κ d n| * KRn (fun t =>
              Dker val x H κ d (LemmaM.valN val (n / d) * (t + h / 2)) -
                Dker val x H κ d (LemmaM.valN val (n / d) * (t - h / 2)))
            ≤ ENNReal.ofReal |-κ d n| *
                (2 * KRn (fun t => Dker val x H κ d (LemmaM.valN val (n / d) * t))) := by
              gcongr; exact h2
          _ = 2 * (ENNReal.ofReal |-κ d n| *
                KRn (fun t => Dker val x H κ d (LemmaM.valN val (n / d) * t))) := by ring
          _ ≤ 2 * ENNReal.ofReal ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d) := by
              gcongr
          _ = ENNReal.ofReal (2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d)) := by
              rw [ENNReal.ofReal_mul (p := 2) (by norm_num)]; norm_num
  calc ENNReal.ofReal h⁻¹ * ∫⁻ t, ‖(mass κ n * stepF a (t + h / 2) + Sf (t + h / 2)) -
        (mass κ n * stepF a (t - h / 2) + Sf (t - h / 2))‖ₑ
      ≤ ENNReal.ofReal h⁻¹ * (ENNReal.ofReal (|mass κ n| * h) + ∑ d ∈ n.properDivisors,
          ENNReal.ofReal (2 * ((LemmaM.valN val (n / d))⁻¹ * KRB val H κ d))) := by
        gcongr
    _ = ENNReal.ofReal (TVB val H κ n) := by
        rw [TVB_eq val H κ hval hH hn, ← ENNReal.ofReal_sum_of_nonneg hKRB,
          ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hh.le) (Finset.sum_nonneg hKRB),
          ← ENNReal.ofReal_mul (inv_pos.mpr hh).le]

/-! ## The nominal masses (eq. (nominal-mass)) -/

variable (val x)

open scoped Classical


/-- The nominal step filter `κ_{d→n} = 1[τ_{n/d} < x/n] 1[x/n ≥ X₀⁻]` for the decision order
`t` (Lemma 5.5's `filt`: `t(p) · n < x` for every prime `p ∣ n/d`). -/
noncomputable def nomFilter (t : ℕ → ℝ) (X0m : ℝ) (d n : ℕ) : ℝ :=
  if LemmaM.filt t val x n d ∧ X0m ≤ x / LemmaM.valN val n then 1 else 0

lemma abs_nomFilter_le (t : ℕ → ℝ) (X0m : ℝ) (d n : ℕ) : |nomFilter val x t X0m d n| ≤ 1 := by
  unfold nomFilter; split_ifs <;> simp

/-- With the nominal filters, the masses `c_n` satisfy the recursion of the sharp resolvent,
so they are the sharp coefficients `c_n(x)` of Lemma 5.5. -/
theorem mass_eq_coeff (t : ℕ → ℝ) (X0m : ℝ) (n : ℕ) :
    mass (nomFilter val x t X0m) n = (LemmaM.coeff t val X0m x n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [mass, LemmaM.coeff]; simp
    · rw [mass_one, LemmaM.coeff]; simp
  rw [mass_eq _ hn, LemmaM.coeff, if_neg (by omega)]
  push_cast
  rw [Finset.sum_attach n.properDivisors (fun d => (if LemmaM.filt t val x n d ∧
    X0m ≤ x / LemmaM.valN val n then (LemmaM.coeff t val X0m x d : ℝ) else 0))]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [ih d (Nat.mem_properDivisors.mp hd).2]
  unfold nomFilter
  split_ifs <;> simp

/-- **(nominal-mass)**: by Lemma 5.5, the masses of the nominal kernels are
`c_n = μ(n) χ^t_x(n) 1[x/n ≥ X₀⁻]`. -/
theorem mass_eq_moebius {t : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < t p)
    (hval : ∀ p, p.Prime → 1 ≤ val p) {X0m : ℝ} (hX0 : 0 ≤ X0m) (hx : X0m ≤ x) {n : ℕ}
    (hn : 1 ≤ n) :
    mass (nomFilter val x t X0m) n =
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (if LemmaM.chi t val x n then 1 else 0) *
        (if X0m ≤ x / LemmaM.valN val n then 1 else 0) := by
  rw [mass_eq_coeff, LemmaM.lemma_M t val ht hval hX0 hx hn]
  push_cast
  split_ifs <;> simp

/-- **Theorem 5.14 for the nominal filters**: the frozen-width nominal kernels of the start `x`
satisfy the KR and TV bounds of `kr_bound`, with the masses
`c_e = μ(e) χ^t_x(e) 1[x/e ≥ X₀⁻]` of Lemma 5.5. -/
theorem kr_bound_nominal {t : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < t p)
    (hval : ∀ p, p.Prime → 1 ≤ val p) {X0m : ℝ} (hX0 : 0 ≤ X0m) (hx : X0m ≤ x)
    (hH : ∀ n, 0 < H n) {n : ℕ} (hn : 2 ≤ n) :
    (eVariationOn (ker val x H (nomFilter val x t X0m) n) univ ≤
        ENNReal.ofReal (TVB val H (nomFilter val x t X0m) n) ∧
      KRn (fun s => ker val x H (nomFilter val x t X0m) n s -
          mass (nomFilter val x t X0m) n * stepF (x / LemmaM.valN val n) s) ≤
        ENNReal.ofReal (KRB val H (nomFilter val x t X0m) n)) ∧
    ∀ e, 1 ≤ e → mass (nomFilter val x t X0m) e =
      ((ArithmeticFunction.moebius e : ℤ) : ℝ) * (if LemmaM.chi t val x e then 1 else 0) *
        (if X0m ≤ x / LemmaM.valN val e then 1 else 0) :=
  ⟨kr_bound hval hH (abs_nomFilter_le val x t X0m) hn,
    fun _ he => mass_eq_moebius val x ht hval hX0 hx he⟩

end KR

end
