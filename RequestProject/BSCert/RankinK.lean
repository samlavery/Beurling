module

public import RequestProject.BSCert.Rankin
public import RequestProject.BSCert.Finite.KArith

/-!
# `rankin_R.py`, head sum, checked by the kernel

For a prime `p` and `σ = a/b`, `x = p^{-σ} = e^{-σ log p}` is bounded above in fixed point
(`FX.logLo` and `FX.expHi`), and `-log(1-x) - x ≤ P_K(x)` (`log_term_le_P`) is bounded above by
evaluating `P_K` with every operation rounded up (`PHi`, monotone in `x`). The head sum over
`p ≤ 10⁵` is a running sum (`K.sumUp`) over all `n ≤ 10⁵`, the non-primes being detected by
trial division (`K.lpf`) and contributing `0`.
-/

@[expose] public section

namespace BSCert.Rankin

open FX Finset BSCert.FiniteN

/-- `∑_{i=j}^{j+n-1} ⌈p_i/(i+2)⌉` with `p_{i+1} = ⌈p_i X⌉` (`p_j ≥ x^{j+2}`), plus the tail
`⌈p_K/(1 - X)⌉`; the result bounds `P_K(x)` for `0 ≤ x ≤ X < 1`. -/
def PHiAux (X : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, pw, s => s + cdiv (pw * ZI) (ZI - X)
  | n + 1, i, pw, s =>
    forceI (s + cdiv pw ((i + 2 : ℕ) : ℤ)) fun s' => forceI (cl (pw * X)) fun pw' =>
      PHiAux X n (i + 1) pw' s'

/-- Upper bound for `P_K(x)`, `x ≤ toR X`. -/
def PHi (K : ℕ) (X : ℤ) : ℤ := PHiAux X K 0 (cl (X * X)) 0

lemma PHiAux_spec {X : ℤ} {x : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ toR X) (hX1 : toR X < 1) :
    ∀ (n i : ℕ) (pw s : ℤ), x ^ (i + 2) ≤ toR pw →
      toR s + (∑ k ∈ Ico i (i + n), x ^ (k + 2) / ((k : ℝ) + 2)) + x ^ (i + n + 2) / (1 - x)
        ≤ toR (PHiAux X n i pw s) := by
  intro n
  induction n with
  | zero =>
    intro i pw s hpw
    simp only [PHiAux, Nat.add_zero, Finset.Ico_self, Finset.sum_empty, add_zero, toR_add]
    have h1x : 0 < 1 - x := by linarith
    have h1X : 0 < 1 - toR X := by linarith
    have hd : (0 : ℤ) < ZI - X := by
      have : toR X < toR ZI := by rw [toR_ZI]; exact hX1
      have := toR_lt_toR.mp this; omega
    have := le_cdiv (a := pw * ZI) hd
    have e : ((pw * ZI : ℤ) : ℝ) / ((ZI - X : ℤ) : ℝ) / ZI = toR pw / (1 - toR X) := by
      unfold toR; push_cast
      have : (ZI : ℝ) - X ≠ 0 := by
        have : (X : ℝ) < ZI := by exact_mod_cast (show X < ZI by omega)
        linarith
      field_simp [ZR_pos.ne']
    have h2 : toR pw / (1 - toR X) ≤ toR (cdiv (pw * ZI) (ZI - X)) := by
      rw [← e]; exact div_le_div_of_nonneg_right this ZR_pos.le
    have h3 : x ^ (i + 2) / (1 - x) ≤ toR pw / (1 - toR X) := by
      have hp : 0 ≤ x ^ (i + 2) := by positivity
      calc x ^ (i + 2) / (1 - x) ≤ toR pw / (1 - x) := div_le_div_of_nonneg_right hpw h1x.le
        _ ≤ toR pw / (1 - toR X) :=
          div_le_div_of_nonneg_left (hp.trans hpw) h1X (by linarith)
    linarith
  | succ n ih =>
    intro i pw s hpw
    simp only [PHiAux, forceI_eq]
    have hpw' : x ^ (i + 1 + 2) ≤ toR (cl (pw * X)) := by
      refine le_trans ?_ le_cl_mul
      rw [show i + 1 + 2 = (i + 2) + 1 by ring, pow_succ]
      exact mul_le_mul hpw hxX hx0 ((by positivity : (0 : ℝ) ≤ x ^ (i + 2)).trans hpw)
    have h1 := ih (i + 1) _ (s + cdiv pw ((i + 2 : ℕ) : ℤ)) hpw'
    refine le_trans ?_ h1
    rw [Finset.sum_eq_sum_Ico_succ_bot (show i < i + (n + 1) by omega), toR_add,
      show i + (n + 1) = i + 1 + n by omega]
    have h2 : x ^ (i + 2) / ((i : ℝ) + 2) ≤ toR (cdiv pw ((i + 2 : ℕ) : ℤ)) := by
      refine le_trans ?_ (le_toR_cdivN pw (by omega))
      push_cast
      exact div_le_div_of_nonneg_right hpw (by positivity)
    linarith

lemma P_le_PHi {X : ℤ} {x : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ toR X) (hX1 : toR X < 1) (K : ℕ) :
    P K x ≤ toR (PHi K X) := by
  have hX0 : 0 ≤ toR X := hx0.trans hxX
  have h := PHiAux_spec hx0 hxX hX1 K 0 (cl (X * X)) 0 (by
    refine le_trans ?_ le_cl_mul
    rw [zero_add, pow_two]; exact mul_le_mul hxX hxX hx0 hX0)
  simp only [toR_zero, zero_add, ← Finset.range_eq_Ico] at h
  unfold P PHi
  push_cast at h ⊢
  linarith

/-- Upper bound for `2^128 (-log(1 - p^{-a/b}) - p^{-a/b})` if `n` may be prime, `0` if `n`
is not prime (or `n < 2`). -/
def termHiK (a b : ℕ) (n : ℕ) : ℤ :=
  if n ≤ 1 then 0 else
  if K.lpf n = 0 ∨ K.lpf n = n then
    match expHi (cdiv (-((a : ℤ) * K.logLoK n)) (b : ℤ)) with
    | some X => if 0 ≤ X ∧ X < ZI then PHi (Kp n) X else ZI * ZI
    | none => ZI * ZI
  else 0

lemma PHi_nonneg {X : ℤ} (h0 : 0 ≤ X) (h1 : X < ZI) (K : ℕ) : 0 ≤ toR (PHi K X) := by
  have hX1 : toR X < 1 := by rw [← toR_ZI]; exact toR_lt_toR.mpr h1
  have := P_le_PHi le_rfl (toR_nonneg.mpr h0) hX1 K
  unfold P at this
  simp at this
  exact this

/-- For `p ≥ 2` and `σ ≥ 1/2`, `-log(1 - p^{-σ}) - p^{-σ} ≤ 4`. -/
lemma rTerm_le_four {σ : ℝ} (hσ : 1 / 2 ≤ σ) {p : ℕ} (hp : 2 ≤ p) : rTerm σ p ≤ 4 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  set x := (p : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
  have hx2 : x ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc x ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num)
            (by exact_mod_cast hp) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h34 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity) (by norm_num)]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hx1 : x < 1 := by linarith
  have h := log_term_le_P hx0 hx1 0
  unfold P at h
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at h
  unfold rTerm
  have : x ^ 2 / (1 - x) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma termHiK_nonneg (a b : ℕ) (p : ℕ) : 0 ≤ toR (termHiK a b p) := by
  have hbig : (0 : ℝ) ≤ toR (ZI * ZI) := toR_nonneg.mpr (mul_pos ZI_pos ZI_pos).le
  unfold termHiK
  split_ifs
  · rw [toR_zero]
  · split
    · split_ifs with hX01
      · exact PHi_nonneg hX01.1 hX01.2 _
      · exact hbig
    · exact hbig
  · rw [toR_zero]

lemma termHiK_spec {a b : ℕ} (hb : 0 < b) (hσ : 1 / 2 ≤ (a : ℝ) / b) (p : ℕ) :
    (if p.Prime then rTerm ((a : ℝ) / b) p else 0) ≤ toR (termHiK a b p) := by
  by_cases hp : p.Prime
  swap
  · rw [if_neg hp]; exact termHiK_nonneg a b p
  rw [if_pos hp]
  have hp2 := hp.two_le
  have hbig : rTerm ((a : ℝ) / b) p ≤ toR (ZI * ZI) := by
    refine (rTerm_le_four hσ hp2).trans ?_
    unfold toR; push_cast; rw [ZI]; norm_num
  have hl : K.lpf p = 0 ∨ K.lpf p = p := by
    by_contra hc
    push_neg at hc
    have := K.lpf_eq_minFac hp2 hc.1
    rw [hp.minFac_eq] at this
    exact hc.2 this
  unfold termHiK
  rw [if_neg (by omega), if_pos hl]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set σ := (a : ℝ) / b
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hL := K.logLoK_le (n := p) (by omega)
  set Y := cdiv (-((a : ℤ) * K.logLoK p)) (b : ℤ)
  have hY : -σ * Real.log p ≤ toR Y := by
    have h1 := le_toR_cdivN (-((a : ℤ) * K.logLoK p)) hb
    have e : toR (-((a : ℤ) * K.logLoK p)) / b = -((a : ℝ) / b) * toR (K.logLoK p) := by
      unfold toR; push_cast; ring
    rw [e] at h1
    have ha : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
    nlinarith
  have hxdef : (p : ℝ) ^ (-σ) = Real.exp (-σ * Real.log p) := by
    rw [Real.rpow_def_of_pos hp0]; ring_nf
  split
  · rename_i X hX
    have hE := le_expHi hX
    split_ifs with hX01
    · have hx0 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
      have hxX : (p : ℝ) ^ (-σ) ≤ toR X := by
        rw [hxdef]; exact (Real.exp_le_exp.mpr hY).trans hE
      have hX1 : toR X < 1 := by rw [← toR_ZI]; exact toR_lt_toR.mpr hX01.2
      unfold rTerm
      exact (log_term_le_P hx0 (lt_of_le_of_lt hxX hX1) (Kp p)).trans
        (le_trans (P_mono hx0 hxX hX1 _) (P_le_PHi (toR_nonneg.mpr hX01.1) le_rfl hX1 _))
    · exact hbig
  · exact hbig

end BSCert.Rankin
