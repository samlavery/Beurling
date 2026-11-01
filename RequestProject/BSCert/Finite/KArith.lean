module

public import RequestProject.BSCert.FX.Log
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Kernel-checkable arithmetic for the finite computations of Section 5

Replacements, evaluated by the kernel (`decide +kernel`), for the checks of
`finite_checks.py`, in the fixed point of `BSCert.FX` (`toR a = a / 2^128`):

* `lpf n`: least prime factor by trial division (`lpf_eq_minFac`; `0` if the fuel runs out);
* `powDiv p f n`: divides out `p` (`= 1` iff `n` is a power of `p`, given enough fuel);
* `logLoK`, `logHiK`: bounds for `log n`; `vmLoK`, `vmHiK`: bounds for `Λ(n)`;
* `sumUp`: running sums of upper bounds; `encLoop`: running enclosures with a check at every
  step; `winLoopK`: running window sums `∑_{n/2 < k ≤ n}`.
-/

@[expose] public section

namespace BSCert.FiniteN.K

open BSCert.FX Finset ArithmeticFunction

/-! ## Least prime factor -/

/-- The least divisor `≥ d` of the odd number `n`, trying `d, d+2, …` (or `n` if there is
none below `√n`); `0` if the fuel runs out. -/
def lpfAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, d => if n < d * d then n else if n % d = 0 then d else lpfAux n f (d + 2)

/-- The least prime factor of `n ≥ 2` (or `0`). -/
def lpf (n : ℕ) : ℕ := if n % 2 = 0 then 2 else lpfAux n n 3

lemma lpfAux_spec {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) : ∀ f d, 2 ≤ d → d % 2 = 1 →
    (∀ e, 2 ≤ e → e < d → ¬ e ∣ n) → lpfAux n f d ≠ 0 → lpfAux n f d = n.minFac := by
  intro f
  induction f with
  | zero => intro d _ _ _ h; simp [lpfAux] at h
  | succ f ih =>
    intro d hd hdodd hno h
    have hmin : d ≤ n.minFac := by
      by_contra hc
      push_neg at hc
      exact hno _ (Nat.Prime.two_le (Nat.minFac_prime (by omega))) hc (Nat.minFac_dvd n)
    unfold lpfAux at h ⊢
    split_ifs at h ⊢ with h1 h2
    · -- no divisor below `√n`: `n` is prime
      by_contra hne
      have hnp : ¬ n.Prime := fun hp => hne (hp.minFac_eq).symm
      have := Nat.minFac_sq_le_self (by omega) hnp
      have : d * d ≤ n.minFac ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hmin hmin
      omega
    · exact (le_antisymm (Nat.minFac_le_of_dvd hd (Nat.dvd_of_mod_eq_zero h2)) hmin).symm
    · refine ih (d + 2) (by omega) (by omega) (fun e he1 he2 hdvd => ?_) h
      rcases (show e < d ∨ e = d ∨ e = d + 1 by omega) with he | rfl | rfl
      · exact hno e he1 he hdvd
      · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
      · -- `d + 1` is even and `n` is odd
        have : 2 ∣ n := (Nat.dvd_of_mod_eq_zero (by omega : (d + 1) % 2 = 0)).trans hdvd
        omega

lemma lpf_eq_minFac {n : ℕ} (hn : 2 ≤ n) (h : lpf n ≠ 0) : lpf n = n.minFac := by
  unfold lpf at h ⊢
  split_ifs at h ⊢ with h2
  · exact (Nat.minFac_eq_two_iff n).mpr (Nat.dvd_of_mod_eq_zero h2) |>.symm
  · exact lpfAux_spec hn (by omega) n 3 (by norm_num) (by norm_num) (fun e he1 he2 hdvd => by
      have : e = 2 := by omega
      subst this; omega) h

/-! ## Prime powers -/

/-- Divide out `p` (at most `f` times). -/
def powDiv (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | f + 1, n => if n % p = 0 then powDiv p f (n / p) else n

lemma powDiv_pow {p : ℕ} (hp : 2 ≤ p) : ∀ k f, k ≤ f → powDiv p f (p ^ k) = 1 := by
  intro k
  induction k with
  | zero =>
    intro f _
    cases f with
    | zero => rfl
    | succ f => simp [powDiv, Nat.mod_eq_of_lt (show 1 < p by omega)]
  | succ k ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [powDiv, pow_succ, Nat.mul_mod_left, if_true]
    rw [Nat.mul_div_cancel _ (by omega)]
    exact ih f (by omega)

lemma powDiv_eq_one {p : ℕ} : ∀ f n, powDiv p f n = 1 → ∃ k, n = p ^ k := by
  intro f
  induction f with
  | zero => intro n h; exact ⟨0, by simpa [powDiv] using h⟩
  | succ f ih =>
    intro n h
    simp only [powDiv] at h
    split_ifs at h with h1
    · obtain ⟨k, hk⟩ := ih _ h
      refine ⟨k + 1, ?_⟩
      rw [pow_succ, ← hk]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)).symm
    · exact ⟨0, by simpa using h⟩

/-! ## Logarithms of integers -/

/-- Upper bound for `2^128 log (X / 2^128)` (`X > 0`), with the fallback `log y ≤ y - 1`. -/
def logHiX (X : ℤ) : ℤ :=
  match logHi X with
  | some h => h
  | none => X - ZI

/-- Lower bound for `2^128 log (X / 2^128)` (`X ≥ 2^128`), with the fallback `0`. -/
def logLoX (X : ℤ) : ℤ :=
  match logLo X with
  | some l => l
  | none => 0

lemma le_logHiX {X : ℤ} (hX : 0 < X) : Real.log (toR X) ≤ toR (logHiX X) := by
  unfold logHiX
  split
  · rename_i h hh; exact le_logHi hX hh
  · rw [toR_sub, toR_ZI]; exact Real.log_le_sub_one_of_pos (toR_pos.mpr hX)

lemma logLoX_le {X : ℤ} (hX : ZI ≤ X) : toR (logLoX X) ≤ Real.log (toR X) := by
  unfold logLoX
  split
  · rename_i l hl; exact logLo_le (lt_of_lt_of_le ZI_pos hX) hl
  · rw [toR_zero]; exact Real.log_nonneg (by rw [← toR_ZI]; exact toR_le_toR.mpr hX)

/-- Upper bound for `2^128 log n`. -/
def logHiK (n : ℕ) : ℤ := logHiX ((n : ℤ) * ZI)

/-- Lower bound for `2^128 log n`. -/
def logLoK (n : ℕ) : ℤ := logLoX ((n : ℤ) * ZI)

lemma toR_natMul (n : ℕ) : toR ((n : ℤ) * ZI) = n := by
  unfold toR; push_cast; field_simp [ZR_pos.ne']

lemma log_le_logHiK {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ toR (logHiK n) := by
  have := le_logHiX (X := (n : ℤ) * ZI) (mul_pos (by exact_mod_cast hn) ZI_pos)
  rwa [toR_natMul] at this

lemma logLoK_le {n : ℕ} (hn : 1 ≤ n) : toR (logLoK n) ≤ Real.log n := by
  have := logLoX_le (X := (n : ℤ) * ZI) (le_mul_of_one_le_left ZI_pos.le (by exact_mod_cast hn))
  rwa [toR_natMul] at this

lemma logHiK_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ toR (logHiK n) :=
  (Real.log_nonneg (by exact_mod_cast hn)).trans (log_le_logHiK hn)

/-! ## The von Mangoldt function -/

/-- Upper bound for `2^128 Λ(n)`. -/
def vmHiK (n : ℕ) : ℤ :=
  if n ≤ 1 then 0 else
  if lpf n = 0 then logHiK n else
  if powDiv (lpf n) n n = 1 then logHiK (lpf n) else 0

/-- Lower bound for `2^128 Λ(n)`. -/
def vmLoK (n : ℕ) : ℤ :=
  if n ≤ 1 then 0 else
  if lpf n = 0 then 0 else
  if powDiv (lpf n) n n = 1 then logLoK (lpf n) else 0

lemma vmHiK_spec (n : ℕ) : Λ n ≤ toR (vmHiK n) := by
  unfold vmHiK
  split_ifs with h1 h2 h3
  · interval_cases n <;> simp [toR_zero]
  · rw [vonMangoldt_apply]
    split_ifs with hpp
    · refine le_trans ?_ (log_le_logHiK (by omega))
      exact Real.log_le_log (by exact_mod_cast (Nat.minFac_pos n))
        (by exact_mod_cast Nat.minFac_le (by omega))
    · exact logHiK_nonneg (by omega)
  · rw [lpf_eq_minFac (by omega) h2]
    rw [vonMangoldt_apply]
    split_ifs
    · exact log_le_logHiK (Nat.minFac_pos n)
    · exact logHiK_nonneg (Nat.minFac_pos n)
  · rw [toR_zero, vonMangoldt_apply]
    split_ifs with hpp
    · exfalso
      obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      rw [lpf_eq_minFac (by omega) h2, Nat.Prime.pow_minFac hq hk.ne'] at h3
      exact h3 (powDiv_pow hq.two_le k _ (Nat.lt_pow_self hq.one_lt).le)
    · exact le_rfl

lemma vmLoK_spec (n : ℕ) : toR (vmLoK n) ≤ Λ n := by
  unfold vmLoK
  split_ifs with h1 h2 h3
  · rw [toR_zero]; exact vonMangoldt_nonneg
  · rw [toR_zero]; exact vonMangoldt_nonneg
  · rw [lpf_eq_minFac (by omega) h2] at h3 ⊢
    obtain ⟨k, hk⟩ := powDiv_eq_one _ _ h3
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    have hpp : IsPrimePow n := (isPrimePow_nat_iff _).mpr ⟨_, k, hp, Nat.pos_of_ne_zero hk0, hk.symm⟩
    rw [vonMangoldt_apply, if_pos hpp]
    exact logLoK_le (Nat.minFac_pos n)
  · rw [toR_zero]; exact vonMangoldt_nonneg

/-- Upper bound for `2^128 log n/(n(n-1))` if `n` is prime, `0` if `n` is not prime. -/
def cm3HiK (n : ℕ) : ℤ :=
  if n ≤ 1 then 0 else
  if lpf n = 0 ∨ lpf n = n then cdiv (logHiK n) ((n * (n - 1) : ℕ) : ℤ) else 0

lemma toR_cdivN_ge (a : ℤ) {d : ℕ} (hd : 0 < d) : toR a / d ≤ toR (cdiv a (d : ℤ)) :=
  le_toR_cdivN a hd

lemma toR_fdivN_le (a : ℤ) {d : ℕ} (hd : 0 < d) : toR (fdiv a (d : ℤ)) ≤ toR a / d :=
  toR_fdivN a hd

/-! ## Running sums -/

/-- `B + ∑_{i=n}^{n+f-1} h i`. -/
def sumUp (h : ℕ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, _, B => B
  | f + 1, n, B => forceI (B + h n) (sumUp h f (n + 1))

lemma sumUp_spec (h : ℕ → ℤ) (g : ℕ → ℝ) (hg : ∀ i, g i ≤ toR (h i)) :
    ∀ f n B, toR B + ∑ i ∈ Ico n (n + f), g i ≤ toR (sumUp h f n B) := by
  intro f
  induction f with
  | zero => intro n B; simp [sumUp]
  | succ f ih =>
    intro n B
    simp only [sumUp, forceI_eq]
    refine le_trans ?_ (ih (n + 1) (B + h n))
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), toR_add, show n + (f + 1) = n + 1 + f by omega]
    linarith [hg n]

lemma sumUp_add (h : ℕ → ℤ) : ∀ a b n B, sumUp h (a + b) n B = sumUp h b (n + a) (sumUp h a n B) := by
  intro a
  induction a with
  | zero => intro b n B; simp [sumUp]
  | succ a ih =>
    intro b n B
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [sumUp, forceI_eq]
    rw [ih, show n + 1 + a = n + (a + 1) by omega]

/-- The checked running-enclosure loop: adds `lo i`, `hi i` and checks `ok i A B`. -/
def encLoop (lo hi : ℕ → ℤ) (ok : ℕ → ℤ → ℤ → Bool) : ℕ → ℕ → ℤ → ℤ → Bool
  | 0, _, _, _ => true
  | f + 1, n, A, B =>
    forceI (A + lo n) fun A' => forceI (B + hi n) fun B' => ok n A' B' && encLoop lo hi ok f (n + 1) A' B'

theorem encLoop_spec (lo hi : ℕ → ℤ) (ok : ℕ → ℤ → ℤ → Bool) (g : ℕ → ℝ)
    (hg : ∀ i, toR (lo i) ≤ g i ∧ g i ≤ toR (hi i)) :
    ∀ f n A B, encLoop lo hi ok f n A B = true →
      toR A ≤ ∑ i ∈ range n, g i → ∑ i ∈ range n, g i ≤ toR B →
      ∀ k, n ≤ k → k < n + f → ∃ A' B' : ℤ,
        toR A' ≤ ∑ i ∈ range (k + 1), g i ∧ ∑ i ∈ range (k + 1), g i ≤ toR B' ∧
          ok k A' B' = true := by
  intro f
  induction f with
  | zero => intro n A B _ _ _ k h1 h2; omega
  | succ f ih =>
    intro n A B h hA hB k hk1 hk2
    simp only [encLoop, forceI_eq, Bool.and_eq_true] at h
    have hA' : toR (A + lo n) ≤ ∑ i ∈ range (n + 1), g i := by
      rw [Finset.sum_range_succ, toR_add]; linarith [(hg n).1]
    have hB' : ∑ i ∈ range (n + 1), g i ≤ toR (B + hi n) := by
      rw [Finset.sum_range_succ, toR_add]; linarith [(hg n).2]
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
    · exact ⟨_, _, hA', hB', h.1⟩
    · exact ih (n + 1) _ _ h.2 hA' hB' k hlt (by omega)

/-! ## Window sums `∑_{k/2 < i ≤ k}` -/

lemma window_succ {M : Type*} [AddCommGroup M] (v : ℕ → M) (k : ℕ) :
    ∑ i ∈ Ioc ((k + 1) / 2) (k + 1), v i =
      ∑ i ∈ Ioc (k / 2) k, v i + v (k + 1) - (if (k + 1) % 2 = 0 then v ((k + 1) / 2) else 0) := by
  split_ifs with h
  · have e : (k + 1) / 2 = k / 2 + 1 := by omega
    rw [e, Finset.sum_Ioc_succ_top (by omega)]
    have := Finset.sum_Ioc_consecutive v (Nat.le_succ (k / 2)) (show k / 2 + 1 ≤ k by omega)
    rw [← this, Nat.Ioc_succ_singleton, Finset.sum_singleton]
    abel
  · have e : (k + 1) / 2 = k / 2 := by omega
    rw [e, Finset.sum_Ioc_succ_top (by omega)]
    abel

/-- The incremental window check: `D` is the window sum at `k`; checks `ok (k+1) D'`. -/
def winLoopK (v : ℕ → ℤ) (ok : ℕ → ℤ → Bool) : ℕ → ℕ → ℤ → Bool
  | 0, _, _ => true
  | f + 1, k, D =>
    forceI (D + v (k + 1) - (if (k + 1) % 2 = 0 then v ((k + 1) / 2) else 0)) fun D' =>
      ok (k + 1) D' && winLoopK v ok f (k + 1) D'

theorem winLoopK_spec (v : ℕ → ℤ) (ok : ℕ → ℤ → Bool) : ∀ f k,
    winLoopK v ok f k (∑ i ∈ Ioc (k / 2) k, v i) = true →
    ∀ k', k < k' → k' ≤ k + f → ok k' (∑ i ∈ Ioc (k' / 2) k', v i) = true := by
  intro f
  induction f with
  | zero => intro k _ k' h1 h2; omega
  | succ f ih =>
    intro k h k' hk1 hk2
    simp only [winLoopK, forceI_eq, Bool.and_eq_true] at h
    rw [← window_succ] at h
    rcases Nat.eq_or_lt_of_le (show k + 1 ≤ k' by omega) with rfl | hlt
    · exact h.1
    · exact ih (k + 1) h.2 k' hlt (by omega)

end BSCert.FiniteN.K
