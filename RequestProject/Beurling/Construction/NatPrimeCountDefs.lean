module

public import RequestProject.BSCert.Transc

/-!
# Kernel-checkable computations for `NatPrimeCount` (`π(N) ≤ 2N/log N`)

All checks are structurally recursive over `ℕ` and use only `Nat` arithmetic (and one
evaluation of the rational `expPt`), so that they are evaluated by the kernel
(`decide +kernel`), without `native_decide`.

* `sweepPi`: walks `N = 0, …, 1000`, carrying an upper bound `c` for `π(N)` (counting the `n`
  accepted by the trial-division test `primeK`, which accepts every prime), and checks
  `c · 7 · k ≤ 20 N` with `N ≤ 2^k` at every `N ≥ 8`; with `log 2 < 0.7` this gives
  `π(N) log N ≤ 2N`.
* `sweepS`: walks `n = 3, …, 1000`, carrying `j` with `U^j ≤ n · 10^(8j)` (`U = 110517092`,
  so `log n ≥ j/10` as `e^{1/10} ≤ U/10⁸`), and accumulates `⌈10⁷/j⌉ ≥ 10⁶/log n`.
-/

@[expose] public section

namespace NatPrimeCount

/-- `force n k = k n`, but the kernel evaluates `n` to a literal before passing it on (an
accumulator passed lazily would otherwise build a deep unevaluated term). -/
def force {α : Sort*} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

lemma force_eq {α : Sort*} (n : ℕ) (k : ℕ → α) : force n k = k n := by
  cases n <;> rfl

/-- Trial division of `n` by `d, d+1, …` while `d² ≤ n` (`true` when the fuel runs out, so the
test can only err towards `true`). -/
def tdiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, d => if n < d * d then true else if n % d = 0 then false else tdiv n f (d + 1)

/-- A test that accepts every prime (`primeK_of_prime`). -/
def primeK (n : ℕ) : Bool := decide (2 ≤ n) && tdiv n 40 2

/-- `kOf f k n` is some `k' ≥ k` with `n ≤ 2^k'` (if `n ≤ 2^(k+f)`). -/
def kOf : ℕ → ℕ → ℕ → ℕ
  | 0, k, _ => k
  | f + 1, k, n => if n ≤ 2 ^ k then k else kOf f (k + 1) n

/-- Walk `n, n+1, …, n+f-1`; `c` bounds the number of primes `< n`. At each `N ≥ 8` check
`c_N · 7 · k ≤ 20 N`, where `c_N ≥ π(N)` and `N ≤ 2^k`. -/
def sweepPi : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f + 1, n, c =>
    let c' := c + (if primeK n then 1 else 0)
    (decide (n < 8) || decide (c' * 7 * kOf 10 0 n ≤ 20 * n)) && sweepPi f (n + 1) c'

/-- `U / 10⁸ ≥ e^{1/10}`. -/
def U10 : ℕ := 110517092

/-- Increase `j` while `U^(j+1) ≤ n · 10^(8(j+1))`. -/
def bump : ℕ → ℕ → ℕ → ℕ
  | 0, _, j => j
  | f + 1, n, j => if U10 ^ (j + 1) ≤ n * 10 ^ (8 * (j + 1)) then bump f n (j + 1) else j

/-- Walk `n, …, n+f-1`, carrying `j` with `log n ≥ j/10`, and add `⌈10⁷/j⌉` to `acc`. -/
def sweepS : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, n, j, acc =>
    force (bump 80 n j) fun j' => force (acc + (10 ^ 7 + j' - 1) / j') (sweepS f (n + 1) j')

/-- The bound for `10⁶ ∑_{n=3}^{1000} 1/log n`. -/
def sumS : ℕ := sweepS 998 3 1 0

/-- `e^{1/10} ≤ U/10⁸`, by the certified rational `expPt`. -/
def e10Ok : Bool :=
  match BSCert.expPt (1 / 10) with
  | some p => decide (p.2 ≤ (U10 : ℚ) / 10 ^ 8)
  | none => false

end NatPrimeCount

end
