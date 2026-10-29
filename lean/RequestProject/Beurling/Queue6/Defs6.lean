module

public import RequestProject.Beurling.Queue6.Increment
public import RequestProject.Beurling.Queue6.Params
public import RequestProject.Beurling.Queue6.FrEvent
public import RequestProject.Beurling.Queue6.Skeleton
public import RequestProject.Beurling.Covers
public import RequestProject.Beurling.Model.Stage

/-!
# The events of Definition 6.8 for the constructed model

For `θ`, `X₀` and the jitters `ω`, `CM θ X₀ ω = Mcl θ X₀ ω` is the constructed model at the
clamped jitters `Ucl ω` (equal to `constructedModel θ X₀ ω` when the jitters lie in `[0, 1]`).
The dyadic scales are
`uS X₀ m = 2^m X₀`. The quantities of §6.3 (`Queue6.Xt`, `Queue6.Ind2`, `Queue6.ellIo`) are read
off the constructed model; the events of Table 1 are:

* E1 (`Queue6.EclE n`, `Queue6.tE1 n`): the cluster event `E_cl(z)` at the dyadic height
  `z_n = (X₀/2) 2^n`, with the cluster bound `M₁(z) = r₀ + φ(r₀) + 1`, `r₀ = ⌈L/(3ℓ)⌉ + 3`,
  `c = c(z)`, `Q = c^{1/2}` (§6.1), and time `⌈2z + H(2z)⌉`;
* E2 (`Queue6.FrE m a b`, time `b`): the event `Fr(I)` for the windows `I = [a, b)` of `𝓘_u`
  (`Queue6.Adm`: integer endpoints, `u ≤ b ≤ 3u`, `b - a ≤ W_len(u)`), with
  `λ = 4 L`, `M₁ = M_q(u)`, `K = K₀ + 5`;
* E4 (`Queue6.LandE m i j`, time `⌈max J + H(max J)⌉`): the landing event `Land(J)` of
  Lemma 6.1 for the windows `J = [P + i/2, P + j/2)` of `𝒥_P`, `P = uS m`;
* the queue constraints `Queue6.okQ j = {Q_j ≤ B(s_j)}` with times `Queue6.tq j = ⌈s_{j+1}⌉ + 1`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueBound QueueMono
  Greedy QueueDet SlotModel

namespace Queue6

variable (θ : ℝ) (X₀ : ℕ)

/-- The constructed model at `ω`, evaluated at the clamped jitters `Ucl ω` (equal to `ω` almost
surely), so that it is adapted (Model/Stage.lean). -/
noncomputable abbrev CM (ω : JitterΩ) : SlotModel X₀ := Mcl θ X₀ ω

/-- The dyadic scale `2^m X₀`. -/
noncomputable def uS (m : ℕ) : ℝ := 2 ^ m * (X₀ : ℝ)

/-! ### The quantities of §6.3 -/

/-- The truncated count `X̃_q(I) = min(X⁽¹⁾_q(I), 2M₁)` of the prime decided at relative slot
`k + 1`, for `I = [a, b)` at scale `m`. -/
noncomputable def Xt (m : ℕ) (a b : ℤ) (k : ℕ) (ω : JitterΩ) : ℝ :=
  min (Xcount (CM θ X₀ ω) (Ucl ω) a b k 1) (2 * Mq X₀ (uS X₀ m))

/-- The indicator of `X⁽²⁾_q(I) ≥ 1`. -/
noncomputable def Ind2 (a b : ℤ) (k : ℕ) (ω : JitterΩ) : ℝ :=
  if 1 ≤ X2count (CM θ X₀ ω) (Ucl ω) a b k then 1 else 0

/-- `ℓ_jit(I)` for the constructed model. -/
noncomputable def ellIo (a b : ℤ) (ω : JitterΩ) : ℕ := ellI θ (CM θ X₀ ω) (Ucl ω) a b

/-! ### E2: the events `Fr(I)` -/

/-- **The windows of `𝓘_u`** at scale `m`: integer endpoints, `u ≤ b ≤ 3u`, `a ≤ b`,
`b - a ≤ W_len(u)`. -/
def Adm (m : ℕ) (a b : ℤ) : Prop :=
  uS X₀ m ≤ b ∧ (b : ℝ) ≤ 3 * uS X₀ m ∧ a ≤ b ∧ ((b - a : ℤ) : ℝ) ≤ Wlen X₀ (uS X₀ m)

open Classical in
/-- **The event `Fr(I)`** (E2) for an admissible window, `univ` otherwise. -/
noncomputable def FrE (m : ℕ) (a b : ℤ) : Set JitterΩ :=
  if Adm X₀ m a b then
    FrAll jitterFiltration jitterMeasure (Xt θ X₀ m a b) (Ind2 θ X₀ a b) (ellIo θ X₀ a b)
      (Mq X₀ (uS X₀ m)) (4 * Lq (uS X₀ m)) (K0 X₀ (uS X₀ m) + 5)
  else univ

/-- The time `t(I) = b` of `Fr(I)`. -/
def tE2 (b : ℤ) : ℕ := b.toNat

/-! ### E1: the cluster events -/

/-- The dyadic height `z_n = (X₀/2) 2^n`. -/
noncomputable def zH (n : ℕ) : ℝ := (X₀ : ℝ) / 2 * 2 ^ n

/-- The rank threshold `r₀ = ⌈L/(3ℓ)⌉ + 3` at height `z`. -/
noncomputable def r0At (z : ℝ) : ℕ := ⌈Real.log z / (3 * Real.log (Real.log z))⌉₊ + 3

/-- The capacity threshold `c(z)` (Theorem 6.23). -/
noncomputable def cAt (z : ℝ) : ℝ := Real.exp (logcAt X₀ z)

/-- **The cluster bound** `M₁(z) = r₀ + φ(r₀) + 1`, `φ(u) = c + u c^{1/2} + u(u+1)/2`. -/
noncomputable def M1cl (z : ℝ) : ℝ :=
  r0At z + Covers.phi (cAt X₀ z) (Real.sqrt (cAt X₀ z)) (r0At z) + 1

/-- **The cluster event `E_cl(z)`** (Proposition 6.11) at the dyadic height `z_n`: every grid
window holds at most `M₁(z)` elements of `𝒩`. -/
def EclE (n : ℕ) : Set JitterΩ :=
  {ω | ∀ k : ℤ, zH X₀ n ≤ k * gridDelta (zH X₀ n) → k * gridDelta (zH X₀ n) < 2 * zH X₀ n →
    (winCount (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) (k * gridDelta (zH X₀ n))
      ((k + 2) * gridDelta (zH X₀ n)) : ℝ) ≤ M1cl X₀ (zH X₀ n)}

/-- The time `t_z = ⌈2z + H(2z)⌉` of `E_cl(z)`. -/
noncomputable def tE1 (n : ℕ) : ℕ := ⌈2 * zH X₀ n + capH X₀ (2 * zH X₀ n)⌉₊

/-! ### E4: the landing events -/

/-- The landing window `J = [P + i/2, P + j/2)`, `P = 2^m X₀`. -/
noncomputable def Jlo (m i : ℕ) : ℝ := uS X₀ m + i / 2

/-- The right end `P + j/2`. -/
noncomputable def Jhi (m j : ℕ) : ℝ := uS X₀ m + j / 2

/-- The windows of `𝒥_P`: `i < j`, `j - i ≤ 12 H(P)`, `P + j/2 ≤ 4P + 1`. -/
def AdmJ (m i j : ℕ) : Prop :=
  i < j ∧ ((j : ℝ) - i) ≤ 12 * capH X₀ (uS X₀ m) ∧ Jhi X₀ m j ≤ 4 * uS X₀ m + 1

open Classical in
/-- The indicator that the prime decided at relative slot `k + 1` is a candidate for `J` (its
slot start is within `H(s)/2` of `J`, selected by decision slot) and lands in `J`. -/
noncomputable def landInd (m i j k : ℕ) (ω : JitterΩ) : ℝ :=
  if placedAt (CM θ X₀ ω) k ∧
      Jlo X₀ m i - capH X₀ ((CM θ X₀ ω).slot (k + 1)) / 2 ≤ (CM θ X₀ ω).slot (k + 1) ∧
      (CM θ X₀ ω).slot (k + 1) ≤ Jhi X₀ m j + capH X₀ ((CM θ X₀ ω).slot (k + 1)) / 2 ∧
      Jlo X₀ m i ≤ primeValueOf (CM θ X₀ ω) (capH X₀) (Ucl ω) k ∧
      primeValueOf (CM θ X₀ ω) (capH X₀) (Ucl ω) k < Jhi X₀ m j
  then 1 else 0

/-- The sure bound `μ̄(J) = (|J| + H₊ + 2) min(1, |J|/H₋)`, `H₋ = H(P/2)`, `H₊ = H(8P)`. -/
noncomputable def muBar (m i j : ℕ) : ℝ :=
  (((j : ℝ) - i) / 2 + capH X₀ (8 * uS X₀ m) + 2) *
    min 1 ((((j : ℝ) - i) / 2) / capH X₀ (uS X₀ m / 2))

open Classical in
/-- **The landing event `Land(J)`** (E4, Lemma 6.1) for `J ∈ 𝒥_P`, `univ` otherwise:
`|Λ(J) - μ(J)| < √(2μ̄(J)λ_P) + 2λ_P/3` along the slots, `λ_P = 4 log P`. -/
noncomputable def LandE (m i j : ℕ) : Set JitterΩ :=
  if AdmJ X₀ m i j then
    {ω | ∀ n, |∑ k ∈ Finset.range n, (landInd θ X₀ m i j k ω -
      (jitterMeasure[landInd θ X₀ m i j k | jitterFiltration k]) ω)| <
        Real.sqrt (2 * muBar X₀ m i j * (4 * Real.log (uS X₀ m))) +
          2 * (4 * Real.log (uS X₀ m)) / 3}
  else univ

/-- The time `⌈max J + H(max J)⌉` of `Land(J)`. -/
noncomputable def tE4 (m j : ℕ) : ℕ := ⌈Jhi X₀ m j + capH X₀ (Jhi X₀ m j)⌉₊

/-! ### The queue constraints -/

/-- The queue constraint at relative slot `j`: `Q_j ≤ B(s_j)`. -/
def okQ (j : ℕ) : Set JitterΩ :=
  {ω | ((CM θ X₀ ω).queue j : ℝ) ≤ queueBScale X₀ ((CM θ X₀ ω).slot j)}

/-- The time `t_j = ⌈s_{j+1}⌉ + 1` of the queue constraint at slot `j`. -/
noncomputable def tq (j : ℕ) (ω : JitterΩ) : ℕ := ⌈(CM θ X₀ ω).slot (j + 1)⌉₊ + 1

end Queue6

end
