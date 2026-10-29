module

public import RequestProject.Beurling.Queue6.Cluster6
public import RequestProject.Beurling.Queue6.Geometry

/-!
# The event family of Definition 6.8 and the named inputs from §3, §5, App A

The base family `E0` collects the events of Table 1:
`E1` (`E1ev`, the cluster events in the window model of Appendix A), `E2` (`FrE`, the events
`Fr(I)`), `E4` (`LandE`, the landing events), the target bounds `T(x) ≤ 3x` (`tB`, used by the
window model) and the events `E3`, `E3′` of §5 (`Sec5Family`, provided by Section 5). The
paper's good
event `Good(<t)` is `G0 t = paperGood E0 t0 okQ tq t` (events and queue constraints with time
`< t`).

`QueueInputs θ X₀` lists the inputs of §6.3 – §6.4 that are results of other sections, each a
named statement of the paper for the constructed model:

* `land` — **(F1)–(F2)**: the compensator of the landing count is surely at most `μ̄(J)`
  (§6.2, "By (F1)–(F2) this is a sure bound");
* `sec5`, `budget5` — **Lemma 5.22 and Table 1 (E3, E3′)**: the noise events of §5 and their
  failure probabilities on the good event, `≤ 1.2 u^{-2}` per scale;
* `R1` — **Corollary 5.40 (R1′ on every window)**, the middle inequality
  `ℓ_jit(I) - Comp(I) ≥ 0.399 |I ∩ [X₀, ∞)|/L - 2` with `L = log max I`, on `Good(< max I)`,
  for the windows of `𝓘_u`; `Comp(I)` is read through the partial sums of the conditional means
  of the truncated counts (each at most `Comp(I)`);
* `comp2` — **Corollary 5.40 (`Comp⁽²⁾(I) ≤ s₂ |I|`) with the bound `s₂|I| ≤ e^{-√L} ≤ 1`
  of the proof of Theorem 6.6(i)**;
* `tbound` — **Lemma 3.4 (target error) on the good event**: `T(x) ≤ 3x` up to `u/2` fails only
  on a null part of `Good`;
* `slotHyp` — the standing hypotheses on `H` of Lemma A.3 (`SlotHyp`: `H(v)/v` decreasing, …);
* `S3d`, `multi`, `cover` — **Lemma A.6 (S3)(d)**, **Lemma A.5 + Theorem A.10 for several runs**
  (`MultiRunSkeletonBound`) and **the Cover Bound** (`CoverSkeletonBound`, Lemmas 6.17–6.19) at
  the dyadic heights `z ≥ X₀`, from which Proposition 6.11 is proved (`eclW_fail`);
* `cluster0` — **Proposition 6.11 at the height `z = X₀/2`** (the window model of `RankFull` is
  stated for `z ≥ X₀`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueBound QueueMono
  Greedy QueueDet SlotModel RankFull RankFull.Config

namespace Queue6

/-- **The events `E3`, `E3′` of §5** (Lemma 5.22): a countable family with times and scales. -/
structure Sec5Family where
  ι : Type
  [count : Countable ι]
  E : ι → Set JitterΩ
  time : ι → ℕ
  scale : ι → ℕ

attribute [instance] Sec5Family.count

variable (θ : ℝ) (X₀ : ℕ) (D : Sec5Family)

open Classical in
/-- **The cluster event E1 at the height `z_n`** (`EclW`, in the window model). -/
noncomputable def E1ev (n : ℕ) : Set JitterΩ :=
  if h : Cond θ X₀ ∧ Even X₀ then EclW h.1 h.2 n else univ

/-- The index type of the base family: `E1 ⊕ E2 ⊕ E4 ⊕ (tB ⊕ E3)`. -/
abbrev ι0 : Type := ℕ ⊕ ((ℕ × ℤ × ℤ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ ⊕ D.ι)))

/-- **The events of Table 1.** -/
noncomputable def E0 : ι0 D → Set JitterΩ :=
  Sum.elim (E1ev θ X₀) (Sum.elim (fun p => FrE θ X₀ p.1 p.2.1 p.2.2)
    (Sum.elim (fun p => LandE θ X₀ p.1 p.2.1 p.2.2) (Sum.elim (tB (θ := θ) (X₀ := X₀)) D.E)))

/-- Their times. -/
noncomputable def t0 : ι0 D → ℕ :=
  Sum.elim (tE1 X₀) (Sum.elim (fun p => tE2 p.2.2)
    (Sum.elim (fun p => tE4 X₀ p.1 p.2.2) (Sum.elim (ttB X₀) D.time)))

/-- Their scales. -/
def s0 : ι0 D → ℕ :=
  Sum.elim id (Sum.elim (fun p => p.1) (Sum.elim (fun p => p.1) (Sum.elim id D.scale)))

/-- **`Good(<t)`** (Definition 6.8). -/
def G0 (t : ℕ) : Set JitterΩ := paperGood (E0 θ X₀ D) (t0 X₀ D) (okQ θ X₀) (tq θ X₀) t

/-- The drift bound R1′ in the form used by Theorem 6.6, for the window `[a, b)` at scale `m`. -/
def R1cond (m : ℕ) (a b : ℤ) (ω : JitterΩ) : Prop :=
  ∀ n, ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω ≤
    (ellIo θ X₀ a b ω : ℝ) * (1 - 0.15 / Lq (uS X₀ m)) + 3

/-- **The inputs of §6.3–§6.4 from other sections** (see the module docstring). -/
structure QueueInputs where
  land : ∀ m i j, AdmJ X₀ m i j → ∀ᵐ ω ∂jitterMeasure, ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[landInd θ X₀ m i j k | jitterFiltration k]) ω ≤
      muBar X₀ m i j
  sec5 : Sec5Family
  budget5 : ∀ m, ∑' i : {i // sec5.scale i = m},
    jitterMeasure ((sec5.E i)ᶜ ∩ QC (okQ θ X₀) (tq θ X₀) (sec5.time i) ∩
      goodBefore (Sum.elim (E1ev θ X₀) sec5.E) (Sum.elim (tE1 X₀) sec5.time) (sec5.time i)) ≤
    ENNReal.ofReal (1.2 / uS X₀ m ^ 2)
  R1 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ sec5 (tE2 b) → ∀ n,
    0.399 * ((b : ℝ) - max (a : ℝ) X₀) / Real.log b - 2 ≤
      (ellIo θ X₀ a b ω : ℝ) -
        ∑ k ∈ Finset.range n, (jitterMeasure[Xt θ X₀ m a b k | jitterFiltration k]) ω
  comp2 : ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ sec5 (tE2 b) → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤ 1
  tbound : ∀ n, jitterMeasure ((tB (θ := θ) (X₀ := X₀) n)ᶜ ∩ G0 θ X₀ sec5 (ttB X₀ n)) = 0
  slotHyp : SlotHyp (capH X₀) X₀
  cluster0 : jitterMeasure ((E1ev θ X₀ 0)ᶜ ∩ G0 θ X₀ sec5 (tE1 X₀ 0)) ≤
    ENNReal.ofReal (Real.log (zH X₀ 0) ^ (-2 : ℝ))
  S3d : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n →
    S3dHyp hc hev (NpZ (zH X₀ n)) (DmaxZ (zH X₀ n)) (smaxZ (zH X₀ n)) (AtopZ X₀ (zH X₀ n))
  multi : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n → ∀ k ∈ gridW X₀ n,
    MultiRunSkeletonBound jitterMeasure
      (G0 θ X₀ sec5 (tE1 X₀ n) ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) (r0At (zH X₀ n))
      (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n)) (EuZ X₀ (zH X₀ n))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
        (gwin (zH X₀ n) k)) E l)
  cover : ∀ (hc : Cond θ X₀) (hev : Even X₀) (n : ℕ), 1 ≤ n →
    ∀ j, ∀ k ∈ gridW X₀ n, ∀ r < r0At (zH X₀ n), ∀ C ∈ CSet r j, ∀ lab ex s4,
      ExOK C ex → ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound jitterMeasure
          (G0 θ X₀ sec5 (tE1 X₀ n) ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) r
          (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n))
          (EuZ X₀ (zH X₀ n)) (zH X₀ n) (fun i => tauSlot (capH X₀) X₀ i) (exExcess ex)
          (r - C.card) l (fun ω => cfgSkelCount (DpZ X₀ (zH X₀ n)) (r0At (zH X₀ n)) 0 0
            (tailOf (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k))
            (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k)) r C lab ex s4)

/-! ### The final family -/

/-- The null events of R1′ (the drift bound holds off a null set of `Good(< max I)`). -/
def Nev (p : ℕ × ℤ × ℤ) : Set JitterΩ :=
  {ω | Adm X₀ p.1 p.2.1 p.2.2 → ω ∈ G0 θ X₀ D (tE2 p.2.2) → R1cond θ X₀ p.1 p.2.1 p.2.2 ω}

/-- The index type of the final family: the modified events of Table 1, the null events of R1′,
the complement of `𝒩₌`, and "all stages good". -/
abbrev ιF : Type := ι0 D ⊕ ((ℕ × ℤ × ℤ) ⊕ (Unit ⊕ Unit))

/-- **The event family** (Definition 6.8 with the queue constraints folded into the events). -/
noncomputable def EF : ιF D → Set JitterΩ :=
  Sum.elim (withQC (E0 θ X₀ D) (t0 X₀ D) (okQ θ X₀) (tq θ X₀))
    (Sum.elim (Nev θ X₀ D) (Sum.elim (fun _ => (tiesEvent θ X₀)ᶜ) fun _ => SG (θ := θ) (X₀ := X₀)))

/-- Its times. -/
noncomputable def tF : ιF D → ℕ := Sum.elim (t0 X₀ D) (Sum.elim (fun _ => 0) fun _ => 0)

/-- Its scales. -/
def sF : ιF D → ℕ := Sum.elim (s0 D) (Sum.elim (fun p => p.1) fun _ => 0)

end Queue6

end
