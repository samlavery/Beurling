# R18: independent check of correction #77 and of the repairs for R17's items

The checker is a fresh agent that did not write the repairs. It worked on a snapshot of the tree after the R17 items and the
#77 repair. pre77 + c77.patch is byte-identical to that snapshot; the patch has 22 hunks over 8 files. The scripts are in
`review/recheck/r18/`, all in exact rational arithmetic:
- `toy.py`, `toy2.py`, `toy3.py`: slot toys;
- `consts.py`: constants;
- `render.py`, `perhunk.py`: rendering checks.

**Verdict.**
- **#77:** CONFIRMED WITH FIXES.
- **R17 items:** CONFIRMED WITH FIXES.
- Nothing is BLOCKING. The lead applied every fix below. Each is marked FIXABLE (F) or COSMETIC (C).

## A. #77: the mathematics is correct

**A1. Well-definedness, for every ϑ_s and ω.**
- T is non-decreasing (because T′_cont > 0 by (G1)), right-continuous and unbounded.
- So {T ≥ c} = [s(c), ∞), J_j = [s_j, s_{j+1}) exactly, and T ∈ [j+ϑ, j+1+ϑ) on J_j.
- s_j > X₀.
- The classification of slots is exhaustive. A jump slot is non-empty and holds exactly one jump. A non-empty continuous
  slot holds no jump.
- An empty slot occurs exactly at a tie, and the next slot is then a jump slot.
- `toy.py` covered 25 seeds × 4 offsets: 55,344 jump slots, 45,971 continuous slots, 15,236 ties and 14,309 runs of jump
  slots. Every claim held exactly.

**A2. The counting fact is true.**
- Between consecutive continuous starts, ∫T′_cont = 1. It holds exactly in all ≈46k gaps.
- It still holds with jumps of size 2. What breaks there is "A_j ≥ 1 on jump slots", so excluding the null event is
  necessary and sufficient.
- The text only sketched the proof (#77-1).

**A3. 𝒩₌ is null for every ϑ_s.** After cancelling, the latest-decided prime lies on one side only, and given the past it is
uniform on a box. The checker confirmed:
- rigid integers vs jittered composites;
- equal primes with different exponents;
- unique factorisation among rational elements;
- that there is no circularity;
- P(τ < ∞) ≤ Σ + P(𝒩₌) = Σ;
- that the sure bounds inside Freedman need only hold almost surely.

**A4. Every consumer holds off 𝒩₌.** The checker went through:
- the greedy rule, C2, Lemma count (including a tie at j₀) and Lindley;
- Cor lag: `toy2.py` placed 4,781 primes, 1,870 of them at empty slots; V_j = j+1+Q_j and the decomposition of D are exact,
  and the constants +3/+4 hold;
- Lemma excess, 04b, 04a T̃′, (G1) and the slot length;
- Remark horizon, the predictability of t_j, and (D);
- the Thm queue sandwich (left edge read closed) and Lindley step;
- 04d, Cor r1, Lemma landing, 04g, 04e, 06 and App. A;
- the start-up of Prop La, and (F2).

**A5. Adaptedness.** {s_{j+1} ≤ u} = {T(u) ≥ j+1+ϑ} ∈ F_{u−H(u)}, so t_j is predictable.

### Findings, all applied

- **#77-1 (F).** The sentence "each slot accounts for one unit of increase" is false as written for a continuous slot
  followed by a jump slot. It is replaced by the explicit proof of the counting fact.
- **#77-2 (F, missed by the sweep).** 05 l.90 said "s₁ < s₂ < …". It now says index order, with s_j ≤ s_{j+1}, equality
  exactly for an empty slot, and distinct starts for continuous slots.
- **#77-3 (C).** "Slot spacing" is replaced by continuous-slot spacing in App. A l.94, 05 l.201 and 05 (F1). Slot j replaces
  slot s_j at 05 l.107.
- **#77-4 (C).** New convention: a slot lies in a window when its start does. The Thm queue edges are written as closed and
  half-open intervals.
- **#77-5 (C).** The null event is renamed 𝒩₌, because N₀ is a local symbol in App. A and 04e.
- **#77-6 (C).** Statements called "sure" or "pathwise" that rest on slot facts hold for ω ∉ 𝒩₌.
- **#77-7 (C).** First failure: {τ < ∞} ⊂ 𝒩₌ ∪ ⋃_E(E^c ∩ Good(<t(E))), and P(𝒩₌) = 0.
- **#77-8 (C, pre-existing).** Cor localcount counted slots by |J| + 1. Only continuous slots decide primes, and there are
  at most (1+10⁻⁸)|J| + 1 of them, so 2|J| becomes 2.0001|J|. The constant 11.4 is kept, since ρ_H ≤ 1 + 1.2·10⁻⁵.

## B. R17 items

**F73-1.** The content is correct. The repairer rightly declined R17's "Y′ ≤ 0.9z": (F3′) case 1 reaches s − H(s/2) > 0.9s,
which is still ≤ š. The Y′ values were checked at every use: Cor saias, Lemma S(ii), 04d, 04k V_P and F_θ.

Findings, all applied:
- **R18-F1 (F).** The bullet "Y′ = y for B₁" sat next to "the start is y ≤ z+H(z), so Y′ ≤ 0.9z", which does not follow.
  Outside (F3′), B₁ enters only through Lemma M, Σ_{n ≤ y/X₀⁻} 1/n ≤ log y + B₁, so Y′ = y/X₀⁻. Every use was checked:
  - 04c l.64;
  - 04f l.172, 236, 289;
  - 04k l.277, 288, 306, 384, 386/410, 453;
  - 06 l.406.
- **R18-F2 (C).** The ζ_NN levels reach 2y/X₀⁻, not y/X₀⁻.
- **R18-F3 (C).** Lemma S(iii) takes a sup over starts; its only use is at starts y ≤ x.
- **R18-F4 (C).** In 04d the Good event is moved to the conclusion of E(I).

Confirmed as applied:
- **C73-1, C73-2.**
- **C73-3.** p < √(x/0.99) = 1.00504√x.
- **C73-4.** 2y ≤ u^{1/400}.
- **C73-5.**
- **C73-7.** The E3 and E4 read times match. The new citation log Y + B₁ is the correct one, since Lemma cm(iv) is a prime
  sum.
- **C76-1.**
- **C76-2.** x_{k−1}⁺ ≤ 2a_{k−1} ≤ 2 log a_k.
- **C76-3.** The terms are ≤ 4.082 x_k x_j^{−0.49}, and x_{k+1}⁺ ≥ exp(x_k⁺/2). The total 0.51 + 2.02 + 0.47 ≤ 3, in units
  of e^{−0.49X₀²}.
- **C76-4.** (x⁺/x)^{1−θ}(log x⁺/log x)³ ≤ 1 + 2H/x.
- **C76-5.** s′ − H(s′)/2 ≥ a_k + 0.005H(a_k).

## C. Rendering

- 138 pages, 15 overfull boxes with the same widths as pre77, 0 undefined references and no warnings.
- 28 comment lines were added, all whole lines.
- Of 106 prose fragments, 101 matched automatically and 5 were checked by hand.

## D. Follow-up: verification of the applied fixes (read-only)
Every item was applied correctly, except two:
- **P1 (FIXABLE).** After #77-8, the chain in eq:localcount needs 4ρ_H + 6.0001 ≤ 11.4, that is ρ_H ≤ 1.349975. The text
  claimed only ρ_H ≤ 1.35, and gave no proof of that for log P ≥ 1100.
  - The lead replaced it with ρ_H ≤ 1.33 and wrote out the proof. The derivative of log H in log z is ≤ 16ℓ/L, because
    H = H_std below X₀, and ℓ/L is largest at L = log(P/2) ≥ 1099.3. This gives ρ_H ≤ 16^{0.10192} ≤ 1.327.
  - Both inequalities now hold: 4·2.33 + 8 = 17.32 ≤ 17.4, and 4·1.33 + 6.0001 = 11.32 ≤ 11.4.
- **P2 (COSMETIC).** A stale N₀ remained in a comment in the budget paragraph. It now reads N_=.

The build after these fixes: 138 pages, 15 overfull boxes, 0 undefined references.
