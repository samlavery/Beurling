# Follow-up: Theorem A below θ = 1/4 (branch followup-theta)

Status (2026-10-30): paper only. Done and checked by one AI agent (Claude); **no independent or human review.** Scope note:
/tmp/rhscratch/ext/theta.md (Tier 1).

## Result

Theorem A now covers **θ ∈ [θ₀, θ₁], θ₀ = 1/20, θ₁ = 1/2 − 10⁻⁴**. The error bound C_{X₀}x^θ + 3x^θ log*x + x^η, X₀ ≥ e^{10⁸},
η = min(θ, ½−θ)/2 and the zeros statement are unchanged. For θ ≥ 1/4 the construction is unchanged.

## Design change

The absorption-window exponent θ_b is no longer always θ/2. It is

    θ_b := min(θ, max(θ/2, 1/8)),   h(u) = u^{θ_b},

so θ_b = θ/2 for θ ≥ 1/4 (as before), θ_b = 1/8 on [1/8, 1/4], and θ_b = θ for θ ≤ 1/8. It always satisfies θ/2 ≤ θ_b ≤ θ and
1/20 ≤ θ_b < 1/4.
- θ_b ≤ θ: the absorbed error 2x^{θ_b} stays ≤ 2x^θ ≤ x^θ log*x, and in Lemma ZA(a) Y = |t|^{1/(1−θ_b)} ≤ x_k.
- θ_b ≥ θ/2: Lemma ZA(a) keeps (1−θ)/(1−θ_b) ≥ 2/3 + 8·10⁻⁵.
- θ_b < 1/4: Lemma ZA's ε = a^{b−1} ≤ (X₀/2)^{−3/4}, threshold mass U^{1−θ_b} ≥ U^{3/4}, and K* = 2M^{1/4} in the X₀-band.

Plain θ_b = θ/2 would give only θ_min ≈ 0.085–0.1.

## The binding inequalities (Theorem caplw Step 5; Lemma P (v)–(vi)), redone with θ_b as a parameter

1. **(12.2) on the ramp.** It reduces to e^s log(θ_bΛe^s/(3.01γ)) ≥ 13.45γ²/θ_b, since 4.02·3.01/0.9 = 13.4447 ≤ 13.45 (the old
   107.6 is 13.45·8). The left side increases in Λ, s and θ_b, and the right side decreases in θ_b, so the worst case is Λ = 10⁸,
   θ_b = 1/20. For s ≥ s_H+1, γ = 7.5 and the inequality is monotone. On s = s_H + t, t ∈ [0,1] (new proof, written in the paper):
   - LHS ≥ 393.28e^t(c+t) with c = log(10⁸·393.28/22.575) − log 20 = 18.2826 ≥ 18.28, so the claim reads
     φ(t) = e^{t/2}(c+t)^{1/2} ≥ kγ with k = (13.45·20/393.28)^{1/2} = 0.82704 ≤ 0.8271.
   - φ is convex, so φ ≥ its tangent at t=1, which is at least 7.2393 + 3.8075(t−1). That is 3.4318 at t=0 and 7.2393 at t=1,
     against kγ ≤ 0.2757 and 6.2033 (γ is linear on the ramp).
   - **Margin: ratio ≥ (7.2393/6.2033)² = 1.3619 ≥ 1.36**, attained at t = 1 (it was 3.57 at θ_b = 1/8). Exact grid minimum:
     1.3624 at t = 1.
2. **(*) u₀ ≥ 2Λ in Lemma P(v)/(vi), and through it Lemma ZA.** u₀ ≥ θ_bΛe^s/(3.01γ). On the ramp γ = γ'(1+t−t*) with
   γ' = 7.5 − γ_*(s_H) = 7.16668 and t* = 1 − γ_*(s_H)/γ' = 0.95349. Since e^t ≥ e^{t*}(1+t−t*),
   e^s/(3.01γ) ≥ e^{s_H+t*}/(3.01γ') = 47.306. For s ≥ s_H+1 the bound is ≥ 47.36. So **u₀ ≥ 47.3θ_bΛ ≥ 2.365Λ at θ_b = 1/20.
   Margin 18% over 2Λ; this is the binding one.** With the precise y the minimum is 2.3732Λ, at s = 6.928, for every
   Λ ∈ {1e8, 1e10, 1e12, 1e20}. The old text had "≥ 5Λ" (5.91 at θ_b = 1/8).
3. **True θ_min of this design (Tier 1):** (*) fails below θ_b ≈ 0.0423, and the analytic (12.2) below about 0.038. I chose
   1/20 for margin. θ = 0.045 would still pass (ratio 1.219, u₀/Λ ≥ 2.129), but it is not claimed.

## Every change, by place (θ-table rows of theta.md in brackets)

- Statements [row 1]: abstract.tex, 00-intro.tex (Theorem A informal), 01-setup.tex (preamble, Theorem A, parameter table: θ_b
  defined, h = u^{θ_b}), README.md, and C-ai-statement.tex. The AI statement keeps "the referee judged … [1/4, ½−10⁻⁴]", which is
  true, and adds that the extension below 1/4 came after that review and was checked only by the agent that made it.
- Proof of Theorem A (01-setup): 2x^{θ_b} ≤ 2x^θ ≤ x^θ log*x (log*x ≥ 2 for x ≥ X₀). The final error bound is unchanged.
- 02-construction: h(u) = u^{θ_b}, with θ_b defined. Lemma T1: |E| ≤ C_{X₀}x^θ + 2x^{θ_b} [row 13]. In the proof, b = θ_b and
  "4/(b log u) ≤ 4·10⁻⁶" becomes "≤ 10⁻⁵ (b ≥ 1/20)"; 1.001/(1−10⁻⁵) ≤ 1.01, so the constants 1.03 and 3.1 hold. C_{X₀} = 2∏(1−p^{−θ})^{−1}
  is finite for every θ > 0.
- 05-queue Theorem caplw: hypothesis θ ∈ [θ₀, θ₁] gives θ_b ∈ [1/20, 1/4) [row 2]. Step 5 ramp: new proof as above [row 3].
  Standard regime: u₀ ≥ θ_b e^ℓ/(12.1ℓ²) ≥ e^ℓ/(242ℓ²), was e^ℓ/(97ℓ²).
- Lemma P: the preamble recalls θ_b. Statement: "ratio ≥ 3.5" becomes "≥ 1.36", which still dwarfs the 1+10⁻⁵ non-dyadic
  loss [row 7].
  - (iv): "u^{θ_b} ≥ e^{L/8} ≥ 2L^{11}" is now derived from (12.2): θ_bL = u₀ log 2y ≥ 100 log y ≥ 500 log(L−1), using y ≥ L₀ ≥
    L_x⁵ [row 6].
  - (vi): u₀ ≥ 47.3θ_bΛ ≥ 2.36Λ, with the e^t ≥ e^{t*}(1+t−t*) proof [row 4].
  - (v), third bullet: "u_* ≤ 1 + L/8" becomes "1 + θ_bL". **The old text was a small slip for θ > 1/4** (θ_b = θ/2 > 1/8 there).
    It was harmless, since only u_* ≤ L is used.
- Remark caplw-numerics: states that the cross-check runs at θ_b = 1/20 and 1/8.
- 03-zeros:
  - w_a bounds: b = θ_b ∈ [1/20, 1/4).
  - Lemma ZA(a) [rows 8, 16]: Y = |t|^{1/(1−θ_b)} ≤ x_k (justified), (1−θ)/(1−θ_b) ≥ (1−θ)/(1−θ/2), and θ_b replaces θ/2 in the
    exponents. ZA's own "u ≥ u₀ ≥ 2Λ" needed no change: it cites Lemma P(vi).
  - T₀ comparison: 3.1u^{θ_b}.
  - Designed zero step 6 [row 10]: |w| ≤ 0.96 (was 0.76; Re w ≤ 1−θ+δ_k ≤ 0.95+δ_k). The O(1) interval lower end −1.5 becomes
    −1.7 (−log 0.96 = 0.041 replaces −log 0.76 = 0.274, so the end is −1.6523). The constant 5.7 becomes 5.9
    (1.7 + 3.152 + 1 = 5.852). This is still ≤ δ_k, because 9 − 3 = 6 loglog x_k ≫ log(1/κ₀) + log 2Λ + 5.9. Also Re w ≤ 1 still
    holds for Re Φ_min.
  - Late noise [row 9]: 165Λx_k^{−1/8} becomes 165Λx_k^{−θ/2}; in Theorem zeros, 165Λe^{−X₀²/8} becomes 165Λe^{−θX₀²/2}
    (≤ e^{−X₀²/41}, still negligible).
- 04a-setup, 04e-lp (threshold mass U^{1−θ_b} ≥ U^{3/4}; D₀ with 3.1u^{θ_b}; a comment θ' ≥ 0.26 becomes θ' ≥ θ_b + 0.01),
  04f-bridge (F_θ range; N_*^{θ_b}), 04x-x0band ((2M)^{θ_b}, "as θ_b < 1/4"), 06-base-range (δ(t) with 2t^{θ_b}) [rows 14, 15, 18, 19, 22].
- 04k-kernels [row 17]: |I_v| ≤ 2.1H(v)/X₀ ≤ h(v/X₀) was asserted without proof. It now has a two-case justification from
  log H ≤ 8(log L)² + 10⁻⁶L (caplw(c)), valid for θ_b ≥ 1/20.
- Rows needing no change: 11 (lag: η ≥ 5·10⁻⁵ needs only θ ≥ 10⁻⁴), 12 (B ≤ x^{10⁻⁵} ≤ x^η, same), 20, 21, 24.
- App. B (B-certificates.tex): documents CAPL_THETA_B, the new outputs, and the new script theta_ramp.py.

Build: `latexmk … -outdir=/tmp/wt-theta-build main.tex`: 0 undefined references, 14 overfull boxes (= baseline). The root
beurling-paper.pdf is not regenerated.

## Scripts (certificates/capl-cert/, /usr/bin/python3 -I -B, each < 7 s, < 15 MB RSS)

- capl_model.py: THETA_B now comes from the env var CAPL_THETA_B. **The default is 1/20, the worst case** (the criterion is
  monotone in θ_b). This changes the default model, but the analytic_capl and cert_capl outputs are identical at 1/20 and 1/8.
- caplw_check_independent.py: the hard-coded 8·3.01γ and 107.6 are replaced by θ_b; it also reports min lhs/rhs and a new check
  u₀ ≥ 2Λ.
- New theta_ramp.py: the analytic Step 5 on a 10⁻⁵ grid, the tangent-proof constants, and min u₀/Λ with the precise y.

Outputs at θ_b = 0.05:

    theta_ramp: (A) 3000001 points: min lhs/rhs = 1.3624 at t = 1.0000 -> OK
                (B) c = 18.2826; tangent 7.2399 + 3.8077(t-1); kγ 0.2757 / 6.2027; ratio^2 at t=1 = 1.3624 -> OK
                analytic min e^s/(3.01γ) = 47.3064; ×θ_b = 2.3653
                (C) Λ = 1e8, 1e10, 1e12, 1e20: min u0/Λ = 2.3732 at s = 6.928 -> OK
    analytic_capl: s_H = 5.9745; G decreasing on all sample lines; 4842/5072/5302/5763/6684/7605 points, 0 failures
    caplw_check_independent: Step1 0, Step2 0 (1.6938), Dickman 0 (1.1897), Step5 0 (min lhs/rhs 1.4113), u0>=2Λ 0 (min 2.3653)
    cert_capl: cells 20790 on [18.421, 60]: failures 0; cells 398801 on [60, 2e4]: failures 0

At θ_b = 1/8, for comparison: theta_ramp 3.5678 and 5.9330; independent Step5 3.6949 and u₀ 5.9133; the other outputs are
identical.

## Lean (not touched; would need changes to extend the formal statement below 1/4)

The top-level Lean result (Corollary 2.2) needs only one θ, so it is unaffected. Formalizing the wider Theorem A would need the
following changes.
- Relax the hypothesis θ ≥ 1/4 (or θ ∈ Icc (1/4) …) to θ ≥ 1/20 in the 78 files of list A below. Key ones:
  - DesignedZero.lean (DesignParams; used for ‖w‖ ≤ 1, now ≤ 0.96).
  - LateNoise.lean (exponent −1/8 → −θ/2).
  - LagTwoSided.lean, Theorem410Base.lean, Theorem410Absorbed.lean.
  - The Construction/*, Model/Top*, Queue6/Top* plumbing.
- Change the window exponent θ/2 to θ_b in the 83 files of list B (h, the T1 absorbed bound, ZA, Lemma P). This matters
  wherever the formalization fixes h = u^{θ/2}, notably Construction/Sparsity.lean, TargetError.lean, AbsorbEmpty.lean and
  PartICapl.lean (caplw Step 5 / Lemma P constants: 107.6 and 5Λ become 13.45/θ_b and 47.3θ_bΛ).

Many hits in list B are θ/2 in other roles (η ≤ θ/2, late noise). They must be triaged one by one; I did not triage them.

## Doubts / not verified

- Everything was checked only by me (one AI pass); there was no independent re-check.
- I did not re-derive Theorem caplw Steps 1–4 or (c). They are θ-free: θ enters caplw only through Step 5.
- I grepped every θ/2, 1/4, 1/8 and θ-bound in sections/*.tex and inspected each hit. A use of θ ≥ 1/4 hidden in a constant
  (not written as θ) could still have been missed. The cleanest candidate list is theta.md's 25 rows, and all of them were
  handled.
- The designed-zero constant 5.9 was re-derived by hand (bound list: log|Φ| ∈ [−1,0], |w| ∈ [0.49,0.96], |Z_B| ∈ [½,2Λ],
  −log 2), not by script.
- Lemma P (iv): the new derivation uses y ≥ L₀ ≥ L_x⁵ for the frozen dyadic scale x of u, so L_x ≥ L − 1. I believe this is
  right but did not trace every scale convention.

## Tier 2 (possible next step): any fixed θ > 0, with X₀ = X₀(θ)

What it would need:
1. The lag. (8ℓ²+2)/L ≤ η needs Λ ≳ 16 log²Λ/θ. The current Λ ≥ 10⁸ suffices only for θ ≥ 5.7·10⁻⁵.
2. The ramp. Replace Λ_s = max(10⁸, e^{−s}) by max(Λ_min(θ), e^{−s}), so that u₀/Λ grows with Λ_min. A rough requirement is
   Λ_min ≈ 10⁴ log²Λ/θ_b. Then re-prove caplw Steps 1–3 and 5–6 with the moved ramp: Step 2's ranges m ≤ Λ³e^{14} and
   D ≤ 2Λe^7 become Λ_min-dependent, and the s_H root and the 393.28 change.
3. Alternatively, or additionally, relax (*) u_* ≥ 2Λ in Lemma P(v) to u_* ≥ e^C with 0.9 → about 0.7. This changes the 0.9 in
   (12.2) and in ZA's 0.45.
4. Recheck the designed zero (|w| ≤ 1 − θ + δ_k ≤ 1 needs θ ≥ δ_k), the late noise (e^{−θX₀²/2} small needs θX₀² ≫ log Λ), and
   C_{X₀} (astronomical, but finite).
5. Rerun analytic_capl/caplw_check_independent/theta_ramp with Λ_min-dependent s_H. Effort about a week plus a re-audit.
   Uncertainty: medium (caplw(a) with a moved ramp is unchecked).

## Appendix: Lean file lists

List A (hypothesis θ ≥ 1/4):
    lean/RequestProject/Beurling/AbsorbEmpty.lean
    lean/RequestProject/Beurling/Construction/Cond81.lean
    lean/RequestProject/Beurling/Construction/ElemCount.lean
    lean/RequestProject/Beurling/Construction/Fix.lean
    lean/RequestProject/Beurling/Construction/HBSDerive.lean
    lean/RequestProject/Beurling/Construction/HBSLag.lean
    lean/RequestProject/Beurling/Construction/HBSLocal.lean
    lean/RequestProject/Beurling/Construction/JitterRegular.lean
    lean/RequestProject/Beurling/Construction/LandingDerive.lean
    lean/RequestProject/Beurling/Construction/Link.lean
    lean/RequestProject/Beurling/Construction/Main.lean
    lean/RequestProject/Beurling/Construction/NoHBS.lean
    lean/RequestProject/Beurling/Construction/Realised.lean
    lean/RequestProject/Beurling/Construction/Scales.lean
    lean/RequestProject/Beurling/Construction/Sparsity.lean
    lean/RequestProject/Beurling/Construction/Top.lean
    lean/RequestProject/Beurling/Construction/Unadapted.lean
    lean/RequestProject/Beurling/Decomp/Theorem410Dec.lean
    lean/RequestProject/Beurling/DesignedZero.lean
    lean/RequestProject/Beurling/DesignSize.lean
    lean/RequestProject/Beurling/Escape.lean
    lean/RequestProject/Beurling/InitialRange.lean
    lean/RequestProject/Beurling/LagBound.lean
    lean/RequestProject/Beurling/LagSplit.lean
    lean/RequestProject/Beurling/LagTwoSided.lean
    lean/RequestProject/Beurling/LocalPNT/Defs.lean
    lean/RequestProject/Beurling/LocalPNT/HBS.lean
    lean/RequestProject/Beurling/LocalPNT/LPa.lean
    lean/RequestProject/Beurling/LocalPNT/Theorem524.lean
    lean/RequestProject/Beurling/Main.lean
    lean/RequestProject/Beurling/Model/Fix.lean
    lean/RequestProject/Beurling/Model/G1BRprime.lean
    lean/RequestProject/Beurling/Model/HBSGood.lean
    lean/RequestProject/Beurling/Model/MarginFinal.lean
    lean/RequestProject/Beurling/Model/MeasTarget.lean
    lean/RequestProject/Beurling/Model/OscD2.lean
    lean/RequestProject/Beurling/Model/S2Final.lean
    lean/RequestProject/Beurling/Model/Slope.lean
    lean/RequestProject/Beurling/Model/SlotsSharp.lean
    lean/RequestProject/Beurling/Model/Stage.lean
    lean/RequestProject/Beurling/Model/T0Mono.lean
    lean/RequestProject/Beurling/Model/Top.lean
    lean/RequestProject/Beurling/Model/TopM.lean
    lean/RequestProject/Beurling/Model/TopS.lean
    lean/RequestProject/Beurling/Model/TopU.lean
    lean/RequestProject/Beurling/Model/Valid.lean
    lean/RequestProject/Beurling/Noise/MarginRealTop.lean
    lean/RequestProject/Beurling/PartI.lean
    lean/RequestProject/Beurling/PartICapl.lean
    lean/RequestProject/Beurling/PartIConcrete.lean
    lean/RequestProject/Beurling/Queue6/Budget6.lean
    lean/RequestProject/Beurling/Queue6/Path.lean
    lean/RequestProject/Beurling/Queue6/Table6.lean
    lean/RequestProject/Beurling/Queue6/Top.lean
    lean/RequestProject/Beurling/Queue6/TopV.lean
    lean/RequestProject/Beurling/Queue6/TopW.lean
    lean/RequestProject/Beurling/Queue6/TopX.lean
    lean/RequestProject/Beurling/Queue6/TopY.lean
    lean/RequestProject/Beurling/Queue6/TopZ.lean
    lean/RequestProject/Beurling/Queue6/WinCount.lean
    lean/RequestProject/Beurling/QueueBound75.lean
    lean/RequestProject/Beurling/SlotCount.lean
    lean/RequestProject/Beurling/SlotModel.lean
    lean/RequestProject/Beurling/TargetError.lean
    lean/RequestProject/Beurling/Theorem410.lean
    lean/RequestProject/Beurling/Theorem410Absorbed.lean
    lean/RequestProject/Beurling/Theorem410Base.lean
    lean/RequestProject/Beurling/Theorem410Count.lean
    lean/RequestProject/Beurling/Theorem410Design.lean
    lean/RequestProject/Beurling/Theorem410Lemma48.lean
    lean/RequestProject/Beurling/Theorem410Mertens.lean
    lean/RequestProject/Beurling/Theorem410Paper.lean
    lean/RequestProject/Beurling/Theorem410Rankin.lean
    lean/RequestProject/Beurling/Theorem410ZB.lean
    lean/RequestProject/Beurling/Zeros.lean
    lean/RequestProject/Beurling/Zeros48/Inputs.lean
    lean/RequestProject/Beurling/Zeros48/Numerics.lean
    lean/RequestProject/Beurling/Zeros48/Realised48.lean

List B (θ/2 exponents; needs triage):
    lean/RequestProject/Beurling/AbsorbEmpty.lean
    lean/RequestProject/Beurling/BaseRange/MarginHc.lean
    lean/RequestProject/Beurling/Construction/Cond81.lean
    lean/RequestProject/Beurling/Construction/ElemCount.lean
    lean/RequestProject/Beurling/Construction/Fix.lean
    lean/RequestProject/Beurling/Construction/HBSDerive.lean
    lean/RequestProject/Beurling/Construction/HBSLocal.lean
    lean/RequestProject/Beurling/Construction/JitterRegular.lean
    lean/RequestProject/Beurling/Construction/LandingDerive.lean
    lean/RequestProject/Beurling/Construction/Link.lean
    lean/RequestProject/Beurling/Construction/Main.lean
    lean/RequestProject/Beurling/Construction/NoHBS.lean
    lean/RequestProject/Beurling/Construction/Realised.lean
    lean/RequestProject/Beurling/Construction/Scales.lean
    lean/RequestProject/Beurling/Construction/Sparsity.lean
    lean/RequestProject/Beurling/Construction/Top.lean
    lean/RequestProject/Beurling/Construction/Unadapted.lean
    lean/RequestProject/Beurling/Decomp/Decomposition.lean
    lean/RequestProject/Beurling/Decomp/Theorem410Dec.lean
    lean/RequestProject/Beurling/DesignSize.lean
    lean/RequestProject/Beurling/InitialRange.lean
    lean/RequestProject/Beurling/LagBound.lean
    lean/RequestProject/Beurling/LagSplit.lean
    lean/RequestProject/Beurling/LagTwoSided.lean
    lean/RequestProject/Beurling/LateNoise.lean
    lean/RequestProject/Beurling/LocalPNT/LPa.lean
    lean/RequestProject/Beurling/LocalPNT/Theorem524.lean
    lean/RequestProject/Beurling/Main.lean
    lean/RequestProject/Beurling/Model/Causal2.lean
    lean/RequestProject/Beurling/Model/Data.lean
    lean/RequestProject/Beurling/Model/G1BDec34.lean
    lean/RequestProject/Beurling/Model/G1BDelta.lean
    lean/RequestProject/Beurling/Model/G1BJump.lean
    lean/RequestProject/Beurling/Model/G1BJumpProof.lean
    lean/RequestProject/Beurling/Model/G1BOth.lean
    lean/RequestProject/Beurling/Model/G1BStep3.lean
    lean/RequestProject/Beurling/Model/HBSGood.lean
    lean/RequestProject/Beurling/Model/Identify.lean
    lean/RequestProject/Beurling/Model/Land.lean
    lean/RequestProject/Beurling/Model/MarginObjects.lean
    lean/RequestProject/Beurling/Model/MeasData.lean
    lean/RequestProject/Beurling/Model/MeasTarget.lean
    lean/RequestProject/Beurling/Model/OscBound.lean
    lean/RequestProject/Beurling/Model/Phi.lean
    lean/RequestProject/Beurling/Model/RhoAGood.lean
    lean/RequestProject/Beurling/Model/S3d.lean
    lean/RequestProject/Beurling/Model/SigmaA.lean
    lean/RequestProject/Beurling/Model/SigmaResp.lean
    lean/RequestProject/Beurling/Model/Slope.lean
    lean/RequestProject/Beurling/Model/SlotsSharp.lean
    lean/RequestProject/Beurling/Model/T0Mono.lean
    lean/RequestProject/Beurling/Model/TargetLocal.lean
    lean/RequestProject/Beurling/Model/TBound.lean
    lean/RequestProject/Beurling/Model/TBoundE1.lean
    lean/RequestProject/Beurling/Model/TBoundGood.lean
    lean/RequestProject/Beurling/Model/TcLow.lean
    lean/RequestProject/Beurling/Model/TcMeas.lean
    lean/RequestProject/Beurling/Model/Top.lean
    lean/RequestProject/Beurling/Model/Valid.lean
    lean/RequestProject/Beurling/Model/WinAtR.lean
    lean/RequestProject/Beurling/Model/Wire.lean
    lean/RequestProject/Beurling/PartI.lean
    lean/RequestProject/Beurling/PartICapl.lean
    lean/RequestProject/Beurling/PartIConcrete.lean
    lean/RequestProject/Beurling/Queue6/CountISmall.lean
    lean/RequestProject/Beurling/Queue6/CountISmallB.lean
    lean/RequestProject/Beurling/Queue6/NCount.lean
    lean/RequestProject/Beurling/Queue6/ShortRecipQ.lean
    lean/RequestProject/Beurling/Queue6/WinCount.lean
    lean/RequestProject/Beurling/QueueBound75.lean
    lean/RequestProject/Beurling/SlotCount.lean
    lean/RequestProject/Beurling/SlotModel.lean
    lean/RequestProject/Beurling/TargetError.lean
    lean/RequestProject/Beurling/Theorem410Absorbed.lean
    lean/RequestProject/Beurling/Theorem410Base.lean
    lean/RequestProject/Beurling/Theorem410Count.lean
    lean/RequestProject/Beurling/Theorem410Design.lean
    lean/RequestProject/Beurling/Theorem410Lemma48.lean
    lean/RequestProject/Beurling/Theorem410Mertens.lean
    lean/RequestProject/Beurling/Theorem410Rankin.lean
    lean/RequestProject/Beurling/Theorem410ZB.lean
    lean/RequestProject/Beurling/Zeros48/Inputs.lean
    lean/RequestProject/Beurling/Zeros48/Realised48.lean
