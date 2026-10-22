# Summary of changes for run dfbedf4a-6bed-4f51-ab86-61a2788664c2
I couldn't fully prove your main theorem (Corollary 2.2: a discrete Beurling system with \(|N(x)-x|\le Cx^\theta\), \(\theta<1/2\), whose zeta function has zeros with real part arbitrarily close to 1). What I did instead was cut it down to a single unproved lemma and prove everything around that lemma in Lean. The project builds, and that lemma is now the only `sorry`.

**What is now proved**
- **`exists_zero_of_near_model`** (new file `RequestProject/Beurling/ZeroCriterion.lean`) is the final step of your Theorem 4.9. Mathlib has no Rouché theorem, so I proved this version from the maximum modulus principle. Suppose \(g\) vanishes at the centre of a closed disc, \(\|g\|\ge M\) and \(\|f-g\|\le m\) on the boundary circle, \(2m<M\), and both functions are holomorphic on the disc. Then \(f\) has a zero inside the disc. Your constants satisfy this: \(|Z_B+M_k|\ge 1/4\) on the circle, and the perturbation is at most \(1/16+o(1)<1/8\). The proof uses only Lean's standard axioms.
- **`exists_no_zeroFree_halfPlane`** (the main theorem, in `RequestProject/Beurling/MainTheorem.lean`, statement unchanged) now follows in Lean from the criterion above, the existing holomorphy result `differentiableAt_zetaCont`, and one remaining input.

**What is still unproved**
- **`exists_system_near_model`** is that remaining input. It states that there is a system with \(|N(x)-x|\le Cx^\theta\), \(\theta<1/2\), and for every \(\varepsilon>0\) a disc in \(\{\theta<\mathrm{Re}\,s,\ 1-\varepsilon<\mathrm{Re}\,s,\ s\ne1\}\) with a holomorphic model function that vanishes at the centre and is close to \(\zeta_P\) on the circle.
- In your paper this is everything before the Rouché step: the randomised greedy construction (Section 3), the lag bound (Sections 5–7, Appendix A, the Appendix B certificates) and Lemmas 4.2–4.8.
- Proving it in Lean would require formalizing all of that. It would also need the Huxley–Heath-Brown short-interval prime number theorem and the Montgomery–Vaughan mean value theorem, neither of which is in Mathlib, so it is out of reach here.

**Status**
- The main theorem is **not** formally verified: its proof depends on that one unproved lemma, and it is marked in progress in the Properties table.
- `VERIFICATION_REPORT.md` has a new section describing this split, and the Properties table lists both new results.