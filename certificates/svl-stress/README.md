# svl-stress: numerical corroboration of the Staged Volume Lemma (NOT part of the proof)

`svl_stress.py` checks, in exact rational arithmetic, the structural facts used in the proof of the Staged Volume Lemma
(Appendix A, Theorem `thm:svl`), on random and adversarial rank-full configurations with 8–12 rows and up to nine stages:
- the stage rows exist;
- column masses are ≥ 1 on the stage prefix;
- late free primes are covered;
- a late free column is determined by its stage-prefix entries, and its coefficient vanishes in the remaining rows;
- the cumulative determinants are nonzero integers;
- the per-row block ranges are disjoint.

These facts are PROVED in Appendix A. This script is an independent sanity check only.

Run: `python3 -I svl_stress.py` (defaults: seed 1, 60 configurations per mode), or `python3 -I svl_stress.py <seed> <n>`.
Expected output: four lines (modes rand, late, refA, nest), each ending in `violations 0`; exit status 0.
Runtime: a few minutes. Python 3 standard library only.
