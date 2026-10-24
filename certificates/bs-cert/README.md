# Beurling–Saias theorem: computer-assisted region (Appendix B of the paper)

These scripts certify the computer-assisted part of the paper's Beurling–Saias theorem: region Z2, 30τ ≤ ℓ < 10¹⁸ with u ≥ 2,
plus the one-variable inequalities. The arb versions are authoritative. Run them with a Python that has python-flint 0.9.0
installed (`pip install python-flint`):

    python -I cert_run_arb_patched.py 1.05 10   # Z2 cell cover: 302,013 cells, 0 failures (no cell needs bisection)
    python -I cert_run_arb.py 1.05 10           # the same cover and cell code (the patched file is an alias, not an independent check)
    python -I aux_cert_arb.py                   # (i) c_A ≥ K'u²log(1+u); (ii) Lemma V one-step on [1,10⁶]; (iii) Lemma V one-step on [1,2] with both extra terms

The binary64 versions (bs_cert.py, cert_run.py, aux_cert.py) are a cross-check only.

The scripts locate their imports from their own directory, so they run from this copy alone.
