# Lemma BS (H⁗) certification scripts (copied from /tmp/rhscratch/gap-localpnt on 2026-10-22)

These scripts back gap-localPNT §6.9.3′(H⁗). The arb versions are authoritative. Run them with a Python that has
python-flint 0.9.0 installed (`pip install python-flint`; originally /tmp/rhscratch/flintenv, which may be wiped):

    python -I cert_run_arb_patched.py 1.05 10   # Z2 cover with referee B's seam fix (§21): 302,013 cells, 0 failures
    python -I cert_run_arb.py 1.05 10           # same seam fix folded in (gap-localpnt): 302,013 cells, 0 failures
    python -I aux_cert_arb.py              # (H″) u ≥ 27 and Lemma V

The binary64 versions (bs_cert.py, cert_run.py, aux_cert.py) are a cross-check only.

The scripts locate their imports from their own directory, so they run from this copy alone.
