module

public import RequestProject.BSCert.Transc
public import RequestProject.BSCert.Consts.ZetaSeries

/-!
# Certified enclosures of `ζ(s)` and `-ζ'(s)` for rational `s > 1`

`zetaHiQ s N` (resp. `zetaLoQ s N`) is the upper (lower) end of an enclosure of
`∑_{n ≤ N} n^{-s}` plus the integral tail bound of `ZetaSeries.lean`; `zetaDHiQ s N` is the
same for `-ζ'(s) = ∑ log n · n^{-s}`. Every power `q^s = exp(s log q)` is enclosed with the
certified `exp`/`log` of `Transc.lean`.
-/

@[expose] public section

namespace BSCert.Consts

open Real Finset BSCert

/-- An enclosure of `q^s` (`q > 0`). -/
def rpowItv (q s : ℚ) : Option Itv :=
  if 0 < q then (Itv.log (Itv.pt q)).bind fun L => Itv.exp (Itv.mul L (Itv.pt s)) else none

lemma mem_rpowItv {q s : ℚ} {I : Itv} (h : rpowItv q s = some I) :
    Itv.Mem ((q : ℝ) ^ (s : ℝ)) I := by
  unfold rpowItv at h
  split_ifs at h with hq
  obtain ⟨L, hL, hE⟩ := Option.bind_eq_some_iff.mp h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.rpow_def_of_pos hq']
  exact Itv.mem_exp (Itv.mem_mul (Itv.mem_log (Itv.mem_pt q) hL).1 (Itv.mem_pt s)) hE

/-- Interval sum of `t 0, …, t (n-1)`. -/
def sumItv (t : ℕ → Option Itv) : ℕ → Option Itv
  | 0 => some (Itv.pt 0)
  | n + 1 =>
    match sumItv t n, t n with
    | some A, some B => some (Itv.add A B)
    | _, _ => none

lemma mem_sumItv {f : ℕ → ℝ} {t : ℕ → Option Itv}
    (ht : ∀ k I, t k = some I → Itv.Mem (f k) I) :
    ∀ n I, sumItv t n = some I → Itv.Mem (∑ k ∈ range n, f k) I := by
  intro n
  induction n with
  | zero =>
    intro I h
    simp only [sumItv, Option.some.injEq] at h
    subst h
    simpa using Itv.mem_pt 0
  | succ n ih =>
    intro I h
    simp only [sumItv] at h
    split at h
    · rename_i A B hA hB
      cases h
      rw [sum_range_succ]
      exact Itv.mem_add (ih A hA) (ht n B hB)
    · cases h

/-- Terms `(k+1)^{-s}`. -/
def zTerm (s : ℚ) (k : ℕ) : Option Itv := rpowItv ((k : ℚ) + 1) (-s)

/-- Terms `log (k+1) · (k+1)^{-s}`. -/
def zdTerm (s : ℚ) (k : ℕ) : Option Itv :=
  (Itv.log (Itv.pt ((k : ℚ) + 1))).bind fun L => (zTerm s k).map (Itv.mul L)

lemma mem_zTerm {s : ℚ} {k : ℕ} {I : Itv} (h : zTerm s k = some I) :
    Itv.Mem (((k : ℝ) + 1) ^ (-(s : ℝ))) I := by
  have := mem_rpowItv h
  push_cast at this
  exact this

lemma mem_zdTerm {s : ℚ} {k : ℕ} {I : Itv} (h : zdTerm s k = some I) :
    Itv.Mem (Real.log ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ (-(s : ℝ))) I := by
  unfold zdTerm at h
  obtain ⟨L, hL, hE⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨J, hJ, rfl⟩ := Option.map_eq_some_iff.mp hE
  have h1 := (Itv.mem_log (Itv.mem_pt ((k : ℚ) + 1)) hL).1
  push_cast at h1
  exact Itv.mem_mul h1 (mem_zTerm hJ)

/-- Certified upper bound for `ζ(s)`. -/
def zetaHiQ (s : ℚ) (N : ℕ) : Option ℚ :=
  (sumItv (zTerm s) N).bind fun A => (rpowItv (N : ℚ) (1 - s)).map fun T => A.hi + T.hi / (s - 1)

/-- Certified lower bound for `ζ(s)`. -/
def zetaLoQ (s : ℚ) (N : ℕ) : Option ℚ :=
  (sumItv (zTerm s) N).bind fun A =>
    (rpowItv ((N : ℚ) + 1) (1 - s)).map fun T => A.lo + T.lo / (s - 1)

/-- Certified upper bound for `-ζ'(s)`. -/
def zetaDHiQ (s : ℚ) (N : ℕ) : Option ℚ :=
  (sumItv (zdTerm s) N).bind fun A => (rpowItv (N : ℚ) (1 - s)).map fun T =>
    A.hi + T.hi * (logHiPt (N : ℚ) / (s - 1) + 1 / (s - 1) ^ 2)

theorem zetaR_le_of_zetaHiQ {s : ℚ} {N : ℕ} {u : ℚ} (hs : 1 < s) (hN : 1 ≤ N)
    (h : zetaHiQ s N = some u) : zetaR s ≤ u := by
  unfold zetaHiQ at h
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have hS := (mem_sumItv (fun k I h => mem_zTerm h) N A hA).2
  have hTm := (mem_rpowItv hT).2
  push_cast at hTm
  have htail := zetaR_tail_le hs' hN
  rw [zetaR_split hs' N]
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  have : (N : ℝ) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1) ≤ (T.hi : ℝ) / ((s : ℝ) - 1) :=
    div_le_div_of_nonneg_right hTm hs1.le
  push_cast
  linarith

theorem zetaLoQ_le_zetaR {s : ℚ} {N : ℕ} {l : ℚ} (hs : 1 < s) (hN : 1 ≤ N)
    (h : zetaLoQ s N = some l) : (l : ℝ) ≤ zetaR s := by
  unfold zetaLoQ at h
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have hS := (mem_sumItv (fun k I h => mem_zTerm h) N A hA).1
  have hTm := (mem_rpowItv hT).1
  push_cast at hTm
  have htail := zetaR_tail_ge hs' hN
  rw [zetaR_split hs' N]
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  have : (T.lo : ℝ) / ((s : ℝ) - 1) ≤ ((N : ℝ) + 1) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1) :=
    div_le_div_of_nonneg_right hTm hs1.le
  push_cast
  linarith

theorem zetaDR_le_of_zetaDHiQ {s : ℚ} {N : ℕ} {u : ℚ} (hs : 1 < s)
    (hs2 : 1 / Real.log 2 ≤ s) (hN : 2 ≤ N)
    (h : zetaDHiQ s N = some u) : zetaDR s ≤ u := by
  unfold zetaDHiQ at h
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have hS := (mem_sumItv (fun k I h => mem_zdTerm h) N A hA).2
  have hTm := (mem_rpowItv hT).2
  push_cast at hTm
  have htail := zetaDR_tail_le hs' hs2 hN
  rw [zetaDR_split hs' N]
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log N ≤ ((logHiPt (N : ℚ) : ℚ) : ℝ) := by
    have := le_logHiPt (a := (N : ℚ)) (by exact_mod_cast (by omega : 0 < N)); exact_mod_cast this
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hpow0 : 0 ≤ (N : ℝ) ^ (1 - (s : ℝ)) := Real.rpow_nonneg hN0.le _
  have hfac : Real.log N / ((s : ℝ) - 1) + 1 / ((s : ℝ) - 1) ^ 2
      ≤ ((logHiPt (N : ℚ) : ℚ) : ℝ) / ((s : ℝ) - 1) + 1 / ((s : ℝ) - 1) ^ 2 := by
    gcongr
  have hfac0 : 0 ≤ Real.log N / ((s : ℝ) - 1) + 1 / ((s : ℝ) - 1) ^ 2 := by positivity
  have : zetaDF s N ≤ (T.hi : ℝ) * (((logHiPt (N : ℚ) : ℚ) : ℝ) / ((s : ℝ) - 1)
      + 1 / ((s : ℝ) - 1) ^ 2) := by
    unfold zetaDF
    exact mul_le_mul hTm hfac hfac0 (le_trans hpow0 hTm)
  push_cast
  linarith

end BSCert.Consts
