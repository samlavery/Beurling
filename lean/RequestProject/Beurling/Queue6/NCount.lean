module

public import RequestProject.Beurling.Queue6.CountI

/-!
# The integer count of a long window on `Good(< t)` (Lemma 5.23, case (i), first bullet)

For `X₀ ≤ a ≤ d` and `ω ∈ Good(< t) ∩ NiceEv` with `t` above `d + H`:

`N(d) - N(a) ≤ 2.00005 (d - a) + 1 + ((d - a)/h + 2) (d + h)^{θ/2} (log a)^{-4} + D(d) + D(a)`
(`Ncount_le`), `h = a^{θ/2}`, `D(v) = B(v) + B(X₀) + H(v) + H(X₀) + 5`:

* `|N - T| ≤ D` at both ends (Corollary 3.8, `lag_G0`);
* `T(d) - T(a) ≤ 2.00005 (d - a) + 1 + #(𝒜 ∩ [a, d])` (`T_incr`);
* `[a, d]` is covered by `⌈(d - a)/h⌉ + 1` windows `[w, w + h]`, `h ≤ w^{θ/2}`, each holding at most
  `w^{θ/2} (log w)^{-4}` absorbed elements (Lemma 6.26, `LC_G0`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel Absorbed

namespace Queue6

open BModel

/-- The lag bound `D(v) = B(v) + B(X₀) + H(v) + H(X₀) + 5` of Corollary 3.8. -/
noncomputable def lagD (X₀ : ℕ) (v : ℝ) : ℝ :=
  queueB X₀ v + queueB X₀ X₀ + capH X₀ v + capH X₀ X₀ + 5

variable {θ : ℝ} {X₀ : ℕ} (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1600000 in
/-- **The integer count of a window `(a, d]`** on `Good(< t) ∩ NiceEv`. -/
theorem Ncount_le {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {a d : ℝ} (ha : (X₀ : ℝ) ≤ a) (had : a ≤ d) (ht1 : d + 26 * Real.log d + 2 < t)
    (ht2 : 2 * (d + a ^ (θ / 2)) + 2 * X₀ + 4 ≤ t) :
    (PR θ X₀ ω).N d - (PR θ X₀ ω).N a ≤
      2.00005 * (d - a) + 1 + ((d - a) / a ^ (θ / 2) + 2) *
        ((d + a ^ (θ / 2)) ^ (θ / 2) * Real.log a ^ (-4 : ℤ)) + lagD X₀ d + lagD X₀ a := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have ha0 : 0 < a := by linarith
  have hθ := hc.hθ
  have hθ0 : 0 ≤ θ / 2 := by linarith [hθ.1]
  set h := a ^ (θ / 2) with hhdef
  have hh0 : 0 < h := Real.rpow_pos_of_pos ha0 _
  -- the lag at both ends
  have hla := lag_G0 D hc hev hG hN ha (by
    have : Real.log a ≤ Real.log d := Real.log_le_log ha0 had
    linarith)
  have hld := lag_G0 D hc hev hG hN (ha.trans had) ht1
  rw [abs_le] at hla hld
  -- the target increment
  have hT := T_incr hc ω ha had
  -- the absorbed count over `[a, d]`, by windows of length `h`
  set A := absSet X₀ (DF θ X₀ ω)
  have hU : ∀ j, Ucl ω j ∈ Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  have hAfin := absSet_locFin (X₀ := X₀) (locFinD_DM hc.hX hU (Mcl θ X₀ ω))
  set n := ⌈(d - a) / h⌉₊ + 1
  set Mw := (d + h) ^ (θ / 2) * Real.log a ^ (-4 : ℤ)
  have hcov := count_le_of_cover (S := A ∩ Icc a d) n
    (fun i => A ∩ Icc (a + i * h) (a + i * h + h))
    (fun i => (hAfin (a + i * h + h)).subset fun y hy => ⟨hy.1, hy.2.2⟩)
    (M := Mw) (fun i hi => by
      have hi' : (i : ℝ) ≤ (d - a) / h + 1 := by
        have h1 : i ≤ ⌈(d - a) / h⌉₊ := by omega
        have h2 : (⌈(d - a) / h⌉₊ : ℝ) < (d - a) / h + 1 :=
          Nat.ceil_lt_add_one (div_nonneg (by linarith) hh0.le)
        have : (i : ℝ) ≤ ⌈(d - a) / h⌉₊ := by exact_mod_cast h1
        linarith
      set w := a + i * h
      have hw : a ≤ w := by have : (0 : ℝ) ≤ i * h := by positivity
                            linarith
      have hwd : w ≤ d + h := by
        have : (i : ℝ) * h ≤ d - a + h := by
          have := mul_le_mul_of_nonneg_right hi' hh0.le
          rw [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at this
          exact this
        linarith
      have hw0 : 0 < w := by linarith
      have hwθ : h ≤ w ^ (θ / 2) := Real.rpow_le_rpow ha0.le hw hθ0
      have hLC := LC_G0 D hc hev hG hN (x := w) (x' := w + h) (ha.trans hw) (by linarith)
        (by linarith)
      have hLC' : ((A ∩ Icc w (w + h)).ncard : ℝ) ≤ w ^ (θ / 2) * Real.log w ^ (-4 : ℤ) :=
        hLC
      refine hLC'.trans ?_
      have hlw : Real.log a ≤ Real.log w := Real.log_le_log ha0 hw
      have hla0 : 0 < Real.log a := by
        have := (logs_of_ge hX0 hc.hX ha).1; linarith
      apply mul_le_mul (Real.rpow_le_rpow hw0.le hwd hθ0) _
        (zpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
      rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hla0.le hlw 4))
    (fun y hy => by
      obtain ⟨hyA, hy1, hy2⟩ := hy
      set i := ⌊(y - a) / h⌋₊
      have hq0 : 0 ≤ (y - a) / h := div_nonneg (by linarith) hh0.le
      refine ⟨i, ?_, hyA, ?_, ?_⟩
      · have h1 : i ≤ ⌈(d - a) / h⌉₊ :=
          (Nat.floor_le_ceil _).trans (Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith)
            hh0.le))
        omega
      · have := Nat.floor_le hq0
        have : (i : ℝ) * h ≤ y - a := by
          rwa [le_div_iff₀ hh0] at this
        linarith
      · have := Nat.lt_floor_add_one ((y - a) / h)
        have : y - a < ((i : ℝ) + 1) * h := by
          rwa [div_lt_iff₀ hh0] at this
        nlinarith)
  have hn : (n : ℝ) ≤ (d - a) / h + 2 := by
    have h2 : (⌈(d - a) / h⌉₊ : ℝ) < (d - a) / h + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by linarith) hh0.le)
    show ((⌈(d - a) / h⌉₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast; linarith
  have hMw0 : 0 ≤ Mw := by
    have : 0 < Real.log a := by have := (logs_of_ge hX0 hc.hX ha).1; linarith
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (zpow_nonneg this.le _)
  have hloc : (localCountA A a d : ℝ) ≤ ((d - a) / h + 2) * Mw := by
    unfold localCountA
    exact hcov.trans (mul_le_mul_of_nonneg_right hn hMw0)
  unfold lagD
  linarith

end Queue6

end
