module

public import RequestProject.BSCert.Finite.X0Formula

/-!
# The jump at `X₀`: exponent vectors over the first seven primes

`nOf ps v = ∏ p_i^{v_i}`; `subs v` lists the vectors `w ≤ v`, so that the divisors of
`nOf ps v` are the `nOf ps w`, `w ∈ subs v` (`dvd_nOf_iff`, `nOf_inj`).

For `m = nOf PL v` the check `okV v hs` evaluates `120000 m² B(m)` exactly (`lhsV_eq`, from
`Bx_formula`), with every sum over divisors taken over `subs v`. The values `hs` of `H_ord` are a
certificate, checked through the zeta transform over the lattice `w ≤ v` (`zeta_spec`): the check
is `H(0) = 1` and `∑_{u ≤ w} H(u) = 2 H(w)` for `w ≠ 0`, which determines `H_ord` (`hOK_sound`).
The cost is `O(|v| · d(m))` kernel steps.
-/

@[expose] public section

open Finset

namespace BSCert.X0Vec

/-- The first seven primes. -/
def PL : List ℕ := [2, 3, 5, 7, 11, 13, 17]

/-- `∏ p_i^{v_i}` over a list of primes. -/
def nOf : List ℕ → List ℕ → ℕ
  | p :: ps, a :: v => p ^ a * nOf ps v
  | _, _ => 1

/-- All vectors `w ≤ v` (componentwise). -/
def subs : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: v => (List.range (a + 1)).flatMap fun j => (subs v).map (j :: ·)

/-- Componentwise `≤` with the same length. -/
def VLe : List ℕ → List ℕ → Prop
  | [], [] => True
  | a :: v, b :: w => a ≤ b ∧ VLe v w
  | _, _ => False

lemma mem_subs : ∀ (v w : List ℕ), w ∈ subs v ↔ VLe w v := by
  intro v
  induction v with
  | nil => intro w; cases w <;> simp [subs, VLe]
  | cons a v ih =>
    intro w
    cases w with
    | nil => simp [subs, VLe]
    | cons b w =>
      simp only [subs, List.mem_flatMap, List.mem_range, List.mem_map, VLe]
      constructor
      · rintro ⟨j, hj, w', hw', h⟩
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by omega, (ih w').mp hw'⟩
      · rintro ⟨hb, hw⟩
        exact ⟨b, by omega, w, (ih w).mpr hw, rfl⟩

lemma subs_nodup : ∀ v : List ℕ, (subs v).Nodup := by
  intro v
  induction v with
  | nil => simp [subs]
  | cons a v ih =>
    simp only [subs]
    rw [List.nodup_flatMap]
    refine ⟨fun j _ => ih.map (fun x y h => by simpa using h), ?_⟩
    refine (List.nodup_range).pairwise_of_forall_ne ?_
    intro i _ j _ hij
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_map] at hx hx'
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, h⟩ := hx'
    simp at h
    exact hij h.1.symm


lemma VLe_length : ∀ {v w : List ℕ}, VLe w v → w.length = v.length := by
  intro v
  induction v with
  | nil => intro w h; cases w <;> simp_all [VLe]
  | cons a v ih => intro w h; cases w <;> simp_all [VLe]

lemma VLe_refl : ∀ v : List ℕ, VLe v v := by
  intro v; induction v with
  | nil => trivial
  | cons a v ih => exact ⟨le_rfl, ih⟩

lemma nOf_pos : ∀ (ps v : List ℕ), (∀ p ∈ ps, p.Prime) → 0 < nOf ps v := by
  intro ps
  induction ps with
  | nil => intro v _; cases v <;> simp [nOf]
  | cons p ps ih =>
    intro v hp
    cases v with
    | nil => simp [nOf]
    | cons a v =>
      simp only [nOf]
      exact Nat.mul_pos (pow_pos (hp p (by simp)).pos _) (ih v (fun q hq => hp q (by simp [hq])))

/-- A prime not in `ps` does not divide `nOf ps v`. -/
lemma not_dvd_nOf : ∀ (ps v : List ℕ) {p : ℕ}, p.Prime → (∀ q ∈ ps, q.Prime) → p ∉ ps →
    ¬ p ∣ nOf ps v := by
  intro ps
  induction ps with
  | nil => intro v p hp _ _; cases v <;> simp [nOf, hp.ne_one]
  | cons q ps ih =>
    intro v p hp hq hnot
    cases v with
    | nil => simp [nOf, hp.ne_one]
    | cons a v =>
      simp only [nOf]
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp (hq q (by simp))).mp (hp.dvd_of_dvd_pow h1)
        exact hnot (by simp [this])
      · exact ih v hp (fun r hr => hq r (by simp [hr])) (fun h => hnot (by simp [h])) h2

lemma coprime_nOf {ps : List ℕ} {p : ℕ} (hp : p.Prime) (hq : ∀ q ∈ ps, q.Prime) (hnot : p ∉ ps)
    (v : List ℕ) (a : ℕ) : Nat.Coprime (p ^ a) (nOf ps v) :=
  Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_nOf ps v hp hq hnot))

/-- The divisors of `nOf ps v` are the `nOf ps w`, `w ≤ v`. -/
lemma dvd_nOf_iff : ∀ (ps : List ℕ) (v : List ℕ), ps.Nodup → (∀ p ∈ ps, p.Prime) →
    v.length = ps.length → ∀ d, d ∣ nOf ps v ↔ ∃ w, VLe w v ∧ d = nOf ps w := by
  intro ps
  induction ps with
  | nil =>
    intro v _ _ hl d
    cases v with
    | nil =>
      simp only [nOf, Nat.dvd_one]
      constructor
      · intro h; exact ⟨[], trivial, h⟩
      · rintro ⟨w, hw, rfl⟩; cases w <;> simp_all [VLe]
    | cons a v => simp at hl
  | cons p ps ih =>
    intro v hnd hpr hl d
    cases v with
    | nil => simp at hl
    | cons a v =>
      have hp : p.Prime := hpr p (by simp)
      have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hpr q (by simp [hq])
      have hnot : p ∉ ps := (List.nodup_cons.mp hnd).1
      have hnd' := (List.nodup_cons.mp hnd).2
      simp only [nOf]
      constructor
      · intro h
        obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.mp h
        obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp h1
        obtain ⟨w, hw, rfl⟩ := (ih v hnd' hpr' (by simpa using hl) d2).mp h2
        exact ⟨j :: w, ⟨hj, hw⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        cases w with
        | nil => exact absurd hw (by simp [VLe])
        | cons j w =>
          obtain ⟨hj, hw⟩ := hw
          simp only [nOf]
          exact mul_dvd_mul (pow_dvd_pow p hj) ((ih v hnd' hpr' (by simpa using hl) _).mpr ⟨w, hw, rfl⟩)

/-- `nOf ps` is injective on vectors of the right length. -/
lemma nOf_inj : ∀ (ps : List ℕ) (v w : List ℕ), ps.Nodup → (∀ p ∈ ps, p.Prime) →
    v.length = ps.length → w.length = ps.length → nOf ps v = nOf ps w → v = w := by
  intro ps
  induction ps with
  | nil => intro v w _ _ hv hw _; cases v <;> cases w <;> simp_all
  | cons p ps ih =>
    intro v w hnd hpr hv hw h
    cases v with
    | nil => simp at hv
    | cons a v =>
      cases w with
      | nil => simp at hw
      | cons b w =>
        have hp : p.Prime := hpr p (by simp)
        have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hpr q (by simp [hq])
        have hnot : p ∉ ps := (List.nodup_cons.mp hnd).1
        have hnd' := (List.nodup_cons.mp hnd).2
        simp only [nOf] at h
        have hM : ∀ u : List ℕ, (nOf ps u).factorization p = 0 := fun u =>
          Nat.factorization_eq_zero_of_not_dvd (not_dvd_nOf ps u hp hpr' hnot)
        have hfa : (p ^ a * nOf ps v).factorization p = a := by
          rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (nOf_pos ps v hpr').ne',
            Finsupp.add_apply, hM, Nat.factorization_pow, hp.factorization]; simp
        have hfb : (p ^ b * nOf ps w).factorization p = b := by
          rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (nOf_pos ps w hpr').ne',
            Finsupp.add_apply, hM, Nat.factorization_pow, hp.factorization]; simp
        have hab : a = b := by rw [← hfa, ← hfb, h]
        subst hab
        have h2 : nOf ps v = nOf ps w :=
          Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h
        rw [ih v w hnd' hpr' (by simpa using hv) (by simpa using hw) h2]


/-- `|subs v| = ∏ (v_i + 1)`. -/
def bs : List ℕ → ℕ
  | [] => 1
  | a :: v => (a + 1) * bs v

lemma length_subs : ∀ v : List ℕ, (subs v).length = bs v := by
  intro v
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [subs, bs, List.length_flatMap, List.length_map, ih]
    simp

/-- Running sums of blocks: block `j` of the output is `acc + F(block 0) + … + F(block j)`. -/
def zrun (F : List ℕ → List ℕ) (n : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, acc, xs => List.zipWith (· + ·) acc (F (xs.take n))
  | k + 1, acc, xs =>
    List.zipWith (· + ·) acc (F (xs.take n)) ++
      zrun F n k (List.zipWith (· + ·) acc (F (xs.take n))) (xs.drop n)

/-- The zeta transform over the lattice `w ≤ v` (values listed in the order of `subs v`). -/
def zeta : List ℕ → List ℕ → List ℕ
  | [], xs => xs
  | a :: v, xs => zrun (zeta v) (bs v) a (List.replicate (bs v) 0) xs

lemma zipWith_map_map {α : Type*} (l : List α) (f g : α → ℕ) :
    List.zipWith (· + ·) (l.map f) (l.map g) = l.map (fun x => f x + g x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Sum of the first `j` blocks. -/
def SB (g : List ℕ → ℕ) (j : ℕ) (w : List ℕ) : ℕ :=
  ((List.range j).map fun i => ((subs w).map fun u => g (i :: u)).sum).sum

lemma SB_succ (g : List ℕ → ℕ) (j : ℕ) (w : List ℕ) :
    SB g (j + 1) w = SB g j w + ((subs w).map fun u => g (j :: u)).sum := by
  simp [SB, List.range_succ]


lemma map_subs_cons (g : List ℕ → ℕ) (a : ℕ) (v : List ℕ) :
    (subs (a :: v)).map g = ((List.range (a + 1)).map fun j => (subs v).map fun u => g (j :: u)).flatten := by
  simp [subs, List.map_flatMap, List.flatMap_def, Function.comp_def]

lemma sum_flatten' : ∀ L : List (List ℕ), L.flatten.sum = (L.map List.sum).sum := by
  intro L; induction L with
  | nil => rfl
  | cons l L ih => simp [List.sum_append_nat, ih]

lemma sum_subs_cons (g : List ℕ → ℕ) (j : ℕ) (w : List ℕ) :
    ((subs (j :: w)).map g).sum = SB g (j + 1) w := by
  rw [map_subs_cons, sum_flatten', List.map_map]; rfl

lemma zrun_spec (F : List ℕ → List ℕ) (v : List ℕ) (g : List ℕ → ℕ)
    (hF : ∀ h : List ℕ → ℕ, F ((subs v).map h) = (subs v).map fun w => ((subs w).map h).sum) :
    ∀ k j0, zrun F (bs v) k ((subs v).map (SB g j0))
      ((List.range' j0 (k + 1)).map fun j => (subs v).map fun u => g (j :: u)).flatten =
      ((List.range' j0 (k + 1)).map fun j => (subs v).map (SB g (j + 1))).flatten := by
  intro k
  induction k with
  | zero =>
    intro j0
    simp only [zero_add, List.range'_one, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, zrun]
    rw [List.take_of_length_le (by simp [length_subs]), hF, zipWith_map_map]
    congr 1; funext w; rw [SB_succ]
  | succ k ih =>
    intro j0
    rw [List.range'_succ, List.map_cons, List.flatten_cons, List.map_cons, List.flatten_cons, zrun]
    have ht : (((subs v).map fun u => g (j0 :: u)) ++ ((List.range' (j0 + 1) (k + 1)).map
        fun j => (subs v).map fun u => g (j :: u)).flatten).take (bs v) =
        (subs v).map fun u => g (j0 :: u) := by
      rw [List.take_append_of_le_length (by simp [length_subs]),
        List.take_of_length_le (by simp [length_subs])]
    have hd : (((subs v).map fun u => g (j0 :: u)) ++ ((List.range' (j0 + 1) (k + 1)).map
        fun j => (subs v).map fun u => g (j :: u)).flatten).drop (bs v) =
        ((List.range' (j0 + 1) (k + 1)).map fun j => (subs v).map fun u => g (j :: u)).flatten := by
      rw [List.drop_append_of_le_length (by simp [length_subs]),
        List.drop_of_length_le (by simp [length_subs]), List.nil_append]
    have hz : List.zipWith (· + ·) ((subs v).map (SB g j0)) (F ((subs v).map fun u => g (j0 :: u))) =
        (subs v).map (SB g (j0 + 1)) := by
      rw [hF, zipWith_map_map]; congr 1; funext w; rw [SB_succ]
    rw [ht, hd, hz, ih]

lemma SB_zero (g : List ℕ → ℕ) (w : List ℕ) : SB g 0 w = 0 := rfl

/-- **The zeta transform**: `zeta v` maps the values `g(w)`, `w ∈ subs v`, to
`∑_{u ≤ w} g(u)`. -/
theorem zeta_spec : ∀ (v : List ℕ) (g : List ℕ → ℕ),
    zeta v ((subs v).map g) = (subs v).map fun w => ((subs w).map g).sum := by
  intro v
  induction v with
  | nil => intro g; simp [zeta, subs]
  | cons a v ih =>
    intro g
    have h0 : List.replicate (bs v) 0 = (subs v).map (SB g 0) := by
      symm; rw [List.eq_replicate_iff]; simp [length_subs, SB_zero]
    rw [zeta, h0, map_subs_cons, List.range_eq_range', zrun_spec (zeta v) v g ih a 0,
      map_subs_cons, ← List.range_eq_range']
    congr 1
    refine List.map_congr_left fun j _ => ?_
    refine List.map_congr_left fun w _ => ?_
    rw [sum_subs_cons]


/-! ## The certificate for `H_ord` -/

lemma PL_prime : ∀ p ∈ PL, p.Prime := by
  simp only [PL, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

lemma PL_nodup : PL.Nodup := by decide

lemma VLe_trans : ∀ {u w v : List ℕ}, VLe u w → VLe w v → VLe u v := by
  intro u
  induction u with
  | nil => intro w v h1 h2; cases w <;> cases v <;> simp_all [VLe]
  | cons a u ih =>
    intro w v h1 h2
    cases w with
    | nil => simp [VLe] at h1
    | cons b w =>
      cases v with
      | nil => simp [VLe] at h2
      | cons c v => exact ⟨h1.1.trans h2.1, ih h1.2 h2.2⟩

/-- All entries zero. -/
def isZ : List ℕ → Bool
  | [] => true
  | a :: v => a == 0 && isZ v

lemma nOf_eq_one_iff : ∀ (w : List ℕ), w.length ≤ PL.length → (nOf PL w = 1 ↔ isZ w = true) := by
  have key : ∀ (ps w : List ℕ), (∀ p ∈ ps, p.Prime) → w.length ≤ ps.length →
      (nOf ps w = 1 ↔ isZ w = true) := by
    intro ps
    induction ps with
    | nil => intro w _ hl; cases w <;> simp_all [nOf, isZ]
    | cons p ps ih =>
      intro w hp hl
      cases w with
      | nil => simp [nOf, isZ]
      | cons a w =>
        have hpp : p.Prime := hp p (by simp)
        simp only [nOf, isZ, Bool.and_eq_true, beq_iff_eq]
        rw [← ih w (fun q hq => hp q (by simp [hq])) (by simpa using hl), mul_eq_one,
          Nat.pow_eq_one]
        simp [hpp.ne_one]
  exact fun w hl => key PL w PL_prime hl

lemma length_of_mem_subs {v w : List ℕ} (hw : w ∈ subs v) : w.length = v.length :=
  VLe_length ((mem_subs v w).mp hw)

lemma nodup_map_subs {w : List ℕ} (hw : w.length = PL.length) : ((subs w).map (nOf PL)).Nodup :=
  (subs_nodup w).map_on fun a ha b hb h =>
    nOf_inj PL a b PL_nodup PL_prime ((length_of_mem_subs ha).trans hw)
      ((length_of_mem_subs hb).trans hw) h

lemma divisors_nOf {w : List ℕ} (hw : w.length = PL.length) :
    (nOf PL w).divisors = ((subs w).map (nOf PL)).toFinset := by
  ext d
  rw [Nat.mem_divisors, List.mem_toFinset, List.mem_map,
    dvd_nOf_iff PL w PL_nodup PL_prime hw d]
  simp only [mem_subs]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, -⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu, rfl⟩, (nOf_pos PL w PL_prime).ne'⟩

lemma sum_divisors_nOf {M : Type*} [AddCommMonoid M] (F : ℕ → M) {w : List ℕ}
    (hw : w.length = PL.length) :
    ∑ d ∈ (nOf PL w).divisors, F d = ((subs w).map fun u => F (nOf PL u)).sum := by
  rw [divisors_nOf hw, List.sum_toFinset _ (nodup_map_subs hw), List.map_map]; rfl

lemma sum_split {α : Type*} [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l)
    (f : α → ℕ) : (l.map f).sum = f a + ((l.erase a).map f).sum := by
  rw [((List.perm_cons_erase ha).map f).sum_eq]; simp

lemma two_Hord {m : ℕ} (hm : 1 < m) : ∑ d ∈ m.divisors, BSCert.X0Band.Hord d = 2 * BSCert.X0Band.Hord m := by
  have h := BSCert.X0Band.Hord_eq m
  rw [if_neg (by omega)] at h
  rw [← Nat.insert_self_properDivisors (by omega), Finset.sum_insert Nat.self_notMem_properDivisors,
    ← h]
  ring

/-- Values attached to `subs v`, as a function. -/
def gOf (l : List (List ℕ)) (hs : List ℕ) (w : List ℕ) : ℕ := ((l.zip hs).lookup w).getD 0

lemma map_gOf : ∀ (l : List (List ℕ)) (hs : List ℕ), l.Nodup → l.length = hs.length →
    l.map (gOf l hs) = hs := by
  intro l
  induction l with
  | nil => intro hs _ h; cases hs <;> simp_all
  | cons w l ih =>
    intro hs hnd hl
    cases hs with
    | nil => simp at hl
    | cons h hs =>
      have hw : w ∉ l := (List.nodup_cons.mp hnd).1
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨by simp [gOf, List.lookup_cons], ?_⟩
      conv_rhs => rw [← ih hs (List.nodup_cons.mp hnd).2 (by simpa using hl)]
      refine List.map_congr_left fun u hu => ?_
      have : (u == w) = false := by
        rw [beq_eq_false_iff_ne]; rintro rfl; exact hw hu
      simp [gOf, List.lookup_cons, this]

/-- Pointwise check of `zeta v hs` against `hs`: `H(0) = 1`, `∑_{u ≤ w} H(u) = 2 H(w)`. -/
def zchk : List (List ℕ) → List ℕ → List ℕ → Bool
  | w :: ws, z :: zs, h :: hs => (if isZ w then h == 1 else z == 2 * h) && zchk ws zs hs
  | _, _, _ => true

lemma zchk_spec (F G : List ℕ → ℕ) : ∀ l : List (List ℕ), zchk l (l.map F) (l.map G) = true →
    ∀ w ∈ l, (isZ w = true → G w = 1) ∧ (isZ w = false → F w = 2 * G w) := by
  intro l
  induction l with
  | nil => intro _ w hw; simp at hw
  | cons a l ih =>
    intro h w hw
    simp only [List.map_cons, zchk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · constructor
      · intro hz; simpa [hz] using h.1
      · intro hz; simpa [hz] using h.1
    · exact ih h.2 w hw

/-- The `H_ord` certificate for `v`: `hs` lists `H_ord(nOf w)`, `w ∈ subs v`. -/
def hOK (v hs : List ℕ) : Bool := hs.length == bs v && zchk (subs v) (zeta v hs) hs

theorem hOK_sound {v hs : List ℕ} (hv : v.length = PL.length) (h : hOK v hs = true) :
    hs = (subs v).map fun w => BSCert.X0Band.Hord (nOf PL w) := by
  simp only [hOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, hz⟩ := h
  set g := gOf (subs v) hs
  have hg : (subs v).map g = hs := map_gOf _ _ (subs_nodup v) (by rw [length_subs, hl])
  rw [← hg, zeta_spec] at hz
  have hs := zchk_spec _ _ _ hz
  suffices H : ∀ M w, nOf PL w = M → w ∈ subs v → g w = BSCert.X0Band.Hord (nOf PL w) by
    rw [← hg]; exact List.map_congr_left fun w hw => H _ w rfl hw
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro w hM hw
    have hwl : w.length = PL.length := (length_of_mem_subs hw).trans hv
    cases hzw : isZ w
    · have h2 := (hs w hw).2 hzw
      have h1 : 1 < nOf PL w := by
        have := nOf_pos PL w PL_prime
        have : nOf PL w ≠ 1 := fun h => by
          rw [(nOf_eq_one_iff w hwl.le).mp h] at hzw; exact absurd hzw (by simp)
        omega
      have hH := two_Hord h1
      rw [sum_divisors_nOf _ hwl] at hH
      have hws : w ∈ subs w := (mem_subs w w).mpr (VLe_refl w)
      rw [sum_split (subs_nodup w) hws] at h2 hH
      have hrest : ((subs w).erase w).map g = ((subs w).erase w).map
          fun u => BSCert.X0Band.Hord (nOf PL u) := by
        refine List.map_congr_left fun u hu => ?_
        have hu' := (subs_nodup w).mem_erase_iff.mp hu
        have hvle : VLe u v := VLe_trans ((mem_subs w u).mp hu'.2) ((mem_subs v w).mp hw)
        have hul : u.length = PL.length := (VLe_length ((mem_subs w u).mp hu'.2)).trans hwl
        have hdvd : nOf PL u ∣ nOf PL w :=
          (dvd_nOf_iff PL w PL_nodup PL_prime hwl _).mpr ⟨u, (mem_subs w u).mp hu'.2, rfl⟩
        have hne : nOf PL u ≠ nOf PL w := fun h =>
          hu'.1 (nOf_inj PL u w PL_nodup PL_prime hul hwl h)
        have hlt : nOf PL u < nOf PL w :=
          lt_of_le_of_ne (Nat.le_of_dvd (nOf_pos PL w PL_prime) hdvd) hne
        exact ih _ (hM ▸ hlt) u rfl ((mem_subs v u).mpr hvle)
      have e := congrArg List.sum hrest
      omega
    · rw [(hs w hw).1 hzw, (nOf_eq_one_iff w hwl.le).mpr hzw, BSCert.X0Band.Hord_eq]; rfl


/-! ## Squarefree parts and the counts `c` -/

/-- `μ²` of `nOf PL w`. -/
def sqV : List ℕ → ℕ
  | [] => 1
  | a :: v => if a ≤ 1 then sqV v else 0

/-- The number of squarefree `u ≤ w`. -/
def cntSq : List ℕ → ℕ
  | [] => 1
  | a :: v => (if a = 0 then 1 else 2) * cntSq v

/-- `c(nOf PL x)`. -/
def cV (x : List ℕ) : ℕ := cntSq x - 1 - (if isZ x then 0 else sqV x)

/-- `v - w`. -/
def vsub (v w : List ℕ) : List ℕ := List.zipWith (· - ·) v w

lemma sq_nOf : ∀ (ps w : List ℕ), ps.Nodup → (∀ p ∈ ps, p.Prime) → w.length ≤ ps.length →
    BSCert.X0Band.sq (nOf ps w) = sqV w := by
  intro ps
  induction ps with
  | nil => intro w _ _ hl; cases w <;> simp_all [nOf, sqV, BSCert.X0Band.sq]
  | cons p ps ih =>
    intro w hnd hp hl
    cases w with
    | nil => simp [nOf, sqV, BSCert.X0Band.sq]
    | cons a w =>
      have hpp : p.Prime := hp p (by simp)
      have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (by simp [hq])
      have hnot : p ∉ ps := (List.nodup_cons.mp hnd).1
      have ih' := ih w (List.nodup_cons.mp hnd).2 hpr' (by simpa using hl)
      simp only [nOf, sqV]
      unfold BSCert.X0Band.sq at ih' ⊢
      have hc := coprime_nOf hpp hpr' hnot w a
      have hpow : Squarefree (p ^ a) ↔ a ≤ 1 := by
        rcases Nat.lt_or_ge a 2 with h | h
        · interval_cases a
          · simp
          · simp [hpp.squarefree]
        · rw [Nat.squarefree_pow_iff hpp.ne_one (by omega)]; omega
      have key : Squarefree (p ^ a * nOf ps w) ↔ a ≤ 1 ∧ Squarefree (nOf ps w) := by
        rw [Nat.squarefree_mul_iff, hpow]; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
      rw [← ih']
      by_cases ha : a ≤ 1 <;> simp [key, ha]

lemma sum_range_if (a C : ℕ) :
    ((List.range (a + 1)).map fun j => if j ≤ 1 then C else 0).sum = (if a = 0 then 1 else 2) * C := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.map_append, List.sum_append_nat, ih]
    rcases a with _ | a <;> simp <;> omega

lemma sum_sqV_subs : ∀ x : List ℕ, ((subs x).map sqV).sum = cntSq x := by
  intro x
  induction x with
  | nil => simp [subs, sqV, cntSq]
  | cons a x ih =>
    rw [map_subs_cons, sum_flatten', List.map_map]
    have : ((fun l : List ℕ => l.sum) ∘ fun j => (subs x).map fun u => sqV (j :: u)) =
        fun j => if j ≤ 1 then cntSq x else 0 := by
      funext j
      simp only [Function.comp_def, sqV]
      split_ifs
      · exact ih
      · simp
    rw [this, sum_range_if]; rfl

lemma cS_nOf {x : List ℕ} (hx : x.length = PL.length) : BSCert.X0Band.cS (nOf PL x) = cV x := by
  have hs : ∑ e ∈ (nOf PL x).divisors, BSCert.X0Band.sq e = cntSq x := by
    rw [sum_divisors_nOf _ hx, ← sum_sqV_subs]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    exact sq_nOf PL u PL_nodup PL_prime ((length_of_mem_subs hu).trans hx).le
  have hM := nOf_pos PL x PL_prime
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun e => 1 < e ∧ e < nOf PL x)] at hs
  unfold BSCert.X0Band.cS cV
  by_cases hz : isZ x = true
  · have h1 : nOf PL x = 1 := (nOf_eq_one_iff x hx.le).mpr hz
    have hc1 : cntSq x = 1 := by
      have := sum_sqV_subs x
      rw [← this]
      have hsub : subs x = [x] := by
        clear this hs h1 hM hx
        induction x with
        | nil => rfl
        | cons a x ih =>
          simp only [isZ, Bool.and_eq_true, beq_iff_eq] at hz
          obtain ⟨rfl, hz⟩ := hz
          simp [subs, ih hz]
      rw [hsub]; simp
      clear this hsub hs h1 hM hx
      induction x with
      | nil => rfl
      | cons a x ih =>
        simp only [isZ, Bool.and_eq_true, beq_iff_eq] at hz
        obtain ⟨rfl, hz⟩ := hz
        simp [sqV, ih hz]
    rw [h1, hc1]
    simp only [hz, if_true]
    have : (Nat.divisors 1).filter (fun e => 1 < e ∧ e < 1) = ∅ := by
      ext e; simp; omega
    rw [this]; rfl
  · have h1 : 1 < nOf PL x := by
      have : nOf PL x ≠ 1 := fun h => hz ((nOf_eq_one_iff x hx.le).mp h)
      omega
    have hset : (nOf PL x).divisors.filter (fun e => ¬(1 < e ∧ e < nOf PL x)) = {1, nOf PL x} := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd, -⟩, hne⟩
        have := Nat.le_of_dvd hM hd
        have : 0 < e := Nat.pos_of_dvd_of_pos hd hM
        omega
      · rintro (rfl | rfl)
        · exact ⟨⟨one_dvd _, by omega⟩, by omega⟩
        · exact ⟨⟨dvd_refl _, by omega⟩, by omega⟩
    rw [hset, Finset.sum_pair (by omega), sq_nOf PL x PL_nodup PL_prime hx.le] at hs
    simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.false_eq_true, if_false]
    have : BSCert.X0Band.sq 1 = 1 := by simp [BSCert.X0Band.sq]
    omega

lemma nOf_vsub : ∀ (ps v w : List ℕ), VLe w v → nOf ps w * nOf ps (vsub v w) = nOf ps v := by
  intro ps
  induction ps with
  | nil => intro v w _; cases v <;> cases w <;> simp [nOf, vsub]
  | cons p ps ih =>
    intro v w h
    cases v with
    | nil => cases w <;> simp_all [VLe, nOf, vsub]
    | cons a v =>
      cases w with
      | nil => simp [VLe] at h
      | cons b w =>
        obtain ⟨hab, h⟩ := h
        have := ih v w h
        simp only [vsub, List.zipWith_cons_cons, nOf] at this ⊢
        rw [← this, show p ^ a = p ^ b * p ^ (a - b) by rw [← pow_add]; congr 1; omega]
        ring

lemma vsub_length {v w : List ℕ} (h : VLe w v) : (vsub v w).length = v.length := by
  simp [vsub, VLe_length h]

/-- `Q`, from the list `hs` of values of `H_ord`. -/
def qV (v : List ℕ) : List (List ℕ) → List ℕ → ℕ
  | w :: ws, h :: hs => (if isZ w then 0 else h * nOf PL (vsub v w) * cV (vsub v w)) + qV v ws hs
  | _, _ => 0

lemma qV_map (v : List ℕ) (g : List ℕ → ℕ) : ∀ l : List (List ℕ), qV v l (l.map g) =
    (l.map fun w => if isZ w then 0 else g w * nOf PL (vsub v w) * cV (vsub v w)).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons w l ih => simp [qV, ih]

lemma QS_nOf {v : List ℕ} (hv : v.length = PL.length) :
    BSCert.X0Band.QS (nOf PL v) = qV v (subs v) ((subs v).map fun w => BSCert.X0Band.Hord (nOf PL w)) := by
  rw [qV_map, BSCert.X0Band.QS, Finset.sum_filter, sum_divisors_nOf _ hv]
  congr 1
  refine List.map_congr_left fun w hw => ?_
  have hvle := (mem_subs v w).mp hw
  have hwl : w.length = PL.length := (VLe_length hvle).trans hv
  have hdiv : nOf PL v / nOf PL w = nOf PL (vsub v w) := by
    rw [← nOf_vsub PL v w hvle, Nat.mul_div_cancel_left _ (nOf_pos PL w PL_prime)]
  have hpos := nOf_pos PL w PL_prime
  cases hz : isZ w
  · have h1 : 1 < nOf PL w := by
      have : nOf PL w ≠ 1 := fun h => by rw [(nOf_eq_one_iff w hwl.le).mp h] at hz; simp at hz
      omega
    rw [if_pos h1, if_neg (by simp), hdiv, cS_nOf ((vsub_length hvle).trans hv)]
  · rw [if_pos rfl, if_neg (by rw [(nOf_eq_one_iff w hwl.le).mpr hz]; omega)]

/-! ## The check for one representative -/

/-- `3 (20000 m μ²(m) + 40000 m c(m) + 10001 Q(m))` (`= 120000 m² B(m)`). -/
def lhsV (v hs : List ℕ) : ℕ :=
  3 * (20000 * nOf PL v * sqV v + 40000 * nOf PL v * cV v + 10001 * qV v (subs v) hs)

/-- `B(nOf PL v) < 5/12`, given the `H_ord` certificate `hs`. -/
def okV (v hs : List ℕ) : Bool :=
  hOK v hs && Nat.blt (lhsV v hs) (50000 * nOf PL v * nOf PL v)

theorem lhsV_eq {v hs : List ℕ} (hv : v.length = PL.length) (h : hOK v hs = true) :
    BSCert.X0Band.Bx (nOf PL v) * (120000 * (nOf PL v : ℚ) ^ 2) = lhsV v hs := by
  have hm : nOf PL v ≠ 0 := (nOf_pos PL v PL_prime).ne'
  have hf := BSCert.X0Band.Bx_formula hm
  rw [hOK_sound hv h, lhsV, ← QS_nOf hv, ← cS_nOf hv, ← sq_nOf PL v PL_nodup PL_prime hv.le]
  push_cast
  linear_combination 3 * hf

theorem okV_sound {v hs : List ℕ} (hv : v.length = PL.length) (h : okV v hs = true) :
    BSCert.X0Band.Bx (nOf PL v) < 5 / 12 := by
  simp only [okV, Bool.and_eq_true, Nat.blt_eq] at h
  have he := lhsV_eq hv h.1
  have hlt : (lhsV v hs : ℚ) < 50000 * (nOf PL v : ℚ) * nOf PL v := by exact_mod_cast h.2
  have hpos : (0 : ℚ) < (nOf PL v : ℚ) := by exact_mod_cast nOf_pos PL v PL_prime
  rw [← he] at hlt
  nlinarith


/-- `B(nOf PL v) = 5/12`, given the `H_ord` certificate `hs`. -/
def eqV (v hs : List ℕ) : Bool :=
  hOK v hs && Nat.beq (lhsV v hs) (50000 * nOf PL v * nOf PL v)

theorem eqV_sound {v hs : List ℕ} (hv : v.length = PL.length) (h : eqV v hs = true) :
    BSCert.X0Band.Bx (nOf PL v) = 5 / 12 := by
  simp only [eqV, Bool.and_eq_true, Nat.beq_eq] at h
  have he := lhsV_eq hv h.1
  have heq : (lhsV v hs : ℚ) = 50000 * (nOf PL v : ℚ) * nOf PL v := by exact_mod_cast h.2
  have hpos : (0 : ℚ) < (nOf PL v : ℚ) := by exact_mod_cast nOf_pos PL v PL_prime
  rw [← he] at heq
  field_simp at heq
  linarith

end BSCert.X0Vec
