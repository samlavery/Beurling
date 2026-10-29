module

public import RequestProject.Beurling.RankFull.OneRun
public import RequestProject.Beurling.RankFull.PILFlat
public import RequestProject.Beurling.RankFull.PILChain
public import RequestProject.Beurling.RankFull.VolumeCaps
public import RequestProject.Beurling.RankFull.EulerOneRun

/-!
# Lemma A.5 + Theorem A.12 for one run: `SkeletonBound` for `l = [k]` in the window model

The window model of `WindowModel.lean` over a jitter process `J : JitterLaw` (decided slots
`dec ω = {n | ω ∈ A n}`, values `q ω n = J.q n ω`), for one skeleton `𝔰 = (E_P, [k])` with a single
run (`T = 1`; no late block, every free column in the early block).

The integrands of Lemma A.5 (pivot labels latest first, `m` the slot of the earliest pivot):
* `PsiOne m ω t = ∑_c 1(u_c ≤ m ≤ s_max) 1(dec(c)) 1(G_{<m}) 1(t ∈ box_c)`, the sum over the
  contents `c` of the early block and the tails (`contents`), `u_c` the first slot after the
  latest free slot, `box_c` = caps `t_j ≥ τ_j` and all rows `c_i ∏_j t_j^{E_ij}` in `J`;
  it is `F_m ⊗ Borel`-measurable;
* `PsiBar ω t`, the same with `1(G_{<m})` replaced by `χ_c = 1(u_c ≤ s_max) 1(G_{<u_c})`
  (step (i), label replacement), free of `m`; it dominates every `PsiOne m`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θ : ℝ≥0∞}

/-- The value `d ∏_{n < m} q_n^{w_n}` of a row content, through the slots before `m` only. -/
noncomputable def cvalLt (J : JitterLaw Ω P θ) (m : ℕ) (ω : Ω) (x : (Fin N → ℕ) × ℕ) : ℝ :=
  (x.2 : ℝ) * ∏ n ∈ univ.filter (fun n : Fin N => (n : ℕ) < m), J.q n ω ^ x.1 n

/-- The integration box of Lemma A.5: caps and windows. -/
def boxSet {K : ℕ} (τ' : Fin K → ℝ) (E' : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ)
    (cv : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {t | (∀ j, τ' j ≤ t j) ∧ ∀ i, nmap cv E' t i ∈ Jw}

/-- All free slots of the content are decided. -/
def decSet {K : ℕ} (J : JitterLaw Ω P θ) (c : Fin K → (Fin N → ℕ) × ℕ) : Set Ω :=
  {ω | DecOK (fun n => ω ∈ J.A n) c}

/-- The pivot integrand of Lemma A.5 for one run, at the earliest pivot slot `m`. -/
noncomputable def PsiOne {K : ℕ} (J : JitterLaw Ω P θ) (G : ℕ → Set Ω) (τ' : Fin K → ℝ)
    (E' : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (m : ℕ) (ω : Ω)
    (_ : Unit) (t : Fin K → ℝ) : ℝ≥0∞ :=
  ∑ c ∈ contents K N D Dmax X₀, if uOf c ≤ m ∧ m ≤ smax then
    (decSet J c ∩ G m).indicator 1 ω *
      (boxSet τ' E' Jw fun i => cvalLt J m ω (c i)).indicator 1 t else 0

/-- The dominating integrand (after the label replacement of step (i)). -/
noncomputable def PsiBar {K : ℕ} (J : JitterLaw Ω P θ) (G : ℕ → Set Ω) (τ' : Fin K → ℝ)
    (E' : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (ω : Ω)
    (_ : Unit) (t : Fin K → ℝ) : ℝ≥0∞ :=
  ∑ c ∈ contents K N D Dmax X₀, if uOf c ≤ smax then
    (decSet J c ∩ G (uOf c)).indicator 1 ω *
      (boxSet τ' E' Jw fun i => cval (fun n => J.q n ω) (c i)).indicator 1 t else 0

lemma cvalLt_eq {J : JitterLaw Ω P θ} {m : ℕ} {ω : Ω} {K : ℕ}
    {c : Fin K → (Fin N → ℕ) × ℕ} (hc : uOf c ≤ m) (i : Fin K) :
    cvalLt J m ω (c i) = cval (fun n => J.q n ω) (c i) := by
  unfold cvalLt cval
  congr 1
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun n _ => ?_
  split_ifs with h
  · rfl
  · have : (c i).1 n = 0 := by
      by_contra h0; exact h ((uOf_le_iff c m).mp hc i n h0)
    simp [this]

/-- **Domination** (step (i) of Lemma A.5, `label_replace`): with nested good events. -/
theorem psiOne_le_psiBar {K : ℕ} (J : JitterLaw Ω P θ) {G : ℕ → Set Ω}
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (τ' : Fin K → ℝ) (E' : Matrix (Fin K) (Fin K) ℕ)
    (Jw : Set ℝ) (D Dmax X₀ smax m : ℕ) (ω : Ω) (p : Unit) (t : Fin K → ℝ) :
    PsiOne (N := N) J G τ' E' Jw D Dmax X₀ smax m ω p t ≤
      PsiBar (N := N) J G τ' E' Jw D Dmax X₀ smax ω p t := by
  unfold PsiOne PsiBar
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases h : uOf c ≤ m ∧ m ≤ smax
  · rw [if_pos h, if_pos (h.1.trans h.2)]
    have hbox : (boxSet τ' E' Jw fun i => cvalLt J m ω (c i)) =
        boxSet τ' E' Jw fun i => cval (fun n => J.q n ω) (c i) := by
      congr 1; funext i; exact cvalLt_eq h.1 i
    rw [hbox]
    gcongr
    exact hG _ _ h.1
  · rw [if_neg h]; exact zero_le _

/-! ## Measurability -/

lemma measurableSet_boxGraph {α : Type*} [MeasurableSpace α] {K : ℕ} (τ' : Fin K → ℝ)
    (E' : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    (cv : α → Fin K → ℝ) (hcv : ∀ i, Measurable fun a => cv a i) :
    MeasurableSet {x : α × (Fin K → ℝ) | x.2 ∈ boxSet τ' E' Jw (cv x.1)} := by
  have hset : {x : α × (Fin K → ℝ) | x.2 ∈ boxSet τ' E' Jw (cv x.1)} =
      (⋂ j, {x : α × (Fin K → ℝ) | τ' j ≤ x.2 j}) ∩
        ⋂ i, {x : α × (Fin K → ℝ) | nmap (cv x.1) E' x.2 i ∈ Jw} := by
    ext x; simp [boxSet]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => ?_)
  · exact measurableSet_le measurable_const ((measurable_pi_apply j).comp measurable_snd)
  · have : Measurable fun x : α × (Fin K → ℝ) => nmap (cv x.1) E' x.2 i := by
      unfold nmap
      exact ((hcv i).comp measurable_fst).mul (Finset.measurable_prod _ fun j _ =>
        ((measurable_pi_apply j).comp measurable_snd).pow_const _)
    exact this hJw

lemma measurable_boxInd {α : Type*} [MeasurableSpace α] {K : ℕ} (τ' : Fin K → ℝ)
    (E' : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    (cv : α → Fin K → ℝ) (hcv : ∀ i, Measurable fun a => cv a i) :
    Measurable fun x : α × (Unit × (Fin K → ℝ)) =>
      (boxSet τ' E' Jw (cv x.1)).indicator (1 : (Fin K → ℝ) → ℝ≥0∞) x.2.2 := by
  have h := measurableSet_boxGraph τ' E' hJw cv hcv
  have hm : Measurable fun x : α × (Unit × (Fin K → ℝ)) => (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have : (fun x : α × (Unit × (Fin K → ℝ)) =>
      (boxSet τ' E' Jw (cv x.1)).indicator (1 : (Fin K → ℝ) → ℝ≥0∞) x.2.2) =
      ((fun x : α × (Unit × (Fin K → ℝ)) => (x.1, x.2.2)) ⁻¹'
        {x : α × (Fin K → ℝ) | x.2 ∈ boxSet τ' E' Jw (cv x.1)}).indicator 1 := by
    funext x; simp [Set.indicator]
  rw [this]
  exact measurable_one.indicator (hm h)

lemma measurableSet_decSet {K : ℕ} (J : JitterLaw Ω P θ) (c : Fin K → (Fin N → ℕ) × ℕ)
    (m : ℕ) (hc : uOf c ≤ m) : MeasurableSet[J.F m] (decSet J c) := by
  have : decSet J c = ⋂ i, ⋂ n, (if (c i).1 n ≠ 0 then J.A n else Set.univ) := by
    ext ω
    simp only [decSet, DecOK, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i n; split_ifs with hn
      · exact h i n hn
      · trivial
    · intro h i n hn; have := h i n; rwa [if_pos hn] at this
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun n => ?_
  split_ifs with hn
  · have hlt := (uOf_le_iff c m).mp hc i n hn
    exact J.F_mono (by omega : (n : ℕ) ≤ m) _ (J.A_meas n)
  · exact MeasurableSet.univ

/-- A generic measurability statement for the integrands. -/
lemma measurable_terms {α C : Type*} [MeasurableSpace α] {K : ℕ} (τ' : Fin K → ℝ)
    (E' : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw) (cs : Finset C)
    (cond : C → Prop) [DecidablePred cond] (S : C → Set α) (hS : ∀ c, cond c → MeasurableSet (S c))
    (cv : C → α → Fin K → ℝ) (hcv : ∀ c, cond c → ∀ i, Measurable fun a => cv c a i) :
    Measurable fun x : α × (Unit × (Fin K → ℝ)) => ∑ c ∈ cs, if cond c then
      (S c).indicator (1 : α → ℝ≥0∞) x.1 *
        (boxSet τ' E' Jw (cv c x.1)).indicator (1 : (Fin K → ℝ) → ℝ≥0∞) x.2.2 else 0 := by
  refine Finset.measurable_sum _ fun c _ => ?_
  by_cases h : cond c
  · simp only [if_pos h]
    exact ((measurable_one.indicator (hS c h)).comp measurable_fst).mul
      (measurable_boxInd τ' E' hJw (cv c) (hcv c h))
  · simp only [if_neg h]; exact measurable_const

lemma measurable_cvalLt {α : Type*} [MeasurableSpace α] (q : Fin N → α → ℝ) (m : ℕ)
    (hq : ∀ n : Fin N, (n : ℕ) < m → Measurable (q n)) (x : (Fin N → ℕ) × ℕ) :
    Measurable fun a => (x.2 : ℝ) * ∏ n ∈ univ.filter (fun n : Fin N => (n : ℕ) < m),
      q n a ^ x.1 n :=
  measurable_const.mul (Finset.measurable_prod _ fun n hn =>
    (hq n (Finset.mem_filter.mp hn).2).pow_const _)

/-- `PsiOne m` is adapted: `F_m ⊗ Borel`-measurable. -/
theorem psiOne_jmeas {K : ℕ} (J : JitterLaw Ω P θ) {G : ℕ → Set Ω}
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (τ' : Fin K → ℝ) (E' : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (D Dmax X₀ smax m : ℕ) :
    JMeas (J.F m) (fun x : Ω × (Unit × (Fin K → ℝ)) =>
      PsiOne (N := N) J G τ' E' Jw D Dmax X₀ smax m x.1 x.2.1 x.2.2) := by
  unfold JMeas PsiOne
  have hq : ∀ n : Fin N, (n : ℕ) < m → Measurable[J.F m] (fun ω => J.q n ω) := fun n hn =>
    (J.q_meas n).mono (J.F_mono (by omega : (n : ℕ) + 1 ≤ m)) le_rfl
  exact @measurable_terms Ω _ (J.F m) K τ' E' Jw hJw (contents K N D Dmax X₀)
    (fun c => uOf c ≤ m ∧ m ≤ smax) _ (fun c => decSet J c ∩ G m)
    (fun c h => (measurableSet_decSet J c m h.1).inter (hGm m))
    (fun c ω i => cvalLt J m ω (c i))
    (fun c _ i => @measurable_cvalLt N Ω (J.F m) (fun n ω => J.q n ω) m hq (c i))

/-- `PsiBar` is measurable. -/
theorem psiBar_meas {K : ℕ} (J : JitterLaw Ω P θ) {G : ℕ → Set Ω}
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (τ' : Fin K → ℝ) (E' : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (D Dmax X₀ smax : ℕ) :
    Measurable (fun x : Ω × (Unit × (Fin K → ℝ)) =>
      PsiBar (N := N) J G τ' E' Jw D Dmax X₀ smax x.1 x.2.1 x.2.2) := by
  unfold PsiBar
  exact measurable_terms τ' E' hJw (contents K N D Dmax X₀) (fun c => uOf c ≤ smax)
    (fun c => decSet J c ∩ G (uOf c))
    (fun c _ => (J.F_le _ _ (measurableSet_decSet J c (uOf c) le_rfl)).inter
      (J.F_le _ _ (hGm (uOf c))))
    (fun c ω i => cval (fun n => J.q n ω) (c i))
    (fun c _ i => measurable_const.mul (Finset.measurable_prod _ fun n _ =>
      (J.q_meas' n).pow_const _))

/-! ## The integral over the pivots: Volume Lemma and the Euler chain -/

lemma one_le_abs_det {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} (hE : (Ereal E).det ≠ 0) :
    1 ≤ |(Ereal E).det| := by
  set Mz : Matrix (Fin K) (Fin K) ℤ := E.map (Nat.cast : ℕ → ℤ)
  have h1 : (Ereal E).det = ((Mz.det : ℤ) : ℝ) := by
    have := RingHom.map_det (Int.castRingHom ℝ) Mz
    simp only [eq_intCast] at this
    rw [this]
    congr 1
  rw [h1] at hE ⊢
  have hd : Mz.det ≠ 0 := fun h => hE (by simp [h])
  exact_mod_cast Int.one_le_abs hd

lemma measurableSet_boxSet {K : ℕ} (τ' : Fin K → ℝ) (E' : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (cv : Fin K → ℝ) :
    MeasurableSet (boxSet τ' E' Jw cv) := by
  have h := measurableSet_boxGraph (α := Unit) τ' E' hJw (fun _ => cv) fun i => measurable_const
  have : boxSet τ' E' Jw cv = (fun t => ((), t)) ⁻¹'
      {x : Unit × (Fin K → ℝ) | x.2 ∈ boxSet τ' E' Jw cv} := by ext; simp
  rw [this]; exact (measurable_const.prodMk measurable_id) h

/-- **The Volume Lemma bound for one box**: `vol(box_c) ≤ δ^K W ∏_i 1/c_i`. -/
lemma volume_boxSet_le {K : ℕ} {τ' : Fin K → ℝ} (hτ' : ∀ j, 1 ≤ τ' j)
    {E' : Matrix (Fin K) (Fin K) ℕ} (hE : (Ereal E').det ≠ 0) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ)
    {cv : Fin K → ℝ} (hcv : ∀ i, 0 < cv i) :
    volume (boxSet τ' E' Jw cv) ≤ ENNReal.ofReal (δ ^ K *
      (∏ j, (τ' j)⁻¹ ^ ((∑ i, E' i j) - 1)) * ∏ i, (cv i)⁻¹) := by
  have h := volume_bound_caps hcv hE (measurableSet_boxSet τ' E' hJw cv) hτ'
    (fun t ht j => ht.1 j) Jw (fun t ht i => ht.2 i)
  refine h.trans ?_
  have hvol : volume (Set.univ.pi fun _ : Fin K => Jw) ≤ ENNReal.ofReal (δ ^ K) := by
    rw [volume_pi_pi, ENNReal.ofReal_pow hδ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    calc volume Jw ≤ volume (Set.Ico a (a + δ)) := measure_mono hJ
      _ = ENNReal.ofReal δ := by rw [Real.volume_Ico]; congr 1; ring
  have hcp : 0 < ∏ i, cv i := Finset.prod_pos fun i _ => hcv i
  have htp : 0 < ∏ j, τ' j ^ ((∑ i, E' i j) - 1) :=
    Finset.prod_pos fun j _ => pow_pos (by linarith [hτ' j]) _
  have hX : (∏ i, cv i) * ∏ j, τ' j ^ ((∑ i, E' i j) - 1) ≤
      |(Ereal E').det| * (∏ i, cv i) * ∏ j, τ' j ^ ((∑ i, E' i j) - 1) := by
    have := one_le_abs_det hE
    nlinarith [mul_pos hcp htp]
  calc volume (Set.univ.pi fun _ : Fin K => Jw) /
        ENNReal.ofReal (|(Ereal E').det| * (∏ i, cv i) * ∏ j, τ' j ^ ((∑ i, E' i j) - 1))
      ≤ ENNReal.ofReal (δ ^ K) /
        ENNReal.ofReal ((∏ i, cv i) * ∏ j, τ' j ^ ((∑ i, E' i j) - 1)) :=
        ENNReal.div_le_div hvol (ENNReal.ofReal_le_ofReal hX)
    _ = ENNReal.ofReal (δ ^ K / ((∏ i, cv i) * ∏ j, τ' j ^ ((∑ i, E' i j) - 1))) :=
        (ENNReal.ofReal_div_of_pos (mul_pos hcp htp)).symm
    _ = _ := by
        congr 1
        have hinv : (∏ j, τ' j ^ ((∑ i, E' i j) - 1))⁻¹ =
            ∏ j, (τ' j)⁻¹ ^ ((∑ i, E' i j) - 1) := by
          rw [← Finset.prod_inv_distrib]; simp [inv_pow]
        rw [div_eq_mul_inv, mul_inv, hinv, Finset.prod_inv_distrib]
        ring

/-- **The integral of `PsiBar`** (the pivot integrals of one run, then the end step (S3)(c)):
`∫ PsiBar(ω, t) dt ≤ δ^K W A^K` for every `ω`, given the sure top bound (S3)(d). -/
theorem lintegral_psiBar_le {K : ℕ} (J : JitterLaw Ω P θ) (G : ℕ → Set Ω) {τ' : Fin K → ℝ}
    (hτ' : ∀ j, 1 ≤ τ' j) {E' : Matrix (Fin K) (Fin K) ℕ} (hE : (Ereal E').det ≠ 0)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ))
    (hδ : 0 ≤ δ) (D Dmax X₀ smax : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → tailSum Dmax X₀ *
      ∏ n ∈ univ.filter (fun n : Fin N => ω ∈ J.A n ∧ (n : ℕ) < u), (1 - (J.q n ω)⁻¹)⁻¹ ≤ A)
    (ω : Ω) :
    ∫⁻ t, PsiBar (N := N) J G τ' E' Jw D Dmax X₀ smax ω () t ≤
      ENNReal.ofReal (δ ^ K * (∏ j, (τ' j)⁻¹ ^ ((∑ i, E' i j) - 1)) * A ^ K) := by
  set W := ∏ j, (τ' j)⁻¹ ^ ((∑ i, E' i j) - 1) with hW
  have hW0 : 0 ≤ W := Finset.prod_nonneg fun j _ =>
    pow_nonneg (inv_nonneg.mpr (by linarith [hτ' j])) _
  set y : (Fin K → (Fin N → ℕ) × ℕ) → ℝ := fun c =>
    if DecOK (fun n => ω ∈ J.A n) c ∧ uOf c ≤ smax ∧ ω ∈ G (uOf c) then
      δ ^ K * W * ∏ i, (cval (fun n => J.q n ω) (c i))⁻¹ else 0 with hy
  have hterm : ∀ c ∈ contents K N D Dmax X₀,
      ∫⁻ t, (if uOf c ≤ smax then (decSet J c ∩ G (uOf c)).indicator (1 : Ω → ℝ≥0∞) ω *
        (boxSet τ' E' Jw fun i => cval (fun n => J.q n ω) (c i)).indicator 1 t else 0) ≤
        ENNReal.ofReal (y c) := by
    intro c hc
    by_cases h : DecOK (fun n => ω ∈ J.A n) c ∧ uOf c ≤ smax ∧ ω ∈ G (uOf c)
    · have hmem : ω ∈ decSet J c ∩ G (uOf c) := ⟨h.1, h.2.2⟩
      simp only [if_pos h.2.1, Set.indicator_of_mem hmem, Pi.one_apply, one_mul, hy,
        if_pos h]
      rw [lintegral_indicator_one (measurableSet_boxSet τ' E' hJw _)]
      refine volume_boxSet_le hτ' hE hJw hJ hδ fun i => ?_
      exact cval_pos (Fintype.mem_piFinset.mp hc i) fun n hn =>
        by linarith [hq ω n (h.1 i n hn)]
    · have h0 : ∀ t, (if uOf c ≤ smax then (decSet J c ∩ G (uOf c)).indicator
          (1 : Ω → ℝ≥0∞) ω * (boxSet τ' E' Jw fun i => cval (fun n => J.q n ω) (c i)).indicator
            1 t else 0) = 0 := by
        intro t
        split_ifs with hs
        · have : ω ∉ decSet J c ∩ G (uOf c) := fun hm => h ⟨hm.1, hs, hm.2⟩
          rw [Set.indicator_of_notMem this, zero_mul]
        · rfl
      simp only [h0, lintegral_zero]
      exact zero_le _
  have hmeas : ∀ c ∈ contents K N D Dmax X₀, AEMeasurable (fun t =>
      (if uOf c ≤ smax then (decSet J c ∩ G (uOf c)).indicator (1 : Ω → ℝ≥0∞) ω *
        (boxSet τ' E' Jw fun i => cval (fun n => J.q n ω) (c i)).indicator 1 t else 0)) := by
    intro c _
    split_ifs
    · exact (measurable_const.mul
        (measurable_one.indicator (measurableSet_boxSet τ' E' hJw _))).aemeasurable
    · exact aemeasurable_const
  unfold PsiBar
  rw [lintegral_finset_sum' _ hmeas]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hy0 : ∀ c ∈ contents K N D Dmax X₀, 0 ≤ y c := by
    intro c hc
    simp only [hy]
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (pow_nonneg hδ _) hW0)
        (prod_inv_cval_nonneg (ok := fun n => ω ∈ J.A n) (fun n hn => hq ω n hn) hc h.1)
    · exact le_rfl
  rw [← ENNReal.ofReal_sum_of_nonneg hy0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum : ∑ c ∈ contents K N D Dmax X₀, y c = δ ^ K * W *
      ∑ c ∈ contents K N D Dmax X₀, (if DecOK (fun n => ω ∈ J.A n) c ∧ uOf c ≤ smax ∧
        ω ∈ G (uOf c) then ∏ i, (cval (fun n => J.q n ω) (c i))⁻¹ else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hy]
    split_ifs <;> simp
  rw [hsum, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ _)
  refine mul_le_mul_of_nonneg_left ?_ hW0
  exact euler_oneRun (fun n => ω ∈ J.A n) (fun n hn => hq ω n hn) D Dmax X₀ smax
    (fun u => ω ∈ G u) hA (fun u hu hG => hS3 ω u hu hG)

/-! ## The realised count as a labelled pivot sum -/

/-- The decided slots of the jitter process. -/
noncomputable def decOf (J : JitterLaw Ω P θ) (ω : Ω) : Finset (Fin N) :=
  univ.filter fun n => ω ∈ J.A n

/-- The prime values of the jitter process. -/
noncomputable def qOf (J : JitterLaw Ω P θ) (ω : Ω) : Fin N → ℝ := fun n => J.q n ω

/-- The pattern with the pivot columns latest first (the order of the labels in `Zs`). -/
def revPat {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) : Matrix (Fin K) (Fin K) ℕ :=
  fun i j => E i (Fin.rev j)

/-- The caps latest first. -/
def revCap {K : ℕ} (τ : Fin K → ℝ) : Fin K → ℝ := fun j => τ (Fin.rev j)

lemma elemVal_ge {q : Fin N → ℝ} {x : (Fin N → ℕ) × ℕ} (hd : 1 ≤ x.2)
    (hq : ∀ n, x.1 n ≠ 0 → 1 ≤ q n) {n : Fin N} (hn : x.1 n ≠ 0) : q n ≤ elemVal q x := by
  unfold elemVal
  have h1 : ∀ m ∈ univ, 1 ≤ q m ^ x.1 m := fun m _ => by
    by_cases h : x.1 m = 0
    · simp [h]
    · exact one_le_pow₀ (hq m h)
  have h2 : q n ^ x.1 n ≤ ∏ m, q m ^ x.1 m := by
    have := Finset.prod_le_prod (s := univ) (f := fun m => if m = n then q n ^ x.1 n else 1)
      (g := fun m => q m ^ x.1 m) (fun m _ => by
        dsimp only
        split_ifs with h
        · exact le_trans zero_le_one (h ▸ h1 m (mem_univ _))
        · exact zero_le_one) (fun m hm => by
        dsimp only
        split_ifs with h
        · rw [h]
        · exact h1 m hm)
    simpa using this
  have h3 : q n ≤ q n ^ x.1 n := by
    calc q n = q n ^ 1 := (pow_one _).symm
      _ ≤ q n ^ x.1 n := pow_le_pow_right₀ (hq n hn) (Nat.one_le_iff_ne_zero.mpr hn)
  have h4 : (1 : ℝ) ≤ x.2 := by exact_mod_cast hd
  have h5 : 0 ≤ ∏ m, q m ^ x.1 m := le_trans zero_le_one (le_trans (h1 n (mem_univ _)) h2)
  nlinarith

/-- **The realised count of one-run skeleton tuples is dominated by the labelled pivot sum** of
Lemma A.5 (pathwise, on `G_{<s_max}`). -/
theorem skelCount_le_Zs {k : ℕ} (J : JitterLaw Ω P θ) (G : ℕ → Set Ω)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (τ : Fin (k + 1) → ℝ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin (k + 1),
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (ω : Ω) (hω : ω ∈ G smax) :
    skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E [k + 1] ≤
      J.Zs (k + 1) N (PsiOne (N := N) J G (revCap τ) (revPat E) Jw D Dmax X₀ smax) ω () := by
  set S := windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw with hS
  set T := (rankTuples (k + 1) S).filter fun t => skel t = (E, [k + 1]) with hT
  set gN : (Fin (k + 1) → Fin N → ℕ) → Fin (k + 1) → ℕ := fun t =>
    if h : (pivs t).card = k + 1 then fun i => (pivSlot t h (Fin.rev i) : ℕ) else 0 with hgN
  set gC : (Fin (k + 1) → Fin N → ℕ) → Fin (k + 1) → (Fin N → ℕ) × ℕ := fun t i =>
    (fun n => if n ∈ pivSet t then 0 else t i n,
      tailOf (decOf J ω) (qOf J ω) X₀ D Dmax Jw (t i)) with hgC
  set F : (Fin (k + 1) → ℕ) × (Fin (k + 1) → (Fin N → ℕ) × ℕ) → ℝ≥0∞ := fun y =>
    (if ChainOK N y.1 then ∏ i, (J.A (y.1 i)).indicator (1 : Ω → ℝ≥0∞) ω else 0) *
      (if uOf y.2 ≤ lastOf N y.1 ∧ lastOf N y.1 ≤ smax then
        (decSet J y.2 ∩ G (lastOf N y.1)).indicator 1 ω *
          (boxSet (revCap τ) (revPat E) Jw fun i => cvalLt J (lastOf N y.1) ω (y.2 i)).indicator
            1 (fun i => J.q (y.1 i) ω) else 0) with hF
  -- the facts about a tuple of `T`
  have hfacts : ∀ t ∈ T, ∃ hk : (pivs t).card = k + 1, (∀ i, t i ∈ S) ∧
      pattern t = E ∧ runList t = [k + 1] ∧ LinearIndependent ℚ (fun i => Covers.vq (t i)) := by
    intro t ht
    obtain ⟨ht1, hskel⟩ := Finset.mem_filter.mp ht
    obtain ⟨htS, -, hli⟩ := Finset.mem_filter.mp ht1
    have hk := card_pivs hli
    obtain ⟨h1, h2⟩ := Prod.mk.inj hskel
    exact ⟨hk, Fintype.mem_piFinset.mp htS, h1, h2, hli⟩
  -- the content lies in `contents`
  have hmemC : ∀ t ∈ T, gC t ∈ contents (k + 1) N D Dmax X₀ := by
    intro t ht
    obtain ⟨hk, hS', -, -, -⟩ := hfacts t ht
    rw [contents, Fintype.mem_piFinset]
    intro i
    have hel := tailOf_mem (hS' i)
    obtain ⟨hel1, -⟩ := Finset.mem_filter.mp hel
    obtain ⟨hv, hd⟩ := Finset.mem_product.mp hel1
    refine Finset.mem_product.mpr ⟨?_, hd⟩
    rw [Fintype.mem_piFinset] at hv ⊢
    intro n
    have := hv n
    simp only [hgC, Finset.mem_range] at this ⊢
    split_ifs
    · omega
    · exact this
  -- the value of `gN` and the last label
  have hgN : ∀ t (hk : (pivs t).card = k + 1), gN t = fun i => (pivSlot t hk (Fin.rev i) : ℕ) :=
    fun t hk => by simp only [hgN, dif_pos hk]
  have hlast : ∀ t (hk : (pivs t).card = k + 1), lastOf N (gN t) = (pivSlot t hk 0 : ℕ) := by
    intro t hk
    rw [hgN t hk]
    simp only [lastOf, dif_pos (Nat.succ_pos k)]
    congr 2
    exact Fin.ext (by simp)
  -- every term of a tuple of `T` is `1`
  have hF1 : ∀ t ∈ T, F (gN t, gC t) = 1 := by
    intro t ht
    obtain ⟨hk, hS', hpat, hrun, -⟩ := hfacts t ht
    set p := pivSlot t hk with hp
    have hpm := pivSlot_strictMono t hk
    -- pivots are decided
    have hpdec : ∀ j, ω ∈ J.A (p j) := by
      intro j
      obtain ⟨i, hi⟩ := pivSlot_mem_colSupp t hk j
      have := windowVecs_supp (hS' i) (p j) hi
      exact (Finset.mem_filter.mp this).2
    -- the free slots
    have hfree : ∀ i n, (gC t i).1 n ≠ 0 → t i n ≠ 0 ∧ n ∉ pivSet t := by
      intro i n hn
      simp only [hgC] at hn
      split_ifs at hn with h
      · exact absurd rfl hn
      · exact ⟨hn, h⟩
    have hu : uOf (gC t) ≤ (p 0 : ℕ) := by
      rw [uOf_le_iff]
      intro i n hn
      obtain ⟨h1, h2⟩ := hfree i n hn
      have := free_lt_pivSlot hk hrun ⟨i, h1⟩
        (fun j hj => h2 ((mem_pivSet t hk n).mpr ⟨j, hj⟩)) 0
      exact this
    -- the earliest pivot is before `s_max`
    have hps : (p 0 : ℕ) ≤ smax := by
      obtain ⟨i, hi⟩ := pivSlot_mem_colSupp t hk 0
      have hel := tailOf_mem (hS' i)
      obtain ⟨hel1, hsupp, -, hval⟩ := Finset.mem_filter.mp hel
      refine hsmax ω (p 0) (hpdec 0) _ hval ?_
      refine elemVal_ge (q := qOf J ω)
        (x := (t i, tailOf (decOf J ω) (qOf J ω) X₀ D Dmax Jw (t i))) ?_ (fun n hn => ?_) hi
      · exact smooth_pos (Finset.mem_product.mp hel1).2
      · exact (hq ω n (Finset.mem_filter.mp (hsupp n hn)).2).le
    simp only [hF]
    rw [hlast t hk]
    -- the label factor
    have hchain : ChainOK N (gN t) := by
      rw [hgN t hk]
      refine ⟨fun a b hab => ?_, fun i => (pivSlot t hk _).isLt⟩
      have := hpm (Fin.rev_lt_rev.mpr hab)
      exact this
    have hprod : ∏ i, (J.A (gN t i)).indicator (1 : Ω → ℝ≥0∞) ω = 1 := by
      rw [hgN t hk]
      exact Finset.prod_eq_one fun i _ => by
        rw [Set.indicator_of_mem (hpdec _)]; rfl
    rw [if_pos hchain, hprod, one_mul, if_pos ⟨hu, hps⟩]
    have hdec : ω ∈ decSet J (gC t) ∩ G (p 0 : ℕ) := by
      refine ⟨fun i n hn => ?_, hG _ _ hps hω⟩
      obtain ⟨h1, -⟩ := hfree i n hn
      exact (Finset.mem_filter.mp (windowVecs_supp (hS' i) n h1)).2
    rw [Set.indicator_of_mem hdec, Pi.one_apply, one_mul]
    -- the box
    have hbox : (fun i => J.q (gN t i) ω) ∈
        boxSet (revCap τ) (revPat E) Jw fun i => cvalLt J (p 0 : ℕ) ω (gC t i) := by
      rw [hgN t hk]
      refine ⟨fun j => ?_, fun i => ?_⟩
      · -- the caps
        simp only [revCap]
        refine hτ ω _ (hpdec _) _ ?_
        have hsub : (Finset.Iio (Fin.rev j)).image p ⊆ (decOf J ω).filter (· < p (Fin.rev j)) := by
          intro n hn
          obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpdec j'⟩,
            hpm (Finset.mem_Iio.mp hj')⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ hpm.injective, Fin.card_Iio] at this
        exact this
      · -- the window
        have hel := tailOf_mem (hS' i)
        have hval := (Finset.mem_filter.mp hel).2.2.2
        convert hval using 1
        unfold nmap elemVal
        dsimp only
        rw [cvalLt_eq hu i]
        unfold cval
        simp only [revPat, hgC]
        rw [prod_split t hk (qOf J ω) (t i)]
        have hre : ∏ j, J.q (pivSlot t hk (Fin.rev j) : ℕ) ω ^ E i (Fin.rev j) =
            ∏ j, J.q (pivSlot t hk j : ℕ) ω ^ t i (pivSlot t hk j) := by
          rw [← Fintype.prod_equiv Fin.revPerm (fun j => J.q (pivSlot t hk j : ℕ) ω ^
            E i j) _ (fun j => by simp [Fin.revPerm])]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← hpat, pattern_eq t hk]
        rw [hre]
        simp only [qOf]
        ring
    rw [Set.indicator_of_mem hbox, Pi.one_apply]
  -- injectivity
  have hinj : Set.InjOn (fun t => (gN t, gC t)) T := by
    intro t ht t' ht' h
    obtain ⟨hk, -, hpat, -, -⟩ := hfacts t ht
    obtain ⟨hk', -, hpat', -, -⟩ := hfacts t' ht'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hpp : ∀ j, pivSlot t hk j = pivSlot t' hk' j := by
      intro j
      have := congrFun h1 (Fin.rev j)
      rw [hgN t hk, hgN t' hk'] at this
      simp only [Fin.rev_rev] at this
      exact Fin.ext this
    have hset : pivSet t = pivSet t' := by
      rw [pivSet_eq_image t hk, pivSet_eq_image t' hk']
      congr 1; funext j; exact hpp j
    funext i n
    by_cases hn : n ∈ pivSet t
    · obtain ⟨j, rfl⟩ := (mem_pivSet t hk n).mp hn
      rw [← pattern_eq t hk, hpat, hpp j, ← pattern_eq t' hk', hpat']
    · have := congrArg Prod.fst (congrFun h2 i)
      have := congrFun this n
      simp only [hgC, if_neg hn, ← hset] at this
      exact this
  -- the sum
  have hcount : skelCount S E [k + 1] = ∑ t ∈ T, (1 : ℝ≥0∞) := by
    simp [skelCount, hT]
  rw [hcount, J.Zs_eq]
  calc ∑ t ∈ T, (1 : ℝ≥0∞) = ∑ t ∈ T, F (gN t, gC t) :=
        Finset.sum_congr rfl fun t ht => (hF1 t ht).symm
    _ = ∑ y ∈ T.image fun t => (gN t, gC t), F y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ T.image gN ×ˢ contents (k + 1) N D Dmax X₀, F y := by
        refine Finset.sum_le_sum_of_subset fun y hy => ?_
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, hmemC t ht⟩
    _ = ∑ ns ∈ T.image gN, ∑ c ∈ contents (k + 1) N D Dmax X₀, F (ns, c) :=
        Finset.sum_product _ _ _
    _ ≤ ∑' ns, ∑ c ∈ contents (k + 1) N D Dmax X₀, F (ns, c) := ENNReal.sum_le_tsum _
    _ = _ := by
        refine tsum_congr fun ns => ?_
        simp only [hF, PsiOne]
        split_ifs with h
        · rw [Finset.mul_sum]
        · simp

/-! ## `SkeletonBound` for one run -/

/-- For one run, `Fin = G_1(Eu) + Eu^k = A^k`. -/
lemma finG_single {A Eu : ℝ} (hEuA : Eu ≤ A) (k : ℕ) : finG A [k + 1] Eu = A ^ (k + 1) := by
  simp only [finG, GRun, List.sum_nil, add_zero, mul_one]
  split_ifs with h
  · have hint : ∫ x in Eu..A, ((k + 1 : ℕ) : ℝ) * x ^ (((k + 1 : ℕ) : ℤ) - 1) =
        A ^ (k + 1) - Eu ^ (k + 1) := by
      have : ∀ x : ℝ, ((k + 1 : ℕ) : ℝ) * x ^ (((k + 1 : ℕ) : ℤ) - 1) =
          ((k + 1 : ℕ) : ℝ) * x ^ k := by
        intro x
        rw [show (((k + 1 : ℕ) : ℤ) - 1) = ((k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      field_simp
    rw [hint]; ring
  · have : Eu = A := le_antisymm hEuA (not_lt.mp h)
    rw [this]; ring

lemma ereal_revPat_det {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} (hE : E ∈ InvPattern K) :
    (Ereal (revPat E)).det ≠ 0 := by
  have h1 : Ereal (revPat E) = (Ereal E).submatrix id Fin.revPerm := by
    ext i j; simp [Ereal, revPat, Fin.revPerm]
  rw [h1, Matrix.det_permute']
  have h2 : (Ereal E).det = (((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) : ℝ) := by
    have := RingHom.map_det (Rat.castHom ℝ) (E.map (Nat.cast : ℕ → ℚ))
    change (((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) : ℝ) = _ at this
    rw [this]
    congr 1
  rw [h2]
  have : ((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) ≠ 0 := hE
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  exact_mod_cast this

lemma weight_revPat {K : ℕ} (τ : Fin K → ℝ) (E : Matrix (Fin K) (Fin K) ℕ) :
    ∏ j, (revCap τ j)⁻¹ ^ ((∑ i, revPat E i j) - 1) = patternWeight τ E := by
  unfold patternWeight revCap revPat
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => by simp [Fin.revPerm])

/-- **`SkeletonBound` for the one-run skeletons** (Lemma A.5 + Theorem A.10 with `C = B'`, the
case `T = 1`): for every invertible pattern `E`,
`E[X_{(E,[k])}; Good] ≤ θ^k δ^k ∏_j τ_j^{-(s_j - 1)} Fin(A, [k], Eu)` in the window model over a
jitter process, under:
* the model hypotheses: prime values `> 1` (`hq`), a prime value below a point of the window is
  decided before `s_max` (`hsmax`), and the caps `τ_j ≤ q` for a prime with at least `j` decided
  slots before it (`hτ`);
* nested adapted good events `G` with `Good ⊆ G_{<s_max}`;
* the sure top bound (S3)(d), `R_D ∏_{decided n < u} (1 - 1/q_n)^{-1} ≤ A` on `G_{<u}`,
  `u ≤ s_max`. -/
theorem skeletonBound_oneRun {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) {k : ℕ}
    (τ : Fin (k + 1) → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) (D Dmax X₀ : ℕ) {A Eu : ℝ}
    (hA : 0 ≤ A) (hEuA : Eu ≤ A)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin (k + 1),
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → tailSum Dmax X₀ *
      ∏ n ∈ univ.filter (fun n : Fin N => ω ∈ J.A n ∧ (n : ℕ) < u), (1 - (J.q n ω)⁻¹)⁻¹ ≤ A)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ) (hE : E ∈ InvPattern (k + 1)) :
    ∫⁻ ω in Good, skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E [k + 1]
      ∂P ≤ ENNReal.ofReal (θ ^ (k + 1) * δ ^ (k + 1) * patternWeight τ E * finG A [k + 1] Eu) := by
  set Ψ := PsiOne (N := N) J G (revCap τ) (revPat E) Jw D Dmax X₀ smax with hΨ
  set Ψb := PsiBar (N := N) J G (revCap τ) (revPat E) Jw D Dmax X₀ smax with hΨb
  have hτ' : ∀ j, 1 ≤ revCap τ j := fun j => hτ1 _
  have hdet := ereal_revPat_det hE
  -- pathwise: the realised count is at most the labelled pivot sum
  have h1 : ∫⁻ ω in Good, skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      E [k + 1] ∂P ≤ ∫⁻ ω, J.Zs (k + 1) N Ψ ω () ∂P := by
    refine le_trans ?_ (setLIntegral_le_lintegral Good _)
    refine setLIntegral_mono' hGood fun ω hω => ?_
    exact skelCount_le_Zs J G hG τ E Jw D Dmax X₀ smax hq hsmax hτ ω (hGoodG hω)
  -- Lemma A.5 for one run
  have h2 := J.iterated_pivots k (Par := Unit) N Ψ
    (fun m => psiOne_jmeas J hGm (revCap τ) (revPat E) hJw D Dmax X₀ smax m) Ψb
    (psiBar_meas J hGm (revCap τ) (revPat E) hJw D Dmax X₀ smax)
    (fun m ω p t => psiOne_le_psiBar J hG (revCap τ) (revPat E) Jw D Dmax X₀ smax m ω p t) ()
  -- the integrals over the pivots, then the end step
  have h3 : ∫⁻ ω, (∫⁻ t, Ψb ω () t) ∂P ≤ ENNReal.ofReal (δ ^ (k + 1) *
      (∏ j, (revCap τ j)⁻¹ ^ ((∑ i, revPat E i j) - 1)) * A ^ (k + 1)) := by
    calc ∫⁻ ω, (∫⁻ t, Ψb ω () t) ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (δ ^ (k + 1) *
          (∏ j, (revCap τ j)⁻¹ ^ ((∑ i, revPat E i j) - 1)) * A ^ (k + 1)) ∂P :=
          lintegral_mono fun ω => lintegral_psiBar_le J G hτ' hdet hJw hJ hδ D Dmax X₀ smax hA
            hq hS3 ω
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  rw [weight_revPat] at h3
  have hW0 : 0 ≤ patternWeight τ E := Finset.prod_nonneg fun j _ =>
    pow_nonneg (inv_nonneg.mpr (by linarith [hτ1 j])) _
  calc _ ≤ ∫⁻ ω, J.Zs (k + 1) N Ψ ω () ∂P := h1
    _ ≤ θE ^ (k + 1) * ∫⁻ ω, (∫⁻ t, Ψb ω () t) ∂P := h2
    _ ≤ ENNReal.ofReal θ ^ (k + 1) *
          ENNReal.ofReal (δ ^ (k + 1) * patternWeight τ E * A ^ (k + 1)) := by
        gcongr
    _ = ENNReal.ofReal (θ ^ (k + 1) * δ ^ (k + 1) * patternWeight τ E * finG A [k + 1] Eu) := by
        rw [← ENNReal.ofReal_pow hθ0, ← ENNReal.ofReal_mul (pow_nonneg hθ0 _), finG_single hEuA]
        congr 1; ring

end RankFull.Config
