import DGPS.Lipschitz.KernelDiagonal

/-!
# Centered U-statistic value moments (LIP013)

For a bounded, centered, symmetric kernel `F` on a probability space, the off-diagonal part
`N⁻¹ ∑_{i<j} F(Xᵢ,Xⱼ)` of the U-statistic `(2N)⁻¹ ∑_{i,j} F(Xᵢ,Xⱼ)` has `L^{2k}` norm at most
`(2k)² ‖F‖∞`, and the diagonal part is bounded by `‖F(x,x)‖∞ / 2`. Applied to `F = K - K_R` this
gives `sup_N ‖U_N^K - U_N^{K_R}‖_{L^q} → 0` as `R → ∞`.
-/

open MeasureTheory

namespace DGPS.Lipschitz.CenteredKernelMoments

universe u
variable {α : Type u} [MeasurableSpace α]

theorem measurable_prod_edges {F : α → α → ℝ} (hFm : Measurable (Function.uncurry F))
    {N n : ℕ} (a b : Fin n → Fin N) :
    Measurable (fun x : Fin N → α => ∏ e, F (x (a e)) (x (b e))) :=
  Finset.measurable_prod _ fun e _ => by
    have h2 : Measurable fun x : Fin N → α => (x (a e), x (b e)) :=
      (measurable_pi_apply (a e)).prodMk (measurable_pi_apply (b e))
    exact hFm.comp h2

omit [MeasurableSpace α] in
theorem abs_prod_edges_le {F : α → α → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    {N n : ℕ} (a b : Fin n → Fin N) (x : Fin N → α) :
    |∏ e, F (x (a e)) (x (b e))| ≤ M ^ n := by
  rw [Finset.abs_prod]
  calc ∏ e, |F (x (a e)) (x (b e))| ≤ ∏ _e : Fin n, M :=
        by gcongr with e he; exact hM _ _
    _ = M ^ n := by simp

theorem integrable_prod_edges {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    {N n : ℕ} (a b : Fin n → Fin N) :
    Integrable (fun x : Fin N → α => ∏ e, F (x (a e)) (x (b e))) (Measure.pi fun _ => μ) :=
  Integrable.of_bound (measurable_prod_edges hFm a b).aestronglyMeasurable (M ^ n)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_prod_edges_le hM a b x)

theorem integral_prod_edges_eq_zero_core {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    (hc : ∀ y, ∫ x, F x y ∂μ = 0) {N' n : ℕ} (a b : Fin n → Fin (N' + 1))
    (v : Fin (N' + 1)) (e0 : Fin n) (hv : a e0 = v)
    (hother : ∀ e, e ≠ e0 → a e ≠ v ∧ b e ≠ v) (hb0 : b e0 ≠ v) :
    ∫ x : Fin (N' + 1) → α, ∏ e, F (x (a e)) (x (b e)) ∂(Measure.pi fun _ => μ) = 0 := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N' + 1) => μ) v
  have hmp' := hmp.symm
  have hint := integrable_prod_edges hFm hM a b (μ := μ)
  have h1 := (hmp'.integral_comp' (g := fun x : Fin (N' + 1) → α => ∏ e, F (x (a e)) (x (b e)))).symm
  rw [h1]
  have hint2 := (hmp'.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
  refine (integral_prod_symm _ hint2).trans ?_
  have hnonempty : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ)
    simp [Set.univ_eq_empty_iff.mpr h] at this
  obtain ⟨x0⟩ := hnonempty
  refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans (integral_zero _ _)
  show ∫ x, ∏ e, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N' + 1) => α) v).symm (x, y) (a e))
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N' + 1) => α) v).symm (x, y) (b e)) ∂μ = 0
  have hsymm : ∀ x, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N' + 1) => α) v).symm (x, y)
      = Fin.insertNth (α := fun _ => α) v x y := fun x => rfl
  simp only [hsymm]
  have hind : ∀ (l : Fin (N' + 1)), l ≠ v → ∀ x, Fin.insertNth (α := fun _ => α) v x y l = Fin.insertNth (α := fun _ => α) v x0 y l := by
    intro l hl x
    obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hl
    simp [Fin.insertNth_apply_succAbove]
  have hrew : ∀ x, ∏ e, F (Fin.insertNth (α := fun _ => α) v x y (a e)) (Fin.insertNth (α := fun _ => α) v x y (b e)) =
      F x (Fin.insertNth (α := fun _ => α) v x0 y (b e0)) *
        ∏ e ∈ Finset.univ.erase e0, F (Fin.insertNth (α := fun _ => α) v x0 y (a e)) (Fin.insertNth (α := fun _ => α) v x0 y (b e)) := by
    intro x
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e0)]
    congr 1
    · rw [hv, Fin.insertNth_apply_same, hind _ hb0 x]
    · refine Finset.prod_congr rfl fun e he => ?_
      have := hother e (Finset.ne_of_mem_erase he)
      rw [hind _ this.1 x, hind _ this.2 x]
  simp only [hrew]
  rw [integral_mul_const, hc, zero_mul]


theorem integral_prod_edges_eq_zero {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    (hsym : ∀ x y, F x y = F y x)
    (hc : ∀ y, ∫ x, F x y ∂μ = 0) {N n : ℕ} (a b : Fin n → Fin N)
    (v : Fin N) (e0 : Fin n) (hv : a e0 = v ∨ b e0 = v) (hab : a e0 ≠ b e0)
    (hother : ∀ e, e ≠ e0 → a e ≠ v ∧ b e ≠ v) :
    ∫ x : Fin N → α, ∏ e, F (x (a e)) (x (b e)) ∂(Measure.pi fun _ => μ) = 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := v.pos; omega⟩
  rcases hv with hv | hv
  · exact integral_prod_edges_eq_zero_core hFm hM hc a b v e0 hv hother
      (fun h => hab (hv.trans h.symm))
  · classical
    have key := integral_prod_edges_eq_zero_core hFm hM hc (Function.update a e0 (b e0))
      (Function.update b e0 (a e0)) v e0 (by simpa using hv)
      (fun e he => by simpa [Function.update_of_ne he] using hother e he)
      (by simpa using fun h => hab (h.trans hv.symm))
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) key
    refine Finset.prod_congr rfl fun e _ => ?_
    by_cases he : e = e0
    · subst he; simp [hsym]
    · simp [Function.update_of_ne he]

open Classical

/-- Pairs `i < j`. -/
noncomputable def edgeSet (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Labels of the `2n` slots (both endpoints of each of `n` edges). -/
def slotLabel {N n : ℕ} (q : Fin n → Fin N × Fin N) : Fin n × Bool → Fin N :=
  fun s => if s.2 then (q s.1).2 else (q s.1).1

/-- Every occurring label occurs at least twice. -/
def Good {N n : ℕ} (f : Fin n × Bool → Fin N) : Prop :=
  ∀ v, (∃ s, f s = v) → 2 ≤ (Finset.univ.filter fun s => f s = v).card

theorem integral_eq_zero_of_not_good {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    (hsym : ∀ x y, F x y = F y x)
    (hc : ∀ y, ∫ x, F x y ∂μ = 0) {N n : ℕ} (q : Fin n → Fin N × Fin N)
    (hq : ∀ t, (q t).1 < (q t).2) (hg : ¬ Good (slotLabel q)) :
    ∫ x : Fin N → α, ∏ t, F (x (q t).1) (x (q t).2) ∂(Measure.pi fun _ => μ) = 0 := by
  unfold Good at hg
  push Not at hg
  obtain ⟨v, ⟨s0, hs0⟩, hlt⟩ := hg
  have hpos : 0 < (Finset.univ.filter fun s => slotLabel q s = v).card :=
    Finset.card_pos.2 ⟨s0, by simp [hs0]⟩
  obtain ⟨s1, hs1⟩ := Finset.card_eq_one.1 (by omega : (Finset.univ.filter fun s => slotLabel q s = v).card = 1)
  have huniq : ∀ s, slotLabel q s = v → s = s1 := fun s hs => by
    have : s ∈ Finset.univ.filter fun s => slotLabel q s = v := by simp [hs]
    rw [hs1] at this; simpa using this
  have hs1v : slotLabel q s1 = v := by
    have : s1 ∈ Finset.univ.filter fun s => slotLabel q s = v := by rw [hs1]; simp
    simpa using this
  obtain ⟨e0, c⟩ := s1
  have hfalse : ∀ e, (q e).1 = v → e = e0 ∧ c = false := fun e he => by
    have := huniq (e, false) (by simpa [slotLabel] using he)
    simpa using this
  have htrue : ∀ e, (q e).2 = v → e = e0 ∧ c = true := fun e he => by
    have := huniq (e, true) (by simpa [slotLabel] using he)
    simpa using this
  refine integral_prod_edges_eq_zero hFm hM hsym hc (fun t => (q t).1) (fun t => (q t).2) v e0 ?_
    (ne_of_lt (hq e0)) ?_
  · cases c
    · left; simpa [slotLabel] using hs1v
    · right; simpa [slotLabel] using hs1v
  · intro e he
    refine ⟨fun h => he (hfalse e h).1, fun h => he (htrue e h).1⟩

theorem card_image_le_of_good {N n : ℕ} {f : Fin n × Bool → Fin N} (h : Good f) :
    (Finset.univ.image f).card ≤ n := by
  have h1 : (Finset.univ : Finset (Fin n × Bool)).card = n * 2 := by simp
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n × Bool)))
    (t := Finset.univ.image f) (f := f) (fun s _ => Finset.mem_image_of_mem f (Finset.mem_univ s))
  have h3 : ∑ v ∈ Finset.univ.image f, 2 ≤ ∑ v ∈ Finset.univ.image f,
      (Finset.filter (fun a => f a = v) Finset.univ).card :=
    Finset.sum_le_sum fun v hv => by
      obtain ⟨s, -, hs⟩ := Finset.mem_image.1 hv
      exact h v ⟨s, hs⟩
  simp only [Finset.sum_const, smul_eq_mul] at h3
  have : (Finset.univ.image f).card * 2 ≤ n * 2 := by
    rw [← h1, h2]; simpa [mul_comm] using h3
  omega

theorem exists_factor {N n : ℕ} (hN : 1 ≤ N) {f : Fin n × Bool → Fin N}
    (h : (Finset.univ.image f).card ≤ n) :
    ∃ (g : Fin n × Bool → Fin n) (h' : Fin n → Fin N), f = h' ∘ g := by
  set T := Finset.univ.image f with hT
  let e := T.equivFin
  refine ⟨fun s => Fin.castLE h (e ⟨f s, Finset.mem_image_of_mem f (Finset.mem_univ s)⟩),
    fun j => if hj : (j : ℕ) < T.card then (e.symm ⟨j, hj⟩ : Fin N) else ⟨0, hN⟩, ?_⟩
  funext s
  simp [Function.comp]

theorem card_good_le {N n : ℕ} (hN : 1 ≤ N) :
    (Finset.univ.filter fun f : Fin n × Bool → Fin N => Good f).card ≤ n ^ (n * 2) * N ^ n := by
  have hsub : (Finset.univ.filter fun f : Fin n × Bool → Fin N => Good f) ⊆
      (Finset.univ : Finset ((Fin n × Bool → Fin n) × (Fin n → Fin N))).image
        (fun p => p.2 ∘ p.1) := by
    intro f hf
    have hg : Good f := (Finset.mem_filter.1 hf).2
    obtain ⟨g, h', rfl⟩ := exists_factor hN (card_image_le_of_good hg)
    exact Finset.mem_image.2 ⟨(g, h'), Finset.mem_univ _, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_prod]


theorem slotLabel_injOn {N n : ℕ} :
    Set.InjOn (slotLabel (N := N) (n := n)) (Set.univ) := by
  intro q _ q' _ h
  funext t
  refine Prod.ext ?_ ?_
  · simpa [slotLabel] using congrFun h (t, false)
  · simpa [slotLabel] using congrFun h (t, true)

theorem integral_pow_offdiag_le {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) (hM0 : 0 ≤ M)
    (hsym : ∀ x y, F x y = F y x) (hc : ∀ y, ∫ x, F x y ∂μ = 0) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ∫ x : Fin N → α, (∑ p ∈ edgeSet N, F (x p.1) (x p.2)) ^ n ∂(Measure.pi fun _ => μ) ≤
      ((n : ℝ) ^ (n * 2) * (N : ℝ) ^ n) * M ^ n := by
  have hexp : ∀ x : Fin N → α, (∑ p ∈ edgeSet N, F (x p.1) (x p.2)) ^ n =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin n => edgeSet N), ∏ t, F (x (q t).1) (x (q t).2) := by
    intro x
    calc _ = ∏ _t : Fin n, ∑ p ∈ edgeSet N, F (x p.1) (x p.2) := by simp
      _ = _ := Finset.prod_univ_sum (fun _ => edgeSet N) (fun _ p => F (x p.1) (x p.2))
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun q _ =>
    integrable_prod_edges hFm hM (fun t => (q t).1) (fun t => (q t).2))]
  have hterm : ∀ q ∈ Fintype.piFinset (fun _ : Fin n => edgeSet N),
      ∫ x : Fin N → α, ∏ t, F (x (q t).1) (x (q t).2) ∂(Measure.pi fun _ => μ) ≤
        if Good (slotLabel q) then M ^ n else 0 := by
    intro q hq
    have hq' : ∀ t, (q t).1 < (q t).2 := fun t => by
      have := Fintype.mem_piFinset.1 hq t
      simpa [edgeSet] using this
    split_ifs with hg
    · calc _ ≤ ‖∫ x : Fin N → α, ∏ t, F (x (q t).1) (x (q t).2) ∂(Measure.pi fun _ => μ)‖ :=
            Real.le_norm_self _
        _ ≤ M ^ n * (Measure.pi fun _ : Fin N => μ).real Set.univ :=
            norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs]
              exact abs_prod_edges_le hM (fun t => (q t).1) (fun t => (q t).2) x)
        _ = M ^ n := by simp
    · exact (integral_eq_zero_of_not_good hFm hM hsym hc q hq' hg).le
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Fintype.piFinset (fun _ : Fin n => edgeSet N)).filter
      fun q => Good (slotLabel q)).card ≤ n ^ (n * 2) * N ^ n := by
    refine le_trans (Finset.card_le_card_of_injOn slotLabel ?_ (slotLabel_injOn.mono (Set.subset_univ _))) (card_good_le hN)
    intro q hq
    simpa using (Finset.mem_filter.1 hq).2
  have : (((Fintype.piFinset (fun _ : Fin n => edgeSet N)).filter
      fun q => Good (slotLabel q)).card : ℝ) ≤ (n : ℝ) ^ (n * 2) * (N : ℝ) ^ n := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right this (pow_nonneg hM0 n)


theorem sum_Ioi_eq_sum_edgeSet {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j = ∑ p ∈ edgeSet N, f p.1 p.2 := by
  unfold edgeSet
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp

theorem offdiag_eLpNorm_le {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    (hsym : ∀ x y, F x y = F y x) (hc : ∀ y, ∫ x, F x y ∂μ = 0) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    eLpNorm (fun x : Fin N → α =>
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, F (x i) (x j)) ((2 * k : ℕ) : ENNReal)
        (Measure.pi fun _ => μ) ≤ ENNReal.ofReal ((((2 * k : ℕ) : ℝ)) ^ 2 * M) := by
  have hnonempty : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ)
    simp [Set.univ_eq_empty_iff.mpr h] at this
  obtain ⟨x0⟩ := hnonempty
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0 x0)
  set n := 2 * k with hn
  have hn0 : n ≠ 0 := by omega
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  have hN : 1 ≤ N := hNpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hW : ∀ x : Fin N → α, ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, F (x i) (x j) =
      ∑ p ∈ edgeSet N, F (x p.1) (x p.2) := fun x =>
    sum_Ioi_eq_sum_edgeSet (fun i j => F (x i) (x j))
  simp only [hW]
  set W : (Fin N → α) → ℝ := fun x => ∑ p ∈ edgeSet N, F (x p.1) (x p.2) with hWdef
  have hWm : Measurable W :=
    Finset.measurable_sum _ fun p _ => by
      have h2 : Measurable fun x : Fin N → α => (x p.1, x p.2) :=
        (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
      exact hFm.comp h2
  have hWb : ∀ x, |W x| ≤ ((edgeSet N).card : ℝ) * M := fun x => by
    calc |W x| ≤ ∑ p ∈ edgeSet N, |F (x p.1) (x p.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ edgeSet N, M := Finset.sum_le_sum fun p _ => hM _ _
      _ = _ := by simp
  have hmem : MemLp (fun x => (N : ℝ)⁻¹ * W x) ((n : ℕ) : ENNReal) (Measure.pi fun _ : Fin N => μ) :=
    MemLp.of_bound ((measurable_const.mul hWm).aestronglyMeasurable)
      ((N : ℝ)⁻¹ * (((edgeSet N).card : ℝ) * M))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hNr)]
        exact mul_le_mul_of_nonneg_left (hWb x) (inv_pos.2 hNr).le)
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hn0) (by simp)]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_natCast]
  have hev : Even n := ⟨k, by omega⟩
  have hint : ∫ x, ‖(N : ℝ)⁻¹ * W x‖ ^ (n : ℝ) ∂(Measure.pi fun _ : Fin N => μ) =
      ((N : ℝ)⁻¹) ^ n * ∫ x, (W x) ^ n ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.rpow_natCast, Real.norm_eq_abs, hev.pow_abs, mul_pow]
  have hbd := integral_pow_offdiag_le hFm hM hM0 hsym hc hN n
  have hnn : 0 ≤ ∫ x, (W x) ^ n ∂(Measure.pi fun _ : Fin N => μ) :=
    integral_nonneg fun x => hev.pow_nonneg _
  have h1 : ∫ x, ‖(N : ℝ)⁻¹ * W x‖ ^ (n : ℝ) ∂(Measure.pi fun _ : Fin N => μ) ≤
      ((n : ℝ) ^ 2 * M) ^ n := by
    rw [hint]
    calc ((N : ℝ)⁻¹) ^ n * ∫ x, (W x) ^ n ∂(Measure.pi fun _ : Fin N => μ)
        ≤ ((N : ℝ)⁻¹) ^ n * (((n : ℝ) ^ (n * 2) * (N : ℝ) ^ n) * M ^ n) :=
          mul_le_mul_of_nonneg_left hbd (pow_nonneg (inv_pos.2 hNr).le n)
      _ = (((N : ℝ)⁻¹) ^ n * (N : ℝ) ^ n) * ((n : ℝ) ^ (n * 2) * M ^ n) := by ring
      _ = ((n : ℝ) ^ 2 * M) ^ n := by
          rw [← mul_pow, inv_mul_cancel₀ hNr.ne', one_pow, one_mul, mul_pow, ← pow_mul,
            mul_comm 2 n]
  have hnn2 : 0 ≤ ∫ x, ‖(N : ℝ)⁻¹ * W x‖ ^ (n : ℝ) ∂(Measure.pi fun _ : Fin N => μ) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ x, ‖(N : ℝ)⁻¹ * W x‖ ^ (n : ℝ) ∂(Measure.pi fun _ : Fin N => μ)) ^ ((n : ℝ)⁻¹)
      ≤ (((n : ℝ) ^ 2 * M) ^ n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow hnn2 h1 (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = (n : ℝ) ^ 2 * M := Real.pow_rpow_inv_natCast (by positivity) hn0


theorem sum_split {N : ℕ} (f : Fin N → Fin N → ℝ) (hs : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = 2 * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j + ∑ i, f i i := by
  have hpt : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) +
      (if j = i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.2 h.le, h.ne']
    · subst h; simp
    · simp [h, not_lt.2 h.le, h.ne]
  have h1 : ∀ i, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext j; simp
  calc ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0) +
        (if j = i then f i j else 0)) := Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hpt i j
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if j < i then f i j else 0) +
        ∑ i, ∑ j, (if j = i then f i j else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j + ∑ i, f i i := by
          have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs]
          rw [h2]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, h1]
          ring

theorem ustat_decomp {N : ℕ} (f : Fin N → Fin N → ℝ) (hs : ∀ i j, f i j = f j i) :
    ((2 : ℝ) * N)⁻¹ * ∑ i, ∑ j, f i j = (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j +
      ((2 : ℝ) * N)⁻¹ * ∑ i, f i i := by
  rw [sum_split f hs, mul_inv]
  ring

omit [MeasurableSpace α] in
theorem diag_abs_le [Nonempty α] {F : α → α → ℝ} {Md : ℝ} (hd : ∀ a, |F a a| ≤ Md) {N : ℕ}
    (x : Fin N → α) :
    |((2 : ℝ) * N)⁻¹ * ∑ i, F (x i) (x i)| ≤ Md / 2 := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hM0 : 0 ≤ Md := (abs_nonneg _).trans (hd a)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc |((2 : ℝ) * N)⁻¹ * ∑ i, F (x i) (x i)|
      = ((2 : ℝ) * N)⁻¹ * |∑ i, F (x i) (x i)| := by
        rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ ((2 : ℝ) * N)⁻¹ * (N * Md) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc |∑ i, F (x i) (x i)| ≤ ∑ i, |F (x i) (x i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, Md := Finset.sum_le_sum fun i _ => hd _
          _ = N * Md := by simp
    _ = Md / 2 := by field_simp

theorem ustat_eLpNorm_le {μ : Measure α} [IsProbabilityMeasure μ] {F : α → α → ℝ}
    (hFm : Measurable (Function.uncurry F)) {M Md : ℝ} (hM : ∀ x y, |F x y| ≤ M)
    (hd : ∀ a, |F a a| ≤ Md)
    (hsym : ∀ x y, F x y = F y x) (hc : ∀ y, ∫ x, F x y ∂μ = 0) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    eLpNorm (fun x : Fin N → α =>
        ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, F (x i) (x j)) ((2 * k : ℕ) : ENNReal)
        (Measure.pi fun _ => μ) ≤
      ENNReal.ofReal ((((2 * k : ℕ) : ℝ)) ^ 2 * M) + ENNReal.ofReal (Md / 2) := by
  have hnonempty : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ)
    simp [Set.univ_eq_empty_iff.mpr h] at this
  have hsplit : (fun x : Fin N → α => ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, F (x i) (x j)) =
      (fun x => (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, F (x i) (x j)) +
      (fun x => ((2 : ℝ) * N)⁻¹ * ∑ i, F (x i) (x i)) := by
    funext x
    exact ustat_decomp (fun i j => F (x i) (x j)) (fun i j => hsym _ _)
  have hm2 : Measurable (fun x : Fin N → α => ((2 : ℝ) * N)⁻¹ * ∑ i, F (x i) (x i)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => by
      have h2 : Measurable fun x : Fin N → α => (x i, x i) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply i)
      exact hFm.comp h2)
  rw [hsplit]
  refine (eLpNorm_add_le (by exact_mod_cast (by omega : 1 ≤ 2 * k))).trans ?_
  refine add_le_add (offdiag_eLpNorm_le hFm hM hsym hc hk N) ?_
  refine (eLpNorm_le_of_ae_bound (C := Md / 2) hm2.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact diag_abs_le hd x
  · simp

open Filter Topology
open scoped ENNReal

/-- Uniform-in-`N` `L^q` smallness of the U-statistic for a family of centered symmetric kernels
converging uniformly to `0`. -/
theorem uStat_family_tendsto {μ : Measure α} [IsProbabilityMeasure μ] {F : ℕ → α → α → ℝ}
    (hFm : ∀ R, Measurable (Function.uncurry (F R)))
    (hsym : ∀ R x y, F R x y = F R y x) (hc : ∀ R y, ∫ x, F R x y ∂μ = 0)
    (hunif : ∀ δ : ℝ, 0 < δ → ∀ᶠ R in atTop, ∀ x y, |F R x y| ≤ δ)
    {q : ℝ≥0∞} (hq : q ≠ ⊤) :
    Tendsto (fun R => ⨆ N : ℕ, eLpNorm (fun x : Fin N → α =>
        ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, F R (x i) (x j)) q
        (Measure.pi fun _ => μ)) atTop (𝓝 0) := by
  set k : ℕ := ⌈q.toReal⌉₊ + 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hqle : q ≤ ((2 * k : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hq,
      show ((2 * k : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 * k : ℕ) : ℝ) from
        (ENNReal.ofReal_natCast _).symm]
    apply ENNReal.ofReal_le_ofReal
    have h1 := Nat.le_ceil q.toReal
    have h2 : (⌈q.toReal⌉₊ : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈q.toReal⌉₊ ≤ 2 * k)
    linarith
  set c : ℝ := (((2 * k : ℕ) : ℝ)) ^ 2 with hc_def
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ R in atTop, (⨆ N : ℕ, eLpNorm (fun x : Fin N → α =>
        ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, F R (x i) (x j)) q
        (Measure.pi fun _ => μ)) ≤ ENNReal.ofReal (c * δ) + ENNReal.ofReal (δ / 2) := by
    intro δ hδ
    filter_upwards [hunif δ hδ] with R hR
    refine iSup_le fun N => ?_
    exact (eLpNorm_le_eLpNorm_of_exponent_le hqle).trans
      (ustat_eLpNorm_le (hFm R) (fun x y => hR x y) (fun a => hR a a) (hsym R) (hc R) hk N)
  have hg : Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ) + ENNReal.ofReal (δ / 2))
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ) + ENNReal.ofReal (δ / 2)) (𝓝 0)
        (𝓝 (ENNReal.ofReal (c * 0) + ENNReal.ofReal (0 / 2))) := by
      refine Tendsto.add ?_ ?_
      · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (by fun_prop : Continuous fun δ : ℝ => c * δ).continuousAt.tendsto
      · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (by fun_prop : Continuous fun δ : ℝ => δ / 2).continuousAt.tendsto
    simp only [mul_zero, zero_div, ENNReal.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ1, hδ2⟩ := (((hg.eventually (ge_mem_nhds hε)).and
    self_mem_nhdsWithin).exists)
  exact (key δ hδ2).mono fun R hR => hR.trans hδ1

theorem nonempty_of_prob (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := measure_univ (μ := μ)
  simp [Set.univ_eq_empty_iff.mpr h] at this

section Torus

open DGPS DGPS.Lipschitz.KernelApproximation

variable {d : ℕ}

theorem TK_symm (S : Spec d) (D : KData d) (hsym : ∀ x y, D.K x y = D.K y x) (i j : ℕ) :
    TK S D.K i j = TK S D.K j i := by
  have hs : D.swap.K = D.K := by funext x y; exact hsym y x
  have := TK_swap S D j i
  rwa [hs] at this

theorem smoothK_symm (S : Spec d) (D : KData d) (hsym : ∀ x y, D.K x y = D.K y x) (t : ℝ)
    (m : ℕ) (x y : Torus d) : smoothK S D t m x y = smoothK S D t m y x := by
  unfold smoothK
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [TK_symm S D hsym j i, add_comm (S.lam j)]
  ring

theorem smoothK_continuous (S : Spec d) (D : KData d) (t : ℝ) (m : ℕ) :
    Continuous (Function.uncurry (smoothK S D t m)) := by
  show Continuous fun p : Torus d × Torus d => smoothK S D t m p.1 p.2
  unfold smoothK
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))

theorem smoothK_centered (S : Spec d) (D : KData d) (h0 : ∀ x, S.v 0 x = 1)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ) (y : Torus d) :
    ∫ x, smoothK S D t m x y ∂S.mu = 0 := by
  have hint : ∀ i j, Integrable (fun x => Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j *
      (S.v i x * S.v j y)) S.mu := fun i j =>
    S.int_cont (continuous_const.mul ((S.vc i).mul continuous_const))
  unfold smoothK
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : i = 0
  · subst hi
    simp [TK_zero_left S D h0 hc]
  · have hvi : ∫ x, S.v i x ∂S.mu = 0 := by
      have := S.orth i 0
      simp only [h0, mul_one] at this
      rw [this]; simp [hi]
    have : (fun x => Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j *
        (S.v i x * S.v j y)) =
        fun x => (Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j * S.v j y) * S.v i x := by
      funext x; ring
    rw [this, integral_const_mul, hvi, mul_zero]

end Torus

end DGPS.Lipschitz.CenteredKernelMoments

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS DGPS.Lipschitz.KernelApproximation DGPS.Lipschitz.CenteredKernelMoments

/-- **Centered U-statistic value moments (LIP013).**

(1) For every `k ≥ 1` there is a constant `C` (depending only on `k`; one may take `C = (2k)²`)
such that for every probability space `(α, μ)` and every measurable, symmetric, `μ`-centered kernel
`F` with `|F| ≤ M` and `|F(a,a)| ≤ Md`, the off-diagonal term `N⁻¹ ∑_{i<j} F(Xᵢ,Xⱼ)` has
`L^{2k}(μ^N)`-norm at most `C M`, and the diagonal term `(2N)⁻¹ ∑ᵢ F(Xᵢ,Xᵢ)` is bounded by `Md / 2`.

(2) For the kernel approximations `K_R` of LIP011 (`smoothK`), the U-statistics
`U_N^K = (2N)⁻¹ ∑_{i,j} K(Xᵢ,Xⱼ)` satisfy `sup_N ‖U_N^K - U_N^{K_R}‖_{L^q(μ^N)} → 0` as
`R → ∞`, for every finite `q ≥ 1`. -/
theorem centered_u_statistic_value_moments :
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ {α : Type} [MeasurableSpace α] (μ : Measure α)
        [IsProbabilityMeasure μ] (F : α → α → ℝ), Measurable (Function.uncurry F) →
        ∀ M Md : ℝ, (∀ x y, |F x y| ≤ M) → (∀ a, |F a a| ≤ Md) →
        (∀ x y, F x y = F y x) → (∀ y, ∫ x, F x y ∂μ = 0) → ∀ N : ℕ,
          eLpNorm (fun x : Fin N → α =>
              (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, F (x i) (x j))
            ((2 * k : ℕ) : ℝ≥0∞) (Measure.pi fun _ => μ) ≤ ENNReal.ofReal (C * M) ∧
          ∀ x : Fin N → α, |((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, F (x i) (x i)| ≤ Md / 2) ∧
    (∀ {d : ℕ} {Φ : Torus d → ℝ} {LΦ : ℝ}, 0 < d → 0 ≤ LΦ → TorusLipschitzWith LΦ Φ →
      ∀ {b : Torus d → Tangent d},
        IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b →
      ∃ S : Spec d, S.w = WeightedGenerator.gibbsW Φ ∧
        ∀ D : KData d, (∀ y, ∫ x, D.K x y ∂S.mu = 0) → (∀ x y, D.K x y = D.K y x) →
          ∃ (t : ℕ → ℝ) (m : ℕ → ℕ), (∀ R, 0 < t R) ∧ Antitone t ∧
            Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
            ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
              Tendsto (fun R => ⨆ N : ℕ, eLpNorm (fun x : Fin N → Torus d =>
                  ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, D.K (x i) (x j) -
                  ((2 : ℝ) * N)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
                    smoothK S D (t R) (m R) (x i) (x j)) q (Measure.pi fun _ => S.mu))
                atTop (𝓝 0)) := by
  refine ⟨fun k hk => ⟨(((2 * k : ℕ) : ℝ)) ^ 2, by positivity, ?_⟩, ?_⟩
  · intro α _ μ _ F hFm M Md hM hd hsym hc N
    have := nonempty_of_prob μ
    exact ⟨offdiag_eLpNorm_le hFm hM hsym hc hk N, fun x => diag_abs_le hd x⟩
  · intro d Φ LΦ hd hL hΦ b hb
    obtain ⟨S, A, hw⟩ := exists_spec_aux hd hL hΦ hb
    refine ⟨S, hw, fun D hc hsym => ?_⟩
    obtain ⟨t, m, C, ht, hanti, htend, hm, -, -, -, -, -, -, hU, -⟩ :=
      smoothed_approximation' S A D
    refine ⟨t, m, ht, hanti, htend, hm, fun q _ hq => ?_⟩
    have : IsProbabilityMeasure S.mu := ⟨by
      have h := S.real_univ
      rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h⟩
    have hKc : ∀ y, Continuous fun x => D.K x y := fun y =>
      D.Kc.comp (continuous_id.prodMk continuous_const)
    have key := uStat_family_tendsto (μ := S.mu)
      (F := fun R x y => D.K x y - smoothK S D (t R) (m R) x y)
      (fun R => (D.Kc.sub (smoothK_continuous S D (t R) (m R))).measurable)
      (fun R x y => by rw [hsym x y, smoothK_symm S D hsym])
      (fun R y => by
        rw [integral_sub (S.int_cont (hKc y)), hc y, smoothK_centered S D A.v0 hc]
        · simp
        · exact S.int_cont ((smoothK_continuous S D (t R) (m R)).comp
            (continuous_id.prodMk continuous_const)))
      (fun δ hδ => by
        have := Metric.tendstoUniformly_iff.mp hU δ hδ
        filter_upwards [this] with R hR x y
        exact (Real.dist_eq _ _ ▸ (hR (x, y)).le))
      hq
    refine key.congr fun R => ?_
    congr 1
    funext N
    congr 1
    funext x
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]

end DGPS.Lipschitz
