import LeanResearch.PeriodicAttractiveLogGas.MovingPoleNumerators

/-! Source-only construction of the literal physical rectangular source
charts used in Lemma 3.5. The Euclidean metric is not replaced by a Pi metric.
The source boxes are normalized by their actual Euclidean volume. Their
images lie in the prescribed closed torus cells, including periodic wrap.
No weak chain rule or Lipschitz representative is asserted here. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff

namespace PeriodicAttractiveLogGas.MovingPoleCharts

open MovingPoleNumerators MovingPoleIntegrability GreenPointWeights
open MeshCells MeshAdjacentCells LabelOccupations ConditionalParameters

variable {ι : Type*} [Fintype ι]

def patchWidth : Patch → Fin 2 → ℝ
  | .cell, _ => 1
  | .edge d, k => edgeWidth d k

theorem patchWidth_pos (b : Patch) (k : Fin 2) : 0 < patchWidth b k := by
  cases b with
  | cell => norm_num [patchWidth]
  | edge d => exact edgeWidth_pos d k

theorem mem_patchClosed_iff (b : Patch) (Z : PlanarSpace) :
    Z ∈ patchClosed b ↔ ∀ k, 0 ≤ Z k ∧ Z k ≤ patchWidth b k := by
  cases b <;> simp [patchClosed, closedUnitSquare, closedEdgeRectangle, patchWidth,
    Set.mem_preimage, Pi.le_def, forall_and]

def lower (J : ℕ) (η : ι → MeshIndex J) (ik : ι × Fin 2) : ℝ :=
  (η ik.1 ik.2 : ℝ) / J

def upper (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch) (ik : ι × Fin 2) : ℝ :=
  ((η ik.1 ik.2 : ℝ) + patchWidth (b ik.1) ik.2) / J

/-- A literal rectangle in physical Euclidean source coordinates. -/
def closedChart (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch) : Set (SourceSpace ι) :=
  WithLp.ofLp ⁻¹' Set.pi univ (fun ik ↦ Icc (lower J η ik) (upper J η b ik))

omit [Fintype ι] in
theorem mem_closedChart_iff (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch)
    (X : SourceSpace ι) :
    X ∈ closedChart J η b ↔ ∀ ik, lower J η ik ≤ X ik ∧ X ik ≤ upper J η b ik := by
  simp [closedChart, Set.mem_preimage, Pi.le_def, forall_and]

omit [Fintype ι] in
theorem lower_lt_upper {J : ℕ} (hJ : 0 < J) (η : ι → MeshIndex J)
    (b : ι → Patch) (ik : ι × Fin 2) : lower J η ik < upper J η b ik := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  apply (div_lt_div_iff_of_pos_right hj).2
  exact lt_add_of_pos_right _ (patchWidth_pos _ _)

omit [Fintype ι] in
theorem isCompact_closedChart (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch) :
    IsCompact (closedChart J η b) := by
  change IsCompact ((PiLp.homeomorph 2 (fun _ : ι × Fin 2 ↦ ℝ)) ⁻¹'
    Set.pi univ (fun ik ↦ Icc (lower J η ik) (upper J η b ik)))
  exact (PiLp.homeomorph 2 (fun _ : ι × Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

omit [Fintype ι] in
theorem convex_closedChart (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch) :
    Convex ℝ (closedChart J η b) := by
  intro X hX Y hY s t hs ht hst
  rw [mem_closedChart_iff] at hX hY ⊢
  intro ik
  change lower J η ik ≤ s * X ik + t * Y ik ∧
    s * X ik + t * Y ik ≤ upper J η b ik
  constructor
  · calc
      _ = s * lower J η ik + t * lower J η ik := by rw [← add_mul, hst, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hX ik).1 hs)
        (mul_le_mul_of_nonneg_left (hY ik).1 ht)
  · calc
      _ ≤ s * upper J η b ik + t * upper J η b ik :=
        add_le_add (mul_le_mul_of_nonneg_left (hX ik).2 hs)
          (mul_le_mul_of_nonneg_left (hY ik).2 ht)
      _ = _ := by rw [← add_mul, hst, one_mul]

/-- Every coordinate interval has positive width. This also handles an
empty source index type: the zero-dimensional Euclidean space has one point. -/
theorem interior_closedChart_nonempty {J : ℕ} (hJ : 0 < J)
    (η : ι → MeshIndex J) (b : ι → Patch) : (interior (closedChart J η b)).Nonempty := by
  let X : SourceSpace ι := WithLp.toLp 2 (fun ik ↦ (lower J η ik + upper J η b ik) / 2)
  refine ⟨X, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply (PiLp.continuous_ofLp 2 (fun _ : ι × Fin 2 ↦ ℝ)).continuousAt.preimage_mem_nhds
  apply set_pi_mem_nhds Set.finite_univ
  intro ik _
  apply Icc_mem_nhds
  · change lower J η ik < (lower J η ik + upper J η b ik) / 2
    linarith [lower_lt_upper hJ η b ik]
  · change (lower J η ik + upper J η b ik) / 2 < upper J η b ik
    linarith [lower_lt_upper hJ η b ik]

theorem closedChart_volume_pos {J : ℕ} (hJ : 0 < J)
    (η : ι → MeshIndex J) (b : ι → Patch) :
    0 < (volume : Measure (SourceSpace ι)) (closedChart J η b) :=
  Measure.measure_pos_of_nonempty_interior volume (interior_closedChart_nonempty hJ η b)

theorem closedChart_volume_ne_top (J : ℕ) (η : ι → MeshIndex J) (b : ι → Patch) :
    (volume : Measure (SourceSpace ι)) (closedChart J η b) ≠ (∞ : ℝ≥0∞) :=
  (isCompact_closedChart J η b).measure_lt_top.ne

theorem closedChart_probability {J : ℕ} (hJ : 0 < J)
    (η : ι → MeshIndex J) (b : ι → Patch) :
    IsProbabilityMeasure (sourceChartMeasure (closedChart J η b)) :=
  sourceChartMeasure_probability (isCompact_closedChart J η b)
    (interior_closedChart_nonempty hJ η b)

theorem inverseBlock_mem_patchClosed {J : ℕ} (hJ : 0 < J)
    (η : ι → MeshIndex J) (b : ι → Patch) {X : SourceSpace ι}
    (hX : X ∈ closedChart J η b) (i : ι) :
    meshAffineInv J (η i) (sourceProjection i X) ∈ patchClosed (b i) := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [mem_patchClosed_iff]
  intro k
  have h := (mem_closedChart_iff J η b X).mp hX (i, k)
  have hlo : (η i k : ℝ) ≤ X (i, k) * J := (div_le_iff₀ hj).mp h.1
  have hup : X (i, k) * J ≤ (η i k : ℝ) + patchWidth (b i) k :=
    (le_div_iff₀ hj).mp h.2
  simp only [meshAffineInv_apply, sourceProjection_apply]
  constructor <;> nlinarith

theorem closure_patchDomain {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    closure (patchDomain J hJ a b) = meshChart J a '' patchClosed b := by
  cases b with
  | cell => exact closure_meshCell J hJ a
  | edge d => exact closure_edgeCellUnion J hJ a d

/-- Continuity descends through the actual compact patch chart. Injectivity
on its closed boundary is unnecessary, so this includes periodic seams. -/
theorem continuousOn_patch_of_comp {V : Type*} [TopologicalSpace V]
    {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) {H : Torus → V}
    (hH : ContinuousOn (fun Z ↦ H (meshChart J a Z)) (patchClosed b)) :
    ContinuousOn H (closure (patchDomain J hJ a b)) := by
  rw [closure_patchDomain hJ]
  let B := patchClosed b
  let T := meshChart J a '' B
  let φ : B → T := fun Z ↦ ⟨meshChart J a Z, mem_image_of_mem _ Z.property⟩
  let : CompactSpace B := (isCompact_iff_compactSpace).mp (isCompact_patchClosed b)
  have hφc : Continuous φ :=
    ((continuous_meshChart J a).comp continuous_subtype_val).subtype_mk _
  have hφs : Function.Surjective φ := by
    rintro ⟨z, Z, hZ, rfl⟩
    exact ⟨⟨Z, hZ⟩, rfl⟩
  have hq := Topology.IsQuotientMap.of_surjective_continuous hφs hφc
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hq.continuous_iff.mpr
  exact hH.domRestrict

theorem ae_mem_closure_patch {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    ∀ᵐ z ∂patchMeasure J hJ a b, z ∈ closure (patchDomain J hJ a b) := by
  have hm := measurePreserving_patch J hJ a b
  rw [← hm.map_eq]
  apply (ae_map_iff hm.aemeasurable isClosed_closure.measurableSet).mpr
  filter_upwards [ae_mem_patchClosed b] with Z hZ
  change meshChart J a Z ∈ closure (patchDomain J hJ a b)
  rw [closure_patchDomain hJ]
  exact mem_image_of_mem _ hZ

/-- Local continuity of the lifted function suffices for actual patch-law
measurability. The original function is unrestricted off the closed patch. -/
theorem aestronglyMeasurable_patch_of_comp {V : Type*} [NormedAddCommGroup V]
    {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) {H : Torus → V}
    (hH : ContinuousOn (fun Z ↦ H (meshChart J a Z)) (patchClosed b)) :
    AEStronglyMeasurable H (patchMeasure J hJ a b) := by
  have hc := continuousOn_patch_of_comp hJ a b hH
  have hm := hc.aestronglyMeasurable (μ := patchMeasure J hJ a b)
    isClosed_closure.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_closure_patch hJ a b)] at hm

theorem source_mem_closure_patch {J : ℕ} (hJ : 0 < J)
    (η : ι → MeshIndex J) (b : ι → Patch) {X : SourceSpace ι}
    (hX : X ∈ closedChart J η b) (i : ι) :
    sources X i ∈ closure (patchDomain J hJ (η i) (b i)) := by
  rw [closure_patchDomain hJ]
  refine ⟨meshAffineInv J (η i) (sourceProjection i X),
    inverseBlock_mem_patchClosed hJ η b hX i, ?_⟩
  change torusQuotient (meshAffine J (η i) (meshAffineInv J (η i) (sourceProjection i X))) = _
  rw [meshAffine_right_inverse J hJ (η i)]
  rfl

def cellChart {J N : ℕ} (I : Finset (Fin N)) (η : LabelVector J N) : Set (SourceSpace I) :=
  closedChart J (fun i : I ↦ η i) (fun _ ↦ .cell)

def adjacentShapes {N : ℕ} (I : Finset (Fin N)) (k : Fin N) (d : Fin 2) : I → Patch :=
  fun i ↦ if (i : Fin N) = k then .edge d else .cell

def adjacentChart {J N : ℕ} (I : Finset (Fin N)) (η : LabelVector J N)
    (k : Fin N) (d : Fin 2) : Set (SourceSpace I) :=
  closedChart J (fun i : I ↦ η i) (adjacentShapes I k d)

theorem cellChart_placement {J N : ℕ} (hJ : 0 < J) (I : Finset (Fin N))
    (η : LabelVector J N) {X : SourceSpace I} (hX : X ∈ cellChart I η) :
    ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)) := by
  intro i hi
  rw [extendedSources_subtype I X (⟨i, hi⟩ : I)]
  simpa only [patchDomain] using
    source_mem_closure_patch hJ (fun i : I ↦ η i) (fun _ ↦ .cell) hX (⟨i, hi⟩ : I)

theorem adjacentChart_cell_placement {J N : ℕ} (hJ : 0 < J) (I : Finset (Fin N))
    (η : LabelVector J N) (k : Fin N) (d : Fin 2) {X : SourceSpace I}
    (hX : X ∈ adjacentChart I η k d) :
    ∀ i ∈ I, i ≠ k → extendedSources I X i ∈ closure (meshCell J hJ (η i)) := by
  intro i hi hik
  rw [extendedSources_subtype I X (⟨i, hi⟩ : I)]
  simpa only [adjacentShapes, ite_eq_right hik, patchDomain] using
    source_mem_closure_patch hJ (fun i : I ↦ η i) (adjacentShapes I k d) hX (⟨i, hi⟩ : I)

theorem adjacentChart_edge_placement {J N : ℕ} (hJ : 0 < J) (I : Finset (Fin N))
    (η : LabelVector J N) (k : Fin N) (d : Fin 2) {X : SourceSpace I}
    (hX : X ∈ adjacentChart I η k d) (hk : k ∈ I) :
    extendedSources I X k ∈ closure (edgeCellUnion J hJ (η k) d) := by
  rw [extendedSources_subtype I X (⟨k, hk⟩ : I)]
  simpa [adjacentShapes, patchDomain] using
    source_mem_closure_patch hJ (fun i : I ↦ η i) (adjacentShapes I k d) hX (⟨k, hk⟩ : I)

/-- Actual physical cell-product chart instantiation, with raw Euclidean
source Lebesgue measure. No compactness, normalization, placement, or weak
derivative assertion is left as a premise. -/
theorem cellChart_numerator (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : SourceSpace I × PlanarSpace → ℝ}
    (hf : SmoothOnChart (cellChart I η) (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b (cellChart I η) 1 f := by
  have hS := isCompact_closedChart J (fun i : I ↦ η i) (fun _ ↦ Patch.cell)
  have hS₀ := interior_closedChart_nonempty hJ (fun i : I ↦ η i) (fun _ ↦ Patch.cell)
  have hn := normalized_chart_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I
    (cellChart I η) hS hS₀ (fun _ ↦ η) (fun _ _ ↦ hη)
    (fun _ hX ↦ cellChart_placement hJ I η hX) w hw₀ hw a b hf
  exact hn.normalized_volume hS hS₀

/-- One prescribed source may range over either oriented adjacent union.
Both endpoint occupation caps remain the genuine geometric hypotheses. -/
theorem adjacentChart_numerator (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N) (k : Fin N) (d : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁) (Function.update η k (nextCell J hJ (η k) d)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : SourceSpace I × PlanarSpace → ℝ}
    (hf : SmoothOnChart (adjacentChart I η k d) (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b (adjacentChart I η k d) 1 f := by
  have hS := isCompact_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d)
  have hS₀ := interior_closedChart_nonempty hJ (fun i : I ↦ η i) (adjacentShapes I k d)
  obtain ⟨labels, hcap, hplace⟩ := exists_capped_labels_one_adjacent hJ I
    (adjacentChart I η k d) η k d (fixedDelta β₀ C₀ C₁) hη₀ hη₁
    (fun _ hX ↦ adjacentChart_cell_placement hJ I η k d hX)
    (fun _ hX hk ↦ adjacentChart_edge_placement hJ I η k d hX hk)
  have hn := normalized_chart_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I
    (adjacentChart I η k d) hS hS₀ labels (fun X _ ↦ hcap X) hplace w hw₀ hw a b hf
  exact hn.normalized_volume hS hS₀

end PeriodicAttractiveLogGas.MovingPoleCharts
