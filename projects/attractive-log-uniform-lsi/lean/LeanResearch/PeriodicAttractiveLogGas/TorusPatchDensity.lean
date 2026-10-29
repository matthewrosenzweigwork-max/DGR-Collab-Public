import LeanResearch.PeriodicAttractiveLogGas.TorusLocalGradient
import LeanResearch.PeriodicAttractiveLogGas.MeshAdjacentCells
import LeanResearch.PeriodicAttractiveLogGas.OrientedRectangleDensity

/-! Source Lemma 3.2 on literal periodic mesh cells and adjacent unions.
The density is relative to meshCellMeasure or edgeCellMeasure. Its Lq bound
is the genuine norm in that measure. Only the restriction of f to the closed
torus patch is Lipschitz. All other values of f are unrestricted.

The vertical reference chart precomposes with an explicit Euclidean linear
isometry. The density and function are both pulled back; no symmetry of
either function, or of the Green kernel, is used.

SOURCE_ONLY candidate. No Lean execution, axiom inspection, independent
semantic verdict, or protected acceptance is asserted by this file.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace PeriodicAttractiveLogGas.TorusPatchDensity

open MeshCells MeshAdjacentCells RectangleDilation RectangleRotation DensityEntropy

inductive Shape where
  | cell
  | edge (j : Fin 2)

def kind : Shape → RectangleDilation.Kind
  | .cell => .square
  | .edge _ => .double

def orientation : Shape → PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace
  | .cell => LinearIsometryEquiv.refl ℝ PlanarSpace
  | .edge j => if j = 0 then LinearIsometryEquiv.refl ℝ PlanarSpace else coordinateSwap

def domain (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Set Torus :=
  match b with
  | .cell => meshCell J hJ a
  | .edge j => edgeCellUnion J hJ a j

def baseMeasure (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Measure Torus :=
  match b with
  | .cell => meshCellMeasure J hJ a
  | .edge j => edgeCellMeasure J hJ a j

instance baseMeasure_probability (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    IsProbabilityMeasure (baseMeasure b J hJ a) := by
  cases b <;> dsimp [baseMeasure] <;> infer_instance

def chart (b : Shape) (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) : Torus :=
  meshChart J a (orientation b Z)

def planeChart (b : Shape) (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) : PlanarSpace :=
  meshAffine J a (orientation b Z)

theorem chart_eq_quotient (b : Shape) (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) :
    chart b J a Z = torusQuotient (planeChart b J a Z) := rfl

theorem planeChart_eq_affine (b : Shape) (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) :
    planeChart b J a Z = affine ((J : ℝ)⁻¹ • meshIndexVector a) J (orientation b Z) := by
  rw [planeChart, meshAffine_eq_dilation]

theorem continuous_chart (b : Shape) (J : ℕ) (a : MeshIndex J) : Continuous (chart b J a) :=
  (continuous_meshChart J a).comp (orientation b).continuous

theorem closedEdgeRectangle_one : closedEdgeRectangle 1 = closedVerticalRectangle := by
  have hw : edgeWidth 1 = verticalWidth := by
    funext j
    fin_cases j <;> norm_num [edgeWidth, verticalWidth, doubleRectangleWidth, swapIndex]
  simp only [closedEdgeRectangle, closedVerticalRectangle, hw]

theorem edgeLebesgue_one : edgeLebesgue 1 = verticalLebesgue := by
  rw [edgeLebesgue_eq_closed, closedEdgeRectangle_one, verticalLebesgue]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem chart_image_closed (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    chart b J a '' closed (kind b) = closure (domain b J hJ a) := by
  cases b with
  | cell => simpa [chart, kind, orientation, closed, domain] using! (closure_meshCell J hJ a).symm
  | edge j =>
      fin_cases j
      · simpa [chart, kind, orientation, closed, domain, closedEdgeRectangle_zero] using!
          (closure_edgeCellUnion J hJ a 0).symm
      · change chart (.edge 1) J a '' closed (kind (.edge 1)) =
          closure (domain (.edge 1) J hJ a)
        rw [domain, closure_edgeCellUnion, closedEdgeRectangle_one,
          ← image_coordinateSwap_closedHorizontal, image_image]
        simp only [chart, kind, orientation, closed, show (1 : Fin 2) ≠ 0 by decide, ite_false]
        rfl

theorem isCompact_closure_domain (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    IsCompact (closure (domain b J hJ a)) := by
  rw [← chart_image_closed]
  exact (isCompact_closed (kind b)).image (continuous_chart b J a)

/-- This is the literal normalized law, including wrapped cells. -/
theorem measurePreserving_chart (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving (chart b J a) (RectangleDilation.referenceMeasure (kind b))
      (baseMeasure b J hJ a) := by
  cases b with
  | cell => simpa [chart, kind, orientation, baseMeasure, RectangleDilation.referenceMeasure] using!
      measurePreserving_meshChart J hJ a
  | edge j =>
      fin_cases j
      · simpa [chart, kind, orientation, baseMeasure, RectangleDilation.referenceMeasure] using!
          measurePreserving_meshChart_rectangle J hJ a
      · have hm := measurePreserving_meshChart_edgeRectangle J hJ a 1
        rw [edgeLebesgue_one] at hm
        simpa [chart, kind, orientation, baseMeasure, RectangleDilation.referenceMeasure,
          Function.comp_def] using! hm.comp measurePreserving_swap_horizontal

theorem ae_mem_closure_domain (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    ∀ᵐ z ∂baseMeasure b J hJ a, z ∈ closure (domain b J hJ a) := by
  have hm := measurePreserving_chart b J hJ a
  rw [← hm.map_eq]
  apply (ae_map_iff hm.aemeasurable isClosed_closure.measurableSet).mpr
  filter_upwards [ae_mem_closed (kind b)] with Z hZ
  change chart b J a Z ∈ closure (domain b J hJ a)
  rw [← chart_image_closed]
  exact ⟨Z, hZ, rfl⟩

theorem dist_planeChart (b : Shape) (J : ℕ) (a : MeshIndex J) (Z W : PlanarSpace) :
    dist (planeChart b J a Z) (planeChart b J a W) = |(J : ℝ)⁻¹| * dist Z W := by
  simp only [planeChart, meshAffine, dist_eq_norm, ← smul_sub,
    add_sub_add_left_eq_sub, norm_smul, Real.norm_eq_abs, ← map_sub,
    (orientation b).norm_map]

theorem lipschitzOnWith_pullback (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) :
    LipschitzOnWith (L * ‖(J : ℝ)⁻¹‖₊) (fun Z ↦ f (chart b J a Z)) (closed (kind b)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro Z hZ W hW
  have hmem (x : PlanarSpace) (hx : x ∈ closed (kind b)) :
      chart b J a x ∈ closure (domain b J hJ a) := by
    rw [← chart_image_closed]
    exact ⟨x, hx, rfl⟩
  calc
    dist (f (chart b J a Z)) (f (chart b J a W))
      ≤ (L : ℝ) * torusEuclideanDist (chart b J a Z) (chart b J a W) := by
        simpa only [Real.dist_eq] using hf _ (hmem _ hZ) _ (hmem _ hW)
    _ ≤ (L : ℝ) * dist (planeChart b J a Z) (planeChart b J a W) :=
      mul_le_mul_of_nonneg_left (torusEuclideanDist_quotient_le _ _) L.coe_nonneg
    _ = _ := by rw [dist_planeChart]; simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]; ring

/-- An exact identity for the ordinary Euclidean gradient. No derivative
compatibility hypothesis or global Lipschitz extension is present. -/
theorem norm_gradient_chart (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (f : Torus → ℝ) (Z : PlanarSpace) :
    ‖rectangleOrdinaryGradient (fun W ↦ f (chart b J a W)) Z‖ =
      (J : ℝ)⁻¹ * ‖torusOrdinaryGradient f (chart b J a Z)‖ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  simpa only [chart_eq_quotient, planeChart_eq_affine] using
    norm_gradient_torus_oriented_affine f (orientation b) ((J : ℝ)⁻¹ • meshIndexVector a) hJr Z

/-! Distribution helpers. The density need only be AE measurable in the
base measure; its Lq hypothesis below supplies this property. -/

theorem lintegral_comp_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {T : A → B} (hT : MeasurePreserving T μ ν)
    {F : B → ℝ≥0∞} (hF : AEMeasurable F ν) :
    (∫⁻ x, F (T x) ∂μ) = ∫⁻ y, F y ∂ν := by
  rw [← hT.map_eq] at hF ⊢
  exact (lintegral_map' hF hT.aemeasurable).symm

theorem measurePreserving_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {T : A → B} (hT : MeasurePreserving T μ ν)
    {p : B → ℝ} (hp : AEMeasurable p ν) :
    MeasurePreserving T (μ.withDensity (fun x ↦ ENNReal.ofReal (p (T x))))
      (ν.withDensity (fun y ↦ ENNReal.ofReal (p y))) := by
  refine ⟨hT.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs]
  exact lintegral_comp_ae (hT.restrict_preimage hs) hp.ennreal_ofReal.restrict

theorem probability_of_measurePreserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure ν] {T : A → B}
    (hT : MeasurePreserving T μ ν) : IsProbabilityMeasure μ := by
  constructor
  simpa only [preimage_univ, measure_univ] using hT.measure_preimage nullMeasurableSet_univ

theorem integral_comp_ae {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure A} {ν : Measure B}
    {T : A → B} (hT : MeasurePreserving T μ ν) {F : B → E} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (T x) ∂μ) = ∫ y, F y ∂ν := by
  rw [← hT.map_eq] at hF ⊢
  exact (integral_map hT.aemeasurable hF).symm

theorem memLp_comp_iff {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] {μ : Measure A} {ν : Measure B} {T : A → B}
    (hT : MeasurePreserving T μ ν) {F : B → E} (hF : AEStronglyMeasurable F ν) (r : ℝ≥0∞) :
    MemLp (fun x ↦ F (T x)) r μ ↔ MemLp F r ν := by
  rw [← hT.map_eq] at hF ⊢
  exact (memLp_map_measure_iff hF hT.aemeasurable).symm

theorem lpNorm_comp_ae {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] {μ : Measure A} {ν : Measure B} {T : A → B}
    (hT : MeasurePreserving T μ ν) {F : B → E} (hF : AEStronglyMeasurable F ν) (r : ℝ≥0∞) :
    lpNorm (fun x ↦ F (T x)) r μ = lpNorm F r ν :=
  congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving (p := r) hF hT)

theorem entropy_comp_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {T : A → B} (hT : MeasurePreserving T μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    entropy μ (fun x ↦ F (T x)) = entropy ν F := by
  have hm : ν.real univ = μ.real univ := by
    simp only [← hT.map_eq, measureReal_def, Measure.map_apply hT.measurable MeasurableSet.univ,
      preimage_univ]
  have he := lintegral_comp_ae hT
    ((continuous_entropyDensity.measurable.comp_aemeasurable hF.aemeasurable).ennreal_ofReal)
  simp only [Function.comp_def] at he
  unfold entropy
  rw [he, integral_comp_ae hT hF, hm]

def law (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (p : Torus → ℝ) : Measure Torus :=
  (baseMeasure b J hJ a).withDensity (fun z ↦ ENNReal.ofReal (p z))

def pulledDensity (b : Shape) (J : ℕ) (a : MeshIndex J) (p : Torus → ℝ) : PlanarSpace → ℝ :=
  fun Z ↦ p (chart b J a Z)

theorem measurePreserving_density_chart (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {p : Torus → ℝ} (hp : AEMeasurable p (baseMeasure b J hJ a)) :
    MeasurePreserving (chart b J a) (referenceLaw (kind b) (pulledDensity b J a p))
      (law b J hJ a p) :=
  measurePreserving_withDensity (measurePreserving_chart b J hJ a) hp

theorem ae_mem_closure_law (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (p : Torus → ℝ) :
    ∀ᵐ z ∂law b J hJ a p, z ∈ closure (domain b J hJ a) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_closure_domain b J hJ a)

theorem density_constants (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ z ∂baseMeasure b J hJ a, c ≤ p z)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (baseMeasure b J hJ a))
    (hK : lpNorm p (ENNReal.ofReal q) (baseMeasure b J hJ a) ≤ K) : c ≤ 1 ∧ 1 ≤ K := by
  let hp := hpq.aestronglyMeasurable.aemeasurable
  let p' := hp.mk p
  have hp' : Measurable p' := hp.measurable_mk
  have he : p =ᵐ[baseMeasure b J hJ a] p' := hp.ae_eq_mk
  have hν : law b J hJ a p =
      (baseMeasure b J hJ a).withDensity (fun z ↦ ENNReal.ofReal (p' z)) :=
    withDensity_congr_ae (he.mono fun z hz ↦ congrArg ENNReal.ofReal hz)
  have hpc' : ∀ᵐ z ∂baseMeasure b J hJ a, c ≤ p' z := by
    filter_upwards [he, hpc] with z hz hc'
    simpa only [← hz] using hc'
  have hpq' : MemLp p' (ENNReal.ofReal q) (baseMeasure b J hJ a) :=
    (memLp_congr_ae he).mp hpq
  have hK' : lpNorm p' (ENNReal.ofReal q) (baseMeasure b J hJ a) ≤ K := by
    rw [← show lpNorm p (ENNReal.ofReal q) (baseMeasure b J hJ a) =
        lpNorm p' (ENNReal.ofReal q) (baseMeasure b J hJ a) from
      congrArg ENNReal.toReal (eLpNorm_congr_ae he)]
    exact hK
  exact DensityMoments.density_constants hν hp' hc hpc' hq hpq' hK'

theorem ae_differentiableAt_reference {b : RectangleDilation.Kind} {u : PlanarSpace → ℝ}
    {L : ℝ≥0} (hu : LipschitzOnWith L u (closed b)) :
    ∀ᵐ Z ∂RectangleDilation.referenceMeasure b, DifferentiableAt ℝ u Z := by
  cases b
  · exact ae_differentiableAt_on_square hu
  · exact ae_differentiableAt_on_rectangle hu

/-- Rademacher on the actual closed reference set, followed by the inverse
affine isometry and lattice invariance. Boundary points are excluded only
by the proved null-boundary statements of the reference rectangles. -/
theorem ae_differentiableAt_all_lifts (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a)))
    {ν : Measure Torus} (hν : ν ≪ baseMeasure b J hJ a) :
    ∀ᵐ z ∂ν, ∀ x : PlanarSpace, torusQuotient x = z →
      DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) x := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hm := measurePreserving_chart b J hJ a
  have hmeas : MeasurableSet {z : Torus |
      DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) (centeredLift z)} :=
    (measurableSet_of_differentiableAt ℝ (fun y ↦ f (torusQuotient y))).preimage
      measurable_centeredLift
  have hd : ∀ᵐ z ∂baseMeasure b J hJ a,
      DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) (centeredLift z) := by
    rw [← hm.map_eq]
    apply (ae_map_iff hm.aemeasurable hmeas).mpr
    filter_upwards [ae_differentiableAt_reference (lipschitzOnWith_pullback b J hJ a hf)] with Z hZ
    have hZ' : DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) (planeChart b J a Z) := by
      rw [planeChart_eq_affine]
      apply differentiableAt_of_oriented_affine_comp (orientation b)
        ((J : ℝ)⁻¹ • meshIndexVector a) hJr
      simpa only [chart_eq_quotient, planeChart_eq_affine] using hZ
    have hq : torusQuotient (centeredLift (chart b J a Z)) = torusQuotient (planeChart b J a Z) :=
      torusQuotient_centeredLift (chart b J a Z)
    exact (differentiableAt_torusLift_iff_of_quotient_eq f hq).mpr hZ'
  filter_upwards [hν.ae_le hd] with z hz
  intro x hx
  exact (differentiableAt_torusLift_iff_of_quotient_eq f
    ((torusQuotient_centeredLift z).trans hx.symm)).mp hz

theorem ae_norm_torusOrdinaryGradient_le (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) :
    ∀ᵐ z ∂baseMeasure b J hJ a, ‖torusOrdinaryGradient f z‖ ≤ (L : ℝ) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hm := measurePreserving_chart b J hJ a
  have hmeas : MeasurableSet {z : Torus | ‖torusOrdinaryGradient f z‖ ≤ (L : ℝ)} :=
    measurableSet_le (measurable_torusOrdinaryGradient f).norm measurable_const
  rw [← hm.map_eq]
  apply (ae_map_iff hm.aemeasurable hmeas).mpr
  filter_upwards [ae_closed_mem_nhds (kind b)] with Z hZ
  have h := norm_fderiv_le_of_lipschitzOn ℝ hZ (lipschitzOnWith_pullback b J hJ a hf)
  rw [← norm_rectangleOrdinaryGradient, norm_gradient_chart b J hJ a f Z] at h
  have hcoef : ((L * ‖(J : ℝ)⁻¹‖₊ : ℝ≥0) : ℝ) = (J : ℝ)⁻¹ * (L : ℝ) := by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hJr), mul_comm]
  rw [hcoef] at h
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr hJr)).mp h

theorem memLp_gradient_law (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)]
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) (r : ℝ≥0∞) :
    MemLp (torusOrdinaryGradient f) r (law b J hJ a p) :=
  MemLp.of_bound (measurable_torusOrdinaryGradient f).aestronglyMeasurable (L : ℝ)
    ((withDensity_absolutelyContinuous _ _).ae_le (ae_norm_torusOrdinaryGradient_le b J hJ a hf))

theorem memLp_function_law (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)]
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) (r : ℝ≥0∞) :
    MemLp f r (law b J hJ a p) :=
  hf.memLp (isCompact_closure_domain b J hJ a) (ae_mem_closure_law b J hJ a p) r

/-- Actual finite gates: no real-integral default or extended-entropy
finiteness is used to stand in for integrability. -/
theorem density_finite (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)]
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) :
    (∀ r : ℝ≥0∞, MemLp f r (law b J hJ a p)) ∧
      (∀ r : ℝ≥0∞, MemLp (torusOrdinaryGradient f) r (law b J hJ a p)) ∧
      Integrable f (law b J hJ a p) ∧
      Integrable (fun z ↦ f z ^ 2) (law b J hJ a p) ∧
      Integrable (fun z ↦ ‖torusOrdinaryGradient f z‖ ^ 2) (law b J hJ a p) ∧
      Integrable (fun z ↦ f z ^ 2 * Real.log (f z ^ 2)) (law b J hJ a p) := by
  have hmem := memLp_function_law b J hJ a p hf
  have hgrad := memLp_gradient_law b J hJ a p hf
  refine ⟨hmem, hgrad, (hmem 1).integrable le_rfl, ?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hmem 2).aestronglyMeasurable).mp (hmem 2)
  · exact (memLp_two_iff_integrable_sq_norm
      (measurable_torusOrdinaryGradient f).aestronglyMeasurable).mp (hgrad 2)
  · have hcont : Continuous (fun t : ℝ ↦ t ^ 2 * Real.log (t ^ 2)) :=
      Real.continuous_mul_log.comp (continuous_id.pow 2)
    exact PhysicalLipschitzOn.integrable_continuous_comp (f := f)
      (μ := law b J hJ a p) (Φ := fun t : ℝ ↦ t ^ 2 * Real.log (t ^ 2)) hf
      (isCompact_closure_domain b J hJ a) (ae_mem_closure_law b J hJ a p) hcont

theorem entropy_sq_eq_integral_law (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)]
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) :
    entropy (law b J hJ a p) (fun z ↦ f z ^ 2) =
      (((∫ z, f z ^ 2 * Real.log (f z ^ 2) ∂law b J hJ a p) -
        (∫ z, f z ^ 2 ∂law b J hJ a p) *
          Real.log (∫ z, f z ^ 2 ∂law b J hJ a p) : ℝ) : EReal) :=
  entropy_eq_integral (Eventually.of_forall fun z ↦ sq_nonneg (f z))
    (density_finite b J hJ a p hf).2.2.2.2.2

theorem integral_gradient_chart (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (f : Torus → ℝ) {μ : Measure PlanarSpace} {ν : Measure Torus}
    (hm : MeasurePreserving (chart b J a) μ ν) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W ↦ f (chart b J a W)) Z‖ ^ 2 ∂μ) =
      ((J : ℝ) ^ 2)⁻¹ * ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν := by
  simp_rw [norm_gradient_chart b J hJ a, mul_pow, inv_pow]
  rw [integral_const_mul,
    integral_comp_ae hm ((measurable_torusOrdinaryGradient f).norm.pow_const 2).aestronglyMeasurable]

theorem lpNorm_gradient_chart (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (f : Torus → ℝ) {μ : Measure PlanarSpace} {ν : Measure Torus}
    (hm : MeasurePreserving (chart b J a) μ ν) (r : ℝ≥0∞) :
    lpNorm (rectangleOrdinaryGradient (fun W ↦ f (chart b J a W))) r μ =
      (J : ℝ)⁻¹ * lpNorm (torusOrdinaryGradient f) r ν := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hG : AEStronglyMeasurable (fun Z ↦ torusOrdinaryGradient f (chart b J a Z)) μ :=
    ((measurable_torusOrdinaryGradient f).comp hm.measurable).aestronglyMeasurable
  have he := congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (p := r)
    (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable (hG.const_smul (J : ℝ)⁻¹)
    (Eventually.of_forall fun Z ↦ by
      rw [norm_gradient_chart b J hJ a f Z, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hJr)]))
  change lpNorm (rectangleOrdinaryGradient (fun W ↦ f (chart b J a W))) r μ =
    lpNorm ((J : ℝ)⁻¹ • (fun Z ↦ torusOrdinaryGradient f (chart b J a Z))) r μ at he
  rw [he, lpNorm_const_smul,
    lpNorm_comp_ae hm (measurable_torusOrdinaryGradient f).aestronglyMeasurable]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJr)]

/-- The three exact source bounds in the physical torus gradient. -/
def Estimates (S : ℝ → ℝ) (J : ℕ) (c q K : ℝ) (ν : Measure Torus) (f : Torus → ℝ) : Prop :=
  MemLp (torusOrdinaryGradient f) 2 ν ∧ MemLp f 2 ν ∧
    ProbabilityTheory.variance f ν ≤ (poincareConstant S c q K / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) ∧
    entropy ν (fun z ↦ f z ^ 2) ≤
      (((logSobolevConstant S c q K / (J : ℝ) ^ 2) *
        (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
    ∀ s : ℝ, 2 ≤ s →
      MemLp (fun z ↦ f z - ∫ w, f w ∂ν) (ENNReal.ofReal s) ν ∧
        lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) (ENNReal.ofReal s) ν ≤
          (momentConstant S c q K s / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν

/-- The actual local density theorem. Every rectangle inequality is
discharged by the checked reference density theorem. Density, ordinary
gradient, mean, variance, entropy, and finite Lp norms are transported here. -/
theorem density_estimates (b : Shape) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) [IsProbabilityMeasure (law b J hJ a p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ z ∂baseMeasure b J hJ a, c ≤ p z)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (baseMeasure b J hJ a))
    (hK : lpNorm p (ENNReal.ofReal q) (baseMeasure b J hJ a) ≤ K)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (domain b J hJ a))) :
    Estimates (sobolevConstant (kind b)) J c q K (law b J hJ a p) f := by
  have hm₀ := measurePreserving_chart b J hJ a
  have hm := measurePreserving_density_chart b J hJ a hpq.aestronglyMeasurable.aemeasurable
  let : IsProbabilityMeasure (referenceLaw (kind b) (pulledDensity b J a p)) :=
    probability_of_measurePreserving hm
  have hpc' : ∀ᵐ Z ∂RectangleDilation.referenceMeasure (kind b),
      c ≤ pulledDensity b J a p Z := hm₀.quasiMeasurePreserving.ae hpc
  have hpq' : MemLp (pulledDensity b J a p) (ENNReal.ofReal q)
      (RectangleDilation.referenceMeasure (kind b)) := hpq.comp_measurePreserving hm₀
  have hK' : lpNorm (pulledDensity b J a p) (ENNReal.ofReal q)
      (RectangleDilation.referenceMeasure (kind b)) ≤ K := by
    change lpNorm (fun Z ↦ p (chart b J a Z)) (ENNReal.ofReal q)
      (RectangleDilation.referenceMeasure (kind b)) ≤ K
    rw [lpNorm_comp_ae hm₀ hpq.aestronglyMeasurable]
    exact hK
  have hu := lipschitzOnWith_pullback b J hJ a hf
  have h := reference_density_estimates (kind b) (pulledDensity b J a p)
    hc hpc' hq hpq' hK' hu
  have hfm := (memLp_function_law b J hJ a p hf 2).aestronglyMeasurable
  have hmean := integral_comp_ae hm hfm
  have hvar := hm.variance_fun_comp hfm.aemeasurable
  have hfm2 : AEStronglyMeasurable (fun z ↦ f z ^ 2) (law b J hJ a p) := hfm.pow 2
  have hent := entropy_comp_ae hm hfm2
  have henergy := integral_gradient_chart b J hJ a f hm
  have hgradnorm := lpNorm_gradient_chart b J hJ a f hm 2
  refine ⟨memLp_gradient_law b J hJ a p hf 2, memLp_function_law b J hJ a p hf 2, ?_, ?_, ?_⟩
  · have hb := h.2.2.1
    rw [hvar, henergy] at hb
    simpa only [div_eq_mul_inv, mul_assoc] using hb
  · have hb := h.2.2.2.1
    rw [hent, henergy] at hb
    simpa only [div_eq_mul_inv, mul_assoc] using hb
  · intro s hs
    have hb := h.2.2.2.2 s hs
    have hmcenter : AEStronglyMeasurable (fun z ↦ f z - ∫ w, f w ∂law b J hJ a p)
        (law b J hJ a p) := hfm.sub aestronglyMeasurable_const
    have hcmem : MemLp (fun z ↦ f z - ∫ w, f w ∂law b J hJ a p)
        (ENNReal.ofReal s) (law b J hJ a p) := by
      apply (memLp_comp_iff hm hmcenter _).mp
      simpa only [hmean] using hb.1
    refine ⟨hcmem, ?_⟩
    have hb' := hb.2
    rw [hmean, lpNorm_comp_ae hm hmcenter, hgradnorm] at hb'
    simpa only [div_eq_mul_inv, mul_assoc] using hb'

/-- The cell specialization uses the literal checked meshCellMeasure. -/
theorem meshCell_density_estimates (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ)
    [IsProbabilityMeasure ((meshCellMeasure J hJ a).withDensity (fun z ↦ ENNReal.ofReal (p z)))]
    {c q K : ℝ} (hc : 0 < c) (hpc : ∀ᵐ z ∂meshCellMeasure J hJ a, c ≤ p z)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (meshCellMeasure J hJ a))
    (hK : lpNorm p (ENNReal.ofReal q) (meshCellMeasure J hJ a) ≤ K)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (meshCell J hJ a))) :
    Estimates squareSobolevConstant J c q K
      ((meshCellMeasure J hJ a).withDensity (fun z ↦ ENNReal.ofReal (p z))) f := by
  let : IsProbabilityMeasure (law .cell J hJ a p) := by
    unfold law baseMeasure
    infer_instance
  simpa only [kind, sobolevConstant, law, baseMeasure] using
    density_estimates .cell J hJ a p hc hpc hq hpq hK hf

/-- Both coordinate directions are included. At J ≥ 2 the base measure is
literally J²/2 times Haar restricted to the two distinct adjacent cells. -/
theorem edgeCell_density_estimates (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (p : Torus → ℝ)
    [IsProbabilityMeasure
      ((edgeCellMeasure J hJ a j).withDensity (fun z ↦ ENNReal.ofReal (p z)))]
    {c q K : ℝ} (hc : 0 < c) (hpc : ∀ᵐ z ∂edgeCellMeasure J hJ a j, c ≤ p z)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (edgeCellMeasure J hJ a j))
    (hK : lpNorm p (ENNReal.ofReal q) (edgeCellMeasure J hJ a j) ≤ K)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (edgeCellUnion J hJ a j))) :
    edgeCellMeasure J hJ a j =
      ((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (edgeCellUnion J hJ a j) ∧
    Estimates rectangleSobolevConstant J c q K
      ((edgeCellMeasure J hJ a j).withDensity (fun z ↦ ENNReal.ofReal (p z))) f := by
  refine ⟨edgeCellMeasure_eq_normalized J hJ hJ2 a j, ?_⟩
  let : IsProbabilityMeasure (law (.edge j) J hJ a p) := by
    unfold law baseMeasure
    infer_instance
  simpa only [kind, sobolevConstant, law, baseMeasure] using
    density_estimates (.edge j) J hJ a p hc hpc hq hpq hK hf

/-- An unoriented edge-adjacent pair, including a pair crossing a periodic
boundary. This measure is written directly as normalized restricted Haar. -/
theorem adjacent_union_density_estimates (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a d : MeshIndex J) (had : EdgeAdjacent J hJ a d) (p : Torus → ℝ)
    [IsProbabilityMeasure
      ((((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ d)).withDensity
        (fun z ↦ ENNReal.ofReal (p z)))]
    {c q K : ℝ} (hc : 0 < c)
    (hpc : ∀ᵐ z ∂((J : ℝ≥0∞) ^ 2 / 2) •
      torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ d), c ≤ p z)
    (hq : 1 < q)
    (hpq : MemLp p (ENNReal.ofReal q)
      (((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ d)))
    (hK : lpNorm p (ENNReal.ofReal q)
      (((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ d)) ≤ K)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (meshCell J hJ a ∪ meshCell J hJ d))) :
    Estimates rectangleSobolevConstant J c q K
      ((((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ d)).withDensity
        (fun z ↦ ENNReal.ofReal (p z))) f := by
  obtain ⟨j, hd | ha⟩ := had
  · subst d
    have he : edgeCellMeasure J hJ a j =
        ((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict
          (meshCell J hJ a ∪ meshCell J hJ (nextCell J hJ a j)) :=
      edgeCellMeasure_eq_normalized J hJ hJ2 a j
    let : IsProbabilityMeasure
        ((edgeCellMeasure J hJ a j).withDensity (fun z ↦ ENNReal.ofReal (p z))) := by
      rw [he]
      infer_instance
    have hpce : ∀ᵐ z ∂edgeCellMeasure J hJ a j, c ≤ p z := by simpa only [he] using hpc
    have hpqe : MemLp p (ENNReal.ofReal q) (edgeCellMeasure J hJ a j) := by
      simpa only [he] using hpq
    have hKe : lpNorm p (ENNReal.ofReal q) (edgeCellMeasure J hJ a j) ≤ K := by
      simpa only [he] using hK
    simpa only [he] using
      (edgeCell_density_estimates J hJ hJ2 a j p hc hpce hq hpqe hKe hf).2
  · subst a
    have he : edgeCellMeasure J hJ d j =
        ((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict
          (meshCell J hJ (nextCell J hJ d j) ∪ meshCell J hJ d) := by
      simpa only [edgeCellUnion, union_comm] using edgeCellMeasure_eq_normalized J hJ hJ2 d j
    let : IsProbabilityMeasure
        ((edgeCellMeasure J hJ d j).withDensity (fun z ↦ ENNReal.ofReal (p z))) := by
      rw [he]
      infer_instance
    have hpce : ∀ᵐ z ∂edgeCellMeasure J hJ d j, c ≤ p z := by simpa only [he] using hpc
    have hpqe : MemLp p (ENNReal.ofReal q) (edgeCellMeasure J hJ d j) := by
      simpa only [he] using hpq
    have hKe : lpNorm p (ENNReal.ofReal q) (edgeCellMeasure J hJ d j) ≤ K := by
      simpa only [he] using hK
    have hfe : PhysicalLipschitzOn L f (closure (edgeCellUnion J hJ d j)) := by
      simpa only [edgeCellUnion, union_comm] using hf
    simpa only [he] using
      (edgeCell_density_estimates J hJ hJ2 d j p hc hpce hq hpqe hKe hfe).2

end PeriodicAttractiveLogGas.TorusPatchDensity
