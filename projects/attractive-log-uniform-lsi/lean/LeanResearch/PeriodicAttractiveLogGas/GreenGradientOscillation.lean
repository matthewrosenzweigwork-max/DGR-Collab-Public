import LeanResearch.PeriodicAttractiveLogGas.GreenConditionalInfluence
import LeanResearch.PeriodicAttractiveLogGas.LabelRatioTransport

/-! The Hessian and diameter argument in source Proposition 3.11.
The vector is the actual ordinary Euclidean Green gradient. Its oscillation
is proved before comparing expectations under different probability laws.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace PeriodicAttractiveLogGas.GreenGradientOscillation

open MeshCells MeshAdjacentCells GreenPointWeights GreenFarOscillation
  RectangleDilation GreenConditionalInfluence

def KernelHessianBound (C₂ : ℝ) : Prop :=
  ∀ z : Torus, z ≠ 0 → ‖greenHessianOperator z‖ ≤ C₂ / torusEuclideanNorm z ^ 2

theorem exists_kernelHessianBound : ∃ C₂ : ℝ, 0 < C₂ ∧ KernelHessianBound C₂ := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  exact ⟨C, hC, fun z hz ↦ (hb z hz).2.2.2⟩

theorem hasFDerivAt_greenGradient_lift {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    HasFDerivAt (fun y : PlanarSpace ↦ greenGradient (torusQuotient y))
      (greenHessianOperator (torusQuotient x)) x := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfun : (fun y : PlanarSpace ↦ greenGradient (torusQuotient y)) =
      R ∘ fderiv ℝ regularGreenLift := by
    funext y
    exact congrArg (fun L : PlanarSpace →L[ℝ] ℝ ↦ R L) (greenDifferential_lift y)
  have hd : DifferentiableAt ℝ (fderiv ℝ regularGreenLift) x :=
    (contDiffOn_fderiv_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds hx)).differentiableAt (by simp)
  rw [hfun]
  change HasFDerivAt (R ∘ fderiv ℝ regularGreenLift)
    (R.comp (greenHessian (torusQuotient x))) x
  rw [greenHessian_lift]
  exact R.hasFDerivAt.comp x hd.hasFDerivAt

def referenceGradient (a : PlanarSpace) (J : ℝ) (y : Torus) (Z : PlanarSpace) : PlanarSpace :=
  greenGradient (torusQuotient (affine a J Z) - y)

theorem hasFDerivAt_referenceGradient (a : PlanarSpace) (J : ℝ) (y : Torus)
    {Z : PlanarSpace} (hZ : torusQuotient (affine a J Z) - y ≠ 0) :
    HasFDerivAt (referenceGradient a J y)
      (J⁻¹ • greenHessianOperator (torusQuotient (affine a J Z) - y)) Z := by
  have hquot := quotient_affine_sub_centeredLift a J y Z
  have hx : affine a J Z - centeredLift y ∈ offIntegerLattice := by
    change torusQuotient (affine a J Z - centeredLift y) ≠ 0
    rw [hquot]
    exact hZ
  have hfun : referenceGradient a J y = fun W ↦
      greenGradient (torusQuotient (affine a J W - centeredLift y)) := by
    funext W
    rw [quotient_affine_sub_centeredLift]
    rfl
  have hh := (hasFDerivAt_greenGradient_lift hx).comp Z
    ((hasFDerivAt_affine a J Z).sub_const (centeredLift y))
  have hmap : (greenHessianOperator (torusQuotient (affine a J Z - centeredLift y))).comp
      (J⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace) =
      J⁻¹ • greenHessianOperator (torusQuotient (affine a J Z) - y) := by
    rw [hquot]
    ext v
    simp
  rw [hfun]
  exact hh.congr_fderiv hmap

theorem norm_scaled_hessian_le {J R C₂ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    {z : Torus} (hz : R / J ≤ torusEuclideanNorm z) :
    ‖J⁻¹ • greenHessianOperator z‖ ≤ C₂ * J / R ^ 2 := by
  have hn := hk z (ne_zero_of_separation hJ hR hz)
  have hs : (R / J) ^ 2 ≤ torusEuclideanNorm z ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hR.le hJ.le) hz 2
  calc
    ‖J⁻¹ • greenHessianOperator z‖ = J⁻¹ * ‖greenHessianOperator z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hJ.le)]
    _ ≤ J⁻¹ * (C₂ / torusEuclideanNorm z ^ 2) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hJ.le)
    _ ≤ J⁻¹ * (C₂ / (R / J) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (sq_pos_of_pos (div_pos hR hJ)) hs)
        (inv_nonneg.mpr hJ.le)
    _ = _ := by field_simp [hJ.ne', hR.ne']

/-- The common sqrt(5) diameter handles both adjacent orientations and
also bounds a single cell. No condition is imposed on the source chart. -/
theorem reference_gradient_oscillation (b : Patch) (a : PlanarSpace) {J R C₂ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (y : Torus)
    (hsep : ∀ Z ∈ patchClosed b,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y))
    {Z W : PlanarSpace} (hZ : Z ∈ patchClosed b) (hW : W ∈ patchClosed b) :
    ‖referenceGradient a J y Z - referenceGradient a J y W‖ ≤
      Real.sqrt 5 * C₂ * J / R ^ 2 := by
  have hd (X : PlanarSpace) (hX : X ∈ patchClosed b) :=
    hasFDerivAt_referenceGradient a J y (ne_zero_of_separation hJ hR (hsep X hX))
  have hn (X : PlanarSpace) (hX : X ∈ patchClosed b) :
      ‖fderiv ℝ (referenceGradient a J y) X‖ ≤ C₂ * J / R ^ 2 := by
    rw [(hd X hX).fderiv]
    exact norm_scaled_hessian_le hJ hR hC hk (hsep X hX)
  have h := (convex_patchClosed b).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX ↦ (hd X hX).differentiableAt) hn hW hZ
  calc
    _ ≤ (C₂ * J / R ^ 2) * ‖Z - W‖ := h
    _ ≤ (C₂ * J / R ^ 2) * Real.sqrt 5 :=
      mul_le_mul_of_nonneg_left (norm_sub_patch_le_sqrt_five b hZ hW) (by positivity)
    _ = _ := by ring

/-- The geometric premise is the literal near-pair complement from the
particle-count argument; all source and target closures are actual cells. -/
theorem far_patch_gradient_oscillation {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (a c : MeshIndex J) (b d : Patch) (hfar : ¬ NearPair J hJ R a c b d)
    {y z z' : Torus} (hy : y ∈ closure (patchDomain J hJ c d))
    (hz : z ∈ closure (patchDomain J hJ a b))
    (hz' : z' ∈ closure (patchDomain J hJ a b)) :
    ‖greenGradient (z - y) - greenGradient (z' - y)‖ ≤
      Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2 := by
  rw [← chart_image_patchClosed] at hz hz'
  obtain ⟨Z, hZ, rfl⟩ := hz
  obtain ⟨W, hW, rfl⟩ := hz'
  have hs (V : PlanarSpace) (hV : V ∈ patchClosed b) :
      (R : ℝ) / J ≤ torusEuclideanNorm
        (torusQuotient (affine (meshTranslation J a) J V) - y) := by
    have hzV : meshChart J a V ∈ closure (patchDomain J hJ a b) := by
      rw [← chart_image_patchClosed]
      exact ⟨V, hV, rfl⟩
    simpa only [meshChart_eq_chart, GreenPointRescaling.chart] using
      far_patch_separation hJ a c b d hfar hzV hy
  have hh := reference_gradient_oscillation b (meshTranslation J a)
    (by exact_mod_cast hJ : (0 : ℝ) < J)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR) : (0 : ℝ) < R)
    hC hk y hs hZ hW
  simpa only [referenceGradient, meshChart_eq_chart, GreenPointRescaling.chart] using hh

/-- Integrate the same pairwise vector bound under two possibly different
probability laws. The coefficient stays one, with no total-variation loss. -/
theorem norm_integral_sub_integral_le_of_oscillation
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ ν : Measure A} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set A} {f : A → E} {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hosc : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ D) :
    ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤ D := by
  have hinner (x : A) (hx : x ∈ S) : ‖f x - ∫ y, f y ∂ν‖ ≤ D := by
    have hi : (∫ y, f x - f y ∂ν) = f x - ∫ y, f y ∂ν := by
      rw [integral_sub (integrable_const _) hfν, integral_const, probReal_univ, one_smul]
    rw [← hi]
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (hν.mono fun y hy ↦ hosc x hx y hy)
  have ho : (∫ x, f x - ∫ y, f y ∂ν ∂μ) = (∫ x, f x ∂μ) - ∫ y, f y ∂ν := by
    rw [integral_sub hfμ (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [← ho]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (hμ.mono fun x hx ↦ hinner x hx)

/-- Finite gradient integrals and their difference bound follow from the
actual far geometry and supported probability laws, without a density ratio. -/
theorem far_patch_gradient_expectations {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (a c : MeshIndex J) (b d : Patch) (hfar : ¬ NearPair J hJ R a c b d)
    {y : Torus} (hy : y ∈ closure (patchDomain J hJ c d))
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ z ∂μ, z ∈ closure (patchDomain J hJ a b))
    (hν : ∀ᵐ z ∂ν, z ∈ closure (patchDomain J hJ a b)) :
    Integrable (fun z ↦ greenGradient (z - y)) μ ∧
      Integrable (fun z ↦ greenGradient (z - y)) ν ∧
      ‖(∫ z, greenGradient (z - y) ∂μ) - ∫ z, greenGradient (z - y) ∂ν‖ ≤
        Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2 := by
  let D := Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2
  have hpair {z z' : Torus} (hz : z ∈ closure (patchDomain J hJ a b))
      (hz' : z' ∈ closure (patchDomain J hJ a b)) :
      ‖greenGradient (z - y) - greenGradient (z' - y)‖ ≤ D :=
    far_patch_gradient_oscillation hJ hR hC hk a c b d hfar hy hz hz'
  obtain ⟨z₀, hz₀⟩ := hμ.exists
  have hb (z : Torus) (hz : z ∈ closure (patchDomain J hJ a b)) :
      ‖greenGradient (z - y)‖ ≤ D + ‖greenGradient (z₀ - y)‖ := by
    calc
      _ = ‖(greenGradient (z - y) - greenGradient (z₀ - y)) + greenGradient (z₀ - y)‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖greenGradient (z - y) - greenGradient (z₀ - y)‖ + ‖greenGradient (z₀ - y)‖ :=
        norm_add_le _ _
      _ ≤ _ := add_le_add (hpair hz hz₀) le_rfl
  have hm : Measurable (fun z ↦ greenGradient (z - y)) :=
    measurable_greenGradient.comp (measurable_id.sub measurable_const)
  have hiμ : Integrable (fun z ↦ greenGradient (z - y)) μ :=
    (integrable_const (D + ‖greenGradient (z₀ - y)‖)).mono' hm.aestronglyMeasurable
      (hμ.mono fun z hz ↦ hb z hz)
  have hiν : Integrable (fun z ↦ greenGradient (z - y)) ν :=
    (integrable_const (D + ‖greenGradient (z₀ - y)‖)).mono' hm.aestronglyMeasurable
      (hν.mono fun z hz ↦ hb z hz)
  exact ⟨hiμ, hiν, norm_integral_sub_integral_le_of_oscillation hμ hν hiμ hiν
    (fun _ hz _ hz' ↦ hpair hz hz')⟩

theorem conditionalKernel_ae_closure {n J : ℕ} (hJ : 0 < J)
    {β₀ β : ℝ} (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hb : ConditionalLawEstimates.LawBounds hJ β₀ β i Y a b) :
    ∀ᵐ z ∂OneCoordinateConditionals.conditionalKernel (patchMeasure J hJ a b) i β Y,
      z ∈ closure (patchDomain J hJ a b) := by
  rw [hb.kernel_eq_raw]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_closure_patch J hJ a b)

/-- The two actual one-coordinate conditional laws of source Proposition
3.11 satisfy the sharp far-source estimate. Their supports and probability
normalizations follow from the actual capped-law theorem. -/
theorem capped_adjacent_gradient_expectations {n J : ℕ} {β β₀ δ C₂ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelOccupations.LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2)
    (hadm : LabelOccupations.AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η i a r)
    (Y : Configuration n)
    (hY : OneCoordinateConditionals.PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y)
    (j : Fin n)
    (hfar : ¬ NearPair J (ConditionalLawEstimates.mesh_pos hmesh)
      (ConditionalLawEstimates.radius β₀) a (η (i.succAbove j)) (.edge r) .cell) :
    let hJ := ConditionalLawEstimates.mesh_pos hmesh
    let μ := OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ a) i β Y
    let ν := OneCoordinateConditionals.conditionalKernel
      (meshCellMeasure J hJ (nextCell J hJ a r)) i β Y
    Integrable (fun z ↦ greenGradient (z - Y j)) μ ∧
      Integrable (fun z ↦ greenGradient (z - Y j)) ν ∧
      ‖(∫ z, greenGradient (z - Y j) ∂μ) - ∫ z, greenGradient (z - Y j) ∂ν‖ ≤
        Real.sqrt 5 * C₂ * J / (ConditionalLawEstimates.radius β₀ : ℝ) ^ 2 := by
  let hJ := ConditionalLawEstimates.mesh_pos hmesh
  let b := nextCell J hJ a r
  have hYa := (LabelRatioTransport.prescribedOutside_update_iff hJ η i a Y).mpr hY
  have ha := ConditionalLawEstimates.capped_patch_law hJ hβ hβ₀ hδ hmesh
    (Function.update η i a) hadm.1 i Y hYa a .cell
  have hb := ConditionalLawEstimates.capped_patch_law hJ hβ hβ₀ hδ hmesh
    (Function.update η i a) hadm.1 i Y hYa b .cell
  let μ := OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ a) i β Y
  let ν := OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ b) i β Y
  let : IsProbabilityMeasure μ := ha.probability
  let : IsProbabilityMeasure ν := hb.probability
  have hμ : ∀ᵐ z ∂μ, z ∈ closure (patchDomain J hJ a (.edge r)) := by
    apply (conditionalKernel_ae_closure hJ i Y a .cell ha).mono
    intro z hz
    apply (mem_closure_patch_iff J hJ a (.edge r) z).mpr
    exact ⟨a, by simp [patchCells], hz⟩
  have hν : ∀ᵐ z ∂ν, z ∈ closure (patchDomain J hJ a (.edge r)) := by
    apply (conditionalKernel_ae_closure hJ i Y b .cell hb).mono
    intro z hz
    apply (mem_closure_patch_iff J hJ a (.edge r) z).mpr
    exact ⟨b, by simp [b, patchCells], hz⟩
  exact far_patch_gradient_expectations hJ (ConditionalLawEstimates.radius_one_le β₀) hC hk a (η (i.succAbove j)) (.edge r) .cell
    hfar (hY j) μ ν hμ hν

end PeriodicAttractiveLogGas.GreenGradientOscillation
