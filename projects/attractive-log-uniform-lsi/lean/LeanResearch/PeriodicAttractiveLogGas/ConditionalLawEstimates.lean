import LeanResearch.PeriodicAttractiveLogGas.OneCoordinateConditionals

/-! Assembly of source Proposition 3.4. The single
kernel constant below is chosen from the proved Green bounds before any
coupling, particle count, mesh, label or source position is introduced.
The law records include the literal source density, all finite centered
moments, actual ordinary-gradient integrability, and the exact P*, L*, S*.
The final joint-law identities reuse the proved nonnegative-observable
disintegration. No formula for a smaller Gibbs marginal is asserted. -/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.ConditionalLawEstimates

open MeshCells MeshAdjacentCells CellRestrictions GreenPointWeights
  LabelOccupations ConditionalParameters LocalPointEstimates OneCoordinateConditionals

/-- One valid common choice for the source constants C₀ and C₁. -/
theorem exists_commonKernelConstant :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : Torus, z ≠ 0 →
        |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C) ∧
      GreenFarOscillation.KernelGradientBound C := by
  obtain ⟨C, hC, h⟩ := exists_regularGreenRepresentative_torus_bounds
  exact ⟨C, hC, fun z hz ↦ (h z hz).1, fun z hz ↦ (h z hz).2.1⟩

def kernelConstant : ℝ := Classical.choose exists_commonKernelConstant

theorem kernelConstant_pos : 0 < kernelConstant :=
  (Classical.choose_spec exists_commonKernelConstant).1

theorem kernel_log_bound (z : Torus) (hz : z ≠ 0) :
    |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ kernelConstant :=
  (Classical.choose_spec exists_commonKernelConstant).2.1 z hz

theorem kernel_gradient_bound : GreenFarOscillation.KernelGradientBound kernelConstant :=
  (Classical.choose_spec exists_commonKernelConstant).2.2

def radius (β₀ : ℝ) : ℕ := nearRadius β₀ kernelConstant

def occupationBound (β₀ : ℝ) : ℝ := fixedDelta β₀ kernelConstant kernelConstant

def lowerBound (β₀ : ℝ) : ℝ := fixedLower β₀ kernelConstant kernelConstant

def densityNormBound (β₀ : ℝ) : ℝ := fixedNorm β₀ kernelConstant kernelConstant

def poincareBound (β₀ : ℝ) : ℝ :=
  OneSiteConstants.poincare (lowerBound β₀) (densityNormBound β₀)

def entropyBound (β₀ : ℝ) : ℝ :=
  OneSiteConstants.logSobolev (lowerBound β₀) (densityNormBound β₀)

def fourthMomentBound (β₀ : ℝ) : ℝ :=
  OneSiteConstants.fourthMoment (lowerBound β₀) (densityNormBound β₀)

theorem radius_one_le (β₀ : ℝ) : 1 ≤ radius β₀ := nearRadius_one_le _ _

theorem radius_eq_source (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    (radius β₀ : ℤ) = max 1 ⌈4 * Real.sqrt 5 * β₀ * kernelConstant⌉ :=
  nearRadius_int_eq hβ₀ kernelConstant_pos.le

theorem chosen_parameters (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    0 < occupationBound β₀ ∧ occupationBound β₀ ≤ 1 / 2 ∧
      β₀ * (2 * (radius β₀ : ℝ) + 2) ^ 2 * occupationBound β₀ ≤ 1 / 16 ∧
      4 * β₀ * (2 * (radius β₀ : ℝ) + 5) ^ 2 * occupationBound β₀ *
        densityNormBound β₀ * (PoleLogMoments.lambdaStar (radius β₀) + kernelConstant) ≤ 1 / 4 :=
  fixedDelta_bounds hβ₀ kernelConstant_pos.le

theorem lowerBound_pos (β₀ : ℝ) : 0 < lowerBound β₀ :=
  sourceLowerConstant_pos
    (lt_of_lt_of_le zero_lt_one (distanceBound_one_le (radius_one_le β₀))) _ _

theorem densityNormBound_pos (β₀ : ℝ) : 0 < densityNormBound β₀ :=
  sourceNormConstant_pos
    (lt_of_lt_of_le zero_lt_one (distanceBound_one_le (radius_one_le β₀))) _ _

theorem chosen_far_oscillation (β₀ : ℝ) :
    oscillationBound β₀ kernelConstant (radius β₀) ≤ 1 / 4 :=
  oscillationBound_nearRadius_le _ _

theorem mesh_pos {β₀ : ℝ} {J : ℕ} (hmesh : 8 * (radius β₀ + 4) ≤ J) : 0 < J := by
  omega

theorem mesh_three_le {β₀ : ℝ} {J : ℕ} (hmesh : 8 * (radius β₀ + 4) ≤ J) : 3 ≤ J := by
  omega

theorem mesh_two_le {β₀ : ℝ} {J : ℕ} (hmesh : 8 * (radius β₀ + 4) ≤ J) : 2 ≤ J :=
  (by norm_num : 2 ≤ 3).trans (mesh_three_le hmesh)

@[simp] theorem occupationBound_zero : occupationBound 0 = 1 / 2 := fixedDelta_zero _ _

/-- The literal source density relative to its actual normalized patch measure. -/
def rawDensity {n : ℕ} (μ : Measure Torus) (β : ℝ) (Y : Configuration n) (z : Torus) : ℝ :=
  rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ

/-- All finite gates and the full source moment family are part of the
conclusion. The gradient is the actual physical Euclidean ordinary gradient. -/
structure FunctionEstimates (β₀ : ℝ) (J : ℕ) (b : Patch) (ν : Measure Torus)
    (f : Torus → ℝ) : Prop where
  function_memLp : ∀ r : ℝ≥0∞, MemLp f r ν
  gradient_memLp : ∀ r : ℝ≥0∞, MemLp (torusOrdinaryGradient f) r ν
  integrable_function : Integrable f ν
  integrable_square : Integrable (fun z ↦ f z ^ 2) ν
  integrable_energy : Integrable (fun z ↦ ‖torusOrdinaryGradient f z‖ ^ 2) ν
  integrable_log_square : Integrable (fun z ↦ f z ^ 2 * Real.log (f z ^ 2)) ν
  rectangle_estimates : TorusPatchDensity.Estimates
    (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) J
    (lowerBound β₀) 4 (densityNormBound β₀) ν f
  uniform_variance : ProbabilityTheory.variance f ν ≤ (poincareBound β₀ / (J : ℝ) ^ 2) *
    (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν)
  uniform_entropy : entropy ν (fun z ↦ f z ^ 2) ≤
    (((entropyBound β₀ / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) : ℝ) : EReal)
  fourth_memLp : MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν
  uniform_fourth : lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ≤
    (fourthMomentBound β₀ / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν

/-- The exact coefficient from Lemma 3.2 for every finite real s ≥ 2,
with the patch's own rectangle Sobolev constant and physical J⁻¹ scaling. -/
theorem FunctionEstimates.centered_moment {β₀ : ℝ} {J : ℕ} {b : Patch}
    {ν : Measure Torus} {f : Torus → ℝ} (h : FunctionEstimates β₀ J b ν f)
    (s : ℝ) (hs : 2 ≤ s) :
    MemLp (fun z ↦ f z - ∫ w, f w ∂ν) (ENNReal.ofReal s) ν ∧
      lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) (ENNReal.ofReal s) ν ≤
        ((2 * densityNormBound β₀ ^ (1 / s) *
          RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b)) (s * (4 / 3)) *
          lowerBound β₀ ^ (-1 / 2 : ℝ)) / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν := by
  simpa only [DensityEntropy.momentConstant, show (4 : ℝ) - 1 = 3 by norm_num] using
    h.rectangle_estimates.2.2.2.2 s hs

theorem pointLaw_functionEstimates {n J : ℕ} (hJ : 0 < J) (β₀ β : ℝ)
    (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hprob : IsProbabilityMeasure
      (pointLaw (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ))))
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b)))
    (hlocal : TorusPatchDensity.Estimates
      (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) J
      (lowerBound β₀) 4 (densityNormBound β₀)
      (pointLaw (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ))) f) :
    FunctionEstimates β₀ J b
      (pointLaw (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ))) f := by
  let p := pointDensity (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ))
  have he : TorusPatchDensity.law (shape b) J hJ a p =
      pointLaw (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ)) := by
    rw [TorusPatchDensity.law, baseMeasure_shape]
    rfl
  let hprob' : IsProbabilityMeasure (TorusPatchDensity.law (shape b) J hJ a p) := by
    rw [he]
    exact hprob
  have hfinite := TorusPatchDensity.density_finite (shape b) J hJ a p hf
  rw [he] at hfinite
  have hu := OneSiteConstants.uniform_estimates hJ b
    (lowerBound_pos β₀).le (densityNormBound_pos β₀).le hlocal
  exact ⟨hfinite.1, hfinite.2.1, hfinite.2.2.1, hfinite.2.2.2.1,
    hfinite.2.2.2.2.1, hfinite.2.2.2.2.2, hlocal, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩

/-- Source-facing properties of the actual Markov conditional version at
one fixed outside placement. No separation of its source positions is required. -/
structure LawBounds {n J : ℕ} (hJ : 0 < J) (β₀ β : ℝ) (i : Fin (n + 1))
    (Y : Configuration n) (a : MeshIndex J) (b : Patch) : Prop where
  regular_integrable : Integrable (OneCoordinateConditionals.sourceWeight β Y) (patchMeasure J hJ a b)
  regular_normalizer_pos : 0 < ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂patchMeasure J hJ a b
  raw_integrable : Integrable (rawSourceWeight β Y) (patchMeasure J hJ a b)
  raw_normalizer_pos : 0 < ∫ z, rawSourceWeight β Y z ∂patchMeasure J hJ a b
  kernel_eq_raw : conditionalKernel (patchMeasure J hJ a b) i β Y =
    (patchMeasure J hJ a b).withDensity
      (fun z ↦ ENNReal.ofReal (rawDensity (patchMeasure J hJ a b) β Y z))
  kernel_eq_pointLaw : conditionalKernel (patchMeasure J hJ a b) i β Y =
    pointLaw (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ))
  kernel_eq_restricted_haar : conditionalKernel (patchMeasure J hJ a b) i β Y =
    ProbabilityTheory.cond ((torusMeasure.restrict (patchDomain J hJ a b)).withDensity
      (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z))) univ
  probability : IsProbabilityMeasure (conditionalKernel (patchMeasure J hJ a b) i β Y)
  density_memLp : MemLp (rawDensity (patchMeasure J hJ a b) β Y) 4 (patchMeasure J hJ a b)
  density_lower : ∀ᵐ z ∂patchMeasure J hJ a b,
    lowerBound β₀ ≤ rawDensity (patchMeasure J hJ a b) β Y z
  density_norm : lpNorm (rawDensity (patchMeasure J hJ a b) β Y) 4
    (patchMeasure J hJ a b) ≤ densityNormBound β₀
  estimates : ∀ {f : Torus → ℝ} {L : ℝ≥0},
    PhysicalLipschitzOn L f (closure (patchDomain J hJ a b)) →
      FunctionEstimates β₀ J b (conditionalKernel (patchMeasure J hJ a b) i β Y) f

/-- This transfer uses the proved Haar-a.e. representative identity for
every fixed source tuple, including coincident tuples. -/
theorem pointDensity_ae_rawDensity {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (β : ℝ) (Y : Configuration n) :
    pointDensity (patchMeasure J hJ a b) Y (fun _ ↦ β / (n + 1 : ℕ)) =ᵐ[patchMeasure J hJ a b]
      rawDensity (patchMeasure J hJ a b) β Y := by
  have hae := (patchMeasure_absolutelyContinuous J hJ hJ2 a b).ae_le
    (sourceWeight_ae_rawSourceWeight β Y)
  have hint := integral_congr_ae hae
  filter_upwards [hae] with z hz
  change OneCoordinateConditionals.sourceWeight β Y z /
      (∫ u, OneCoordinateConditionals.sourceWeight β Y u ∂patchMeasure J hJ a b) =
    rawSourceWeight β Y z / (∫ u, rawSourceWeight β Y u ∂patchMeasure J hJ a b)
  rw [hint, hz]

/-- The completed occupation cap supplies all analytic premises through
the actual Green estimates. Smaller caps use exactly the same constants. -/
theorem capped_patch_law {n J : ℕ} (hJ : 0 < J) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) : LawBounds hJ β₀ β i Y a b := by
  have hη' : OccupationCap (fixedDelta β₀ kernelConstant kernelConstant) η := hη.mono hδ
  have hb := capped_source_bounds hJ hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le
    kernel_log_bound kernel_gradient_bound hmesh η hη' i Y hY a b
  have hraw := capped_conditional_formula hJ (mesh_two_le hmesh) hβ hβ₀
    kernelConstant_pos.le kernelConstant_pos.le kernel_log_bound kernel_gradient_bound
    hmesh η hη' i Y hY a b
  have hden := pointDensity_ae_rawDensity hJ (mesh_two_le hmesh) a b β Y
  refine ⟨hb.1, hb.2.1, hraw.1, hraw.2.1, hraw.2.2.1, hraw.2.2.2,
    conditionalKernel_eq_restricted_source hJ (mesh_two_le hmesh) i β Y a b hb.1,
    ?_, (memLp_congr_ae hden).mp hb.2.2.2.1, ?_, ?_, ?_⟩
  · rw [hraw.2.2.2]
    exact hb.2.2.1
  · filter_upwards [hb.2.2.2.2.1, hden] with z hz he
    exact he ▸ hz
  · change (eLpNorm (rawDensity (patchMeasure J hJ a b) β Y) 4
      (patchMeasure J hJ a b)).toReal ≤ _
    rw [← eLpNorm_congr_ae hden]
    exact hb.2.2.2.2.2
  · intro f L hf
    have hlocal := pointLaw_estimates hJ a b Y (fun _ ↦ β / (n + 1 : ℕ))
      (lowerBound_pos β₀) hb.2.2.1 hb.2.2.2.2.1 hb.2.2.2.1 hb.2.2.2.2.2 hf
    rw [hraw.2.2.2]
    exact pointLaw_functionEstimates hJ β₀ β Y a b hb.2.2.1 hf hlocal

/-- Literal specified-label assembly: the all-closed-placement law bounds
and the actual conditional-version identity under the specified-label law.
The particle count is N=n+1; hN is exactly the source gate N≥2. -/
theorem label_conditionals {n J : ℕ} {β β₀ δ : ℝ} (hN : 2 ≤ n + 1)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i : Fin (n + 1)) :
    (∀ Y : Configuration n, PrescribedOutside (mesh_pos hmesh) η i Y →
      LawBounds (mesh_pos hmesh) β₀ β i Y (η i) .cell) ∧
    (∀ F : Configuration (n + 1) → ℝ≥0∞, Measurable F →
      (∫⁻ X, F X ∂labelGibbsMeasure (mesh_pos hmesh) η β) =
        ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
          ∂(meshCellMeasure J (mesh_pos hmesh) (η i)).withDensity
            (fun z ↦ ENNReal.ofReal
              (rawDensity (meshCellMeasure J (mesh_pos hmesh) (η i)) β Y z))
          ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) := by
  constructor
  · intro Y hY
    exact capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell
  · intro F hF
    exact lintegral_label_raw_conditionals (mesh_pos hmesh) (mesh_two_le hmesh) hN
      hβ hβ₀ (hβ₀.trans_lt hsub) kernelConstant_pos.le kernelConstant_pos.le
      kernel_log_bound kernel_gradient_bound hmesh η (hη.mono hδ) i hF

/-- All coordinates of an admissible adjacent-cell restriction are covered.
In particular i and t are independent indices: the variable coordinate need
not be the coordinate whose allowed domain is the adjacent-cell union. -/
theorem adjacent_conditionals {n J : ℕ} {β β₀ δ : ℝ} (hN : 2 ≤ n + 1)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a d) :
    (∀ Y : Configuration n,
      PatchOutside (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t d) i Y →
        LawBounds (mesh_pos hmesh) β₀ β i Y
          (Function.update η t a i) (adjacentShapes t d i)) ∧
    (∀ F : Configuration (n + 1) → ℝ≥0∞, Measurable F →
      let P := twoCellGibbsMeasure (mesh_pos hmesh) η t a (nextCell J (mesh_pos hmesh) a d) β
      let μ := patchMeasure J (mesh_pos hmesh) (Function.update η t a i) (adjacentShapes t d i)
      (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
        ∂μ.withDensity (fun z ↦ ENNReal.ofReal (rawDensity μ β Y z))
        ∂Measure.map (removeSite i) P) := by
  constructor
  · intro Y hY
    obtain ⟨ζ, hζ, hYζ⟩ := exists_capped_adjacent_outside (mesh_pos hmesh) η t i a d hadm Y hY
    exact capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh ζ hζ i Y hYζ
      (Function.update η t a i) (adjacentShapes t d i)
  · intro F hF
    have hadm' : AdjacentAdmissible (mesh_pos hmesh)
        (fixedDelta β₀ kernelConstant kernelConstant) η t a d :=
      ⟨hadm.1.mono hδ, hadm.2.mono hδ⟩
    exact lintegral_twoCell_raw_conditionals (mesh_pos hmesh) (mesh_two_le hmesh) hN
      hβ hβ₀ (hβ₀.trans_lt hsub) kernelConstant_pos.le kernelConstant_pos.le
      kernel_log_bound kernel_gradient_bound hmesh η t i a d hadm' hF

/-- The i≠t case really uses the single prescribed cell for coordinate i. -/
theorem adjacent_measure_of_ne {N J : ℕ} (hJ : 0 < J) (η : LabelVector J N)
    (t i : Fin N) (a : MeshIndex J) (d : Fin 2) (hit : i ≠ t) :
    patchMeasure J hJ (Function.update η t a i) (adjacentShapes t d i) =
      meshCellMeasure J hJ (η i) := by
  simp only [Function.update_of_ne hit, adjacentShapes, patchMeasure]

theorem adjacent_measure_self {N J : ℕ} (hJ : 0 < J) (η : LabelVector J N)
    (t : Fin N) (a : MeshIndex J) (d : Fin 2) :
    patchMeasure J hJ (Function.update η t a t) (adjacentShapes t d t) =
      edgeCellMeasure J hJ a d := by
  simp only [Function.update_self, adjacentShapes, patchMeasure]

/-- The probe holds every outside source fixed. Every allowed completion,
including both endpoints for an edge patch, is required capped. This is
an actual one-variable law, with no assertion about an integrated marginal. -/
theorem probe_law {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible δ η i (allowedPatchLabels (mesh_pos hmesh) a b))
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    LawBounds (mesh_pos hmesh) β₀ β i Y a b := by
  obtain ⟨ζ, hζ, hYζ⟩ := exists_capped_probe_outside (mesh_pos hmesh) η i a b hadm Y hY
  exact capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh ζ hζ i Y hYζ a b

/-- The zero-coupling endpoint is the actual normalized patch measure. -/
theorem zero_coupling_law {n J : ℕ} (hJ : 0 < J) (i : Fin (n + 1))
    (Y : Configuration n) (a : MeshIndex J) (b : Patch) :
    conditionalKernel (patchMeasure J hJ a b) i 0 Y = patchMeasure J hJ a b :=
  conditionalKernel_zero _ i Y

@[simp] theorem rawDensity_zero {n J : ℕ} (hJ : 0 < J) (Y : Configuration n)
    (a : MeshIndex J) (b : Patch) (z : Torus) :
    rawDensity (patchMeasure J hJ a b) 0 Y z = 1 := by
  simp only [rawDensity, rawSourceWeight_zero, integral_const, probReal_univ, one_smul, div_one]

end PeriodicAttractiveLogGas.ConditionalLawEstimates
