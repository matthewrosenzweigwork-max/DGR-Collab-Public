import LeanResearch.PeriodicAttractiveLogGas.SchauderCompactImage
import LeanResearch.PeriodicAttractiveLogGas.ReferenceMapCompactness
import LeanResearch.PeriodicAttractiveLogGas.ReferenceMapInvariance

/-! The actual all-cell reference family in source Proposition
`prop:entropy-reference`, lines 2350--2391. Schauder is applied to the
released closed convex subset of the finite product of cell L1 spaces.
The resulting measures use the original occupation weights and Green
potential. No uniqueness of this reference family is asserted. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceFamilyExistence

open MeshCells LabelOccupations ReferenceResidual ReferenceSelfTerms
  ReferenceDensityChange ReferenceConvolutionContinuity ReferenceDensityDomain
  ReferenceMapInvariance

/-- Genuine fixed-point existence for the actual reference map in its
infinite-dimensional finite-product L1 ambient space. -/
theorem exists_fixedDensityFamily {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    ∃ φ : DensityFamily hJ,
      ∀ a, referenceMap (by omega : 0 < N) η hβ φ a = (φ a).val := by
  let f : ↥(admissibleDomain hJ) → ↥(admissibleDomain hJ) :=
    sourceMapOnDomain hN ht hβ hβ₀ hC hk hη hscale hsmall
  have hf : Continuous f :=
    continuous_sourceMapOnDomain hN ht hβ hβ₀ hC hk hη hscale hsmall
  have hc : IsCompact (closure (Set.range (fun x : ↥(admissibleDomain hJ) =>
      (f x : Ambient hJ)))) := by
    change IsCompact (closure (Set.range (fun x : ↥(admissibleDomain hJ) =>
      referenceMap (by omega : 0 < N) η hβ ((familyHomeomorph hJ).symm x))))
    exact ReferenceMapCompactness.isCompact_closure_referenceMap_domain (by omega) η hβ
  obtain ⟨x, hx⟩ := SchauderCompactImage.exists_fixedPoint
    (admissibleDomain_nonempty hJ) (admissibleDomain_isClosed hJ)
    (admissibleDomain_convex hJ) f hf hc
  refine ⟨(familyHomeomorph hJ).symm x, ?_⟩
  intro a
  exact congrFun (congrArg Subtype.val hx) a

/-- L1 equality gives equality of the genuine densities almost everywhere;
no pointwise identity of arbitrarily chosen Lp representatives is used. -/
theorem fixedDensity_ae {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (hfix : ∀ a, referenceMap hN η hβ φ a = (φ a).val) (a : MeshIndex J) :
    (φ a).val =ᵐ[meshCellMeasure J hJ a] referenceMapValue η β φ a := by
  have he := (referenceMapValue_memLp hN η hβ φ a).coeFn_toLp
  change referenceMap hN η hβ φ a =ᵐ[meshCellMeasure J hJ a]
    referenceMapValue η β φ a at he
  rw [hfix a] at he
  exact he

/-- The precise `hformula` interface used by the later entropy argument,
proved here from the fixed L1 classes on every cell. -/
theorem fixedDensity_formula {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (hfix : ∀ a, referenceMap hN η hβ φ a = (φ a).val) (a : MeshIndex J) :
    familyMeasures φ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential (familyMeasures φ) η z) /
        cellNormalizer hJ (familyMeasures φ) η β a)) := by
  apply withDensity_congr_ae
  filter_upwards [fixedDensity_ae hN η hβ φ hfix a] with z hz
  exact congrArg ENNReal.ofReal hz

/-- The precise `hdensity` interface, independent of whether the cell is
occupied. Its constants have no particle, mesh, or temperature dependence. -/
theorem fixedDensity_bounds {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (hfix : ∀ a, referenceMap hN η hβ φ a = (φ a).val) (a : MeshIndex J) :
    ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential (familyMeasures φ) η z) /
        cellNormalizer hJ (familyMeasures φ) η β a ∧
      Real.exp (β * averagePotential (familyMeasures φ) η z) /
        cellNormalizer hJ (familyMeasures φ) η β a ≤ Real.exp 1 := by
  filter_upwards [fixedDensity_ae hN η hβ φ hfix a, (φ a).property.1] with z hz hb
  simpa only [hz, referenceMapValue] using hb

/-- The laws represented by the density family are supported on the actual
half-open mesh cells, not only on their closures. -/
theorem familyMeasures_ae_mem_cell {J : ℕ} {hJ : 0 < J} (φ : DensityFamily hJ)
    (a : MeshIndex J) : ∀ᵐ z ∂familyMeasures φ a, z ∈ meshCell J hJ a :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_meshCell J hJ a)

/-- At each fixed pole the original and regular Green representatives agree
almost everywhere for the actual occupation mixture. -/
theorem mixture_green_ae {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ)
    (x : Torus) :
    greenKernel x =ᵐ[mixture η φ] fun y => greenRealRepresentative (x - y) := by
  have hac : mixture η φ ≪ torusMeasure := Measure.absolutelyContinuous_of_le_smul
    (mixture_le_haar hN hη φ)
  exact hac.ae_le ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    regularGreenRepresentative_ae)

/-- Actual finite and positive cell normalizers are established before any
normalized-density formula is used. -/
theorem family_cellNormalizer {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) :
    Integrable (fun z => Real.exp (β * averagePotential (familyMeasures φ) η z))
      (meshCellMeasure J hJ a) ∧
    0 < cellNormalizer hJ (familyMeasures φ) η β a := by
  have hh := ReferencePotentialBounds.cell_exponential_normalizer hJ hN (familyMeasures φ)
    (fun b => (φ b).law_le) η hβ a
  exact ⟨hh.1, hh.2.1⟩

/-- The same normalization assertions for the literal original Green
convolution. Equality of the two potentials holds at every pole, after
integration under the genuine absolutely continuous mixture. -/
theorem family_original_cellNormalizer {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η)
    {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ) (a : MeshIndex J) :
    Integrable (fun z => Real.exp (β *
      (∫ y, greenRealRepresentative (z - y) ∂mixture η φ))) (meshCellMeasure J hJ a) ∧
    0 < ∫ z, Real.exp (β * (∫ y, greenRealRepresentative (z - y) ∂mixture η φ))
      ∂meshCellMeasure J hJ a := by
  simp_rw [(mixture_original_green hN hη φ _).2]
  exact family_cellNormalizer hN η hβ φ a

/-- The fixed point gives precisely the normalized original Green
convolution, including on unoccupied cells. -/
theorem fixedDensity_original_formula {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η)
    {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (hfix : ∀ a, referenceMap hN η hβ φ a = (φ a).val) (a : MeshIndex J) :
    familyMeasures φ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * (∫ y, greenRealRepresentative (z - y) ∂mixture η φ)) /
        (∫ w, Real.exp (β * (∫ y, greenRealRepresentative (w - y) ∂mixture η φ))
          ∂meshCellMeasure J hJ a))) := by
  simp_rw [(mixture_original_green hN hη φ _).2]
  exact fixedDensity_formula hN η hβ φ hfix a

/-- All-cell source existence with explicit probability, support,
occupation-mixture and original-Green identities. The two density predicates
are exactly the previously explicit entropy interfaces, now supplied by a
genuine fixed point rather than assumed. -/
theorem exists_referenceFamily {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    ∃ μ : MeshIndex J → Measure Torus, ∃ ρ : Measure Torus,
      (∀ a, IsProbabilityMeasure (μ a)) ∧
      (∀ a, ∀ᵐ z ∂μ a, z ∈ meshCell J hJ a) ∧
      ρ = ∑ a, ENNReal.ofReal (occupationWeight η a) • μ a ∧
      IsProbabilityMeasure ρ ∧
      ρ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ)^2) • torusMeasure ∧
      (∀ z, Integrable (greenKernel z) ρ ∧
        Integrable (fun y => greenRealRepresentative (z - y)) ρ ∧
        greenKernel z =ᵐ[ρ] (fun y => greenRealRepresentative (z - y)) ∧
        potential ρ z = averagePotential μ η z ∧
        (∫ y, greenRealRepresentative (z - y) ∂ρ) = averagePotential μ η z) ∧
      (∀ a, Integrable (fun z => Real.exp (β * averagePotential μ η z))
        (meshCellMeasure J hJ a) ∧ 0 < cellNormalizer hJ μ η β a) ∧
      (∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
        ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) ∧
      (∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
        Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
        Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1) ∧
      (∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
        ENNReal.ofReal (Real.exp (β * (∫ y, greenRealRepresentative (z - y) ∂ρ)) /
          (∫ w, Real.exp (β * (∫ y, greenRealRepresentative (w - y) ∂ρ))
            ∂meshCellMeasure J hJ a)))) := by
  obtain ⟨φ, hfix⟩ := exists_fixedDensityFamily (hJ := hJ) hN ht hβ hβ₀ hC hk hη hscale hsmall
  refine ⟨familyMeasures φ, mixture η φ, fun a => inferInstance,
    familyMeasures_ae_mem_cell φ, rfl, mixture_probability (by omega) η φ,
    mixture_le_haar (by omega) hη φ, ?_, family_cellNormalizer (by omega) η hβ φ,
    fixedDensity_formula (by omega) η hβ φ hfix,
    fixedDensity_bounds (by omega) η hβ φ hfix,
    fixedDensity_original_formula (by omega) hη hβ φ hfix⟩
  intro z
  exact ⟨mixture_green_integrable η φ z, (mixture_original_green (by omega) hη φ z).1,
    mixture_green_ae (by omega) hη φ z, potential_mixture_eq_averagePotential η φ z,
    (mixture_original_green (by omega) hη φ z).2⟩

/-- In particular, the previously explicit entropy-reference assumptions
have an actual witness for the single already chosen kernel constant.
The stronger microscopic and subcritical source hypotheses are unnecessary
for this isolated existence step; every allowed source parameter is included. -/
theorem exists_sourceReferenceFamily {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    {η : LabelVector J N} (hη : OccupationCap t η)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * ConditionalLawEstimates.kernelConstant *
      Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    ∃ μ : MeshIndex J → Measure Torus, ∃ ρ : Measure Torus,
      (∀ a, IsProbabilityMeasure (μ a)) ∧
      (∀ a, ∀ᵐ z ∂μ a, z ∈ meshCell J hJ a) ∧
      ρ = ∑ a, ENNReal.ofReal (occupationWeight η a) • μ a ∧
      IsProbabilityMeasure ρ ∧
      ρ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ)^2) • torusMeasure ∧
      (∀ z, Integrable (greenKernel z) ρ ∧
        Integrable (fun y => greenRealRepresentative (z - y)) ρ ∧
        greenKernel z =ᵐ[ρ] (fun y => greenRealRepresentative (z - y)) ∧
        potential ρ z = averagePotential μ η z ∧
        (∫ y, greenRealRepresentative (z - y) ∂ρ) = averagePotential μ η z) ∧
      (∀ a, Integrable (fun z => Real.exp (β * averagePotential μ η z))
        (meshCellMeasure J hJ a) ∧ 0 < cellNormalizer hJ μ η β a) ∧
      (∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
        ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) ∧
      (∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
        Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
        Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1) ∧
      (∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
        ENNReal.ofReal (Real.exp (β * (∫ y, greenRealRepresentative (z - y) ∂ρ)) /
          (∫ w, Real.exp (β * (∫ y, greenRealRepresentative (w - y) ∂ρ))
            ∂meshCellMeasure J hJ a)))) :=
  exists_referenceFamily hN ht hβ hβ₀ ConditionalLawEstimates.kernelConstant_pos.le
    ConditionalLawEstimates.kernel_gradient_bound hη hscale hsmall

/-- At zero inverse temperature the literal normalized cell laws themselves
satisfy every cell formula and bound. No fixed-point choice, positive lower
bound on beta, cap, or resolution restriction is needed for this witness. -/
theorem uniform_reference_zero {J N : ℕ} (hJ : 0 < J) (η : LabelVector J N) :
    (∀ a : MeshIndex J, IsProbabilityMeasure (meshCellMeasure J hJ a)) ∧
    (∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a, z ∈ meshCell J hJ a) ∧
    (∀ a, Integrable (fun z => Real.exp (0 * averagePotential (meshCellMeasure J hJ) η z))
      (meshCellMeasure J hJ a) ∧ 0 < cellNormalizer hJ (meshCellMeasure J hJ) η 0 a) ∧
    (∀ a, meshCellMeasure J hJ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (0 * averagePotential (meshCellMeasure J hJ) η z) /
        cellNormalizer hJ (meshCellMeasure J hJ) η 0 a))) ∧
    (∀ a z, Real.exp (-1) ≤
      Real.exp (0 * averagePotential (meshCellMeasure J hJ) η z) /
        cellNormalizer hJ (meshCellMeasure J hJ) η 0 a ∧
      Real.exp (0 * averagePotential (meshCellMeasure J hJ) η z) /
        cellNormalizer hJ (meshCellMeasure J hJ) η 0 a ≤ Real.exp 1) := by
  refine ⟨fun a => inferInstance, ae_mem_meshCell J hJ, ?_, ?_, ?_⟩
  · intro a
    constructor
    · simpa only [zero_mul, Real.exp_zero] using
        (integrable_const (μ := meshCellMeasure J hJ a) (1 : ℝ))
    · simp [cellNormalizer]
  · intro a
    simp [cellNormalizer]
  · intro a z
    simp [cellNormalizer]

/-- Every beta-zero instance of the already-used formula agrees
with the explicit uniform witness. This also identifies the measures returned
by the existence theorem at beta zero. -/
theorem zero_formula_eq_uniform {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) (η : LabelVector J N)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (0 * averagePotential μ η z) / cellNormalizer hJ μ η 0 a))) :
    μ = meshCellMeasure J hJ := by
  funext a
  simpa [cellNormalizer] using hformula a

/-- The exact occupation mixture of the explicit uniform reference is a
probability for every positive particle count. Empty cells have weight zero. -/
theorem uniform_mixture_probability {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (η : LabelVector J N) : IsProbabilityMeasure
      (∑ a, ENNReal.ofReal (occupationWeight η a) • meshCellMeasure J hJ a) := by
  constructor
  simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => occupationWeight_nonneg η a),
    sum_occupationWeight hN η, ENNReal.ofReal_one]

/-- In particular, the mixture in the proved source package specializes
to the literal uniform-cell occupation mixture when beta is zero. -/
theorem zero_mixture_eq_uniform {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) (η : LabelVector J N) (ρ : Measure Torus)
    (hmix : ρ = ∑ a, ENNReal.ofReal (occupationWeight η a) • μ a)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (0 * averagePotential μ η z) / cellNormalizer hJ μ η 0 a))) :
    ρ = ∑ a, ENNReal.ofReal (occupationWeight η a) • meshCellMeasure J hJ a := by
  rw [hmix, zero_formula_eq_uniform hJ μ η hformula]

end PeriodicAttractiveLogGas.ReferenceFamilyExistence
