import DGRHS.Gaussian.PeriodicHeatFeatureGram

/-! Actual jointly measurable full heat Gaussian evaluation. The countable
Gaussian product and the feature isometry are constructed; no infinite
standard Gaussian measure on the feature Hilbert space is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology InnerProductSpace ENNReal
namespace DGRHS.Gaussian

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- Keep the actual linear isometry together with its measurable representative,
so every finite spatial sum can subsequently be identified in L2. -/
theorem exists_separable_featureGaussian_isometry_representative
    {k : X → H} (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ) :
    ∃ W : H →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian,
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ h : H, IsonormalProcess.iidStdGaussian.map (W h) =
        gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2))) ∧
      (∀ h h' : H, (∫ ω, W h ω * W h' ω ∂IsonormalProcess.iidStdGaussian) =
        inner ℝ h h') ∧
      ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian] W (k x) := by
  obtain ⟨s,b,_⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  let f : s ↪ ℕ := countableGaussianIndex
  obtain ⟨g,hg,hg2,hW,_⟩ := exists_featureGaussian_representative b f f.injective hk.measurable hk2
  exact ⟨indexedGaussianIsometry b f f.injective,g,hg,hg2,
    map_indexedGaussianIsometry_eq_gaussianReal b f f.injective,
    indexedGaussianIsometry_cov b f f.injective,hW⟩

end DGRHS.Gaussian
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The canonical countable complex Hilbert basis has dense separable span;
this proves separability of the same underlying real Hilbert space. -/
instance periodicHeatFeatureSpace_separable :
    TopologicalSpace.SeparableSpace (PeriodicHeatFeatureSpace ι) := by
  let b : HilbertBasis (PeriodicFrequency ι) ℂ (PeriodicHeatFeatureSpace ι) := default
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range b) : Set (PeriodicHeatFeatureSpace ι)) :=
    (Set.countable_range b).isSeparable.span
  have hd : Dense (Submodule.span ℂ (Set.range b) : Set (PeriodicHeatFeatureSpace ι)) := by
    rw [dense_iff_closure_eq]
    change ((Submodule.span ℂ (Set.range b)).topologicalClosure : Set (PeriodicHeatFeatureSpace ι))=Set.univ
    rw [b.dense_span]
    rfl
  exact hd.isSeparable_iff.mp hs

/-- Full heat field and genuine covariance realization for every positive heat
parameter. Its feature and all covariance constants are fixed explicitly. -/
theorem exists_periodicHeatGaussianField (τ : ℝ) (hτ : 0<τ) :
    ∃ W : PeriodicHeatFeatureSpace ι →ₗᵢ[ℝ] Lp ℝ 2 IsonormalProcess.iidStdGaussian,
    ∃ g : PeriodicTorus ι × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 ((periodicHaar ι).prod IsonormalProcess.iidStdGaussian) ∧
      (∀ h : PeriodicHeatFeatureSpace ι, IsonormalProcess.iidStdGaussian.map (W h) =
        gaussianReal 0 (Real.toNNReal (‖h‖ ^ 2))) ∧
      (∀ x y : PeriodicTorus ι,
        (∫ ω, W (periodicHeatFeature τ hτ x) ω * W (periodicHeatFeature τ hτ y) ω
          ∂IsonormalProcess.iidStdGaussian)=periodicHeatFourierKernel τ (x-y)) ∧
      ∀ᵐ x ∂periodicHaar ι, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        W (periodicHeatFeature τ hτ x) := by
  borelize ↥(PeriodicHeatFeatureSpace ι)
  obtain ⟨W,g,hg,hg2,hLaw,hCov,hW⟩ :=
    DGRHS.Gaussian.exists_separable_featureGaussian_isometry_representative
      (periodicHeatFeature_continuous (ι := ι) τ hτ).stronglyMeasurable
      (periodicHeatFeature_memLp τ hτ)
  refine ⟨W,g,hg,hg2,hLaw,?_,hW⟩
  intro x y
  rw [hCov,periodicHeatFeature_gram]

end DGRHS.Periodic
#print axioms DGRHS.Gaussian.exists_separable_featureGaussian_isometry_representative
#print axioms DGRHS.Periodic.exists_periodicHeatGaussianField
#check @DGRHS.Periodic.exists_periodicHeatGaussianField
