import DGRHS.Gaussian.FeatureRateSourceKernel
import DGRHS.Kernel.SpectralMultiplicityLabels
import DGRHS.Kernel.RegularizedDeterminantNonzero

/-! Actual source-operator spectral labels. Unchanged checked root helpers are
reused with provenance in records/gaussian/rate-provenance/source-spectrum.
Nonzero finite multiplicities and the label equivalence are DERIVED from the
same compact symmetric operator. Genuine HasProd convergence is transported,
including zero labels, rather than comparing totalized products alone. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma sourceKernel_integralOperator_isSymmetric (h : X × X → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (heq : h =ᵐ[μ.prod μ] featureKernel k) :
    (DGRHS.Kernel.integralOperator h hh).toLinearMap.IsSymmetric := by
  rw [integralOperator_eq_of_ae_kernel hh (memLp_featureKernel k hk hk2) heq]
  exact DGRHS.Kernel.integralOperator_isSymmetric (featureKernel k)
    (memLp_featureKernel k hk hk2) (Filter.Eventually.of_forall (featureKernel_symmetric k))

lemma finiteDimensional_sourceKernel_nonzero_eigenspace
    (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ)) (r : ℝ) (hr : r ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace
      (DGRHS.Kernel.integralOperator h hh).toLinearMap r) :=
  (DGRHS.Kernel.integralOperator h hh).finite_dimensional_eigenspace
    (DGRHS.Kernel.integralOperator_isCompact h hh) r hr

/-- Any two complete eigenbases of this actual source operator have the same
finite nonzero fibers and a derived value-preserving nonzero label bijection.
No multiplicity equality or spectral matching is assumed. -/
theorem exists_nonzero_sourceKernel_eigenbasis_equiv {ι κ : Type*}
    (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ)) (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (heq : h =ᵐ[μ.prod μ] featureKernel k)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator h hh (e i) = c i • e i) :
    ∃ f : {i // a i ≠ 0} ≃ {j // c j ≠ 0}, ∀ i : {i // a i ≠ 0}, a i.val = c (f i).val := by
  have hT := sourceKernel_integralOperator_isSymmetric h hh k hk hk2 heq
  have hF := finiteDimensional_sourceKernel_nonzero_eigenspace h hh
  exact DGRHS.Kernel.exists_nonzeroSpectralLabelEquiv
    (DGRHS.Kernel.integralOperator h hh).toLinearMap hT
    (DGRHS.Kernel.integralOperator h hh).toLinearMap hT a b hb c e he hF hF (fun _ _ => rfl)

/-- Narrow adaptation of the checked root FeatureMultiplicity HasProd transport
using Mathlib subtype and equivalence APIs; actual label equivalence is supplied
by the preceding operator theorem. Zero factors are exactly one. -/
private lemma hasProd_factors_of_nonzero_equiv {ι κ : Type*}
    (a : ι → ℝ) (c : κ → ℝ) (β d : ℝ)
    (e : {i // a i ≠ 0} ≃ {j // c j ≠ 0})
    (he : ∀ i : {i // a i ≠ 0}, a i.val = c (e i).val)
    (ha : HasProd (fun i => (1 + β * a i) * Real.exp (-(β * a i))) d) :
    HasProd (fun i => (1 + β * c i) * Real.exp (-(β * c i))) d := by
  have hsa : Function.mulSupport (fun i => (1 + β * a i) * Real.exp (-(β * a i))) ⊆
      {i | a i ≠ 0} := by
    intro i hi hz
    exact hi (by simp [hz])
  have hsc : Function.mulSupport (fun i => (1 + β * c i) * Real.exp (-(β * c i))) ⊆
      {i | c i ≠ 0} := by
    intro i hi hz
    exact hi (by simp [hz])
  rw [← hasProd_subtype_iff_of_mulSupport_subset hsa] at ha
  rw [← hasProd_subtype_iff_of_mulSupport_subset hsc]
  have hh : (fun i : {i // a i ≠ 0} => (1 + β * a i) * Real.exp (-(β * a i))) =
      (fun j : {j // c j ≠ 0} => (1 + β * c j) * Real.exp (-(β * c j))) ∘ e := by
    funext i
    simp only [Function.comp_apply, he]
  change HasProd (fun i : {i // a i ≠ 0} => (1 + β * a i) * Real.exp (-(β * a i))) d at ha
  change HasProd (fun j : {j // c j ≠ 0} => (1 + β * c j) * Real.exp (-(β * c j))) d
  rw [hh] at ha
  exact e.hasProd_iff.mp ha

/-- Transport an existing genuine product limit through actual nonzero
multiplicities of the same source integral operator. -/
theorem hasProd_sourceKernel_regularizedFactors_of_eigenbasis {ι κ : Type*}
    (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ)) (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (heq : h =ᵐ[μ.prod μ] featureKernel k)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator h hh (e i) = c i • e i)
    (β d : ℝ) (ha : HasProd (fun i => (1 + β * a i) * Real.exp (-(β * a i))) d) :
    HasProd (fun i => (1 + β * c i) * Real.exp (-(β * c i))) d := by
  obtain ⟨f, hf⟩ := exists_nonzero_sourceKernel_eigenbasis_equiv h hh k hk hk2 heq a b hb c e he
  exact hasProd_factors_of_nonzero_equiv a c β d f hf ha

private lemma summable_scaled_squares_of_positive_trace {ι : Type*}
    (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    Summable (fun i => (β * a i) ^ 2) := by
  have hb : ∀ i, 0 ≤ β * a i := fun i => mul_nonneg hβ (ha i)
  have ht := hs.mul_left β
  apply (ht.mul_left (∑' i, β * a i)).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (ht.le_tsum i (fun j _ => hb j)) (hb i)

variable [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace.CountablyGenerated X]

/-- The rate against ANY actual complete source eigenbasis. Compactness and
finite nonzero multiplicities are proved, the label equivalence is constructed,
and a genuine positive regularized product limit is derived and transported. -/
theorem sourceKernel_eigenbasis_feature_rate {κ : Type*}
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator h hh (e i) = c i • e i) :
    HasProd (fun i => (1 + β * c i) * Real.exp (-(β * c i)))
      (DGRHS.Kernel.regularizedDet (fun i => β * c i)) ∧
    0 < DGRHS.Kernel.regularizedDet (fun i => β * c i) ∧
    ∀ N : ℕ, 1 ≤ N →
      Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
        ∂Measure.pi (fun _ : Fin N => μ)) -
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * c i)))⁻¹| ≤
        (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  obtain ⟨ι, a, b, hi, hb, ha, hs, ht, hRate⟩ :=
    exists_sourceKernelParticleStatistic_feature_rate β hβ h hh k hk hM hmean heq
  have hsq := summable_scaled_squares_of_positive_trace β hβ a ha hs
  have hp : ∀ i, 0 < 1 + β * a i := fun i => by have := mul_nonneg hβ (ha i); linarith
  have hProd := DGRHS.Kernel.hasProd_regularizedDet hsq hp
  have hOther := hasProd_sourceKernel_regularizedFactors_of_eigenbasis h hh k hk
    (memLp_feature_of_exponential_moment β hβ k hk hM) heq a b hb c e he β _ hProd
  have hdet : DGRHS.Kernel.regularizedDet (fun i => β * a i) =
      DGRHS.Kernel.regularizedDet (fun i => β * c i) := hProd.tprod_eq.trans hOther.tprod_eq.symm
  refine ⟨?_, ?_, fun N hN => ?_⟩
  · change HasProd (fun i => (1 + β * c i) * Real.exp (-(β * c i)))
      (∏' i, (1 + β * c i) * Real.exp (-(β * c i)))
    rw [hOther.tprod_eq]
    exact hOther
  · rw [← hdet]
    exact DGRHS.Kernel.regularizedDet_pos hsq hp
  · simpa only [hdet] using hRate N hN

end DGRHS.Gaussian

#check DGRHS.Gaussian.sourceKernel_integralOperator_isSymmetric
#print axioms DGRHS.Gaussian.sourceKernel_integralOperator_isSymmetric

#check DGRHS.Gaussian.finiteDimensional_sourceKernel_nonzero_eigenspace
#print axioms DGRHS.Gaussian.finiteDimensional_sourceKernel_nonzero_eigenspace

#check DGRHS.Gaussian.exists_nonzero_sourceKernel_eigenbasis_equiv
#print axioms DGRHS.Gaussian.exists_nonzero_sourceKernel_eigenbasis_equiv

#check DGRHS.Gaussian.hasProd_sourceKernel_regularizedFactors_of_eigenbasis
#print axioms DGRHS.Gaussian.hasProd_sourceKernel_regularizedFactors_of_eigenbasis

#check DGRHS.Gaussian.sourceKernel_eigenbasis_feature_rate
#print axioms DGRHS.Gaussian.sourceKernel_eigenbasis_feature_rate

#check DGRHS.Kernel.symmetric_apply_apply_eq_zero
#print axioms DGRHS.Kernel.symmetric_apply_apply_eq_zero

#check DGRHS.Kernel.symmetric_pow_apply_eq_zero
#print axioms DGRHS.Kernel.symmetric_pow_apply_eq_zero

#check DGRHS.Kernel.symmetric_maxGenEigenspace_eq
#print axioms DGRHS.Kernel.symmetric_maxGenEigenspace_eq

#check DGRHS.Kernel.spectralFiberVector
#print axioms DGRHS.Kernel.spectralFiberVector

#check DGRHS.Kernel.spectralFiberVector_orthonormal
#print axioms DGRHS.Kernel.spectralFiberVector_orthonormal

#check DGRHS.Kernel.finite_spectralFiber
#print axioms DGRHS.Kernel.finite_spectralFiber

#check DGRHS.Kernel.spectralFiber_span_orthogonal_eq_bot
#print axioms DGRHS.Kernel.spectralFiber_span_orthogonal_eq_bot

#check DGRHS.Kernel.finrank_eq_card_spectralFiber
#print axioms DGRHS.Kernel.finrank_eq_card_spectralFiber

#check DGRHS.Kernel.nonzeroFiberEquiv
#print axioms DGRHS.Kernel.nonzeroFiberEquiv

#check DGRHS.Kernel.exists_nonzeroSpectralLabelEquiv
#print axioms DGRHS.Kernel.exists_nonzeroSpectralLabelEquiv

#check DGRHS.Kernel.regularizedDet_restrict_nonzero
#print axioms DGRHS.Kernel.regularizedDet_restrict_nonzero
