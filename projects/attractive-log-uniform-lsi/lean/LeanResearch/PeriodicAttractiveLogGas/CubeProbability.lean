import LeanResearch.PeriodicAttractiveLogGas.ClusterCubeIntegral
import LeanResearch.PeriodicAttractiveLogGas.BlockProductIntegration

/-! Normalized Lebesgue laws on the actual product cubes. Normalization,
coordinate independence and translation are proved, rather than assumed
in the fixed-particle weight argument. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.CubeProbability
open PhysicalCubes

def coordinateLaw (c : PlanarSpace) (ℓ : ℝ) : Measure PlanarSpace :=
  (ENNReal.ofReal (ℓ ^ 2))⁻¹ • volume.restrict (cube c ℓ)

theorem coordinateLaw_probability (c : PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (coordinateLaw c ℓ) := by
  constructor
  rw [coordinateLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    cube_volume c hℓ.le]
  simp only [Fintype.card_fin, smul_eq_mul]
  exact ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr (sq_pos_of_pos hℓ)).ne')
    ENNReal.ofReal_ne_top

def productLaw (k : ℕ) (c : Fin k → PlanarSpace) (ℓ : ℝ) : Measure (Fin k → PlanarSpace) :=
  Measure.pi (fun i => coordinateLaw (c i) ℓ)

theorem productLaw_probability (k : ℕ) (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (productLaw k c ℓ) := by
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw (c i) ℓ) :=
    fun i => coordinateLaw_probability (c i) hℓ
  exact Measure.pi.instIsProbabilityMeasure _

theorem productLaw_eq (k : ℕ) (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    productLaw k c ℓ = (ENNReal.ofReal (ℓ ^ (2 * k)))⁻¹ •
      volume.restrict (particleCube k c ℓ) := by
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw (c i) ℓ) :=
    fun i => coordinateLaw_probability (c i) hℓ
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change (ENNReal.ofReal (ℓ ^ (2 * k)))⁻¹ *
    volume (pi univ s ∩ pi univ (fun i => cube (c i) ℓ)) = _
  rw [← pi_inter_distrib, volume_pi_pi]
  simp only [coordinateLaw, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow (sq_nonneg ℓ), ← pow_mul]

theorem integral_productLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) (F : (Fin k → PlanarSpace) → E) :
    (∫ X, F X ∂productLaw k c ℓ) =
      (ℓ ^ (2 * k))⁻¹ • ∫ X in particleCube k c ℓ, F X := by
  rw [productLaw_eq k c hℓ, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hℓ.le _)]

theorem ae_mem_productCube (k : ℕ) (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ X ∂productLaw k c ℓ, X ∈ particleCube k c ℓ := by
  rw [productLaw_eq k c hℓ]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (particleCube_measurable k c ℓ)

theorem integrable_productLaw_iff {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) (F : (Fin k → PlanarSpace) → E) :
    Integrable F (productLaw k c ℓ) ↔ IntegrableOn F (particleCube k c ℓ) volume := by
  rw [productLaw_eq k c hℓ]
  exact integrable_inv_smul_measure
    ((ENNReal.ofReal_pos.mpr (pow_pos hℓ _)).ne') ENNReal.ofReal_ne_top

theorem isCompact_particleCube (k : ℕ) (c : Fin k → PlanarSpace) (ℓ : ℝ) :
    IsCompact (particleCube k c ℓ) := isCompact_univ_pi fun i => isCompact_cube (c i) ℓ

/-- Local collision integrability already proved for the genuine periodic
weight supplies every compact cube, including cubes meeting collisions. -/
theorem integrable_torusWeight_productLaw (k : ℕ) (hk : 0 < k) (c : Fin k → PlanarSpace)
    {a ℓ : ℝ} (ha : 0 ≤ a) (hsub : a * (k : ℝ) < 4) (hℓ : 0 < ℓ) :
    Integrable (fun X => torusPairWeight k a (planarConfigurationQuotient k X))
      (productLaw k c ℓ) := by
  apply (integrable_productLaw_iff k c hℓ _).mpr
  exact (locallyIntegrable_torusPairWeight_lift k hk ha hsub).integrableOn_isCompact
    (isCompact_particleCube k c ℓ)

theorem preimage_cube_add (c b : PlanarSpace) (ℓ : ℝ) :
    (fun x : PlanarSpace => x + b) ⁻¹' cube (c + b) ℓ = cube c ℓ := by
  ext x
  simp only [mem_preimage, mem_cube, PiLp.add_apply, add_sub_add_right_eq_sub]

theorem coordinateLaw_add (c b : PlanarSpace) (ℓ : ℝ) :
    MeasurePreserving (fun x : PlanarSpace => x + b)
      (coordinateLaw c ℓ) (coordinateLaw (c + b) ℓ) := by
  have hp := (measurePreserving_add_right (volume : Measure PlanarSpace) b).restrict_preimage
    (measurableSet_cube (c + b) ℓ)
  rw [preimage_cube_add] at hp
  refine ⟨hp.measurable, ?_⟩
  rw [coordinateLaw, Measure.map_smul _ hp.measurable.aemeasurable, hp.map_eq]
  rfl

theorem productLaw_add (k : ℕ) (c b : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasurePreserving (fun X : Fin k → PlanarSpace => X + b)
      (productLaw k c ℓ) (productLaw k (c + b) ℓ) := by
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw (c i) ℓ) :=
    fun i => coordinateLaw_probability (c i) hℓ
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw ((c + b) i) ℓ) :=
    fun i => coordinateLaw_probability ((c + b) i) hℓ
  exact measurePreserving_pi (fun i => coordinateLaw (c i) ℓ)
    (fun i => coordinateLaw ((c + b) i) ℓ) (fun i => coordinateLaw_add (c i) (b i) ℓ)


/-- The existing increasing coordinate split preserves the actual product
of normalized cube laws, including the centers in both subfamilies. -/
theorem split_productLaw {k : ℕ} (S : Finset (Fin k)) (c : Fin k → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasurePreserving (clusterCoordinateSplit S) (productLaw k c ℓ)
      ((productLaw S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ).prod
        (productLaw Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ℓ)) := by
  classical
  letI : ∀ i : Fin k, IsProbabilityMeasure (coordinateLaw (c i) ℓ) :=
    fun i => coordinateLaw_probability (c i) hℓ
  have hA := (measurePreserving_piCongrLeft
    (fun i : S => coordinateLaw (c i) ℓ) (S.orderIsoOfFin rfl).toEquiv).symm _
  have hB := (measurePreserving_piCongrLeft
    (fun i : {i : Fin k // i ∉ S} => coordinateLaw (c i) ℓ)
    (clusterComplementEnum S)).symm _
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun i : Fin k => coordinateLaw (c i) ℓ) (fun i => i ∈ S)
  exact (hA.prod hB).comp (by
    convert hsplit using 1
    · rfl
    · congr 3
      exact Subsingleton.elim _ _)

/-- Single-coordinate translations do not change the normalized mean of
a periodic function when the translation preserves its torus arguments. -/
theorem integral_periodic_translate (k : ℕ) (c b : Fin k → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (F : Configuration k → ℝ)
    (hperiod : ∀ i, torusQuotient (b i) = 0) :
    (∫ X, F (planarConfigurationQuotient k X) ∂productLaw k (c + b) ℓ) =
      ∫ X, F (planarConfigurationQuotient k X) ∂productLaw k c ℓ := by
  have he (X : Fin k → PlanarSpace) :
      planarConfigurationQuotient k (X + b) = planarConfigurationQuotient k X := by
    funext i
    simp only [planarConfigurationQuotient, Pi.add_apply, torusQuotient_add, hperiod, add_zero]
  have hh := (productLaw_add k c b hℓ).integral_comp
    (MeasurableEquiv.addRight b).measurableEmbedding
    (fun X => F (planarConfigurationQuotient k X))
  simpa only [he] using hh.symm

end PeriodicAttractiveLogGas.CubeProbability
