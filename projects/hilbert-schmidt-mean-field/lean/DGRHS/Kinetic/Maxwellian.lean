import DGRHS.Kinetic.SpatialTensorization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The standard quadratic kinetic energy and its actual normalized Maxwellian.
The normalization is computed from native proper Gaussian integrals. The
position/velocity Gibbs factorization is a measure identity, not a premise. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Kinetic
variable {J X V : Type*} [Fintype J] [MeasurableSpace X] [MeasurableSpace V]

def kineticExponent (β : ℝ) (v : J → ℝ) : ℝ := -(β / 2) * ∑ j, (v j)^2

def maxwellian (J : Type*) [Fintype J] (β : ℝ) : Measure (J → ℝ) :=
  volume.tilted (kineticExponent β)

lemma kinetic_exp_product (β : ℝ) (v : J → ℝ) :
    Real.exp (kineticExponent β v) = ∏ j, Real.exp (-(β/2)*(v j)^2) := by
  rw [← Real.exp_sum]
  congr 1
  exact Finset.mul_sum _ _ _

theorem kinetic_exp_integrable (β : ℝ) (hβ : 0 < β) :
    Integrable (fun v : J → ℝ => Real.exp (kineticExponent β v)) volume := by
  simp_rw [kinetic_exp_product]
  exact Integrable.fintype_prod (fun _ : J => integrable_exp_neg_mul_sq (by positivity : 0 < β/2))

theorem kinetic_partition (β : ℝ) (hβ : 0 < β) :
    (∫ v : J → ℝ, Real.exp (kineticExponent β v)) =
      (Real.sqrt (2*Real.pi/β))^(Fintype.card J) := by
  simp_rw [kinetic_exp_product]
  rw [integral_fintype_prod_volume_eq_pow (ι := J)
    (fun x : ℝ => Real.exp (-(β/2)*x^2)), integral_gaussian]
  congr 2
  field_simp

theorem maxwellian_probability (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (maxwellian J β) :=
  isProbabilityMeasure_tilted (kinetic_exp_integrable β hβ)

theorem maxwellian_density (β : ℝ) (hβ : 0 < β) :
    maxwellian J β = volume.withDensity (fun v : J → ℝ =>
      ENNReal.ofReal (Real.exp (-(β/2)*∑ j, (v j)^2) /
        (Real.sqrt (2*Real.pi/β))^(Fintype.card J))) := by
  unfold maxwellian Measure.tilted
  rw [kinetic_partition β hβ]
  rfl

/-- Genuine separable Hamiltonian tensorization; properness is established
separately in downstream uses before calling the factors probability laws. -/
theorem gibbs_separable_tensor (μ : Measure X) (η : Measure V)
    [SFinite μ] [SFinite η] (u : X → ℝ) (g : V → ℝ)
    (hu : Measurable u) (hg : Measurable g) :
    (μ.prod η).tilted (fun z => u z.1 + g z.2) = (μ.tilted u).prod (η.tilted g) := by
  have he : (∫ z : X × V, Real.exp (u z.1 + g z.2) ∂μ.prod η) =
      (∫ x, Real.exp (u x) ∂μ) * ∫ v, Real.exp (g v) ∂η := by
    simp_rw [Real.exp_add]
    exact integral_prod_mul (μ := μ) (ν := η)
      (fun x => Real.exp (u x)) (fun v => Real.exp (g v))
  have hu' : Measurable (fun x => ENNReal.ofReal (Real.exp (u x) / ∫ y, Real.exp (u y) ∂μ)) :=
    ((Real.continuous_exp.measurable.comp hu).div_const _).ennreal_ofReal
  have hg' : Measurable (fun v => ENNReal.ofReal (Real.exp (g v) / ∫ w, Real.exp (g w) ∂η)) :=
    ((Real.continuous_exp.measurable.comp hg).div_const _).ennreal_ofReal
  unfold Measure.tilted
  rw [he, prod_withDensity hu' hg']
  congr 1
  funext z
  rw [Real.exp_add, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  exact mul_div_mul_comm _ _ _ _

theorem kinetic_gibbs_factorization (μ : Measure X) [SFinite μ]
    (u : X → ℝ) (hu : Measurable u) (β : ℝ) :
    (μ.prod (volume : Measure (J → ℝ))).tilted
      (fun z => u z.1 - (β/2)*∑ j, (z.2 j)^2) =
      (μ.tilted u).prod (maxwellian J β) := by
  have hg : Measurable (kineticExponent (J := J) β) := by
    unfold kineticExponent
    fun_prop
  simpa only [maxwellian, kineticExponent, sub_eq_add_neg, neg_mul] using
    gibbs_separable_tensor μ volume u (kineticExponent (J := J) β) hu hg

theorem kinetic_full_partition (μ : Measure X) [SFinite μ]
    (u : X → ℝ) (β : ℝ) (hβ : 0 < β) :
    (∫ z : X × (J → ℝ), Real.exp (u z.1 - (β/2)*∑ j, (z.2 j)^2)
      ∂μ.prod volume) = (∫ x, Real.exp (u x) ∂μ) *
        (Real.sqrt (2*Real.pi/β))^(Fintype.card J) := by
  have he (z : X × (J → ℝ)) : Real.exp (u z.1 - (β/2)*∑ j, (z.2 j)^2) =
      Real.exp (u z.1) * Real.exp (kineticExponent β z.2) := by
    rw [← Real.exp_add]
    congr 1
    simp [kineticExponent, sub_eq_add_neg]
  simp_rw [he]
  rw [integral_prod_mul (μ := μ) (ν := (volume : Measure (J → ℝ)))
    (fun x => Real.exp (u x)) (fun v => Real.exp (kineticExponent β v)),
    kinetic_partition β hβ]

theorem kinetic_full_integrable (μ : Measure X) [SFinite μ]
    (u : X → ℝ) (hu : Integrable (fun x => Real.exp (u x)) μ)
    (β : ℝ) (hβ : 0 < β) :
    Integrable (fun z : X × (J → ℝ) =>
      Real.exp (u z.1 - (β/2)*∑ j, (z.2 j)^2)) (μ.prod volume) := by
  simpa only [kineticExponent, sub_eq_add_neg, neg_mul, Real.exp_add] using
    hu.mul_prod (kinetic_exp_integrable (J := J) β hβ)

theorem kinetic_full_gibbs_probability (μ : Measure X) [SFinite μ] [NeZero μ]
    (u : X → ℝ) (hu : Integrable (fun x => Real.exp (u x)) μ)
    (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure ((μ.prod (volume : Measure (J → ℝ))).tilted
      (fun z => u z.1 - (β/2)*∑ j, (z.2 j)^2)) := by
  have hnonzero : μ.prod (volume : Measure (J → ℝ)) ≠ 0 := by
    intro hz
    have hval : (μ.prod (volume : Measure (J → ℝ))) Set.univ ≠ 0 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)
    apply hval
    simp [hz]
  letI : NeZero (μ.prod (volume : Measure (J → ℝ))) := ⟨hnonzero⟩
  exact isProbabilityMeasure_tilted (kinetic_full_integrable μ u hu β hβ)

end DGRHS.Kinetic
#check @DGRHS.Kinetic.kinetic_exp_product
#print axioms DGRHS.Kinetic.kinetic_exp_product
#check @DGRHS.Kinetic.kinetic_exp_integrable
#print axioms DGRHS.Kinetic.kinetic_exp_integrable
#check @DGRHS.Kinetic.kinetic_partition
#print axioms DGRHS.Kinetic.kinetic_partition
#check @DGRHS.Kinetic.maxwellian_probability
#print axioms DGRHS.Kinetic.maxwellian_probability
#check @DGRHS.Kinetic.maxwellian_density
#print axioms DGRHS.Kinetic.maxwellian_density
#check @DGRHS.Kinetic.gibbs_separable_tensor
#print axioms DGRHS.Kinetic.gibbs_separable_tensor
#check @DGRHS.Kinetic.kinetic_gibbs_factorization
#print axioms DGRHS.Kinetic.kinetic_gibbs_factorization
#check @DGRHS.Kinetic.kinetic_full_partition
#print axioms DGRHS.Kinetic.kinetic_full_partition
#check @DGRHS.Kinetic.kinetic_full_integrable
#print axioms DGRHS.Kinetic.kinetic_full_integrable
#check @DGRHS.Kinetic.kinetic_full_gibbs_probability
#print axioms DGRHS.Kinetic.kinetic_full_gibbs_probability
