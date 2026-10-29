import DGRHS.Gaussian.Imported.IsonormalProcess
import Mathlib.MeasureTheory.Measure.Prod

/-!
The joint-representative identification adapter. Its product convergence and
fiber convergence hypotheses are explicit analytic obligations, not assumed
Gaussian covariance or an assumed jointly measurable isonormal map. Constructing
the product L2 limit of the actual feature truncations remains separate.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace DGRHS.Gaussian

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- Product and fiber convergence identify fibers on a single full-measure set. -/
theorem ae_fiber_eq_of_joint_convergence
    {F : ℕ → X × Ω → ℝ} {g : X × Ω → ℝ} {W : X → Ω → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hprod : TendstoInMeasure (μ.prod P) F atTop g)
    (hfiber : ∀ x, TendstoInMeasure P (fun n ω => F n (x, ω)) atTop (W x)) :
    ∀ᵐ x ∂μ, W x =ᵐ[P] fun ω => g (x, ω) := by
  obtain ⟨ns, hns, hae⟩ := hprod.exists_seq_tendsto_ae
  have hsections := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hsections] with x hx
  have hm : TendstoInMeasure P (fun n ω => F (ns n) (x, ω)) atTop
      (fun ω => g (x, ω)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hF (ns n)).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact hx
  exact tendstoInMeasure_ae_unique ((hfiber x).comp hns.tendsto_atTop) hm

/-- A product L2 class supplies a strongly measurable representative; convergence
identifies its fibers. The product limit hypothesis still must be proved. -/
theorem exists_joint_representative_of_product_limit
    {F : ℕ → X × Ω → ℝ} (Z : Lp ℝ 2 (μ.prod P)) {W : X → Ω → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hprod : TendstoInMeasure (μ.prod P) F atTop (Z : X × Ω → ℝ))
    (hfiber : ∀ x, TendstoInMeasure P (fun n ω => F n (x, ω)) atTop (W x)) :
    ∃ g : X × Ω → ℝ, StronglyMeasurable g ∧
      g =ᵐ[μ.prod P] (Z : X × Ω → ℝ) ∧
      ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[P] W x := by
  let hz := Lp.aestronglyMeasurable Z
  let g := hz.mk (Z : X × Ω → ℝ)
  refine ⟨g, hz.stronglyMeasurable_mk, hz.ae_eq_mk.symm, ?_⟩
  have hp : TendstoInMeasure (μ.prod P) F atTop g := hprod.congr_right hz.ae_eq_mk
  exact (ae_fiber_eq_of_joint_convergence hF hp hfiber).mono (fun _ h => h.symm)

/-- Fiber Gaussianity is transported after identification, rather than postulated
for a choice of product-L2 representative. -/
theorem ae_hasGaussianLaw_of_joint_convergence
    {F : ℕ → X × Ω → ℝ} {g : X × Ω → ℝ} {W : X → Ω → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hprod : TendstoInMeasure (μ.prod P) F atTop g)
    (hfiber : ∀ x, TendstoInMeasure P (fun n ω => F n (x, ω)) atTop (W x))
    (hW : ∀ x, HasGaussianLaw (W x) P) :
    ∀ᵐ x ∂μ, HasGaussianLaw (fun ω => g (x, ω)) P := by
  filter_upwards [ae_fiber_eq_of_joint_convergence hF hprod hfiber] with x hx
  exact (hW x).congr hx

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.ae_fiber_eq_of_joint_convergence
#print axioms DGRHS.Gaussian.exists_joint_representative_of_product_limit
#print axioms DGRHS.Gaussian.ae_hasGaussianLaw_of_joint_convergence

#check DGRHS.Gaussian.ae_fiber_eq_of_joint_convergence
#check DGRHS.Gaussian.exists_joint_representative_of_product_limit
#check DGRHS.Gaussian.ae_hasGaussianLaw_of_joint_convergence
