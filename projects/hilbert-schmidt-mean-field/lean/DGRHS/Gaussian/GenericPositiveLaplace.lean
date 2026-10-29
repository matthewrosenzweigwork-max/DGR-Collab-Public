import DGRHS.Gaussian.InfinitePositiveLaplace
import DGRHS.Gaussian.IndexedIsonormal
import Mathlib.Probability.Independence.InfinitePi

/- Actual full-family law transport of the checked positive diagonal identity. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian
noncomputable section
variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

def familyQuadratic (a : ι → ℝ) (z : ι → ℝ) : ℝ := ∑' i, a i * z i ^ 2

def familyCenteredExp (β : ℝ) (a : ι → ℝ) (z : ι → ℝ) : ℝ :=
  Real.exp (β * ((∑' i, a i) - familyQuadratic a z) / 2)

theorem measurable_familyQuadratic (a : ι → ℝ) : Measurable (familyQuadratic a) := by
  apply Measurable.tsum
  intro i
  exact measurable_const.mul ((measurable_pi_apply i).pow_const 2)

theorem measurable_familyCenteredExp (β : ℝ) (a : ι → ℝ) :
    Measurable (familyCenteredExp β a) := by
  exact Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_const.sub (measurable_familyQuadratic a))).div_const 2)

theorem map_standardGaussian_family (Y : ι → Ω → ℝ)
    (hY : ∀ i, AEMeasurable (Y i) P) (hI : iIndepFun Y P)
    (hm : ∀ i, P.map (Y i) = gaussianReal 0 1) :
    P.map (fun ω i => Y i ω) = Measure.infinitePi (fun _ : ι => gaussianReal 0 1) := by
  rw [hI.map_fun_eq_infinitePi_map₀' hY]
  simp_rw [hm]

theorem map_selectedGaussian_family (f : ι → ℕ) (hf : Function.Injective f) :
    IsonormalProcess.iidStdGaussian.map (fun ω i => IsonormalProcess.coord (f i) ω) =
      Measure.infinitePi (fun _ : ι => gaussianReal 0 1) := by
  exact map_standardGaussian_family _
    (fun i => (IsonormalProcess.measurable_coord (f i)).aemeasurable)
    (IsonormalProcess.iIndepFun_coord.precomp hf) (fun i => IsonormalProcess.map_coord (f i))

theorem integrable_familyCenteredExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (Y : ι → Ω → ℝ)
    (hY : ∀ i, AEMeasurable (Y i) P) (hI : iIndepFun Y P)
    (hm : ∀ i, P.map (Y i) = gaussianReal 0 1) :
    Integrable (fun ω => familyCenteredExp β a (fun i => Y i ω)) P := by
  let f : ι → ℕ := countableGaussianIndex
  have hf : Function.Injective f := countableGaussianIndex.injective
  have hC : AEMeasurable (fun ω i => IsonormalProcess.coord (f i) ω)
      IsonormalProcess.iidStdGaussian := aemeasurable_pi_iff.2
    (fun i => (IsonormalProcess.measurable_coord (f i)).aemeasurable)
  have hp : Integrable (familyCenteredExp β a)
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
    rw [← map_selectedGaussian_family f hf]
    exact (integrable_map_measure (measurable_familyCenteredExp β a).aestronglyMeasurable hC).2 (integrable_diagonalCenteredExp β hβ a ha hs f)
  rw [← map_standardGaussian_family Y hY hI hm] at hp
  exact (integrable_map_measure (measurable_familyCenteredExp β a).aestronglyMeasurable (aemeasurable_pi_iff.2 hY)).1 hp

theorem integral_familyCenteredExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (Y : ι → Ω → ℝ)
    (hY : ∀ i, AEMeasurable (Y i) P) (hI : iIndepFun Y P)
    (hm : ∀ i, P.map (Y i) = gaussianReal 0 1) :
    (∫ ω, familyCenteredExp β a (fun i => Y i ω) ∂P) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ := by
  let f : ι → ℕ := countableGaussianIndex
  have hf : Function.Injective f := countableGaussianIndex.injective
  have hC : AEMeasurable (fun ω i => IsonormalProcess.coord (f i) ω)
      IsonormalProcess.iidStdGaussian := aemeasurable_pi_iff.2
    (fun i => (IsonormalProcess.measurable_coord (f i)).aemeasurable)
  calc
    _ = ∫ z, familyCenteredExp β a z ∂(P.map (fun ω i => Y i ω)) :=
      (integral_map (aemeasurable_pi_iff.2 hY)
        (measurable_familyCenteredExp β a).aestronglyMeasurable).symm
    _ = ∫ z, familyCenteredExp β a z ∂(IsonormalProcess.iidStdGaussian.map
        (fun ω i => IsonormalProcess.coord (f i) ω)) := by
      rw [map_standardGaussian_family Y hY hI hm, map_selectedGaussian_family f hf]
    _ = ∫ ω, diagonalCenteredExp β a f ω ∂IsonormalProcess.iidStdGaussian :=
      integral_map hC (measurable_familyCenteredExp β a).aestronglyMeasurable
    _ = _ := integral_diagonalCenteredExp β hβ a ha hs f hf

end
end DGRHS.Gaussian
#check DGRHS.Gaussian.integrable_familyCenteredExp
#print axioms DGRHS.Gaussian.integrable_familyCenteredExp
#check DGRHS.Gaussian.integral_familyCenteredExp
#print axioms DGRHS.Gaussian.integral_familyCenteredExp

#check DGRHS.Gaussian.familyQuadratic
#print axioms DGRHS.Gaussian.familyQuadratic

#check DGRHS.Gaussian.familyCenteredExp
#print axioms DGRHS.Gaussian.familyCenteredExp

#check DGRHS.Gaussian.measurable_familyQuadratic
#print axioms DGRHS.Gaussian.measurable_familyQuadratic

#check DGRHS.Gaussian.measurable_familyCenteredExp
#print axioms DGRHS.Gaussian.measurable_familyCenteredExp

#check DGRHS.Gaussian.map_standardGaussian_family
#print axioms DGRHS.Gaussian.map_standardGaussian_family

#check DGRHS.Gaussian.map_selectedGaussian_family
#print axioms DGRHS.Gaussian.map_selectedGaussian_family
