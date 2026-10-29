import DGRHS.Gaussian.FiniteLaplace
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Actual independent Gaussian pair coordinates. Product-measure uniqueness
and the native Gaussian scaling law construct the law; no favorable joint
Gaussian distribution is introduced as a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

def periodicPairCoordinates (w : ι → ℝ × ℝ) (q : ι × Bool) : ℝ :=
  if q.2 then (w q.1).2 else (w q.1).1

lemma periodicPairCoordinates_measurable : Measurable (periodicPairCoordinates (ι := ι)) := by
  apply measurable_pi_lambda
  rintro ⟨i,b⟩
  cases b <;> simp only [periodicPairCoordinates,Bool.false_eq_true,↓reduceIte]
  · exact measurable_fst.comp (measurable_pi_apply i)
  · exact measurable_snd.comp (measurable_pi_apply i)

lemma periodicPairCoordinates_preserving (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (periodicPairCoordinates (ι := ι))
      (Measure.pi fun _ : ι => μ.prod μ) (Measure.pi fun _ : ι × Bool => μ) := by
  refine ⟨periodicPairCoordinates_measurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.pi countable_univ (fun i _ => hs i)
  have hp : periodicPairCoordinates ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : ι => s (i,false) ×ˢ s (i,true)) := by
    ext w
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
    constructor
    · intro h i
      exact ⟨h (i,false),h (i,true)⟩
    · intro h q
      rcases q with ⟨i,b⟩
      cases b
      · exact (h i).1
      · exact (h i).2
  rw [Measure.map_apply periodicPairCoordinates_measurable hset,hp,Measure.pi_pi,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.prod_prod]
  simp only [Fintype.prod_bool]
  ring

lemma periodicHalfGaussian_scale_preserving :
    MeasurePreserving (fun x : ℝ => Real.sqrt 2*x) (gaussianReal 0 (1/2)) (gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mul,NNReal.coe_mk,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num

lemma periodicHalfGaussian_coordinates_preserving :
    MeasurePreserving (fun w : ι → ℝ × ℝ => fun q => Real.sqrt 2*periodicPairCoordinates w q)
      (Measure.pi fun _ : ι => (gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2)))
      (finiteStandardGaussian (ι × Bool)) := by
  exact (measurePreserving_pi (fun _ : ι × Bool => gaussianReal 0 (1/2))
    (fun _ => gaussianReal 0 1) (fun _ => periodicHalfGaussian_scale_preserving)).comp
      (periodicPairCoordinates_preserving (gaussianReal 0 (1/2)))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPairCoordinates_preserving
#print axioms DGRHS.Periodic.periodicHalfGaussian_scale_preserving
#print axioms DGRHS.Periodic.periodicHalfGaussian_coordinates_preserving
#check @DGRHS.Periodic.periodicHalfGaussian_coordinates_preserving
