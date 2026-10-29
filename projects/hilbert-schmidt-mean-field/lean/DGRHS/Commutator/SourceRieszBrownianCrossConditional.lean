import DGRHS.Commutator.SourceRieszBrownianPredictableBracket
import Mathlib.Probability.Independence.Integration

/-! Cross-coordinate Brownian conditioning in the supplied full filtration.
The primitive data are independent Brownian drivers and independence of their
joint future increment from the past. No independence of random-coefficient
stochastic integrals, nor a zero cross bracket, is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_indep_pair_swap (P : Measure Ω) (m : MeasurableSpace Ω)
    (X Y : Ω→ℝ)
    (hi : Indep (MeasurableSpace.comap (fun ω=>(X ω,Y ω)) inferInstance) m P) :
    Indep (MeasurableSpace.comap (fun ω=>(Y ω,X ω)) inferInstance) m P := by
  apply indep_of_indep_of_le_left hi
  have hself : Measurable[MeasurableSpace.comap (fun ω=>(X ω,Y ω)) inferInstance]
      (fun ω=>(X ω,Y ω)) := Measurable.of_comap_le le_rfl
  exact (hself.snd.prodMk hself.fst).comap_le

lemma sourceRiesz_brownian_cross_increment_conditional
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B C : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hBm : ∀ r,Measurable (B r)) (hCm : ∀ r,Measurable (C r))
    (hd : IndepFun (fun ω=>fun r=>B r ω) (fun ω=>fun r=>C r ω) P)
    (s t u : ℝ≥0)
    (hp : Indep (MeasurableSpace.comap (fun ω=>(B t ω-B s ω,C u ω-C s ω))
      inferInstance) (F s) P) :
    Integrable (fun ω=>(B t ω-B s ω)*(C u ω-C s ω)) P ∧
      (P[fun ω=>(B t ω-B s ω)*(C u ω-C s ω) | F s])=ᵐ[P] (fun _=>0) := by
  have hBL := (hB.hasLaw_sub t s).hasGaussianLaw.memLp_two
  have hCL := (hC.hasLaw_sub u s).hasGaussianLaw.memLp_two
  have hXY : IndepFun (fun ω=>B t ω-B s ω) (fun ω=>C u ω-C s ω) P :=
    hd.comp ((measurable_pi_apply t).sub (measurable_pi_apply s))
      ((measurable_pi_apply u).sub (measurable_pi_apply s))
  have hzB : (∫ ω,B t ω-B s ω ∂P)=0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),hB.integral_eval,hB.integral_eval]
    ring
  have hz : (∫ ω,(B t ω-B s ω)*(C u ω-C s ω) ∂P)=0 := by
    have he := hXY.integral_mul_eq_mul_integral hBL.aestronglyMeasurable hCL.aestronglyMeasurable
    change (∫ ω,(B t ω-B s ω)*(C u ω-C s ω) ∂P)=
      (∫ ω,B t ω-B s ω ∂P)*(∫ ω,C u ω-C s ω ∂P) at he
    rw [he,hzB,zero_mul]
  have hm : Measurable (fun ω=>(B t ω-B s ω,C u ω-C s ω)) :=
    ((hBm t).sub (hBm s)).prodMk ((hCm u).sub (hCm s))
  have hg : StronglyMeasurable[MeasurableSpace.comap
      (fun ω=>(B t ω-B s ω,C u ω-C s ω)) inferInstance]
      (fun ω=>(B t ω-B s ω)*(C u ω-C s ω)) := by
    have hself : Measurable[MeasurableSpace.comap
        (fun ω=>(B t ω-B s ω,C u ω-C s ω)) inferInstance]
        (fun ω=>(B t ω-B s ω,C u ω-C s ω)) := Measurable.of_comap_le le_rfl
    exact (hself.fst.mul hself.snd).stronglyMeasurable
  refine ⟨hBL.integrable_mul hCL,?_⟩
  simpa only [hz] using (condExp_indep_eq hm.comap_le (F.le s) hg hp)

lemma sourceRiesz_brownian_cross_bounded_increment
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B C : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hBm : ∀ r,Measurable (B r)) (hCm : ∀ r,Measurable (C r))
    (hd : IndepFun (fun ω=>fun r=>B r ω) (fun ω=>fun r=>C r ω) P)
    (s t u : ℝ≥0)
    (hp : Indep (MeasurableSpace.comap (fun ω=>(B t ω-B s ω,C u ω-C s ω))
      inferInstance) (F s) P)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F s] Z) (K : ℝ) (hb : ∀ᵐ ω ∂P,‖Z ω‖≤K) :
    Integrable (fun ω=>Z ω*(B t ω-B s ω)*(C u ω-C s ω)) P ∧
      (∫ ω,Z ω*(B t ω-B s ω)*(C u ω-C s ω) ∂P)=0 := by
  obtain ⟨hi,hzero⟩ := sourceRiesz_brownian_cross_increment_conditional P F B C hB hC hBm hCm hd s t u hp
  have hip := hi.bdd_mul (hZ.mono (F.le s)).aestronglyMeasurable hb
  have hce := condExp_stronglyMeasurable_mul_of_bound (F.le s) hZ hi K hb
  change (P[fun ω=>Z ω*((B t ω-B s ω)*(C u ω-C s ω)) | F s])=ᵐ[P]
    (fun ω=>Z ω*(P[fun ω=>(B t ω-B s ω)*(C u ω-C s ω) | F s]) ω) at hce
  have he : (P[fun ω=>Z ω*((B t ω-B s ω)*(C u ω-C s ω)) | F s])=ᵐ[P] (fun _=>0) := by
    filter_upwards [hce,hzero] with ω h1 h2
    rw [h1,h2,mul_zero]
  have hz : (∫ ω,Z ω*((B t ω-B s ω)*(C u ω-C s ω)) ∂P)=0 := by
    rw [←integral_condExp (F.le s),integral_congr_ae he,integral_zero]
  simpa only [mul_assoc] using And.intro hip hz

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_indep_pair_swap
#print axioms DGRHS.Commutator.sourceRiesz_indep_pair_swap
#check @DGRHS.Commutator.sourceRiesz_brownian_cross_increment_conditional
#print axioms DGRHS.Commutator.sourceRiesz_brownian_cross_increment_conditional
#check @DGRHS.Commutator.sourceRiesz_brownian_cross_bounded_increment
#print axioms DGRHS.Commutator.sourceRiesz_brownian_cross_bounded_increment
