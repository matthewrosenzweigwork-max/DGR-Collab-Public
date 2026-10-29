/- Native polynomial-exponential absorption for the already checked UNBOUNDED
repulsive feature-rate factory. No bounded-feature norm assumption is added. -/
import DGRHS.Gaussian.FeatureRateFactory
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X} [IsProbabilityMeasure μ]

def featureDiagonalMomentConstant (β : ℝ) : ℝ := 1+24/(β/2)^4

lemma featureExponentialMomentWeight_le_diagonal_exp (β : ℝ) (hβ : 0<β)
    (k : X→H) (x : X) :
    featureExponentialMomentWeight β k x ≤
      featureDiagonalMomentConstant β*Real.exp (β*‖k x‖^2) := by
  let D := ‖k x‖^2
  let θ := β/2
  have hθ : 0<θ := by dsimp [θ];positivity
  have hD : 0≤D := sq_nonneg _
  have hp := Real.pow_div_factorial_le_exp (θ*D) (mul_nonneg hθ.le hD) 4
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,
    Nat.cast_one,mul_one] at hp
  have ht : 0<θ^4 := pow_pos hθ _
  have hpoly : D^4≤(24/θ^4)*Real.exp (θ*D) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    rw [mul_pow] at hp
    nlinarith
  have hone : 1≤Real.exp (θ*D) := Real.one_le_exp (mul_nonneg hθ.le hD)
  have hs : 1+D^4≤(1+24/θ^4)*Real.exp (θ*D) := by nlinarith
  calc
    _ = Real.exp (θ*D)*(1+D^4) := by dsimp [featureExponentialMomentWeight,θ,D];congr 1;ring
    _ ≤ Real.exp (θ*D)*((1+24/θ^4)*Real.exp (θ*D)) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
    _ = _ := by
      rw [show β*‖k x‖^2=θ*D+θ*D by dsimp [θ,D];ring,Real.exp_add]
      dsimp [featureDiagonalMomentConstant,θ]
      ring

lemma integrable_featureRateWeight_of_diagonal_exponential
    (β a : ℝ) (hβ : 0<β) (ha : β≤a) (k : X→H) (hk : StronglyMeasurable k)
    (hexp : Integrable (fun x=>Real.exp (a*‖k x‖^2)) μ) :
    Integrable (featureExponentialMomentWeight β k) μ ∧
      (∫ x,featureExponentialMomentWeight β k x ∂μ)≤
        featureDiagonalMomentConstant β*(∫ x,Real.exp (a*‖k x‖^2) ∂μ) := by
  have hc : 0≤featureDiagonalMomentConstant β := by unfold featureDiagonalMomentConstant;positivity
  have hb (x : X) : featureExponentialMomentWeight β k x≤
      featureDiagonalMomentConstant β*Real.exp (a*‖k x‖^2) :=
    (featureExponentialMomentWeight_le_diagonal_exp β hβ k x).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right ha (sq_nonneg _))) hc)
  have hm : StronglyMeasurable (featureExponentialMomentWeight β k) := by
    unfold featureExponentialMomentWeight
    simp only [div_eq_mul_inv]
    exact (Real.continuous_exp.comp_stronglyMeasurable
      (((hk.norm.pow 2).const_mul β).mul_const (2:ℝ)⁻¹)).mul
      (stronglyMeasurable_const.add ((hk.norm.pow 2).pow 4))
  have hi : Integrable (featureExponentialMomentWeight β k) μ :=
    (hexp.const_mul _).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x=>by
        rw [Real.norm_eq_abs,abs_of_nonneg]
        · exact hb x
        · unfold featureExponentialMomentWeight;positivity)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x,featureDiagonalMomentConstant β*Real.exp (a*‖k x‖^2) ∂μ :=
      integral_mono_ae hi (hexp.const_mul _) (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _
end DGRHS.Gaussian
#check @DGRHS.Gaussian.integrable_featureRateWeight_of_diagonal_exponential
#print axioms DGRHS.Gaussian.featureExponentialMomentWeight_le_diagonal_exp
#print axioms DGRHS.Gaussian.integrable_featureRateWeight_of_diagonal_exponential
