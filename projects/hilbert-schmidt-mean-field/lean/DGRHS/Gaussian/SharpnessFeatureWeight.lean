import DGRHS.Gaussian.SharpnessDyadicFeature
import DGRHS.Gaussian.FeatureRateFactory

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]

omit [MeasurableSpace X] in
lemma sharpness_feature_weight_bound (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (D : ℝ) (_hD : 0 ≤ D) (hb : ∀ x, ‖k x‖^2 ≤ D) (x : X) :
    featureExponentialMomentWeight β k x ≤ Real.exp (β*D/2)*(1+D^4) := by
  unfold featureExponentialMomentWeight
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x) hβ) (by norm_num)
  · simpa only [add_comm] using add_le_add_left (pow_le_pow_left₀ (sq_nonneg _) (hb x) 4) 1
  · positivity
  · positivity

/-- Proper exponential feature weight follows from the genuine pointwise
diagonal cap. A finite totalized expectation is never used as properness. -/
lemma sharpness_feature_weight_integrable {μ : Measure X} [IsFiniteMeasure μ]
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (D : ℝ) (hD : 0 ≤ D) (hb : ∀ x, ‖k x‖^2 ≤ D) :
    Integrable (featureExponentialMomentWeight β k) μ := by
  apply (MeasureTheory.integrable_const (Real.exp (β*D/2)*(1+D^4))).mono'
  · unfold featureExponentialMomentWeight
    have harg : StronglyMeasurable (fun x => β*‖k x‖^2/2) := by
      simpa only [div_eq_mul_inv,Pi.pow_apply] using (((hk.norm.pow 2).const_mul β).mul_const ((2:ℝ)⁻¹))
    have hw := (Real.continuous_exp.comp_stronglyMeasurable harg).mul
      ((stronglyMeasurable_const : StronglyMeasurable (fun _ : X => (1:ℝ))).add ((hk.norm.pow 2).pow 4))
    change StronglyMeasurable (fun x => Real.exp (β*‖k x‖^2/2)*(1+(‖k x‖^2)^4)) at hw
    exact hw.aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold featureExponentialMomentWeight; positivity)]
    exact sharpness_feature_weight_bound β hβ k D hD hb x

lemma sharpness_feature_weight_integral_bound {μ : Measure X} [IsProbabilityMeasure μ]
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (D : ℝ) (hD : 0 ≤ D) (hb : ∀ x, ‖k x‖^2 ≤ D) :
    (∫ x,featureExponentialMomentWeight β k x ∂μ) ≤ Real.exp (β*D/2)*(1+D^4) := by
  calc
    _ ≤ ∫ _ : X,Real.exp (β*D/2)*(1+D^4) ∂μ :=
      integral_mono (sharpness_feature_weight_integrable β hβ k hk D hD hb)
        (MeasureTheory.integrable_const _) (sharpness_feature_weight_bound β hβ k D hD hb)
    _ = _ := by simp

variable {ι : Type*} [Fintype ι]
/-- Proper quantitative-feature moment of the actual dyadic compression,
with its exact exponential-in-diagonal coefficient. -/
theorem sharpness_dyadic_feature_weight (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : Box ι) (L : ℝ) (hL : 0 < L) (hw : ∀ i, I.upper i-I.lower i = L)
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2:ℝ))
    (m : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    let k := sharpnessDyadicFeature s ρ a I m
    let D := sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
      8*gaussianRieszPhysicalPotentialConstant s M ι
    Integrable (featureExponentialMomentWeight β k) (gaussianRieszDensityMeasure ρ) ∧
      (∫ x,featureExponentialMomentWeight β k x ∂gaussianRieszDensityMeasure ρ) ≤
        Real.exp (β*D/2)*(1+D^4) := by
  let k := sharpnessDyadicFeature s ρ a I m
  let D := sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
    8*gaussianRieszPhysicalPotentialConstant s M ι
  have hf := sharpness_dyadic_feature_data s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m
  have hb : ∀ x, ‖k x‖^2 ≤ D := hf.2.2.2.2
  have hD : 0 ≤ D := (sq_nonneg ‖k 0‖).trans (hb 0)
  exact ⟨sharpness_feature_weight_integrable β hβ k hf.1 D hD hb,
    sharpness_feature_weight_integral_bound β hβ k hf.1 D hD hb⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_dyadic_feature_weight
#check @DGRHS.Gaussian.sharpness_dyadic_feature_weight
