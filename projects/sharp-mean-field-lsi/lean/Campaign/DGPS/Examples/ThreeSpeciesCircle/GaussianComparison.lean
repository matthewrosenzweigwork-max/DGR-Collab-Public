import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel
import DGPS.Equilibrium.ComparisonRates

/-! Actual coercive Hessian and a full-domain Gaussian comparison for the
canonical elementary model. This unit proves only the coarse half-Poincare
lower bound; strict Gaussian lifting and the two-sector equality are separate
spectral obligations. No generator-interaction commutation is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The existing actual half-Hessian estimate supplies the native coercivity
predicate at the same canonical reference, for every positive field. -/
theorem elementaryModel_coerciveHessian {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) : IsCoerciveDensityHessian (modelData h ε) (refProb hh) :=
  ⟨1 / 2, by norm_num, hessian_half hh hε hεmax⟩

/-- The actual inverse covariance has norm-form upper bound two. The coercivity
proof can be any proof of the native predicate, retaining the same covariance. -/
theorem elementaryModel_covariance_form_le_two {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h)
    (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh))
    (f : centeredL2 (refProb hh)) :
    inner ℝ f (densityCovariance (modelData h ε) (refProb hh) hH f) ≤ 2 * ‖f‖ ^ 2 := by
  let w := densityCovariance (modelData h ε) (refProb hh) hH f
  have hw : densityHessian (modelData h ε) (refProb hh) w = f :=
    densityHessian_densityCovariance _ _ hH f
  have hlo := hessian_half hh hε hεmax w
  rw [hw, real_inner_comm] at hlo
  have hcs : inner ℝ f w ≤ ‖w‖ * ‖f‖ := by
    simpa only [real_inner_comm, mul_comm] using real_inner_le_norm w f
  have hn : ‖w‖ ≤ 2 * ‖f‖ := by
    rcases (norm_nonneg w).eq_or_lt with hw0 | hwp
    · rw [← hw0]
      positivity
    · by_contra hc
      have hc' : 2 * ‖f‖ < ‖w‖ := lt_of_not_ge hc
      nlinarith [mul_lt_mul_of_pos_right hc' hwp]
  change inner ℝ f w ≤ _
  calc
    _ ≤ ‖w‖ * ‖f‖ := hcs
    _ ≤ (2 * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg f)
    _ = _ := by ring

private theorem variance_centered_norm {μ : ProbabilityMeasure (Torus 1)}
    (f : WeakH1Test μ) (hf : ∫ x, f.fn x ∂(μ : Measure (Torus 1)) = 0) :
    weightedVariance μ f.fn = ‖f.toCentered μ hf‖ ^ 2 := by
  unfold weightedVariance
  rw [hf, ← real_inner_self_eq_norm_sq]
  have hi : inner ℝ (f.toCentered μ hf) (f.toCentered μ hf) =
      inner ℝ (f.isWeak.memLp.toLp f.fn) (f.isWeak.memLp.toLp f.fn) := rfl
  rw [hi, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.isWeak.memLp.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

/-- A genuine full-native-domain Gaussian comparison. No test regularity beyond
its original weighted weak H1 membership, or rate finiteness premise, is added. -/
theorem elementaryModel_gaussianRate_ge_half_referencePoincare {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh)) :
    ENNReal.ofReal (1 / 2 : ℝ) * poincareRate (refProb hh) ≤
      gaussianRate (modelData h ε) (refProb hh) hH := by
  rw [le_gaussianRate_iff_forall]
  intro f hf
  have hv := variance_centered_norm f hf.1
  have hvpos : 0 < weightedVariance (refProb hh) f.fn := by
    rw [hv]
    exact pow_pos (norm_pos_iff.2 (toCentered_ne_zero (refProb hh) hf)) 2
  have hd : gaussianDenominator (modelData h ε) (refProb hh) hH f hf.1 ≤
      2 * weightedVariance (refProb hh) f.fn := by
    rw [hv]
    exact elementaryModel_covariance_form_le_two hh hε hεmax hH _
  have hdhalf : (1 / 2 : ℝ) * gaussianDenominator (modelData h ε) (refProb hh) hH f hf.1 ≤
      weightedVariance (refProb hh) f.fn := by linarith
  calc
    (ENNReal.ofReal (1 / 2 : ℝ) * poincareRate (refProb hh)) *
        ENNReal.ofReal (gaussianDenominator (modelData h ε) (refProb hh) hH f hf.1) =
        poincareRate (refProb hh) * (ENNReal.ofReal (1 / 2 : ℝ) *
          ENNReal.ofReal (gaussianDenominator (modelData h ε) (refProb hh) hH f hf.1)) := by ac_rfl
    _ = poincareRate (refProb hh) * ENNReal.ofReal
        ((1 / 2 : ℝ) * gaussianDenominator (modelData h ε) (refProb hh) hH f hf.1) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ poincareRate (refProb hh) * ENNReal.ofReal (weightedVariance (refProb hh) f.fn) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hdhalf)
    _ ≤ dirichletEnergy (refProb hh) f :=
      (le_poincareRate_iff_forall (refProb hh) _).1 le_rfl f hvpos

end DGPS.Examples.ThreeSpeciesCircle
