import DGRHS.Concentration.HilbertQuadratic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped Topology
namespace DGRHS.Concentration

lemma bounded_integrableExpSet_eq_univ {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) :
    integrableExpSet Z μ = Set.univ := by
  ext t
  simp only [integrableExpSet,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  have hs := scalar_mul_ae_bounded hZ hB t
  exact (bounded_exp_positive hs.1 hs.2).integrable

lemma bounded_hasDerivAt_cgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) (t : ℝ) :
    HasDerivAt (cgf Z μ) ((∫ x, Z x*Real.exp (t*Z x) ∂μ)/mgf Z μ t) t := by
  have ht : t ∈ interior (integrableExpSet Z μ) := by
    simp [bounded_integrableExpSet_eq_univ hZ hB]
  have hs := scalar_mul_ae_bounded hZ hB t
  exact (hasDerivAt_mgf ht).log (mgf_pos (bounded_exp_positive hs.1 hs.2).integrable).ne'

lemma bounded_cgf_deriv_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) :
    deriv (cgf Z μ) 0 = ∫ x, Z x ∂μ := by
  simpa using (bounded_hasDerivAt_cgf hZ hB 0).deriv

lemma bounded_entropy_cgf_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) (t : ℝ) :
    functionalEntropy μ (fun x ↦ Real.exp (t*Z x)) =
      mgf Z μ t*(t*deriv (cgf Z μ) t-cgf Z μ t) := by
  have hs := scalar_mul_ae_bounded hZ hB t
  have hm := mgf_pos (bounded_exp_positive hs.1 hs.2).integrable
  have he : (fun x ↦ Real.exp (t*Z x)*Real.log (Real.exp (t*Z x))) =
      fun x ↦ t*(Z x*Real.exp (t*Z x)) := by
    funext x
    rw [Real.log_exp]
    ring
  unfold functionalEntropy
  rw [he,integral_const_mul,(bounded_hasDerivAt_cgf hZ hB t).deriv]
  change _ - mgf Z μ t*cgf Z μ t = _
  field_simp [hm.ne']

lemma bounded_cgf_weighted_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) (t : ℝ) :
    (∫ x, Real.exp (t*Z x)*Z x ∂μ) = mgf Z μ t*deriv (cgf Z μ) t := by
  have hs := scalar_mul_ae_bounded hZ hB t
  have hm := mgf_pos (bounded_exp_positive hs.1 hs.2).integrable
  rw [(bounded_hasDerivAt_cgf hZ hB t).deriv]
  rw [mul_div_cancel₀ _ hm.ne']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ mul_comm _ _

/-- Integrate the self-bounding differential inequality with its genuine derivative at zero. -/
lemma self_bounding_cgf_calculus (G : ℝ → ℝ) (c theta : ℝ)
    (hG : Differentiable ℝ G) (h0 : G 0 = 0) (htheta : 0 ≤ theta)
    (hden : 0 < 1-c*theta)
    (hineq : ∀ t, 0 < t → t ≤ theta →
      t*deriv G t-G t ≤ c*t^2*deriv G t) :
    G theta ≤ theta*deriv G 0/(1-c*theta) := by
  rcases eq_or_lt_of_le htheta with htheta | htheta
  · subst theta
    simp [h0]
  let f := fun t ↦ (1-c*t)*dslope G 0 t
  have hsc : Continuous (dslope G 0) := continuous_iff_continuousAt.mpr fun x ↦ by
    by_cases hx : x=0
    · subst x
      exact continuousAt_dslope_same.mpr (hG 0)
    · exact (continuousAt_dslope_of_ne hx).mpr (hG x).continuousAt
  have hfc : Continuous f := (continuous_const.sub (continuous_const.mul continuous_id)).mul hsc
  have hfd : ∀ x, x ≠ 0 → HasDerivAt f
      ((((-c)*G x+(1-c*x)*deriv G x)*x-(1-c*x)*G x)/x^2) x := by
    intro x hx
    have hd : HasDerivAt (fun y ↦ (1-c*y)*G y/y)
        ((((-c)*G x+(1-c*x)*deriv G x)*x-(1-c*x)*G x)/x^2) x := by
      convert (((hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).const_mul c)).mul (hG x).hasDerivAt).div
          (hasDerivAt_id x) hx using 1
      · funext y
        simp only [Pi.sub_apply,Pi.mul_apply,Pi.div_apply,id_eq]
      · simp only [Pi.sub_apply,Pi.mul_apply,id_eq]
        ring
    have he : f =ᶠ[𝓝 x] (fun y ↦ (1-c*y)*G y/y) := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne G hx] with y hy
      simp [f,hy,slope,h0,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    exact he.hasDerivAt_iff.mpr hd
  have ha : AntitoneOn f (Icc 0 theta) := antitoneOn_of_deriv_nonpos (convex_Icc 0 theta)
    hfc.continuousOn (fun x hx ↦
      (hfd x (by have h := (mem_Ioo.mp (by simpa using hx : x ∈ Ioo 0 theta)).1; exact h.ne')).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ by
      have hx' : x ∈ Ioo 0 theta := by simpa using hx
      rw [(hfd x hx'.1.ne').deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg x)
      have hi := hineq x hx'.1 hx'.2.le
      nlinarith [hi])
  have hh := ha (show (0 : ℝ) ∈ Icc 0 theta from ⟨le_rfl,htheta.le⟩)
    (show theta ∈ Icc 0 theta from ⟨htheta.le,le_rfl⟩) htheta.le
  have hf0 : f 0 = deriv G 0 := by simp [f]
  have hft : f theta = ((1-c*theta)*G theta)/theta := by
    simp [f,dslope_of_ne G htheta.ne',slope,h0,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  rw [hf0,hft] at hh
  apply (le_div_iff₀ hden).mpr
  have h := (div_le_iff₀ htheta).mp hh
  nlinarith [h]

theorem empirical_quadratic_cgf_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B theta : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (htheta : 0 ≤ theta) (hden : 0 < 1-(B^2/2)*theta) :
    cgf (empiricalQuadraticOnProduct Z) (Measure.pi μ) theta ≤
      theta*(∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ)/(1-(B^2/2)*theta) := by
  let V := empiricalQuadraticOnProduct Z
  let G := cgf V (Measure.pi μ)
  have hv := empirical_quadratic_product_aestronglyMeasurable μ Z hZ
  have hj : ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖Z i (ω i)‖ ≤ B := ae_all_iff.mpr fun i ↦
    (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i)
  have hb : ∀ᵐ ω ∂Measure.pi μ, |V ω| ≤ (n : ℝ)*B^2 := by
    filter_upwards [hj] with ω hω
    change |empiricalQuadratic (fun i ↦ Z i (ω i))| ≤ _
    rw [abs_of_nonneg (empirical_quadratic_nonneg _)]
    exact empirical_quadratic_le_uniform _ B hω
  have hg : Differentiable ℝ G := fun t ↦ (bounded_hasDerivAt_cgf hv hb t).differentiableAt
  have hi : ∀ t, 0 < t → t ≤ theta → t*deriv G t-G t ≤ (B^2/2)*t^2*deriv G t := by
    intro t ht _
    have hs := scalar_mul_ae_bounded hv hb t
    have hm := mgf_pos (bounded_exp_positive hs.1 hs.2).integrable
    have hh := empirical_quadratic_entropy n μ Z B hZ hB t ht.le
    rw [bounded_entropy_cgf_identity hv hb t,bounded_cgf_weighted_mean hv hb t] at hh
    have hp : mgf V (Measure.pi μ) t*(t*deriv G t-G t) ≤
        mgf V (Measure.pi μ) t*((B^2/2)*t^2*deriv G t) := by
      convert hh using 1
      ring
    exact (mul_le_mul_iff_right₀ hm).mp (by simpa only [mul_comm] using hp)
  have h := self_bounding_cgf_calculus G (B^2/2) theta hg (by simp [G]) htheta hden hi
  rw [bounded_cgf_deriv_zero hv hb] at h
  exact h

#print axioms DGRHS.Concentration.bounded_hasDerivAt_cgf
#print axioms DGRHS.Concentration.bounded_entropy_cgf_identity
#print axioms DGRHS.Concentration.self_bounding_cgf_calculus
#print axioms DGRHS.Concentration.empirical_quadratic_cgf_bound
#check @DGRHS.Concentration.empirical_quadratic_cgf_bound

end DGRHS.Concentration
