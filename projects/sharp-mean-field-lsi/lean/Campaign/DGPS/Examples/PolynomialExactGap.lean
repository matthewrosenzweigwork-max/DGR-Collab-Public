import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel
import DGPS.Examples.PolynomialEquilibrium
import DGPS.Circle.VonMisesSmallField
import DGPS.Model.FreeEnergy
import DGPS.Variational.EquilibriumGibbs
import DGPS.Measure.EntropyChain
import DGPS.Equilibrium.Hessian

open MeasureTheory InformationTheory
open scoped ENNReal ContDiff
open DGPS DGPS.Examples.PolynomialSpecies DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.ThreeSpeciesCircle
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Examples.PolynomialExactGap


theorem isSmooth_cosT_EX055 (k : ℕ) : IsSmoothPeriodic (cosT k) := circ_smooth_cosHarm k

theorem isSmooth_polyFeature_EX055 (h : ℝ) : IsSmoothPeriodic (polyFeature h) := by
  have h2 := isSmooth_cosT_EX055 2
  have h1 := isSmooth_cosT_EX055 1
  unfold IsSmoothPeriodic at *
  unfold polyFeature
  exact h2.sub (contDiff_const.mul h1)

/-- Gibbs potential `U_{h,s} = -h cos θ + s P_h`. -/
noncomputable def polyPot_EX055 (h s : ℝ) (x : Torus 1) : ℝ :=
  -h * cosT 1 x + s * polyFeature h x

theorem isSmooth_polyPot_EX055 (h s : ℝ) : IsSmoothPeriodic (polyPot_EX055 h s) := by
  have h1 := isSmooth_cosT_EX055 1
  have hf := isSmooth_polyFeature_EX055 h
  unfold IsSmoothPeriodic at *
  unfold polyPot_EX055
  exact (contDiff_const.mul h1).add (contDiff_const.mul hf)

/-- Drift potential of a probability `ν`: `U_ν = -h cos θ + 2η (m_ν - m₀) P_h`. -/
noncomputable def polyDrift_EX055 (h : ℝ) (ν : Measure (Torus 1)) : Torus 1 → ℝ :=
  polyPot_EX055 h (2 * eta * (∫ y, polyFeature h y ∂ν - polyCentering h))

theorem isSmooth_polyDrift_EX055 (h : ℝ) (ν : Measure (Torus 1)) :
    IsSmoothPeriodic (polyDrift_EX055 h ν) :=
  isSmooth_polyPot_EX055 _ _

theorem isSmooth_polyV_EX055 (h : ℝ) : IsSmoothPeriodic (polyV h) := by
  have h1 := isSmooth_cosT_EX055 1
  have hf := isSmooth_polyFeature_EX055 h
  unfold IsSmoothPeriodic at *
  unfold polyV
  exact (contDiff_const.mul h1).add (contDiff_const.mul ((hf.sub contDiff_const).pow 2))

theorem isSmooth_polyW_left_EX055 (h : ℝ) (y : Torus 1) :
    IsSmoothPeriodic (fun x => polyW h x y) := by
  have hf := isSmooth_polyFeature_EX055 h
  unfold IsSmoothPeriodic at *
  unfold polyW
  exact contDiff_const.mul ((hf.sub contDiff_const).pow 2)

theorem polyPot_deriv_EX055 (h s : ℝ) (t : ℝ) :
    HasDerivAt (fun r => polyPot_EX055 h s (pt r))
      (-h * coordPartial 0 (cosT 1) (pt t) + s * coordPartial 0 (polyFeature h) (pt t)) t := by
  have hc := circ_coordPartial_pt (isSmooth_cosT_EX055 1) t
  have hf := circ_coordPartial_pt (isSmooth_polyFeature_EX055 h) t
  have key := (hc.const_mul (-h)).add (hf.const_mul s)
  exact key

theorem polyV_deriv_EX055 (h : ℝ) (t : ℝ) :
    HasDerivAt (fun r => polyV h (pt r))
      (-h * coordPartial 0 (cosT 1) (pt t)
        + 2 * eta * (polyFeature h (pt t) - polyCentering h) * coordPartial 0 (polyFeature h) (pt t)) t := by
  have hc := circ_coordPartial_pt (isSmooth_cosT_EX055 1) t
  have hf := circ_coordPartial_pt (isSmooth_polyFeature_EX055 h) t
  have key := (hc.const_mul (-h)).add
    (((hf.sub_const (polyCentering h)).mul (hf.sub_const (polyCentering h))).const_mul eta)
  convert key using 1
  · funext r
    simp only [Pi.add_apply, Pi.mul_apply, polyV]
    ring
  · ring

theorem polyW_deriv_EX055 (h : ℝ) (y : Torus 1) (t : ℝ) :
    HasDerivAt (fun r => polyW h (pt r) y)
      (-2 * eta * (polyFeature h (pt t) - polyFeature h y) * coordPartial 0 (polyFeature h) (pt t)) t := by
  have hf := circ_coordPartial_pt (isSmooth_polyFeature_EX055 h) t
  have key := ((hf.sub_const (polyFeature h y)).mul (hf.sub_const (polyFeature h y))).const_mul (-eta)
  convert key using 1
  · funext r
    simp only [Pi.mul_apply, polyW]
    ring
  · ring

theorem integral_affine_EX055 (h : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (α β : ℝ) :
    ∫ y, (α + β * polyFeature h y) ∂ν = α + β * ∫ y, polyFeature h y ∂ν := by
  have hi : Integrable (polyFeature h) ν :=
    (continuous_polyFeature h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add (integrable_const _) (hi.const_mul β), integral_const, integral_const_mul]
  simp

theorem canonical_V_EX055 (h : ℝ) : (canonical_elementary_polynomial_model h).V = polyV h := rfl

theorem canonical_W_EX055 (h : ℝ) : (canonical_elementary_polynomial_model h).W = polyW h := rfl

theorem drift_eq_EX055 (h : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (x : Torus 1) :
    coordPartial 0 (polyV h) x + ∫ y, coordPartial 0 (fun x' => polyW h x' y) x ∂ν
      = coordPartial 0 (polyDrift_EX055 h ν) x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hV := (circ_coordPartial_pt (isSmooth_polyV_EX055 h) t).unique (polyV_deriv_EX055 h t)
  have hW : ∀ y : Torus 1, coordPartial 0 (fun x' => polyW h x' y) (pt t)
      = -2 * eta * (polyFeature h (pt t) - polyFeature h y) * coordPartial 0 (polyFeature h) (pt t) :=
    fun y => (circ_coordPartial_pt (isSmooth_polyW_left_EX055 h y) t).unique (polyW_deriv_EX055 h y t)
  have hD := (circ_coordPartial_pt (isSmooth_polyDrift_EX055 h ν) t).unique
    (polyPot_deriv_EX055 h _ t)
  rw [hV, hD]
  simp_rw [hW]
  have hpt : ∀ y : Torus 1,
      -2 * eta * (polyFeature h (pt t) - polyFeature h y) * coordPartial 0 (polyFeature h) (pt t)
        = (-2 * eta * polyFeature h (pt t) * coordPartial 0 (polyFeature h) (pt t))
          + (2 * eta * coordPartial 0 (polyFeature h) (pt t)) * polyFeature h y := by
    intro y; ring
  simp_rw [hpt]
  rw [integral_affine_EX055 h ν]
  ring

theorem stationary_iff_gibbs_EX055 (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary (canonical_elementary_polynomial_model h) ν
      ↔ (ν : Measure (Torus 1)) = gibbsMeasure (polyDrift_EX055 h (ν : Measure (Torus 1))) := by
  have hsm := isSmooth_polyDrift_EX055 h (ν : Measure (Torus 1))
  have key : ∀ φ : Torus 1 → ℝ,
      ∫ x, (coordPartial 0 (coordPartial 0 φ) x -
        (coordPartial 0 (canonical_elementary_polynomial_model h).V x
          + ∫ y, coordPartial 0 (fun x' => (canonical_elementary_polynomial_model h).W x' y) x
            ∂(ν : Measure (Torus 1))) * coordPartial 0 φ x) ∂(ν : Measure (Torus 1))
      = ∫ x, (coordPartial 0 (coordPartial 0 φ) x
        - coordPartial 0 (polyDrift_EX055 h (ν : Measure (Torus 1))) x * coordPartial 0 φ x)
          ∂(ν : Measure (Torus 1)) := by
    intro φ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [canonical_V_EX055, canonical_W_EX055, drift_eq_EX055 h (ν : Measure (Torus 1)) x]
  constructor
  · intro hs
    exact eq_gibbs_of_stationary hsm fun φ hφ => by rw [← key]; exact hs φ hφ
  · intro heq φ hφ
    rw [key]
    have := gibbs_stationary hsm hφ
    rwa [← heq] at this

theorem polyFeature_bound_EX055 (h : ℝ) : ∃ C : ℝ, ∀ x : Torus 1, |polyFeature h x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Torus 1))).exists_bound_of_continuousOn
    (continuous_polyFeature h).continuousOn
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x (Set.mem_univ x)⟩

theorem quadratic_W_nonneg_EX055 (h : ℝ) (μ : ProbabilityMeasure (Torus 1)) (g : Torus 1 → ℝ)
    (hg : Integrable g (μ : Measure (Torus 1))) (hmean : ∫ x, g x ∂(μ : Measure (Torus 1)) = 0) :
    0 ≤ ∫ p, (canonical_elementary_polynomial_model h).W p.1 p.2 * (g p.1 * g p.2)
      ∂((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := by
  obtain ⟨C, hC⟩ := polyFeature_bound_EX055 h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hP : Continuous (polyFeature h) := continuous_polyFeature h
  have hPm : AEStronglyMeasurable (polyFeature h) (μ : Measure (Torus 1)) := hP.aestronglyMeasurable
  have hPb : ∀ᵐ x ∂(μ : Measure (Torus 1)), ‖polyFeature h x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hPPb : ∀ᵐ x ∂(μ : Measure (Torus 1)), ‖polyFeature h x * polyFeature h x‖ ≤ C * C :=
    Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC x) (hC x) (abs_nonneg _) hC0)
  have hPPm : AEStronglyMeasurable (fun x => polyFeature h x * polyFeature h x) (μ : Measure (Torus 1)) :=
    (hP.mul hP).aestronglyMeasurable
  set u0 : Torus 1 → ℝ := g with hu0def
  set u1 : Torus 1 → ℝ := fun x => polyFeature h x * g x with hu1def
  set u2 : Torus 1 → ℝ := fun x => polyFeature h x * polyFeature h x * g x with hu2def
  have hu1 : Integrable u1 (μ : Measure (Torus 1)) := hg.bdd_mul hPm hPb
  have hu2 : Integrable u2 (μ : Measure (Torus 1)) := hg.bdd_mul hPPm hPPb
  have key : (fun p : Torus 1 × Torus 1 =>
      (canonical_elementary_polynomial_model h).W p.1 p.2 * (g p.1 * g p.2)) =
      fun p => (-eta) * (u2 p.1 * u0 p.2 - 2 * (u1 p.1 * u1 p.2) + u0 p.1 * u2 p.2) := by
    funext p
    simp only [model_W, polyW, hu0def, hu1def, hu2def]
    ring
  have i1 : Integrable (fun z : Torus 1 × Torus 1 => u2 z.1 * u0 z.2)
      ((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := hu2.mul_prod hg
  have i2 : Integrable (fun z : Torus 1 × Torus 1 => u1 z.1 * u1 z.2)
      ((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := hu1.mul_prod hu1
  have i3 : Integrable (fun z : Torus 1 × Torus 1 => u0 z.1 * u2 z.2)
      ((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := hg.mul_prod hu2
  have hsub : Integrable (fun z : Torus 1 × Torus 1 => u2 z.1 * u0 z.2 - 2 * (u1 z.1 * u1 z.2))
      ((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := i1.sub (i2.const_mul 2)
  have j2 : Integrable (fun z : Torus 1 × Torus 1 => 2 * (u1 z.1 * u1 z.2))
      ((μ : Measure (Torus 1)).prod (μ : Measure (Torus 1))) := i2.const_mul 2
  rw [key, integral_const_mul, integral_add hsub i3, integral_sub i1 j2, integral_const_mul,
    integral_prod_mul, integral_prod_mul, integral_prod_mul]
  have hm : ∫ x, u0 x ∂(μ : Measure (Torus 1)) = 0 := hmean
  rw [hm]
  have : (0 : ℝ) ≤ (∫ x, u1 x ∂(μ : Measure (Torus 1))) ^ 2 := sq_nonneg _
  nlinarith [eta_pos]

theorem densityHessian_coercive_EX055 (h : ℝ) (μ : ProbabilityMeasure (Torus 1)) :
    IsCoerciveDensityHessian (canonical_elementary_polynomial_model h) μ := by
  refine ⟨1, one_pos, fun f => ?_⟩
  rw [inner_densityHessian, one_mul]
  have hq := quadratic_W_nonneg_EX055 h μ (f : Lp ℝ 2 (μ : Measure (Torus 1)))
    (integrable_lp μ f) ((mem_centeredL2 _).1 f.2)
  linarith [sq_nonneg ‖f‖]

/-! ### Moment bridge: Gibbs integrals of the feature are the EX054 moments -/

theorem moment_gibbs_EX055 (h s : ℝ) :
    ∫ x, polyFeature h x ∂(gibbsMeasure (polyPot_EX055 h s)) = moment_EX054 h s := by
  have hU := isSmooth_polyPot_EX055 h s
  have key2 : ∀ x : Torus 1, Real.exp (-polyPot_EX055 h s x) = weight_EX054 h s (angEquiv x) := by
    intro x
    have e1 : angCos (angEquiv x) = cosT 1 x := DGPS.Circle.VonMisesSmallField.ex010_angCos x
    simp only [polyPot_EX055, weight_EX054, feature_model_EX054, e1]
    congr 1
    ring
  have key : ∀ x : Torus 1, Real.exp (-polyPot_EX055 h s x) * polyFeature h x
      = (fun θ => feature_EX054 h θ * weight_EX054 h s θ) (angEquiv x) := by
    intro x
    simp only
    rw [key2 x, ← feature_model_EX054 h x]
    ring
  have hZ : gibbsZ (polyPot_EX055 h s) = partition_EX054 h s := by
    unfold gibbsZ partition_EX054
    calc ∫ x, Real.exp (-polyPot_EX055 h s x) ∂haar 1
        = ∫ x, (fun θ => weight_EX054 h s θ) (angEquiv x) ∂haar 1 := by
          congr 1; funext x; simp only [key2 x]
      _ = ∫ θ, weight_EX054 h s θ ∂angHaar := integral_comp_angEquiv _
  rw [integral_gibbsMeasure_eq hU, moment_EX054]
  simp only [gibbsDensity, div_mul_eq_mul_div]
  rw [integral_div, hZ]
  congr 1
  calc ∫ x, Real.exp (-polyPot_EX055 h s x) * polyFeature h x ∂haar 1
      = ∫ x, (fun θ => feature_EX054 h θ * weight_EX054 h s θ) (angEquiv x) ∂haar 1 := by
        congr 1; funext x; exact key x
    _ = ∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar :=
        integral_comp_angEquiv (fun θ => feature_EX054 h θ * weight_EX054 h s θ)

/-! ### Real potential and interaction energies of the canonical model -/

theorem integral_polyPot_EX055 (h s : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    ∫ x, polyPot_EX055 h s x ∂ν = -h * ∫ x, cosT 1 x ∂ν + s * ∫ x, polyFeature h x ∂ν := by
  have hc : Continuous (cosT 1) := (isSmooth_cosT_EX055 1).continuous_torus
  have hP : Continuous (polyFeature h) := continuous_polyFeature h
  have i1 : Integrable (fun x => -h * cosT 1 x) ν :=
    (continuous_const.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => s * polyFeature h x) ν :=
    (continuous_const.mul hP).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold polyPot_EX055
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul]

theorem integral_sq_sub_EX055 (f : Torus 1 → ℝ) (hf : Continuous f) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] (a : ℝ) :
    ∫ x, (f x - a) ^ 2 ∂ν = ∫ x, f x ^ 2 ∂ν - 2 * a * ∫ x, f x ∂ν + a ^ 2 := by
  have i1 : Integrable (fun x => f x ^ 2) ν :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable f ν := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i3 : Integrable (fun x => -2 * a * f x) ν := i2.const_mul _
  have J0 : ∫ x, (f x - a) ^ 2 ∂ν = ∫ x, (f x ^ 2 + -2 * a * f x + a ^ 2) ∂ν := by
    congr 1; funext x; ring
  have J1 : ∫ x, (f x ^ 2 + -2 * a * f x) ∂ν = ∫ x, f x ^ 2 ∂ν + ∫ x, -2 * a * f x ∂ν :=
    integral_add i1 i3
  have J2 : ∫ x, (f x ^ 2 + -2 * a * f x + a ^ 2) ∂ν
      = ∫ x, (f x ^ 2 + -2 * a * f x) ∂ν + ∫ x, a ^ 2 ∂ν :=
    integral_add (i1.add i3) (integrable_const _)
  have J3 : ∫ x, -2 * a * f x ∂ν = -2 * a * ∫ x, f x ∂ν := by
    rw [integral_const_mul]
  have J4 : ∫ x, a ^ 2 ∂ν = a ^ 2 := by simp
  rw [J0, J2, J1, J3, J4]
  ring

theorem potential_real_EX055 (h : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    potentialEnergy (canonical_elementary_polynomial_model h) ν +
        (1 / 2 : ℝ) * interactionEnergy (canonical_elementary_polynomial_model h) ν =
      -h * ∫ x, cosT 1 x ∂ν + eta * ((∫ x, polyFeature h x ∂ν) - polyCentering h) ^ 2 := by
  have hc : Continuous (cosT 1) := (isSmooth_cosT_EX055 1).continuous_torus
  have hP : Continuous (polyFeature h) := continuous_polyFeature h
  have hintP : ∀ f : Torus 1 × Torus 1 → ℝ, Continuous f →
      Integrable f (ν.prod ν) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hV : potentialEnergy (canonical_elementary_polynomial_model h) ν =
      -h * ∫ x, cosT 1 x ∂ν + eta * (∫ x, polyFeature h x ^ 2 ∂ν
        - 2 * polyCentering h * ∫ x, polyFeature h x ∂ν + polyCentering h ^ 2) := by
    unfold potentialEnergy
    change ∫ x, polyV h x ∂ν = _
    have hQ : Continuous fun x => (polyFeature h x - polyCentering h) ^ 2 :=
      (hP.sub continuous_const).pow 2
    have i1 : Integrable (fun x => -h * cosT 1 x) ν :=
      (continuous_const.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have i2 : Integrable (fun x => eta * (polyFeature h x - polyCentering h) ^ 2) ν :=
      (hQ.const_mul eta).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have e : ∫ x, polyV h x ∂ν
        = ∫ x, (-h * cosT 1 x + eta * (polyFeature h x - polyCentering h) ^ 2) ∂ν := by
      congr 1
    have J1 : ∫ x, (-h * cosT 1 x + eta * (polyFeature h x - polyCentering h) ^ 2) ∂ν
        = ∫ x, -h * cosT 1 x ∂ν + ∫ x, eta * (polyFeature h x - polyCentering h) ^ 2 ∂ν :=
      integral_add i1 i2
    have J2 : ∫ x, -h * cosT 1 x ∂ν = -h * ∫ x, cosT 1 x ∂ν := by
      rw [integral_const_mul]
    have J3 : ∫ x, eta * (polyFeature h x - polyCentering h) ^ 2 ∂ν
        = eta * ∫ x, (polyFeature h x - polyCentering h) ^ 2 ∂ν := by
      rw [integral_const_mul]
    have J4 : ∫ x, (polyFeature h x - polyCentering h) ^ 2 ∂ν
        = ∫ x, polyFeature h x ^ 2 ∂ν - 2 * polyCentering h * ∫ x, polyFeature h x ∂ν
          + polyCentering h ^ 2 :=
      integral_sq_sub_EX055 _ hP ν _
    rw [e, J1, J2, J3, J4]
  have hI : interactionEnergy (canonical_elementary_polynomial_model h) ν =
      -2 * eta * (∫ x, polyFeature h x ^ 2 ∂ν - (∫ x, polyFeature h x ∂ν) ^ 2) := by
    unfold interactionEnergy
    change ∫ p, polyW h p.1 p.2 ∂(ν.prod ν) = _
    have e : ∀ p : Torus 1 × Torus 1, polyW h p.1 p.2 =
        (-eta) * (polyFeature h p.1 ^ 2 + polyFeature h p.2 ^ 2
          - 2 * (polyFeature h p.1 * polyFeature h p.2)) := by
      intro p; unfold polyW; ring
    simp only [e]
    have hA : Continuous fun p : Torus 1 × Torus 1 => polyFeature h p.1 ^ 2 :=
      (hP.comp continuous_fst).pow 2
    have hB : Continuous fun p : Torus 1 × Torus 1 => polyFeature h p.2 ^ 2 :=
      (hP.comp continuous_snd).pow 2
    have hC : Continuous fun p : Torus 1 × Torus 1 => polyFeature h p.1 * polyFeature h p.2 :=
      (hP.comp continuous_fst).mul (hP.comp continuous_snd)
    have iA : Integrable (fun p : Torus 1 × Torus 1 => polyFeature h p.1 ^ 2) (ν.prod ν) :=
      hintP _ hA
    have iB : Integrable (fun p : Torus 1 × Torus 1 => polyFeature h p.2 ^ 2) (ν.prod ν) :=
      hintP _ hB
    have iC : Integrable (fun p : Torus 1 × Torus 1 => 2 * (polyFeature h p.1 * polyFeature h p.2))
        (ν.prod ν) := hintP _ (hC.const_mul 2)
    have L1 : ∫ p : Torus 1 × Torus 1,
        (polyFeature h p.1 ^ 2 + polyFeature h p.2 ^ 2 - 2 * (polyFeature h p.1 * polyFeature h p.2))
          ∂(ν.prod ν)
        = ∫ p : Torus 1 × Torus 1, (polyFeature h p.1 ^ 2 + polyFeature h p.2 ^ 2) ∂(ν.prod ν)
          - ∫ p : Torus 1 × Torus 1, 2 * (polyFeature h p.1 * polyFeature h p.2) ∂(ν.prod ν) :=
      integral_sub (iA.add iB) iC
    have L2 : ∫ p : Torus 1 × Torus 1, (polyFeature h p.1 ^ 2 + polyFeature h p.2 ^ 2) ∂(ν.prod ν)
        = ∫ p : Torus 1 × Torus 1, polyFeature h p.1 ^ 2 ∂(ν.prod ν)
          + ∫ p : Torus 1 × Torus 1, polyFeature h p.2 ^ 2 ∂(ν.prod ν) :=
      integral_add iA iB
    have L3 : ∫ p : Torus 1 × Torus 1, 2 * (polyFeature h p.1 * polyFeature h p.2) ∂(ν.prod ν)
        = 2 * ∫ p : Torus 1 × Torus 1, (polyFeature h p.1 * polyFeature h p.2) ∂(ν.prod ν) := by
      rw [integral_const_mul]
    have f1 : ∫ p : Torus 1 × Torus 1, polyFeature h p.1 ^ 2 ∂(ν.prod ν) = ∫ x, polyFeature h x ^ 2 ∂ν := by
      rw [integral_fun_fst (fun x => polyFeature h x ^ 2)]; simp
    have f2 : ∫ p : Torus 1 × Torus 1, polyFeature h p.2 ^ 2 ∂(ν.prod ν) = ∫ x, polyFeature h x ^ 2 ∂ν := by
      rw [integral_fun_snd (fun x => polyFeature h x ^ 2)]; simp
    have f3 : ∫ p : Torus 1 × Torus 1, polyFeature h p.1 * polyFeature h p.2 ∂(ν.prod ν)
        = (∫ x, polyFeature h x ∂ν) * ∫ x, polyFeature h x ∂ν :=
      integral_prod_mul (polyFeature h) (polyFeature h)
    rw [integral_const_mul, L1, L2, L3, f1, f2, f3]
    ring
  rw [hV, hI]
  ring

/-! ### Gibbs shift of relative entropy -/

theorem bound_EX055 (U : Torus 1 → ℝ) (hU : Continuous U) : ∃ B : ℝ, ∀ x, |-U x| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Torus 1))).exists_bound_of_continuousOn
    hU.neg.continuousOn
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x (Set.mem_univ x)⟩

theorem klDiv_gibbs_ne_top_iff_EX055 (U : Torus 1 → ℝ) (hU : IsSmoothPeriodic U)
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    klDiv ν (gibbsMeasure U) ≠ ⊤ ↔ klDiv ν (haar 1) ≠ ⊤ := by
  have hT : gibbsMeasure U = (haar 1).tilted (fun x => -U x) := rfl
  obtain ⟨B, hB⟩ := bound_EX055 U hU.continuous_torus
  rw [hT]
  exact DGPS.Lipschitz.klDiv_tilted_ne_top_iff (f := fun x => -U x) (B := B)
    hU.continuous_torus.neg.measurable hB

theorem klDiv_gibbs_toReal_EX055 (U : Torus 1 → ℝ) (hU : IsSmoothPeriodic U)
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (hν : klDiv ν (haar 1) ≠ ⊤) :
    (klDiv ν (gibbsMeasure U)).toReal =
      (klDiv ν (haar 1)).toReal + ∫ x, U x ∂ν + Real.log (gibbsZ U) := by
  have hT : gibbsMeasure U = (haar 1).tilted (fun x => -U x) := rfl
  obtain ⟨B, hB⟩ := bound_EX055 U hU.continuous_torus
  have key := (DGPS.Lipschitz.klDiv_tilted_forward (ρ := ν) (ν := haar 1) (f := fun x => -U x)
    (B := B) hU.continuous_torus.neg.measurable hB hν).2
  rw [hT, key]
  simp only [integral_neg, gibbsZ]
  ring

/-- Gibbs potential at `s`, with the constant-free shape `-h cos + s P_h`. -/
noncomputable def gapOffset_EX055 (h s : ℝ) (ν : Measure (Torus 1)) : ℝ :=
  -s * (∫ x, polyFeature h x ∂ν) + eta * ((∫ x, polyFeature h x ∂ν) - polyCentering h) ^ 2
    - Real.log (gibbsZ (polyPot_EX055 h s))

/-- Free energy of a probability in the Gibbs form at potential `polyPot h s`. -/
theorem freeEnergy_gibbs_EX055 (h s : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (canonical_elementary_polynomial_model h) ν =
      ((klDiv (ν : Measure (Torus 1)) (gibbsMeasure (polyPot_EX055 h s)) : ℝ≥0∞) : EReal) +
        ((gapOffset_EX055 h s (ν : Measure (Torus 1)) : ℝ) : EReal) := by
  have hU := isSmooth_polyPot_EX055 h s
  rw [freeEnergy_eq_klDiv, potential_real_EX055 h (ν : Measure (Torus 1))]
  by_cases hH : klDiv (ν : Measure (Torus 1)) (haar 1) = ⊤
  · have hG : klDiv (ν : Measure (Torus 1)) (gibbsMeasure (polyPot_EX055 h s)) = ⊤ := by
      by_contra hne
      exact (klDiv_gibbs_ne_top_iff_EX055 _ hU _).mp hne hH
    rw [hH, hG, EReal.coe_ennreal_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  · have hG : klDiv (ν : Measure (Torus 1)) (gibbsMeasure (polyPot_EX055 h s)) ≠ ⊤ :=
      (klDiv_gibbs_ne_top_iff_EX055 _ hU _).mpr hH
    rw [← EReal.coe_ennreal_toReal hH, ← EReal.coe_ennreal_toReal hG, ← EReal.coe_add,
      ← EReal.coe_add]
    congr 1
    rw [klDiv_gibbs_toReal_EX055 _ hU _ hH, integral_polyPot_EX055]
    unfold gapOffset_EX055
    ring

/-! ### Equilibrium measure, gap identity, minimization, stationarity, Hessian -/

instance polyPot_fact_EX055 (h s : ℝ) : Fact (IsSmoothPeriodic (polyPot_EX055 h s)) :=
  ⟨isSmooth_polyPot_EX055 h s⟩

/-- The canonical equilibrium `qhat_h` as a measure: the Gibbs measure at the root potential. -/
noncomputable def polyEqM_EX055 (h : ℝ) : Measure (Torus 1) :=
  gibbsMeasure (polyPot_EX055 h (root_EX054 h))

instance polyEqM_isProb_EX055 (h : ℝ) : IsProbabilityMeasure (polyEqM_EX055 h) := by
  unfold polyEqM_EX055
  infer_instance

/-- The canonical equilibrium `qhat_h` as a probability measure. -/
noncomputable def polyEq_EX055 (h : ℝ) : ProbabilityMeasure (Torus 1) :=
  ⟨polyEqM_EX055 h, polyEqM_isProb_EX055 h⟩

theorem polyEq_coe_EX055 (h : ℝ) :
    ((polyEq_EX055 h : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = polyEqM_EX055 h := rfl

theorem mean_polyEq_EX055 (h : ℝ) :
    ∫ x, polyFeature h x ∂(polyEqM_EX055 h) = moment_EX054 h (root_EX054 h) :=
  moment_gibbs_EX055 h (root_EX054 h)

/-- Shift of the Gibbs offset when the reference measure has mean `moment(root)`. -/
theorem gapOffset_shift_EX055 (h : ℝ) (ν q : Measure (Torus 1))
    (hq : ∫ x, polyFeature h x ∂q = moment_EX054 h (root_EX054 h)) :
    gapOffset_EX055 h (root_EX054 h) ν =
      gapOffset_EX055 h (root_EX054 h) q
        + eta * ((∫ x, polyFeature h x ∂ν) - ∫ x, polyFeature h x ∂q) ^ 2 := by
  unfold gapOffset_EX055
  rw [hq]
  linear_combination (-((∫ x, polyFeature h x ∂ν) - moment_EX054 h (root_EX054 h)))
    * root_equation_EX054 h

theorem freeEnergy_polyEq_EX055 (h : ℝ) :
    freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h) =
      ((gapOffset_EX055 h (root_EX054 h) (polyEqM_EX055 h) : ℝ) : EReal) := by
  have hK0 : klDiv (polyEqM_EX055 h) (polyEqM_EX055 h) = 0 := klDiv_self _
  have key : freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h) =
      ((klDiv (polyEqM_EX055 h) (polyEqM_EX055 h) : ℝ≥0∞) : EReal)
        + ((gapOffset_EX055 h (root_EX054 h) (polyEqM_EX055 h) : ℝ) : EReal) :=
    freeEnergy_gibbs_EX055 h (root_EX054 h) (polyEq_EX055 h)
  rw [key, hK0]
  simp

/-- Exact gap identity: `F(ν) = F(qhat) + H(ν | qhat) + η (ν(P_h) - qhat(P_h))²`. -/
theorem gap_identity_EX055 (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (canonical_elementary_polynomial_model h) ν =
      freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h)
        + ((klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h) : ℝ≥0∞) : EReal)
        + ((eta * ((∫ x, polyFeature h x ∂(ν : Measure (Torus 1)))
            - ∫ x, polyFeature h x ∂(polyEqM_EX055 h)) ^ 2 : ℝ) : EReal) := by
  have hgap : freeEnergy (canonical_elementary_polynomial_model h) ν =
      ((klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h) : ℝ≥0∞) : EReal)
        + ((gapOffset_EX055 h (root_EX054 h) (ν : Measure (Torus 1)) : ℝ) : EReal) :=
    freeEnergy_gibbs_EX055 h (root_EX054 h) ν
  rw [hgap, freeEnergy_polyEq_EX055 h,
    gapOffset_shift_EX055 h (ν : Measure (Torus 1)) (polyEqM_EX055 h) (mean_polyEq_EX055 h),
    EReal.coe_add]
  abel

theorem freeEnergyMinimum_eq_EX055 (h : ℝ) :
    freeEnergyMinimum (canonical_elementary_polynomial_model h) =
      freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h) := by
  apply le_antisymm
  · exact iInf_le _ (polyEq_EX055 h)
  · apply le_iInf
    intro ν
    rw [gap_identity_EX055 h ν]
    exact le_trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
      (le_add_of_nonneg_right (EReal.coe_nonneg.2 (mul_nonneg eta_pos.le (sq_nonneg _))))

theorem freeEnergy_eq_min_iff_EX055 (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (canonical_elementary_polynomial_model h) ν =
        freeEnergyMinimum (canonical_elementary_polynomial_model h) ↔
      ν = polyEq_EX055 h := by
  rw [freeEnergyMinimum_eq_EX055 h]
  constructor
  · intro hν
    rw [gap_identity_EX055 h ν, freeEnergy_polyEq_EX055 h] at hν
    have hKt : klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h) ≠ ⊤ := by
      intro hKt
      rw [hKt, EReal.coe_ennreal_top, EReal.coe_add_top,
        EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hν
      exact EReal.coe_ne_top _ hν.symm
    have hr := EReal.coe_ennreal_toReal hKt
    rw [← hr, ← EReal.coe_add, ← EReal.coe_add] at hν
    have hreal := EReal.coe_eq_coe_iff.1 hν
    have hXn : 0 ≤ eta * ((∫ x, polyFeature h x ∂(ν : Measure (Torus 1)))
        - ∫ x, polyFeature h x ∂(polyEqM_EX055 h)) ^ 2 :=
      mul_nonneg eta_pos.le (sq_nonneg _)
    have hKn : 0 ≤ (klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h)).toReal :=
      ENNReal.toReal_nonneg
    have hr0 : (klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h)).toReal = 0 := by
      linarith
    rcases (ENNReal.toReal_eq_zero_iff _).1 hr0 with hK0 | htop
    · have : IsProbabilityMeasure (ν : Measure (Torus 1)) := ν.2
      have hmeas : (ν : Measure (Torus 1)) = polyEqM_EX055 h := klDiv_eq_zero_iff.1 hK0
      exact Subtype.ext hmeas
    · exact absurd htop hKt
  · rintro rfl
    rfl

theorem stationary_iff_eq_EX055 (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary (canonical_elementary_polynomial_model h) ν ↔
      ν = polyEq_EX055 h := by
  constructor
  · intro hs
    have hν := (stationary_iff_gibbs_EX055 h ν).1 hs
    obtain ⟨s', hs'⟩ : ∃ s' : ℝ,
        s' = 2 * eta * ((∫ y, polyFeature h y ∂(ν : Measure (Torus 1))) - polyCentering h) :=
      ⟨_, rfl⟩
    have hν' : (ν : Measure (Torus 1)) = gibbsMeasure (polyPot_EX055 h s') := by
      rw [hs']
      exact hν
    have hm : ∫ y, polyFeature h y ∂(ν : Measure (Torus 1)) = moment_EX054 h s' := by
      rw [hν']
      exact moment_gibbs_EX055 h s'
    rw [hm] at hs'
    have hsr : s' = root_EX054 h := root_unique_EX054 h s' hs'
    apply Subtype.ext
    calc (ν : Measure (Torus 1)) = gibbsMeasure (polyPot_EX055 h s') := hν'
      _ = gibbsMeasure (polyPot_EX055 h (root_EX054 h)) := by rw [hsr]
      _ = polyEqM_EX055 h := rfl
  · rintro rfl
    have hdrift : polyDrift_EX055 h (polyEqM_EX055 h) = polyPot_EX055 h (root_EX054 h) := by
      unfold polyDrift_EX055
      rw [mean_polyEq_EX055, ← root_equation_EX054 h]
    apply (stationary_iff_gibbs_EX055 h _).2
    calc ((polyEq_EX055 h : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        = gibbsMeasure (polyPot_EX055 h (root_EX054 h)) := rfl
      _ = gibbsMeasure (polyDrift_EX055 h ((polyEq_EX055 h : ProbabilityMeasure (Torus 1)) :
            Measure (Torus 1))) := by
          rw [polyEq_coe_EX055, hdrift]

theorem hessian_ge_id_EX055 (h : ℝ) (μ : ProbabilityMeasure (Torus 1)) (f : centeredL2 μ) :
    ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (canonical_elementary_polynomial_model h) μ f) := by
  rw [inner_densityHessian]
  have hq := quadratic_W_nonneg_EX055 h μ (f : Lp ℝ 2 (μ : Measure (Torus 1)))
    (integrable_lp μ f) ((mem_centeredL2 _).1 f.2)
  linarith

/-- EX055 main theorem: for the canonical polynomial model with coupling `h`, the equilibrium
`qhat_h` is the unique scalar equilibrium and the unique distributional stationary probability;
the free-energy gap is `H(ν | qhat_h) + η (ν(P_h) - qhat_h(P_h))²`; the minimum is attained
exactly at `qhat_h`; and the density Hessian at `qhat_h` dominates the identity. -/
theorem polynomial_exact_gap_stationary_uniqueness_and_hessian (h : ℝ) :
    (∃! s : ℝ, s = 2 * eta * (moment_EX054 h s - polyCentering h)) ∧
    IsCircleDistributionalStationary (canonical_elementary_polynomial_model h) (polyEq_EX055 h) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      IsCircleDistributionalStationary (canonical_elementary_polynomial_model h) ν →
        ν = polyEq_EX055 h) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy (canonical_elementary_polynomial_model h) ν =
        freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h)
          + ((klDiv (ν : Measure (Torus 1)) (polyEqM_EX055 h) : ℝ≥0∞) : EReal)
          + ((eta * ((∫ x, polyFeature h x ∂(ν : Measure (Torus 1)))
              - ∫ x, polyFeature h x ∂(polyEqM_EX055 h)) ^ 2 : ℝ) : EReal)) ∧
    freeEnergyMinimum (canonical_elementary_polynomial_model h) =
      freeEnergy (canonical_elementary_polynomial_model h) (polyEq_EX055 h) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy (canonical_elementary_polynomial_model h) ν =
          freeEnergyMinimum (canonical_elementary_polynomial_model h) ↔
        ν = polyEq_EX055 h) ∧
    (∀ f : centeredL2 (polyEq_EX055 h),
      ‖f‖ ^ 2 ≤ inner ℝ f
        (densityHessian (canonical_elementary_polynomial_model h) (polyEq_EX055 h) f)) :=
  ⟨⟨root_EX054 h, root_equation_EX054 h, fun s hs => root_unique_EX054 h s hs⟩,
    (stationary_iff_eq_EX055 h _).2 rfl,
    fun ν hν => (stationary_iff_eq_EX055 h ν).1 hν,
    gap_identity_EX055 h,
    freeEnergyMinimum_eq_EX055 h,
    freeEnergy_eq_min_iff_EX055 h,
    fun f => hessian_ge_id_EX055 h (polyEq_EX055 h) f⟩

end DGPS.Examples.PolynomialExactGap
