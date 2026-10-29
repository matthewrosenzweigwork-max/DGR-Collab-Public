import DGPS.Examples.AttractiveXYCritical
import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel

/-!
# Critical stationary uniqueness (EX020)

The Gibbs fixed-point classification is proved by rotating the first moment and
using the strict Bessel ratio bound. Distributional and absolute-domain bridges
are proved separately so that their hypotheses remain visible.

R5 correspondence: the existing circle distributional predicate is the exact
physical-period-one PDE from preparation definitions Section 7: every smooth
real periodic test and every Borel probability, with generator phi'' minus
(V' + integral of the first W derivative) times phi'. No density assumption
appears in its Gibbs identification. The family clause uses actual common-force
dissipation, arbitrary positive normalized weights and only absolute square-root
H1 roots, including roots with zero sets.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal ContDiff
open DGPS DGPS.Models DGPS.Examples.AttractiveXY
open DGPS.Examples.AttractiveXYCritical
open DGPS.Examples.ThreeSpeciesCircle
  (gibbsMeasure gibbsDensity gibbsZ eq_gibbs_of_stationary gibbs_stationary
    circ_withDensity_integral IsCircleDistributionalStationary)
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Examples.AttractiveXYStationaryEX020

theorem integral_firstTilt_EX020 (z1 z2 : ℝ) (hb : 0 < z1 ^ 2 + z2 ^ 2) :
    ∫ x, Real.exp (2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) *
      (z1 * (xyMode x).re + z2 * (xyMode x).im) ∂haar 1 =
      Real.sqrt (z1 ^ 2 + z2 ^ 2) * besselI 1 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) := by
  have _ := isAddHaar_haar_xyc
  set w : ℂ := ⟨z1, z2⟩ with hw
  have hw0 : w ≠ 0 := by
    intro h
    have h1 : z1 = 0 := congrArg Complex.re h
    have h2 : z2 = 0 := congrArg Complex.im h
    rw [h1, h2] at hb
    simp at hb
  have hn : ‖w‖ = Real.sqrt (z1 ^ 2 + z2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hw]
    simp [sq]
  set x0 : Torus 1 := torusLift (fun _ => Complex.arg w / (2 * Real.pi)) with hx0
  have hre : (xyMode x0).re = z1 / ‖w‖ := by
    rw [hx0, xyMode_re_lift]
    have : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by field_simp
    rw [this, Complex.cos_arg hw0]
  have him : (xyMode x0).im = z2 / ‖w‖ := by
    rw [hx0, xyMode_im_lift]
    have : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by field_simp
    rw [this, Complex.sin_arg]
  have key : ∀ x : Torus 1,
      z1 * (xyMode x).re + z2 * (xyMode x).im = ‖w‖ * (xyMode (x - x0)).re := by
    intro x
    rw [xyMode_re_sub, hre, him]
    field_simp
  simp_rw [key]
  have hp : ∀ x : Torus 1,
      Real.exp (2 * (‖w‖ * (xyMode (x - x0)).re)) * (‖w‖ * (xyMode (x - x0)).re) =
      ‖w‖ * (fun y => Real.exp ((2 * ‖w‖) * (xyMode y).re) * (xyMode y).re) (x - x0) := by
    intro x
    rw [show 2 * (‖w‖ * (xyMode (x - x0)).re) =
      (2 * ‖w‖) * (xyMode (x - x0)).re by ring]
    ring
  simp_rw [hp]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y => Real.exp ((2 * ‖w‖) * (xyMode y).re) * (xyMode y).re) x0]
  have hi : ∫ x, Real.exp ((2 * ‖w‖) * (xyMode x).re) * (xyMode x).re ∂haar 1 =
      besselI 1 (2 * ‖w‖) := by
    rw [besselI_one]
    simp_rw [pow_one, xyMode_re_eq_angCos_xyc]
    exact integral_comp_angEquiv (fun θ => Real.exp ((2 * ‖w‖) * angCos θ) * angCos θ)
  rw [hi, hn]

theorem frozen_fixed_unique_EX020 (ν : ProbabilityMeasure (Torus 1))
    (hfix : (ν : Measure (Torus 1)) = (xyFrozenLaw 2 0 (ν : Measure (Torus 1))).measure) :
    ν = haarProbability 1 := by
  set z1 := xyZ1 (ν : Measure (Torus 1)) with hz1
  set z2 := xyZ2 (ν : Measure (Torus 1)) with hz2
  have hnonneg : 0 ≤ z1 ^ 2 + z2 ^ 2 := by positivity
  have hzero : z1 ^ 2 + z2 ^ 2 = 0 := by
    by_contra hn
    have hb : 0 < z1 ^ 2 + z2 ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hn)
    have hi : ∫ x, (z1 * (xyMode x).re + z2 * (xyMode x).im) ∂(ν : Measure (Torus 1)) =
        z1 ^ 2 + z2 ^ 2 := by
      rw [integral_add ((integrable_xyMode_re _).const_mul _) ((integrable_xyMode_im _).const_mul _),
        integral_const_mul, integral_const_mul]
      change z1 * z1 + z2 * z2 = _
      ring
    have hden : xyPartition (0 + 2 * z1) (2 * z2) =
        besselI 0 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) := by
      unfold xyPartition xyTrig
      convert integral_exp_rot_xyc z1 z2 hb using 1
      congr 1
      funext x
      congr 1
      ring
    have hi2 : ∫ x, (z1 * (xyMode x).re + z2 * (xyMode x).im) ∂(ν : Measure (Torus 1)) =
        Real.sqrt (z1 ^ 2 + z2 ^ 2) *
          besselRatio (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) := by
      rw [hfix]
      unfold BoundedPositiveReference.measure
      rw [circ_withDensity_integral (haar 1)
        (xyFrozenLaw 2 0 (ν : Measure (Torus 1))).measurable_density]
      · change (∫ x, (Real.exp (xyTrig (0 + 2 * z1) (2 * z2) 0 x) /
            xyPartition (0 + 2 * z1) (2 * z2)) *
            (z1 * (xyMode x).re + z2 * (xyMode x).im) ∂haar 1) = _
        simp_rw [div_mul_eq_mul_div]
        rw [integral_div, hden]
        have he : ∀ x : Torus 1,
            xyTrig (0 + 2 * z1) (2 * z2) 0 x =
              2 * (z1 * (xyMode x).re + z2 * (xyMode x).im) := by
          intro x
          unfold xyTrig
          ring
        simp_rw [he]
        rw [integral_firstTilt_EX020 z1 z2 hb]
        unfold besselRatio
        ring
      · intro x
        change 0 ≤ Real.exp _ / xyPartition _ _
        exact div_nonneg (Real.exp_pos _).le (xyPartition_pos _ _).le
    have hs := Real.sqrt_pos.2 hb
    have hsq := Real.sq_sqrt hnonneg
    have hratio := DGPS.Circle.BesselMonotonicity.ratio_lt_half (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2))
      (by positivity)
    have hlt : besselRatio (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) <
        Real.sqrt (z1 ^ 2 + z2 ^ 2) := by
      rw [div_lt_iff₀ (by positivity)] at hratio
      nlinarith
    rw [hi] at hi2
    have := mul_lt_mul_of_pos_left hlt hs
    nlinarith
  have h1 : z1 = 0 := by nlinarith [sq_nonneg z2]
  have h2 : z2 = 0 := by nlinarith [sq_nonneg z1]
  apply ProbabilityMeasure.toMeasure_injective
  rw [hfix]
  change (xyFrozen (0 + 2 * z1) (2 * z2)).measure = haar 1
  rw [h1, h2]
  simp [BoundedPositiveReference.measure, xyFrozen, xyTrig, xyPartition]


theorem drift_eq_EX020 (κ h : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (x : Torus 1) :
    coordPartial 0 (attractiveXY κ h).V x +
        ∫ y, coordPartial 0 (fun x' => (attractiveXY κ h).W x' y) x ∂ν =
      coordPartial 0 (xyTrig (-(h + κ * xyZ1 ν)) (-(κ * xyZ2 ν)) 0) x := by
  have hV : (attractiveXY κ h).V = xyTrig (-h) 0 0 := by
    funext y
    simp [attractiveXY_V, xyTrig]
  have hW : ∀ y : Torus 1, (fun x' => (attractiveXY κ h).W x' y) =
      xyTrig (-κ * (xyMode y).re) (-κ * (xyMode y).im) κ := by
    intro y
    funext x'
    rw [attractiveXY_W, xyMode_re_sub]
    unfold xyTrig
    ring
  have hWi : ∀ y : Torus 1,
      coordPartial 0 (fun x' => (attractiveXY κ h).W x' y) x =
        (2 * Real.pi * κ * (xyMode x).im) * (xyMode y).re +
          (-(2 * Real.pi * κ * (xyMode x).re)) * (xyMode y).im := by
    intro y
    rw [hW y, coordPartial_xyTrig]
    unfold xyTrig
    ring
  simp_rw [hWi]
  rw [integral_add ((integrable_xyMode_re ν).const_mul _)
    ((integrable_xyMode_im ν).const_mul _), integral_const_mul, integral_const_mul,
    hV, coordPartial_xyTrig, coordPartial_xyTrig]
  unfold xyZ1 xyZ2 xyTrig
  ring

theorem gibbs_eq_frozen_EX020 (κ h : ℝ) (ν : Measure (Torus 1)) :
    gibbsMeasure (xyTrig (-(h + κ * xyZ1 ν)) (-(κ * xyZ2 ν)) 0) =
      (xyFrozenLaw κ h ν).measure := by
  have he : ∀ x : Torus 1,
      -xyTrig (-(h + κ * xyZ1 ν)) (-(κ * xyZ2 ν)) 0 x =
        xyTrig (h + κ * xyZ1 ν) (κ * xyZ2 ν) 0 x := by
    intro x
    unfold xyTrig
    ring
  unfold gibbsMeasure gibbsDensity gibbsZ
  simp_rw [he]
  rfl

theorem stationary_iff_frozen_EX020 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary (attractiveXY κ h) ν ↔
      (ν : Measure (Torus 1)) = (xyFrozenLaw κ h (ν : Measure (Torus 1))).measure := by
  let U := xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
    (-(κ * xyZ2 (ν : Measure (Torus 1)))) 0
  have hU : IsSmoothPeriodic U := isSmoothPeriodic_xyTrig _ _ _
  have hDrift := drift_eq_EX020 κ h (ν : Measure (Torus 1))
  constructor
  · intro hs
    rw [← gibbs_eq_frozen_EX020]
    exact eq_gibbs_of_stationary hU fun φ hφ => by
      simpa only [U, hDrift] using hs φ hφ
  · intro hs
    rw [← gibbs_eq_frozen_EX020] at hs
    intro φ hφ
    change (ν : Measure (Torus 1)) = gibbsMeasure U at hs
    have hg := gibbs_stationary hU hφ
    rw [← hs] at hg
    simpa only [U, hDrift] using hg

/-- The absolute square-root H1 domain suffices: no density H1 or positivity hypothesis. -/
theorem eq_gibbs_of_zero_score_EX020 (U : Torus 1 → ℝ) (hU : IsSmoothPeriodic U)
    (ρ : AbsoluteDensity 1)
    (hs : ∀ᵐ x ∂haar 1,
      2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x * coordPartial 0 U x = 0) :
    (densityMeasure ρ : Measure (Torus 1)) = gibbsMeasure U := by
  apply eq_gibbs_of_stationary hU
  intro φ hφ
  rw [integral_densityMeasure]
  have hφ1 := hφ.isSmoothPeriodic_coordPartial 0
  have hφ2 := hφ1.isSmoothPeriodic_coordPartial 0
  have hg := (density_gradient ρ).1
  have hi1 : Integrable (fun x => ρ.density x *
      coordPartial 0 (coordPartial 0 φ) x) (haar 1) := by
      obtain ⟨C, hC⟩ := ae_norm_le_of_memLp_top hφ2.memLp_top
      exact ρ.integrable_density.mul_bdd hφ2.continuous_torus.aestronglyMeasurable hC
  have hi2 : Integrable (fun x =>
      ((2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) 0 *
        coordPartial 0 φ x) (haar 1) := by
      obtain ⟨C, hC⟩ := ae_norm_le_of_memLp_top hφ1.memLp_top
      exact ((memLp_coord_of_memLp hg.memLp_grad 0).integrable le_rfl).mul_bdd
        hφ1.continuous_torus.aestronglyMeasurable hC
  have he : (fun x => ρ.density x *
      (coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x))
      =ᵐ[haar 1] fun x => ρ.density x * coordPartial 0 (coordPartial 0 φ) x +
        ((2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) 0 * coordPartial 0 φ x := by
    filter_upwards [hs] with x hx
    simp only [PiLp.smul_apply, smul_eq_mul]
    unfold AbsoluteDensity.density
    have hm := congrArg (fun t : ℝ => ρ.sqrt x * coordPartial 0 φ x * t) hx
    nlinarith only [hm]
  rw [integral_congr_ae he, integral_add hi1 hi2, hg.ibp _ hφ1 0]
  ring

theorem common_force_EX020 (b : AbsoluteDrift (attractiveXY 2 0)) (σ : AbsoluteDensity 1) :
    b.force σ =ᵐ[haar 1] fun x =>
      smoothGrad (xyTrig (-(0 + 2 * xyZ1 (densityMeasure σ : Measure (Torus 1))))
        (-(2 * xyZ2 (densityMeasure σ : Measure (Torus 1)))) 0) x := by
  have h := b.ae_eq_of_isWeakGradient σ
    (isWeakGradientLp_one_of_smooth (isSmoothPeriodic_interactionPotential 2 0 σ))
  filter_upwards [h] with x hx
  rw [hx, interactionPotential_attractiveXY]
  ext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  simp only [smoothGrad_apply, coordPartial_xyTrig]

theorem species_frozen_EX020 (b : AbsoluteDrift (attractiveXY 2 0))
    (F : SpeciesFamily 1) (hD : speciesDissipation (attractiveXY 2 0) b F = 0) :
    ∀ s, (densityMeasure (F.density s) : Measure (Torus 1)) =
      (xyFrozenLaw 2 0 (densityMeasure (barycenter F) : Measure (Torus 1))).measure := by
  intro s
  unfold speciesDissipation at hD
  have hsum := (Finset.sum_eq_zero_iff.mp hD) s (Finset.mem_univ s)
  have hI : (∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2) ∂haar 1) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (ENNReal.ofReal_pos.mpr (F.weight_pos s)).ne'
  have hm : AEMeasurable (fun x => ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)) (haar 1) := by
    exact (((F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable.const_smul
      (2 : ℝ)).add ((F.density s).memLp_sqrt.aestronglyMeasurable.smul
        (b.measurable_force (barycenter F)).aestronglyMeasurable)).norm.aemeasurable.pow_const
          2 |>.ennreal_ofReal
  have ha := (lintegral_eq_zero_iff' hm).mp hI
  rw [← gibbs_eq_frozen_EX020]
  apply eq_gibbs_of_zero_score_EX020 _ (isSmoothPeriodic_xyTrig _ _ _)
  filter_upwards [ha, common_force_EX020 b (barycenter F)] with x hx hf
  have hz : (2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (barycenter F) x = 0 := by
    have hle := ENNReal.ofReal_eq_zero.mp hx
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp
      (le_antisymm hle (sq_nonneg _)))
  have hz0 := congrArg (fun v : Tangent 1 => v 0) hz
  rw [hf] at hz0
  simpa only [SpeciesFamily.sqrtGradient, PiLp.add_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul, smoothGrad_apply] using hz0

theorem species_unique_EX020 (b : AbsoluteDrift (attractiveXY 2 0))
    (F : SpeciesFamily 1) (hD : speciesDissipation (attractiveXY 2 0) b F = 0) :
    ∀ s, densityMeasure (F.density s) = haarProbability 1 := by
  have hs := species_frozen_EX020 b F hD
  let P := xyFrozenLaw 2 0 (densityMeasure (barycenter F) : Measure (Torus 1))
  have h1 : xyZ1 (densityMeasure (barycenter F) : Measure (Torus 1)) = xyZ1 P.measure := by
    rw [xyZ1_barycenter]
    simp_rw [xyZ1, hs]
    rw [← Finset.sum_mul, F.weight_sum, one_mul]
  have h2 : xyZ2 (densityMeasure (barycenter F) : Measure (Torus 1)) = xyZ2 P.measure := by
    rw [xyZ2_barycenter]
    simp_rw [xyZ2, hs]
    rw [← Finset.sum_mul, F.weight_sum, one_mul]
  intro s
  apply frozen_fixed_unique_EX020
  have h1s : xyZ1 (densityMeasure (F.density s) : Measure (Torus 1)) =
      xyZ1 (densityMeasure (barycenter F) : Measure (Torus 1)) := by
    rw [hs s, h1]
  have h2s : xyZ2 (densityMeasure (F.density s) : Measure (Torus 1)) =
      xyZ2 (densityMeasure (barycenter F) : Measure (Torus 1)) := by
    rw [hs s, h2]
  simpa only [xyFrozenLaw, h1s, h2s] using hs s


theorem haar_fixed_EX020 :
    (haarProbability 1 : Measure (Torus 1)) =
      (xyFrozenLaw 2 0 (haarProbability 1 : Measure (Torus 1))).measure := by
  have h1 : xyZ1 (haar 1) = 0 := by
    rw [← re_integral_xyMode_xyc, integral_xyMode_haar_xyc]
    rfl
  have h2 : xyZ2 (haar 1) = 0 := by
    rw [← im_integral_xyMode_xyc, integral_xyMode_haar_xyc]
    rfl
  change haar 1 = (xyFrozen (0 + 2 * xyZ1 (haar 1)) (2 * xyZ2 (haar 1))).measure
  rw [h1, h2]
  simp [BoundedPositiveReference.measure, xyFrozen, xyTrig, xyPartition]

end DGPS.Examples.AttractiveXYStationaryEX020

namespace DGPS.Examples

open DGPS.Examples.AttractiveXYStationaryEX020

/-- EX020: all distributional stationary Borel probabilities are Haar, and every species
in every actual zero-dissipation absolute-domain finite family is Haar. The stationary
predicate uses physical period-one derivatives and every smooth periodic real test. -/
theorem critical_stationary_uniqueness_iff_EX020 :
    (∀ ν : ProbabilityMeasure (Torus 1),
      IsCircleDistributionalStationary (attractiveXY 2 0) ν ↔ ν = haarProbability 1) ∧
    (∀ b : AbsoluteDrift (attractiveXY 2 0), ∀ F : SpeciesFamily 1,
      speciesDissipation (attractiveXY 2 0) b F = 0 →
        ∀ s, densityMeasure (F.density s) = haarProbability 1) := by
  refine ⟨fun ν => ⟨fun hs => frozen_fixed_unique_EX020 ν
    ((stationary_iff_frozen_EX020 2 0 ν).mp hs), ?_⟩, species_unique_EX020⟩
  rintro rfl
  exact (stationary_iff_frozen_EX020 2 0 (haarProbability 1)).mpr haar_fixed_EX020


/-- The canonical stationary implication over every Borel probability. -/
theorem critical_stationary_probability_haar_EX020 (ν : ProbabilityMeasure (Torus 1))
    (hν : IsCircleDistributionalStationary (attractiveXY 2 0) ν) :
    ν = haarProbability 1 :=
  (critical_stationary_uniqueness_iff_EX020.1 ν).mp hν

/-- The canonical finite-family conclusion for the actual critical XY drift. -/
theorem critical_zero_dissipation_family_haar_EX020 (F : SpeciesFamily 1)
    (hD : speciesDissipation (attractiveXY 2 0) (attractiveXYDrift 2 0) F = 0) :
    ∀ s, densityMeasure (F.density s) = haarProbability 1 :=
  critical_stationary_uniqueness_iff_EX020.2 (attractiveXYDrift 2 0) F hD

/-- EX020 in the packet's one-way stationary and finite-family implication form. -/
theorem critical_stationary_uniqueness :
    (∀ ν : ProbabilityMeasure (Torus 1),
      IsCircleDistributionalStationary (attractiveXY 2 0) ν → ν = haarProbability 1) ∧
    (∀ b : AbsoluteDrift (attractiveXY 2 0), ∀ F : SpeciesFamily 1,
      speciesDissipation (attractiveXY 2 0) b F = 0 →
        ∀ s, densityMeasure (F.density s) = haarProbability 1) :=
  ⟨critical_stationary_probability_haar_EX020, critical_stationary_uniqueness_iff_EX020.2⟩

end DGPS.Examples
