import DGPS.Examples.AttractiveXYCritical
import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel
import DGPS.Variational.EquilibriumGibbs

/-!
# Tilted attractive XY model (EX023)

The scalar fixed point is treated with the strict decrease of the Bessel ratio divided
by its argument. All law and variational statements use Borel probability measures.
-/

open MeasureTheory UnitAddTorus DGPS.Circle.AngularNormalization
open scoped ENNReal NNReal ContDiff Topology

namespace DGPS.Examples.AttractiveXYTilt

open DGPS DGPS.Models DGPS.Examples.AttractiveXY
open DGPS.Examples.AttractiveXYCritical
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity

/-- The normalized von Mises probability on the physical unit circle. -/
noncomputable def xyLaw_EX023 (t : ℝ) : ProbabilityMeasure (Torus 1) :=
  ⟨(haar 1).tilted (xyTrig t 0 0), isProbabilityMeasure_tilted (integrable_exp_xyTrig t 0)⟩

theorem partition_EX023 (t : ℝ) : xyPartition t 0 = besselI 0 t := by
  simpa [xyPartition, xyTrig] using integral_exp_re_xyc t

theorem law_integral_EX023 (t : ℝ) (f : Torus 1 → ℝ) :
    ∫ x, f x ∂(xyLaw_EX023 t : Measure (Torus 1)) =
      ∫ x, Real.exp (t * (xyMode x).re) / besselI 0 t * f x ∂haar 1 := by
  change (∫ x, f x ∂(haar 1).tilted (xyTrig t 0 0)) = _
  rw [integral_tilted]
  simp only [xyTrig, zero_mul, add_zero, smul_eq_mul]
  rw [integral_exp_re_xyc]

theorem positive_root_bounds_EX023 {κ h t : ℝ} (hκ : 0 ≤ κ) (_hh : 0 < h)
    (ht : 0 < t) (heq : t = κ * besselRatio t + h) :
    h ≤ t ∧ t ≤ h + κ ∧ (0 < κ → h < t ∧ t < h + κ) := by
  have hg := besselRatio_pos t ht
  have hgu := besselRatio_lt_one t
  refine ⟨?_, ?_, fun hk => ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem positive_root_atMostOne_EX023 {κ h a b : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) (hea : a = κ * besselRatio a + h)
    (heb : b = κ * besselRatio b + h) : a = b := by
  have hno : ∀ {a b : ℝ}, 0 < a → 0 < b →
      a = κ * besselRatio a + h → b = κ * besselRatio b + h → ¬ a < b := by
    intro a b ha hb hea heb hab
    have hr := strictAntiOn_ratio ha hb hab
    have hm := mul_le_mul_of_nonneg_left hr.le hκ
    have hd : h / b < h / a := div_lt_div_of_pos_left hh ha hab
    have hea' : 1 = κ * (besselRatio a / a) + h / a := by
      field_simp [ha.ne']
      nlinarith [hea]
    have heb' : 1 = κ * (besselRatio b / b) + h / b := by
      field_simp [hb.ne']
      nlinarith [heb]
    linarith
  exact le_antisymm (le_of_not_gt (hno hb ha heb hea))
    (le_of_not_gt (hno ha hb hea heb))

theorem positive_root_exists_EX023 {κ h : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) :
    ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h := by
  let f : ℝ → ℝ := fun t => t - κ * besselRatio t - h
  have hc : Continuous f := by
    have hg : Continuous besselRatio := continuous_iff_continuousAt.2
      (fun t => (hasDerivAt_besselRatio t).continuousAt)
    exact (continuous_id.sub (continuous_const.mul hg)).sub continuous_const
  have hlo : f h ≤ 0 := by
    dsimp [f]
    have := mul_nonneg hκ (besselRatio_pos h hh).le
    linarith
  have hhi : 0 ≤ f (h + κ) := by
    dsimp [f]
    have := mul_le_mul_of_nonneg_left (besselRatio_lt_one (h + κ)).le hκ
    linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show h ≤ h + κ by linarith)
    hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨t, lt_of_lt_of_le hh ht.1, by dsimp [f] at hft; linarith⟩

theorem positive_root_unique_EX023 {κ h : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) :
    ∃! t : ℝ, 0 < t ∧ t = κ * besselRatio t + h := by
  obtain ⟨t, ht, he⟩ := positive_root_exists_EX023 hκ hh
  exact ⟨t, ⟨ht, he⟩, fun u hu => positive_root_atMostOne_EX023 hκ hh hu.1 ht hu.2 he⟩

end DGPS.Examples.AttractiveXYTilt

namespace DGPS.Examples.AttractiveXYTilt

open DGPS DGPS.Models DGPS.Examples.AttractiveXY
open DGPS.Examples.AttractiveXYCritical
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity
open InformationTheory

noncomputable def xyBivariateLaw_EX023 (a b : ℝ) : ProbabilityMeasure (Torus 1) :=
  ⟨(haar 1).tilted (xyTrig a b 0), isProbabilityMeasure_tilted (integrable_exp_xyTrig a b)⟩

theorem law_cos_EX023 (t : ℝ) :
    xyZ1 (xyLaw_EX023 t : Measure (Torus 1)) = besselRatio t := by
  rw [xyZ1, law_integral_EX023]
  simp_rw [xyMode_re_eq_angCos_xyc]
  rw [integral_comp_angEquiv
    (fun θ => Real.exp (t * angCos θ) / besselI 0 t * angCos θ)]
  simpa [besselDensity, mul_comm] using (besselRatio_eq_mean t).symm

theorem mode_neg_EX023 (x : Torus 1) : xyMode (-x) = (starRingEnd ℂ) (xyMode x) := by
  simpa [xyMode_zero] using xyMode_sub 0 x

theorem law_sin_EX023 (t : ℝ) :
    xyZ2 (xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  rw [xyZ2, law_integral_EX023]
  have hi := integral_neg_eq_self
    (fun x : Torus 1 => Real.exp (t * (xyMode x).re) / besselI 0 t * (xyMode x).im) (haar 1)
  simp only [mode_neg_EX023, Complex.conj_re, Complex.conj_im,
    mul_neg, integral_neg] at hi
  linarith

theorem law_entropy_EX023 (t : ℝ) :
    relativeEntropy (xyLaw_EX023 t : Measure (Torus 1)) (haar 1) ≠ ⊤ ∧
    (relativeEntropy (xyLaw_EX023 t : Measure (Torus 1)) (haar 1)).toReal =
      t * besselRatio t - Real.log (besselI 0 t) := by
  have hf := (continuous_xyTrig t 0 0).measurable
  have hb := abs_xyTrig_zero_le t 0
  have hs : klDiv (xyLaw_EX023 t : Measure (Torus 1))
      ((haar 1).tilted (xyTrig t 0 0)) ≠ ⊤ := by
    change klDiv (xyLaw_EX023 t : Measure (Torus 1)) (xyLaw_EX023 t : Measure (Torus 1)) ≠ ⊤
    simp
  have hfin := (DGPS.Lipschitz.klDiv_tilted_ne_top_iff hf hb).1 hs
  obtain ⟨_, heq⟩ := DGPS.Lipschitz.klDiv_tilted_forward hf hb hfin
  have hint : ∫ x, xyTrig t 0 0 x ∂(xyLaw_EX023 t : Measure (Torus 1)) =
      t * besselRatio t := by
    simp only [xyTrig, zero_mul, add_zero]
    rw [integral_const_mul]
    exact congrArg (t * ·) (law_cos_EX023 t)
  have hself : klDiv (xyLaw_EX023 t : Measure (Torus 1)) ((haar 1).tilted (xyTrig t 0 0)) = 0 := by
    change klDiv (xyLaw_EX023 t : Measure (Torus 1)) (xyLaw_EX023 t : Measure (Torus 1)) = 0
    simp
  rw [hself, ENNReal.toReal_zero, hint] at heq
  constructor
  · rwa [DGPS.Analysis.relativeEntropy_eq_klDiv]
  · rw [DGPS.Analysis.relativeEntropy_eq_klDiv]
    rw [show (∫ x, Real.exp (xyTrig t 0 0 x) ∂haar 1) = besselI 0 t from partition_EX023 t] at heq
    linarith

/-- Actual free energy of the normalized law, without a stationarity assumption. -/
theorem law_freeEnergy_EX023 (κ h t : ℝ) :
    freeEnergy (attractiveXY κ h) (xyLaw_EX023 t) =
      ((t * besselRatio t - Real.log (besselI 0 t) + κ / 2 - h * besselRatio t -
        κ / 2 * besselRatio t ^ 2 : ℝ) : EReal) := by
  rw [freeEnergy_attractiveXY, law_cos_EX023, law_sin_EX023]
  obtain ⟨hf, he⟩ := law_entropy_EX023 t
  rw [← EReal.coe_ennreal_toReal hf, he, ← EReal.coe_add]
  congr 1
  ring

/-- Reversing the tilt changes only the external field contribution. -/
theorem opposite_energy_EX023 (κ h s : ℝ) :
    freeEnergy (attractiveXY κ h) (xyLaw_EX023 (-s)) =
      freeEnergy (attractiveXY κ h) (xyLaw_EX023 s) + ((2 * h * besselRatio s : ℝ) : EReal) := by
  rw [law_freeEnergy_EX023, law_freeEnergy_EX023, besselRatio_neg, besselI_neg]
  norm_num only [pow_zero, one_mul]
  rw [← EReal.coe_add]
  congr 1
  ring

/-- Every negative tilted law has the claimed gap above the unrestricted global minimum. -/
theorem negative_gap_EX023 {κ h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    ((2 * h * besselRatio s : ℝ) : EReal) ≤
      freeEnergy (attractiveXY κ h) (xyLaw_EX023 (-s)) -
        freeEnergyMinimum (attractiveXY κ h) ∧
    0 < 2 * h * besselRatio s := by
  have hmin : freeEnergyMinimum (attractiveXY κ h) ≤
      freeEnergy (attractiveXY κ h) (xyLaw_EX023 s) := iInf_le _ _
  have hco := coe_freeEnergyMinimumReal (attractiveXY κ h)
  rw [← hco, law_freeEnergy_EX023] at hmin
  rw [EReal.coe_le_coe_iff] at hmin
  constructor
  · rw [opposite_energy_EX023, law_freeEnergy_EX023, ← hco,
      ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · exact mul_pos (mul_pos (by norm_num) hh) (besselRatio_pos s hs)

/-- The complete smooth XY mean-field potential for any Borel probability. -/
theorem potential_EX023 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    DGPS.Lipschitz.equilibriumPotential (attractiveXY κ h) (ν : Measure (Torus 1)) =
      xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
        (-(κ * xyZ2 (ν : Measure (Torus 1)))) κ := by
  funext x
  unfold DGPS.Lipschitz.equilibriumPotential DGPS.Lipschitz.interactionConvolution
  have hW : ∀ y, (attractiveXY κ h).W x y =
      κ + (-(κ * (xyMode x).re)) * (xyMode y).re + (-(κ * (xyMode x).im)) * (xyMode y).im := by
    intro y
    rw [attractiveXY_W, xyMode_re_sub]
    ring
  simp_rw [hW]
  have i1 := (integrable_xyMode_re (ν : Measure (Torus 1))).const_mul (-(κ * (xyMode x).re))
  have i2 := (integrable_xyMode_im (ν : Measure (Torus 1))).const_mul (-(κ * (xyMode x).im))
  have i0 : Integrable (fun y : Torus 1 =>
      κ + (-(κ * (xyMode x).re)) * (xyMode y).re) (ν : Measure (Torus 1)) :=
    (integrable_const κ).add i1
  rw [integral_add i0 i2, integral_add (integrable_const κ) i1,
    integral_const_mul, integral_const_mul]
  simp only [attractiveXY_V, xyTrig, xyZ1, xyZ2, integral_const]
  simp
  ring

theorem tilted_add_const_EX023 (f : Torus 1 → ℝ) (c : ℝ) :
    (haar 1).tilted (fun x => f x + c) = (haar 1).tilted f := by
  unfold Measure.tilted
  have h : ∫ x, Real.exp (f x + c) ∂haar 1 =
      (∫ x, Real.exp (f x) ∂haar 1) * Real.exp c := by
    simp_rw [Real.exp_add]
    exact integral_mul_const _ _
  congr 1
  ext x
  rw [h, Real.exp_add, mul_div_mul_right _ _ (Real.exp_pos c).ne']

theorem gibbs_bivariate_EX023 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    DGPS.Lipschitz.gibbsMeasure (attractiveXY κ h) (ν : Measure (Torus 1)) =
      (xyBivariateLaw_EX023 (h + κ * xyZ1 (ν : Measure (Torus 1)))
        (κ * xyZ2 (ν : Measure (Torus 1))) : Measure (Torus 1)) := by
  unfold DGPS.Lipschitz.gibbsMeasure
  rw [potential_EX023]
  have e : (fun x => -xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
      (-(κ * xyZ2 (ν : Measure (Torus 1)))) κ x) =
      fun x => xyTrig (h + κ * xyZ1 (ν : Measure (Torus 1)))
        (κ * xyZ2 (ν : Measure (Torus 1))) 0 x + (-κ) := by
    funext x
    simp only [xyTrig]
    ring
  rw [e, tilted_add_const_EX023]
  rfl

end DGPS.Examples.AttractiveXYTilt

namespace DGPS.Examples.AttractiveXYTilt

open DGPS DGPS.Models DGPS.Examples.AttractiveXY
open DGPS.Examples.AttractiveXYCritical
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity

/-- The transverse moment identity is the integral of the derivative of the Gibbs density. -/
theorem bivariate_torque_EX023 (a b : ℝ) :
    a * xyZ2 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) -
      b * xyZ1 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) = 0 := by
  let E : Torus 1 → ℝ := fun x => Real.exp (xyTrig a b 0 x)
  have hT := isSmoothPeriodic_xyTrig a b 0
  have hE : IsSmoothPeriodic E := Real.contDiff_exp.comp hT
  have hd : ∀ x, coordPartial 0 E x = E x * xyTrig (2 * Real.pi * b) (-(2 * Real.pi) * a) 0 x := by
    intro x
    obtain ⟨t, rfl⟩ := circ_exists_pt x
    have he := circ_coordPartial_pt hE t
    have ht := (circ_coordPartial_pt hT t).exp
    have heq := he.unique ht
    simpa only [coordPartial_xyTrig] using heq
  have iz : ∫ x, coordPartial 0 E x ∂haar 1 = 0 := by
    have hz := (isWeakGradient_const (d := 1) 1).ibp E hE 0
    simpa using hz
  let μ : Measure (Torus 1) := xyBivariateLaw_EX023 a b
  have it : ∫ x, xyTrig (2 * Real.pi * b) (-(2 * Real.pi) * a) 0 x ∂μ = 0 := by
    change (∫ x, xyTrig (2 * Real.pi * b) (-(2 * Real.pi) * a) 0 x
      ∂(haar 1).tilted (xyTrig a b 0)) = 0
    rw [integral_tilted]
    simp only [smul_eq_mul]
    have e : ∀ x, Real.exp (xyTrig a b 0 x) / (∫ y, Real.exp (xyTrig a b 0 y) ∂haar 1) *
        xyTrig (2 * Real.pi * b) (-(2 * Real.pi) * a) 0 x =
        coordPartial 0 E x / xyPartition a b := by
      intro x
      rw [hd]
      dsimp [E, xyPartition]
      ring
    simp_rw [e]
    rw [integral_div, iz, zero_div]
  have i1 := (integrable_xyMode_re μ).const_mul (2 * Real.pi * b)
  have i2 := (integrable_xyMode_im μ).const_mul (-(2 * Real.pi) * a)
  simp only [xyTrig, add_zero] at it
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at it
  change (2 * Real.pi * b) * xyZ1 μ + (-(2 * Real.pi) * a) * xyZ2 μ = 0 at it
  have hm : (2 * Real.pi) * (a * xyZ2 μ - b * xyZ1 μ) = 0 := by
    nlinarith [it]
  exact (mul_eq_zero.mp hm).resolve_left (by positivity)

/-- Any Gibbs fixed point is a scalar root; the field excludes the zero root. -/
theorem fixedPoint_scalar_EX023 {κ h : ℝ} (hh : 0 < h)
    (ν : ProbabilityMeasure (Torus 1))
    (hf : (ν : Measure (Torus 1)) =
      DGPS.Lipschitz.gibbsMeasure (attractiveXY κ h) (ν : Measure (Torus 1))) :
    ∃ t : ℝ, t ≠ 0 ∧ t = κ * besselRatio t + h ∧ ν = xyLaw_EX023 t := by
  rw [gibbs_bivariate_EX023] at hf
  have ht := bivariate_torque_EX023 (h + κ * xyZ1 (ν : Measure (Torus 1)))
    (κ * xyZ2 (ν : Measure (Torus 1)))
  rw [← hf] at ht
  have hz : xyZ2 (ν : Measure (Torus 1)) = 0 := by
    have hm : h * xyZ2 (ν : Measure (Torus 1)) = 0 := by nlinarith [ht]
    exact (mul_eq_zero.mp hm).resolve_left hh.ne'
  rw [hz, mul_zero] at hf
  let t := h + κ * xyZ1 (ν : Measure (Torus 1))
  have hν : ν = xyLaw_EX023 t := Subtype.ext hf
  have hc : xyZ1 (ν : Measure (Torus 1)) = besselRatio t := by
    rw [hν]
    exact law_cos_EX023 t
  have he : t = κ * besselRatio t + h := by dsimp [t]; rw [← hc]; ring
  have hg0 : besselRatio 0 = 0 := by
    have := besselRatio_neg 0
    simp only [neg_zero] at this
    linarith
  refine ⟨t, ?_, he, hν⟩
  intro hzero
  rw [hzero, hg0, mul_zero, zero_add] at he
  exact hh.ne' he.symm

/-- The canonical distributional drift equals the derivative of the smooth potential. -/
theorem drift_EX023 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1)) (x : Torus 1) :
    coordPartial 0 (attractiveXY κ h).V x +
      (∫ y, coordPartial 0 (fun x' => (attractiveXY κ h).W x' y) x
        ∂(ν : Measure (Torus 1))) =
      coordPartial 0 (xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
        (-(κ * xyZ2 (ν : Measure (Torus 1)))) κ) x := by
  have hV : (attractiveXY κ h).V = xyTrig (-h) 0 0 := by
    funext x
    simp [attractiveXY_V, xyTrig]
  have hW : ∀ y, (fun x' => (attractiveXY κ h).W x' y) =
      xyTrig (-κ * (xyMode y).re) (-κ * (xyMode y).im) κ := by
    intro y
    funext x'
    rw [attractiveXY_W, xyMode_re_sub]
    simp only [xyTrig]
    ring
  have hw : ∀ y, coordPartial 0 (fun x' => (attractiveXY κ h).W x' y) x =
      (2 * Real.pi * κ * (xyMode x).im) * (xyMode y).re +
        (-(2 * Real.pi * κ * (xyMode x).re)) * (xyMode y).im := by
    intro y
    rw [hW, coordPartial_xyTrig]
    simp only [xyTrig]
    ring
  simp_rw [hw]
  have i1 := (integrable_xyMode_re (ν : Measure (Torus 1))).const_mul
    (2 * Real.pi * κ * (xyMode x).im)
  have i2 := (integrable_xyMode_im (ν : Measure (Torus 1))).const_mul
    (-(2 * Real.pi * κ * (xyMode x).re))
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, hV,
    coordPartial_xyTrig, coordPartial_xyTrig]
  simp only [xyTrig, xyZ1, xyZ2]
  ring

/-- This implication starts with the full weak equation for an arbitrary Borel probability. -/
theorem stationary_fixedPoint_EX023 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1))
    (hs : IsCircleDistributionalStationary (attractiveXY κ h) ν) :
    (ν : Measure (Torus 1)) =
      DGPS.Lipschitz.gibbsMeasure (attractiveXY κ h) (ν : Measure (Torus 1)) := by
  let U := xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
    (-(κ * xyZ2 (ν : Measure (Torus 1)))) κ
  have hU : IsSmoothPeriodic U := isSmoothPeriodic_xyTrig _ _ _
  have hst : ∀ φ : Torus 1 → ℝ, IsSmoothPeriodic φ →
      ∫ x, (coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x)
        ∂(ν : Measure (Torus 1)) = 0 := by
    intro φ hφ
    have ht := hs φ hφ
    simp_rw [drift_EX023] at ht
    exact ht
  have he := eq_gibbs_of_stationary hU hst
  rw [DGPS.Lipschitz.gibbsMeasure, potential_EX023]
  exact he

end DGPS.Examples.AttractiveXYTilt

namespace DGPS.Examples.AttractiveXYTilt

open DGPS DGPS.Models DGPS.Examples.AttractiveXY
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity

theorem law_density_EX023 (t : ℝ) :
    (xyLaw_EX023 t : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal
        (Real.exp (t * (xyMode x).re) / besselI 0 t)) := by
  change (haar 1).tilted (xyTrig t 0 0) = _
  unfold Measure.tilted
  simp only [xyTrig, zero_mul, add_zero]
  rw [DGPS.Examples.AttractiveXYCritical.integral_exp_re_xyc]

theorem fixedPoint_stationary_EX023 (κ h : ℝ) (ν : ProbabilityMeasure (Torus 1))
    (hf : (ν : Measure (Torus 1)) =
      DGPS.Lipschitz.gibbsMeasure (attractiveXY κ h) (ν : Measure (Torus 1))) :
    IsCircleDistributionalStationary (attractiveXY κ h) ν := by
  let U := xyTrig (-(h + κ * xyZ1 (ν : Measure (Torus 1))))
    (-(κ * xyZ2 (ν : Measure (Torus 1)))) κ
  have hU : IsSmoothPeriodic U := isSmoothPeriodic_xyTrig _ _ _
  have he : (ν : Measure (Torus 1)) = gibbsMeasure U := by
    rw [hf, DGPS.Lipschitz.gibbsMeasure, potential_EX023]
    rfl
  intro φ hφ
  simp_rw [drift_EX023]
  change (∫ x, (coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x)
    ∂(ν : Measure (Torus 1))) = 0
  rw [he]
  exact gibbs_stationary hU hφ

theorem root_stationary_EX023 {κ h t : ℝ} (he : t = κ * besselRatio t + h) :
    IsCircleDistributionalStationary (attractiveXY κ h) (xyLaw_EX023 t) := by
  apply fixedPoint_stationary_EX023
  rw [gibbs_bivariate_EX023, law_cos_EX023, law_sin_EX023, mul_zero,
    show h + κ * besselRatio t = t by linarith [he]]
  rfl

theorem negative_energy_strict_EX023 {κ h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    freeEnergy (attractiveXY κ h) (xyLaw_EX023 s) <
      freeEnergy (attractiveXY κ h) (xyLaw_EX023 (-s)) := by
  rw [opposite_energy_EX023, law_freeEnergy_EX023, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have := mul_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) hh) (besselRatio_pos s hs)
  linarith

/-- Positivity of a minimizing tilt follows from an actual competing probability law. -/
theorem minimizer_positive_law_EX023 {κ h : ℝ} (hh : 0 < h)
    (ν : ProbabilityMeasure (Torus 1))
    (hm : ∀ μ : ProbabilityMeasure (Torus 1),
      freeEnergy (attractiveXY κ h) ν ≤ freeEnergy (attractiveXY κ h) μ) :
    ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h ∧ ν = xyLaw_EX023 t := by
  obtain ⟨t, ht, he, hν⟩ := fixedPoint_scalar_EX023 hh ν
    (DGPS.Lipschitz.minimizer_eq_gibbs _ ν hm)
  refine ⟨t, ?_, he, hν⟩
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hcomp := hm (xyLaw_EX023 (-t))
    rw [hν] at hcomp
    have hstrict := negative_energy_strict_EX023 (κ := κ) hh (neg_pos.mpr hneg)
    rw [neg_neg] at hstrict
    exact False.elim ((not_le_of_gt hstrict) hcomp)
  · exact hpos

end DGPS.Examples.AttractiveXYTilt

namespace DGPS.Examples

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.ThreeSpeciesCircle hiding besselI
open DGPS.Circle.BesselMoments

/-- EX023. For every nonnegative interaction and positive external field, all weak stationary
Borel probabilities are precisely the normalized nonzero scalar-root laws. There is exactly
one positive root, including the endpoint case `κ = 0`; its law is the unique unrestricted
free-energy minimizer. Every negative-root law has the asserted strictly positive actual gap.
-/
theorem tilted_stationary_scalar_root_and_global_minimizer {κ h : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) :
    (∀ ν : ProbabilityMeasure (Torus 1),
      IsCircleDistributionalStationary (attractiveXY κ h) ν ↔
        ∃ t : ℝ, t ≠ 0 ∧ t = κ * besselRatio t + h ∧ ν = xyLaw_EX023 t) ∧
    (∀ t : ℝ, (xyLaw_EX023 t : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal
        (Real.exp (t * (xyMode x).re) / besselI 0 t))) ∧
    ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h ∧
      (∀ u : ℝ, 0 < u → u = κ * besselRatio u + h → u = t) ∧
      h ≤ t ∧ t ≤ h + κ ∧ (0 < κ → h < t ∧ t < h + κ) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        freeEnergy (attractiveXY κ h) ν = freeEnergyMinimum (attractiveXY κ h) ↔
          ν = xyLaw_EX023 t) ∧
      (∀ s : ℝ, 0 < s → -s = κ * besselRatio (-s) + h →
        ((2 * h * besselRatio s : ℝ) : EReal) ≤
          freeEnergy (attractiveXY κ h) (xyLaw_EX023 (-s)) -
            freeEnergyMinimum (attractiveXY κ h) ∧ 0 < 2 * h * besselRatio s) := by
  refine ⟨?_, law_density_EX023, ?_⟩
  · intro ν
    constructor
    · intro hs
      exact fixedPoint_scalar_EX023 hh ν (stationary_fixedPoint_EX023 κ h ν hs)
    · rintro ⟨t, _, he, rfl⟩
      exact root_stationary_EX023 he
  · obtain ⟨t, ht, he⟩ := positive_root_exists_EX023 hκ hh
    have hu : ∀ u : ℝ, 0 < u → u = κ * besselRatio u + h → u = t :=
      fun u hpu heu => positive_root_atMostOne_EX023 hκ hh hpu ht heu he
    obtain ⟨μ, hμ⟩ := freeEnergy_minimum_exists (attractiveXY κ h)
    have hm : ∀ ν : ProbabilityMeasure (Torus 1),
        freeEnergy (attractiveXY κ h) μ ≤ freeEnergy (attractiveXY κ h) ν := by
      intro ν
      rw [hμ]
      exact iInf_le _ ν
    obtain ⟨u, hpu, heu, heμ⟩ := minimizer_positive_law_EX023 hh μ hm
    rw [hu u hpu heu] at heμ
    have hval : freeEnergy (attractiveXY κ h) (xyLaw_EX023 t) =
        freeEnergyMinimum (attractiveXY κ h) := by rw [← heμ]; exact hμ
    obtain ⟨hb1, hb2, hbs⟩ := positive_root_bounds_EX023 hκ hh ht he
    refine ⟨t, ht, he, hu, hb1, hb2, hbs, ?_, fun s hs _ => negative_gap_EX023 hh hs⟩
    intro ν
    constructor
    · intro hν
      have hmn : ∀ μ : ProbabilityMeasure (Torus 1),
          freeEnergy (attractiveXY κ h) ν ≤ freeEnergy (attractiveXY κ h) μ := by
        intro μ
        rw [hν]
        exact iInf_le _ μ
      obtain ⟨u, hpu, heu, heν⟩ := minimizer_positive_law_EX023 hh ν hmn
      rwa [hu u hpu heu] at heν
    · intro heν
      rw [heν, hval]

end DGPS.Examples
