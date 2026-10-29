import DGPS.Examples.AttractiveXY
import DGPS.Circle.BesselMonotonicity

/-!
# Strict entropy Fourier inequality at criticality (EX019)

For every Borel probability `ν` other than Haar, `H(ν | m) > |∫ e^{2πi x} dν|²`, with infinite
entropy allowed on the left.  At the critical attractive XY model `κ = 2`, `h = 0`
(EX018), `F(ν) = 1 + H(ν | m) - |ν̂(1)|²`, so Haar is the unique global minimizer and `F_* = 1`.

Proof.  If `z = ∫ φ dν ≠ 0` and `b = |z|`, tilt Haar by the cosine aligned with `z`,
`f = 2 (z₁ cos + z₂ sin)`.  Then `∫ e^f dm = I₀(2b)` (rotation invariance of Haar and the
angular transfer of EX003's Bessel function), `∫ f dν = 2b²`, and non-negativity of the
relative entropy `H(ν | m^f)` gives `H(ν | m) ≥ 2b² - log I₀(2b) > b²` since
`I₀(2b) < e^{b²}` (EX003).  If `z = 0` the bound is `H > 0`, i.e. `DGPS.relativeEntropy_zero_iff`.

Design choices (R5 note).
* Statement: for `ProbabilityMeasure (Torus 1)` and `ν ≠ haarProbability 1`,
  `ENNReal.ofReal (‖∫ xyMode dν‖ ^ 2) < relativeEntropy ν (haar 1)`, where `xyMode x = e^{2πi x}`
  (EX018) so `‖∫ xyMode dν‖² = z₁² + z₂²`.  The `ℝ≥0∞`-valued left side keeps `H = ∞` allowed.
  The same theorem packages the critical free-energy identity, `F(haar) = 1`, strict
  minimality of Haar, uniqueness of the minimizer, `freeEnergyMinimum = 1` (in `EReal`) and
  `freeEnergyMinimumReal = 1`.
* Helper lemmas carry the suffix `_xyc` to avoid project-wide name clashes.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

namespace DGPS.Examples.AttractiveXYCritical

open DGPS.Examples.AttractiveXY DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

theorem xyMode_re_eq_angCos_xyc (x : DGPS.Torus 1) :
    (xyMode x).re = angCos (angEquiv x) := by
  rw [xyMode_apply, angEquiv_apply]
  generalize x 0 = s
  induction s using QuotientAddGroup.induction_on with
  | H t =>
    rw [angRescale_mk]
    exact (fourier_one_re_coe t).trans (by simp [angCos, angMode_coe])

theorem integral_exp_re_xyc (c : ℝ) :
    ∫ x, Real.exp (c * (xyMode x).re) ∂(DGPS.haar 1) = besselI 0 c := by
  rw [besselI_zero]
  simp_rw [xyMode_re_eq_angCos_xyc]
  simpa using integral_comp_angEquiv (fun θ => Real.exp (c * angCos θ))

theorem isAddHaar_haar_xyc : (DGPS.haar 1).IsAddHaarMeasure := by
  rw [DGPS.haar_eq_pi_haarAddCircle]; infer_instance

theorem integral_exp_rot_xyc (z1 z2 : ℝ) (hb : 0 < z1 ^ 2 + z2 ^ 2) :
    ∫ x, Real.exp (2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) ∂(DGPS.haar 1) =
      besselI 0 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) := by
  have _ := isAddHaar_haar_xyc
  set w : ℂ := ⟨z1, z2⟩ with hw
  have hw0 : w ≠ 0 := by
    intro h
    have h1 : z1 = 0 := congrArg Complex.re h
    have h2 : z2 = 0 := congrArg Complex.im h
    rw [h1, h2] at hb; simp at hb
  have hn : ‖w‖ = Real.sqrt (z1 ^ 2 + z2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hw]; simp [sq]
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set x0 : DGPS.Torus 1 := DGPS.torusLift (fun _ => Complex.arg w / (2 * Real.pi)) with hx0
  have hre : (xyMode x0).re = z1 / ‖w‖ := by
    rw [hx0, xyMode_re_lift]
    have : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by
      field_simp
    rw [this, Complex.cos_arg hw0]
  have him : (xyMode x0).im = z2 / ‖w‖ := by
    rw [hx0, xyMode_im_lift]
    have : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by
      field_simp
    rw [this, Complex.sin_arg]
  have key : ∀ x : DGPS.Torus 1,
      Real.exp (2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) =
        Real.exp ((2 * ‖w‖) * (xyMode (x - x0)).re) := by
    intro x
    rw [xyMode_re_sub, hre, him]
    congr 1
    field_simp
  simp_rw [key]
  rw [integral_sub_right_eq_self (fun y => Real.exp ((2 * ‖w‖) * (xyMode y).re)) x0,
    integral_exp_re_xyc, hn]


theorem continuous_tilt_xyc (z1 z2 : ℝ) :
    Continuous (fun x : DGPS.Torus 1 => 2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) :=
  continuous_const.mul ((continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)).add
    (continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)))

theorem integrable_exp_tilt_xyc (z1 z2 : ℝ) :
    Integrable (fun x : DGPS.Torus 1 => Real.exp (2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)))
      (DGPS.haar 1) :=
  (Real.continuous_exp.comp (continuous_tilt_xyc z1 z2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem toReal_relativeEntropy_xyc (ν : Measure (DGPS.Torus 1)) [IsProbabilityMeasure ν]
    (h : DGPS.relativeEntropy ν (DGPS.haar 1) ≠ ⊤) :
    ν ≪ DGPS.haar 1 ∧ Integrable (llr ν (DGPS.haar 1)) ν ∧
      (DGPS.relativeEntropy ν (DGPS.haar 1)).toReal =
        ∫ x, llr ν (DGPS.haar 1) x ∂ν := by
  rw [DGPS.Analysis.relativeEntropy_eq_klDiv] at h
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp h
  refine ⟨hac, hint, ?_⟩
  rw [DGPS.Analysis.relativeEntropy_eq_klDiv]
  exact InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)

/-- Entropy duality for the aligned cosine tilt. -/
theorem entropy_ge_tilt_xyc (ν : Measure (DGPS.Torus 1)) [IsProbabilityMeasure ν]
    (h : DGPS.relativeEntropy ν (DGPS.haar 1) ≠ ⊤) (z1 z2 : ℝ) (hb : 0 < z1 ^ 2 + z2 ^ 2) :
    2 * (z1 * xyZ1 ν + z2 * xyZ2 ν) - Real.log (besselI 0 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2))) ≤
      (DGPS.relativeEntropy ν (DGPS.haar 1)).toReal := by
  obtain ⟨hac, hint, hH⟩ := toReal_relativeEntropy_xyc ν h
  have _ := isAddHaar_haar_xyc
  have hfint : Integrable (fun x : DGPS.Torus 1 =>
      2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) ν :=
    ((continuous_tilt_xyc z1 z2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hexp := integrable_exp_tilt_xyc z1 z2
  have hpos : 0 < ∫ x, Real.exp (2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) ∂(DGPS.haar 1) :=
    by rw [integral_exp_rot_xyc z1 z2 hb]; exact besselI_zero_pos _
  have : IsProbabilityMeasure ((DGPS.haar 1).tilted
      (fun x : DGPS.Torus 1 => 2 * (z1 * (xyMode x).re + z2 * (xyMode x).im))) :=
    isProbabilityMeasure_tilted hexp
  have hac2 : ν ≪ (DGPS.haar 1).tilted
      (fun x : DGPS.Torus 1 => 2 * (z1 * (xyMode x).re + z2 * (xyMode x).im)) :=
    hac.trans (absolutelyContinuous_tilted hexp)
  have hnn : 0 ≤ ∫ x, llr ν ((DGPS.haar 1).tilted
      (fun x : DGPS.Torus 1 => 2 * (z1 * (xyMode x).re + z2 * (xyMode x).im))) x ∂ν := by
    rw [← InformationTheory.toReal_klDiv_of_measure_eq hac2 (by simp)]
    exact ENNReal.toReal_nonneg
  rw [integral_llr_tilted_right hac hfint hexp hint, ← hH,
    integral_exp_rot_xyc z1 z2 hb] at hnn
  have hI : ∫ x, 2 * (z1 * (xyMode x).re + z2 * (xyMode x).im) ∂ν =
      2 * (z1 * xyZ1 ν + z2 * xyZ2 ν) := by
    rw [integral_const_mul, integral_add ((integrable_xyMode_re ν).const_mul z1)
      ((integrable_xyMode_im ν).const_mul z2), integral_const_mul, integral_const_mul]
    rfl
  rw [hI] at hnn
  linarith


theorem integrable_xyMode_xyc (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Integrable xyMode ν :=
  continuous_xyMode.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem re_integral_xyMode_xyc (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    (∫ x, xyMode x ∂ν).re = xyZ1 ν := by
  rw [xyZ1]; exact (integral_re (integrable_xyMode_xyc ν)).symm

theorem im_integral_xyMode_xyc (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    (∫ x, xyMode x ∂ν).im = xyZ2 ν := by
  rw [xyZ2]; exact (integral_im (integrable_xyMode_xyc ν)).symm

theorem norm_sq_integral_xyMode_xyc (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    ‖∫ x, xyMode x ∂ν‖ ^ 2 = xyZ1 ν ^ 2 + xyZ2 ν ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_integral_xyMode_xyc, im_integral_xyMode_xyc]
  ring

theorem integral_xyMode_haar_xyc : ∫ x, xyMode x ∂(DGPS.haar 1) = 0 := by
  have h := SharpLSI.integral_mFourier (ι := Fin 1) (fun _ => (1 : ℤ))
  have hne : (fun _ : Fin 1 => (1 : ℤ)) ≠ 0 := fun h0 => absurd (congrFun h0 0) (by simp)
  rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 hne)] at h
  exact h

/-- Core strict inequality, in the form `z₁² + z₂² < H`. -/
theorem strict_xyc (ν : ProbabilityMeasure (DGPS.Torus 1)) (hν : ν ≠ DGPS.haarProbability 1) :
    ENNReal.ofReal (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 + xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2) <
      DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) := by
  set z1 := xyZ1 (ν : Measure (DGPS.Torus 1)) with hz1
  set z2 := xyZ2 (ν : Measure (DGPS.Torus 1)) with hz2
  by_cases htop : DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) = ⊤
  · rw [htop]; exact ENNReal.ofReal_lt_top
  rcases (add_nonneg (sq_nonneg z1) (sq_nonneg z2)).eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero]
    refine pos_iff_ne_zero.mpr fun h => hν ?_
    have := (DGPS.relativeEntropy_zero_iff (ν := (ν : Measure (DGPS.Torus 1)))
      (P := DGPS.haar 1)).mp h
    exact Subtype.ext this
  · have hge := entropy_ge_tilt_xyc (ν : Measure (DGPS.Torus 1)) htop z1 z2 hpos
    have hlt := (strict_bessel_ratio_inequalities.2.1 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2))
      (by positivity))
    have hsq : (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2)) ^ 2 / 4 = z1 ^ 2 + z2 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpos.le]; ring
    rw [hsq] at hlt
    have hlog : Real.log (besselI 0 (2 * Real.sqrt (z1 ^ 2 + z2 ^ 2))) < z1 ^ 2 + z2 ^ 2 := by
      calc _ < Real.log (Real.exp (z1 ^ 2 + z2 ^ 2)) :=
            Real.log_lt_log (besselI_zero_pos _) hlt
        _ = _ := Real.log_exp _
    rw [← ENNReal.ofReal_toReal htop]
    refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
    · linarith [Real.log_exp (z1 ^ 2 + z2 ^ 2), sq_nonneg z1, sq_nonneg z2]
    · nlinarith


theorem freeEnergy_critical_xyc (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) ν =
      ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((1 - (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 + xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2) :
          ℝ) : EReal) := by
  rw [freeEnergy_attractiveXY]
  congr 2
  ring

theorem freeEnergy_haar_xyc :
    DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) = ((1 : ℝ) : EReal) := by
  have h1 : xyZ1 (DGPS.haar 1) = 0 := by
    rw [← re_integral_xyMode_xyc, integral_xyMode_haar_xyc]; rfl
  have h2 : xyZ2 (DGPS.haar 1) = 0 := by
    rw [← im_integral_xyMode_xyc, integral_xyMode_haar_xyc]; rfl
  rw [freeEnergy_critical_xyc]
  show ((DGPS.relativeEntropy (DGPS.haar 1) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
    ((1 - (xyZ1 (DGPS.haar 1) ^ 2 + xyZ2 (DGPS.haar 1) ^ 2) : ℝ) : EReal) = _
  rw [DGPS.relativeEntropy_self, h1, h2]
  simp

theorem freeEnergy_gt_xyc (ν : ProbabilityMeasure (DGPS.Torus 1))
    (hν : ν ≠ DGPS.haarProbability 1) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) <
      DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) ν := by
  rw [freeEnergy_haar_xyc, freeEnergy_critical_xyc]
  have hs := strict_xyc ν hν
  by_cases htop : DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) = ⊤
  · rw [htop, EReal.coe_ennreal_top, EReal.top_add_coe]
    exact EReal.coe_lt_top _
  · rw [← EReal.coe_ennreal_toReal htop, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    have := (ENNReal.ofReal_lt_iff_lt_toReal
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) htop).mp hs
    linarith

end DGPS.Examples.AttractiveXYCritical

namespace DGPS.Examples

open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical

/-- EX019: strict entropy Fourier inequality at criticality.  For every Borel probability `ν`
different from Haar, `H(ν | Haar) > |ν(exp(2πi ·))|²` (the entropy may be `+∞`), and at the
critical attractive XY model `κ = 2`, `h = 0` the free energy is
`F(ν) = 1 + H(ν | Haar) - |ν(exp(2πi ·))|²`, Haar is the unique global minimizer and `F_* = 1`. -/
theorem strict_entropy_fourier_inequality_at_criticality :
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1), ν ≠ DGPS.haarProbability 1 →
      ENNReal.ofReal (‖∫ x, xyMode x ∂(ν : Measure (DGPS.Torus 1))‖ ^ 2) <
        DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1)) ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) ν =
        ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
          ((1 - ‖∫ x, xyMode x ∂(ν : Measure (DGPS.Torus 1))‖ ^ 2 : ℝ) : EReal)) ∧
    DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) = ((1 : ℝ) : EReal) ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1), ν ≠ DGPS.haarProbability 1 →
      DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) <
        DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) ν) ∧
    DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY 2 0) = ((1 : ℝ) : EReal) ∧
    DGPS.freeEnergyMinimumReal (DGPS.Models.attractiveXY 2 0) = 1 ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) ν =
        DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY 2 0) → ν = DGPS.haarProbability 1) := by
  have hmin : DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY 2 0) = ((1 : ℝ) : EReal) := by
    refine le_antisymm ?_ (le_iInf fun ν => ?_)
    · exact freeEnergy_haar_xyc ▸ iInf_le _ (DGPS.haarProbability 1)
    · by_cases hν : ν = DGPS.haarProbability 1
      · rw [hν, freeEnergy_haar_xyc]
      · rw [← freeEnergy_haar_xyc]; exact (freeEnergy_gt_xyc ν hν).le
  refine ⟨fun ν hν => ?_, fun ν => ?_, freeEnergy_haar_xyc, freeEnergy_gt_xyc, hmin, ?_, ?_⟩
  · rw [norm_sq_integral_xyMode_xyc]; exact strict_xyc ν hν
  · rw [freeEnergy_critical_xyc, norm_sq_integral_xyMode_xyc]
  · have := DGPS.coe_freeEnergyMinimumReal (DGPS.Models.attractiveXY 2 0)
    rw [hmin] at this
    exact_mod_cast this
  · intro ν hν
    by_contra hne
    have := freeEnergy_gt_xyc ν hne
    rw [hν, hmin, freeEnergy_haar_xyc] at this
    exact lt_irrefl _ this

end DGPS.Examples
