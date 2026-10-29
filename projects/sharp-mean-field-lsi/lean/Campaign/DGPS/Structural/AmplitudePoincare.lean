import DGPS.Analysis.WeightedRateComparison
import DGPS.Analysis.LSITensorization

/-!
# Amplitude upper bound for the equilibrium Poincare rate (STR013)

Frozen source: `campaign/frozen_gibbs_rate_comparison.md` Section 4.  If `mu = q m` on the unit
`d`-torus (`d >= 1`) with `qmin <= q <= qmax` and `qmax <= e^M qmin`, then
`lambda_P(mu) <= a0 e^M` with `a0 = 4 pi^2`.

Route: the first-coordinate sine `sin (2 pi x_0)` is a Haar test function with mean zero, variance
`1/2` and energy `2 pi^2`, so `lambda_P(m) <= a0`; the energy of `mu` is at least `qmin` times
and its variance at most `1/qmin`-times-comparable to the Haar ones, which is exactly the
bounded-density comparison core of EX007 (`ex007_poincareRateOn_core`).  No Poincare optimizer is
assumed.  The density-ratio bound is stated with explicit essential bounds `qmin`, `qmax`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace DGPS.Structural

variable {d : ℕ}

/-- One-dimensional sine mode on the circle. -/
noncomputable def sineMode (z : Torus 1) : ℝ := Real.sin (2 * Real.pi * SharpLSI.secT z 0)

theorem sineMode_lift (x : Fin 1 → ℝ) : sineMode (torusLift x) = Real.sin (2 * Real.pi * x 0) := by
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq x
  have h : SharpLSI.secT (torusLift x) 0 = x 0 + (SharpLSI.intVec m) 0 := by
    have := congrFun hm 0
    simpa [torusLift] using this
  unfold sineMode
  rw [h]
  have : Real.sin (2 * Real.pi * (x 0 + (SharpLSI.intVec m) 0)) = Real.sin (2 * Real.pi * x 0) := by
    simp only [SharpLSI.intVec]
    rw [mul_add, show 2 * Real.pi * ((m 0 : ℤ) : ℝ) = (m 0 : ℤ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi _ _
  exact this


theorem isSmoothPeriodic_sineMode : IsSmoothPeriodic sineMode := by
  unfold IsSmoothPeriodic
  have : sineMode ∘ torusLift = fun x : Fin 1 → ℝ => Real.sin (2 * Real.pi * x 0) :=
    funext sineMode_lift
  rw [this]
  exact (Real.contDiff_sin.comp ((contDiff_const.mul (contDiff_apply ℝ ℝ (0 : Fin 1)))))

theorem coordPartial_sineMode (z : Torus 1) :
    coordPartial 0 sineMode z = 2 * Real.pi * Real.cos (2 * Real.pi * SharpLSI.secT z 0) := by
  unfold coordPartial
  have hu : sineMode ∘ torusLift = fun x : Fin 1 → ℝ => Real.sin (2 * Real.pi * x 0) :=
    funext sineMode_lift
  rw [hu]
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t))
      (Real.cos (2 * Real.pi * SharpLSI.secT z 0) * (2 * Real.pi)) (SharpLSI.secT z 0) := by
    have := (hasDerivAt_id (SharpLSI.secT z 0)).const_mul (2 * Real.pi)
    simpa using this.sin
  have hd := h1.comp_hasFDerivAt (SharpLSI.secT z)
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (SharpLSI.secT z))
  rw [show (fun x : Fin 1 → ℝ => Real.sin (2 * Real.pi * x 0)) =
    (fun t : ℝ => Real.sin (2 * Real.pi * t)) ∘ (fun f : Fin 1 → ℝ => f 0) from rfl, hd.fderiv]
  simp
  ring


theorem integral_haar_coordProj (p : Fin d) {F : Torus 1 → ℝ} (hF : Continuous F) :
    ∫ x, F (DGPS.Analysis.coordProj p x) ∂haar d = ∫ z, F z ∂haar 1 := by
  have hP := DGPS.Analysis.measurePreserving_coordProj p
  conv_rhs => rw [← hP.map_eq]
  rw [integral_map hP.measurable.aemeasurable hF.aestronglyMeasurable]

theorem integral_haar1_sine_comp (G : ℝ → ℝ) :
    ∫ z, G (sineMode z) ∂haar 1 = ∫ t in Ioc (0 : ℝ) 1, G (Real.sin (2 * Real.pi * t)) :=
  DGPS.Analysis.integral_haar1_secT (fun t => G (Real.sin (2 * Real.pi * t)))

theorem continuous_sineMode : Continuous sineMode := isSmoothPeriodic_sineMode.continuous_torus


theorem integral_sin_two_pi_Ioc : ∫ t in Ioc (0 : ℝ) 1, Real.sin (2 * Real.pi * t) = 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sin u) hc
  rw [this]; simp [integral_sin]

theorem integral_sin_sq_Ioc : ∫ t in Ioc (0 : ℝ) 1, Real.sin (2 * Real.pi * t) ^ 2 = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact DGPS.Analysis.CircleMoments.integral_sin_sq_two_pi

theorem integral_cos_sq_Ioc : ∫ t in Ioc (0 : ℝ) 1, Real.cos (2 * Real.pi * t) ^ 2 = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact DGPS.Analysis.CircleMoments.integral_cos_sq_two_pi

theorem isMeasureWeakGradient_haar {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) :
    IsMeasureWeakGradient (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) u g where
  memLp := h.memLp
  memLp_grad := h.memLp_grad
  integrable := h.memLp.integrable one_le_two
  integrable_grad := h.memLp_grad.integrable one_le_two
  ibp := h.ibp

/-- The first-coordinate sine test function `sin (2π x₀)` on `𝕋^d`. -/
noncomputable def sineTest (p : Fin d) (x : Torus d) : ℝ := sineMode (DGPS.Analysis.coordProj p x)

theorem isSmoothPeriodic_sineTest (p : Fin d) : IsSmoothPeriodic (sineTest p) :=
  DGPS.Analysis.isSmoothPeriodic_comp_coordProj p isSmoothPeriodic_sineMode

theorem norm_smoothGrad_sineTest_sq (p : Fin d) (x : Torus d) :
    ‖smoothGrad (sineTest p) x‖ ^ 2 =
      (coordPartial 0 sineMode (DGPS.Analysis.coordProj p x)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [smoothGrad_apply, Real.norm_eq_abs, sq_abs]
  have : ∀ j, coordPartial j (sineTest p) x =
      if j = p then coordPartial 0 sineMode (DGPS.Analysis.coordProj p x) else 0 := by
    intro j
    unfold sineTest
    show coordPartial j (sineMode ∘ DGPS.Analysis.coordProj p) x = _
    rw [DGPS.Analysis.coordPartial_comp_coordProj p isSmoothPeriodic_sineMode j x]
  simp only [this]
  simp [Finset.sum_ite_eq']

theorem poincareRate_haar_le (hd : 0 < d) :
    poincareRate (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) ≤
      ENNReal.ofReal (4 * Real.pi ^ 2) := by
  set p : Fin d := ⟨0, hd⟩
  let f : WeakH1Test (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) :=
    ⟨sineTest p, smoothGrad (sineTest p),
      isMeasureWeakGradient_haar (isSmoothPeriodic_sineTest p).isWeakGradient⟩
  have hcont : Continuous (sineTest p) := (isSmoothPeriodic_sineTest p).continuous_torus
  have hmean : ∫ x, sineTest p x ∂haar d = 0 := by
    unfold sineTest
    rw [integral_haar_coordProj p continuous_sineMode]
    simpa using (integral_haar1_sine_comp id).trans integral_sin_two_pi_Ioc
  have hsq : ∫ x, sineTest p x ^ 2 ∂haar d = 1 / 2 := by
    unfold sineTest
    rw [integral_haar_coordProj p (F := fun z => sineMode z ^ 2) (continuous_sineMode.pow 2)]
    exact (integral_haar1_sine_comp (fun y => y ^ 2)).trans integral_sin_sq_Ioc
  have hvar : weightedVariance (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d))
      (sineTest p) = 1 / 2 := by
    unfold weightedVariance
    simp only [ProbabilityMeasure.coe_mk]
    rw [hmean]
    simpa using hsq
  have hE : dirichletEnergy (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) f =
      ENNReal.ofReal (2 * Real.pi ^ 2) := by
    unfold dirichletEnergy
    have h1 : ∀ x, ‖f.grad x‖ₑ ^ 2 = ENNReal.ofReal (‖smoothGrad (sineTest p) x‖ ^ 2) := by
      intro x
      show ‖smoothGrad (sineTest p) x‖ₑ ^ 2 = _
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ProbabilityMeasure.coe_mk, h1]
    have hgi : Integrable (fun x => ‖smoothGrad (sineTest p) x‖ ^ 2) (haar d) :=
      (isSmoothPeriodic_sineTest p).isWeakGradient.memLp_grad.norm.integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    congr 1
    simp_rw [norm_smoothGrad_sineTest_sq]
    rw [integral_haar_coordProj p (F := fun z => coordPartial 0 sineMode z ^ 2)
      (isSmoothPeriodic_sineMode.continuous_coordPartial 0 |>.pow 2)]
    simp_rw [coordPartial_sineMode]
    refine (DGPS.Analysis.integral_haar1_secT
      (fun t : ℝ => (2 * Real.pi * Real.cos (2 * Real.pi * t)) ^ 2)).trans ?_
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_cos_sq_Ioc]
    ring
  have hf : f.fn = sineTest p := rfl
  have hpos : 0 < weightedVariance (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) f.fn := by
    rw [hf, hvar]; norm_num
  refine (poincareRate_le_quotient _ f hpos).trans (le_of_eq ?_)
  unfold poincareQuotient
  rw [hE, hf, hvar, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring


/-- The Haar probability as a bounded positive reference (density `1`). -/
noncomputable def unitReference (d : ℕ) : BoundedPositiveReference d where
  density := fun _ => 1
  measurable_density := measurable_const
  lower := 1
  upper := 1
  lower_pos := one_pos
  lower_le := Filter.Eventually.of_forall fun _ => le_rfl
  le_upper := Filter.Eventually.of_forall fun _ => le_rfl
  mass_one := by simp

theorem unitReference_measure (d : ℕ) : (unitReference d).measure = haar d := by
  simp [BoundedPositiveReference.measure, unitReference]

/-- **STR013.** If `μ = q m` on the unit `d`-torus (`d ≥ 1`) with `qmin ≤ q ≤ qmax` almost
everywhere, `0 < qmin` and `qmax ≤ e^M qmin`, then `λ_P(μ) ≤ a₀ e^M`, where `a₀ = 4π²` is the
Haar Poincaré constant.  The proof tests the first-coordinate sine `sin (2π x₀)`, which has
Haar mean zero, Haar variance `1/2` and Haar energy `2π²`; no Poincaré optimizer is used. -/
theorem poincareRate_le_haarRate_densityRatio (hd : 0 < d) (P : BoundedPositiveReference d)
    (M qmin qmax : ℝ) (hqmin : 0 < qmin) (hlow : ∀ᵐ x ∂haar d, qmin ≤ P.density x)
    (hup : ∀ᵐ x ∂haar d, P.density x ≤ qmax) (hratio : qmax ≤ Real.exp M * qmin) :
    poincareRate (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d)) ≤
      ENNReal.ofReal (a0 * Real.exp M) := by
  have hqmax : 0 < qmax := by
    obtain ⟨x, h1, h2⟩ := (hlow.and hup).exists
    linarith
  have hU := unitReference_measure d
  have h1 : ENNReal.ofReal (1 / qmax) • P.measure ≤ haar d := by
    rw [← hU]
    refine DGPS.Examples.ex007_le_measure P (unitReference d) (by positivity) ?_
    filter_upwards [hup] with x hx
    show 1 / qmax * P.density x ≤ 1
    rw [div_mul_eq_mul_div, one_mul, div_le_one hqmax]; exact hx
  have h2 : haar d ≤ ENNReal.ofReal (1 / qmin) • P.measure := by
    rw [← hU]
    refine DGPS.Examples.ex007_measure_le P (unitReference d) ?_
    filter_upwards [hlow] with x hx
    show 1 ≤ 1 / qmin * P.density x
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hqmin]; linarith
  have htrans : ∀ f : WeakH1Test (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)),
      IsMeasureWeakGradient (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d))
        f.fn f.grad := fun f =>
    ⟨P.memLp_measure_iff.2 f.isWeak.memLp, P.memLp_measure_iff.2 f.isWeak.memLp_grad,
      f.isWeak.integrable, f.isWeak.integrable_grad, f.isWeak.ibp⟩
  have hcore := DGPS.Examples.ex007_poincareRateOn_core (μP := ⟨P.measure, P.isProbabilityMeasure⟩)
    (μQ := ⟨haar d, inferInstance⟩) (fun _ => True) (a := 1 / qmax) (A := 1 / qmin)
    (by positivity) (by positivity) h1 h2 htrans
  rw [← DGPS.Examples.ex007_poincareRate_eq_on (⟨P.measure, P.isProbabilityMeasure⟩ :
    ProbabilityMeasure (Torus d)), ← DGPS.Examples.ex007_poincareRate_eq_on
    (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d))] at hcore
  have hH := poincareRate_haar_le hd
  have hc : 0 < qmin / qmax := by positivity
  have e1 : (1 / qmax) / (1 / qmin) = qmin / qmax := by field_simp
  rw [e1] at hcore
  have hR := hcore.trans hH
  set R := poincareRate (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d))
  calc R = ENNReal.ofReal (qmax / qmin) * (ENNReal.ofReal (qmin / qmax) * R) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show qmax / qmin * (qmin / qmax) = 1 by field_simp]; simp
    _ ≤ ENNReal.ofReal (qmax / qmin) * ENNReal.ofReal (4 * Real.pi ^ 2) :=
        mul_le_mul' le_rfl hR
    _ = ENNReal.ofReal (qmax / qmin * (4 * Real.pi ^ 2)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (a0 * Real.exp M) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : qmax / qmin ≤ Real.exp M := by
          rw [div_le_iff₀ hqmin]; exact hratio
        have h4 : (4 * Real.pi ^ 2) = a0 := rfl
        rw [h4]
        nlinarith [a0_pos]

end DGPS.Structural
