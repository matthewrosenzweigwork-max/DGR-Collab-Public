import DGPS.FiniteN.CriticalXYLower
import DGPS.FiniteN.SymmetricHarmonicTrial

/-!
# Rotational symmetric magnetization variance (FIN031)

For an angular `N`-particle law that is a mixture `∫ q_z^{⊗N} dη(z)` of product von Mises laws
over a quarter-turn invariant (in particular radial) probability measure `η` on the auxiliary
plane, the symmetric magnetization `F = ∑ᵢ cos 2π xᵢ` (`= ∑ᵢ cos θᵢ` on the angular torus) is a
smooth `H¹` test with
* `P(F) = 0`,
* `Var_P(F) = (N/2) [1 + (N-1) ∫ g(|z|)² dη]`, `g = I₁/I₀`,
* Dirichlet energy `E(F) = a₀ N / 2`, `a₀ = 4π²`.

The proof uses only quarter-turn invariance of `η`: the one-site moments satisfy
`⟨cos⟩(qz) = -⟨sin⟩(z)`, `⟨cos²⟩(qz) = ⟨sin²⟩(z)`, and the mean vector of `q_z` is
`g(|z|) z/|z|`, so `⟨cos⟩² + ⟨sin⟩² = g²`.  The critical XY model is the instance
`η = criticalAuxiliaryLaw N`.
-/

open MeasureTheory Real
open DGPS.Circle.AngularNormalization DGPS.FiniteN.Tools.UniformVonMises DGPS.Circle.BesselMoments
  DGPS.FiniteN.Tools.ConditionalEntropyPinsker DGPS.FiniteN.UnitTorusNormalization

namespace DGPS.FiniteN.RotationalTools

/-- cosine on the angular circle -/
noncomputable def cosA (θ : AngCircle) : ℝ := ((AddCircle.toCircle θ : Circle) : ℂ).re
/-- sine on the angular circle -/
noncomputable def sinA (θ : AngCircle) : ℝ := ((AddCircle.toCircle θ : Circle) : ℂ).im

theorem cosA_coe (t : ℝ) : cosA (t : AngCircle) = Real.cos t := by
  have := congrFun (phi_coe t) 0
  simpa [phi, cosA] using this

theorem sinA_coe (t : ℝ) : sinA (t : AngCircle) = Real.sin t := by
  have := congrFun (phi_coe t) 1
  simpa [phi, sinA] using this

theorem vmPhase_eq (z : E2) (θ : AngCircle) : vmPhase z θ = z 0 * cosA θ + z 1 * sinA θ := rfl

theorem continuous_cosA : Continuous cosA := by
  unfold cosA
  have := AddCircle.continuous_toCircle (T := 2 * π)
  fun_prop

theorem continuous_sinA : Continuous sinA := by
  unfold sinA
  have := AddCircle.continuous_toCircle (T := 2 * π)
  fun_prop

theorem cosA_sq_add_sinA_sq (θ : AngCircle) : cosA θ ^ 2 + sinA θ ^ 2 = 1 :=
  re_sq_add_im_sq θ

theorem abs_cosA_le (θ : AngCircle) : |cosA θ| ≤ 1 := by
  have := cosA_sq_add_sinA_sq θ
  nlinarith [sq_nonneg (sinA θ), abs_le.2 (show -1 ≤ cosA θ ∧ cosA θ ≤ 1 by
    constructor <;> nlinarith [sq_nonneg (sinA θ), sq_nonneg (cosA θ - 1), sq_nonneg (cosA θ + 1)])]

theorem abs_sinA_le (θ : AngCircle) : |sinA θ| ≤ 1 := by
  have := cosA_sq_add_sinA_sq θ
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (cosA θ), sq_nonneg (sinA θ - 1), sq_nonneg (sinA θ + 1)]

theorem angCos_eq_cosA : angCos = cosA := by
  funext θ
  induction θ using QuotientAddGroup.induction_on with
  | H s => simp [angCos, angMode_coe, cosA_coe]

theorem cosA_add (θ φ : AngCircle) : cosA (θ + φ) = cosA θ * cosA φ - sinA θ * sinA φ := by
  unfold cosA sinA
  rw [AddCircle.toCircle_add, Circle.coe_mul, Complex.mul_re]

theorem sinA_add (θ φ : AngCircle) : sinA (θ + φ) = cosA θ * sinA φ + sinA θ * cosA φ := by
  unfold cosA sinA
  rw [AddCircle.toCircle_add, Circle.coe_mul, Complex.mul_im]

theorem cosA_neg (θ : AngCircle) : cosA (-θ) = cosA θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [← AddCircle.coe_neg, cosA_coe, cosA_coe, Real.cos_neg]

theorem sinA_neg (θ : AngCircle) : sinA (-θ) = - sinA θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [← AddCircle.coe_neg, sinA_coe, sinA_coe, Real.sin_neg]

/-- the quarter turn `π/2` on the angular circle -/
noncomputable def quarter : AngCircle := ((π / 2 : ℝ) : AngCircle)

theorem cosA_quarter : cosA quarter = 0 := by
  rw [quarter, cosA_coe]; exact Real.cos_pi_div_two

theorem sinA_quarter : sinA quarter = 1 := by
  rw [quarter, sinA_coe]; exact Real.sin_pi_div_two

theorem cosA_add_quarter (θ : AngCircle) : cosA (θ + quarter) = - sinA θ := by
  rw [cosA_add, cosA_quarter, sinA_quarter]; ring

theorem sinA_add_quarter (θ : AngCircle) : sinA (θ + quarter) = cosA θ := by
  rw [sinA_add, cosA_quarter, sinA_quarter]; ring

theorem integral_add_quarter (f : AngCircle → ℝ) :
    ∫ θ, f (θ + quarter) ∂angHaar = ∫ θ, f θ ∂angHaar :=
  integral_add_right_eq_self (μ := angHaar) f quarter

theorem integral_neg_ang (f : AngCircle → ℝ) :
    ∫ θ, f (-θ) ∂angHaar = ∫ θ, f θ ∂angHaar :=
  integral_neg_eq_self f angHaar


/-! ### the quarter turn of the plane -/

/-- the unit complex number `i` as an element of the circle -/
noncomputable def qI : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

theorem qI_coe : (qI : ℂ) = Complex.I := rfl

/-- the quarter turn `(z₀, z₁) ↦ (-z₁, z₀)` of the plane as a linear isometry -/
noncomputable def qturnL : E2 ≃ₗᵢ[ℝ] E2 :=
  Complex.orthonormalBasisOneI.repr.symm.trans
    ((rotation qI).trans Complex.orthonormalBasisOneI.repr)

theorem qturnL_zero (z : E2) : qturnL z 0 = - z 1 := by
  simp [qturnL, qI_coe]

theorem qturnL_one (z : E2) : qturnL z 1 = z 0 := by
  simp [qturnL, qI_coe]

theorem norm_qturnL (z : E2) : ‖qturnL z‖ = ‖z‖ := qturnL.norm_map z

/-! ### integrals against the von Mises law -/

theorem integral_vmLaw (z : E2) (h : AngCircle → ℝ) :
    ∫ θ, h θ ∂vmLaw z = (∫ θ, exp (vmPhase z θ) * h θ ∂angHaar) / vmNorm z := by
  have hp := vmNorm_pos z
  unfold vmLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun θ => ENNReal.ofReal (exp (vmPhase z θ) / vmNorm z))
    (ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (continuous_vmPhase z).measurable).div_const _))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem vmPhase_shift (z : E2) (θ : AngCircle) :
    vmPhase z ((vmAngle z : AngCircle) + θ) = ‖z‖ * cosA θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s => rw [← AddCircle.coe_add, vmPhase_rot, vmCplx_norm, cosA_coe]

theorem integrable_angHaar_of_continuous {f : AngCircle → ℝ} (hf : Continuous f) :
    Integrable f angHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_exp_sin (r : ℝ) : ∫ θ, exp (r * cosA θ) * sinA θ ∂angHaar = 0 := by
  have h := integral_neg_ang (fun θ => exp (r * cosA θ) * sinA θ)
  simp only [cosA_neg, sinA_neg, mul_neg, integral_neg] at h
  linarith

theorem integral_exp_cos (r : ℝ) :
    ∫ θ, exp (r * cosA θ) * cosA θ ∂angHaar = besselI 1 r := by
  rw [besselI_one, angCos_eq_cosA]
  simp

theorem vmNorm_eq_besselI0 (z : E2) : vmNorm z = besselI 0 ‖z‖ := vmNorm_eq_bessel z

theorem mean_cos (z : E2) :
    ∫ θ, cosA θ ∂vmLaw z = Real.cos (vmAngle z) * besselRatio ‖z‖ := by
  rw [integral_vmLaw, vmNorm_eq_bessel]
  have e : ∫ θ, exp (vmPhase z θ) * cosA θ ∂angHaar =
      Real.cos (vmAngle z) * besselI 1 ‖z‖ := by
    rw [← integral_add_left_eq_self (μ := angHaar) _ (vmAngle z : AngCircle)]
    have key : ∀ θ : AngCircle, exp (vmPhase z ((vmAngle z : AngCircle) + θ)) *
        cosA ((vmAngle z : AngCircle) + θ) =
        Real.cos (vmAngle z) * (exp (‖z‖ * cosA θ) * cosA θ) -
          Real.sin (vmAngle z) * (exp (‖z‖ * cosA θ) * sinA θ) := by
      intro θ
      simp only [vmPhase_shift, cosA_add, cosA_coe, sinA_coe]
      ring
    simp_rw [key]
    rw [integral_sub, integral_const_mul, integral_const_mul, integral_exp_sin, integral_exp_cos]
    · ring
    · exact (integrable_angHaar_of_continuous (by
        have := continuous_cosA; have := continuous_sinA; fun_prop)).const_mul _
    · exact (integrable_angHaar_of_continuous (by
        have := continuous_cosA; have := continuous_sinA; fun_prop)).const_mul _
  rw [e, besselRatio]
  ring

theorem mean_sin (z : E2) :
    ∫ θ, sinA θ ∂vmLaw z = Real.sin (vmAngle z) * besselRatio ‖z‖ := by
  rw [integral_vmLaw, vmNorm_eq_bessel]
  have e : ∫ θ, exp (vmPhase z θ) * sinA θ ∂angHaar =
      Real.sin (vmAngle z) * besselI 1 ‖z‖ := by
    rw [← integral_add_left_eq_self (μ := angHaar) _ (vmAngle z : AngCircle)]
    have key : ∀ θ : AngCircle, exp (vmPhase z ((vmAngle z : AngCircle) + θ)) *
        sinA ((vmAngle z : AngCircle) + θ) =
        Real.cos (vmAngle z) * (exp (‖z‖ * cosA θ) * sinA θ) +
          Real.sin (vmAngle z) * (exp (‖z‖ * cosA θ) * cosA θ) := by
      intro θ
      simp only [vmPhase_shift, sinA_add, cosA_coe, sinA_coe]
      ring
    simp_rw [key]
    rw [integral_add, integral_const_mul, integral_const_mul, integral_exp_sin, integral_exp_cos]
    · ring
    · exact (integrable_angHaar_of_continuous (by
        have := continuous_cosA; have := continuous_sinA; fun_prop)).const_mul _
    · exact (integrable_angHaar_of_continuous (by
        have := continuous_cosA; have := continuous_sinA; fun_prop)).const_mul _
  rw [e, besselRatio]
  ring

theorem mean_sq_add (z : E2) :
    (∫ θ, cosA θ ∂vmLaw z) ^ 2 + (∫ θ, sinA θ ∂vmLaw z) ^ 2 = besselRatio ‖z‖ ^ 2 := by
  rw [mean_cos, mean_sin]
  have := Real.cos_sq_add_sin_sq (vmAngle z)
  nlinarith


/-! ### quarter-turn covariance of the von Mises law -/

theorem vmNorm_qturnL (z : E2) : vmNorm (qturnL z) = vmNorm z := by
  rw [vmNorm_eq_bessel, vmNorm_eq_bessel, norm_qturnL]

theorem vmPhase_qturnL (z : E2) (θ : AngCircle) :
    vmPhase (qturnL z) (θ + quarter) = vmPhase z θ := by
  rw [vmPhase_eq, vmPhase_eq, cosA_add_quarter, sinA_add_quarter, qturnL_zero, qturnL_one]
  ring

theorem integral_vmLaw_qturnL (z : E2) (h : AngCircle → ℝ) :
    ∫ θ, h θ ∂vmLaw (qturnL z) = ∫ θ, h (θ + quarter) ∂vmLaw z := by
  rw [integral_vmLaw, integral_vmLaw, vmNorm_qturnL]
  congr 1
  rw [← integral_add_quarter (fun θ => exp (vmPhase (qturnL z) θ) * h θ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [vmPhase_qturnL]

/-- the first moment of `cos` under the site law -/
noncomputable def siteCos (z : E2) : ℝ := ∫ θ, cosA θ ∂vmLaw z
/-- the first moment of `sin` under the site law -/
noncomputable def siteSin (z : E2) : ℝ := ∫ θ, sinA θ ∂vmLaw z
/-- the second moment of `cos` under the site law -/
noncomputable def siteCos2 (z : E2) : ℝ := ∫ θ, cosA θ ^ 2 ∂vmLaw z
/-- the second moment of `sin` under the site law -/
noncomputable def siteSin2 (z : E2) : ℝ := ∫ θ, sinA θ ^ 2 ∂vmLaw z

theorem siteCos_qturnL (z : E2) : siteCos (qturnL z) = - siteSin z := by
  unfold siteCos siteSin
  rw [integral_vmLaw_qturnL]
  simp_rw [cosA_add_quarter]
  rw [integral_neg]

theorem siteSin_qturnL (z : E2) : siteSin (qturnL z) = siteCos z := by
  unfold siteCos siteSin
  rw [integral_vmLaw_qturnL]
  simp_rw [sinA_add_quarter]

theorem siteCos2_qturnL (z : E2) : siteCos2 (qturnL z) = siteSin2 z := by
  unfold siteCos2 siteSin2
  rw [integral_vmLaw_qturnL]
  simp_rw [cosA_add_quarter, neg_sq]

theorem siteSin2_qturnL (z : E2) : siteSin2 (qturnL z) = siteCos2 z := by
  unfold siteCos2 siteSin2
  rw [integral_vmLaw_qturnL]
  simp_rw [sinA_add_quarter]

theorem siteCos2_add_siteSin2 (z : E2) : siteCos2 z + siteSin2 z = 1 := by
  unfold siteCos2 siteSin2
  have hc : Integrable (fun θ => cosA θ ^ 2) (vmLaw z) :=
    (continuous_cosA.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun θ => sinA θ ^ 2) (vmLaw z) :=
    (continuous_sinA.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_add hc hs]
  simp_rw [cosA_sq_add_sinA_sq]
  simp

theorem abs_integral_vmLaw_le {h : AngCircle → ℝ} {B : ℝ} (hB : ∀ θ, |h θ| ≤ B) (z : E2) :
    |∫ θ, h θ ∂vmLaw z| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := vmLaw z) (f := h) (C := B)
    (Filter.Eventually.of_forall fun θ => by simpa [Real.norm_eq_abs] using hB θ)
  simpa [Real.norm_eq_abs] using this

/-! ### continuity of site moments -/

theorem continuous_param_integral {h : AngCircle → ℝ} (hh : Continuous h) :
    Continuous fun z : E2 => ∫ θ, exp (vmPhase z θ) * h θ ∂angHaar := by
  have hz0 : Continuous fun z : E2 => z 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have hz1 : Continuous fun z : E2 => z 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have hc := continuous_cosA
  have hs := continuous_sinA
  have hjoint : Continuous (Function.uncurry fun (z : E2) (θ : AngCircle) =>
      exp (vmPhase z θ) * h θ) := by
    simp only [Function.uncurry_def, vmPhase_eq]
    fun_prop
  have := continuous_parametric_integral_of_continuous (μ := angHaar) hjoint isCompact_univ
  simpa using this

theorem continuous_vmNorm : Continuous vmNorm := by
  have := continuous_param_integral (h := fun _ => (1 : ℝ)) continuous_const
  have e : vmNorm = fun z : E2 => ∫ θ, exp (vmPhase z θ) * (1 : ℝ) ∂angHaar := by
    funext z; simp [vmNorm]
  rw [e]; exact this

theorem continuous_integral_vmLaw {h : AngCircle → ℝ} (hh : Continuous h) :
    Continuous fun z : E2 => ∫ θ, h θ ∂vmLaw z := by
  simp_rw [integral_vmLaw]
  exact (continuous_param_integral hh).div continuous_vmNorm fun z => (vmNorm_pos z).ne'

theorem continuous_siteCos : Continuous siteCos := continuous_integral_vmLaw continuous_cosA
theorem continuous_siteSin : Continuous siteSin := continuous_integral_vmLaw continuous_sinA
theorem continuous_siteCos2 : Continuous siteCos2 :=
  continuous_integral_vmLaw (continuous_cosA.pow 2)
theorem continuous_siteSin2 : Continuous siteSin2 :=
  continuous_integral_vmLaw (continuous_sinA.pow 2)


/-! ### moments under the product of von Mises laws -/

theorem integrable_pi_cont {N : ℕ+} (z : E2) {f : (Fin N → AngCircle) → ℝ} (hf : Continuous f) :
    Integrable f (Measure.pi fun _ : Fin N => vmLaw z) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_pi_eval {N : ℕ+} (z : E2) (i : Fin N) {f : AngCircle → ℝ} (hf : Continuous f) :
    ∫ θ, f (θ i) ∂(Measure.pi fun _ : Fin N => vmLaw z) = ∫ x, f x ∂vmLaw z :=
  integral_comp_eval (μ := fun _ : Fin N => vmLaw z) hf.aestronglyMeasurable

theorem integral_pi_pair {N : ℕ+} (z : E2) {i j : Fin N} (hij : i ≠ j) {f g : AngCircle → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ∫ θ, f (θ i) * g (θ j) ∂(Measure.pi fun _ : Fin N => vmLaw z) =
      (∫ x, f x ∂vmLaw z) * ∫ x, g x ∂vmLaw z := by
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => vmLaw z)
    (X := fun k => if k = i then f else g) (fun k => by
      by_cases h : k = i
      · simp only [h, ite_true]; exact hf.measurable.aemeasurable
      · simp only [h, ite_false]; exact hg.measurable.aemeasurable)
  have hXY : ProbabilityTheory.IndepFun (fun θ : Fin N → AngCircle => f (θ i)) (fun θ => g (θ j))
      (Measure.pi fun _ : Fin N => vmLaw z) := by
    simpa [hij.symm] using hind.indepFun hij
  have := hXY.integral_mul_eq_mul_integral (hf.comp (continuous_apply i)).aestronglyMeasurable
    (hg.comp (continuous_apply j)).aestronglyMeasurable
  rw [integral_pi_eval z i hf, integral_pi_eval z j hg] at this
  exact this

theorem integral_F_pi {N : ℕ+} (z : E2) :
    ∫ θ, ∑ i : Fin N, cosA (θ i) ∂(Measure.pi fun _ : Fin N => vmLaw z) =
      (N : ℝ) * siteCos z := by
  have h := integral_finsetSum (μ := Measure.pi fun _ : Fin N => vmLaw z) Finset.univ
    (f := fun (i : Fin N) (θ : Fin N → AngCircle) => cosA (θ i))
    (fun i _ => integrable_pi_cont z (continuous_cosA.comp (continuous_apply i)))
  rw [h]
  simp_rw [integral_pi_eval z _ continuous_cosA]
  simp [siteCos]

theorem integral_F_sq_pi {N : ℕ+} (z : E2) :
    ∫ θ, (∑ i : Fin N, cosA (θ i)) ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw z) =
      (N : ℝ) * siteCos2 z + (N : ℝ) * ((N : ℝ) - 1) * siteCos z ^ 2 := by
  have hc : ∀ i : Fin N, Continuous fun θ : Fin N → AngCircle => cosA (θ i) :=
    fun i => continuous_cosA.comp (continuous_apply i)
  have e : ∀ θ : Fin N → AngCircle, (∑ i, cosA (θ i)) ^ 2 =
      ∑ i, ∑ j, cosA (θ i) * cosA (θ j) := by
    intro θ; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  have hij : ∀ i j : Fin N, Integrable (fun θ : Fin N → AngCircle => cosA (θ i) * cosA (θ j))
      (Measure.pi fun _ : Fin N => vmLaw z) := fun i j =>
    integrable_pi_cont z ((hc i).mul (hc j))
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hij i j)]
  have hrow : ∀ i : Fin N, ∫ θ, ∑ j, cosA (θ i) * cosA (θ j)
      ∂(Measure.pi fun _ : Fin N => vmLaw z) = (N : ℝ) * siteCos z ^ 2 + (siteCos2 z - siteCos z ^ 2) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hij i j)]
    have : ∀ j : Fin N, ∫ θ, cosA (θ i) * cosA (θ j) ∂(Measure.pi fun _ : Fin N => vmLaw z) =
        siteCos z ^ 2 + (if i = j then siteCos2 z - siteCos z ^ 2 else 0) := by
      intro j
      by_cases h : i = j
      · subst h
        simp only [ite_true]
        have : ∫ θ, cosA (θ i) * cosA (θ i) ∂(Measure.pi fun _ : Fin N => vmLaw z) =
            ∫ θ, cosA (θ i) ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw z) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          simp [sq]
        rw [this, integral_pi_eval z i (f := fun x => cosA x ^ 2) (continuous_cosA.pow 2)]
        unfold siteCos2; ring
      · simp only [h, ite_false, add_zero]
        rw [integral_pi_pair z h continuous_cosA continuous_cosA]
        unfold siteCos; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  simp_rw [hrow]
  simp
  ring

theorem integral_sin_sq_pi {N : ℕ+} (z : E2) (i : Fin N) :
    ∫ θ, sinA (θ i) ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw z) = siteSin2 z :=
  integral_pi_eval z i (continuous_sinA.pow 2)


/-! ### integrals against a quarter-turn invariant auxiliary law -/

theorem integral_qturnL_comp (η : Measure E2) (hη : η.map qturnL = η) (φ : E2 → ℝ) :
    ∫ z, φ (qturnL z) ∂η = ∫ z, φ z ∂η := by
  conv_rhs => rw [← hη]
  exact (qturnL.toHomeomorph.measurableEmbedding.integral_map φ).symm

theorem integrable_of_abs_le (η : Measure E2) [IsFiniteMeasure η] {f : E2 → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ z, |f z| ≤ B) : Integrable f η :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB z)

theorem abs_siteCos_le (z : E2) : |siteCos z| ≤ 1 := abs_integral_vmLaw_le abs_cosA_le z
theorem abs_siteSin_le (z : E2) : |siteSin z| ≤ 1 := abs_integral_vmLaw_le abs_sinA_le z

theorem abs_cosA_sq_le (θ : AngCircle) : |cosA θ ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_cosA_le θ)

theorem abs_sinA_sq_le (θ : AngCircle) : |sinA θ ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_sinA_le θ)

theorem abs_siteCos2_le (z : E2) : |siteCos2 z| ≤ 1 := abs_integral_vmLaw_le abs_cosA_sq_le z
theorem abs_siteSin2_le (z : E2) : |siteSin2 z| ≤ 1 := abs_integral_vmLaw_le abs_sinA_sq_le z

theorem abs_sq_le_one {x : ℝ} (h : |x| ≤ 1) : |x ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h

theorem integral_siteCos_eta (η : Measure E2) [IsProbabilityMeasure η] (hη : η.map qturnL = η) :
    ∫ z, siteCos z ∂η = 0 := by
  have h1 := integral_qturnL_comp η hη siteCos
  have h2 := integral_qturnL_comp η hη siteSin
  simp_rw [siteCos_qturnL, siteSin_qturnL] at h1 h2
  rw [integral_neg] at h1
  linarith

theorem integral_siteCos2_eta (η : Measure E2) [IsProbabilityMeasure η] (hη : η.map qturnL = η) :
    ∫ z, siteCos2 z ∂η = 1 / 2 := by
  have h1 := integral_qturnL_comp η hη siteCos2
  simp_rw [siteCos2_qturnL] at h1
  have hc : Integrable siteCos2 η := integrable_of_abs_le η continuous_siteCos2 abs_siteCos2_le
  have hs : Integrable siteSin2 η := integrable_of_abs_le η continuous_siteSin2 abs_siteSin2_le
  have h3 := integral_add hc hs
  simp_rw [siteCos2_add_siteSin2] at h3
  simp at h3
  linarith

theorem integral_siteSin2_eta (η : Measure E2) [IsProbabilityMeasure η] (hη : η.map qturnL = η) :
    ∫ z, siteSin2 z ∂η = 1 / 2 := by
  have h1 := integral_qturnL_comp η hη siteCos2
  simp_rw [siteCos2_qturnL] at h1
  rw [h1]
  exact integral_siteCos2_eta η hη

theorem integral_siteCos_sq_eta (η : Measure E2) [IsProbabilityMeasure η] (hη : η.map qturnL = η) :
    ∫ z, siteCos z ^ 2 ∂η = 1 / 2 * ∫ z, besselRatio ‖z‖ ^ 2 ∂η := by
  have h1 := integral_qturnL_comp η hη (fun z => siteCos z ^ 2)
  simp only [siteCos_qturnL, neg_sq] at h1
  have hc : Integrable (fun z => siteCos z ^ 2) η :=
    integrable_of_abs_le η (continuous_siteCos.pow 2) (fun z => abs_sq_le_one (abs_siteCos_le z))
  have hs : Integrable (fun z => siteSin z ^ 2) η :=
    integrable_of_abs_le η (continuous_siteSin.pow 2) (fun z => abs_sq_le_one (abs_siteSin_le z))
  have h3 := integral_add hc hs
  have e : ∀ z : E2, siteCos z ^ 2 + siteSin z ^ 2 = besselRatio ‖z‖ ^ 2 := fun z => mean_sq_add z
  simp_rw [e] at h3
  linarith


/-! ### bridge to the unit torus -/

theorem mode_one_re (y : DGPS.Torus 1) : (DGPS.FiniteN.mode 1 y).re = cosA (angEquiv y) := by
  have hx : y = DGPS.torusLift (SharpLSI.secT y) := by
    simp [DGPS.torusLift, SharpLSI.liftT_secT]
  set u := SharpLSI.secT y 0 with hu
  have h1 : angEquiv y = ((2 * π * u : ℝ) : AngCircle) := by
    rw [angEquiv_apply]
    have : y 0 = ((u : ℝ) : UnitAddCircle) := by
      conv_lhs => rw [hx]
      rfl
    rw [this, angRescale_mk]
  rw [h1, cosA_coe, hx, DGPS.FiniteN.mode_lift]
  have h : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (SharpLSI.secT y 0 : ℂ)) =
      ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]


theorem mode_one_im (y : DGPS.Torus 1) : (DGPS.FiniteN.mode 1 y).im = sinA (angEquiv y) := by
  have hx : y = DGPS.torusLift (SharpLSI.secT y) := by
    simp [DGPS.torusLift, SharpLSI.liftT_secT]
  set u := SharpLSI.secT y 0 with hu
  have h1 : angEquiv y = ((2 * π * u : ℝ) : AngCircle) := by
    rw [angEquiv_apply]
    have : y 0 = ((u : ℝ) : UnitAddCircle) := by
      conv_lhs => rw [hx]
      rfl
    rw [this, angRescale_mk]
  rw [h1, sinA_coe, hx, DGPS.FiniteN.mode_lift]
  have h : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (SharpLSI.secT y 0 : ℂ)) =
      ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]


/-! ### the magnetization and the mixture hypothesis -/

/-- The magnetization `θ ↦ ∑ᵢ cos θᵢ` on the angular torus. -/
noncomputable def magnetization (N : ℕ+) (θ : AngParticleSpace N) : ℝ := ∑ i, cosA (θ i)

/-- The (unnormalized) Dirichlet integrand `θ ↦ ∑ᵢ 4π² sin² θᵢ` of the magnetization. -/
noncomputable def sinEnergy (N : ℕ+) (θ : AngParticleSpace N) : ℝ :=
  ∑ i, (4 * Real.pi ^ 2) * sinA (θ i) ^ 2

theorem continuous_magnetization (N : ℕ+) : Continuous (magnetization N) :=
  continuous_finsetSum _ fun i _ => continuous_cosA.comp (continuous_apply i)

theorem continuous_sinEnergy (N : ℕ+) : Continuous (sinEnergy N) :=
  continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_sinA.comp (continuous_apply i)).pow 2)

/-- The angular particle law of `A` is the mixture over `z ∼ η` of the product von Mises laws
`q_z^{⊗N}` (tested against continuous observables). -/
def IsAngularMixture (A : DGPS.InteractionData 1) (N : ℕ+) (η : Measure E2) : Prop :=
  ∀ G : AngParticleSpace N → ℝ, Continuous G →
    ∫ θ, G θ ∂angParticleLaw (angV A) (angW A) N =
      ∫ z, ∫ θ, G θ ∂(Measure.pi fun _ : Fin N => vmLaw z) ∂η

theorem integral_magnetization_pi {N : ℕ+} (z : E2) :
    ∫ θ, magnetization N θ ∂(Measure.pi fun _ : Fin N => vmLaw z) = (N : ℝ) * siteCos z :=
  integral_F_pi z

theorem integral_magnetization_sq_pi {N : ℕ+} (z : E2) :
    ∫ θ, magnetization N θ ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw z) =
      (N : ℝ) * siteCos2 z + (N : ℝ) * ((N : ℝ) - 1) * siteCos z ^ 2 :=
  integral_F_sq_pi z

theorem integral_sinEnergy_pi {N : ℕ+} (z : E2) :
    ∫ θ, sinEnergy N θ ∂(Measure.pi fun _ : Fin N => vmLaw z) =
      (N : ℝ) * ((4 * Real.pi ^ 2) * siteSin2 z) := by
  unfold sinEnergy
  have hc : ∀ i : Fin N, Continuous fun θ : Fin N → AngCircle =>
      (4 * Real.pi ^ 2) * sinA (θ i) ^ 2 := fun i =>
    continuous_const.mul ((continuous_sinA.comp (continuous_apply i)).pow 2)
  rw [integral_finsetSum _ (fun i _ => integrable_pi_cont z (hc i))]
  have : ∀ i : Fin N, ∫ θ, (4 * Real.pi ^ 2) * sinA (θ i) ^ 2
      ∂(Measure.pi fun _ : Fin N => vmLaw z) = (4 * Real.pi ^ 2) * siteSin2 z := by
    intro i
    rw [integral_const_mul, integral_sin_sq_pi]
  simp_rw [this]
  simp

theorem harmonicTrial_eq_magnetization (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.FiniteN.harmonicTrial N x = magnetization N (angEquivN N x) := by
  unfold DGPS.FiniteN.harmonicTrial magnetization
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mode_one_re, angEquivN_apply]

theorem sum_im_eq_sinEnergy (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    ∑ i, (4 * Real.pi ^ 2) * (DGPS.FiniteN.mode 1 (x i)).im ^ 2 = sinEnergy N (angEquivN N x) := by
  unfold sinEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mode_one_im, angEquivN_apply]

end DGPS.FiniteN.RotationalTools

namespace DGPS.FiniteN

open DGPS.FiniteN.RotationalTools

/-- **FIN031 (generic form).** Let the angular particle law of `A` be a mixture `∫ q_z^{⊗N} dη(z)`
of product von Mises laws over a quarter-turn invariant (in particular radial) probability
measure `η` on the auxiliary plane.  Then `F = ∑ᵢ cos 2π xᵢ` is a smooth symmetric `H¹` test with
`E(F) = 0`, `Var(F) = (N/2) [1 + (N-1) ∫ g(|z|)² dη]` (`g = I₁/I₀`) and Dirichlet energy
`a₀ N / 2`. -/
theorem rotational_symmetric_magnetization_variance (A : DGPS.InteractionData 1) (N : ℕ+)
    (η : Measure E2) [IsProbabilityMeasure η] (hη : η.map qturnL = η)
    (hmix : IsAngularMixture A N η) :
    ∃ f : DGPS.ParticleH1 A N,
      f.1 = (fun x : DGPS.ParticleSpace 1 N => ∑ i, (mode 1 (x i)).re) ∧
      DGPS.IsSmoothPeriodicParticle f.1 ∧
      (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
        f.1 (DGPS.permuteParticles σ x) = f.1 x) ∧
      DGPS.IsSymmetricParticleTest f ∧
      ∫ x, f.1 x ∂DGPS.particleLaw A N = 0 ∧
      ProbabilityTheory.variance f.1 (DGPS.particleLaw A N) =
        (N : ℝ) / 2 * (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂η) ∧
      DGPS.particleEnergy A N f = DGPS.Circle.AngularNormalization.a0 * (N : ℝ) / 2 ∧
      DGPS.particlePoincareQuotient A N f =
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 /
          (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂η)) := by
  set P := DGPS.particleLaw A N with hP
  have hPprob : IsProbabilityMeasure P := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have ha0 : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 :=
    (angular_to_unit_torus_normalization).1
  set Gg : ℝ := ∫ z, besselRatio ‖z‖ ^ 2 ∂η with hGg
  have hGg0 : 0 ≤ Gg := integral_nonneg fun z => sq_nonneg _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  -- transfer of integrals to the mixture
  have hT : ∀ (g : DGPS.ParticleSpace 1 N → ℝ) (G : AngParticleSpace N → ℝ), Continuous G →
      (∀ x, g x = G (angEquivN N x)) →
      ∫ x, g x ∂P = ∫ z, ∫ θ, G θ ∂(Measure.pi fun _ : Fin N => vmLaw z) ∂η := by
    intro g G hG hg
    have hgG : g = G ∘ angEquivN N := funext hg
    rw [hgG]
    calc ∫ x, (G ∘ angEquivN N) x ∂P
        = ∫ θ, G θ ∂angParticleLaw (angV A) (angW A) N :=
          (measurePreserving_angEquivN_law A N).integral_comp' (f := angEquivN N) G
      _ = _ := hmix G hG
  -- membership in H¹
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth
    (isSmooth_harmonicTrial N)
  have hGP : DGPS.IsParticleWeakGradient A N (harmonicTrial N)
      (fun x i => WithLp.toLp 2 fun j => DGPS.particlePartial i j (harmonicTrial N) x) :=
    (DGPS.isParticleWeakGradient_iff A N _ _).2 hG
  have hmem : DGPS.MemParticleH1 A N (harmonicTrial N) := ⟨_, hGP⟩
  set f : DGPS.ParticleH1 A N := ⟨harmonicTrial N, hmem⟩ with hf
  have hfv : f.1 = harmonicTrial N := rfl
  have hc1 : Integrable siteCos η :=
    integrable_of_abs_le η continuous_siteCos abs_siteCos_le
  have hc2 : Integrable siteCos2 η :=
    integrable_of_abs_le η continuous_siteCos2 abs_siteCos2_le
  have hcs : Integrable (fun z => siteCos z ^ 2) η :=
    integrable_of_abs_le η (continuous_siteCos.pow 2) (fun z => abs_sq_le_one (abs_siteCos_le z))
  -- mean
  have hmean : ∫ x, harmonicTrial N x ∂P = 0 := by
    rw [hT _ (magnetization N) (continuous_magnetization N)
      (harmonicTrial_eq_magnetization N)]
    simp_rw [integral_magnetization_pi]
    rw [integral_const_mul, integral_siteCos_eta η hη]
    simp
  -- second moment
  have hsq : ∫ x, (harmonicTrial N x) ^ 2 ∂P = (N : ℝ) / 2 * (1 + ((N : ℝ) - 1) * Gg) := by
    rw [hT _ (fun θ => magnetization N θ ^ 2) ((continuous_magnetization N).pow 2)
      (fun x => by simp only [harmonicTrial_eq_magnetization])]
    simp_rw [integral_magnetization_sq_pi]
    rw [integral_add (hc2.const_mul _) (hcs.const_mul _), integral_const_mul, integral_const_mul,
      integral_siteCos2_eta η hη, integral_siteCos_sq_eta η hη]
    ring
  have hvar : ProbabilityTheory.variance (harmonicTrial N) P =
      (N : ℝ) / 2 * (1 + ((N : ℝ) - 1) * Gg) := by
    rw [ProbabilityTheory.variance_eq_integral (continuous_harmonicTrial N).aemeasurable]
    simp only [hmean, sub_zero]
    exact hsq
  have hvpos : 0 < (N : ℝ) / 2 * (1 + ((N : ℝ) - 1) * Gg) := by
    have : 0 ≤ ((N : ℝ) - 1) * Gg := mul_nonneg (by linarith) hGg0
    positivity
  -- energy
  have hen : DGPS.particleEnergy A N f = DGPS.Circle.AngularNormalization.a0 * (N : ℝ) / 2 := by
    rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient f hGP, ha0]
    simp only [DGPS.particleTangentNormSq_eq]
    have e : ∀ x : DGPS.ParticleSpace 1 N,
        ∑ i, ∑ j : Fin 1, (WithLp.toLp 2 (fun j => DGPS.particlePartial i j (harmonicTrial N) x) :
          DGPS.Tangent 1) j ^ 2 = ∑ i, (4 * Real.pi ^ 2) * (mode 1 (x i)).im ^ 2 := by
      intro x
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.sum_univ_one]
      rw [particlePartial_harmonicTrial]; ring
    simp_rw [e]
    rw [← hP, hT _ (sinEnergy N) (continuous_sinEnergy N) (sum_im_eq_sinEnergy N)]
    simp_rw [integral_sinEnergy_pi]
    rw [integral_const_mul, integral_const_mul, integral_siteSin2_eta η hη]
    ring
  refine ⟨f, rfl, isSmooth_harmonicTrial N, ?_, ?_, hmean, hvar, hen, ?_⟩
  · intro σ x
    show harmonicTrial N _ = harmonicTrial N x
    rw [harmonicTrial_eq_witness, DGPS.FiniteN.PositiveRate.witnessSum_permute]
  · rw [DGPS.isSymmetricParticleTest_iff f]
    intro σ
    refine Filter.Eventually.of_forall fun x => ?_
    show harmonicTrial N _ = harmonicTrial N x
    rw [harmonicTrial_eq_witness, DGPS.FiniteN.PositiveRate.witnessSum_permute]
  · unfold DGPS.particlePoincareQuotient
    rw [hen, hfv, hvar, ← ENNReal.ofReal_div_of_pos hvpos]
    congr 1
    field_simp

end DGPS.FiniteN

namespace DGPS.FiniteN.RotationalTools

theorem map_qturnL_withDensity (h : E2 → ENNReal) (hh : ∀ x, h (qturnL x) = h x) :
    ((volume : Measure E2).withDensity h).map qturnL = (volume : Measure E2).withDensity h := by
  refine Measure.ext fun s hs => ?_
  have hm : Measurable qturnL := qturnL.toHomeomorph.measurable
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs]
  have hT : MeasurePreserving qturnL (volume : Measure E2) volume := qturnL.measurePreserving
  have := hT.setLIntegral_comp_preimage_emb qturnL.toHomeomorph.measurableEmbedding h s
  simp_rw [hh] at this
  exact this

theorem criticalAuxiliaryLaw_map_qturnL (M : ℝ) :
    (criticalAuxiliaryLaw M).map qturnL = criticalAuxiliaryLaw M := by
  unfold criticalAuxiliaryLaw DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs
  refine map_qturnL_withDensity _ fun x => ?_
  simp only [criticalPotential, norm_qturnL]

theorem isProbabilityMeasure_criticalAuxiliaryLaw (N : ℕ+) :
    IsProbabilityMeasure (criticalAuxiliaryLaw (N : ℝ)) := by
  rw [← auxLaw_map_critical N]
  exact (Measure.isProbabilityMeasure_map_iff
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable).2
    (DGPS.FiniteN.Tools.AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_angular
      criticalD_posDef (fun _ : Fin 2 => (0 : ℝ)) N)

theorem isAngularMixture_critical {A : DGPS.InteractionData 1} (hA : IsCriticalXY A) (N : ℕ+) :
    IsAngularMixture A N (criticalAuxiliaryLaw (N : ℝ)) := by
  intro G hG
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  rw [particleLaw_critical hA N]
  have key := DGPS.FiniteN.Tools.AuxiliaryTransfer.integral_particle_eq hubbardHyp_angular criticalD_posDef
    (fun _ : Fin 2 => (0 : ℝ)) N hG.measurable (B := C) (fun x => by simpa using hC x (Set.mem_univ x))
  rw [key, ← auxLaw_map_critical N]
  rw [(MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [MeasurableEquiv.toLp_apply]
  rw [pi_vmLaw_eq_condLaw]

end DGPS.FiniteN.RotationalTools

namespace DGPS.FiniteN

open DGPS.FiniteN.RotationalTools

/-- **FIN031 (critical XY).**  For the critical XY model, the radial auxiliary law is
`η_N = criticalAuxiliaryLaw N` and the generic statement holds with this `η_N`:
`P(F) = 0`, `Var(F) = (N/2) [1 + (N-1) ∫ g(|z|)² dη_N]`, `E(F) = a₀ N / 2`. -/
theorem rotational_symmetric_magnetization_variance_critical {A : DGPS.InteractionData 1}
    (hA : IsCriticalXY A) (N : ℕ+) :
    ∃ f : DGPS.ParticleH1 A N,
      f.1 = (fun x : DGPS.ParticleSpace 1 N => ∑ i, (mode 1 (x i)).re) ∧
      DGPS.IsSmoothPeriodicParticle f.1 ∧
      (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
        f.1 (DGPS.permuteParticles σ x) = f.1 x) ∧
      DGPS.IsSymmetricParticleTest f ∧
      ∫ x, f.1 x ∂DGPS.particleLaw A N = 0 ∧
      ProbabilityTheory.variance f.1 (DGPS.particleLaw A N) =
        (N : ℝ) / 2 * (1 + ((N : ℝ) - 1) *
          ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ)) ∧
      DGPS.particleEnergy A N f = DGPS.Circle.AngularNormalization.a0 * (N : ℝ) / 2 ∧
      DGPS.particlePoincareQuotient A N f =
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 /
          (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ))) := by
  have := isProbabilityMeasure_criticalAuxiliaryLaw N
  exact rotational_symmetric_magnetization_variance A N (criticalAuxiliaryLaw (N : ℝ))
    (criticalAuxiliaryLaw_map_qturnL _) (isAngularMixture_critical hA N)

end DGPS.FiniteN
