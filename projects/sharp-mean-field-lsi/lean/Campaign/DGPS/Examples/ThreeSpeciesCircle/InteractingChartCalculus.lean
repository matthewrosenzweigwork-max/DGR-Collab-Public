import DGPS.Examples.ThreeSpeciesCircle.InteractingBranchBaseInverse
import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNativeMoments
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackMeans

/-! The actual fixed-h rank-three angular feedback formulas on the retained
periodic Holder carriers. Smoothness and the zero-coupling identity are proved here.
Identification with the native first variation is a separate bridge. Physical rate
r = a0 * (1 + gamma); the returned gradient is divided by a0. -/

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private def chartFeature (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 :=
  ![h⁻¹ • e0_STR02955 cosC2_STR02915,
    h⁻¹ • e0_STR02955 sinC2_STR02915,
    (15 / (4 * h ^ 3)) • (c3_STR02954 - referenceMean h • (1 : PeriodicHolder_STR02968))] i

private def chartFeatureD (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 :=
  ![(-h⁻¹) • e0_STR02955 sinC2_STR02915,
    h⁻¹ • e0_STR02955 cosC2_STR02915, (-45 / (4 * h ^ 3)) • s3_STR02955] i

private def chartFeatureDD (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 :=
  ![(-h⁻¹) • e0_STR02955 cosC2_STR02915,
    (-h⁻¹) • e0_STR02955 sinC2_STR02915, (-135 / (4 * h ^ 3)) • c3_STR02954] i

private def chartFeatureA (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 :=
  a0 • (-chartFeatureDD h i + (3 * h) • (s3_STR02955 * chartFeatureD h i))

private def chartCoefficient (i : Fin 3) : ℝ := ![kAlpha, kAlpha, -kBeta] i

private def chartDensity (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  rho_STR02954 (h, e0_STR02955 u)

private def chartMean (h : ℝ) (u : PeriodicC2_STR02969) (f : PeriodicHolder_STR02968) : ℝ :=
  meanCLM_STR02954 (chartDensity h u * f)

private theorem chartDensity_smooth (h : ℝ) : ContDiff ℝ ∞ (chartDensity h) :=
  rho_smooth_STR02954.comp (contDiff_const.prodMk e0_STR02955.contDiff)

private theorem chartMean_smooth (h : ℝ) (f : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (fun u => chartMean h u f) :=
  meanCLM_STR02954.contDiff.comp ((chartDensity_smooth h).mul contDiff_const)

private def chartKernel (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (chartCoefficient i * chartMean h u (chartFeature h i)) • chartFeature h i

private def chartKernelD (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (chartCoefficient i * chartMean h u (chartFeature h i)) • chartFeatureD h i

private def chartKernelA (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (chartCoefficient i * chartMean h u (chartFeature h i)) • chartFeatureA h i

private def chartGeneratorFeedback (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (chartCoefficient i * chartMean h u (chartFeatureA h i)) • chartFeature h i

private def chartForceFeedback (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3,
    (chartCoefficient i * chartMean h u (chartKernelD h u * chartFeatureD h i)) • chartFeature h i

private theorem chartKernel_smooth (h : ℝ) : ContDiff ℝ ∞ (chartKernel h) := by
  unfold chartKernel
  exact ContDiff.sum fun i _ =>
    (contDiff_const.mul (chartMean_smooth h _)).smul contDiff_const

private theorem chartKernelD_smooth (h : ℝ) : ContDiff ℝ ∞ (chartKernelD h) := by
  unfold chartKernelD
  exact ContDiff.sum fun i _ =>
    (contDiff_const.mul (chartMean_smooth h _)).smul contDiff_const

private theorem chartKernelA_smooth (h : ℝ) : ContDiff ℝ ∞ (chartKernelA h) := by
  unfold chartKernelA
  exact ContDiff.sum fun i _ =>
    (contDiff_const.mul (chartMean_smooth h _)).smul contDiff_const

private theorem chartGeneratorFeedback_smooth (h : ℝ) :
    ContDiff ℝ ∞ (chartGeneratorFeedback h) := by
  unfold chartGeneratorFeedback
  exact ContDiff.sum fun i _ =>
    (contDiff_const.mul (chartMean_smooth h _)).smul contDiff_const

private theorem chartForceFeedback_smooth (h : ℝ) : ContDiff ℝ ∞ (chartForceFeedback h) := by
  unfold chartForceFeedback
  refine ContDiff.sum fun i _ => ?_
  have hm : ContDiff ℝ ∞ (fun u => chartMean h u (chartKernelD h u * chartFeatureD h i)) :=
    meanCLM_STR02954.contDiff.comp
      ((chartDensity_smooth h).mul ((chartKernelD_smooth h).mul contDiff_const))
  exact (contDiff_const.mul hm).smul contDiff_const

private def chartCFeedback (h γ : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  chartKernelA h u + chartGeneratorFeedback h u - (a0 * (1 + γ)) • chartKernel h u

private def chartJFeedback (h : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  a0 • (chartKernelD h u * chartKernelD h u + (2 : ℝ) • chartForceFeedback h u)

private theorem chartCFeedback_smooth (h : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicC2_STR02969 => chartCFeedback h x.1 x.2) := by
  unfold chartCFeedback
  exact (((chartKernelA_smooth h).comp contDiff_snd).add
    ((chartGeneratorFeedback_smooth h).comp contDiff_snd)).sub
      ((contDiff_const.mul (contDiff_const.add contDiff_fst)).smul
        ((chartKernel_smooth h).comp contDiff_snd))

private theorem chartJFeedback_smooth (h : ℝ) : ContDiff ℝ ∞ (chartJFeedback h) := by
  unfold chartJFeedback
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : PeriodicC2_STR02969 => a0)).smul
    (((chartKernelD_smooth h).mul (chartKernelD_smooth h)).add
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : PeriodicC2_STR02969 => (2 : ℝ))).smul
        (chartForceFeedback_smooth h)))

private def chartCenter (h : ℝ) (u : PeriodicC2_STR02969)
    (f : PeriodicHolder_STR02968) : PeriodicHolder_STR02968 :=
  chartDensity h u * (f - chartMean h u f • (1 : PeriodicHolder_STR02968))

private theorem chartCenter_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : ℝ) {u : X → PeriodicC2_STR02969} {f : X → PeriodicHolder_STR02968}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => chartCenter h (u x) (f x)) := by
  have hr := (chartDensity_smooth h).comp hu
  have hm := meanCLM_STR02954.contDiff.comp (hr.mul hf)
  exact hr.mul (hf.sub (hm.smul contDiff_const))

/-- Fixed-h angular expression of the full nonlinear feedback gradient. The
physical rate is a0*(1+gamma), and the whole gradient is normalized by a0. -/
def interactingChartGradient (h : ℝ) (x : ℝ × ℝ × PeriodicC2_STR02969) :
    PeriodicHolder_STR02968 :=
  Gfun_STR02955 h x.2.1 x.2.2 +
    (2 * x.1 / a0) • chartCenter h x.2.2 (chartCFeedback h x.2.1 x.2.2) +
    (x.1 ^ 2 / a0) • chartCenter h x.2.2 (chartJFeedback h x.2.2)

/-- Smoothness includes every real perturbation epsilon at each fixed h. -/
theorem interactingChartGradient_smooth (h : ℝ) : ContDiff ℝ ∞ (interactingChartGradient h) := by
  have hu : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hγ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hε : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.1) := contDiff_fst
  have hG := Gmap_smooth_STR02955.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ × PeriodicC2_STR02969 => h)).prodMk (hγ.prodMk hu))
  have hC := (chartCFeedback_smooth h).comp (hγ.prodMk hu)
  have hJ := (chartJFeedback_smooth h).comp hu
  unfold interactingChartGradient
  exact (hG.add (((contDiff_const.mul hε).div_const a0).smul
    (chartCenter_smooth h hu hC))).add
      (((hε.pow 2).div_const a0).smul (chartCenter_smooth h hu hJ))

/-- At epsilon zero the full expression is exactly the retained ordinary gradient. -/
theorem interactingChartGradient_zero (h γ : ℝ) (u : PeriodicC2_STR02969) :
    interactingChartGradient h (0, γ, u) = Gfun_STR02955 h γ u := by
  simp [interactingChartGradient]

/-- The fixed-h complement map on the SAME ordinary amplitude/rate coordinates.
Parameters are epsilon, a, b, gamma, with complement w. -/
def interactingChartRange (h : ℝ) (q : (ℝ × ℝ × ℝ × ℝ) × E_STR02969) : Y_STR02969 :=
  PY_STR02955 (interactingChartGradient h
    (q.1.1, q.1.2.2.2,
      q.1.2.1 • cosC2_STR02915 + q.1.2.2.1 • sinC2_STR02915 +
        (q.2 : PeriodicC2_STR02969)))

theorem interactingChartRange_smooth (h : ℝ) : ContDiff ℝ ∞ (interactingChartRange h) := by
  have hu : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ × ℝ) × E_STR02969 =>
      q.1.2.1 • cosC2_STR02915 + q.1.2.2.1 • sinC2_STR02915 +
        (q.2 : PeriodicC2_STR02969)) := by
    have ha : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ × ℝ) × E_STR02969 => q.1.2.1) := by fun_prop
    have hb : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ × ℝ) × E_STR02969 => q.1.2.2.1) := by fun_prop
    exact ((ha.smul contDiff_const).add (hb.smul contDiff_const)).add
      (E_STR02969.subtypeL.contDiff.comp contDiff_snd)
  unfold interactingChartRange
  exact PY_STR02955.contDiff.comp ((interactingChartGradient_smooth h).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.snd.snd.prodMk hu)))

/-- No new range convention is introduced at zero coupling. -/
theorem interactingChartRange_zero (h a b γ : ℝ) (w : E_STR02969) :
    interactingChartRange h ((0, a, b, γ), w) = Rpar_STR02916 (a, b, h, γ) w := by
  unfold interactingChartRange
  rw [interactingChartGradient_zero]
  rfl

private def chartC (h γ : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  2 * chartMean h u (chartKernelA h u) -
    a0 * (1 + γ) * chartMean h u (chartKernel h u)

private def chartJ (h : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  a0 * chartMean h u (chartKernelD h u * chartKernelD h u)

private theorem chartC_smooth (h : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicC2_STR02969 => chartC h x.1 x.2) := by
  have hr := (chartDensity_smooth h).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × PeriodicC2_STR02969 → _))
  have hAK := (chartKernelA_smooth h).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × PeriodicC2_STR02969 → _))
  have hK := (chartKernel_smooth h).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × PeriodicC2_STR02969 → _))
  unfold chartC chartMean
  exact (contDiff_const.mul (meanCLM_STR02954.contDiff.comp (hr.mul hAK))).sub
    ((contDiff_const.mul (contDiff_const.add contDiff_fst)).mul
      (meanCLM_STR02954.contDiff.comp (hr.mul hK)))

private theorem chartJ_smooth (h : ℝ) : ContDiff ℝ ∞ (chartJ h) := by
  unfold chartJ chartMean
  exact contDiff_const.mul (meanCLM_STR02954.contDiff.comp
    ((chartDensity_smooth h).mul ((chartKernelD_smooth h).mul (chartKernelD_smooth h))))

private theorem ordinaryChartDeficit_joint_smooth (h : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicC2_STR02969 => JC2_STR02956 h x.1 x.2) := by
  have h0 : ContDiff ℝ ∞ (fun x : ℝ × PeriodicC2_STR02969 => e0_STR02955 x.2) :=
    e0_STR02955.contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × PeriodicC2_STR02969 => e1_STR02955 x.2) :=
    e1_STR02955.contDiff.comp contDiff_snd
  have hr := rho_smooth_STR02954.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × PeriodicC2_STR02969 => h)).prodMk h0)
  have hZ := logZ_smooth_STR02954.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × PeriodicC2_STR02969 => h)).prodMk h0)
  have hI := meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hr)
  have hE := meanCLM_STR02954.contDiff.comp (h0.mul hr)
  unfold JC2_STR02956
  exact hI.sub ((contDiff_const.mul (contDiff_const.add contDiff_fst)).mul
    ((hE.sub hZ).add contDiff_const))

/-- The fixed-h physical deficit divided by a0, in the actual three-feature
angular formula. The native functional identification is a separate bridge. -/
def interactingChartDeficit (h : ℝ) (x : ℝ × ℝ × PeriodicC2_STR02969) : ℝ :=
  JC2_STR02956 h x.2.1 x.2.2 + (x.1 / a0) * chartC h x.2.1 x.2.2 +
    (x.1 ^ 2 / a0) * chartJ h x.2.2

theorem interactingChartDeficit_smooth (h : ℝ) : ContDiff ℝ ∞ (interactingChartDeficit h) := by
  have hu : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hγ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hε : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.1) := contDiff_fst
  unfold interactingChartDeficit
  exact (((ordinaryChartDeficit_joint_smooth h).comp (hγ.prodMk hu)).add
    ((hε.div_const a0).mul ((chartC_smooth h).comp (hγ.prodMk hu)))).add
      (((hε.pow 2).div_const a0).mul ((chartJ_smooth h).comp hu))

/-- The zero-coupling scalar constraint is the exact retained ordinary deficit. -/
theorem interactingChartDeficit_zero (h γ : ℝ) (u : PeriodicC2_STR02969) :
    interactingChartDeficit h (0, γ, u) = JC2_STR02956 h γ u := by
  simp [interactingChartDeficit]

/-! Native dictionary, including arbitrary stored square-root representatives.
The angular density representation is required only almost everywhere. -/

private theorem chart_angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

private def nativeFeature (h : ℝ) (i : Fin 3) : Torus 1 → ℝ :=
  ![featureC h, featureS h, featureB h] i

private theorem nativeFeature_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (nativeFeature h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private def featureLift (h : ℝ) (i : Fin 3) (s : ℝ) : ℝ :=
  ![Real.cos (2 * Real.pi * s) / h, Real.sin (2 * Real.pi * s) / h,
    15 * (Real.cos (6 * Real.pi * s) - referenceMean h) / (4 * h ^ 3)] i

private def featureLiftD (h : ℝ) (i : Fin 3) (s : ℝ) : ℝ :=
  ![-(2 * Real.pi) * Real.sin (2 * Real.pi * s) / h,
    (2 * Real.pi) * Real.cos (2 * Real.pi * s) / h,
    -(90 * Real.pi) * Real.sin (6 * Real.pi * s) / (4 * h ^ 3)] i

private def featureLiftDD (h : ℝ) (i : Fin 3) (s : ℝ) : ℝ :=
  ![-(2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * s) / h,
    -(2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi * s) / h,
    -(540 * Real.pi ^ 2) * Real.cos (6 * Real.pi * s) / (4 * h ^ 3)] i

private theorem featureLift_value (h : ℝ) (i : Fin 3) (s : ℝ) :
    nativeFeature h i (pt s) = featureLift h i s := by
  fin_cases i <;> simp only [nativeFeature, featureLift, featureC, featureS, featureB,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, cosHarm_pt, sinHarm_pt,
    Nat.cast_one, Nat.cast_ofNat, mul_one]
  all_goals first | rfl | (congr 3 <;> ring)

private theorem featureLift_deriv (h : ℝ) (i : Fin 3) (s : ℝ) :
    HasDerivAt (featureLift h i) (featureLiftD h i s) s := by
  fin_cases i
  · change HasDerivAt (fun y => Real.cos (2 * Real.pi * y) / h)
      (-(2 * Real.pi) * Real.sin (2 * Real.pi * s) / h) s
    exact (((hasDerivAt_id s).const_mul (2 * Real.pi)).cos.div_const h).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun y => Real.sin (2 * Real.pi * y) / h)
      ((2 * Real.pi) * Real.cos (2 * Real.pi * s) / h) s
    exact (((hasDerivAt_id s).const_mul (2 * Real.pi)).sin.div_const h).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun y => 15 * (Real.cos (6 * Real.pi * y) - referenceMean h) / (4 * h ^ 3))
      (-(90 * Real.pi) * Real.sin (6 * Real.pi * s) / (4 * h ^ 3)) s
    exact (((((hasDerivAt_id s).const_mul (6 * Real.pi)).cos.sub_const
      (referenceMean h)).const_mul 15).div_const (4 * h ^ 3)).congr_deriv (by simp only [id_eq]; ring)

private theorem featureLift_deriv2 (h : ℝ) (i : Fin 3) (s : ℝ) :
    HasDerivAt (featureLiftD h i) (featureLiftDD h i s) s := by
  fin_cases i
  · change HasDerivAt (fun y => -(2 * Real.pi) * Real.sin (2 * Real.pi * y) / h)
      (-(2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * s) / h) s
    exact ((((hasDerivAt_id s).const_mul (2 * Real.pi)).sin.const_mul
      (-(2 * Real.pi))).div_const h).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun y => (2 * Real.pi) * Real.cos (2 * Real.pi * y) / h)
      (-(2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi * s) / h) s
    exact ((((hasDerivAt_id s).const_mul (2 * Real.pi)).cos.const_mul
      (2 * Real.pi)).div_const h).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun y => -(90 * Real.pi) * Real.sin (6 * Real.pi * y) / (4 * h ^ 3))
      (-(540 * Real.pi ^ 2) * Real.cos (6 * Real.pi * s) / (4 * h ^ 3)) s
    exact ((((hasDerivAt_id s).const_mul (6 * Real.pi)).sin.const_mul
      (-(90 * Real.pi))).div_const (4 * h ^ 3)).congr_deriv (by simp only [id_eq]; ring)

private theorem nativeFeature_derivatives (h : ℝ) (i : Fin 3) (s : ℝ) :
    coordPartial 0 (nativeFeature h i) (pt s) = featureLiftD h i s ∧
      elementaryFeatureGenerator h (nativeFeature h i) (pt s) =
        -featureLiftDD h i s - sg0 h s * featureLiftD h i s := by
  have hfun : (fun y => nativeFeature h i (pt y)) = featureLift h i :=
    funext (featureLift_value h i)
  have hfirst (y : ℝ) : coordPartial 0 (nativeFeature h i) (pt y) = featureLiftD h i y := by
    have hd := circ_coordPartial_pt (nativeFeature_smooth h i) y
    rw [hfun] at hd
    exact hd.unique (featureLift_deriv h i y)
  have hd2 := circ_coordPartial_pt ((nativeFeature_smooth h i).isSmoothPeriodic_coordPartial 0) s
  rw [show (fun y => coordPartial 0 (nativeFeature h i) (pt y)) = featureLiftD h i from
    funext hfirst] at hd2
  refine ⟨hfirst s, ?_⟩
  unfold elementaryFeatureGenerator
  rw [hfirst, hd2.unique (featureLift_deriv2 h i s), sigT_lift]

private theorem chart_neg_val (F : PeriodicHolder_STR02968) (t : ℝ) :
    (-F).val t = -F.val t := rfl

private theorem chart_c3_val (t : ℝ) : c3_STR02954.val t = Real.cos (3 * t) := rfl
private theorem chart_s3_val (t : ℝ) : s3_STR02955.val t = Real.sin (3 * t) := rfl

private theorem chartFeature_dictionary {h : ℝ} (hh : 0 < h) (i : Fin 3) (t : ℝ) :
    (chartFeature h i).val t = nativeFeature h i (angEquiv.symm (t : AngCircle)) ∧
      (2 * Real.pi) * (chartFeatureD h i).val t =
        coordPartial 0 (nativeFeature h i) (angEquiv.symm (t : AngCircle)) ∧
      (chartFeatureA h i).val t =
        elementaryFeatureGenerator h (nativeFeature h i) (angEquiv.symm (t : AngCircle)) := by
  have hc : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  simp only [chart_angular_point, featureLift_value,
    (nativeFeature_derivatives h i (t / (2 * Real.pi))).1,
    (nativeFeature_derivatives h i (t / (2 * Real.pi))).2]
  fin_cases i <;> constructor
  all_goals first
    | (constructor <;> skip)
    | skip
  all_goals simp only [chartFeature, chartFeatureD, chartFeatureA, chartFeatureDD, featureLift,
    featureLiftD, featureLiftDD, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    chart_neg_val, chart_c3_val, chart_s3_val, PeriodicHolder_STR02968.val_smul, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, val_mul_STR02954,
    val_one_STR02954, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, e0_val_STR02955, cosC2_val_STR02915, sinC2_val_STR02915, hc, sg0, a0]
  all_goals change _ = _
  all_goals have hc3 : 6 * Real.pi * (t / (2 * Real.pi)) = 3 * t := by field_simp; ring
  all_goals try rw [hc3]
  all_goals field_simp [hh.ne', Real.pi_ne_zero]
  all_goals ring

/-- Fixed actual Holder feature, exposed for arbitrary-density feedback estimates. -/
def interactingHolderFeature (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 := chartFeature h i

/-- The physical coordinate derivative, retaining the angular factor 2*pi. -/
def interactingHolderDerivative (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 :=
  (2 * Real.pi) • chartFeatureD h i

/-- The actual reference-generator image, including its higher harmonics. -/
def interactingHolderGenerator (h : ℝ) (i : Fin 3) : PeriodicHolder_STR02968 := chartFeatureA h i

/-- Pointwise dictionary independent of any density chart or minimizer. -/
theorem interactingHolderFeature_native {h : ℝ} (hh : 0 < h) (i : Fin 3) (t : ℝ) :
    (interactingHolderFeature h i).val t =
        ![featureC h, featureS h, featureB h] i (angEquiv.symm (t : AngCircle)) ∧
      (interactingHolderDerivative h i).val t =
        coordPartial 0 (![featureC h, featureS h, featureB h] i)
          (angEquiv.symm (t : AngCircle)) ∧
      (interactingHolderGenerator h i).val t =
        elementaryFeatureGenerator h (![featureC h, featureS h, featureB h] i)
          (angEquiv.symm (t : AngCircle)) := by
  simpa only [interactingHolderFeature, interactingHolderDerivative, interactingHolderGenerator,
    PeriodicHolder_STR02968.val_smul, Pi.smul_apply, smul_eq_mul, nativeFeature] using
      chartFeature_dictionary hh i t

theorem interactingChartIntegral_native_ae (h : ℝ) (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))) =
      meanT_STR02901 (fun t => rhoT_STR02901 h u.val t * g (angEquiv.symm (t : AngCircle))) := by
  rw [Structural.budget_integral_densityMeasure]
  have hfun : (fun x => ρ.density x * g x) =ᵐ[haar 1]
      (fun θ : AngCircle => rhoT_STR02901 h u.val (angSec θ) * g (angEquiv.symm θ)) ∘ angEquiv := by
    have hh := (ae_comp_angEquiv_iff (p := fun θ : AngCircle =>
      ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))).mpr hρ
    filter_upwards [hh] with x hx
    simpa only [Function.comp_apply, angEquiv.symm_apply_apply] using congrArg (fun a => a * g x) hx
  rw [integral_congr_ae hfun]
  simp only [Function.comp_apply]
  rw [integral_comp_angEquiv
    (fun θ : AngCircle => rhoT_STR02901 h u.val (angSec θ) * g (angEquiv.symm θ))]
  have hsec : (fun θ : AngCircle => rhoT_STR02901 h u.val (angSec θ) * g (angEquiv.symm θ)) =
      fun θ => (fun t : ℝ => rhoT_STR02901 h u.val t * g (angEquiv.symm (t : AngCircle))) (angSec θ) := by
    funext θ
    change rhoT_STR02901 h u.val (angSec θ) * g (angEquiv.symm θ) =
      rhoT_STR02901 h u.val (angSec θ) * g (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
    rw [coe_angSec_STR02962]
  rw [hsec]
  exact integral_angSec_STR02962
    (fun t : ℝ => rhoT_STR02901 h u.val t * g (angEquiv.symm (t : AngCircle)))

private theorem chartMean_native {h : ℝ} {u : PeriodicC2_STR02969} {ρ : AbsoluteDensity 1}
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (f : PeriodicHolder_STR02968) (g : Torus 1 → ℝ)
    (hfg : ∀ t, f.val t = g (angEquiv.symm (t : AngCircle))) :
    chartMean h u f = ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) := by
  rw [interactingChartIntegral_native_ae h u ρ hρ g]
  unfold chartMean chartDensity
  rw [meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
  exact congrArg (rhoT_STR02901 h u.val t * ·) (hfg t)

private theorem chartKernel_dictionary {h : ℝ} (hh : 0 < h)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    (∀ t, (chartKernel h u).val t = elementaryKernelMean h (densityMeasure ρ)
      (angEquiv.symm (t : AngCircle))) ∧
    (∀ t, (chartKernelA h u).val t = elementaryAK h (densityMeasure ρ)
      (angEquiv.symm (t : AngCircle))) ∧
    (∀ t, (2 * Real.pi) * (chartKernelD h u).val t = elementaryKprime h (densityMeasure ρ)
      (angEquiv.symm (t : AngCircle))) := by
  have hm (i : Fin 3) : chartMean h u (chartFeature h i) =
      ∫ x, nativeFeature h i x ∂(densityMeasure ρ : Measure (Torus 1)) :=
    chartMean_native hρ _ _ fun t => (chartFeature_dictionary hh i t).1
  have hK (t : ℝ) : (chartKernel h u).val t =
      elementaryKernelMean h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
    unfold chartKernel
    rw [show (∑ i : Fin 3, (chartCoefficient i * chartMean h u (chartFeature h i)) • chartFeature h i) =
      (chartCoefficient 0 * chartMean h u (chartFeature h 0)) • chartFeature h 0 +
      (chartCoefficient 1 * chartMean h u (chartFeature h 1)) • chartFeature h 1 +
      (chartCoefficient 2 * chartMean h u (chartFeature h 2)) • chartFeature h 2 by
        simp [Fin.sum_univ_three]]
    simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm,
      (chartFeature_dictionary hh 0 t).1, (chartFeature_dictionary hh 1 t).1,
      (chartFeature_dictionary hh 2 t).1]
    dsimp only [chartCoefficient, nativeFeature, elementaryKernelMean, momC, momS, momB]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hAK (t : ℝ) : (chartKernelA h u).val t =
      elementaryAK h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
    rw [elementaryAK_moments]
    unfold chartKernelA
    simp only [Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm,
      (chartFeature_dictionary hh 0 t).2.2, (chartFeature_dictionary hh 1 t).2.2,
      (chartFeature_dictionary hh 2 t).2.2]
    dsimp only [chartCoefficient, nativeFeature, momC, momS, momB]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hKD (t : ℝ) : (2 * Real.pi) * (chartKernelD h u).val t =
      elementaryKprime h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
    rw [elementaryKprime_three_features]
    unfold chartKernelD
    simp only [Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm]
    have hd0 := (chartFeature_dictionary hh 0 t).2.1
    have hd1 := (chartFeature_dictionary hh 1 t).2.1
    have hd2 := (chartFeature_dictionary hh 2 t).2.1
    dsimp only [chartCoefficient, nativeFeature, momC, momS, momB] at *
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
    rw [← hd0, ← hd1, ← hd2]
    ring
  exact ⟨hK, hAK, hKD⟩

/-- The written nonlinear C/J chart corrections are exactly the actual physical
native corrections, on AE represented absolute H1 densities. -/
theorem interactingChartDeficit_native_corrections {h : ℝ} (hh : 0 < h)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (γ ε : ℝ) :
    a0 * (interactingChartDeficit h (ε, γ, u) - JC2_STR02956 h γ u) =
      ε * elementaryC h (a0 * (1 + γ)) ρ + ε ^ 2 * elementaryJ h ρ := by
  obtain ⟨hK, hAK, hKD⟩ := chartKernel_dictionary hh u ρ hρ
  have hQ := chartMean_native hρ (chartKernel h u) (elementaryKernelMean h (densityMeasure ρ)) hK
  have hA := chartMean_native hρ (chartKernelA h u) (elementaryAK h (densityMeasure ρ)) hAK
  have hJ : chartJ h u = elementaryJ h ρ := by
    have hd := chartMean_native hρ
      (a0 • (chartKernelD h u * chartKernelD h u))
      (fun x => (elementaryKprime h (densityMeasure ρ) x) ^ 2) (fun t => by
        simp only [PeriodicHolder_STR02968.val_smul, val_mul_STR02954, Pi.smul_apply,
          Pi.mul_apply, smul_eq_mul]
        rw [← hKD t]
        unfold a0
        ring)
    have hlinear : chartMean h u (a0 • (chartKernelD h u * chartKernelD h u)) =
        a0 * chartMean h u (chartKernelD h u * chartKernelD h u) := by
      unfold chartMean
      rw [mul_smul_comm, map_smul]
      rfl
    unfold chartJ
    rw [← hlinear, hd, Structural.budget_integral_densityMeasure]
    rfl
  have hC : chartC h γ u = elementaryC h (a0 * (1 + γ)) ρ := by
    unfold chartC elementaryC elementaryQ
    rw [hA, hQ, Structural.budget_integral_densityMeasure]
  unfold interactingChartDeficit
  rw [hC, hJ]
  have ha : a0 ≠ 0 := by unfold a0; positivity
  field_simp [ha]
  ring

/-- Pointwise identification of the written gradient with the actual physical
nonlocal Euler feedback fields. The original density needs only an AE chart. -/
theorem interactingChartGradient_native {h : ℝ} (hh : 0 < h)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (γ ε t : ℝ) :
    (interactingChartGradient h (ε, γ, u)).val t = gradG_STR02950 h γ u.val t +
      (2 * ε / a0) * rhoT_STR02901 h u.val t *
        (elementaryAK h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) +
          elementaryGeneratorFeedback h ρ (angEquiv.symm (t : AngCircle)) -
          (a0 * (1 + γ)) * elementaryKernelMean h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) -
          elementaryC h (a0 * (1 + γ)) ρ) +
      (ε ^ 2 / a0) * rhoT_STR02901 h u.val t *
        ((elementaryKprime h (densityMeasure ρ) (angEquiv.symm (t : AngCircle))) ^ 2 +
          2 * elementaryForceFeedback h ρ (angEquiv.symm (t : AngCircle)) - 3 * elementaryJ h ρ) := by
  obtain ⟨hK, hAK, hKD⟩ := chartKernel_dictionary hh u ρ hρ
  have hmA (i : Fin 3) : chartMean h u (chartFeatureA h i) =
      ∫ x, elementaryFeatureGenerator h (nativeFeature h i) x
        ∂(densityMeasure ρ : Measure (Torus 1)) :=
    chartMean_native hρ _ _ fun s => (chartFeature_dictionary hh i s).2.2
  have hLA (s : ℝ) : (chartGeneratorFeedback h u).val s =
      elementaryGeneratorFeedback h ρ (angEquiv.symm (s : AngCircle)) := by
    unfold chartGeneratorFeedback
    simp only [Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hmA,
      (chartFeature_dictionary hh 0 s).1, (chartFeature_dictionary hh 1 s).1,
      (chartFeature_dictionary hh 2 s).1]
    dsimp only [chartCoefficient, nativeFeature, elementaryGeneratorFeedback]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hmD (i : Fin 3) : a0 * chartMean h u (chartKernelD h u * chartFeatureD h i) =
      ∫ x, elementaryKprime h (densityMeasure ρ) x * coordPartial 0 (nativeFeature h i) x
        ∂(densityMeasure ρ : Measure (Torus 1)) := by
    have hd := chartMean_native hρ (a0 • (chartKernelD h u * chartFeatureD h i))
      (fun x => elementaryKprime h (densityMeasure ρ) x * coordPartial 0 (nativeFeature h i) x)
      (fun s => by
        simp only [PeriodicHolder_STR02968.val_smul, val_mul_STR02954, Pi.smul_apply,
          Pi.mul_apply, smul_eq_mul]
        rw [← hKD s, ← (chartFeature_dictionary hh i s).2.1]
        unfold a0
        ring)
    unfold chartMean at *
    rw [mul_smul_comm, map_smul] at hd
    simpa only [smul_eq_mul] using hd
  have hLP (s : ℝ) : a0 * (chartForceFeedback h u).val s =
      elementaryForceFeedback h ρ (angEquiv.symm (s : AngCircle)) := by
    unfold chartForceFeedback
    simp only [Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      (chartFeature_dictionary hh 0 s).1, (chartFeature_dictionary hh 1 s).1,
      (chartFeature_dictionary hh 2 s).1]
    have hm0 := hmD 0
    have hm1 := hmD 1
    have hm2 := hmD 2
    unfold elementaryForceFeedback chartCoefficient
    dsimp only [nativeFeature] at hm0 hm1 hm2 ⊢
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hm0 hm1 hm2 ⊢
    rw [← hm0, ← hm1, ← hm2]
    ring
  have hFC (s : ℝ) : (chartCFeedback h γ u).val s =
      elementaryAK h (densityMeasure ρ) (angEquiv.symm (s : AngCircle)) +
        elementaryGeneratorFeedback h ρ (angEquiv.symm (s : AngCircle)) -
        (a0 * (1 + γ)) * elementaryKernelMean h (densityMeasure ρ) (angEquiv.symm (s : AngCircle)) := by
    unfold chartCFeedback
    simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hK, hAK, hLA]
  have hFJ (s : ℝ) : (chartJFeedback h u).val s =
      (elementaryKprime h (densityMeasure ρ) (angEquiv.symm (s : AngCircle))) ^ 2 +
        2 * elementaryForceFeedback h ρ (angEquiv.symm (s : AngCircle)) := by
    unfold chartJFeedback
    simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [← hKD s, ← hLP s]
    unfold a0
    ring
  have hmC : chartMean h u (chartCFeedback h γ u) = elementaryC h (a0 * (1 + γ)) ρ :=
    (chartMean_native hρ _ _ hFC).trans (elementaryC_feedback_mean h (a0 * (1 + γ)) ρ)
  have hmJ : chartMean h u (chartJFeedback h u) = 3 * elementaryJ h ρ :=
    (chartMean_native hρ _ _ hFJ).trans (elementaryJ_feedback_mean h ρ)
  unfold interactingChartGradient chartCenter chartDensity
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Gfun_val_STR02955, rho_val_STR02954, e0_val_STR02955, hmC, hmJ, hFC, hFJ]
  ring

/-- The complete written feedback gradient has zero Haar mean, by actual density
normalization and centering of both nonlinear force feedbacks. -/
theorem interactingChartGradient_mean_zero (h γ ε : ℝ) (u : PeriodicC2_STR02969) :
    meanCLM_STR02954 (interactingChartGradient h (ε, γ, u)) = 0 := by
  have hρ : meanCLM_STR02954 (chartDensity h u) = 1 := by
    rw [meanCLM_apply_STR02954]
    have hv : (chartDensity h u).val = rhoT_STR02901 h u.val := by
      funext t
      exact rho_val_STR02954 (h, e0_STR02955 u) t
    rw [hv]
    exact meanT_rho_STR02950 h u.isC2.2.1.continuous
  have hcenter (f : PeriodicHolder_STR02968) : meanCLM_STR02954 (chartCenter h u f) = 0 := by
    unfold chartCenter chartMean
    rw [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, hρ]
    simp only [smul_eq_mul, mul_one, sub_self]
  have hG : meanCLM_STR02954 (Gfun_STR02955 h γ u) = 0 := by
    rw [meanCLM_apply_STR02954, Gfun_val_STR02955]
    exact str029_50_integrate_variation_compute_mean_mean_zero h γ u.isC2
  unfold interactingChartGradient
  rw [map_add, map_add, map_smul, map_smul, hG, hcenter, hcenter]
  simp

/-- The actual projected range and the two first-harmonic rows determine the
full written gradient, since its mean vanishes. No stationarity is assumed. -/
theorem interactingChartGradient_zero_of_projected (h γ ε : ℝ) (u : PeriodicC2_STR02969)
    (hR : PY_STR02955 (interactingChartGradient h (ε, γ, u)) = 0)
    (hC : meanCLM_STR02954
      (interactingChartGradient h (ε, γ, u) * e0_STR02955 cosC2_STR02915) = 0)
    (hS : meanCLM_STR02954
      (interactingChartGradient h (ε, γ, u) * e0_STR02955 sinC2_STR02915) = 0) :
    interactingChartGradient h (ε, γ, u) = 0 := by
  let G := interactingChartGradient h (ε, γ, u)
  have hm : meanT_STR02901 G.val = 0 := interactingChartGradient_mean_zero h γ ε u
  have hc : pair_STR02953 Real.cos G.val = 0 := by
    calc
      _ = meanCLM_STR02954 (G * e0_STR02955 cosC2_STR02915) := by
        rw [meanCLM_apply_STR02954]
        unfold pair_STR02953
        congr 1
      _ = 0 := hC
  have hs : pair_STR02953 Real.sin G.val = 0 := by
    calc
      _ = meanCLM_STR02954 (G * e0_STR02955 sinC2_STR02915) := by
        rw [meanCLM_apply_STR02954]
        unfold pair_STR02953
        congr 1
      _ = 0 := hS
  apply ext_STR02954
  funext t
  change G.val t = 0
  have he := congrArg (fun y : Y_STR02969 => (y : PeriodicHolder_STR02968).val t) hR
  change projP_STR02953 G.val t = 0 at he
  unfold projP_STR02953 at he
  rw [hm, hc, hs] at he
  simpa only [zero_mul, mul_zero, sub_zero] using he

end DGPS.Examples.ThreeSpeciesCircle
