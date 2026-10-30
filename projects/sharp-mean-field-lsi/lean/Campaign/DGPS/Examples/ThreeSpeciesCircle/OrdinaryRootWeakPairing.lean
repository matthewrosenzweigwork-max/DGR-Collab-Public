import DGPS.Frontier.STR029.T26s1
import DGPS.Frontier.STR029.T26s2
import DGPS.Basic.ParabolicChainRule
import DGPS.Lipschitz.WeightedGenerator

/-! Genuine weak integration by parts against C1 periodic coefficients. This transfers the
full periodic weak-H1 domain to the existing Haar-H1 pairing theorem and back, with both
physical derivative factors 2*pi cancelled. No pointwise weak-gradient equality is asserted. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Lipschitz.ParabolicChainRule

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem c1_comp_angEquiv (ψ : AngCircle → ℝ)
    (hψ : ContDiff ℝ 1 (fun t : ℝ => ψ (t : AngCircle))) :
    IsC1Periodic (ψ ∘ angEquiv) := by
  unfold IsC1Periodic
  have he : ((ψ ∘ angEquiv) ∘ torusLift : (Fin 1 → ℝ) → ℝ) =
      (fun t : ℝ => ψ (t : AngCircle)) ∘ (fun y : Fin 1 → ℝ => 2 * π * y 0) := by
    funext y
    exact comp_angEquiv_liftT ψ y
  rw [he]
  exact hψ.comp (by fun_prop)

private theorem c1_coordPartial_comp_angEquiv {ψ : AngCircle → ℝ}
    (hψ : ContDiff ℝ 1 (fun t : ℝ => ψ (t : AngCircle))) (x : Torus 1) :
    coordPartial 0 (ψ ∘ angEquiv) x = 2 * π * angDeriv ψ (angEquiv x) := by
  have h1 : ((ψ ∘ angEquiv) ∘ torusLift : (Fin 1 → ℝ) → ℝ) =
      (fun t : ℝ => ψ (t : AngCircle)) ∘ (fun y : Fin 1 → ℝ => 2 * π * y 0) := by
    funext y
    exact comp_angEquiv_liftT ψ y
  unfold coordPartial angDeriv
  rw [h1, angSec_angEquiv]
  have hd : DifferentiableAt ℝ (fun t : ℝ => ψ (t : AngCircle))
      (2 * π * SharpLSI.secT x 0) :=
    (hψ.differentiable (by norm_num)).differentiableAt
  have hL : HasFDerivAt (fun y : Fin 1 → ℝ => 2 * π * y 0)
      ((2 * π) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ))
      (SharpLSI.secT x) := by
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
      (x := SharpLSI.secT x)).const_mul (2 * π)
    simpa using h
  rw [(hd.hasDerivAt.comp_hasFDerivAt (SharpLSI.secT x) hL).fderiv]
  simp
  ring

/-- The original periodic weak derivative pairs with every C1 periodic coefficient.
Both integrals are genuine finite L2 pairings on the normalized angular period. -/
theorem ordinaryRoot_periodicWeak_ibp_c1 (w g c : ℝ → ℝ)
    (hw : IsPeriodicWeakDerivative_STR02933 w g)
    (hper : Function.Periodic c (2 * π)) (hc : ContDiff ℝ 1 c) :
    normInt_STR02933 (fun t => w t * deriv c t) =
      -normInt_STR02933 (fun t => g t * c t) := by
  let ψ : AngCircle → ℝ := hper.lift
  have hlift : (fun t : ℝ => ψ (t : AngCircle)) = c :=
    funext fun t => hper.lift_coe t
  have hψ : ContDiff ℝ 1 (fun t : ℝ => ψ (t : AngCircle)) := by
    rw [hlift]
    exact hc
  have hψeq : ∀ θ : AngCircle, ψ θ = c (angSec θ) := by
    intro θ
    calc
      ψ θ = ψ ((angSec θ : ℝ) : AngCircle) := by rw [coe_angSec_STR02962]
      _ = c (angSec θ) := hper.lift_coe _
  have hderiv : ∀ θ : AngCircle, angDeriv ψ θ = deriv c (angSec θ) := by
    intro θ
    unfold angDeriv
    rw [hlift]
  have hu := (isWeakGradient_comp_iff (fun θ => w (angSec θ))
    (fun θ => g (angSec θ))).1 (periodicWD_to_angularWD_STR02926 hw)
  have hy := (c1_comp_angEquiv ψ hψ).isWeakGradient
  have hIBP := DGPS.Lipschitz.WeightedGenerator.ibp_H1 hu hy (0 : Fin 1)
  have hleft : (∫ x, ((fun θ => w (angSec θ)) ∘ angEquiv) x *
      smoothGrad (ψ ∘ angEquiv) x 0 ∂haar 1) =
      (2 * π) * normInt_STR02933 (fun t => w t * deriv c t) := by
    have he : (fun x : Torus 1 => ((fun θ => w (angSec θ)) ∘ angEquiv) x *
        smoothGrad (ψ ∘ angEquiv) x 0) = fun x =>
        (2 * π) * (fun θ => w (angSec θ) * deriv c (angSec θ)) (angEquiv x) := by
      funext x
      change w (angSec (angEquiv x)) * coordPartial 0 (ψ ∘ angEquiv) x = _
      rw [c1_coordPartial_comp_angEquiv hψ, hderiv]
      ring
    rw [he, integral_const_mul,
      integral_comp_angEquiv (fun θ => w (angSec θ) * deriv c (angSec θ)),
      integral_angSec_STR02962 (fun t => w t * deriv c t),
      normInt_eq_meanT_STR02962]
    rfl
  have hright : (∫ x, physGrad (fun θ => g (angSec θ)) x 0 *
      (ψ ∘ angEquiv) x ∂haar 1) =
      (2 * π) * normInt_STR02933 (fun t => g t * c t) := by
    rw [integral_physGrad_mul]
    simp_rw [hψeq]
    rw [integral_angSec_STR02962 (fun t => g t * c t), normInt_eq_meanT_STR02962]
    rfl
  rw [hleft, hright] at hIBP
  apply mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0)
  simpa only [mul_neg] using hIBP


/-- A classical C1 periodic function supplies its genuine full periodic weak derivative. -/
theorem ordinaryRoot_periodicWeak_of_c1 (c : ℝ → ℝ)
    (hper : Function.Periodic c (2 * π)) (hc : ContDiff ℝ 1 c) :
    IsPeriodicWeakDerivative_STR02933 c (deriv c) := by
  let ψ : AngCircle → ℝ := hper.lift
  have hlift : (fun t : ℝ => ψ (t : AngCircle)) = c :=
    funext fun t => hper.lift_coe t
  have hψ : ContDiff ℝ 1 (fun t : ℝ => ψ (t : AngCircle)) := by
    rw [hlift]
    exact hc
  have hgrad : smoothGrad (ψ ∘ angEquiv) = physGrad (angDeriv ψ) := by
    funext x
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    change coordPartial 0 (ψ ∘ angEquiv) x = physGrad (angDeriv ψ) x 0
    rw [physGrad_apply, c1_coordPartial_comp_angEquiv hψ]
  have hy : IsWeakGradient (ψ ∘ angEquiv) (physGrad (angDeriv ψ)) := by
    rw [← hgrad]
    exact (c1_comp_angEquiv ψ hψ).isWeakGradient
  have ha := (isWeakGradient_comp_iff ψ (angDeriv ψ)).2 hy
  have hp := angularWD_to_periodicWD_STR02926 ha
  have hderfun : (fun t : ℝ => angDeriv ψ (t : AngCircle)) = deriv c := by
    funext t
    unfold angDeriv
    rw [hlift]
    have hdper := periodic_deriv_STR02901 hper
    calc
      deriv c (angSec (t : AngCircle)) =
          hdper.lift (((angSec (t : AngCircle)) : ℝ) : AngCircle) :=
        (hdper.lift_coe _).symm
      _ = hdper.lift (t : AngCircle) := by rw [coe_angSec_STR02962]
      _ = deriv c t := hdper.lift_coe t
  simpa only [hlift, hderfun] using hp


/-- A zero projected gradient pairs to zero with every genuine L2 complement test.
No continuous representative of the test is required. -/
theorem ordinaryRoot_complement_projection_pairing_zero (G w : ℝ → ℝ)
    (hw : MemLp w 2 (volume.restrict (Ioc 0 (2 * π))))
    (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0)
    (hP : ∀ t, projP_STR02953 G t = 0) :
    normInt_STR02933 (fun t => G t * w t) = 0 := by
  have hi := integrable_of_memLp_STR02934 hw
  have hic : Integrable (fun t => w t * Real.cos t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [one_mul] using integrable_mul_cos_STR02934 hi 1
  have his : Integrable (fun t => w t * Real.sin t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [one_mul] using integrable_mul_sin_STR02934 hi 1
  have he : (fun t => G t * w t) = fun t =>
      meanT_STR02901 G * w t + (2 * pair_STR02953 Real.cos G) * (w t * Real.cos t) +
        (2 * pair_STR02953 Real.sin G) * (w t * Real.sin t) := by
    funext t
    have h := hP t
    simp only [projP_STR02953] at h
    linear_combination (w t) * h
  rw [he]
  unfold normInt_STR02933 at h0 hc hs ⊢
  rw [integral_add
      (f := fun t => meanT_STR02901 G * w t +
        (2 * pair_STR02953 Real.cos G) * (w t * Real.cos t))
      (g := fun t => (2 * pair_STR02953 Real.sin G) * (w t * Real.sin t))
      ((hi.const_mul _).add (hic.const_mul _)) (his.const_mul _),
    integral_add (f := fun t => meanT_STR02901 G * w t)
      (g := fun t => (2 * pair_STR02953 Real.cos G) * (w t * Real.cos t))
      (hi.const_mul _) (hic.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  linear_combination (meanT_STR02901 G) * h0 +
    (2 * pair_STR02953 Real.cos G) * hc + (2 * pair_STR02953 Real.sin G) * hs

end DGPS.Examples.ThreeSpeciesCircle
