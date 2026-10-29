import FullLabeledLSI.Nonvacuity.Prop82.Score
import FullLabeledLSI.Paper.Sec8Smooth

/-!
# Lane E, part 1: classical calculus on the circle

Product rule, linearity and integration by parts for the classical derivative
`dpart u 0` of smooth functions on `Torus 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82.HeatE

open SharpLSI

variable {u v : Torus 1 → Real}

/-! ### Smoothness -/

theorem smooth_add (hu : IsSmoothT u) (hv : IsSmoothT v) : IsSmoothT (fun x => u x + v x) :=
  ContDiff.add hu hv

theorem smooth_sub (hu : IsSmoothT u) (hv : IsSmoothT v) : IsSmoothT (fun x => u x - v x) :=
  ContDiff.sub hu hv

theorem smooth_mul (hu : IsSmoothT u) (hv : IsSmoothT v) : IsSmoothT (fun x => u x * v x) :=
  ContDiff.mul hu hv

theorem smooth_const (c : Real) : IsSmoothT (fun _ : Torus 1 => c) := contDiff_const

theorem smooth_const_mul (c : Real) (hu : IsSmoothT u) : IsSmoothT (fun x => c * u x) :=
  ContDiff.mul contDiff_const hu

theorem smooth_neg (hu : IsSmoothT u) : IsSmoothT (fun x => -u x) := ContDiff.neg hu

theorem smooth_pow (hu : IsSmoothT u) (n : Nat) : IsSmoothT (fun x => u x ^ n) :=
  ContDiff.pow hu n

theorem smooth_dpart (hu : IsSmoothT u) : IsSmoothT (dpart u 0) :=
  Sec8.isSmoothT_dpart hu 0

theorem smooth_dpart2 (hu : IsSmoothT u) : IsSmoothT (dpart (dpart u 0) 0) :=
  smooth_dpart (smooth_dpart hu)

theorem smooth_dpart3 (hu : IsSmoothT u) : IsSmoothT (dpart (dpart (dpart u 0) 0) 0) :=
  smooth_dpart (smooth_dpart2 hu)

theorem smooth_continuous (hu : IsSmoothT u) : Continuous u := Sec8.continuous_of_smooth hu

theorem smooth_integrable (hu : IsSmoothT u) : Integrable u (haar 1) :=
  Sec8.integrable_of_smooth hu

theorem smooth_c1 (hu : IsSmoothT u) : ContDiff Real 1 (u ∘ liftT) :=
  ContDiff.of_le hu (by exact_mod_cast le_top)

theorem differentiableAt_lift (hu : IsSmoothT u) (z : Fin 1 → Real) :
    DifferentiableAt Real (u ∘ liftT) z :=
  (smooth_c1 hu).differentiable one_ne_zero z

/-! ### Differentiation rules -/

theorem dpart_add' (hu : IsSmoothT u) (hv : IsSmoothT v) (x : Torus 1) :
    dpart (fun y => u y + v y) 0 x = dpart u 0 x + dpart v 0 x := by
  unfold dpart
  have e : ((fun y => u y + v y) ∘ liftT) = fun z => (u ∘ liftT) z + (v ∘ liftT) z := rfl
  rw [e, fderiv_fun_add (differentiableAt_lift hu _) (differentiableAt_lift hv _)]
  rfl

theorem dpart_sub' (hu : IsSmoothT u) (hv : IsSmoothT v) (x : Torus 1) :
    dpart (fun y => u y - v y) 0 x = dpart u 0 x - dpart v 0 x := by
  unfold dpart
  have e : ((fun y => u y - v y) ∘ liftT) = fun z => (u ∘ liftT) z - (v ∘ liftT) z := rfl
  rw [e, fderiv_fun_sub (differentiableAt_lift hu _) (differentiableAt_lift hv _)]
  rfl

theorem dpart_const_mul' (c : Real) (hu : IsSmoothT u) (x : Torus 1) :
    dpart (fun y => c * u y) 0 x = c * dpart u 0 x := by
  unfold dpart
  have e : ((fun y => c * u y) ∘ liftT) = fun z => c * (u ∘ liftT) z := rfl
  rw [e, fderiv_const_mul (differentiableAt_lift hu _)]
  simp

theorem dpart_neg' (hu : IsSmoothT u) (x : Torus 1) :
    dpart (fun y => -u y) 0 x = -dpart u 0 x := by
  have := dpart_const_mul' (-1) hu x
  simpa using this

theorem dpart_mul' (hu : IsSmoothT u) (hv : IsSmoothT v) (x : Torus 1) :
    dpart (fun y => u y * v y) 0 x = dpart u 0 x * v x + u x * dpart v 0 x := by
  unfold dpart
  have e : ((fun y => u y * v y) ∘ liftT) = fun z => (u ∘ liftT) z * (v ∘ liftT) z := rfl
  rw [e, fderiv_fun_mul (differentiableAt_lift hu _) (differentiableAt_lift hv _)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    Function.comp_apply, liftT_secT]
  ring

theorem dpart_const (c : Real) (x : Torus 1) : dpart (fun _ : Torus 1 => c) 0 x = 0 := by
  unfold dpart
  have e : ((fun _ : Torus 1 => c) ∘ liftT) = fun _ => c := rfl
  rw [e]
  simp

theorem dpart_sq (hu : IsSmoothT u) (x : Torus 1) :
    dpart (fun y => u y ^ 2) 0 x = 2 * u x * dpart u 0 x := by
  have := dpart_mul' hu hu x
  have e : (fun y => u y ^ 2) = fun y => u y * u y := funext fun y => sq (u y)
  rw [e, this]; ring

/-- Derivative of the cube, used for the Fisher identity. -/
theorem dpart_cube (hu : IsSmoothT u) (x : Torus 1) :
    dpart (fun y => u y ^ 3) 0 x = 3 * u x ^ 2 * dpart u 0 x := by
  have h1 : (fun y => u y ^ 3) = fun y => u y * (u y * u y) := by funext y; ring
  rw [h1, dpart_mul' hu (smooth_mul hu hu), dpart_mul' hu hu]
  ring

/-! ### Integration by parts -/

theorem integral_dpart (hu : IsSmoothT u) : ∫ x, dpart u 0 x ∂haar 1 = 0 :=
  integral_dpart_eq_zero (smooth_c1 hu) 0

theorem integral_mul_dpart (hu : IsSmoothT u) (hv : IsSmoothT v) :
    ∫ x, u x * dpart v 0 x ∂haar 1 = -∫ x, dpart u 0 x * v x ∂haar 1 := by
  have h0 := integral_dpart (smooth_mul hu hv)
  have hi1 : Integrable (fun x => dpart u 0 x * v x) (haar 1) :=
    smooth_integrable (smooth_mul (smooth_dpart hu) hv)
  have hi2 : Integrable (fun x => u x * dpart v 0 x) (haar 1) :=
    smooth_integrable (smooth_mul hu (smooth_dpart hv))
  have e : (fun x => dpart (fun y => u y * v y) 0 x) =
      fun x => dpart u 0 x * v x + u x * dpart v 0 x := funext (dpart_mul' hu hv)
  rw [e, integral_add hi1 hi2] at h0
  linarith

theorem integral_dpart_mul (hu : IsSmoothT u) (hv : IsSmoothT v) :
    ∫ x, dpart u 0 x * v x ∂haar 1 = -∫ x, u x * dpart v 0 x ∂haar 1 := by
  rw [integral_mul_dpart hu hv]; ring

theorem integral_mul_dpart2 (hu : IsSmoothT u) (hv : IsSmoothT v) :
    ∫ x, u x * dpart (dpart v 0) 0 x ∂haar 1 = ∫ x, dpart (dpart u 0) 0 x * v x ∂haar 1 := by
  rw [integral_mul_dpart hu (smooth_dpart hv), integral_mul_dpart (smooth_dpart hu) hv]
  ring

theorem integral_dpart_dpart (hu : IsSmoothT u) :
    ∫ x, dpart (dpart u 0) 0 x ∂haar 1 = 0 :=
  integral_dpart (smooth_dpart hu)

theorem integral_dpart_zero (hu : IsSmoothT u) : ∫ x, dpart u 0 x ∂haar 1 = 0 :=
  integral_dpart hu

theorem integral_dpart2_zero (hu : IsSmoothT u) :
    ∫ x, dpart (dpart u 0) 0 x ∂haar 1 = 0 :=
  integral_dpart_dpart hu

end SharpLSI.FL.Prop82.HeatE
