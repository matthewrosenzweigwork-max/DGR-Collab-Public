import FullLabeledLSI.Nonvacuity.Prop82.Assembly
import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# Lane D: bridge between `Torus 1` and 1-periodic functions on `ℝ`

For a smooth positive probability density `ρ` on the circle, `pf ρ := ρ ∘ lineT` is a smooth,
positive, 1-periodic function on `ℝ`; Fisher information, entropy and the half-turn average are
expressed through interval integrals of `pf ρ`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

/-- The 1-periodic function on `ℝ` attached to a function on the circle. -/
noncomputable def pf (rho : Torus 1 → Real) (t : Real) : Real := rho (lineT t)

theorem lineT_eq (t : Real) : lineT t = liftT (lineF t) := rfl

theorem contDiff_lineF : ContDiff ℝ ∞ lineF :=
  contDiff_pi.2 fun _ => contDiff_id

theorem pf_eq_comp (rho : Torus 1 → Real) : pf rho = (rho ∘ liftT) ∘ lineF := rfl

theorem pf_smooth {rho : Torus 1 → Real} (h : IsSmoothT rho) : ContDiff ℝ ∞ (pf rho) :=
  h.comp contDiff_lineF

theorem pf_periodic (rho : Torus 1 → Real) (t : Real) : pf rho (t + 1) = pf rho t := by
  have := lineT_add_int t 1
  simp only [Int.cast_one] at this
  unfold pf
  rw [this]

theorem pf_pos {rho : Torus 1 → Real} (h : ∀ x, 0 < rho x) (t : Real) : 0 < pf rho t := h _

theorem pf_continuous {rho : Torus 1 → Real} (h : IsSmoothT rho) : Continuous (pf rho) :=
  (pf_smooth h).continuous

theorem hasDerivAt_lineF (t : Real) : HasDerivAt lineF (fun _ : Fin 1 => (1 : Real)) t := by
  rw [hasDerivAt_pi]
  intro i
  exact hasDerivAt_id t

theorem deriv_pf {rho : Torus 1 → Real} (h : IsSmoothT rho) (t : Real) :
    deriv (pf rho) t = dpart rho 0 (lineT t) := by
  rw [lineT_eq, dpart_liftT]
  have hd : DifferentiableAt ℝ (rho ∘ liftT) (lineF t) :=
    (h.differentiable (by simp)) _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lineF t)
  rw [pf_eq_comp, h1.deriv]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  simp

/-- Torus integrals of continuous functions are interval integrals along `lineT`. -/
theorem integral_torus_eq {g : Torus 1 → Real} (hg : Continuous g) :
    ∫ y, g y ∂haar 1 = ∫ t in (0 : Real)..1, g (lineT t) :=
  (intervalIntegral_lineT hg.aestronglyMeasurable).symm

theorem lineT_add_half (t : Real) : lineT (t + 1 / 2) = lineT t + halfTurn := by
  funext i
  simp only [lineT, liftT, lineF, Pi.add_apply, halfTurn]
  exact AddCircle.coe_add (p := (1 : Real)) t (1 / 2)

theorem pf_halfSymmetrize (rho : Torus 1 → Real) (t : Real) :
    pf (halfSymmetrize rho) t = (pf rho t + pf rho (t + 1 / 2)) / 2 := by
  unfold pf halfSymmetrize
  rw [lineT_add_half]

theorem halfSymmetrize_smooth {rho : Torus 1 → Real} (h : IsSmoothT rho) :
    IsSmoothT (halfSymmetrize rho) := by
  have hshift : ContDiff ℝ ∞ (fun z : Fin 1 → Real => z + fun _ => (1 / 2 : Real)) :=
    contDiff_id.add contDiff_const
  have h2 : ContDiff ℝ ∞ ((rho ∘ liftT) ∘ fun z : Fin 1 → Real => z + fun _ => (1 / 2 : Real)) :=
    h.comp hshift
  have : (halfSymmetrize rho ∘ liftT) =
      fun z => ((rho ∘ liftT) z + ((rho ∘ liftT) ∘
        fun z : Fin 1 → Real => z + fun _ => (1 / 2 : Real)) z) / 2 := by
    funext z
    simp only [Function.comp, halfSymmetrize]
    congr 3
  unfold IsSmoothT
  rw [this]
  exact (h.add h2).div_const 2

end SharpLSI.FL.Prop82
