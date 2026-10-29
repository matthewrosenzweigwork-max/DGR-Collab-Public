import FullLabeledLSI.Examples.E01g1_Smooth
import SharpSymmetricLSI.Infra.SmoothWeakGrad
import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# Lane D, Task C (E01g1): weak gradient of a smooth function is `dT`
-/

open MeasureTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem fderiv_single_eq_deriv {h : Torus 1 → ℝ} (hh : IsSmoothT h) (t : ℝ) :
    fderiv ℝ (h ∘ liftT) (fun _ : Fin 1 => t) (Pi.single 0 1) = deriv (fun s => h (lift1 s)) t := by
  have hd : Differentiable ℝ (h ∘ liftT) := hh.differentiable (by simp)
  have hc : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (Pi.single 0 1 : Fin 1 → ℝ) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    simpa using hasDerivAt_id' t
  have := (hd (fun _ => t)).hasFDerivAt.comp_hasDerivAt t hc
  exact this.deriv.symm

theorem weakGrad_ae_dT {h : Torus 1 → ℝ} (hh : IsSmoothT h) :
    (fun x => weakGrad h x 0) =ᵐ[haar 1] dT h := by
  have h1 : ContDiff ℝ 1 (h ∘ liftT) := hh.of_le (by exact_mod_cast le_top)
  filter_upwards [weakGrad_ae_eq_of_contDiff h1] with x hx
  have := congrFun hx 0
  rw [this]
  have hx' : secT x = fun _ : Fin 1 => secT x 0 := by funext i; fin_cases i; rfl
  rw [hx', fderiv_single_eq_deriv hh]
  have : x = lift1 (secT x 0) := by
    have := liftT_secT x
    rw [liftT_eq_lift1] at this
    exact this.symm
  conv_rhs => rw [this]
  rw [dT_lift1]

theorem hasWeakGrad_of_smooth {h : Torus 1 → ℝ} (hh : IsSmoothT h) : HasWeakGrad h :=
  ⟨_, isWeakGrad_of_contDiff (hh.of_le (by exact_mod_cast le_top))⟩

theorem dT_const_sub (a : ℝ) (h : Torus 1 → ℝ) (x : Torus 1) :
    dT (fun y => a - h y) x = - dT h x := by
  rw [dT_apply, dT_apply]
  simp only [deriv_const_sub]

end SharpLSI.FL.Ex.LaneD
