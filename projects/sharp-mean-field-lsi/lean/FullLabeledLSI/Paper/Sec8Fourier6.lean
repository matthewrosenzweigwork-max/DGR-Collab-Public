import FullLabeledLSI.Paper.Sec8Fourier5
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.AppAStab2
import SharpSymmetricLSI.Paper.GroundState
import SharpSymmetricLSI.Paper.CosineDissipation

/-!
# Section 8.5 (Corollary 8.4), part 6: the dissipation of a density against `W = G(x-y) - G(0)`

For `u = √ρ ∈ H¹` and `b = ∇(W*ρ)`: `D(ρ) = ∫ |2∇u + u b|² ≥ 4∫|∇u|² - 2 ∬ ΔG(x-y) ρ(x)ρ(y)`.
The cross term is `2 ∫ ∇ρ · b` and the integration by parts is done for each fixed `y` against the
smooth periodic function `x ↦ ∂_k G(x-y)`, followed by Fubini.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem secT_sub_eq (x y : Torus d) :
    ∃ m : Fin d → ℤ, secT (x - y) = secT x - secT y + intVec m := by
  obtain ⟨m, hm⟩ := secT_liftT_eq (secT x - secT y)
  refine ⟨m, ?_⟩
  have : liftT (secT x - secT y) = x - y := by rw [liftT_sub, liftT_secT, liftT_secT]
  rw [this] at hm; exact hm

theorem dpart_sub_eq (u : Torus d → ℝ) (k : Fin d) (x y : Torus d) :
    dpart u k (x - y) = SharpLSI.Dk (u ∘ liftT) k (secT x - secT y) := by
  obtain ⟨m, hm⟩ := secT_sub_eq x y
  unfold dpart SharpLSI.Dk
  rw [hm, fderiv_lift_periodic u m]

theorem bGrad_WG {G : Torus d → ℝ} (hG : IsSmoothT G) (x y : Torus d) (k : Fin d) :
    bGrad (WG G) x y k = dpart G k (x - y) := by
  rw [← lipGrad_slice y x k, dpart_sub_eq G k x y]
  unfold lipGrad
  set c := secT y with hc
  have hGl : Differentiable ℝ (G ∘ liftT) := hG.differentiable (by simp)
  have e : ((fun x => WG G x y) ∘ liftT) = fun z => (G ∘ liftT) (z - c) - G 0 := by
    funext z
    simp only [Function.comp, WG, hc, liftT_sub, liftT_secT]
  rw [e]
  have h : HasFDerivAt (fun z => (G ∘ liftT) (z - c) - G 0)
      (fderiv ℝ (G ∘ liftT) (secT x - c)) (secT x) := by
    have := ((hGl (secT x - c)).hasFDerivAt.comp (secT x) ((hasFDerivAt_id (secT x)).sub_const c))
    exact (this.sub_const (G 0)).congr_fderiv (by simp)
  rw [(h.hasLineDerivAt _).lineDeriv]
  rfl

/-- Integration by parts against `x ↦ ∂_k G(x - y)`. -/
theorem ibp_shift {G : Torus d → ℝ} (hG : IsSmoothT G) {f : Torus d → ℝ}
    {g : Torus d → Fin d → ℝ} (h : IsWeakGrad f g) (hf : Integrable f volume)
    (hg : ∀ k, Integrable (fun y => g y k) volume) (y : Torus d) (k : Fin d) :
    ∫ x, f x * dpart (dpart G k) k (x - y) = -∫ x, g x k * dpart G k (x - y) := by
  set Θ : (Fin d → ℝ) → ℝ := fun z => SharpLSI.Dk (G ∘ liftT) k (z - secT y) with hΘdef
  have hGs : ContDiff ℝ ∞ (G ∘ liftT) := hG
  have hΘ : ContDiff ℝ ∞ Θ := (contDiff_Dk hGs k).comp (contDiff_id.sub contDiff_const)
  have hp : IsPer Θ := fun m z => by
    simp only [hΘdef]
    rw [show z + intVec m - secT y = (z - secT y) + intVec m by abel]
    exact (isPer_lift G).Dk k m _
  have key := integral_mul_Dk_eq h hf hg hΘ hp k
  have e1 : ∀ x : Torus d, SharpLSI.Dk Θ k (secT x) = dpart (dpart G k) k (x - y) := by
    intro x
    have : SharpLSI.Dk Θ k (secT x) =
        SharpLSI.Dk (SharpLSI.Dk (G ∘ liftT) k) k (secT x - secT y) := by
      unfold SharpLSI.Dk
      simp only [hΘdef]
      rw [fderiv_comp_sub]
      rfl
    rw [this, dpart_sub_eq (dpart G k) k x y, dpart_comp_liftT]
    rfl
  have e2 : ∀ x : Torus d, Θ (secT x) = dpart G k (x - y) := by
    intro x
    simp only [hΘdef]
    rw [dpart_sub_eq G k x y]
  simp_rw [e1, e2] at key
  exact key

end Sec8
end SharpLSI.FL
