import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Lipschitz.EigenfunctionC1
import DGPS.Variational.FrozenGibbs

/-!
# Weak Hessians on the retained frozen spectral witness

The actual Gibbs spectral construction retains its exact weight. The weak eigen-equation
then identifies the distributional Laplacian, and periodic elliptic regularity provides
weak Hessians for the same continuous eigenfunctions and their same actual gradients.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz
open DGPS.Analysis DGPS.Analysis.CompactResolvent KernelApproximation WeightedGenerator
  ParabolicChainRule
variable {d : ℕ}

/-- Weak Hessians and the frozen weak Laplacian for the same retained spectral witness. -/
theorem t01_frozen_spectral_hessian_of_weight (S : Spec d) (aux : Aux S)
    (Φ : Torus d → ℝ) {L : ℝ} (hL : 0 ≤ L) (hΦ : TorusLipschitzWith L Φ)
    (hw : S.w = gibbsW Φ) (hC1 : ∀ j, IsC1Periodic (S.v j))
    (heig : ∀ j (f : Hw d S.w) (Y : Torus d → Tangent d),
      IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm S.w (aux.g j) Y = S.lam j * inner ℝ (S.e j) f) :
    ∃ H : ℕ → Fin d → Fin d → Torus d → ℝ,
      (∀ j, IsWeakHessian (S.v j) (smoothGrad (S.v j)) (H j)) ∧
      (∀ j, IsWeakLaplacian (S.v j)
        (fun z => inner ℝ (smoothGrad Φ z) (smoothGrad (S.v j) z) - S.lam j * S.v j z)) := by
  obtain ⟨c, C, hwd⟩ := gibbs_wdata hL hΦ
  have hwd' : WData d S.w (fun x => -smoothGrad Φ x) c C := by
    rw [hw]
    exact hwd
  have hlap : ∀ j, IsWeakLaplacian (S.v j)
      (fun z => inner ℝ (smoothGrad Φ z) (smoothGrad (S.v j) z) - S.lam j * S.v j z) := by
    intro j
    have hG : IsWeakGradient (S.e j : Torus d → ℝ) (aux.g j) :=
      (aux.gw j).congr_ae (S.ve j) (EventuallyEq.refl _ _)
    have he := EigenfunctionC1.weak_laplacian_of_eig hwd' hG (heig j)
    have hga : aux.g j =ᵐ[haar d] smoothGrad (S.v j) :=
      (aux.gw j).ae_eq (hC1 j).isWeakGradient
    have hrhs : (fun z => -(S.lam j * (S.e j : Torus d → ℝ) z +
        inner ℝ (-smoothGrad Φ z) (aux.g j z))) =ᵐ[haar d]
        (fun z => inner ℝ (smoothGrad Φ z) (smoothGrad (S.v j) z) - S.lam j * S.v j z) := by
      filter_upwards [S.ve j, hga] with z hz hgz
      rw [← hz, hgz, inner_neg_left]
      ring
    refine ⟨(aux.gw j).memLp, he.memLp_lap.ae_eq hrhs, fun φ hφ => ?_⟩
    calc (∫ x, S.v j x * periodicLaplacian φ x ∂haar d)
        = ∫ x, (S.e j : Torus d → ℝ) x * periodicLaplacian φ x ∂haar d :=
          integral_congr_ae ((S.ve j).mono fun x hx =>
            congrArg (fun t : ℝ => t * periodicLaplacian φ x) hx)
      _ = ∫ x, -(S.lam j * (S.e j : Torus d → ℝ) x +
          inner ℝ (-smoothGrad Φ x) (aux.g j x)) * φ x ∂haar d := he.ibp φ hφ
      _ = _ := integral_congr_ae (hrhs.mono fun x hx =>
          congrArg (fun t : ℝ => t * φ x) hx)
  have hH : ∀ j, ∃ H : Fin d → Fin d → Torus d → ℝ,
      IsWeakHessian (S.v j) (smoothGrad (S.v j)) H := by
    intro j
    obtain ⟨G, H, h, -, -⟩ := exists_hessian_of_weakLaplacian
      ⟨smoothGrad (S.v j), (hC1 j).isWeakGradient⟩ (hlap j)
    have hGa : G =ᵐ[haar d] smoothGrad (S.v j) :=
      h.grad.ae_eq (hC1 j).isWeakGradient
    refine ⟨H, (hC1 j).isWeakGradient, h.memLp_hess, fun i k φ hφ => ?_⟩
    calc (∫ x, smoothGrad (S.v j) x k * coordPartial i φ x ∂haar d)
        = ∫ x, G x k * coordPartial i φ x ∂haar d :=
          integral_congr_ae (hGa.mono fun x hx =>
            congrArg (fun Y : Tangent d => Y k * coordPartial i φ x) hx.symm)
      _ = _ := h.ibp i k φ hφ
  choose H hH using hH
  exact ⟨H, hH, hlap⟩

/-- One actual frozen spectral witness supplies the basis, the centered kernel and weak Hessians.
No second independent basis is selected for the dual generator. -/
theorem exists_equilibrium_spectral_hessian_data (A : InteractionData d) (hA : LipschitzData A)
    (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ (S : Spec d) (aux : Aux S) (D : KData d)
      (H : ℕ → Fin d → Fin d → Torus d → ℝ),
      S.mu = (μ : Measure (Torus d)) ∧ Monotone S.lam ∧ S.lam 0 = 0 ∧
      S.lam 0 < S.lam 1 ∧ (∀ j, IsC1Periodic (S.v j)) ∧
      (∀ j (f : Hw d S.w) (Y : Torus d → Tangent d),
        IsWeakGradient (f : Torus d → ℝ) Y →
          weightedForm S.w (aux.g j) Y = S.lam j * inner ℝ (S.e j) f) ∧
      D.K = centeredKernel A S.mu ∧
      (∀ j, IsWeakHessian (S.v j) (smoothGrad (S.v j)) (H j)) ∧
      (∀ j, IsWeakLaplacian (S.v j) (fun z =>
        inner ℝ (smoothGrad (frozenPotential A μ) z) (smoothGrad (S.v j) z) - S.lam j * S.v j z)) ∧
      IsWeakGradient (frozenPotential A μ) (smoothGrad (frozenPotential A μ)) ∧
      S.w = gibbsW (frozenPotential A μ) := by
  obtain ⟨L, hL, hΦ⟩ := lipschitz_equilibriumPotential A hA
  have hgrad := weak_gradient_log_gibbsDensity A (μ : Measure (Torus d))
    (exists_weak_gradient hL (hΦ (μ : Measure (Torus d)))).1
  have hlog : IsWeakGradient
      (fun x => Real.log (gibbsW (equilibriumPotential A μ) x))
      (fun x => -smoothGrad (equilibriumPotential A μ) x) := by
    apply isWeakGradient_iff_isWeakGradientLp.mpr
    simpa only [gibbsW, gibbsDensity, gibbsPartition] using
      (show IsWeakGradientLp 2 (fun x => Real.log (gibbsDensity A μ x))
        (fun x => -smoothGrad (equilibriumPotential A μ) x) from
        ⟨hgrad.memLp.mono_exponent (by simp), hgrad.memLp_grad.mono_exponent (by simp), hgrad.ibp⟩)
  obtain ⟨S, aux, hw, hmono, hl0, hl01, hC1, hE⟩ :=
    exists_spec_aux_eigen hd hL (hΦ (μ : Measure (Torus d))) hlog
  have hS : S.mu = (μ : Measure (Torus d)) := by
    rw [minimizer_eq_gibbs A μ hμ, gibbsMeasure_eq_withDensity]
    change wMeasure d S.w = _
    rw [hw]
    rfl
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  obtain ⟨H, hH, hlap⟩ := t01_frozen_spectral_hessian_of_weight S aux
    (equilibriumPotential A μ) hL (hΦ (μ : Measure (Torus d))) hw hC1 hE
  have hΦgrad : IsWeakGradient (equilibriumPotential A μ) (smoothGrad (equilibriumPotential A μ)) := by
    obtain ⟨h, -⟩ := exists_weak_gradient hL (hΦ (μ : Measure (Torus d)))
    exact isWeakGradient_iff_isWeakGradientLp.mpr
      ⟨h.memLp.mono_exponent (by simp), h.memLp_grad.mono_exponent (by simp), h.ibp⟩
  refine ⟨S, aux, D, H, hS, hmono, hl0, hl01, hC1, hE, ?_, hH, hlap, hΦgrad, hw⟩
  rw [hS]
  exact hD

end DGPS.Lipschitz
