import DGPS.Lipschitz.T01CovarianceMatrix
import SharpSymmetricLSI.Paper.GaussLSI2

/-!
# Gaussian LSI and Poincare for the actual common reference

The full `L2` inequalities follow from the generic cylinder relaxation, using the
genuine covariance inverse and the actual density Hessian coercivity certificate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI

/-- The genuine common-reference Gaussian has its matrix quotient LSI and Poincare rate. -/
theorem t01_gaussian_lsi_poincare {d : ℕ} (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (hpos1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A)) :
    0 < lamG (lamShift S.lam) (t01CovarianceMatrix S A) ∧
      lamG (lamShift S.lam) (t01CovarianceMatrix S A) < ⊤ ∧
      (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
        ent γ (fun z => f z ^ 2) ≤
          2 / lamG (lamShift S.lam) (t01CovarianceMatrix S A) *
            gaussForm (lamShift S.lam) γ f ∧
        var γ f ≤ gaussForm (lamShift S.lam) γ f /
          lamG (lamShift S.lam) (t01CovarianceMatrix S A)) := by
  obtain ⟨σ, hσ, hbound⟩ := hH
  have P := t01CovarianceMatrix_symPkg S aux A D hD hσ hbound
  have hPSD := blockMat_posSemidef P.symm P.hs P.pos P.sec P.inv
  have hlam0 : 0 < lamShift S.lam 0 := hpos1
  have hlam : ∀ i, lamShift S.lam 0 ≤ lamShift S.lam i :=
    fun i => hmono (by omega)
  have hpos := lamG_pos P.pos P.Csymm P.nn P.up (fun j => (P.inv j).1) hlam0 hlam
  have htop := lamG_lt_top P.Csymm P.nn P.inv (lamShift S.lam)
  exact ⟨hpos, htop, fun f hf =>
    ⟨gaussian_lsi_relax hγ hPSD P.nn hpos htop f hf,
      gaussian_poincare hγ hPSD P.nn hpos htop f hf⟩⟩

end DGPS.Lipschitz
