import DGPS.Lipschitz.T01CovarianceMatrix
import SharpSymmetricLSI.Paper.FormDuality7
import SharpSymmetricLSI.Paper.GaussForm24

/-!
# Gaussian form duality for the actual common reference

The genuine covariance inverse and the finite-section Hessian bound supply the generic
simultaneous diagonalization hypotheses. All coordinates use the same positive spectral
modes; the generator retains the order `Λ(I+T)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI

/-- Form duality for the actual covariance, without a legacy semiconvexity hypothesis. -/
theorem t01_gaussian_form_duality {d : ℕ} (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (hpos1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htop : Tendsto S.lam atTop atTop)
    (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A))
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat A.W S.mu S.v) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (gaussForm (lamShift S.lam) γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift S.lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift S.lam) γ : EReal) := by
  obtain ⟨σ, hσ, hbound⟩ := hH
  have P := t01CovarianceMatrix_symPkg S aux A D hD hσ hbound
  have hpos : ∀ i, 0 < lamShift S.lam i := fun i =>
    hpos1.trans_le (hmono (by omega))
  have ht : Tendsto (lamShift S.lam) atTop atTop :=
    htop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨v, ν, hv, hvC, hvΛ, hν0, hνmono, -, -, hpar⟩ :=
    exists_genEigen_matrix P.symm P.hs P.pos P.sec hpos P.inv P.Csymm ht
  have hex : ∀ j, ∃ ξ, IsRowVariable v γ j ξ := fun j =>
    exists_rowVariable hγ P.pos P.nn P.up (hv j).1
  choose ξ hξ using hex
  haveI := hγ.1
  have hΞ : AEMeasurable (fun z j => ξ j z) γ :=
    aemeasurable_pi_iff.2 fun j => (hξ j).1.aestronglyMeasurable.aemeasurable
  have hmap := map_xi_eq_gammaRef P.symm P.hs P.pos P.sec P.inv P.Csymm hγ
    (fun j => (hv j).1) hvC hξ
  have hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) →
        F =ᵐ[γ] 0 :=
    fun F hF horth => hermite_complete_xi P.symm P.hs P.pos P.sec P.inv P.Csymm hγ
      (fun j => (hv j).1) hvC hξ hpar hF horth
  have hW : ∀ j k, Tendsto
      (fun N => ∑ i ∈ Finset.range N, lamShift S.lam i * v j i * v k i) atTop
        (𝓝 (if j = k then ν j else 0)) := fun j k => by
    rw [← hvΛ j k]
    exact tendsto_partial_lam_vv (hv j).2 (hv k).1
  have hLξ := tendsto_gen_xi P.symm P.hs P.pos P.sec P.inv P.Csymm hγ
    (fun j => (hv j).1) hvC hξ hpar (fun j => (hv j).2) hvΛ hY
  have hν : ∀ j, 0 ≤ ν j := fun j => hν0.le.trans (hνmono (Nat.zero_le j))
  exact form_duality_generic hγ (blockMat_posSemidef P.symm P.hs P.pos P.sec P.inv)
    P.inv hY (fun i => (hpos i).le) hν hξ hW hLξ hΞ hmap hcomp hf

end DGPS.Lipschitz
