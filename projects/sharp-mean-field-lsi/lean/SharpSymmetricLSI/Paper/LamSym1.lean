import SharpSymmetricLSI.Paper.TestEnergy9
import SharpSymmetricLSI.Paper.ForceExp

/-!
# R33 groundwork: linear fluctuation tests (manuscript Section 8.5, upper bound)

`f_N = ∑_i v_i Z_{N,i}` (with `C¹` representatives) is symmetric, in `H¹(P_N)`, and
`|∇f_N|² = ∑_{ij} v_i v_j A_{N,ij}` a.e.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The linear functional `z ↦ ∑ v_i z_i`. -/
noncomputable def linCLM {J : ℕ} (v : Fin J → ℝ) : (Fin J → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj i

theorem linCLM_apply {J : ℕ} (v z : Fin J → ℝ) : linCLM v z = ∑ i, v i * z i := by
  simp [linCLM]

theorem fderiv_linCLM {J : ℕ} (v z : Fin J → ℝ) (i : Fin J) :
    fderiv ℝ (linCLM v) z (Pi.single i 1) = v i := by
  rw [(linCLM v).fderiv, linCLM_apply]
  simp [Pi.single_apply]

/-- The linear test `f_N = ∑_i v_i Z_{N,i}`. -/
noncomputable def linTest (eC : ℕ → Torus d → ℝ) (N J : ℕ) (v : Fin J → ℝ) (X : Config N d) : ℝ :=
  linCLM v (zC eC N J X)

theorem linTest_symm (eC : ℕ → Torus d → ℝ) (N J : ℕ) (v : Fin J → ℝ) :
    IsSymmetric (linTest eC N J v) := by
  intro σ X
  simp only [linTest, linCLM_apply, zC]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact Equiv.sum_comp σ (fun l => eC (i + 1) (X l))

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
include hyp hμ hφ

/-- `|∇φ(Z_N)|² = ∑ ∂_iφ ∂_jφ A_{ij}` a.e. under `μ^{⊗N}`, for `C¹` `φ`. -/
theorem gradSqC_compZ_ae (N : ℕ) {J : ℕ} (φ : (Fin J → ℝ) → ℝ) (hφ1 : ContDiff ℝ 1 φ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (fun X => φ (zC eC N J X)) X =
        ∑ i : Fin J, ∑ j : Fin J, fderiv ℝ φ (zC eC N J X) (Pi.single i 1) *
          fderiv ℝ φ (zC eC N J X) (Pi.single j 1) * mobA eC N X i j := by
  have h := isWeakGrad_compZ hφ N φ hφ1
  filter_upwards [ae_pi_of_ae_volume hyp hμ (weakGrad_ae_eq h)] with X hX
  unfold gradSqC weakGradC
  simp_rw [hX]
  have e1 : unflat (flat X) = X := rfl
  have e2 : ∀ l, projBlock l (flat X) = X l := fun _ => rfl
  try simp only [e1, e2]
  rw [sum_sq_regroup (fun (i : Fin J) (l : Fin N) (k : Fin d) =>
    fderiv ℝ φ (zC eC N J X) (Pi.single i 1) *
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (eC (i + 1)) (X l) k))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold mobA
  rw [← rpow_neg_half_sq N, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `|∇f_N|² = ∑ v_i v_j A_{ij}` a.e. -/
theorem gradSqC_linTest_ae (N J : ℕ) (v : Fin J → ℝ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (linTest eC N J v) X = ∑ i : Fin J, ∑ j : Fin J, v i * v j * mobA eC N X i j := by
  filter_upwards [gradSqC_compZ_ae hyp hμ hφ N (linCLM v) (linCLM v).contDiff] with X hX
  rw [show linTest eC N J v = fun X => linCLM v (zC eC N J X) from rfl, hX]
  simp only [fderiv_linCLM]

theorem memH1C_linTest (N J : ℕ) (v : Fin J → ℝ) : MemH1C (gibbs V W N) (linTest eC N J v) := by
  have hP := gibbs_isProbabilityMeasure hyp N
  have hac := minimizer_ac hyp hμ
  have h1 : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  have h2 := h1.trans (pi_ac_volume hac N)
  have h3 : (gibbs V W N).map flat ≪ volume := by
    have := h2.map measurable_flat
    rwa [map_flat_volume N] at this
  exact memH1_of_contDiff_ac h3 (contDiff_compZ hφ N (linCLM v).contDiff)

end

end SharpLSI
