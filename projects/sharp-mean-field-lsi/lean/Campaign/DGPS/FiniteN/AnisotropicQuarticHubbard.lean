import DGPS.FiniteN.QuarticSaddleGlobalFIN066
import DGPS.FiniteN.ScalarFoldFIN060E

/-!
# The actual anisotropic quartic Hubbard representation

The squared-difference, zero-diagonal interaction agrees with the attractive bilinear
Hubbard weight after the one-body quadratic terms cancel in the Hamiltonian. The model
is never replaced by interaction data with a nonzero diagonal. All normalization and
posterior identities below use that exact Hamiltonian-level equality.
-/

open MeasureTheory Matrix
open DGPS DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Circle.BesselMoments
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

namespace DGPS.FiniteN

noncomputable def quarticHubbardFeature (x : Torus 1) : Fin 2 → ℝ :=
  ![scalarCos x, scalarSin x]

def quarticHubbardU : Torus 1 → ℝ := fun _ => 0

noncomputable def quarticHubbardD : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![quarticKappa, quarticKappa * quarticEta]

def quarticHubbardField : Fin 2 → ℝ := ![1, 0]

/-- Actual bounded single-site data, with no spectral or rate hypothesis. -/
theorem quartic_hubbard_hyp : HubbardHyp (haar 1) quarticHubbardU quarticHubbardFeature where
  m_ne_zero := (haar_isProbabilityMeasure 1).ne_zero
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := Measurable.of_eval fun i => by
    fin_cases i
    · exact continuous_scalarCos.measurable
    · exact continuous_scalarSin.measurable
  φ_bound := ⟨1, fun x => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    fin_cases i
    · change ‖scalarCos x‖ ≤ 1
      simpa only [Real.norm_eq_abs] using scalarCos_bound x
    · change ‖scalarSin x‖ ≤ 1
      simpa only [Real.norm_eq_abs, scalarSin_eq_FIN066] using abs_xyMode_im_le x⟩

/-- The anisotropic covariance matrix is positive definite at the actual fixed parameters. -/
theorem quartic_hubbard_D_posDef : quarticHubbardD.PosDef := by
  unfold quarticHubbardD
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i
  · exact quarticKappa_pos_FIN066
  · exact kappa_eta_pos_FIN066

theorem quartic_hubbard_D_inv :
    quarticHubbardD⁻¹ = Matrix.diagonal ![1 / quarticKappa, 1 / (quarticKappa * quarticEta)] := by
  have hk := quarticKappa_pos_FIN066.ne'
  have hke := kappa_eta_pos_FIN066.ne'
  unfold quarticHubbardD
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change quarticKappa * (1 / quarticKappa) = 1
    exact mul_one_div_cancel hk
  · change (quarticKappa * quarticEta) * (1 / (quarticKappa * quarticEta)) = 1
    exact mul_one_div_cancel hke

/-- The actual feature has Euclidean length one, the precise bound used in transfer. -/
theorem quartic_hubbard_feature_length (x : Torus 1) :
    Real.sqrt (∑ i, quarticHubbardFeature x i ^ 2) = 1 := by
  have h : scalarCos x ^ 2 + scalarSin x ^ 2 = 1 := by
    rw [scalarCos_eq_FIN066, scalarSin_eq_FIN066, im_sq_FIN066]
    ring
  simpa only [quarticHubbardFeature, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, h, Real.sqrt_one] using (rfl : (1 : ℝ) = 1)

/-- The exact gauge cancellation, including the original zero diagonal. -/
theorem quartic_hubbard_particle_weight (N : ℕ+) (x : ParticleSpace 1 N) :
    particleWeight quarticHubbardU quarticHubbardFeature quarticHubbardD quarticHubbardField N x =
      Real.exp (-particleHamiltonian anisotropicQuarticSaddle N x) := by
  unfold particleWeight
  rw [hamiltonian_FIN066]
  congr 1
  simp only [quarticHubbardU, quarticHubbardFeature, quarticHubbardD, quarticHubbardField,
    fieldSum, dotProduct, Fin.sum_univ_two, Finset.sum_apply, Matrix.mulVec_diagonal,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_const_zero,
    neg_zero, zero_add, one_mul, zero_mul, add_zero]
  ring

/-- Particle normalization is exactly the original Gibbs partition function. -/
theorem quartic_hubbard_particle_mass (N : ℕ+) :
    particleMass quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature (haar 1) N =
      ENNReal.ofReal (particlePartition anisotropicQuarticSaddle N) :=
  ScalarFoldFIN060.particleMass_eq_FIN060 (quartic_hubbard_particle_weight N)

/-- Exact equality of the actual particle laws, valid on the full canonical particle space. -/
theorem quartic_hubbard_particle_law (N : ℕ+) :
    hubbardParticleLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
      (haar 1) N = particleLaw anisotropicQuarticSaddle N :=
  ScalarFoldFIN060.hubbardParticleLaw_eq_particleLaw_FIN060 (quartic_hubbard_particle_weight N)

/-- The posterior center is the actual empirical field, with its original external shift. -/
theorem quartic_hubbard_posterior_center (N : ℕ+) (x : ParticleSpace 1 N) :
    posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x =
      ![1 + quarticKappa * (∑ i, scalarCos (x i)) / (N : ℝ),
        (quarticKappa * quarticEta) * (∑ i, scalarSin (x i)) / (N : ℝ)] := by
  ext i
  fin_cases i <;>
    simp [posteriorCenter, quarticHubbardD, quarticHubbardField, quarticHubbardFeature,
      fieldSum, Finset.sum_apply, div_eq_mul_inv] <;> ring

/-- The auxiliary normalizer is the same Bessel function used in the actual quartic potential. -/
theorem quartic_hubbard_aux_partition (w : Fin 2 → ℝ) :
    auxPartition quarticHubbardU quarticHubbardFeature (haar 1) w =
      besselI 0 (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) := by
  rw [← partition_rot_FIN066]
  unfold auxPartition expTerm xyPartition xyTrig
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  congr 1
  simp [quarticHubbardU, quarticHubbardFeature, dotProduct, Fin.sum_univ_two,
    scalarCos_eq_FIN066, scalarSin_eq_FIN066]

/-- Exact auxiliary potential, not a comparison up to a diagonal or additive gauge. -/
theorem quartic_hubbard_aux_potential (w : Fin 2 → ℝ) :
    auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD quarticHubbardField (haar 1) w =
      quarticPsi_FIN066 !₂[w 0, w 1] := by
  have hk := quarticKappa_pos_FIN066.ne'
  have hke := kappa_eta_pos_FIN066.ne'
  unfold auxPotential
  rw [quartic_hubbard_D_inv, quartic_hubbard_aux_partition]
  simp [quadForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two,
    quarticHubbardField, quarticPsi_FIN066, Matrix.vecHead, Matrix.vecTail] <;> field_simp [hk, hke] <;> ring

end DGPS.FiniteN
