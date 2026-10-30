import DGPS.FiniteN.QuarticSaddleGlobalFIN066
import DGPS.FiniteN.Tools.EntropyDefects

/-!
# The actual quartic particle entropy defect

The exact Hamiltonian cancellation gives an entropy defect linear in particle number
on the full canonical weak H1 domain. This is the defect term for FIN070 tightening;
it supplies neither the auxiliary global Poincare estimate nor a final scale claim.
-/

open MeasureTheory
open DGPS DGPS.Models DGPS.Particle
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.EntropyDefects DGPS.FiniteN.Tools.WeightedSobolev

namespace DGPS.FiniteN

/-- Exact lifted Hamiltonian, with the original zero-diagonal interaction. -/
theorem quartic_hamiltonian_trig_lift (N : ℕ+)
    (a : Fin ((N : ℕ) * 1) → ℝ) :
    particleHamiltonian anisotropicQuarticSaddle N (ofT 1 N (torusLift a)) =
      trigF 1 (quarticKappa / (2 * (N : ℝ)))
        (quarticKappa * quarticEta / (2 * (N : ℝ))) 0 a := by
  rw [hamiltonian_FIN066]
  have hC : (∑ i : Fin N, scalarCos (ofT 1 N (torusLift a) i)) = cosSum a := by
    simp only [ofT_torusLift_apply, scalarCos_lift]
    exact (sum_idx_one N (fun t => Real.cos (2 * Real.pi * t)) a).symm
  have hS : (∑ i : Fin N, scalarSin (ofT 1 N (torusLift a) i)) = sinSum a := by
    simp only [ofT_torusLift_apply, scalarSin_lift]
    exact (sum_idx_one N (fun t => Real.sin (2 * Real.pi * t)) a).symm
  rw [hC, hS]
  unfold trigF
  ring

/-- Unconditional linear entropy defect on the full canonical particle H1 domain. -/
theorem quartic_particle_entropy_defect (N : ℕ+) (f : ParticleH1 anisotropicQuarticSaddle N) :
    homogeneousEntropy (particleLaw anisotropicQuarticSaddle N) (fun x => f.1 x ^ 2) ≤
      ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy anisotropicQuarticSaddle N f +
        (1 + quarticKappa + quarticKappa * quarticEta) * (N : ℝ) *
          ∫ x, f.1 x ^ 2 ∂particleLaw anisotropicQuarticSaddle N) := by
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  have h := trig_entropy_defect anisotropicQuarticSaddle N (h := 1)
    (p := quarticKappa / (2 * (N : ℝ)))
    (q := quarticKappa * quarticEta / (2 * (N : ℝ))) (r := 0)
    (by positivity) (by positivity) le_rfl (quartic_hamiltonian_trig_lift N) f
  convert h using 3
  simp only [Nat.mul_one, abs_one, zero_add, one_mul]
  field_simp
  ring

end DGPS.FiniteN
