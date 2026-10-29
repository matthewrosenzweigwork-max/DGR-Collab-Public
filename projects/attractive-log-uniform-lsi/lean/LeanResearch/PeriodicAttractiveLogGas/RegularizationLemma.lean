import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierGradient
import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierSmoothConvergence

/-! Source Lemma 2.2 for the fixed, genuinely radial compact probability
mollifier and its prescribed inverse-square scaling and periodization.
Smoothness and local smooth convergence are expressed by the ordinary
Euclidean lifts, as for the singular kernel itself. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

/-- The full radial-regularization conclusions. The lower constant also bounds
the actual singular kernel; one upper/gradient constant is chosen before every
scale and point. The second conjunct includes every derivative order on every
compact subset of the nonsingular Euclidean cover and every scale filter. -/
theorem regularizationLemma :
    (∃ Cg C : ℝ, 0 < Cg ∧ 0 < C ∧
      (∀ z : Torus, -Cg ≤ regularGreenRepresentative z) ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
        ContDiff ℝ ∞ (fun x : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient x)) ∧
        (∀ z : Torus, regularizedGreen ε hε (-z) = regularizedGreen ε hε z) ∧
        (∫ z, regularizedGreen ε hε z ∂torusMeasure) = 0 ∧
        (∀ z : Torus, -Cg ≤ regularizedGreen ε hε z) ∧
        ∀ z : Torus, z ≠ 0 →
          regularizedGreen ε hε z ≤ regularGreenRepresentative z + C * ε ^ 2 ∧
          ‖regularizedGreenGradient ε hε z‖ ≤ C / torusEuclideanNorm z) ∧
    (∀ (ι : Type) (l : Filter ι) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i),
      (∀ i, ε i ≤ (1 / 16 : ℝ)) → Tendsto ε l (𝓝 0) →
      ∀ K : Set PlanarSpace, IsCompact K → K ⊆ offIntegerLattice → ∀ n : ℕ,
        TendstoUniformlyOn
          (fun i ↦ iteratedFDeriv ℝ n
            (fun y : PlanarSpace ↦ regularizedGreen (ε i) (hε i) (torusQuotient y)))
          (iteratedFDeriv ℝ n regularGreenLift) l K) := by
  constructor
  · obtain ⟨Cg, hCg, hlo⟩ := exists_regularGreenRepresentative_lower_bound
    obtain ⟨Cu, hCu, hup⟩ := exists_regularizedGreen_upper_bound
    obtain ⟨Cd, hCd, hgrad⟩ := exists_regularizedGreenGradient_bound
    refine ⟨Cg, max Cu Cd, hCg, lt_of_lt_of_le hCu (le_max_left _ _), hlo, ?_⟩
    intro ε hε hs
    refine ⟨contDiff_regularizedGreen_lift ε hε hs,
      regularizedGreen_even ε hε, regularizedGreen_integral_zero ε hε,
      regularizedGreen_lower_bound hlo ε hε hs, ?_⟩
    intro z hz
    constructor
    · exact (hup ε hε hs z hz).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ε)))
    · exact (hgrad ε hε hs z hz).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (torusEuclideanNorm_nonneg z))
  · intro ι l ε hε hs ht K hK hKU n
    exact tendstoUniformlyOn_iteratedFDeriv_regularizedGreen_lift hε hs ht hK hKU n

end PeriodicAttractiveLogGas
