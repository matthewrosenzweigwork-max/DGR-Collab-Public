import DGPS.Lipschitz.EquilibriumManifold

/-!
# Continuous orthonormal coordinates for the actual Hessian nullspace

Compactness makes the nullspace finite dimensional. Its elements have continuous
representatives from the eigenvalue identity `f = -T f`, without additional regularity.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Every actual nullspace admits the continuous orthonormal basis used in the local
equilibrium graph. No minimizer or direct-Lipschitz assumption is needed for this construction. -/
theorem exists_t01_equilibriumBasis (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    ∃ k : ℕ, ∃ φ : Fin k → C(Torus d, ℝ), IsEquilibriumBasis A μ φ := by
  classical
  let : FiniteDimensional ℝ (nullspace A μ) := finiteDimensional_nullspace A μ
  let k := Module.finrank ℝ (nullspace A μ)
  let B : OrthonormalBasis (Fin k) ℝ (nullspace A μ) :=
    stdOrthonormalBasis ℝ (nullspace A μ)
  let inc : nullspace A μ →ₗ[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) :=
    (meanZeroL2 μ).subtype.comp (nullspace A μ).subtype
  let v : Fin k → Lp ℝ 2 (μ : Measure (Torus d)) := fun i => inc (B i)
  let φ : Fin k → C(Torus d, ℝ) := fun i => -Tcont A (μ : Measure (Torus d)) (v i)
  have hφ : ∀ i, ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i) = v i := by
    intro i
    dsimp only [φ]
    rw [map_neg]
    change -centeredOperator A (μ : Measure (Torus d)) (v i) = v i
    have h := centeredOperator_of_mem_nullspace A μ (B i).2
    change centeredOperator A (μ : Measure (Torus d)) (v i) = -(v i) at h
    rw [h, neg_neg]
  refine ⟨k, φ, ?_⟩
  constructor
  · rw [orthonormal_iff_ite]
    intro i j
    rw [hφ i, hφ j]
    exact orthonormal_iff_ite.mp B.orthonormal i j
  · apply le_antisymm
    · apply Submodule.span_le.2
      rintro f ⟨i, rfl⟩
      change ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i) ∈
        (nullspace A μ).map (meanZeroL2 μ).subtype
      rw [hφ i]
      exact ⟨(B i).1, (B i).2, rfl⟩
    · intro f hf
      obtain ⟨e, he, rfl⟩ := hf
      refine (Submodule.mem_span_range_iff_exists_fun ℝ).2
        ⟨fun i => B.repr ⟨e, he⟩ i, ?_⟩
      simp_rw [hφ]
      have h := congrArg inc (B.sum_repr ⟨e, he⟩)
      simpa [inc, v, LinearMap.comp_apply] using h

end DGPS.Lipschitz
