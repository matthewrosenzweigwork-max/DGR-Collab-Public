import SharpSymmetricLSI.Defs.D02_Hypotheses
import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Infra.GibbsGeneric

/-!
# D8: Hamiltonian, partition function, Gibbs measure (1.1)

`H_N(X) = ∑ᵢ V(xᵢ) + (1/(2N)) ∑_{i,j} W(xᵢ,xⱼ)` (diagonal terms included),
`dP_N = Z_N^{-1} e^{-H_N} dm^{⊗N}`.
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- The Hamiltonian `H_N` (manuscript (1.1)). -/
noncomputable def hamiltonian (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ)
    (X : Config N d) : ℝ :=
  ∑ i, V (X i) + 1 / (2 * (N : ℝ)) * ∑ i, ∑ j, W (X i) (X j)

/-- The partition function `Z_N = ∫ e^{-H_N} dm^{⊗N}`. -/
noncomputable def partitionFn (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) : ℝ :=
  ∫ X : Config N d, Real.exp (-hamiltonian V W N X)

/-- The canonical Gibbs measure `P_N` (manuscript (1.1)). -/
noncomputable def gibbs (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) :
    Measure (Config N d) :=
  (volume : Measure (Config N d)).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-hamiltonian V W N X) / partitionFn V W N))

/-- Sanity lemma for D8: under (1.2), `P_N` is a probability measure. -/
theorem gibbs_isProbabilityMeasure {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) : IsProbabilityMeasure (gibbs V W N) := by
  have hW : ∀ i j : Fin N, Continuous fun X : Config N d => W (X i) (X j) := fun i j =>
    hyp.continuous_W.comp ((continuous_apply i).prodMk (continuous_apply j) :
      Continuous fun X : Config N d => (X i, X j))
  have hH : Continuous (hamiltonian V W N) := by
    unfold hamiltonian
    exact (continuous_finsetSum _ fun i _ => hyp.continuous_V.comp (continuous_apply i)).add
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => hW i j))
  exact isProbabilityMeasure_withDensity_gibbs volume hH

end SharpLSI
