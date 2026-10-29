import DGRHS.Commutator.SourceLogTransportKernel
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffAt_sourceLogPotential (n : ℕ) {z : E} (hz : z ≠ 0) :
    ContDiffAt ℝ n sourceLogPotential z :=
  ((contDiffAt_norm ℝ hz).log (norm_ne_zero_iff.mpr hz)).neg

theorem contDiffOn_sourceLogPotential (n : ℕ) :
    ContDiffOn ℝ n (sourceLogPotential (E := E)) ({0}ᶜ : Set E) := by
  intro z hz
  exact (contDiffAt_sourceLogPotential n (by simpa using hz)).contDiffWithinAt

theorem sourceLogPotential_smul {r : ℝ} (hr : 0 < r) {z : E} (hz : z ≠ 0) :
    sourceLogPotential (r • z) = sourceLogPotential z + (-Real.log r) := by
  unfold sourceLogPotential
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hz)]
  ring

variable [FiniteDimensional ℝ E]

/-- Exact positive scaling of the actual higher derivative, obtained without a derivative bound. -/
theorem sourceLogPotential_iteratedFDeriv_smul {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) {z : E} (hz : z ≠ 0) :
    r ^ n • iteratedFDeriv ℝ n sourceLogPotential (r • z) =
      iteratedFDeriv ℝ n sourceLogPotential z := by
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toContinuousLinearEquiv
  have hg : ∀ u, g u = r • u := fun _ => rfl
  have hc : iteratedFDeriv ℝ n (sourceLogPotential ∘ g) z =
      (iteratedFDeriv ℝ n sourceLogPotential (g z)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right sourceLogPotential uniqueDiffOn_univ (mem_univ z) n
  have he : (sourceLogPotential ∘ g) =ᶠ[𝓝 z]
      (sourceLogPotential + fun _ => -Real.log r) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
      (show z ∈ ({0}ᶜ : Set E) by simpa using hz)] with u hu
    exact sourceLogPotential_smul hr (by simpa using hu)
  have hh := (he.iteratedFDeriv ℝ n).eq_of_nhds
  rw [iteratedFDeriv_add_apply (contDiffAt_sourceLogPotential n hz) contDiffAt_const,
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn), Pi.zero_apply, add_zero] at hh
  rw [hc] at hh
  ext m
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ => F m) hh
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg,
    ContinuousMultilinearMap.map_smul_univ] using hm

#print axioms contDiffAt_sourceLogPotential
#print axioms sourceLogPotential_smul
#print axioms sourceLogPotential_iteratedFDeriv_smul
end DGRHS.Commutator
