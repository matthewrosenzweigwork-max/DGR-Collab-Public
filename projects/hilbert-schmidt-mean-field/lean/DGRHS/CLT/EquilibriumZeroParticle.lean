/- Empty product conventions, needed only to express the original positive-N
canonical CLT as a natural-number sequence without changing its limit. -/
import DGRHS.CLT.EquilibriumCollisionWeight
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]
lemma canonicalSingularLaw_zero (ν₀ : Measure S) (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) :
    canonicalSingularLaw ν₀ W V β 0=Measure.pi (fun _ : Fin 0 => ν₀) := by
  simp [canonicalSingularLaw,canonicalSingularPartition,canonicalSingularWeight,
    sourceHamiltonian,DGRHS.CanonicalVariance.offDiagonalSum]
lemma sourceEnergyTilt_zero (ν₀ μ : Measure S) (h : S × S → ℝ)
    (F : S → ℝ) (I β : ℝ) :
    (Measure.pi (fun _ : Fin 0 => μ)).tilted
      (fun x => -β*(0 : ℝ)*sourceCanonicalModulatedEnergy h F I 0 x)=
      Measure.pi (fun _ : Fin 0 => ν₀) := by
  have he : (fun x : Fin 0 → S => -β*(0 : ℝ)*sourceCanonicalModulatedEnergy h F I 0 x)=
      fun _ => (0 : ℝ) := by funext x;simp
  rw [he]
  rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
    Measure.pi_of_empty (fun _ : Fin 0 => ν₀)]
  exact tilted_const _ _
end DGRHS.CLT
#check @DGRHS.CLT.canonicalSingularLaw_zero
#check @DGRHS.CLT.sourceEnergyTilt_zero
#print axioms DGRHS.CLT.canonicalSingularLaw_zero
#print axioms DGRHS.CLT.sourceEnergyTilt_zero
