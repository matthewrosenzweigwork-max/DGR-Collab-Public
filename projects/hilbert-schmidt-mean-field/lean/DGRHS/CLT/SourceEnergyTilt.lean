/- Literal source modulated-energy exponent versus its affine canonical form.
Positive-N exponents agree; at N=0 the affine constant cancels from the
normalized measure. Partition integrals agree eventually at infinity. -/
import DGRHS.CLT.SourceBoundedMGF
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma sourceEnergyExponent_eq {N : ℕ} (h : S × S → ℝ) (F : S → ℝ) (I β : ℝ)
    (hN : 0 < N) :
    (fun x : Fin N → S => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x) =
      sourceParticleExponent h F I β N := by
  funext x
  exact sourceCanonicalModulatedEnergy_exponent h F I β hN x

lemma sourceEnergyTilt_eq (h : S × S → ℝ) (F : S → ℝ) (I β : ℝ) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).tilted
      (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x) =
    (Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N) := by
  by_cases hN : N = 0
  · subst N
    have hE : (fun x : Fin 0 → S => -β*(0 : ℝ)*sourceCanonicalModulatedEnergy h F I 0 x) =
        fun _ => (0 : ℝ) := by funext x; simp
    have hA : sourceParticleExponent h F I β 0 = fun _ => -β*I := by
      funext x
      simp [sourceParticleExponent,DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
        DGRHS.CanonicalVariance.offDiagonalSum]
    norm_num only [Nat.cast_zero]
    rw [hE,hA,tilted_const,tilted_const]
  · rw [sourceEnergyExponent_eq h F I β (Nat.pos_of_ne_zero hN)]

lemma sourceEnergy_partition_eventually_eq (h : S × S → ℝ) (F : S → ℝ) (I β : ℝ) :
    (fun N => ∫ x : Fin N → S,Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)
      ∂Measure.pi (fun _ : Fin N => μ)) =ᶠ[atTop]
    (fun N => ∫ x : Fin N → S,Real.exp (sourceParticleExponent h F I β N x)
      ∂Measure.pi (fun _ : Fin N => μ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  apply integral_congr_ae
  exact ae_of_all _ fun x => congrArg Real.exp (congrFun (sourceEnergyExponent_eq h F I β hN) x)

lemma sourceEnergy_partition_tendsto (h : S × S → ℝ) (F : S → ℝ) (I β z : ℝ)
    (hz : Tendsto (fun N => ∫ x : Fin N → S,Real.exp (sourceParticleExponent h F I β N x)
      ∂Measure.pi (fun _ : Fin N => μ)) atTop (𝓝 z)) :
    Tendsto (fun N => ∫ x : Fin N → S,Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)
      ∂Measure.pi (fun _ : Fin N => μ)) atTop (𝓝 z) :=
  hz.congr' (sourceEnergy_partition_eventually_eq h F I β).symm
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceEnergyExponent_eq
#print axioms DGRHS.CLT.sourceEnergyTilt_eq
#print axioms DGRHS.CLT.sourceEnergy_partition_tendsto
#check @DGRHS.CLT.sourceEnergyTilt_eq
