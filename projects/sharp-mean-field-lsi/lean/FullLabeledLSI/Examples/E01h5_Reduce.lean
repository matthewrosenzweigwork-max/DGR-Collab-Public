import FullLabeledLSI.Examples.E01h2_UintPoly
import FullLabeledLSI.Examples.E01h3_Series

/-!
# Lane D, Task B2: the Hessian is affine in `ρ` (reduction to Dirac masses)

`σ((g * ρ) h) = ∫ σ(g(· - y) h) dρ(y)` (Fubini), so
`UintHess C ℓ ρ α β = ∫ (A + E(y)) dρ(y)` with `A = 4σ(C''*σ) + 2ℓσ(C*σ)` and
`E(y) = 2 (C'*σ)(y)² + 4 σ(C'(· - y) (C'*σ))`.
-/

open MeasureTheory Filter Topology
open scoped Real ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

section

variable {g h : Torus 1 → ℝ} (hg : Continuous g) (hh : Continuous h)
  (ρ α β : Measure (Torus 1)) [IsFiniteMeasure ρ] [IsFiniteMeasure α] [IsFiniteMeasure β]

include hg hh in
theorem continuous_param_int (μ : Measure (Torus 1)) [IsFiniteMeasure μ] :
    Continuous fun y : Torus 1 => ∫ z, g (z - y) * h z ∂μ := by
  have := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun y z : Torus 1 => g (z - y) * h z)
    ((hg.comp (continuous_snd.sub continuous_fst)).mul (hh.comp continuous_snd)) (isCompact_univ)
  simpa using this

include hg hh in
theorem continuous_intS_param :
    Continuous fun y : Torus 1 => intS (fun z => g (z - y) * h z) α β := by
  unfold intS
  exact (continuous_param_int hg hh α).sub (continuous_param_int hg hh β)

include hg hh in
theorem int_cvM_mul (μ : Measure (Torus 1)) [IsFiniteMeasure μ] :
    ∫ z, cvM ρ g z * h z ∂μ = ∫ y, ∫ z, g (z - y) * h z ∂μ ∂ρ := by
  have e : ∀ z, cvM ρ g z * h z = ∫ y, g (z - y) * h z ∂ρ := fun z => by
    unfold cvM; rw [integral_mul_const]
  simp_rw [e]
  have hc : Continuous (Function.uncurry fun z y : Torus 1 => g (z - y) * h z) :=
    (hg.comp (continuous_fst.sub continuous_snd)).mul (hh.comp continuous_fst)
  exact integral_integral_swap
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

include hg hh in
theorem intS_cvM_mul :
    intS (fun z => cvM ρ g z * h z) α β = ∫ y, intS (fun z => g (z - y) * h z) α β ∂ρ := by
  unfold intS
  rw [int_cvM_mul hg hh ρ α, int_cvM_mul hg hh ρ β, ← integral_sub]
  · exact (continuous_param_int hg hh α).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_param_int hg hh β).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end

end SharpLSI.FL.Ex.LaneD
