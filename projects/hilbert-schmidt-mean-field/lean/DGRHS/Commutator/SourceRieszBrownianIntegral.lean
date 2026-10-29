/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: full-filtration predictable L2 domain and directly
proved rectangle density/isometry, with native continuous extension.
-/
import DGRHS.Commutator.SourceRieszBrownianAssemblyIsometry
import Mathlib.Analysis.Normed.Operator.Extend

/-! Actual Brownian integral of every finite-horizon predictable L2 integrand.
The construction follows MathFin/Foundations/ItoIntegralCLM.lean at
f085fd572075c934827f1eb92c4a085941cd21e5, using the independently established
full-filtration density and concrete Brownian-sum isometry. This module constructs
the terminal L2 random variable; continuous process versions and common-driver
quadratic covariations are separate obligations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal InnerProductSpace
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

def sourceRieszBrownianIntegral :
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) →L[ℝ] Lp ℝ 2 P :=
  (sourceRieszBrownianItoAssembly P F T B hB hBa hind).extendOfNorm
    (sourceRieszBrownianAtomAssembly P F T)

theorem sourceRieszBrownianIntegral_elementary (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    sourceRieszBrownianIntegral P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c)=
      sourceRieszBrownianItoAssembly P F T B hB hBa hind c := by
  unfold sourceRieszBrownianIntegral
  exact LinearMap.extendOfNorm_eq (sourceRieszBrownianAtomAssembly_dense P F T)
    ⟨1,fun d=>by rw [one_mul];exact (sourceRieszBrownianAssembly_isometry P F T B hB hBa hind d).le⟩ c

theorem sourceRieszBrownianIntegral_norm
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ‖sourceRieszBrownianIntegral P F T B hB hBa hind g‖=‖g‖ := by
  unfold sourceRieszBrownianIntegral
  exact ((sourceRieszBrownianItoAssembly P F T B hB hBa hind).extendOfIsometry
    (sourceRieszBrownianAtomAssembly_dense P F T)
    (sourceRieszBrownianAssembly_isometry P F T B hB hBa hind)).norm_map g

theorem sourceRieszBrownianIntegral_elementary_coe (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    (sourceRieszBrownianIntegral P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) : Ω→ℝ)
      =ᵐ[P] fun ω=>∑ A∈c.support,(c A*A.value ω)*(B A.b ω-B A.a ω) := by
  rw [sourceRieszBrownianIntegral_elementary]
  convert sourceRieszBrownianItoAssembly_coe P F T B hB hBa hind c using 1
  exact (funext (sourceRieszBrownianItoRawAssembly_apply F T B c)).symm

theorem sourceRieszBrownianIntegral_isometry :
    Isometry (sourceRieszBrownianIntegral P F T B hB hBa hind) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact sourceRieszBrownianIntegral_norm P F T B hB hBa hind

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszBrownianIntegral
#print axioms DGRHS.Commutator.sourceRieszBrownianIntegral

#check @DGRHS.Commutator.sourceRieszBrownianIntegral_elementary
#print axioms DGRHS.Commutator.sourceRieszBrownianIntegral_elementary

#check @DGRHS.Commutator.sourceRieszBrownianIntegral_norm
#print axioms DGRHS.Commutator.sourceRieszBrownianIntegral_norm

#check @DGRHS.Commutator.sourceRieszBrownianIntegral_elementary_coe
#print axioms DGRHS.Commutator.sourceRieszBrownianIntegral_elementary_coe

#check @DGRHS.Commutator.sourceRieszBrownianIntegral_isometry
#print axioms DGRHS.Commutator.sourceRieszBrownianIntegral_isometry
