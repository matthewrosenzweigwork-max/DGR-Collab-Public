import FullLabeledLSI.Defs.F03_RelFisher
import FullLabeledLSI.Infra.HypercontrTorusCalc
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# Section 8: classical calculus for smooth positive densities

Smooth strictly positive densities `A`, `B` on the torus: `√A` is smooth and in `H^1`, and
`relFisher A B` is the integral of the squared difference of the classical weighted scores
(the manuscript's `∫ |∇log A - ∇log B|² A`).  Also the pointwise identity for
`A = ρ (1 + c k)` against `ρ`.
-/

open MeasureTheory InformationTheory Filter Topology SharpLSI.FL.Gross
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ}

theorem isSmoothT_sqrt {f : Torus d → ℝ} (hf : IsSmoothT f) (hpos : ∀ x, 0 < f x) :
    IsSmoothT (fun x => Real.sqrt (f x)) :=
  ContDiff.sqrt hf fun z => (hpos _).ne'

theorem c1T_of_smooth {f : Torus d → ℝ} (hf : IsSmoothT f) : C1T f :=
  ContDiff.of_le hf (by simp)

theorem memH1_of_smooth {f : Torus d → ℝ} (hf : IsSmoothT f) : MemH1 (haar d) f :=
  SharpLSI.memH1_of_contDiff hf

theorem continuous_of_smooth {f : Torus d → ℝ} (hf : IsSmoothT f) : Continuous f :=
  SharpLSI.IsSmoothT.continuous hf

theorem integrable_of_smooth {f : Torus d → ℝ} (hf : IsSmoothT f) : Integrable f (haar d) :=
  SharpLSI.integrable_of_continuous (continuous_of_smooth hf)

theorem isSmoothT_mul {f g : Torus d → ℝ} (hf : IsSmoothT f) (hg : IsSmoothT g) :
    IsSmoothT (fun x => f x * g x) := ContDiff.mul hf hg

theorem isSmoothT_one_add {k : Torus d → ℝ} (c : ℝ) (hk : IsSmoothT k) :
    IsSmoothT (fun x => 1 + c * k x) := contDiff_const.add (contDiff_const.mul hk)

theorem relFisher_smooth {A B : Torus d → ℝ} (hA : IsSmoothT A) (hB : IsSmoothT B)
    (hApos : ∀ x, 0 < A x) (hBpos : ∀ x, 0 < B x) :
    relFisher A B = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * dT (fun y => Real.sqrt (A y)) k x -
      Real.sqrt (A x) * (2 * dT (fun y => Real.sqrt (B y)) k x / Real.sqrt (B x))) ^ 2) ∂haar d := by
  have hsA := isSmoothT_sqrt hA hApos
  have hsB := isSmoothT_sqrt hB hBpos
  have hHA : MemH1 (haar d) (fun x => Real.sqrt (A x)) := memH1_of_smooth hsA
  have hHB : MemH1 (haar d) (fun x => Real.sqrt (B x)) := memH1_of_smooth hsB
  have hac : densMeasure A ≪ densMeasure B := by
    refine (withDensity_absolutelyContinuous _ _).trans ?_
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (ENNReal.measurable_ofReal.comp (c1T_of_smooth hB).measurable).aemeasurable
    · simpa using hBpos x
  unfold relFisher
  rw [if_pos ⟨hac, hHA, hHB⟩]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_dT (c1T_of_smooth hsA), weakGrad_ae_eq_dT (c1T_of_smooth hsB)]
    with x h1 h2
  have e1 := fun k => congrFun h1 k
  have e2 := fun k => congrFun h2 k
  simp only [score, if_pos (hBpos x), e1, e2]

/-- `S x = |∇k(x)|²` (classical gradient). -/
noncomputable def gradSq (k : Torus d → ℝ) (x : Torus d) : ℝ := ∑ j, dT k j x ^ 2

theorem gradSq_nonneg (k : Torus d → ℝ) (x : Torus d) : 0 ≤ gradSq k x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end Sec8
end SharpLSI.FL
