import DGRHS.Commutator.SourceC2PointwiseApproximation
import DGRHS.Commutator.SourceCompactC2Mollifier
import DGRHS.Commutator.SourceLogCompactC2Cutoff

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

The two concrete constructors of pointwise C2 approximations used by the LOG
and positive-Riesz source-class bridges:

* mollification of a compact C2 test by compact SMOOTH tests
  (`exists_source_mollifier_pointwiseApproximation`);
* the geometric cutoff of a bounded C2 test by compact C2 tests, from the A
  draft `SourceLogCompactC2Cutoff` (`SourceLogCompactC2Approximation.toPointwise`;
  despite its draft name that construction is purely geometric).

Neither contains a measure, law, weak identity or desired conclusion. -/
noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped Topology ContDiff
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Mollification of a compact C2 test as a pointwise C2 approximation by
compact smooth tests. -/
lemma exists_source_mollifier_pointwiseApproximation (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    ∃ a : SourceC2PointwiseApproximation ψ,
      ∀ n, ContDiff ℝ ∞ (a.test n) ∧ HasCompactSupport (a.test n) := by
  obtain ⟨C, hC, hb⟩ := sourceMollify_deriv_bound ψ hψ hc
  exact ⟨⟨fun n => sourceMollify (ι := ι) n ψ,
      fun n => (sourceMollify_contDiff ψ hψ hc n).of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)),
      C, hC, hb,
      fun x => (sourceMollify_tendstoUniformly_value ψ hψ hc).tendsto_at x,
      sourceMollify_tendsto_gradient ψ hψ hc, sourceMollify_tendsto_laplacian ψ hψ hc⟩,
    fun n => ⟨sourceMollify_contDiff ψ hψ hc n, sourceMollify_hasCompactSupport ψ hψ hc n⟩⟩

/-- The cutoff approximation of the drafts is a special pointwise approximation;
recorded so that both routes visibly use one passage lemma. -/
def SourceLogCompactC2Approximation.toPointwise {φ : E → ℝ}
    (a : SourceLogCompactC2Approximation φ) : SourceC2PointwiseApproximation φ where
  test := a.test
  smooth := a.smooth
  bound := a.bound
  bound_nonneg := a.bound_nonneg
  deriv_bound := a.deriv_bound
  tendsto_value x := by
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq x] with n hn
    exact hn.eq_of_nhds.symm
  tendsto_gradient x := by
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq x] with n hn
    exact hn.gradient_eq.symm
  tendsto_laplacian x := by
    apply tendsto_const_nhds.congr'
    filter_upwards [a.local_eq x] with n hn
    exact (InnerProductSpace.laplacian_congr_nhds hn).eq_of_nhds.symm

/-- Every bounded C2 test is a pointwise limit of compact C2 tests with one
derivative bound. -/
lemma exists_source_cutoff_pointwiseApproximation (φ : E → ℝ) (hφ : SourceBoundedC2Test φ) :
    ∃ a : SourceC2PointwiseApproximation φ, ∀ n, HasCompactSupport (a.test n) := by
  obtain ⟨b⟩ := exists_sourceLogCompactC2Approximation φ hφ
  exact ⟨b.toPointwise, b.compact⟩

end DGRHS.Commutator
