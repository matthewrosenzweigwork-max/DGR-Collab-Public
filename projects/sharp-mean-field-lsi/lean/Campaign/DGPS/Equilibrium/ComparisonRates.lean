import DGPS.Analysis.RelativeFisher
import DGPS.Equilibrium.GaussianRate
import DGPS.Variational.FrozenGibbs

/-!
# The two-sector rate and the unrestricted comparison rate (DEF028)

INTERFACES/definitions.md §6, common_lemmas.md DEF028; `PINNED_MANUSCRIPT/examples.tex`
eq:two-sector-gap, eq:two-sector-dissipation; `DGPS_Lipschitz_Proof` eq:lambdaG-note.

For a bounded positive reference `μ = P` (a probability `P = w m`) with coercive density Hessian:

* `twoSectorRate A P hH = min {λ_G, λ_P(P)}` (`gaussianRate`, `poincareRate`): the rate of the
  infinitesimal species expansion, the ratio of the Dirichlet quadratic form to the covariance
  (Hessian-inverse) form on the mean and on the equal-and-opposite contrasts;
* `unrestrictedComparisonRate A P hH = min {λ_G, r_LS(P)}` (`gaussianRate`, `ordinaryLSRate`): the
  separate comparison rate `b` of the unrestricted ordinary LSI comparison (T01).

The two are different definitions: `λ_P(P)` is the Poincaré rate, `r_LS(P)` the ordinary LSI rate
(`ordinaryLSRate`).  Both are valued in `ℝ≥0∞`, like `gaussianRate`.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- DEF028: the two-sector (infinitesimal species) rate `λ_two = min {λ_G, λ_P(μ)}` of the
bounded positive reference `μ = P`, under coercivity of the density Hessian. -/
noncomputable def twoSectorRate (A : InteractionData d) (P : BoundedPositiveReference d)
    (hcoercive : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) : ℝ≥0∞ :=
  min (gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ hcoercive)
    (poincareRate ⟨P.measure, P.isProbabilityMeasure⟩)

/-- DEF028: the unrestricted comparison rate `b = min {λ_G, r_LS(μ)}` of the bounded positive
reference `μ = P`, under coercivity of the density Hessian.  Not interchangeable with
`twoSectorRate`: it uses the ordinary LSI rate in place of the Poincaré rate. -/
noncomputable def unrestrictedComparisonRate (A : InteractionData d) (P : BoundedPositiveReference d)
    (hcoercive : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) : ℝ≥0∞ :=
  min (gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ hcoercive) (ordinaryLSRate P)

theorem twoSectorRate_le_gaussianRate (A : InteractionData d) (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) :
    twoSectorRate A P h ≤ gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ h :=
  min_le_left _ _

theorem twoSectorRate_le_poincareRate (A : InteractionData d) (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) :
    twoSectorRate A P h ≤ poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ :=
  min_le_right _ _

theorem unrestrictedComparisonRate_le_gaussianRate (A : InteractionData d)
    (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) :
    unrestrictedComparisonRate A P h ≤ gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ h :=
  min_le_left _ _

theorem unrestrictedComparisonRate_le_ordinaryLSRate (A : InteractionData d)
    (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) :
    unrestrictedComparisonRate A P h ≤ ordinaryLSRate P :=
  min_le_right _ _

theorem le_twoSectorRate_iff (A : InteractionData d) (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) (r : ℝ≥0∞) :
    r ≤ twoSectorRate A P h ↔
      r ≤ gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ h ∧
        r ≤ poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ :=
  le_min_iff

theorem le_unrestrictedComparisonRate_iff (A : InteractionData d) (P : BoundedPositiveReference d)
    (h : IsCoerciveDensityHessian A ⟨P.measure, P.isProbabilityMeasure⟩) (r : ℝ≥0∞) :
    r ≤ unrestrictedComparisonRate A P h ↔
      r ≤ gaussianRate A ⟨P.measure, P.isProbabilityMeasure⟩ h ∧ r ≤ ordinaryLSRate P :=
  le_min_iff

end DGPS
