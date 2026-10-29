import FullLabeledLSI.Nonvacuity.Prop82.ExplicitTrial
import FullLabeledLSI.Nonvacuity.Prop82.Score
import FullLabeledLSI.Nonvacuity.Prop82.Compactness
import SharpSymmetricLSI.Paper.AppAEvol2

/-!
# The explicitly conditional assembly, and the remaining analytic obligations

IMPORTANT: this file does NOT prove `Nonvacuous` without extra assumptions.
`AnalyticSteps` is an ordinary proposition with four fields. No inhabitant of
it, no instance, and no axiom supplying it is declared. Each field is an
analytic part of the informal proof still awaiting its own Lean proof.

`#print axioms nonvacuity_of_analytic_steps` cannot certify that those fields
have been proved: they are hypotheses of the theorem, not axioms. Read its
full type, which retains the argument `(h : AnalyticSteps)`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

noncomputable def cosMoment (rho : Torus 1 → Real) : Real :=
  ∫ x, gCos x * rho x ∂haar 1

noncomputable def sinMoment (rho : Torus 1 → Real) : Real :=
  ∫ x, sCos x * rho x ∂haar 1

/-- The second harmonic in the direction of the first moment. On `Q > 0`
this is `Re (exp (-2 i arg M) M2)`. The quotient is used only with `Q > 0`. -/
noncomputable def alignedSecondMoment (rho : Torus 1 → Real) : Real :=
  (∫ x, rho x *
    ((cosMoment rho ^ 2 - sinMoment rho ^ 2) * c2 x +
      4 * cosMoment rho * sinMoment rho * gCos x * sCos x) ∂haar 1) /
    firstMode rho

noncomputable def halfTurn : Torus 1 :=
  fun _ => ((1 / 2 : Real) : UnitAddCircle)

noncomputable def halfSymmetrize (rho : Torus 1 → Real) (x : Torus 1) : Real :=
  (rho x + rho (x + halfTurn)) / 2

/-- OPEN: the nonlinear direct method, INCLUDING exclusion of a zero-gap
limit. Rellich extraction alone (`Compactness.lean`) does not prove this. -/
def AttainmentBelowThreshold : Prop :=
  realRate < aCos * (3 / 2) → ∃ rho : Torus 1 → Real, RawOptimizer rho

/-- OPEN: the Euler--Lagrange regularity and no-zero argument. This asks only
for a smooth positive representative; transporting attainment is proved below. -/
def PositiveSmoothRepresentative : Prop :=
  ∀ rho : Torus 1 → Real, RawOptimizer rho →
    ∃ sigma : Torus 1 → Real,
      rho =ᵐ[haar 1] sigma ∧ SmoothProbability sigma

/-- OPEN: Fisher convexity under the half-turn average, the doubled-frequency
circle LSI, entropy loss at most `log 2`, and the oriented second-moment entropy
bound. The finiteness condition is included before `toReal` is interpreted. -/
def HalfTurnEntropyEstimates : Prop :=
  ∀ rho : Torus 1 → Real, SmoothProbability rho →
    klDiv (densMeasure (halfSymmetrize rho)) (haar 1) ≠ ⊤ ∧
    8 * aCos * entropy (halfSymmetrize rho) ≤ fisher rho ∧
    entropy rho ≤ entropy (halfSymmetrize rho) + Real.log 2 ∧
    (0 < firstMode rho → alignedSecondMoment rho ^ 2 ≤ entropy (halfSymmetrize rho))

/-- OPEN: differentiating `D - 2 r G` along the heat direction at the smooth
optimizer, with both the interaction derivative and the Fisher derivative.
Every quantity below is in physical coordinates. -/
def HeatStationarity : Prop :=
  ∀ rho : Torus 1 → Real, SmoothOptimizer rho → 0 < firstMode rho →
    0 = -2 * scoreEnergy rho - 5 * aCos ^ 2 * firstMode rho +
      3 * aCos ^ 2 * firstMode rho * alignedSecondMoment rho +
      2 * realRate * (fisher rho + aCos * firstMode rho)

/-- These are explicit inputs, not a typeclass and not an axiom package.
The current development supplies NO proof of this proposition. -/
structure AnalyticSteps : Prop where
  attainment : AttainmentBelowThreshold
  regularity : PositiveSmoothRepresentative
  halfTurnEstimates : HalfTurnEntropyEstimates
  heatStationarity : HeatStationarity

/-- Almost-everywhere representative changes preserve the original gap and
dissipation. Smoothness and pointwise positivity are supplied for the new
representative, not falsely inferred for the original function. -/
theorem RawOptimizer.toSmooth {rho sigma : Torus 1 → Real}
    (h : RawOptimizer rho) (hae : rho =ᵐ[haar 1] sigma)
    (hsigma : SmoothProbability sigma) : SmoothOptimizer sigma := by
  have hm := SharpLSI.densMeasure_congr_ae hae
  have hD := SharpLSI.dissipation_congr_ae (V := cosV) (W := cosW 1) hae
  refine ⟨hsigma, ?_, ?_⟩
  · rw [← hm]
    exact h.1.2.2.2
  · rw [← hm, ← hD]
    exact h.2

/-- The numeric second-moment bound follows from the precise entropy inputs. -/
theorem second_moment_bound_of_halfTurn_estimates
    (hhalf : HalfTurnEntropyEstimates) {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) (hR : realRate < aCos * (3 / 2))
    (hQ : 0 < firstMode rho) : |alignedSecondMoment rho| < 2 / 3 := by
  obtain ⟨hfinite, hsym, hent, hmoment⟩ := hhalf rho h.probability
  have hquot : realDiss rho / (2 * realGap rho) < aCos * (3 / 2) := by
    rw [h.raw.real_quotient]
    exact hR
  have hI := (subthreshold_bounds h.admissible hquot).1
  have hsub : fisher rho / aCos < 3 * entropy rho := by
    apply (div_lt_iff₀ a_pos).mpr
    nlinarith
  have h8 : 8 * entropy (halfSymmetrize rho) ≤ fisher rho / aCos := by
    apply (le_div_iff₀ a_pos).mpr
    nlinarith
  exact second_moment_lt_two_thirds hsub h8 hent (hmoment hQ)

/-- Both Poincare branches refer to the SAME optimizer. The zero-first-moment
branch is unconditional apart from `SmoothProbability`; the nonzero branch
uses the two still-open analytic inputs stated above. -/
theorem optimizer_poincare_strict_of_analytic_steps
    (hhalf : HalfTurnEntropyEstimates) (hheat : HeatStationarity)
    (hR : realRate < aCos * (3 / 2)) {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) : poincareConst (densMeasure rho) < mfRate := by
  by_cases hQ : firstMode rho = 0
  · exact poincare_lt_rate_of_firstMode_zero h.probability hQ
  · have hQpos : 0 < firstMode rho :=
      lt_of_le_of_ne (firstMode_nonneg rho) (Ne.symm hQ)
    have hb : alignedSecondMoment rho < 2 / 3 :=
      (le_abs_self _).trans_lt (second_moment_bound_of_halfTurn_estimates hhalf h hR hQpos)
    have hstat := hheat rho h hQpos
    rw [fisher_eq_score_variance h.probability] at hstat
    exact poincare_lt_rate_of_score_data h.probability
      (scoreTest_smooth h.probability) (scoreTest_mean_zero h.probability)
      (scoreTest_variance_pos h) hQpos hR hb hstat

/-- CONDITIONAL ASSEMBLY, not the unconditional nonvacuity theorem.
To finish the requested formalization, construct `h : AnalyticSteps` from the
original library, with no new axioms, placeholders, or extra mathematical
assumptions, and then apply this theorem. -/
theorem nonvacuity_of_analytic_steps (h : AnalyticSteps) : Nonvacuous := by
  have hR := realRate_lt_threshold
  obtain ⟨rho, hrho⟩ := h.attainment hR
  obtain ⟨sigma, hae, hsigma⟩ := h.regularity rho hrho
  have hopt := hrho.toSmooth hae hsigma
  exact nonvacuous_iff.mpr ⟨sigma, hopt,
    optimizer_poincare_strict_of_analytic_steps
      h.halfTurnEstimates h.heatStationarity hR hopt⟩

/-- A downstream application, still explicitly conditional on all four
unproved analytic fields. -/
theorem obstruction_of_analytic_steps (h : AnalyticSteps) :
    Tendsto (fun N => rAll cosV (cosW 1) N) atTop (𝓝 (rMs cosV (cosW 1))) ∧
    rMs cosV (cosW 1) < mfRate ∧
    Tendsto (fun N => rSym cosV (cosW 1) N) atTop (𝓝 mfRate) := by
  obtain ⟨rho, hrho, hP⟩ := nonvacuous_iff.mp (nonvacuity_of_analytic_steps h)
  exact obstruction_of_witness hrho hP

end SharpLSI.FL.Prop82
