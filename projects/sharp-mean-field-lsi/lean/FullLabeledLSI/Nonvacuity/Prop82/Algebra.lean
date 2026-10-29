import FullLabeledLSI.Nonvacuity.Prop82.Model
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar estimates in the Proposition 8.2 nonvacuity argument

These statements isolate genuine algebraic consequences. They neither assume
nor claim the existence of a quotient optimizer. In `compactness_bounds` the
strong circle deficit replaces the logarithmic coercivity argument and gives
explicit bounds `H < 6` and `I < 18 a` in physical coordinates.
-/

open Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

/-- The fourth-order coefficient calculation, in angular coordinates. This
polynomial identity is NOT the analytic assertion that the integrals have
these Taylor expansions. -/
theorem quartic_defect_identity (t : Real) :
    ((t ^ 2 / 2 + 11 * t ^ 4 / 200) + 2 * (t ^ 2 / 4) +
      (t ^ 2 / 8 - t ^ 4 / 80)) -
      3 * ((t ^ 2 / 4 + 13 * t ^ 4 / 800) + (t ^ 2 / 4) / 2) =
        -(t ^ 4) / 160 := by
  ring

/-- A sub-threshold quotient forces `I < 3 a H`. -/
theorem fisher_lt_three_entropy {a H I Q P : Real}
    (ha : 0 < a) (hQ : 0 ≤ Q) (hP : 0 ≤ P)
    (hlt : I + 2 * a * Q + P < 3 * a * (H + Q / 2)) :
    I < 3 * a * H := by
  nlinarith [mul_nonneg ha.le hQ]

/-- An explicit coercivity estimate, using only the quantitative LSI deficit. -/
theorem compactness_bounds {a H I : Real}
    (ha : 0 < a) (hH : 0 < H)
    (hdeficit : a / 6 * H ^ 2 ≤ I - 2 * a * H)
    (hI : I < 3 * a * H) : H < 6 ∧ I < 18 * a := by
  have hH6 : H < 6 := by
    by_contra h
    have h6 : 0 ≤ H - 6 := by linarith
    have hprod := mul_nonneg (mul_pos ha hH).le h6
    nlinarith
  refine ⟨hH6, ?_⟩
  have hprod := mul_pos ha (sub_pos.mpr hH6)
  nlinarith

/-- The elementary numerical comparison used in the second-harmonic estimate. -/
theorem log_two_lt_twenty_over_twentyseven : Real.log 2 < 20 / 27 := by
  linarith [Real.log_two_lt_d9]

/-- Entropy symmetrization and the entropy/moment bound imply the only moment
estimate required by the strict Poincare comparison. -/
theorem second_moment_lt_two_thirds {H Hs I beta : Real}
    (hsub : I < 3 * H)
    (hsym : 8 * Hs ≤ I)
    (hentropy : H ≤ Hs + Real.log 2)
    (hmoment : beta ^ 2 ≤ Hs) : |beta| < 2 / 3 := by
  have hH : Hs < 3 * Real.log 2 / 5 := by linarith
  have hb : beta ^ 2 < 4 / 9 := by
    linarith [log_two_lt_twenty_over_twentyseven]
  rw [abs_lt]
  constructor
  · by_contra h
    have hbeta : beta ≤ -(2 / 3 : Real) := by linarith
    have hh := sq_nonneg (beta + 2 / 3)
    nlinarith
  · by_contra h
    have hbeta : (2 / 3 : Real) ≤ beta := by linarith
    have hh := sq_nonneg (beta - 2 / 3)
    nlinarith

/-- Physical normalization of the heat-stationarity identity. -/
theorem score_energy_of_stationarity {a R Q I E beta : Real}
    (hstationary : 0 = -2 * E - 5 * a ^ 2 * Q +
      3 * a ^ 2 * Q * beta + 2 * R * (I + a * Q)) :
    E = R * I - a * Q * (5 * a / 2 - R - 3 * a * beta / 2) := by
  nlinarith

/-- Once the analytic stationarity identity and moment bound are supplied,
the strict inequality follows by ordered-field arithmetic, not by identifying
Poincare and mean-field constants by definition. -/
theorem score_energy_strict {a R Q I E beta : Real}
    (ha : 0 < a) (hQ : 0 < Q) (hR : R < a * (3 / 2))
    (hbeta : beta < 2 / 3)
    (henergy : E = R * I - a * Q * (5 * a / 2 - R - 3 * a * beta / 2)) :
    E < R * I := by
  have hb := mul_pos ha (sub_pos.mpr hbeta)
  have hfactor : 0 < 5 * a / 2 - R - 3 * a * beta / 2 := by
    nlinarith
  have hcorrection := mul_pos (mul_pos ha hQ) hfactor
  linarith

/-- A negative fourth-order limit gives a strict sign on a punctured
neighborhood. The existence of that limit is a separate analytic lemma. -/
theorem eventually_negative_of_quartic_limit {f : Real → Real} {a : Real}
    (ha : 0 < a)
    (hlim : Tendsto (fun t : Real => f t / t ^ 4)
      (𝓝[≠] 0) (𝓝 (-a / 160))) :
    ∀ᶠ t in 𝓝[≠] (0 : Real), f t < 0 := by
  have hneg : -a / 160 < 0 := by nlinarith
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : Real), f t / t ^ 4 < 0 :=
    hlim.eventually (gt_mem_nhds hneg)
  have hne : ∀ᶠ t in 𝓝[≠] (0 : Real), t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [hsmall, hne] with t ht ht0
  have ht4 : 0 < t ^ 4 := by positivity
  have := (div_lt_iff₀ ht4).mp ht
  simpa using this

end SharpLSI.FL.Prop82
