import DGPS.Frontier.LIP032.T41
import DGPS.Frontier.LIP032.T42
import DGPS.Variational.EquilibriumGibbs

/-!
# LIP032.43: Strict negative minimum and nonzero cosine moments

Task id and title: LIP032.43, "Strict negative minimum and nonzero cosine moments" (node LIP032,
contractibility of the minimizer set; leaf formalization of the explicit counterexample model on
the circle).

## Provides
* `DGPS.Frontier.LIP032.trialMeasure_LIP03243` : the probability measure `μ_{f_*}` of the explicit
  trial density `f_* = 1 + γ/2` of LIP032.42, packaged as a `ProbabilityMeasure (Torus 1)`.
* `DGPS.Frontier.LIP032.trialMeasure_coe_LIP03243` : its underlying measure is
  `densityMeasure_LIP03218 trialDensity_LIP03242`.
* `DGPS.Frontier.LIP032.gammaStar_eq_gammaCos_LIP03243` : pointwise agreement of the cosine of
  LIP032.41 (`gammaStar_LIP03241`) and the cosine of LIP032.42 (`gammaCos_LIP03242`).
* `DGPS.Frontier.LIP032.gammaStar_eq_gammaCos_fun_LIP03243` : the same agreement as an equality of
  functions.
* `DGPS.Frontier.LIP032.moment_trial_LIP03243` : the cosine moment `M(μ_{f_*})` equals `1/4`.
* `DGPS.Frontier.LIP032.freeEnergy_trial_le_LIP03243` : `F_{A_*}(μ_{f_*}) ≤ -1/8` in `EReal`.
* `DGPS.Frontier.LIP032.freeEnergyMinimum_le_LIP03243` : the free-energy minimum `F_{A_*,min}` of
  the explicit model satisfies `F_{A_*,min} ≤ -1/8` in `EReal`.
* `DGPS.Frontier.LIP032.entropy_ne_top_of_minimizer_LIP03243` : every minimizer of `F_{A_*}` has
  finite relative entropy with respect to `m`.
* `DGPS.Frontier.LIP032.moment_sq_bound_LIP03243` : every minimizer `ν` satisfies `1/32 ≤ M(ν)²`.
* `DGPS.Frontier.LIP032.moment_ne_zero_LIP03243` : every minimizer `ν` satisfies `M(ν) ≠ 0`.
* `DGPS.Frontier.LIP032.lip032_43_strict_negative_minimum_nonzero_cosine_moments` : MAIN. The
  conjunction of (1) the minimizing set is nonempty, (2) the minimum is a real number `r` with
  `r ≤ -1/8`, and (3) every minimizer `ν` satisfies `1/32 ≤ M(ν)²` and `M(ν) ≠ 0`.

## R5 notes
* The model is the explicit interaction data `A_* = interactionDataStar_LIP03241` of LIP032.41:
  `γ(x) = cos(2π x)` on `𝕋¹`, `V_* = -4γ²`, `W_*(x, y) = 4 (γ x - γ y)²`. The statement concerns
  this model only. It is not the general contractibility statement of the node, and no property of
  the general model is assumed.
* No hypothesis is assumed. The statement has no positive-rate, flow, mean-field, interaction-
  gradient or LIP031 input. The specification classes this unit as a counterexample task, which
  does not assume a positive rate; the LIP031 header (`hr`, `hrate`, `hu`) is not referenced here.
  The Lipschitz data of `A_*` is proved in LIP032.41 and is not needed by this statement.
* The minimum `E_{*,min}` is `freeEnergyMinimum A_*`, an infimum in `EReal` over all Borel
  probability measures on `𝕋¹`. "Finite real minimum" is read as
  `∃ r : ℝ, freeEnergyMinimum A_* = (r : EReal)`. This finiteness is taken from LIP017
  (`DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity`, conjunct 2). Only conjuncts 1 and 2 of
  LIP017 are used; its Gibbs identity (conjunct 3) is not used.
* "Nonempty minimizing set" is read as the existence of a `ProbabilityMeasure` `ν` with
  `freeEnergy A_* ν = freeEnergyMinimum A_*`, again from LIP017, conjunct 1.
* The bound `E_{*,min} ≤ -1/8` is proved through the trial measure `μ_{f_*}` of LIP032.42. Its
  entropy is at most `1/8` and not infinite, and its cosine moment is `1/4`. The energy identity
  `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²` of LIP032.41 then gives `1/8 - 4 (1/4)² = -1/8`. The
  minimality of the infimum gives the bound for `E_{*,min}`.
* The entropy `H(ν | m)` is `DGPS.relativeEntropy` with values in `ENNReal`. "Finite entropy of a
  minimizer" is read as `≠ ⊤`. It is derived from the finiteness of the minimum through
  `DGPS.finiteFreeEnergy_iff`; it is not assumed. The real value `H.toReal` is nonnegative.
* The cosine moment `M(ν)` is `momentStar_LIP03241 (ν : Measure (Torus 1))`, the integral
  `∫ γ dν`. The inequality `1/32 ≤ M(ν)²` is claimed for minimizers only, not for every probability
  measure. The conclusion `M(ν) ≠ 0` is derived from that inequality.
* The arithmetic is carried out in `ℝ`: the `EReal` identities are converted through
  `EReal.coe_ennreal_toReal`, `EReal.coe_sub` and `EReal.coe_le_coe_iff` (or `EReal.coe_eq_coe_iff`)
  only after finiteness of the entropy has been established.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-- The probability measure `μ_{f_*}` of the explicit trial density `f_* = 1 + γ/2` (LIP032.42). -/
noncomputable def trialMeasure_LIP03243 : ProbabilityMeasure (Torus 1) :=
  ⟨densityMeasure_LIP03218 trialDensity_LIP03242,
    lip032_42_explicit_positive_trial_density_probability⟩

/-- The underlying measure of `trialMeasure_LIP03243` is the density measure of `f_*`. -/
theorem trialMeasure_coe_LIP03243 :
    (trialMeasure_LIP03243 : Measure (Torus 1)) =
      densityMeasure_LIP03218 trialDensity_LIP03242 :=
  rfl

/-- The cosine of LIP032.41 and the cosine of LIP032.42 agree at every point of `𝕋¹`. -/
theorem gammaStar_eq_gammaCos_LIP03243 (x : Torus 1) :
    gammaStar_LIP03241 x = gammaCos_LIP03242 x := by
  obtain ⟨a, rfl⟩ := exists_lift_LIP03241 x
  have ha : a = fun _ : Fin 1 => a 0 := funext fun i => congrArg a (Subsingleton.elim i 0)
  rw [gammaStar_lift_LIP03241, ← gammaCos_lift_LIP03242 (a 0)]
  exact congrArg (fun y => gammaCos_LIP03242 (torusLift y)) ha.symm

/-- The two cosine functions agree. -/
theorem gammaStar_eq_gammaCos_fun_LIP03243 : gammaStar_LIP03241 = gammaCos_LIP03242 :=
  funext gammaStar_eq_gammaCos_LIP03243

/-- The cosine moment of the trial measure is `1/4`. -/
theorem moment_trial_LIP03243 :
    momentStar_LIP03241 (trialMeasure_LIP03243 : Measure (Torus 1)) = 1 / 4 := by
  rw [trialMeasure_coe_LIP03243]
  unfold momentStar_LIP03241
  rw [gammaStar_eq_gammaCos_fun_LIP03243]
  exact lip032_42_explicit_positive_trial_density_moment

/-- The free energy of the trial measure is at most `-1/8`. The entropy is finite, so the
`EReal` arithmetic reduces to real arithmetic. -/
theorem freeEnergy_trial_le_LIP03243 :
    freeEnergy interactionDataStar_LIP03241 trialMeasure_LIP03243 ≤
      ((-(1 / 8) : ℝ) : EReal) := by
  have hH := lip032_42_explicit_positive_trial_density_entropy
  have hne : DGPS.relativeEntropy (trialMeasure_LIP03243 : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
    rw [trialMeasure_coe_LIP03243]
    exact hH.2
  have hreal :
      (DGPS.relativeEntropy (trialMeasure_LIP03243 : Measure (Torus 1)) (haar 1)).toReal ≤
        1 / 8 := by
    rw [trialMeasure_coe_LIP03243]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hH.1
  have h4 : (4 : ℝ) * (1 / 4) ^ 2 = 1 / 4 := by norm_num
  rw [energy_LIP03241 trialMeasure_LIP03243, moment_trial_LIP03243,
    ← EReal.coe_ennreal_toReal hne, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith [hreal, h4]

/-- The free-energy minimum of the explicit model is at most `-1/8`. -/
theorem freeEnergyMinimum_le_LIP03243 :
    freeEnergyMinimum interactionDataStar_LIP03241 ≤ ((-(1 / 8) : ℝ) : EReal) :=
  (iInf_le (fun ν : ProbabilityMeasure (Torus 1) => freeEnergy interactionDataStar_LIP03241 ν)
    trialMeasure_LIP03243).trans freeEnergy_trial_le_LIP03243

/-- Every minimizer of the explicit free energy has finite relative entropy. The finiteness comes
from the finiteness of the free-energy minimum (LIP017), not from an assumption on `ν`. -/
theorem entropy_ne_top_of_minimizer_LIP03243 (ν : ProbabilityMeasure (Torus 1))
    (hν : freeEnergy interactionDataStar_LIP03241 ν =
      freeEnergyMinimum interactionDataStar_LIP03241) :
    DGPS.relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
  obtain ⟨r, hr⟩ :=
    (DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity interactionDataStar_LIP03241).2.1
  exact (DGPS.finiteFreeEnergy_iff interactionDataStar_LIP03241 ν).1
    (Exists.intro r (hν.trans hr))

/-- Every minimizer `ν` of the explicit free energy satisfies `1/32 ≤ M(ν)²`. -/
theorem moment_sq_bound_LIP03243 (ν : ProbabilityMeasure (Torus 1))
    (hν : freeEnergy interactionDataStar_LIP03241 ν =
      freeEnergyMinimum interactionDataStar_LIP03241) :
    1 / 32 ≤ momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2 := by
  obtain ⟨r, hr⟩ :=
    (DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity interactionDataStar_LIP03241).2.1
  have hne := entropy_ne_top_of_minimizer_LIP03243 ν hν
  have hE := energy_LIP03241 ν
  rw [hν, hr, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at hE
  have hmin := freeEnergyMinimum_le_LIP03243
  rw [hr] at hmin
  have hr8 : r ≤ -(1 / 8) := EReal.coe_le_coe_iff.1 hmin
  have hpos : 0 ≤ (DGPS.relativeEntropy (ν : Measure (Torus 1)) (haar 1)).toReal :=
    ENNReal.toReal_nonneg
  linarith

/-- Every minimizer `ν` of the explicit free energy has nonzero cosine moment. -/
theorem moment_ne_zero_LIP03243 (ν : ProbabilityMeasure (Torus 1))
    (hν : freeEnergy interactionDataStar_LIP03241 ν =
      freeEnergyMinimum interactionDataStar_LIP03241) :
    momentStar_LIP03241 (ν : Measure (Torus 1)) ≠ 0 := by
  intro h0
  have h := moment_sq_bound_LIP03243 ν hν
  rw [h0] at h
  norm_num at h

/-- **LIP032.43.** Strict negative minimum and nonzero cosine moments for the explicit model
`A_*`. The minimizing set is nonempty; the free-energy minimum is a real number `r` with
`r ≤ -1/8`; and every minimizer `ν` has `1/32 ≤ M(ν)²`, in particular `M(ν) ≠ 0`. -/
theorem lip032_43_strict_negative_minimum_nonzero_cosine_moments :
    (∃ ν : ProbabilityMeasure (Torus 1),
        freeEnergy interactionDataStar_LIP03241 ν =
          freeEnergyMinimum interactionDataStar_LIP03241) ∧
      (∃ r : ℝ, freeEnergyMinimum interactionDataStar_LIP03241 = (r : EReal) ∧ r ≤ -(1 / 8)) ∧
      ∀ ν : ProbabilityMeasure (Torus 1),
        freeEnergy interactionDataStar_LIP03241 ν =
            freeEnergyMinimum interactionDataStar_LIP03241 →
          1 / 32 ≤ momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2 ∧
            momentStar_LIP03241 (ν : Measure (Torus 1)) ≠ 0 := by
  have hLIP :=
    DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity interactionDataStar_LIP03241
  refine ⟨hLIP.1, ?_, fun ν hν => ⟨moment_sq_bound_LIP03243 ν hν, moment_ne_zero_LIP03243 ν hν⟩⟩
  obtain ⟨r, hr⟩ := hLIP.2.1
  refine ⟨r, hr, ?_⟩
  have hmin := freeEnergyMinimum_le_LIP03243
  rw [hr] at hmin
  exact EReal.coe_le_coe_iff.1 hmin

end DGPS.Frontier.LIP032
