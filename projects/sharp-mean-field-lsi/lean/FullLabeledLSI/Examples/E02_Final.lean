import Lean
import FullLabeledLSI.Examples.E01_AttractiveStatements
import FullLabeledLSI.Examples.E01b_LaneA
import FullLabeledLSI.Examples.E01c_LaneB
import FullLabeledLSI.Examples.E01c2_LaneB
import FullLabeledLSI.Examples.E01f_Deficit
import FullLabeledLSI.Examples.E01f_OneSite
import FullLabeledLSI.Examples.E01f_SmallRate
import FullLabeledLSI.Examples.E01f_NearCritical
import FullLabeledLSI.Examples.E01g8_MinSeq
import FullLabeledLSI.Examples.E01g9_Attain
import FullLabeledLSI.Examples.E01h5_Concavity
import FullLabeledLSI.Examples.E01h9_Final

/-!
# Section 9 examples: final assembly check

The frozen statements of `E01_AttractiveStatements.lean` (13 theorems) keep their `sorry` proofs: that file is the
statement layer and is not edited.  The sorry-free proofs live in the lane files.  This module checks, for each of
the 13 statements,

1. that the proving theorem has *exactly* the type of the frozen statement (`type_of% … = type_of% … := rfl`), and
2. that the proving theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
   (`#assert_std_axioms` fails the build otherwise).
-/

open Lean Elab Command

/-- Fails if a constant depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`
(in particular on `sorryAx`). -/
elab "#assert_std_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do
      throwError "{n} depends on non-standard axioms {bad}"

namespace SharpLSI.FL.Ex

example : (type_of% @fourier_entropy_bound) = (type_of% @fourier_entropy_bound_proved) := rfl
example : (type_of% @first_attractive_cosine) = (type_of% @first_attractive_cosine_proved) := rfl
example : (type_of% @second_mode_remainder) = (type_of% @second_mode_remainder_proved) := rfl
example : (type_of% @second_harmonic_small) = (type_of% @LaneBb.second_harmonic_small_proved) := rfl
example : (type_of% @harmonic_deficit_attainment) = (type_of% @LaneC.harmonic_deficit_attainment) := rfl
example : (type_of% @harmonic_small_rate_uniqueness) = (type_of% @LaneC.harmonic_small_rate_uniqueness) := rfl
example : (type_of% @higher_near_critical) = (type_of% @LaneC.higher_near_critical) := rfl
example : (type_of% @interaction_concavity) = (type_of% @interaction_concavity_proved) := rfl
example : (type_of% @interaction_compensation) = (type_of% @interaction_compensation_proved) := rfl
example : (type_of% @scalar_quotient_attainment) = (type_of% @LaneD.scalar_quotient_attainment) := rfl
example : (type_of% @scalar_quotient_minimizing_sequence) =
    (type_of% @LaneD.scalar_quotient_minimizing_sequence) := rfl
example : (type_of% @nonlinear_equality) = (type_of% @LaneD.nonlinear_equality) := rfl
example : (type_of% @analytic_concavity) = (type_of% @LaneD.analytic_concavity) := rfl

#assert_std_axioms
  fourier_entropy_bound_proved first_attractive_cosine_proved second_mode_remainder_proved
  LaneBb.second_harmonic_small_proved LaneC.harmonic_deficit_attainment
  LaneC.harmonic_small_rate_uniqueness LaneC.higher_near_critical interaction_concavity_proved
  interaction_compensation_proved LaneD.scalar_quotient_attainment
  LaneD.scalar_quotient_minimizing_sequence LaneD.nonlinear_equality LaneD.analytic_concavity

#assert_std_axioms LaneC.harmonic_one_site_regularity

end SharpLSI.FL.Ex
