import DGPS.Frontier.FIN068.T18

/-!
Task id and title: FIN068.05, Exact jet (module `DGPS.Frontier.FIN068.T05`).

Provides:
* `DGPS.Frontier.FIN068.fin068_05_exact_jet`: with `J = liftPotential_FIN06804`, `b = quarticB`
  and `g'(4) = deriv besselRatio 4`, at `(u, z) = (0, 0)` the scalar partials are
  `J_u = 0`, `J_z = 0`, `J_uu = b/5 - g'(4)` (this is `A`), `J_uz = J_zu = -(b - 4 g'(4))/32`
  and `J_zz = (b - 4 g'(4))/256` (this is `d/256` with `d = b - 4 g'(4)`). Both mixed orders
  are stated.
* `DGPS.Frontier.FIN068.fin068_05_exact_jet_frechet`: the same values as Fréchet entries of
  `jetPotential_FIN06818` (the function `J` read on `EuclideanSpace ℝ (Fin 2)`), namely
  `fderiv ℝ jetPotential_FIN06818 0 eᵢ` and `fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 eᵢ eⱼ`
  for the standard basis vectors `e₀`, `e₁`.
* Helper declarations, all with suffix `_FIN06805` and not part of the interface:
  `inv_quarticKappa_FIN06805` (`1/κ = b/5`) and `inv_two_kappa_eta_FIN06805`
  (`1/(2κη) = b/8`).

Proof: FIN068.18 gives the jet of `J` in the forms `J_u = -5/κ + b`, `J_z = 1/(2κη) - b/8`,
`J_uu = 1/κ - g'(4)`, `J_uz = J_zu = g'(4)/8 - b/32`, `J_zz = b/256 - g'(4)/64`. The campaign
identities `κ = 5/b` and `η = 4/5` give `5/κ = b`, `1/κ = b/5` and `1/(2κη) = b/8`. Substituting
these and closing with `linear_combination` (ring arithmetic on the atoms `b`, `g'(4)`) gives
the stated values.

R5 notes:
* No hypothesis is added. Both statements are closed.
* `A` and `d` are written out in the statement as `quarticB / 5 - deriv besselRatio 4` and
  `quarticB - 4 * deriv besselRatio 4`, the node definitions `A = b/5 - g'(4)` and
  `d = b - 4 g'(4)`. FIN068.03 (`quarticA_FIN06803`, `quarticD_FIN06803`) is not imported,
  because it is not a listed prerequisite of this packet.
* The Proof paragraph of the specification writes `A` in the form `1/κ - g'(4)`. The statement
  uses `b/5 - g'(4)` instead, and the two agree by the helper `inv_quarticKappa_FIN06805`.
* `g'(4)` is read as `deriv besselRatio 4`, the derivative value and not the coordinate variable.
* The campaign constants are `quarticB = besselRatio 4`, `quarticKappa = 5 / quarticB` and
  `quarticEta = 4 / 5` (FIN065, `DGPS.FiniteN.QuarticSaddle`). The identities used hold without
  any positivity of `b`: they follow from the definitions by `one_div_div` and `ring`.
* The scalar partials are read as iterated one-variable derivatives of coordinate slices of
  `liftPotential_FIN06804 u z`, as in FIN068.18. `J_uz` differentiates in `u` first and `J_zu` in
  `z` first. Both are stated and proved separately, so no Schwarz symmetry is used.
* The specification's "mixed partials are equal" comment is not a separate claim here. Both
  mixed orders are part of the statement.
* Fréchet reading (added by this file, not literal): `J` is read on `EuclideanSpace ℝ (Fin 2)`
  with `w 0 = u` and `w 1 = z`, as in FIN068.17 and FIN068.18, and the entries are tested on
  `EuclideanSpace.single i 1`.
* The weighted `O(6)` remainder and the Morse-coordinate parts of the node are not in this packet.
-/

open DGPS.Models DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

lemma inv_quarticKappa_FIN06805 : 1 / quarticKappa = quarticB / 5 := by
  unfold quarticKappa
  exact one_div_div 5 quarticB

lemma five_div_quarticKappa_FIN06805 : 5 / quarticKappa = quarticB := by
  unfold quarticKappa
  rw [div_div_eq_mul_div]
  ring

lemma inv_two_kappa_eta_FIN06805 : 1 / (2 * quarticKappa * quarticEta) = quarticB / 8 := by
  have h : 2 * quarticKappa * quarticEta = 8 / quarticB := by
    unfold quarticKappa quarticEta
    ring
  rw [h, one_div_div]

/-- Main declaration. At `(u, z) = (0, 0)`, the scalar partials of `J = liftPotential_FIN06804`:
`J_u = J_z = 0`, `J_uu = A`, `J_uz = J_zu = -d/32`, `J_zz = d/256`, with `A` and `d` written out
as `quarticB / 5 - g'(4)` and `quarticB - 4 g'(4)`, where `g'(4) = deriv besselRatio 4`. -/
theorem fin068_05_exact_jet :
    deriv (fun t : ℝ => liftPotential_FIN06804 t 0) 0 = 0 ∧
    deriv (fun t : ℝ => liftPotential_FIN06804 0 t) 0 = 0 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 s 0) t) 0 =
      quarticB / 5 - deriv besselRatio 4 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 s t) 0) 0 =
      -(quarticB - 4 * deriv besselRatio 4) / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 t s) 0) 0 =
      -(quarticB - 4 * deriv besselRatio 4) / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 0 s) t) 0 =
      (quarticB - 4 * deriv besselRatio 4) / 256 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := fin068_18_assemble_jet_j
  have hk := five_div_quarticKappa_FIN06805
  have hi := inv_quarticKappa_FIN06805
  have hz := inv_two_kappa_eta_FIN06805
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, neg_div]
    linear_combination -hk
  · rw [h2]
    linear_combination hz
  · rw [h3]
    linear_combination hi
  · rw [h4]
    ring
  · rw [h5]
    ring
  · rw [h6]
    ring

/-- Main declaration, Fréchet reading. At the origin of `EuclideanSpace ℝ (Fin 2)`, the first
and second Fréchet entries of `jetPotential_FIN06818` (the function `J` with `w 0 = u`, `w 1 = z`)
have the values of `fin068_05_exact_jet`. -/
theorem fin068_05_exact_jet_frechet :
    fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 0 1) = 0 ∧
    fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 1 1) = 0 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 0 1) = quarticB / 5 - deriv besselRatio 4 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) = -(quarticB - 4 * deriv besselRatio 4) / 32 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 0 1) = -(quarticB - 4 * deriv besselRatio 4) / 32 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) = (quarticB - 4 * deriv besselRatio 4) / 256 := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, h12⟩ := fin068_18_assemble_jet_j
  have hk := five_div_quarticKappa_FIN06805
  have hi := inv_quarticKappa_FIN06805
  have hz := inv_two_kappa_eta_FIN06805
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h7, neg_div]
    linear_combination -hk
  · rw [h8]
    linear_combination hz
  · rw [h9]
    linear_combination hi
  · rw [h10]
    ring
  · rw [h11]
    ring
  · rw [h12]
    ring

end DGPS.Frontier.FIN068
