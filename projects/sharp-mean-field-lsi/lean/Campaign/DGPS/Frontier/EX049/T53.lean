import DGPS.Frontier.EX049.T03

/-!
# EX049.53: Periodic integrated square identity

Task id: EX049.53 (node EX049, leaf formalization, size M; prerequisite EX049.03, the angular
products and periodic integration by parts). Here `angHaar` is the normalized Haar probability
`dm = dθ/(2π)` of the angular circle `AngCircle`, and the derivative `g'` of the multiplier is the
circle derivative `angDeriv g`.

## Provides

- `DGPS.Frontier.EX049.ex049_53_periodic_integrated_square_identity`: for a smooth periodic real
  function `g` on the angular circle (`IsSmoothAngular g`) and a real angular `H¹` function `w`
  with weak derivative `w'` (`IsAngularWeakDeriv w w'`), the identity
  `∫ (w' + g w)² dm = ∫ ((w')² + (g² - g') w²) dm` holds, with no boundary term.

No helper declarations are introduced. The proof uses the EX049.03 declarations
`DGPS.Frontier.EX049.ibp_EX04903` (periodic integration by parts against a lifted `C¹` multiplier),
`DGPS.Frontier.EX049.sq_weak_EX04903` (weak derivative of `w²` is `w' w + w w'`), and the
EX049.35 and EX049.02 bookkeeping lemmas `memLp_bdd_mul_EX04935`, `continuous_of_coe_EX04935`
and `bdd_EX04903`.

## R5 notes

- Hypotheses. The statement has exactly two hypotheses: `IsSmoothAngular g` and
  `IsAngularWeakDeriv w w'`. Nothing else is assumed: no sign or positivity condition on `g`
  or `w`, no entropy or mass condition, and no boundedness of `w`. Integrability of every
  summand is proved inside the proof, not assumed.
- Smooth periodic `g`. The specification's "smooth periodic real `g`" is read as
  `IsSmoothAngular g`, that is, the lift `s ↦ g s` to `ℝ` is `C^∞`. Periodicity is built in,
  because `g` is a function on the circle `AngCircle = AddCircle (2π)`.
- Angular `H¹` function. The specification's "real angular `H¹` function `w`" is read as the
  pair `(w, w')` with `IsAngularWeakDeriv w w'` of EX049.02. This structure includes
  `MemLp w 2 angHaar` and `MemLp w' 2 angHaar`, the unweighted domain of EX049.02 (not the
  weighted `L²(μ_h)` domain). `AngularH1 w` is the existence of such a `w'`, so quantifying over
  every weak derivative `w'` of `w` covers every real angular `H¹` function `w`.
- The weak derivative. The statement holds for every weak derivative `w'` of `w`, not for a
  chosen representative. Weak derivatives are unique up to almost everywhere equality, and both
  sides depend on `w'` only through integrals, so this is the specification's `w'`. It is at
  least as strong as the literal reading.
- The derivative `g'`. It is `angDeriv g`, the circle derivative of EX049.35 and
  AngularNormalization. At every real representative it equals `deriv` of the lift.
- The measure `dm`. It is `angHaar`, the normalized Haar probability `dθ/(2π)` of the
  specification, not Lebesgue measure on `[0, 2π)`.
- Periodicity of the integration by parts. There is no boundary contribution, because the
  circle has no boundary. The identity `∫ g (w²)' = -∫ g' w²` is the periodic integration by
  parts of EX049.03 (`ibp_EX04903`), which uses the endpoint identification `2π = 0` on
  `AngCircle`. It is not assumed.
- Proof route. Pointwise, `(w' + g w)² = w'² + g (w' w + w w') + g² w²`, with `w' w + w w'`
  the weak derivative of `w²`. The cross term is integrated by `ibp_EX04903` with multiplier `g`,
  which gives `-∫ g' w²`. The three integrals are split with `integral_add` and `integral_sub`,
  using the integrability facts recorded in the proof.
-/

open MeasureTheory
open scoped ContDiff
open DGPS.Circle.AngularNormalization

namespace DGPS.Frontier.EX049

/-- Periodic integrated square identity (EX049.53). For a smooth periodic real function `g` on the
angular circle and a real angular `H¹` function `w` with weak derivative `w'`,
`∫ (w' + g w)² dm = ∫ ((w')² + (g² - g') w²) dm`, where `dm = angHaar` and
`g' = angDeriv g`. -/
theorem ex049_53_periodic_integrated_square_identity {g w w' : AngCircle → ℝ}
    (hg : IsSmoothAngular g) (hw : IsAngularWeakDeriv w w') :
    ∫ θ, (w' θ + g θ * w θ) ^ 2 ∂angHaar =
      ∫ θ, (w' θ ^ 2 + (g θ ^ 2 - angDeriv g θ) * w θ ^ 2) ∂angHaar := by
  have hgs : ContDiff ℝ ∞ (fun s : ℝ => g (s : AngCircle)) := hg
  have ha : ContDiff ℝ 1 (fun s : ℝ => g (s : AngCircle)) :=
    hgs.of_le (by exact_mod_cast le_top)
  have hgc : Continuous g := continuous_of_coe_EX04935 ha.continuous
  obtain ⟨M, hM⟩ := bdd_EX04903 hgc
  obtain ⟨hI1, hI2, hibp⟩ : Integrable (fun θ => g θ * (w' θ * w θ + w θ * w' θ)) angHaar ∧
      Integrable (fun θ => angDeriv g θ * w θ ^ 2) angHaar ∧
      ∫ θ, g θ * (w' θ * w θ + w θ * w' θ) ∂angHaar =
        -∫ θ, angDeriv g θ * w θ ^ 2 ∂angHaar :=
    ibp_EX04903 (L := g) ha (fun _ => rfl) hw (sq_weak_EX04903 hw)
  have hsq' : Integrable (fun θ => w' θ ^ 2) angHaar := hw.memLp_deriv.integrable_sq
  have hI3 : Integrable (fun θ => g θ ^ 2 * w θ ^ 2) angHaar :=
    (memLp_bdd_mul_EX04935 hgc hM hw.memLp).integrable_sq.congr
      (ae_of_all _ fun θ => by simp only [mul_pow])
  have e1 : (fun θ => (w' θ + g θ * w θ) ^ 2) =
      fun θ => (w' θ ^ 2 + g θ * (w' θ * w θ + w θ * w' θ)) + g θ ^ 2 * w θ ^ 2 := by
    funext θ
    ring
  have e2 : (fun θ => w' θ ^ 2 + (g θ ^ 2 - angDeriv g θ) * w θ ^ 2) =
      fun θ => w' θ ^ 2 + (g θ ^ 2 * w θ ^ 2 - angDeriv g θ * w θ ^ 2) := by
    funext θ
    ring
  have hA : Integrable (fun θ => w' θ ^ 2 + g θ * (w' θ * w θ + w θ * w' θ)) angHaar :=
    hsq'.add hI1
  have hC : Integrable (fun θ => g θ ^ 2 * w θ ^ 2 - angDeriv g θ * w θ ^ 2) angHaar :=
    hI3.sub hI2
  rw [e1, e2, integral_add hA hI3, integral_add hsq' hI1, integral_add hsq' hC,
    integral_sub hI3 hI2, hibp]
  ring

end DGPS.Frontier.EX049
