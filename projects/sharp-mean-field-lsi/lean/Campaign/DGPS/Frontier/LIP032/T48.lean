import DGPS.Frontier.LIP032.T43
import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.WeakContractions

/-!
# LIP032.48. Haar positive gap and literal zero score

Task id LIP032.48. Title: Haar positive gap and literal zero score.

The explicit model `A_*` on `𝕋¹` (LIP032.41, with `γ(x) = cos (2π x)`) and its free-energy minimum,
which is at most `-1/8` (LIP032.43), are used. The constant density `ρ_H = 1` relative to the
Haar probability measure `m = haar 1` is evaluated directly: its square root lies in `H¹`, its
free energy is zero, the gap `0 - E_{*,min}` is at least `1/8`, the equilibrium potential
`V_* + W_* * m` is the constant `2`, and the literal square-root score and its squared norm
integrate to zero.

## Provides

* `DGPS.Frontier.LIP032.rhoH_LIP03248`: the constant density `ρ_H = 1` on `𝕋¹`.
* `DGPS.Frontier.LIP032.haarMeasure_LIP03248`: the Haar measure `m = haar 1` as a `ProbabilityMeasure`.
* `DGPS.Frontier.LIP032.haarMeasure_coe_LIP03248`: the underlying measure of `haarMeasure_LIP03248` is `haar 1`.
* `DGPS.Frontier.LIP032.sqrt_rhoH_LIP03248`: the square root of `ρ_H` is the constant function `1`.
* `DGPS.Frontier.LIP032.mem_H1Haar_const_LIP03248`: every constant function lies in `H1Haar 1`.
* `DGPS.Frontier.LIP032.moment_haar_LIP03248`: the cosine moment of `m` is zero.
* `DGPS.Frontier.LIP032.integral_gammaStar_sq_LIP03248`: `∫ γ² dm = 1/2`.
* `DGPS.Frontier.LIP032.freeEnergy_haar_LIP03248`: the free energy of `m` is zero.
* `DGPS.Frontier.LIP032.gap_LIP03248`: `1/8 ≤ 0 - E_{*,min}` in `EReal`.
* `DGPS.Frontier.LIP032.integral_WStar_LIP03248`: `∫ W_*(x, y) dm(y) = 4 γ(x)² + 2`.
* `DGPS.Frontier.LIP032.potential_eq_two_LIP03248`: `V_*(x) + (W_* * m)(x) = 2` for every `x`.
* `DGPS.Frontier.LIP032.potential_eq_const_LIP03248`: the potential `V_* + W_* * m` is the constant function `2`.
* `DGPS.Frontier.LIP032.score_zero_ae_LIP03248`: for any weak gradients `g` of `√ρ_H` and `h` of the potential, `2 g + √ρ_H h = 0` `m`-a.e.
* `DGPS.Frontier.LIP032.lip032_48_haar_positive_gap_literal_zero_score`: the main statement (LIP032.48).

## R5 notes

* Density. `ρ_H` is the plain function `fun _ => 1` on `Torus 1`, relative to `m = haar 1`. The
  campaign structures `AbsoluteDensity`, `densityMeasure` and `scalarDissipation` are not used, so
  the statement does not depend on any campaign representation choice. "Square root in `H¹`" is read
  as membership of the function `√ρ_H` in `H1Haar 1` (an `L²` weak gradient exists).
* Free energy. "Free energy zero" is `freeEnergy interactionDataStar_LIP03241 haarMeasure_LIP03248 = 0`
  in `EReal`, with the entropy term the campaign `relativeEntropy` in `ℝ≥0∞`. The Haar entropy is
  computed as `relativeEntropy m m = 0` (`relativeEntropy_self`), not as an explicit integral `∫ 1 log 1 dm`.
* Gap. `E_{*,min}` is read as `freeEnergyMinimum interactionDataStar_LIP03241`, the infimum over
  probability measures in `EReal`. The gap `0 - E_{*,min}` is taken in `EReal`. It is finite and
  at least `1/8` because LIP032.43 gives a real value `r ≤ -1/8`.
* Potential. `W_* * m` is read as `x ↦ ∫ W_*(x, y) dm(y)`, the integral against `m` in the second
  variable. The identity `V_* + W_* * m = 2` is proved pointwise for every `x`, which is stronger than
  an almost-everywhere statement. The Haar trigonometric integrals used are `∫ γ dm = 0` and `∫ γ² dm = 1/2`.
* Score. `∇` is read as the campaign `L²` weak gradient `IsWeakGradient` on the torus, with respect
  to `m`. The score is quantified over all weak gradients `g` of `√ρ_H` and `h` of `V_* + W_* * m`.
  Weak gradients are unique only almost everywhere (`IsWeakGradient.ae_eq`), so the scalar identity
  holds `m`-almost everywhere; no pointwise identity is claimed for an arbitrary representative.
  The dissipation `∫ |·|² dm` uses the Euclidean norm on `Tangent 1 = EuclideanSpace ℝ (Fin 1)`.
* Added conjuncts (not hypotheses). The statement also asserts `√ρ_H ∈ H1Haar 1` and
  `V_* + W_* * m ∈ H1Haar 1`. These are provable and make the universally quantified score clause
  non-vacuous, since they guarantee that weak gradients exist. They strengthen the conclusion
  relative to the bare list of assertions in the specification and are recorded here for audit.
* No hypotheses. The statement has no positive-rate, flow or LIP031 hypothesis. None is listed for
  LIP032.48 in the specification, and the proof uses none. No hypothesis is added or strengthened.
* Domain. The model is the explicit one-dimensional model on `Torus 1` only. `m = haar 1` is the mass-one
  Haar measure, and `dm` is integration against `haar 1`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-- The constant density `ρ_H = 1` on `𝕋¹`. -/
def rhoH_LIP03248 : Torus 1 → ℝ := fun _ => 1

/-- The Haar measure `m = haar 1` as a probability measure. -/
noncomputable def haarMeasure_LIP03248 : ProbabilityMeasure (Torus 1) :=
  ⟨haar 1, inferInstance⟩

/-- The underlying measure of `haarMeasure_LIP03248` is `haar 1`. -/
theorem haarMeasure_coe_LIP03248 :
    (haarMeasure_LIP03248 : Measure (Torus 1)) = haar 1 :=
  rfl

/-- The square root of the constant density `ρ_H = 1` is the constant function `1`. -/
theorem sqrt_rhoH_LIP03248 :
    (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x)) = fun _ => 1 := by
  funext x
  simp [rhoH_LIP03248]

/-- Every constant function on `𝕋¹` lies in `H¹(m)`, with weak gradient zero. -/
theorem mem_H1Haar_const_LIP03248 (c : ℝ) : (fun _ : Torus 1 => c) ∈ H1Haar 1 :=
  mem_H1Haar.2
    (⟨fun _ => 0, isWeakGradient_const (d := 1) c⟩ :
      ∃ g, IsWeakGradient (fun _ : Torus 1 => c) g)

/-- The cosine moment of the Haar measure is zero. -/
theorem moment_haar_LIP03248 : momentStar_LIP03241 (haar 1) = 0 := by
  unfold momentStar_LIP03241
  simp only [gammaStar_eq_gammaCos_LIP03243]
  exact integral_gammaCos_LIP03242

/-- The second moment `∫ γ² dm` of the Haar measure is `1/2`. -/
theorem integral_gammaStar_sq_LIP03248 :
    ∫ y, gammaStar_LIP03241 y ^ 2 ∂haar 1 = 1 / 2 := by
  simp only [gammaStar_eq_gammaCos_LIP03243]
  exact integral_gammaCos_sq_LIP03242

/-- The free energy of the Haar measure is zero: its entropy is `0` and its moment is `0`. -/
theorem freeEnergy_haar_LIP03248 :
    freeEnergy interactionDataStar_LIP03241 haarMeasure_LIP03248 = 0 := by
  rw [energy_LIP03241 haarMeasure_LIP03248, haarMeasure_coe_LIP03248, moment_haar_LIP03248,
    relativeEntropy_self]
  simp

/-- The gap `0 - E_{*,min}` is at least `1/8`, by LIP032.43. -/
theorem gap_LIP03248 :
    ((1 / 8 : ℝ) : EReal) ≤ (0 : EReal) - freeEnergyMinimum interactionDataStar_LIP03241 := by
  obtain ⟨r, hr, hr8⟩ := lip032_43_strict_negative_minimum_nonzero_cosine_moments.2.1
  rw [hr, ← EReal.coe_zero, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

/-- The Haar integral of the two-body interaction: `∫ W_*(x, y) dm(y) = 4 γ(x)² + 2`. -/
theorem integral_WStar_LIP03248 (x : Torus 1) :
    ∫ y, WStar_LIP03241 x y ∂haar 1 = 4 * gammaStar_LIP03241 x ^ 2 + 2 := by
  have hγ : Continuous gammaStar_LIP03241 := continuous_gammaStar_LIP03241
  have hfun : (fun y => WStar_LIP03241 x y) =
      fun y => (4 * gammaStar_LIP03241 x ^ 2 - (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y) +
        4 * gammaStar_LIP03241 y ^ 2 := by
    funext y
    unfold WStar_LIP03241
    ring
  have hI1 : Integrable
      (fun y => 4 * gammaStar_LIP03241 x ^ 2 - (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y)
      (haar 1) :=
    integrable_of_continuous_LIP03241 (haar 1) (continuous_const.sub (continuous_const.mul hγ))
  have hI2 : Integrable (fun y => 4 * gammaStar_LIP03241 y ^ 2) (haar 1) :=
    integrable_of_continuous_LIP03241 (haar 1) (continuous_const.mul (hγ.pow 2))
  have hI3 : Integrable (fun y => (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y) (haar 1) :=
    integrable_of_continuous_LIP03241 (haar 1) (continuous_const.mul hγ)
  have hA : ∫ y, (4 * gammaStar_LIP03241 x ^ 2 - (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y)
      ∂haar 1 = 4 * gammaStar_LIP03241 x ^ 2 := by
    rw [integral_sub (integrable_const _) hI3, integral_const, integral_const_mul,
      show ∫ y, gammaStar_LIP03241 y ∂haar 1 = momentStar_LIP03241 (haar 1) from rfl,
      moment_haar_LIP03248]
    simp
  have hB : ∫ y, 4 * gammaStar_LIP03241 y ^ 2 ∂haar 1 = 2 := by
    rw [integral_const_mul, integral_gammaStar_sq_LIP03248]
    norm_num
  rw [hfun, integral_add hI1 hI2, hA, hB]

/-- The equilibrium potential is the constant `2`: `V_*(x) + (W_* * m)(x) = 2` for every `x`. -/
theorem potential_eq_two_LIP03248 (x : Torus 1) :
    VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1 = 2 := by
  rw [integral_WStar_LIP03248]
  unfold VStar_LIP03241
  ring

/-- The potential `V_* + W_* * m` is the constant function `2`. -/
theorem potential_eq_const_LIP03248 :
    (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1) = fun _ => 2 :=
  funext potential_eq_two_LIP03248

/-- The literal square-root score vanishes `m`-almost everywhere, for any weak gradients. -/
theorem score_zero_ae_LIP03248 (g h : Torus 1 → Tangent 1)
    (hg : IsWeakGradient (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x)) g)
    (hh : IsWeakGradient
      (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1) h) :
    ∀ᵐ x ∂haar 1, (2 : ℝ) • g x + Real.sqrt (rhoH_LIP03248 x) • h x = 0 := by
  rw [sqrt_rhoH_LIP03248] at hg
  rw [potential_eq_const_LIP03248] at hh
  have hg0 := hg.ae_eq (isWeakGradient_const (d := 1) (1 : ℝ))
  have hh0 := hh.ae_eq (isWeakGradient_const (d := 1) (2 : ℝ))
  filter_upwards [hg0, hh0] with x hx1 hx2
  simp [hx1, hx2, rhoH_LIP03248]

/-- **LIP032.48.** Haar positive gap and literal zero score. The density `ρ_H = 1` has square root
in `H¹`, free energy zero, and gap `0 - E_{*,min} ≥ 1/8`. The potential `V_* + W_* * m` is the
constant `2`, and it has the square-root score `2 ∇√ρ_H + √ρ_H ∇(V_* + W_* * m) = 0` `m`-a.e., with
`∫ |·|² dm = 0`. The `H¹` membership of the potential is an added conjunct; see the R5 notes. -/
theorem lip032_48_haar_positive_gap_literal_zero_score :
    (∀ x : Torus 1, rhoH_LIP03248 x = 1) ∧
    (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x)) ∈ H1Haar 1 ∧
    freeEnergy interactionDataStar_LIP03241 haarMeasure_LIP03248 = 0 ∧
    ((1 / 8 : ℝ) : EReal) ≤ (0 : EReal) - freeEnergyMinimum interactionDataStar_LIP03241 ∧
    (∀ x : Torus 1, VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1 = 2) ∧
    (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1) ∈ H1Haar 1 ∧
    ∀ g h : Torus 1 → Tangent 1,
      IsWeakGradient (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x)) g →
      IsWeakGradient (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1) h →
      (∀ᵐ x ∂haar 1, (2 : ℝ) • g x + Real.sqrt (rhoH_LIP03248 x) • h x = 0) ∧
      ∫ x, ‖(2 : ℝ) • g x + Real.sqrt (rhoH_LIP03248 x) • h x‖ ^ 2 ∂haar 1 = 0 := by
  refine ⟨fun _ => rfl, ?_, freeEnergy_haar_LIP03248, gap_LIP03248, potential_eq_two_LIP03248,
    ?_, ?_⟩
  · rw [sqrt_rhoH_LIP03248]
    exact mem_H1Haar_const_LIP03248 1
  · rw [potential_eq_const_LIP03248]
    exact mem_H1Haar_const_LIP03248 2
  · intro g h hg hh
    have hscore := score_zero_ae_LIP03248 g h hg hh
    refine ⟨hscore, ?_⟩
    have hz : (fun x : Torus 1 => ‖(2 : ℝ) • g x + Real.sqrt (rhoH_LIP03248 x) • h x‖ ^ 2) =ᵐ[haar 1] 0 := by
      filter_upwards [hscore] with x hx
      simp [hx]
    exact integral_eq_zero_of_ae hz

end DGPS.Frontier.LIP032
