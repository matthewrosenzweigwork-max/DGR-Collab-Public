import DGPS.Model.FreeEnergy
import DGPS.Analysis.CircleMoments

/-!
# LIP032.41: Smooth model and exact one-moment energy

Task id and title: LIP032.41, "Smooth model and exact one-moment energy" (node LIP032, contractibility
of the minimizer set; leaf formalization of the explicit model on the circle).

## Provides
* `DGPS.Frontier.LIP032.gammaStar_LIP03241`, `VStar_LIP03241`, `WStar_LIP03241`,
  `momentStar_LIP03241` (definitions): `γ(x) = cos (2π x)` on `𝕋¹` (the campaign mode `cosMode`),
  `V_* = -4 γ²`, `W_*(x, y) = 4 (γ x - γ y)²`, and the moment `M(ν) = ∫ γ dν`.
* `DGPS.Frontier.LIP032.interactionDataStar_LIP03241` (definition): the explicit interaction data
  `A_* : InteractionData 1` with `A_*.V = V_*` and `A_*.W = W_*`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy`: MAIN. The conjunction of
  the statements below: `γ` is the cosine of the lift, `γ`, `V_*` are smooth periodic and `W_*` has
  a smooth periodic lift to `ℝ¹ × ℝ¹`, `W_*` is symmetric and vanishes on the diagonal,
  `|V_*| ≤ 4`, `|W_*| ≤ 16`, the one-body and two-body Lipschitz estimates with constants `16π` and
  `32π`, the joint Lipschitz bound `64π` for the Euclidean quotient product metric and for the usual
  product metric, `A_*` has the data `V_*`, `W_*` and satisfies `LipschitzData`, and for every
  Borel probability `ν` the integrands are integrable, the real part
  `∫ V_* dν + (1/2) ∬ W_* d(ν ⊗ ν)` equals `-4 M(ν)²`, and `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²` in
  `EReal`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_smooth`: smoothness and the
  lift formula for `γ`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_symm_diag`: symmetry and
  vanishing on the diagonal of `W_*`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_bounds`: the sup bounds
  `|V_*| ≤ 4` and `|W_*| ≤ 16`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_lipschitz`: the Lipschitz
  estimates for `V_*` and `W_*` and the joint bounds `64π`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_data`: the explicit data
  `A_*` and `LipschitzData A_*`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_potential_part`: for every
  probability measure `ν` on the torus, the integrability of the integrands and the real identity
  `∫ V_* dν + (1/2) ∬ W_* d(ν ⊗ ν) = -4 M(ν)²`.
* `DGPS.Frontier.LIP032.lip032_41_smooth_model_exact_one_moment_energy_energy`: the identity
  `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²` in `EReal`, for every `ν : ProbabilityMeasure (𝕋¹)`.

## R5 notes
* The specification's `cos (2π x)` for `x ∈ 𝕋¹` is read as the periodic function whose lift to `ℝ`
  is `s ↦ cos (2π s)`. It is the campaign function `cosMode` (the real part of the first Fourier
  mode), whose lift formula `cosMode (torusLift y) = cos (2π y 0)` is a conjunct of the main
  statement, so the definition is pinned down by the specification.
* "Smooth periodic" for `γ` and `V_*` is the campaign predicate `IsSmoothPeriodic` (the lift to
  `Fin 1 → ℝ` is `C^∞`). For `W_*`, a function of two torus points, no campaign predicate exists;
  it is read as `C^∞` of the lift `(s, t) ↦ W_*(lift s, lift t)` on `(Fin 1 → ℝ) × (Fin 1 → ℝ)`.
* The metric `d` of the Lipschitz estimates for `V_*` and for the two-variable sum form is the
  Euclidean quotient distance `torusDist`, as in `LipschitzData`. The "Euclidean quotient product
  metric" is `√(torusDist x x'² + torusDist y y'²)`, the form used in `LipschitzData`. The "usual
  product metric" is Mathlib's metric on `Torus 1 × Torus 1` (the maximum of the sup-metric
  distances of the components), and the joint bound is stated for `dist p q`. On `𝕋¹` the sup
  metric and `torusDist` agree up to the factor `√1 = 1` given by `torusDist_comparison`; the bound
  with the usual product metric follows from the one with `torusDist` through the inequality
  `torusDist ≤ dist`. The joint constant `64π` is the same in both forms, as in the specification.
* "These functions supply the explicit interaction data `A_*`": `A_*` is the structure
  `interactionDataStar_LIP03241` whose fields are `V_*`, `W_*` and the continuity, symmetry and
  diagonal proofs. The main statement records `A_*.V = V_*`, `A_*.W = W_*` and
  `LipschitzData A_*`, with `LipschitzData` the campaign property (existence of the constants).
* "The interaction part finite": in the campaign free energy the potential parts are real numbers
  (`potentialEnergy`, `interactionEnergy` are real integrals), so no infinite values occur there.
  This is recorded by the integrability of `V_*` against `ν` and of `W_*` against `ν ⊗ ν`, and by
  the real identity `potentialEnergy A_* ν + (1/2) * interactionEnergy A_* ν = -(4 * M(ν) ^ 2)`.
* The energy identity is the equality in `EReal`
  `freeEnergy A_* ν = ↑(relativeEntropy ν (haar 1)) - ↑(4 * M(ν) ^ 2)`, with the entropy the
  `ℝ≥0∞`-valued campaign relative entropy coerced to `EReal`, which may be `⊤`. The subtraction of
  the real number `4 M(ν)²` is `EReal` subtraction; it never subtracts two infinite values.
* The moment `M(ν) = ∫ γ dν` is stated for the underlying measure of a probability, with
  `momentStar_LIP03241` defined on `Measure (Torus 1)`.
* No positive-rate, flow, gradient or other hypothesis of the node is used or assumed: the task is
  pure model construction and product-integral algebra, and no statement issue arises. No
  hypothesis is added to the specification.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.Frontier.LIP032

/-- The first harmonic `γ(x) = cos (2π x)` on `𝕋¹`, the campaign function `cosMode`. -/
noncomputable def gammaStar_LIP03241 (x : Torus 1) : ℝ :=
  DGPS.Analysis.CircleMoments.cosMode x

/-- The one-body potential `V_* = -4 γ²`. -/
noncomputable def VStar_LIP03241 (x : Torus 1) : ℝ :=
  -4 * gammaStar_LIP03241 x ^ 2

/-- The two-body interaction `W_*(x, y) = 4 (γ x - γ y)²`. -/
noncomputable def WStar_LIP03241 (x y : Torus 1) : ℝ :=
  4 * (gammaStar_LIP03241 x - gammaStar_LIP03241 y) ^ 2

/-- The first moment `M(ν) = ∫ γ dν` of a measure on the circle. -/
noncomputable def momentStar_LIP03241 (ν : Measure (Torus 1)) : ℝ :=
  ∫ x, gammaStar_LIP03241 x ∂ν

/-! ### The function `γ` -/

/-- The lift formula `γ (lift s) = cos (2π s)`. -/
theorem gammaStar_lift_LIP03241 (y : Fin 1 → ℝ) :
    gammaStar_LIP03241 (torusLift y) = Real.cos (2 * Real.pi * y 0) :=
  DGPS.Analysis.CircleMoments.cosMode_lift y

theorem continuous_gammaStar_LIP03241 : Continuous gammaStar_LIP03241 :=
  DGPS.Analysis.CircleMoments.continuous_cosMode

theorem abs_gammaStar_le_LIP03241 (x : Torus 1) : |gammaStar_LIP03241 x| ≤ 1 :=
  DGPS.Analysis.CircleMoments.abs_cosMode_le x

theorem abs_gammaStar_sub_le_LIP03241 (x y : Torus 1) :
    |gammaStar_LIP03241 x - gammaStar_LIP03241 y| ≤ 2 := by
  have hx := abs_gammaStar_le_LIP03241 x
  have hy := abs_gammaStar_le_LIP03241 y
  rw [abs_le] at hx hy ⊢
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem isSmoothPeriodic_gammaStar_LIP03241 : IsSmoothPeriodic gammaStar_LIP03241 :=
  DGPS.Analysis.CircleMoments.isSmoothPeriodic_cosMode

/-- Every point of `𝕋¹` is the lift of a real point. -/
theorem exists_lift_LIP03241 (x : Torus 1) : ∃ a : Fin 1 → ℝ, torusLift a = x :=
  ⟨SharpLSI.secT x, SharpLSI.liftT_secT x⟩

/-- Shifting the lift by an integer does not change the point of the torus. -/
theorem lift_add_int_LIP03241 (b : Fin 1 → ℝ) (k : ℤ) :
    torusLift (fun i => b i + (k : ℝ)) = torusLift b := by
  funext i
  have hk0 : ((k : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨k, by simp⟩
  show (((b i + (k : ℝ) : ℝ)) : UnitAddCircle) = ((b i : ℝ) : UnitAddCircle)
  rw [AddCircle.coe_add, hk0, add_zero]

/-- `γ` is `2π`-Lipschitz for the Euclidean quotient distance. -/
theorem gammaStar_lipschitz_LIP03241 (x x' : Torus 1) :
    |gammaStar_LIP03241 x - gammaStar_LIP03241 x'| ≤ 2 * Real.pi * torusDist x x' := by
  obtain ⟨a, rfl⟩ := exists_lift_LIP03241 x
  obtain ⟨b, rfl⟩ := exists_lift_LIP03241 x'
  set k : ℤ := round (a 0 - b 0) with hk
  have hshift := lift_add_int_LIP03241 b k
  have hh : ∀ j : Fin 1, |a j - (fun i => b i + (k : ℝ)) j| ≤ 1 / 2 := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have h := abs_sub_round (a 0 - b 0)
    have e : a 0 - (b 0 + (k : ℝ)) = a 0 - b 0 - (round (a 0 - b 0) : ℝ) := by
      rw [hk]; ring
    show |a 0 - (b 0 + (k : ℝ))| ≤ 1 / 2
    rw [e]
    exact h
  have hd : torusDist (torusLift a) (torusLift b) = |a 0 - (b 0 + (k : ℝ))| := by
    rw [← hshift, torusDist_liftT_eq hh]
    simp [Real.sqrt_sq_eq_abs]
  have hgb : gammaStar_LIP03241 (torusLift b) = Real.cos (2 * Real.pi * (b 0 + (k : ℝ))) := by
    rw [← hshift]
    exact gammaStar_lift_LIP03241 _
  rw [gammaStar_lift_LIP03241, hgb, hd]
  calc |Real.cos (2 * Real.pi * a 0) - Real.cos (2 * Real.pi * (b 0 + (k : ℝ)))|
      ≤ |2 * Real.pi * a 0 - 2 * Real.pi * (b 0 + (k : ℝ))| := Real.abs_cos_sub_cos_le _ _
    _ = 2 * Real.pi * |a 0 - (b 0 + (k : ℝ))| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- On `𝕋¹` the Euclidean quotient distance is at most the sup distance. -/
theorem torusDist_le_dist_LIP03241 (x y : Torus 1) : torusDist x y ≤ dist x y := by
  have h := (torusDist_comparison x y).2
  simpa using h

/-- A continuous real function on a compact space is integrable for a finite measure. -/
theorem integrable_of_continuous_LIP03241 {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### The potentials -/

theorem continuous_VStar_LIP03241 : Continuous VStar_LIP03241 :=
  continuous_const.mul (continuous_gammaStar_LIP03241.pow 2)

theorem continuous_WStar_LIP03241 :
    Continuous fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2 :=
  continuous_const.mul
    (((continuous_gammaStar_LIP03241.comp continuous_fst).sub
      (continuous_gammaStar_LIP03241.comp continuous_snd)).pow 2)

theorem WStar_symm_LIP03241 (x y : Torus 1) : WStar_LIP03241 x y = WStar_LIP03241 y x := by
  unfold WStar_LIP03241
  ring

theorem WStar_diag_LIP03241 (x : Torus 1) : WStar_LIP03241 x x = 0 := by
  unfold WStar_LIP03241
  ring

theorem abs_VStar_le_LIP03241 (x : Torus 1) : |VStar_LIP03241 x| ≤ 4 := by
  have h := abs_gammaStar_le_LIP03241 x
  have h2 : gammaStar_LIP03241 x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (gammaStar_LIP03241 x)]
  unfold VStar_LIP03241
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (gammaStar_LIP03241 x)]

theorem abs_WStar_le_LIP03241 (x y : Torus 1) : |WStar_LIP03241 x y| ≤ 16 := by
  have h := abs_gammaStar_sub_le_LIP03241 x y
  have h2 : (gammaStar_LIP03241 x - gammaStar_LIP03241 y) ^ 2 ≤ 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (gammaStar_LIP03241 x - gammaStar_LIP03241 y)]
  unfold WStar_LIP03241
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (gammaStar_LIP03241 x - gammaStar_LIP03241 y)]

theorem VStar_lipschitz_LIP03241 (x x' : Torus 1) :
    |VStar_LIP03241 x - VStar_LIP03241 x'| ≤ 16 * Real.pi * torusDist x x' := by
  have hl := gammaStar_lipschitz_LIP03241 x x'
  have hx := abs_gammaStar_le_LIP03241 x
  have hx' := abs_gammaStar_le_LIP03241 x'
  have hs : |gammaStar_LIP03241 x + gammaStar_LIP03241 x'| ≤ 2 := by
    rw [abs_le] at hx hx' ⊢
    constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have e : VStar_LIP03241 x - VStar_LIP03241 x' =
      -4 * ((gammaStar_LIP03241 x - gammaStar_LIP03241 x') *
        (gammaStar_LIP03241 x + gammaStar_LIP03241 x')) := by
    unfold VStar_LIP03241
    ring
  rw [e, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h0 : 0 ≤ |gammaStar_LIP03241 x - gammaStar_LIP03241 x'| := abs_nonneg _
  calc 4 * (|gammaStar_LIP03241 x - gammaStar_LIP03241 x'| *
        |gammaStar_LIP03241 x + gammaStar_LIP03241 x'|)
      ≤ 4 * (|gammaStar_LIP03241 x - gammaStar_LIP03241 x'| * 2) := by
        gcongr
    _ ≤ 4 * ((2 * Real.pi * torusDist x x') * 2) := by gcongr
    _ = 16 * Real.pi * torusDist x x' := by ring

theorem WStar_lipschitz_LIP03241 (x y x' y' : Torus 1) :
    |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
      32 * Real.pi * (torusDist x x' + torusDist y y') := by
  have hl1 := gammaStar_lipschitz_LIP03241 x x'
  have hl2 := gammaStar_lipschitz_LIP03241 y y'
  have hD := abs_gammaStar_sub_le_LIP03241 x y
  have hD' := abs_gammaStar_sub_le_LIP03241 x' y'
  set D := gammaStar_LIP03241 x - gammaStar_LIP03241 y with hDdef
  set D' := gammaStar_LIP03241 x' - gammaStar_LIP03241 y' with hD'def
  have hs : |D + D'| ≤ 4 := by
    rw [abs_le] at hD hD' ⊢
    constructor <;> linarith [hD.1, hD.2, hD'.1, hD'.2]
  have hdiff : |D - D'| ≤ 2 * Real.pi * (torusDist x x' + torusDist y y') := by
    have e : D - D' = (gammaStar_LIP03241 x - gammaStar_LIP03241 x') -
        (gammaStar_LIP03241 y - gammaStar_LIP03241 y') := by
      rw [hDdef, hD'def]; ring
    rw [e]
    calc |(gammaStar_LIP03241 x - gammaStar_LIP03241 x') -
          (gammaStar_LIP03241 y - gammaStar_LIP03241 y')|
        ≤ |gammaStar_LIP03241 x - gammaStar_LIP03241 x'| +
          |gammaStar_LIP03241 y - gammaStar_LIP03241 y'| := abs_sub _ _
      _ ≤ 2 * Real.pi * torusDist x x' + 2 * Real.pi * torusDist y y' := add_le_add hl1 hl2
      _ = 2 * Real.pi * (torusDist x x' + torusDist y y') := by ring
  have e : WStar_LIP03241 x y - WStar_LIP03241 x' y' = 4 * ((D - D') * (D + D')) := by
    unfold WStar_LIP03241
    rw [hDdef, hD'def]; ring
  rw [e, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h0 : 0 ≤ |D - D'| := abs_nonneg _
  calc 4 * (|D - D'| * |D + D'|)
      ≤ 4 * (|D - D'| * 4) := by gcongr
    _ ≤ 4 * ((2 * Real.pi * (torusDist x x' + torusDist y y')) * 4) := by gcongr
    _ = 32 * Real.pi * (torusDist x x' + torusDist y y') := by ring

/-- `a + b ≤ 2 √(a² + b²)` for real `a, b`. -/
theorem add_le_two_sqrt_LIP03241 (a b : ℝ) :
    a + b ≤ 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : (a + b) ^ 2 ≤ (2 * Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  exact (abs_le_of_sq_le_sq' h (by positivity)).2

/-- The joint Lipschitz bound `64π` for the Euclidean quotient product metric. -/
theorem WStar_lipschitz_euclid_LIP03241 (x y x' y' : Torus 1) :
    |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
      64 * Real.pi * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by
  refine (WStar_lipschitz_LIP03241 x y x' y').trans ?_
  have h := add_le_two_sqrt_LIP03241 (torusDist x x') (torusDist y y')
  have hp : 0 ≤ 32 * Real.pi := by positivity
  calc 32 * Real.pi * (torusDist x x' + torusDist y y')
      ≤ 32 * Real.pi * (2 * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :=
        mul_le_mul_of_nonneg_left h hp
    _ = 64 * Real.pi * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by ring

/-- The joint Lipschitz bound `64π` for the usual (maximum) product metric. -/
theorem WStar_lipschitz_prod_LIP03241 (p q : Torus 1 × Torus 1) :
    |WStar_LIP03241 p.1 p.2 - WStar_LIP03241 q.1 q.2| ≤ 64 * Real.pi * dist p q := by
  refine (WStar_lipschitz_LIP03241 p.1 p.2 q.1 q.2).trans ?_
  have h1 : torusDist p.1 q.1 ≤ dist p q :=
    (torusDist_le_dist_LIP03241 _ _).trans (by rw [Prod.dist_eq]; exact le_max_left _ _)
  have h2 : torusDist p.2 q.2 ≤ dist p q :=
    (torusDist_le_dist_LIP03241 _ _).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  have hp : 0 ≤ 32 * Real.pi := by positivity
  calc 32 * Real.pi * (torusDist p.1 q.1 + torusDist p.2 q.2)
      ≤ 32 * Real.pi * (dist p q + dist p q) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hp
    _ = 64 * Real.pi * dist p q := by ring

/-! ### The explicit interaction data -/

/-- The explicit interaction data `A_* = (V_*, W_*)` on `𝕋¹`. -/
noncomputable def interactionDataStar_LIP03241 : InteractionData 1 where
  V := VStar_LIP03241
  W := WStar_LIP03241
  V_continuous := continuous_VStar_LIP03241
  W_continuous := continuous_WStar_LIP03241
  W_symm := WStar_symm_LIP03241
  W_diag := WStar_diag_LIP03241

theorem lipschitzData_interactionDataStar_LIP03241 :
    LipschitzData interactionDataStar_LIP03241 := by
  refine ⟨⟨16 * Real.pi, fun x y => ?_⟩, ⟨64 * Real.pi, fun x y x' y' => ?_⟩⟩
  · exact VStar_lipschitz_LIP03241 x y
  · exact WStar_lipschitz_euclid_LIP03241 x y x' y'

/-! ### The exact one-moment energy -/

/-- The real part of the free energy of `A_*`: `∫ V_* dν + (1/2) ∬ W_* d(ν ⊗ ν) = -4 M(ν)²`,
together with the integrability of the two integrands. -/
theorem potential_part_LIP03241 (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    Integrable VStar_LIP03241 μ ∧
      Integrable (fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2) (μ.prod μ) ∧
      potentialEnergy interactionDataStar_LIP03241 μ +
        (1 / 2 : ℝ) * interactionEnergy interactionDataStar_LIP03241 μ =
      -(4 * momentStar_LIP03241 μ ^ 2) := by
  have hγ := continuous_gammaStar_LIP03241
  have hP1 : Integrable (fun p : Torus 1 × Torus 1 => gammaStar_LIP03241 p.1 ^ 2) (μ.prod μ) :=
    integrable_of_continuous_LIP03241 _ ((hγ.comp continuous_fst).pow 2)
  have hP2 : Integrable (fun p : Torus 1 × Torus 1 => gammaStar_LIP03241 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_continuous_LIP03241 _ ((hγ.comp continuous_snd).pow 2)
  have hP3 : Integrable
      (fun p : Torus 1 × Torus 1 => gammaStar_LIP03241 p.1 * gammaStar_LIP03241 p.2)
      (μ.prod μ) :=
    integrable_of_continuous_LIP03241 _ ((hγ.comp continuous_fst).mul (hγ.comp continuous_snd))
  have hsum : Integrable
      (fun p : Torus 1 × Torus 1 => gammaStar_LIP03241 p.1 ^ 2 + gammaStar_LIP03241 p.2 ^ 2)
      (μ.prod μ) := hP1.add hP2
  have hVint : Integrable VStar_LIP03241 μ :=
    integrable_of_continuous_LIP03241 μ continuous_VStar_LIP03241
  have hWint : Integrable (fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2) (μ.prod μ) :=
    integrable_of_continuous_LIP03241 _ continuous_WStar_LIP03241
  refine ⟨hVint, hWint, ?_⟩
  have hpot : potentialEnergy interactionDataStar_LIP03241 μ =
      -4 * ∫ x, gammaStar_LIP03241 x ^ 2 ∂μ := by
    unfold potentialEnergy
    exact integral_const_mul (-4 : ℝ) (fun x => gammaStar_LIP03241 x ^ 2)
  have hW : (fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2) = fun p =>
      4 * (gammaStar_LIP03241 p.1 ^ 2 + gammaStar_LIP03241 p.2 ^ 2 -
        2 * (gammaStar_LIP03241 p.1 * gammaStar_LIP03241 p.2)) := by
    funext p
    unfold WStar_LIP03241
    ring
  have hint : interactionEnergy interactionDataStar_LIP03241 μ =
      4 * ((∫ x, gammaStar_LIP03241 x ^ 2 ∂μ) + (∫ x, gammaStar_LIP03241 x ^ 2 ∂μ) -
        2 * (momentStar_LIP03241 μ) ^ 2) := by
    unfold interactionEnergy
    show ∫ p : Torus 1 × Torus 1, WStar_LIP03241 p.1 p.2 ∂(μ.prod μ) = _
    rw [hW, integral_const_mul, integral_sub hsum (hP3.const_mul 2),
      integral_add hP1 hP2, integral_const_mul]
    have e1 : ∫ p : Torus 1 × Torus 1, gammaStar_LIP03241 p.1 ^ 2 ∂(μ.prod μ) =
        ∫ x, gammaStar_LIP03241 x ^ 2 ∂μ := by
      rw [integral_fun_fst (fun x => gammaStar_LIP03241 x ^ 2)]
      simp
    have e2 : ∫ p : Torus 1 × Torus 1, gammaStar_LIP03241 p.2 ^ 2 ∂(μ.prod μ) =
        ∫ x, gammaStar_LIP03241 x ^ 2 ∂μ := by
      rw [integral_fun_snd (fun x => gammaStar_LIP03241 x ^ 2)]
      simp
    have e3 : ∫ p : Torus 1 × Torus 1, gammaStar_LIP03241 p.1 * gammaStar_LIP03241 p.2
        ∂(μ.prod μ) = (momentStar_LIP03241 μ) ^ 2 := by
      rw [integral_prod_mul gammaStar_LIP03241 gammaStar_LIP03241]
      unfold momentStar_LIP03241
      ring
    rw [e1, e2, e3]
  rw [hpot, hint]
  ring

/-- The identity `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²` in `EReal`. -/
theorem energy_LIP03241 (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy interactionDataStar_LIP03241 ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) -
        ((4 * momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2 : ℝ) : EReal) := by
  have h := (potential_part_LIP03241 (ν : Measure (Torus 1))).2.2
  unfold freeEnergy
  rw [add_assoc, ← EReal.coe_add, h, EReal.coe_neg, sub_eq_add_neg]

/-! ### Public statements -/

/-- Smoothness: the lift formula for `γ`, and `γ`, `V_*` smooth periodic, `W_*` with smooth lift. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_smooth :
    (∀ y : Fin 1 → ℝ, gammaStar_LIP03241 (torusLift y) = Real.cos (2 * Real.pi * y 0)) ∧
      IsSmoothPeriodic gammaStar_LIP03241 ∧ IsSmoothPeriodic VStar_LIP03241 ∧
      ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        WStar_LIP03241 (torusLift p.1) (torusLift p.2)) := by
  have hg : ContDiff ℝ ∞ (gammaStar_LIP03241 ∘ torusLift) := isSmoothPeriodic_gammaStar_LIP03241
  refine ⟨gammaStar_lift_LIP03241, isSmoothPeriodic_gammaStar_LIP03241, ?_, ?_⟩
  · show ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => -4 * gammaStar_LIP03241 (torusLift y) ^ 2)
    exact contDiff_const.mul (hg.pow 2)
  · show ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      4 * (gammaStar_LIP03241 (torusLift p.1) - gammaStar_LIP03241 (torusLift p.2)) ^ 2)
    exact contDiff_const.mul ((hg.comp contDiff_fst |>.sub (hg.comp contDiff_snd)).pow 2)

/-- Symmetry of `W_*` and vanishing on the diagonal. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_symm_diag :
    (∀ x y, WStar_LIP03241 x y = WStar_LIP03241 y x) ∧ ∀ x, WStar_LIP03241 x x = 0 :=
  ⟨WStar_symm_LIP03241, WStar_diag_LIP03241⟩

/-- The sup bounds `|V_*| ≤ 4` and `|W_*| ≤ 16`. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_bounds :
    (∀ x, |VStar_LIP03241 x| ≤ 4) ∧ ∀ x y, |WStar_LIP03241 x y| ≤ 16 :=
  ⟨abs_VStar_le_LIP03241, abs_WStar_le_LIP03241⟩

/-- The Lipschitz estimates for `V_*` and `W_*`, and the joint bounds `64π` for the Euclidean
quotient product metric and for the usual product metric. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_lipschitz :
    (∀ x x', |VStar_LIP03241 x - VStar_LIP03241 x'| ≤ 16 * Real.pi * torusDist x x') ∧
      (∀ x y x' y', |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
        32 * Real.pi * (torusDist x x' + torusDist y y')) ∧
      (∀ x y x' y', |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
        64 * Real.pi * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) ∧
      ∀ p q : Torus 1 × Torus 1,
        |WStar_LIP03241 p.1 p.2 - WStar_LIP03241 q.1 q.2| ≤ 64 * Real.pi * dist p q :=
  ⟨VStar_lipschitz_LIP03241, WStar_lipschitz_LIP03241, WStar_lipschitz_euclid_LIP03241,
    WStar_lipschitz_prod_LIP03241⟩

/-- The explicit interaction data `A_*` has the potentials `V_*`, `W_*` and is Lipschitz. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_data :
    interactionDataStar_LIP03241.V = VStar_LIP03241 ∧
      interactionDataStar_LIP03241.W = WStar_LIP03241 ∧
      LipschitzData interactionDataStar_LIP03241 :=
  ⟨rfl, rfl, lipschitzData_interactionDataStar_LIP03241⟩

/-- For every probability measure, the integrands are integrable and the real part of the free
energy is `-4 M(ν)²`. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_potential_part
    (ν : ProbabilityMeasure (Torus 1)) :
    Integrable VStar_LIP03241 (ν : Measure (Torus 1)) ∧
      Integrable (fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2)
        ((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) ∧
      potentialEnergy interactionDataStar_LIP03241 (ν : Measure (Torus 1)) +
        (1 / 2 : ℝ) * interactionEnergy interactionDataStar_LIP03241 (ν : Measure (Torus 1)) =
      -(4 * momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2) :=
  potential_part_LIP03241 (ν : Measure (Torus 1))

/-- The exact one-moment energy identity `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²` in `EReal`. -/
theorem lip032_41_smooth_model_exact_one_moment_energy_energy
    (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy interactionDataStar_LIP03241 ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) -
        ((4 * momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2 : ℝ) : EReal) :=
  energy_LIP03241 ν

/-- MAIN (LIP032.41). The explicit smooth model `(γ, V_*, W_*)` on `𝕋¹` and the exact one-moment
energy `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²`. -/
theorem lip032_41_smooth_model_exact_one_moment_energy :
    (∀ y : Fin 1 → ℝ, gammaStar_LIP03241 (torusLift y) = Real.cos (2 * Real.pi * y 0)) ∧
      IsSmoothPeriodic gammaStar_LIP03241 ∧ IsSmoothPeriodic VStar_LIP03241 ∧
      ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        WStar_LIP03241 (torusLift p.1) (torusLift p.2)) ∧
      (∀ x y, WStar_LIP03241 x y = WStar_LIP03241 y x) ∧ (∀ x, WStar_LIP03241 x x = 0) ∧
      (∀ x, |VStar_LIP03241 x| ≤ 4) ∧ (∀ x y, |WStar_LIP03241 x y| ≤ 16) ∧
      (∀ x x', |VStar_LIP03241 x - VStar_LIP03241 x'| ≤ 16 * Real.pi * torusDist x x') ∧
      (∀ x y x' y', |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
        32 * Real.pi * (torusDist x x' + torusDist y y')) ∧
      (∀ x y x' y', |WStar_LIP03241 x y - WStar_LIP03241 x' y'| ≤
        64 * Real.pi * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) ∧
      (∀ p q : Torus 1 × Torus 1,
        |WStar_LIP03241 p.1 p.2 - WStar_LIP03241 q.1 q.2| ≤ 64 * Real.pi * dist p q) ∧
      interactionDataStar_LIP03241.V = VStar_LIP03241 ∧
      interactionDataStar_LIP03241.W = WStar_LIP03241 ∧
      LipschitzData interactionDataStar_LIP03241 ∧
      ∀ ν : ProbabilityMeasure (Torus 1),
        (Integrable VStar_LIP03241 (ν : Measure (Torus 1)) ∧
          Integrable (fun p : Torus 1 × Torus 1 => WStar_LIP03241 p.1 p.2)
            ((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) ∧
          potentialEnergy interactionDataStar_LIP03241 (ν : Measure (Torus 1)) +
            (1 / 2 : ℝ) * interactionEnergy interactionDataStar_LIP03241 (ν : Measure (Torus 1)) =
          -(4 * momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2)) ∧
        freeEnergy interactionDataStar_LIP03241 ν =
          ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) -
            ((4 * momentStar_LIP03241 (ν : Measure (Torus 1)) ^ 2 : ℝ) : EReal) := by
  obtain ⟨hlift, hsmooth_g, hsmooth_V, hsmooth_W⟩ :=
    lip032_41_smooth_model_exact_one_moment_energy_smooth
  obtain ⟨hsymm, hdiag⟩ := lip032_41_smooth_model_exact_one_moment_energy_symm_diag
  obtain ⟨hbV, hbW⟩ := lip032_41_smooth_model_exact_one_moment_energy_bounds
  obtain ⟨hlV, hlW, hlE, hlP⟩ := lip032_41_smooth_model_exact_one_moment_energy_lipschitz
  obtain ⟨hdV, hdW, hLip⟩ := lip032_41_smooth_model_exact_one_moment_energy_data
  exact ⟨hlift, hsmooth_g, hsmooth_V, hsmooth_W, hsymm, hdiag, hbV, hbW, hlV, hlW, hlE, hlP,
    hdV, hdW, hLip, fun ν => ⟨lip032_41_smooth_model_exact_one_moment_energy_potential_part ν,
      lip032_41_smooth_model_exact_one_moment_energy_energy ν⟩⟩

end DGPS.Frontier.LIP032
