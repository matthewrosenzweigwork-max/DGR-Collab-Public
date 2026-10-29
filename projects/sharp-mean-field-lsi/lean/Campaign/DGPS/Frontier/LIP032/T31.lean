import DGPS.Frontier.LIP032.T30

/-!
# LIP032.31: Nonnegative-time uniqueness and uniqueness of the limit

Task id and title: LIP032.31, "Nonnegative-time uniqueness and uniqueness of the limit" (node LIP032,
contractibility of the minimizer set; conditional on the flow context of LIP028 and on the
positive-rate flow context of LIP031, inherited as in LIP032.30).

## Provides
* `DGPS.Frontier.LIP032.lip032_31_nonnegative_time_uniqueness_limit_uniqueness` : MAIN. For two
  global probability flows `u` and `v` of the mean-field model with the same initial class `c`,
  (i) `u t = v t` in `L²` for every `t ≥ 0`, and (ii) any two free-energy minimizers `R`, `R'`
  with `∫ (u t) φ dm → ∫ φ dR` and `∫ (v t) φ dm → ∫ φ dR'` as `t → +∞`, for every continuous
  `φ`, are equal. Thus the limiting probability depends only on the initial class.
* `DGPS.Frontier.LIP032.probMeasure_eq_of_integral_LIP03231` (helper) : two probability measures
  on the torus whose integrals of every continuous real test function agree are equal.

## R5 notes
* Flows. "Admissible flow" is read as `IsGlobalProbFlow hMF c u`, the LIP028 notion of a global
  bounded mild probability flow, with the same mean-field data `hMF` for `u` and `v`.
* Inherited context. The positive-rate context of LIP031 (`A`, `drift`, `G`, `B`, `g`, `β`,
  `hMF`, `hV`, `hWB`, `r`, `hr`, `hrate`) is taken as binders, exactly as in LIP032.30. The
  proof uses only `hMF`, `u`, `v`, `c` and the test-function limits; `hV`, `hWB`, `hr` and
  `hrate` are carried so that the statement reads as "limiting probabilities supplied by LIP031",
  and are unused (their names carry an underscore to silence the unused-binder linter).
* Minimizer clauses. The conditions `freeEnergy A R = freeEnergyMinimum A` (and for `R'`) are
  part of the LIP031 conclusion and are carried as hypotheses; they are unused by the proof.
* Limit identity. The limit is `Tendsto (fun t => ∫ x, u t x * φ x ∂haar d) atTop (𝓝 (∫ φ dR))`
  for continuous `φ : Torus d → ℝ`, exactly as in LIP031 and LIP032.30.
* Negative times. Equality is used only at `t ≥ 0`, transferred to the `atTop` filter by
  `eventually_ge_atTop 0`; no value at a negative time is compared or assumed.
* Equality of classes. `u t = v t` is equality of `L²` elements (a.e. equality of
  representatives), which makes the pairing integrals agree; no continuity of the choice of flow
  or limit in `c` is claimed.
* Probability measures. The equality `R = R'` is obtained from equal integrals of all bounded
  continuous real functions via Mathlib's finite-measure test-function criterion on the torus,
  restricted to continuous `φ`, which is the test family of the limits.
* Binding. The conclusion is stated for an arbitrary initial class `c`; the identification of
  `c` with `[f_{ν,s}]` (LIP032.29 and LIP032.30) is not used here, so the statement is not
  restricted to that family.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper: two probability measures on the torus with equal integrals of every continuous real
test function coincide. -/
theorem probMeasure_eq_of_integral_LIP03231 {P Q : ProbabilityMeasure (Torus d)}
    (h : ∀ φ : Torus d → ℝ, Continuous φ →
      ∫ x, φ x ∂(P : Measure (Torus d)) = ∫ x, φ x ∂(Q : Measure (Torus d))) :
    P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact h f f.continuous

/-- **LIP032.31.** Let `u`, `v` be global probability flows of the mean-field model from the same
initial class `c`. Then `u t = v t` for every `t ≥ 0`, and any two free-energy minimizers `R`, `R'`
that are the LIP031 limits of `u` and `v` along continuous test functions coincide. -/
theorem lip032_31_nonnegative_time_uniqueness_limit_uniqueness (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (_hV : IsWeakGradient A.V G)
    (_hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (_hr : 0 < r) (_hrate : ENNReal.ofReal r < scalarRate A drift)
    {c : DGPS.Lipschitz.L2s d} {u v : ℝ → DGPS.Lipschitz.L2s d}
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF c u)
    (hv : DGPS.Lipschitz.IsGlobalProbFlow hMF c v) :
    (∀ t : ℝ, 0 ≤ t → u t = v t) ∧
    ∀ (R R' : ProbabilityMeasure (Torus d)),
      freeEnergy A R = freeEnergyMinimum A → freeEnergy A R' = freeEnergyMinimum A →
      (∀ φ : Torus d → ℝ, Continuous φ →
        Tendsto (fun t : ℝ => ∫ x, u t x * φ x ∂haar d) atTop
          (𝓝 (∫ x, φ x ∂(R : Measure (Torus d))))) →
      (∀ φ : Torus d → ℝ, Continuous φ →
        Tendsto (fun t : ℝ => ∫ x, v t x * φ x ∂haar d) atTop
          (𝓝 (∫ x, φ x ∂(R' : Measure (Torus d))))) →
      R = R' := by
  refine ⟨fun t ht => hu.unique hv ht, ?_⟩
  intro R R' _ _ hRlim hR'lim
  apply probMeasure_eq_of_integral_LIP03231
  intro φ hφ
  have hev : (fun t : ℝ => ∫ x, u t x * φ x ∂haar d) =ᶠ[atTop]
      (fun t : ℝ => ∫ x, v t x * φ x ∂haar d) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hu.unique hv ht]
  exact tendsto_nhds_unique (Tendsto.congr' hev (hRlim φ hφ)) (hR'lim φ hφ)

end DGPS.Frontier.LIP032
