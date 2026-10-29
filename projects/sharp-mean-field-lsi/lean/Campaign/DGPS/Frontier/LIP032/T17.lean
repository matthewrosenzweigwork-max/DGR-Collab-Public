import DGPS.Frontier.LIP032.T16

/-!
# LIP032.17: Positive normalized exponential

Task id and title: LIP032.17, "Positive normalized exponential" (node LIP032, contractibility of
the minimizer set; leaf formalization, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.normalizer_LIP03217` : the normalizer `Z(U) = ∫ e^{-U} dm`.
* `DGPS.Frontier.LIP032.normExp_LIP03217` : the normalized exponential
  `p_U(x) = e^{-U(x)} / Z(U)`.
* `DGPS.Frontier.LIP032.lip032_17_positive_normalized_exponential` : for continuous `U` on
  `𝕋^d` with `|U| ≤ B`, `e^{-B} ≤ Z(U) ≤ e^{B}`, `0 < Z(U)`, `e^{-2B} ≤ p_U ≤ e^{2B}`,
  `∫ p_U dm = 1`, and `p_U` is continuous.
* `DGPS.Frontier.LIP032.lip032_17_positive_normalized_exponential_interaction` : the same
  five-part conclusion for `U_ν(x) = A.V x + ∫ A.W(x,y) dν(y)` with `B_0 = M_V + M_W`, for every
  probability `ν` on `𝕋^d` (uses LIP032.16).

## R5 notes
* Hypotheses of the main statement: `U : Torus d → ℝ` continuous, a real `B` and
  `∀ x, |U x| ≤ B`. The specification says "a fixed `B ≥ 0`"; nonnegativity of `B` follows from
  the bound at any point of the (nonempty) torus, so it is not assumed separately. The same
  applies to `M_V`, `M_W` in the interaction corollary.
* `m` is `haar d`, a probability measure (instance `haar_isProbabilityMeasure`). `Z(U)` is the
  Bochner integral `∫ x, Real.exp (-U x) ∂haar d`; integrability follows from continuity and
  the bound, so no junk value of the integral is used.
* The conclusion is a conjunction in the order: `e^{-B} ≤ Z`, `Z ≤ e^B`, `0 < Z`, the two-sided
  pointwise bound for `p_U`, `∫ p_U = 1`, `Continuous p_U`. Positivity of `Z` is stated after
  the bounds exactly as in the specification.
* "In particular for `U_ν` with `B = B_0`" is the separate public corollary `..._interaction`.
  Its hypotheses are `A : InteractionData d`, reals `M_V`, `M_W` with `|A.V| ≤ M_V` and
  `|A.W| ≤ M_W`, and a probability `ν`; the bound `|U_ν| ≤ M_V + M_W` is derived from the
  LIP032.16 bound on the kernel integral. `U_ν` is spelled out as the function
  `x ↦ A.V x + ∫ y, A.W x y ∂ν`; the packet's `gibbsDensity` is not referenced since it is not
  an upstream dependency of this leaf (the corollary's `normExp_LIP03217` is that density).
* `ν` is a `Measure (Torus d)` with `[IsProbabilityMeasure ν]`, as in LIP032.16.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The normalizer `Z(U) = ∫ e^{-U} dm`. -/
noncomputable def normalizer_LIP03217 (U : Torus d → ℝ) : ℝ :=
  ∫ x, Real.exp (-U x) ∂haar d

/-- The normalized exponential `p_U = e^{-U} / Z(U)`. -/
noncomputable def normExp_LIP03217 (U : Torus d → ℝ) (x : Torus d) : ℝ :=
  Real.exp (-U x) / normalizer_LIP03217 U

/-- Pointwise bounds `e^{-B} ≤ e^{-U x} ≤ e^B`. -/
theorem exp_bounds_LIP03217 {U : Torus d → ℝ} {B : ℝ} (hU : ∀ x, |U x| ≤ B) (x : Torus d) :
    Real.exp (-B) ≤ Real.exp (-U x) ∧ Real.exp (-U x) ≤ Real.exp B := by
  have h := abs_le.mp (hU x)
  exact ⟨Real.exp_le_exp.mpr (by linarith [h.2]), Real.exp_le_exp.mpr (by linarith [h.1])⟩

/-- The exponential integrand is integrable. -/
theorem integrable_exp_LIP03217 {U : Torus d → ℝ} (hc : Continuous U) {B : ℝ}
    (hU : ∀ x, |U x| ≤ B) : Integrable (fun x => Real.exp (-U x)) (haar d) :=
  Integrable.of_bound (Real.continuous_exp.comp hc.neg).aestronglyMeasurable (Real.exp B)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (exp_bounds_LIP03217 hU x).2)

/-- Normalizer bounds `e^{-B} ≤ Z(U) ≤ e^B`. -/
theorem normalizer_bounds_LIP03217 {U : Torus d → ℝ} (hc : Continuous U) {B : ℝ}
    (hU : ∀ x, |U x| ≤ B) :
    Real.exp (-B) ≤ normalizer_LIP03217 U ∧ normalizer_LIP03217 U ≤ Real.exp B := by
  have hi := integrable_exp_LIP03217 hc hU
  constructor
  · have := integral_mono (integrable_const (Real.exp (-B))) hi
      (fun x => (exp_bounds_LIP03217 hU x).1)
    simpa [normalizer_LIP03217] using this
  · have := integral_mono hi (integrable_const (Real.exp B))
      (fun x => (exp_bounds_LIP03217 hU x).2)
    simpa [normalizer_LIP03217] using this

/-- **LIP032.17.** For continuous `U` with `|U| ≤ B`: `e^{-B} ≤ Z(U) ≤ e^B`, `Z(U) > 0`,
`e^{-2B} ≤ p_U ≤ e^{2B}`, `∫ p_U dm = 1`, and `p_U` is continuous. -/
theorem lip032_17_positive_normalized_exponential
    (U : Torus d → ℝ) (hc : Continuous U) (B : ℝ) (hU : ∀ x, |U x| ≤ B) :
    Real.exp (-B) ≤ normalizer_LIP03217 U ∧ normalizer_LIP03217 U ≤ Real.exp B ∧
    0 < normalizer_LIP03217 U ∧
    (∀ x, Real.exp (-(2 * B)) ≤ normExp_LIP03217 U x ∧ normExp_LIP03217 U x ≤ Real.exp (2 * B)) ∧
    ∫ x, normExp_LIP03217 U x ∂haar d = 1 ∧ Continuous (normExp_LIP03217 U) := by
  obtain ⟨hZl, hZu⟩ := normalizer_bounds_LIP03217 hc hU
  have hZpos : 0 < normalizer_LIP03217 U := lt_of_lt_of_le (Real.exp_pos _) hZl
  refine ⟨hZl, hZu, hZpos, fun x => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := exp_bounds_LIP03217 hU x
    unfold normExp_LIP03217
    constructor
    · rw [le_div_iff₀ hZpos]
      calc Real.exp (-(2 * B)) * normalizer_LIP03217 U
          ≤ Real.exp (-(2 * B)) * Real.exp B :=
            mul_le_mul_of_nonneg_left hZu (Real.exp_pos _).le
        _ = Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-U x) := h1
    · rw [div_le_iff₀ hZpos]
      calc Real.exp (-U x) ≤ Real.exp B := h2
        _ = Real.exp (2 * B) * Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (2 * B) * normalizer_LIP03217 U :=
            mul_le_mul_of_nonneg_left hZl (Real.exp_pos _).le
  · unfold normExp_LIP03217
    rw [integral_div]
    exact div_self hZpos.ne'
  · exact (Real.continuous_exp.comp hc.neg).div_const _

/-- `U_ν(x) = A.V x + ∫ A.W(x,y) dν(y)` is bounded by `B_0 = M_V + M_W` and continuous, so the
conclusions of LIP032.17 hold for it. -/
theorem lip032_17_positive_normalized_exponential_interaction
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    let U : Torus d → ℝ := fun x => A.V x + ∫ y, A.W x y ∂ν
    Real.exp (-(M_V + M_W)) ≤ normalizer_LIP03217 U ∧
    normalizer_LIP03217 U ≤ Real.exp (M_V + M_W) ∧
    0 < normalizer_LIP03217 U ∧
    (∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ normExp_LIP03217 U x ∧
      normExp_LIP03217 U x ≤ Real.exp (2 * (M_V + M_W))) ∧
    ∫ x, normExp_LIP03217 U x ∂haar d = 1 ∧ Continuous (normExp_LIP03217 U) := by
  intro U
  have hK := (lip032_16_continuous_kernel_integrals_common_bounds A M_W hW).1 ν
  have hc : Continuous U := A.V_continuous.add hK.1
  have hb : ∀ x, |U x| ≤ M_V + M_W := fun x =>
    (abs_add_le _ _).trans (add_le_add (hV x) (hK.2 x))
  exact lip032_17_positive_normalized_exponential U hc (M_V + M_W) hb

end DGPS.Frontier.LIP032
