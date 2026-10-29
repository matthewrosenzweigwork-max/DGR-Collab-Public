import DGPS.FiniteN.Tools.StrongConvexityLSI
import DGPS.FiniteN.Tools.StrongConvexityBobkovLedoux
import DGPS.FiniteN.Tools.PrekopaLeindler
import Mathlib

/-!
# Strong convexity LSI and bounded correction (FIN025, final assembly)

Unconditional assembly of FIN025 from INF001 (Prekopa-Leindler), INF002 (Bobkov-Ledoux) and the
partial FIN025 reductions (bounded correction via FIN004, dilation).
-/

open MeasureTheory

namespace DGPS.FiniteN.Tools

/-- Prekopa-Leindler in the form consumed by INF002 (open interval of parameters). -/
theorem prekopaLeindlerStatement_holds (k : ℕ) :
    StrongConvexityBobkovLedoux.PrekopaLeindlerStatement k :=
  fun _ ht0 ht1 _ _ _ hf hg hh hf0 hg0 _ hfgh hfi hgi hhi =>
    prekopaLeindler k ⟨ht0.le, ht1.le⟩ hf hg hh hf0 hg0 hfgh hfi hgi hhi

/-- Euclidean strongly convex LSI: `D²U ≥ λ I` gives `Ent(f²) ≤ (2/λ) ∫ |∇f|²`. -/
theorem hasLSIRate_of_stronglyConvex {k : ℕ} {U : EuclideanSpace ℝ (Fin k) → ℝ}
    (hU : ContDiff ℝ 2 U) {lam : ℝ} (hlam : 0 < lam)
    (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v) :
    StrongConvexityLSI.HasLSIRate (StrongConvexityLSI.gibbs U) lam :=
  hasLSIRate_of_stronglyConvex_of_PL (prekopaLeindlerStatement_holds k) hU hlam hconv

/-- Removal of a bounded correction `q` (oscillation `≤ b`) making `U + q` `λ`-convex. -/
theorem hasLSIRate_of_stronglyConvex_bounded_correction {k : ℕ}
    {U q : EuclideanSpace ℝ (Fin k) → ℝ} {b lam : ℝ} (hlam : 0 < lam)
    (hU : Continuous U) (hq : Measurable q) (hosc : ∀ x y, q x - q y ≤ b)
    (hUq : ContDiff ℝ 2 (fun x => U x + q x))
    (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun x => U x + q x)) x v v) :
    StrongConvexityLSI.HasLSIRate (StrongConvexityLSI.gibbs U) (lam * Real.exp (-b)) := by
  obtain ⟨y0⟩ : Nonempty (EuclideanSpace ℝ (Fin k)) := inferInstance
  have hint' := StrongConvexityBobkovLedoux.integrable_exp_neg_of_convex hUq hlam hconv
  have hint : Integrable (fun x => Real.exp (-U x)) := by
    refine (hint'.mul_const (Real.exp (b + q y0))).mono' ?_ ?_
    · exact (Real.measurable_exp.comp hU.measurable.neg).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [hosc x y0])
  exact StrongConvexityLSI.hasLSIRate_of_bounded_correction hlam hU hq hosc hint
    (hasLSIRate_of_stronglyConvex hUq hlam hconv)

/-- **FIN025.** Strong convexity LSI, bounded correction, and dilation scaling. -/
theorem strong_convexity_lsi_and_bounded_correction :
    (∀ (k : ℕ) (U : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ 2 U → ∀ lam : ℝ, 0 < lam →
      (∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v) →
      StrongConvexityLSI.HasLSIRate (StrongConvexityLSI.gibbs U) lam) ∧
    (∀ (k : ℕ) (U q : EuclideanSpace ℝ (Fin k) → ℝ) (b lam : ℝ), 0 < lam →
      Continuous U → Measurable q → (∀ x y, q x - q y ≤ b) →
      ContDiff ℝ 2 (fun x => U x + q x) →
      (∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun x => U x + q x)) x v v) →
      StrongConvexityLSI.HasLSIRate (StrongConvexityLSI.gibbs U) (lam * Real.exp (-b))) ∧
    (∀ (k : ℕ) (s : ℝ) (hs : 0 < s) (μ : Measure (EuclideanSpace ℝ (Fin k))) (κ : ℝ), 0 < κ →
      StrongConvexityLSI.HasLSIRate μ κ →
      StrongConvexityLSI.HasLSIRate (μ.map (StrongConvexityLSI.dil s hs).symm) (s ^ 2 * κ)) :=
  ⟨fun _ _ hU _ hlam hconv => hasLSIRate_of_stronglyConvex hU hlam hconv,
   fun _ _ _ _ _ hlam hU hq hosc hUq hconv =>
     hasLSIRate_of_stronglyConvex_bounded_correction hlam hU hq hosc hUq hconv,
   fun _ s hs _ _ hκ h => StrongConvexityLSI.hasLSIRate_map_smul s hs hκ h⟩

end DGPS.FiniteN.Tools
