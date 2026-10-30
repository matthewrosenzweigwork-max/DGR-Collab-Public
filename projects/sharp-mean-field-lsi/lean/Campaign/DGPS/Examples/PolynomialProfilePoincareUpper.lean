import DGPS.Circle.FirstClusterPerturbation
import DGPS.Circle.VonMisesParity

/-! A one-sided native Poincare bound from a factual angular log-profile jet.
The logarithm is unnormalized: the supplied reference has exactly its normalized
exponential density. Constants precede the profile, reference and coefficients.
The existing first-cluster theorem supplies the full weak-H1 spectral bridge. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace
open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Circle.AngularNormalization DGPS.Circle.FirstClusterPerturbation
open DGPS.Circle.VonMisesParity

namespace DGPS.Examples.PolynomialSpecies

/-- The cosine diagonal bounds the least spectral coefficient from above.
No evenness or reflection symmetry is required of the reference. -/
theorem polynomial_profile_poincare_upper {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ δ F : ℝ, 0 < δ ∧ 0 < F ∧
      ∀ (p : Fin 4 → ℝ) (P : BoundedPositiveReference 1)
        (ell : AngCircle → ℝ) (h : ℝ),
      (∀ i, |p i| ≤ M) → IsSmoothAngular ell →
      P.density = angularGibbs_EX009 ell → |h| ≤ δ →
      c2JetError_EX009 ell h (p 0) (p 1) (p 2) (p 3) R →
      poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ ≤
        ENNReal.ofReal (a0 * (1 + h ^ 2 *
          ((p 0 ^ 2 + p 1 ^ 2) / 6 - p 2)) + a0 * F * |h| ^ 3) := by
  obtain ⟨δ, F, hδ, hF, hcluster⟩ := uniform_box_cluster_EX009 hM hR
  refine ⟨δ, F, hδ, hF, ?_⟩
  intro p P ell h hp hell hP hh hjet
  have hc := hcluster p ell h hp hell hh hjet
  rw [← hP] at hc
  obtain ⟨e, lam, G, hsd, he0, hl0, hmono, _htop, hfirst, _hsecond, _hthird,
    herror, _herror2⟩ := hc
  have hspec : SpecData P e lam G :=
    ⟨he0, hl0, by have := DGPS.Circle.AngularNormalization.a0_pos; linarith,
      hmono, hsd.grad, hsd.eig, hsd.energy⟩
  have hsqrt : p 2 ≤ Real.sqrt (p 2 ^ 2 + p 3 ^ 2) := by
    calc
      p 2 ≤ |p 2| := le_abs_self _
      _ = Real.sqrt (p 2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (p 3)])
  have hmodel : modelMinimum_EX009 p ≤ (p 0 ^ 2 + p 1 ^ 2) / 6 - p 2 := by
    unfold modelMinimum_EX009
    linarith
  have ha : 0 < a0 := DGPS.Circle.AngularNormalization.a0_pos
  have he : lam 1 / a0 - (1 + h ^ 2 * modelMinimum_EX009 p) ≤ F * |h| ^ 3 := (abs_le.mp herror).2
  have he' : lam 1 ≤ a0 * (1 + h ^ 2 * modelMinimum_EX009 p) +
      a0 * F * |h| ^ 3 := by
    have he0 : lam 1 / a0 ≤ 1 + h ^ 2 * modelMinimum_EX009 p + F * |h| ^ 3 := by
      linarith
    have hm := (div_le_iff₀ ha).mp he0
    nlinarith
  have hbound : lam 1 ≤ a0 * (1 + h ^ 2 *
      ((p 0 ^ 2 + p 1 ^ 2) / 6 - p 2)) + a0 * F * |h| ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hmodel (sq_nonneg h)
    have hm' := mul_le_mul_of_nonneg_left hm ha.le
    nlinarith
  calc
    poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ = ENNReal.ofReal (lam 1) :=
      hspec.poincareRate_eq
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end DGPS.Examples.PolynomialSpecies
