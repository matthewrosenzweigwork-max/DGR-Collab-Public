import DGPS.Examples.ThreeSpeciesCircle.OrdinaryEuler
import DGPS.Structural.SmallRateCircle

/-! Genuine normalized absolute H1 variations and their bounded-observable
derivatives. These paths remain in the original density carrier, including when
the varied root vanishes. This is a first-variation ingredient, not an optimizer
Euler or regularity theorem. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A genuine absolute-density path, normalized wherever its squared mass is
positive. The harmless fallback only makes the path total away from zero. -/
def absoluteRootVariation (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) (t : ℝ) : AbsoluteDensity 1 :=
  if hn : 0 < ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1 then
    normAbs (fun x => ρ.sqrt x + t * φ x)
      ⟨_, (isWeakGradient_weakGradient ρ.sqrt_mem).add (hφ.smul t)⟩ hn
  else ρ

/-- The actual varied probability has the normalized quadratic observable
moment. No regularity or positivity of the stored root is required. -/
theorem absoluteRootVariation_moment (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) (t : ℝ)
    (hnt : 0 < ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1) (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1))) =
      (∫ x, (ρ.sqrt x + t * φ x) ^ 2 * g x ∂haar 1) /
        ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1 := by
  rw [Structural.budget_integral_densityMeasure]
  unfold absoluteRootVariation
  rw [dif_pos hnt, ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [normAbs, AbsoluteDensity.density]
    rw [div_pow, sq_abs, Real.sq_sqrt hnt.le]
    ring

/-- Actual normalized H1 moment differentiation includes the normalization
covariance term. It applies to every bounded continuous observable, so in
particular to each actual model feature and generator feature. -/
theorem absoluteRootVariation_moment_hasDerivAt (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    (g : Torus 1 → ℝ) (hg : Continuous g) :
    HasDerivAt
      (fun t : ℝ => ∫ x, g x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)))
      (2 * (∫ x, ρ.sqrt x * φ x * g x ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
          ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))) 0 := by
  let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
  let A := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 * g x ∂haar 1
  have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
  have hn : HasDerivAt n (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) 0 := by
    have hh := hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
    simpa only [n, mul_one] using hh
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hA : HasDerivAt A (2 * ∫ x, ρ.sqrt x * φ x * g x ∂haar 1) 0 :=
    hasDerivAt_integral_quad hg.aestronglyMeasurable
      (fun x => by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x))
      ρ.memLp_sqrt hφ.memLp
  have hA0 : A 0 = ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) := by
    rw [Structural.budget_integral_densityMeasure]
    simp only [A, zero_mul, add_zero, AbsoluteDensity.density]
  have hnt : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t :=
    hn.continuousAt.eventually (lt_mem_nhds (by rw [hn0]; norm_num))
  have hquot := hA.div hn (by rw [hn0]; exact one_ne_zero)
  have hder : HasDerivAt (fun t => A t / n t)
      (2 * (∫ x, ρ.sqrt x * φ x * g x ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
          ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))) 0 := by
    convert hquot using 1 <;> rw [hn0, hA0] <;> ring
  apply hder.congr_of_eventuallyEq
  filter_upwards [hnt] with t ht
  exact absoluteRootVariation_moment ρ hφ t ht g

end DGPS.Examples.ThreeSpeciesCircle
