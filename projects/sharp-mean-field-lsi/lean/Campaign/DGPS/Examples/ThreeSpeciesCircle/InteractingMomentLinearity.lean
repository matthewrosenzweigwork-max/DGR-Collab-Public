import DGPS.Examples.ThreeSpeciesCircle.InteractingGapVariation

/-! Finite observable contractions for the ACTUAL normalized original-H1
moment derivative. All mixed integrals are proved integrable before linearity
is used; these identities support the explicit nonlinear weak Euler operator. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

theorem absoluteRootMixedMoment_integrable (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    {g : Torus 1 → ℝ} (hg : Continuous g) :
    Integrable (fun x => ρ.sqrt x * φ x * g x) (haar 1) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact integrable_mul_bdd_two hg.aestronglyMeasurable
    (fun x => by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x))
    ρ.memLp_sqrt hφ.memLp

theorem absoluteRootMomentDerivative_add (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    absoluteRootMomentDerivative ρ φ (fun x => f x + g x) =
      absoluteRootMomentDerivative ρ φ f + absoluteRootMomentDerivative ρ φ g := by
  have hi := absoluteRootMixedMoment_integrable ρ hφ hf
  have hj := absoluteRootMixedMoment_integrable ρ hφ hg
  have hfi := hf.integrable_of_hasCompactSupport (μ := (densityMeasure ρ : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have hgi := hg.integrable_of_hasCompactSupport (μ := (densityMeasure ρ : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have he : (fun x => ρ.sqrt x * φ x * (f x + g x)) =
      fun x => ρ.sqrt x * φ x * f x + ρ.sqrt x * φ x * g x := by funext x; ring
  unfold absoluteRootMomentDerivative
  rw [he, integral_add hi hj, integral_add hfi hgi]
  ring

theorem absoluteRootMomentDerivative_const_mul (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    {g : Torus 1 → ℝ} (hg : Continuous g) (a : ℝ) :
    absoluteRootMomentDerivative ρ φ (fun x => a * g x) =
      a * absoluteRootMomentDerivative ρ φ g := by
  have hi := absoluteRootMixedMoment_integrable ρ hφ hg
  have he : (fun x => ρ.sqrt x * φ x * (a * g x)) =
      fun x => a * (ρ.sqrt x * φ x * g x) := by funext x; ring
  simp only [absoluteRootMomentDerivative, he, integral_const_mul] <;> ring

theorem absoluteRootMomentDerivative_sub (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    absoluteRootMomentDerivative ρ φ (fun x => f x - g x) =
      absoluteRootMomentDerivative ρ φ f - absoluteRootMomentDerivative ρ φ g := by
  have he : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [he, absoluteRootMomentDerivative_add ρ hφ hf (hg.const_mul (-1)),
    absoluteRootMomentDerivative_const_mul ρ hφ hg]
  ring

/-- Every finite observable contraction uses actual finite mixed moments.
No integrability assumption on an unbounded or unspecified test is hidden. -/
theorem absoluteRootMomentDerivative_sum {ι : Type*} (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    (s : Finset ι) (g : ι → Torus 1 → ℝ) (hg : ∀ i ∈ s, Continuous (g i)) :
    absoluteRootMomentDerivative ρ φ (fun x => ∑ i ∈ s, g i x) =
      ∑ i ∈ s, absoluteRootMomentDerivative ρ φ (g i) := by
  classical
  have hi (i : ι) (his : i ∈ s) := absoluteRootMixedMoment_integrable ρ hφ (hg i his)
  have he (i : ι) (his : i ∈ s) : Integrable (g i) (densityMeasure ρ : Measure (Torus 1)) :=
    (hg i his).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmul : (fun x => ρ.sqrt x * φ x * (∑ i ∈ s, g i x)) =
      fun x => ∑ i ∈ s, ρ.sqrt x * φ x * g i x := by
    funext x
    exact Finset.mul_sum _ _ _
  unfold absoluteRootMomentDerivative
  rw [hmul, integral_finsetSum _ hi, integral_finsetSum _ he,
    Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]

end DGPS.Examples.ThreeSpeciesCircle
