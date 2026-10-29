import DGRHS.Gaussian.GaussianRieszAllCutoffMoment
import DGRHS.Gaussian.GaussianRieszPhysicalPotential

/-! Genuine full-cutoff pointwise convergence from dominated convergence in
the scale variable. The integrability dominating the limit is the proved full
Riesz scale integral away from the origin. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma tendsto_gaussianRieszEuclideanTruncation (s : ℝ) (hs : 0 < s)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0))
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    Tendsto (fun j => gaussianRieszEuclideanTruncation s (η j) x) atTop
      (𝓝 (‖x‖^(-s)/s)) := by
  let F := fun t : ℝ => t^(-s-1)*Real.exp (-‖x‖^2/(2*t^2))
  have hF : Measurable F := by dsimp [F];fun_prop
  have hi : Integrable F (volume.restrict (Ioi 0)) :=
    integrableOn_gaussianRieszEuclidean_full_scale s hs x hx
  have ht : Tendsto (fun j => ∫ t in Ioi 0, (Ioi (η j)).indicator F t) atTop
      (𝓝 (∫ t in Ioi 0,F t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    · intro j
      exact (hF.indicator measurableSet_Ioi).aestronglyMeasurable
    · exact hi.norm
    · intro j
      apply Filter.Eventually.of_forall
      intro t
      by_cases h : t ∈ Ioi (η j)
      · simp only [indicator_of_mem h,le_refl]
      · simp only [indicator_of_notMem h,norm_zero]
        exact norm_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he : ∀ᶠ j : ℕ in atTop, η j < t := hη0.eventually (gt_mem_nhds ht)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with j hj
      rw [indicator_of_mem (show t ∈ Ioi (η j) from hj)]
  have he (j : ℕ) : (∫ t in Ioi 0,(Ioi (η j)).indicator F t) = ∫ t in Ioi (η j),F t := by
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi (hη j).le)]
  simp_rw [he] at ht
  have hh := ht.const_mul (gaussianRieszSourceCoefficient s)
  rw [gaussianRieszEuclidean_full_scale s hs x hx] at hh
  exact hh

end DGRHS.Gaussian

#check DGRHS.Gaussian.tendsto_gaussianRieszEuclideanTruncation
#print axioms DGRHS.Gaussian.tendsto_gaussianRieszEuclideanTruncation
