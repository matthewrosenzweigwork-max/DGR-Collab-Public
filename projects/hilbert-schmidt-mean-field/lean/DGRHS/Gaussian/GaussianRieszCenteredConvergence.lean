import DGRHS.Gaussian.GaussianRieszCutoffConvergence

/-! Proper dominated convergence for the actual density potentials and pair
mean. The source diagonal is removed by its own null-singleton property. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma tendsto_gaussianRieszCutoff_potential (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0))
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun j => ∫ y,gaussianRieszTruncatedPair s (η j) (x,y) ∂gaussianRieszDensityMeasure ρ) atTop
      (𝓝 (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure;infer_instance
  apply tendsto_integral_of_dominated_convergence (fun y => gaussianRieszPhysicalPair s (x,y))
  · intro j
    exact ((stronglyMeasurable_gaussianRieszTruncatedPair s (η j) hs (hη j)).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (gaussianRieszPhysicalPotential_bound s hs ha ρ M hM hρ x).1
  · intro j
    filter_upwards [μ.ae_ne x] with y hy
    have hb := gaussianRieszEuclidean_truncation_bounds s (η j) hs (hη j) (x-y) (sub_ne_zero.mpr hy.symm)
    change ‖gaussianRieszEuclideanTruncation s (η j) (x-y)‖ ≤ ‖x-y‖^(-s)/s
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2.1
  · filter_upwards [μ.ae_ne x] with y hy
    exact tendsto_gaussianRieszEuclideanTruncation s hs η hη hη0 (x-y) (sub_ne_zero.mpr hy.symm)

lemma tendsto_gaussianRieszCutoff_pairMean (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun j => ∫ p,gaussianRieszTruncatedPair s (η j) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) atTop
      (𝓝 (∫ p,gaussianRieszPhysicalPair s p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  apply tendsto_integral_of_dominated_convergence (gaussianRieszPhysicalPair s)
  · intro j
    exact (stronglyMeasurable_gaussianRieszTruncatedPair s (η j) hs (hη j)).aestronglyMeasurable
  · exact (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  · intro j
    filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    have hb := gaussianRieszEuclidean_truncation_bounds s (η j) hs (hη j) (p.1-p.2) (sub_ne_zero.mpr hp)
    change ‖gaussianRieszEuclideanTruncation s (η j) (p.1-p.2)‖ ≤ ‖p.1-p.2‖^(-s)/s
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2.1
  · filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    exact tendsto_gaussianRieszEuclideanTruncation s hs η hη hη0 (p.1-p.2) (sub_ne_zero.mpr hp)

lemma tendsto_gaussianRieszCenteredCutoff (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (hp : p.1 ≠ p.2) :
    Tendsto (fun j => hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s (η j)) p)
      atTop (𝓝 (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have h1 := tendsto_gaussianRieszCutoff_potential s hs ha ρ M hM hρ η hη hη0 p.1
  have h2 := tendsto_gaussianRieszCutoff_potential s hs ha ρ M hM hρ η hη hη0 p.2
  have he (j : ℕ) : (∫ x,gaussianRieszTruncatedPair s (η j) (p.2,x) ∂μ) =
      ∫ x,gaussianRieszTruncatedPair s (η j) (x,p.2) ∂μ := by
    congr 1
    funext x
    unfold gaussianRieszTruncatedPair gaussianRieszEuclideanTruncation
    rw [norm_sub_rev]
  have hef : (∫ x,gaussianRieszPhysicalPair s (p.2,x) ∂μ) =
      ∫ x,gaussianRieszPhysicalPair s (x,p.2) ∂μ := by
    congr 1
    funext x
    unfold gaussianRieszPhysicalPair
    rw [norm_sub_rev]
  change Tendsto (fun j => ∫ x,gaussianRieszTruncatedPair s (η j) (p.2,x) ∂μ) atTop
    (𝓝 (∫ x,gaussianRieszPhysicalPair s (p.2,x) ∂μ)) at h2
  simp_rw [he,hef] at h2
  have h0 := tendsto_gaussianRieszEuclideanTruncation s hs η hη hη0 (p.1-p.2) (sub_ne_zero.mpr hp)
  have hm := tendsto_gaussianRieszCutoff_pairMean s hs ha ρ M hM hρ η hη hη0
  exact ((h0.sub h1).sub h2).add hm

end DGRHS.Gaussian

#check DGRHS.Gaussian.tendsto_gaussianRieszCutoff_potential
#print axioms DGRHS.Gaussian.tendsto_gaussianRieszCutoff_potential

#check DGRHS.Gaussian.tendsto_gaussianRieszCutoff_pairMean
#print axioms DGRHS.Gaussian.tendsto_gaussianRieszCutoff_pairMean

#check DGRHS.Gaussian.tendsto_gaussianRieszCenteredCutoff
#print axioms DGRHS.Gaussian.tendsto_gaussianRieszCenteredCutoff
