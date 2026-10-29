import DGRHS.Gaussian.GaussianLogAnchored
import DGRHS.Gaussian.LogPhysicalCenteredL2

/-! proper source convergence of anchored logarithmic kernels.
Raw log-square and an operator-L2 infrared limit are not assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogInfraredPair (T : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianLogAnchored T ‖p.1-p.2‖

lemma stronglyMeasurable_gaussianLogInfraredPair (T : ℝ) :
    StronglyMeasurable (gaussianLogInfraredPair (ι := ι) T) := by
  have hm : Measurable (fun p : ℝ × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =>
      p.1⁻¹ * (Real.exp (-‖p.2.1-p.2.2‖ ^ 2 / (2 * p.1 ^ 2)) -
        Real.exp (-1 / (2 * p.1 ^ 2)))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_left'

lemma integrable_gaussianLogInfraredPair_source (T : ℝ)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Integrable (gaussianLogInfraredPair T)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  apply hpair.norm.mono' (stronglyMeasurable_gaussianLogInfraredPair T).aestronglyMeasurable
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  change ‖gaussianLogAnchored T ‖p.1-p.2‖‖ ≤ ‖-Real.log ‖p.1-p.2‖‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  exact gaussianLogAnchored_abs_le T _ (norm_pos_iff.mpr (sub_ne_zero.mpr hp))

lemma integrable_gaussianLogInfrared_potential (T : ℝ)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianLogInfraredPair T (x,y)) (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have hi := (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).1
  apply hi.norm.mono' ((stronglyMeasurable_gaussianLogInfraredPair T).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [μ.ae_ne x] with y hy
  change ‖gaussianLogAnchored T ‖x-y‖‖ ≤ ‖-Real.log ‖x-y‖‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  exact gaussianLogAnchored_abs_le T _ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))

lemma tendsto_gaussianLogInfrared_potential (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun j => ∫ y, gaussianLogInfraredPair (T j) (x,y) ∂gaussianRieszDensityMeasure ρ)
      atTop (𝓝 (logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  apply tendsto_integral_of_dominated_convergence (fun y => ‖logPhysicalPair (x,y)‖)
  · intro j
    exact ((stronglyMeasurable_gaussianLogInfraredPair (T j)).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).1.norm
  · intro j
    filter_upwards [μ.ae_ne x] with y hy
    change ‖gaussianLogAnchored (T j) ‖x-y‖‖ ≤ ‖-Real.log ‖x-y‖‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    exact gaussianLogAnchored_abs_le (T j) _ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))
  · filter_upwards [μ.ae_ne x] with y hy
    exact tendsto_gaussianLogAnchored T hT ‖x-y‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))

lemma tendsto_gaussianLogInfrared_pairMean (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Tendsto (fun j => ∫ p, gaussianLogInfraredPair (T j) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) atTop
      (𝓝 (∫ p, logPhysicalPair p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  apply tendsto_integral_of_dominated_convergence (fun p => ‖logPhysicalPair p‖)
  · intro j
    exact (stronglyMeasurable_gaussianLogInfraredPair (T j)).aestronglyMeasurable
  · exact hpair.norm
  · intro j
    filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    change ‖gaussianLogAnchored (T j) ‖p.1-p.2‖‖ ≤ ‖-Real.log ‖p.1-p.2‖‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    exact gaussianLogAnchored_abs_le (T j) _ (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  · filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    exact tendsto_gaussianLogAnchored T hT ‖p.1-p.2‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hp))

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogInfraredPair
#print axioms DGRHS.Gaussian.gaussianLogInfraredPair

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogInfraredPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogInfraredPair

#check @DGRHS.Gaussian.integrable_gaussianLogInfraredPair_source
#print axioms DGRHS.Gaussian.integrable_gaussianLogInfraredPair_source

#check @DGRHS.Gaussian.integrable_gaussianLogInfrared_potential
#print axioms DGRHS.Gaussian.integrable_gaussianLogInfrared_potential

#check @DGRHS.Gaussian.tendsto_gaussianLogInfrared_potential
#print axioms DGRHS.Gaussian.tendsto_gaussianLogInfrared_potential

#check @DGRHS.Gaussian.tendsto_gaussianLogInfrared_pairMean
#print axioms DGRHS.Gaussian.tendsto_gaussianLogInfrared_pairMean

