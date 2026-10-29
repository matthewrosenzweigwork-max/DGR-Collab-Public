import DGRHS.Gaussian.GaussianLogPhaseL2

/-! Supporting development. Actual product-L2 membership and the same raw phase's
constructed Hilbert representative. Continuity and weighted mean zero are separate. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
variable (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
variable (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
variable [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
variable (hpair : Integrable logPhysicalPair
  ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))

include hη hd M hM hρ hpair

lemma memLp_gaussianLogCenteredPhase_section (x : EuclideanSpace ℝ ι) :
    MemLp (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x) 2 (gaussianLogPhaseMeasure ι η) :=
  (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_gaussianLogCenteredPhase_section (gaussianRieszDensityMeasure ρ) x).aestronglyMeasurable).mpr
    (integrable_gaussianLogCenteredPhase_sq η hη hd ρ M hM hρ hpair x).1

lemma memLp_gaussianLogCenteredPhase_product :
    MemLp (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) q.1 q.2) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianLogPhaseMeasure ι η)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  let F := fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) => ‖gaussianLogCenteredPhase μ q.1 q.2‖^2
  let m := gaussianLogBandDiagonalMajorant η M μ
  have hsm : StronglyMeasurable F := (stronglyMeasurable_gaussianLogCenteredPhase_joint μ).norm.pow 2
  have hmn (x : EuclideanSpace ℝ ι) : 0 ≤ m x := gaussianLogBandDiagonalMajorant_nonneg η M hη.le hM μ x
  have hmi : Integrable m μ := integrable_gaussianLogBandDiagonalMajorant η M μ hpair
  have hs (x : EuclideanSpace ℝ ι) : (∫⁻ p, ENNReal.ofReal (F (x,p)) ∂ν) ≤ ENNReal.ofReal (m x) := by
    obtain ⟨hi,hb⟩ := integrable_gaussianLogCenteredPhase_sq η hη hd ρ M hM hρ hpair x
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun p => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hb
  have hB : (∫⁻ q, ENNReal.ofReal (F q) ∂μ.prod ν) ≤ ENNReal.ofReal (∫ x,m x ∂μ) := by
    calc
      _ = ∫⁻ x, (∫⁻ p, ENNReal.ofReal (F (x,p)) ∂ν) ∂μ :=
        lintegral_prod _ (ENNReal.measurable_ofReal.comp_aemeasurable hsm.aestronglyMeasurable.aemeasurable)
      _ ≤ ∫⁻ x, ENNReal.ofReal (m x) ∂μ := lintegral_mono hs
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hmi (Eventually.of_forall hmn)).symm
  have hi : Integrable F (μ.prod ν) := ⟨hsm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun q => sq_nonneg _))).mpr
      (hB.trans_lt ENNReal.ofReal_lt_top)⟩
  exact (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_gaussianLogCenteredPhase_joint μ).aestronglyMeasurable).mpr hi

def gaussianLogCenteredInfiniteFeature (x : EuclideanSpace ℝ ι) : Lp ℂ 2 (gaussianLogPhaseMeasure ι η) :=
  (memLp_gaussianLogCenteredPhase_section η hη hd ρ M hM hρ hpair x).toLp
    (gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x)

lemma coeFn_gaussianLogCenteredInfiniteFeature (x : EuclideanSpace ℝ ι) :
    (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x : (ℝ × (ι → ℝ)) → ℂ) =ᵐ[gaussianLogPhaseMeasure ι η]
      gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x :=
  (memLp_gaussianLogCenteredPhase_section η hη hd ρ M hM hρ hpair x).coeFn_toLp

lemma norm_sq_gaussianLogCenteredInfiniteFeature (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x‖^2 =
      ∫ p, ‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p‖^2 ∂gaussianLogPhaseMeasure ι η := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x] with p hp
  rw [hp,real_inner_self_eq_norm_sq]

lemma norm_sq_gaussianLogCenteredInfiniteFeature_le (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x‖^2 ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) x := by
  rw [norm_sq_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair]
  exact (integrable_gaussianLogCenteredPhase_sq η hη hd ρ M hM hρ hpair x).2

end DGRHS.Gaussian
#check @DGRHS.Gaussian.memLp_gaussianLogCenteredPhase_section
#print axioms DGRHS.Gaussian.memLp_gaussianLogCenteredPhase_section
#check @DGRHS.Gaussian.memLp_gaussianLogCenteredPhase_product
#print axioms DGRHS.Gaussian.memLp_gaussianLogCenteredPhase_product
#check @DGRHS.Gaussian.gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.coeFn_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.coeFn_gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature_le
#print axioms DGRHS.Gaussian.norm_sq_gaussianLogCenteredInfiniteFeature_le
