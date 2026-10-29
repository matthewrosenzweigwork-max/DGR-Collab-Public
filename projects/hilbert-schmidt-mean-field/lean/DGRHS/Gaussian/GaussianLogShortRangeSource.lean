import DGRHS.Gaussian.GaussianLogShortRange

/-! Actual source-density near-field and centered short-range bounds for the
normalized Gaussian logarithmic profile. No desired norm or potential bound
is a hypothesis. The full physical kernel is literally -log norm. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogShortPair (η : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianLogShortRange η (p.1-p.2)

def gaussianLogTruncatedPair (η : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  logPhysicalPair p - gaussianLogShortPair η p

lemma stronglyMeasurable_gaussianLogShortPair (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) : StronglyMeasurable (gaussianLogShortPair (ι := ι) η) :=
  (stronglyMeasurable_gaussianLogShortRange η hη hd).comp_measurable (by fun_prop)

lemma memLp_gaussianLogShortPair (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (gaussianLogShortPair η) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hm := stronglyMeasurable_gaussianLogShortRange (ι := ι) η hη hd
  apply (memLp_two_iff_integrable_sq (stronglyMeasurable_gaussianLogShortPair η hη hd).aestronglyMeasurable).2
  exact integrable_sq_sub_density_product ρ M hM hρ _ hm
    (memLp_gaussianLogShortRange η hη hd).integrable_sq

lemma norm_gaussianLogShortPair_toLp_le (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖(memLp_gaussianLogShortPair η hη hd ρ M hM hρ).toLp (gaussianLogShortPair η)‖ ≤
      Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)*
        η^((Fintype.card ι : ℝ)/2) := by
  have hb := integral_sq_sub_density_product_le ρ M hM hρ (gaussianLogShortRange η)
    (stronglyMeasurable_gaussianLogShortRange η hη hd)
    (memLp_gaussianLogShortRange η hη hd).integrable_sq
  have hv := integral_gaussianLogShortRange_sq_le (ι := ι) η hη hd
  have hK : 0 ≤ M*Real.pi^((Fintype.card ι : ℝ)/2) := by positivity
  have hs := Real.sq_sqrt hK
  have he : (Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)*
      η^((Fintype.card ι : ℝ)/2))^2 =
      M*((η^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))^2*Real.pi^((Fintype.card ι : ℝ)/2)) := by
    rw [mul_pow,div_pow,hs]
    ring
  have hb' : ‖(memLp_gaussianLogShortPair η hη hd ρ M hM hρ).toLp (gaussianLogShortPair η)‖^2 ≤
      M*((η^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))^2*Real.pi^((Fintype.card ι : ℝ)/2)) := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact hb.trans (mul_le_mul_of_nonneg_left hv hM)
  have hp : 0 ≤ Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)*
      η^((Fintype.card ι : ℝ)/2) := by positivity
  nlinarith [norm_nonneg ((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).toLp (gaussianLogShortPair η))]

lemma gaussianLogCenteredShortPair_lower (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η) p ≤
      2*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*η^(Fintype.card ι : ℝ))) := by
  have h1 := gaussianLogShortRange_convolution_le η hη hd ρ M hM hρ p.1
  have h2 := gaussianLogShortRange_convolution_le η hη hd ρ M hM hρ p.2
  have he : (fun x => gaussianLogShortRange η (x-p.2)) = (fun x => gaussianLogShortRange η (p.2-x)) := by
    funext x
    simp only [gaussianLogShortRange, norm_sub_rev]
  have hn := gaussianLogShortRange_nonneg η (p.1-p.2)
  have hm : 0 ≤ ∫ z, gaussianLogShortPair η z
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun z => gaussianLogShortRange_nonneg η _)
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change -(gaussianLogShortRange η (p.1-p.2) -
    (∫ y, gaussianLogShortRange η (p.1-y) ∂gaussianRieszDensityMeasure ρ) -
    (∫ x, gaussianLogShortRange η (x-p.2) ∂gaussianRieszDensityMeasure ρ) +
    (∫ z, gaussianLogShortPair η z ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) ≤ _
  rw [he]
  linarith

lemma ae_logPhysical_centered_truncation_difference (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair -
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η) :=
  ae_hoeffdingCentered_sub _ _ _ hpair
    ((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable (by norm_num))

lemma memLp_logPhysicalCenteredTruncatedPair (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hF := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  have hS := memLp_gaussianLogShortPair η hη hd ρ M hM hρ
  have hCS := memLp_hoeffdingCentered (gaussianRieszDensityMeasure ρ) _
    (stronglyMeasurable_gaussianLogShortPair η hη hd) hS
  exact (memLp_congr_ae (ae_logPhysical_centered_truncation_difference η hη hd ρ M hM hρ hpair)).2 (hF.sub hCS)

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogShortPair
#print axioms DGRHS.Gaussian.gaussianLogShortPair

#check @DGRHS.Gaussian.gaussianLogTruncatedPair
#print axioms DGRHS.Gaussian.gaussianLogTruncatedPair

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogShortPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogShortPair

#check @DGRHS.Gaussian.memLp_gaussianLogShortPair
#print axioms DGRHS.Gaussian.memLp_gaussianLogShortPair

#check @DGRHS.Gaussian.norm_gaussianLogShortPair_toLp_le
#print axioms DGRHS.Gaussian.norm_gaussianLogShortPair_toLp_le

#check @DGRHS.Gaussian.gaussianLogCenteredShortPair_lower
#print axioms DGRHS.Gaussian.gaussianLogCenteredShortPair_lower

#check @DGRHS.Gaussian.ae_logPhysical_centered_truncation_difference
#print axioms DGRHS.Gaussian.ae_logPhysical_centered_truncation_difference

#check @DGRHS.Gaussian.memLp_logPhysicalCenteredTruncatedPair
#print axioms DGRHS.Gaussian.memLp_logPhysicalCenteredTruncatedPair
