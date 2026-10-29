import DGRHS.Gaussian.GaussianShortRangeNorm

/-! Exact physical Riesz-minus-cutoff AE correspondence and original
source eq:fetaL2Rate for the constructed Gaussian-profile cutoff.
The diagonal is removed by actual absolute continuity of the source density;
no diagonal slice of a product AE equality is used. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma ae_gaussianRieszDensity_pair_ne (ρ : EuclideanSpace ℝ ι → ℝ) [Nonempty ι]
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∀ᵐ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ), p.1 ≠ p.2 := by
  letI : NullSingletonClass (gaussianRieszDensityMeasure ρ) := by
    unfold gaussianRieszDensityMeasure
    infer_instance
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
  exact Filter.Eventually.of_forall (fun x => ((gaussianRieszDensityMeasure ρ).ae_ne x).mono
    (fun y hy => hy.symm))

lemma ae_gaussianRieszEuclideanShortRange_eq_physical_remainder (s η : ℝ) (hs : 0 < s)
    (hη : 0 < η) (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianRieszEuclideanShortRange s η (p.1 - p.2))
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
    (fun p => ‖p.1 - p.2‖ ^ (-s) / s - gaussianRieszEuclideanTruncation s η (p.1 - p.2)) := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  exact gaussianRieszEuclideanShortRange_eq_remainder s η hs hη _ (sub_ne_zero.mpr hp)

lemma memLp_gaussianRieszEuclidean_physical_remainder (s η : ℝ) (hs : 0 < s)
    (hη : 0 < η) (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ‖p.1 - p.2‖ ^ (-s) / s - gaussianRieszEuclideanTruncation s η (p.1 - p.2)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  (memLp_congr_ae (ae_gaussianRieszEuclideanShortRange_eq_physical_remainder s η hs hη ha ρ)).1
    (memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ)

lemma gaussianRieszEuclidean_physical_remainder_L2_rate (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η →
      MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        ‖p.1 - p.2‖ ^ (-s) / s - gaussianRieszEuclideanTruncation s η (p.1 - p.2)) 2
        ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
      (eLpNorm (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        ‖p.1 - p.2‖ ^ (-s) / s - gaussianRieszEuclideanTruncation s η (p.1 - p.2)) 2
        ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))).toReal ≤
          C * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
  refine ⟨gaussianRieszShortRangeRateConstant s M ι, Real.sqrt_nonneg _, ?_⟩
  intro η hη
  refine ⟨memLp_gaussianRieszEuclidean_physical_remainder s η hs hη ha ρ M hM hρ, ?_⟩
  rw [← eLpNorm_congr_ae (ae_gaussianRieszEuclideanShortRange_eq_physical_remainder s η hs hη ha ρ)]
  exact eLpNorm_toReal_gaussianRieszEuclideanShortRange_source_le s η hη ha ρ M hM hρ

end DGRHS.Gaussian

#check DGRHS.Gaussian.ae_gaussianRieszDensity_pair_ne
#print axioms DGRHS.Gaussian.ae_gaussianRieszDensity_pair_ne
#check DGRHS.Gaussian.ae_gaussianRieszEuclideanShortRange_eq_physical_remainder
#print axioms DGRHS.Gaussian.ae_gaussianRieszEuclideanShortRange_eq_physical_remainder
#check DGRHS.Gaussian.memLp_gaussianRieszEuclidean_physical_remainder
#print axioms DGRHS.Gaussian.memLp_gaussianRieszEuclidean_physical_remainder
#check DGRHS.Gaussian.gaussianRieszEuclidean_physical_remainder_L2_rate
#print axioms DGRHS.Gaussian.gaussianRieszEuclidean_physical_remainder_L2_rate
