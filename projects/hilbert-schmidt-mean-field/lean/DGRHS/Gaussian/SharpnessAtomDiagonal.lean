import DGRHS.Gaussian.SharpnessRieszRows

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The actual singular row restricted to any atom is proper and is bounded
by the short convolution plus the cutoff diagonal times the actual atom mass.
This is valid throughout 0<s<d, including the non-Hilbert--Schmidt range. -/
theorem sharpness_riesz_atom_row_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : Set (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszPhysicalPair s (x,y))
      ((gaussianRieszDensityMeasure ρ).restrict A) ∧
    (∫ y in A, gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s)) +
      (gaussianRieszSourceCoefficient s/s * δ^(-s)) *
        (gaussianRieszDensityMeasure ρ A).toReal := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  have : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have he : (fun y => gaussianRieszPhysicalPair s (x,y)) =ᵐ[μ.restrict A]
      (fun y => gaussianRieszEuclideanShortRange s δ (x-y)+
        gaussianRieszEuclideanTruncation s δ (x-y)) := by
    filter_upwards [ae_restrict_of_ae (μ.ae_ne x)] with y hy
    exact gaussianRieszEuclidean_full_short_long_split s δ hs hδ _ (sub_ne_zero.mpr hy.symm)
  have hiS := integrable_gaussianRieszShortRange_convolution s δ hδ ha ρ M hρ x
  have hiL := integrable_gaussianRieszTruncation_convolution s δ hs hδ μ x
  refine ⟨(sharpness_riesz_potential_bound s hs ha ρ M hM hρ x).1.restrict, ?_⟩
  rw [integral_congr_ae he, integral_add (hiS.restrict) (hiL.restrict)]
  have hS : (∫ y in A, gaussianRieszEuclideanShortRange s δ (x-y) ∂μ) ≤
      M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s)) := by
    exact (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun y => gaussianRieszEuclideanShortRange_nonneg s δ hs (x-y))
      hiS).trans (gaussianRieszShortRange_convolution_le s δ hs hδ ha ρ M hM hρ x)
  have hL : (∫ y in A, gaussianRieszEuclideanTruncation s δ (x-y) ∂μ) ≤
      (gaussianRieszSourceCoefficient s/s * δ^(-s)) * (μ A).toReal := by
    calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszSourceCoefficient s/s * δ^(-s) ∂μ.restrict A :=
        integral_mono_ae (hiL.restrict) (integrable_const _)
          (Filter.Eventually.of_forall fun y => (le_abs_self _).trans (by
            simpa only [Real.norm_eq_abs] using
              gaussianRieszEuclideanTruncation_le_diagonal s δ hs hδ (x-y)))
      _ = _ := by simp [Measure.real, mul_comm]
  exact add_le_add hS hL

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_atom_row_bound
#check @DGRHS.Gaussian.sharpness_riesz_atom_row_bound
