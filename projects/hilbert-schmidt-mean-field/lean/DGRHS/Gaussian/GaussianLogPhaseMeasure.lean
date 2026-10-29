import DGRHS.Gaussian.GaussianLogBand
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Supporting development. Actual sigma-finite logarithmic scale-frequency law and its
finite-band restrictions. It is never asserted to be a probability measure. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian

def gaussianLogInfiniteScaleMeasure (η : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi η)).withDensity (fun t => ENNReal.ofReal t⁻¹)

lemma sigmaFinite_gaussianLogInfiniteScaleMeasure (η : ℝ) :
    SigmaFinite (gaussianLogInfiniteScaleMeasure η) := by
  unfold gaussianLogInfiniteScaleMeasure
  infer_instance

attribute [instance] sigmaFinite_gaussianLogInfiniteScaleMeasure

def gaussianLogPhaseMeasure (ι : Type*) [Fintype ι] (η : ℝ) : Measure (ℝ × (ι → ℝ)) :=
  (gaussianLogInfiniteScaleMeasure η).prod (finiteStandardGaussian ι)

lemma sigmaFinite_gaussianLogPhaseMeasure (ι : Type*) [Fintype ι] (η : ℝ) :
    SigmaFinite (gaussianLogPhaseMeasure ι η) := by
  unfold gaussianLogPhaseMeasure
  infer_instance

attribute [instance] sigmaFinite_gaussianLogPhaseMeasure

lemma gaussianLogInfiniteScaleMeasure_restrict (η T : ℝ) :
    (gaussianLogInfiniteScaleMeasure η).restrict (Iic T) = gaussianLogBandMeasure η T := by
  unfold gaussianLogInfiniteScaleMeasure gaussianLogBandMeasure
  rw [restrict_withDensity measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have he : Iic T ∩ Ioi η = Ioc η T := by
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]
    exact and_comm
  rw [he]

lemma gaussianLogPhaseMeasure_restrict (ι : Type*) [Fintype ι] (η T : ℝ) :
    (gaussianLogPhaseMeasure ι η).restrict (Iic T ×ˢ univ) =
      (gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι) := by
  unfold gaussianLogPhaseMeasure
  rw [← Measure.prod_restrict, Measure.restrict_univ, gaussianLogInfiniteScaleMeasure_restrict]

lemma gaussianLogPhase_band_exhaustion (ι : Type*) [Fintype ι] (η : ℝ) :
    (⋃ j : ℕ, Iic (max η (j+1 : ℕ)) ×ˢ (univ : Set (ι → ℝ))) = univ := by
  ext p
  simp only [mem_iUnion,mem_prod,mem_Iic,mem_univ,and_true,iff_true]
  obtain ⟨j,hj⟩ := exists_nat_gt p.1
  refine ⟨j, (le_of_lt hj).trans ?_⟩
  have hj' : (j : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (Nat.le_succ j)
  exact hj'.trans (le_max_right _ _)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogInfiniteScaleMeasure
#print axioms DGRHS.Gaussian.gaussianLogInfiniteScaleMeasure
#check @DGRHS.Gaussian.sigmaFinite_gaussianLogInfiniteScaleMeasure
#print axioms DGRHS.Gaussian.sigmaFinite_gaussianLogInfiniteScaleMeasure
#check @DGRHS.Gaussian.gaussianLogPhaseMeasure
#print axioms DGRHS.Gaussian.gaussianLogPhaseMeasure
#check @DGRHS.Gaussian.sigmaFinite_gaussianLogPhaseMeasure
#print axioms DGRHS.Gaussian.sigmaFinite_gaussianLogPhaseMeasure
#check @DGRHS.Gaussian.gaussianLogInfiniteScaleMeasure_restrict
#print axioms DGRHS.Gaussian.gaussianLogInfiniteScaleMeasure_restrict
#check @DGRHS.Gaussian.gaussianLogPhaseMeasure_restrict
#print axioms DGRHS.Gaussian.gaussianLogPhaseMeasure_restrict
#check @DGRHS.Gaussian.gaussianLogPhase_band_exhaustion
#print axioms DGRHS.Gaussian.gaussianLogPhase_band_exhaustion
