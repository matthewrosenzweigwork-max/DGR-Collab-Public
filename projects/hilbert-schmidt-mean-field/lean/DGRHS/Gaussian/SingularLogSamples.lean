import DGRHS.Gaussian.SingularLogIntegrability
import DGRHS.Decoupling.Product
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The original singular pair-L1 assumption excludes every off-diagonal
particle collision almost everywhere under the actual iid law, without
bounded density or a pointwise collision-free sample assumption. -/
theorem singularAbsLog_iid_collision_free (μ : Measure E) [IsProbabilityMeasure μ]
    (hf : (∫⁻ p,singularAbsLog p ∂μ.prod μ)<∞) (N : ℕ) :
    ∀ᵐ x : Fin N → E ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin N,i ≠ j → x i ≠ x j := by
  classical
  have hne := ((singularAbsLog_finite_iff μ).mp hf).2
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun x h => (h hij).elim
  · exact (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij).quasiMeasurePreserving.ae hne
      |>.mono (fun x hx _ => hx)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.singularAbsLog_iid_collision_free
#print axioms DGRHS.Gaussian.singularAbsLog_iid_collision_free
