import DGRHS.Gaussian.PeriodicHeatFourierKernel
import DGRHS.Gaussian.SeparableFeatureEvaluation

/-! A genuine separable Hilbert feature for the full heat kernel. Square-root
coefficient summability gives uniform convergence and continuity into l2. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ComplexConjugate lp InnerProductSpace ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

abbrev PeriodicHeatFeatureSpace (ι : Type u) := ℓ²(PeriodicFrequency ι,ℂ)

def periodicHeatFeatureCoefficient (τ : ℝ) (x : PeriodicTorus ι) (k : PeriodicFrequency ι) : ℂ :=
  (Real.sqrt (periodicHeatCoefficient τ k):ℂ)*UnitAddTorus.mFourier k x

lemma periodicHeatFeatureCoefficient_norm (τ : ℝ) (x : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    ‖periodicHeatFeatureCoefficient τ x k‖=Real.sqrt (periodicHeatCoefficient τ k) := by
  simp only [periodicHeatFeatureCoefficient,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),periodic_mFourier_norm_apply,mul_one]

lemma periodicHeatFeatureCoefficient_mem (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) :
    Memℓp (periodicHeatFeatureCoefficient τ x) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_ofNat,periodicHeatFeatureCoefficient_norm,Real.rpow_two,
    Real.sq_sqrt (periodicHeatCoefficient_nonneg τ _)] using periodicHeatCoefficient_summable (ι := ι) τ hτ

def periodicHeatFeature (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) : PeriodicHeatFeatureSpace ι :=
  ⟨periodicHeatFeatureCoefficient τ x,periodicHeatFeatureCoefficient_mem τ hτ x⟩

lemma periodicHeatFeature_apply (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    periodicHeatFeature τ hτ x k=periodicHeatFeatureCoefficient τ x k := rfl

lemma periodicHeatFeature_series (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) :
    periodicHeatFeature τ hτ x=∑' k : PeriodicFrequency ι,lp.single 2 k (periodicHeatFeatureCoefficient τ x k) :=
  (lp.hasSum_single (by norm_num) (periodicHeatFeature τ hτ x)).tsum_eq.symm

lemma periodicHeatFeature_continuous (τ : ℝ) (hτ : 0<τ) :
    Continuous (periodicHeatFeature (ι := ι) τ hτ) := by
  have he : periodicHeatFeature (ι := ι) τ hτ =
      fun x => ∑' k : PeriodicFrequency ι,lp.single 2 k (periodicHeatFeatureCoefficient τ x k) :=
    funext (periodicHeatFeature_series τ hτ)
  rw [he]
  apply continuous_tsum (fun k =>
    (lp.isometry_single (p := 2) (E := fun _ : PeriodicFrequency ι => ℂ) k).continuous.comp
      (continuous_const.mul (UnitAddTorus.mFourier k).continuous)) (periodicHeatCoefficient_sqrt_summable τ hτ)
  intro k x
  change ‖(lp.single 2 k (periodicHeatFeatureCoefficient τ x k):PeriodicHeatFeatureSpace ι)‖≤_
  rw [lp.norm_single (by norm_num),periodicHeatFeatureCoefficient_norm]

lemma periodicHeatFeature_norm_bound (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) :
    ‖periodicHeatFeature τ hτ x‖≤∑' k : PeriodicFrequency ι,Real.sqrt (periodicHeatCoefficient τ k) := by
  rw [periodicHeatFeature_series]
  have hn : Summable (fun k : PeriodicFrequency ι => ‖(lp.single 2 k (periodicHeatFeatureCoefficient τ x k):PeriodicHeatFeatureSpace ι)‖) := by
    simpa only [lp.norm_single (by norm_num : (0:ℝ≥0∞)<2),periodicHeatFeatureCoefficient_norm] using
      periodicHeatCoefficient_sqrt_summable (ι := ι) τ hτ
  simpa only [lp.norm_single (by norm_num : (0:ℝ≥0∞)<2),periodicHeatFeatureCoefficient_norm] using norm_tsum_le_tsum_norm hn

lemma periodicHeatFeature_memLp (τ : ℝ) (hτ : 0<τ) :
    MemLp (periodicHeatFeature (ι := ι) τ hτ) 2 (periodicHaar ι) :=
  MemLp.of_bound (periodicHeatFeature_continuous τ hτ).aestronglyMeasurable _
    (Eventually.of_forall (periodicHeatFeature_norm_bound τ hτ))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatFeature_continuous
#print axioms DGRHS.Periodic.periodicHeatFeature_memLp
#check @DGRHS.Periodic.periodicHeatFeature_continuous
