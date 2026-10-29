import DGRHS.Gaussian.GaussianRieszBandScaling
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! The actual scaled centered positive physical band has the measurable,
bounded, symmetric, canonical and deterministic cap prerequisites of the
master backend. These are derived from the SAME Fourier Gram feature. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianRieszMasterBand (s η δ c : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  c • hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ)

lemma measurable_gaussianRieszMasterBand (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (gaussianRieszMasterBand s η δ c ρ) :=
  ((stronglyMeasurable_hoeffdingCentered _ _
    (stronglyMeasurable_gaussianRieszBandPair s η δ hs hη hηδ)).const_smul c).measurable

lemma memLp_infty_gaussianRieszMasterBand (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (gaussianRieszMasterBand s η δ c ρ) ∞
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  (memLp_infty_gaussianRieszCenteredBand s η δ hs hη hηδ ha ρ M hM hρ).const_smul c

lemma gaussianRieszMasterBand_symmetric (s η δ c : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x y : EuclideanSpace ℝ ι) :
    gaussianRieszMasterBand s η δ c ρ (x,y)=gaussianRieszMasterBand s η δ c ρ (y,x) := by
  unfold gaussianRieszMasterBand
  simp only [Pi.smul_apply,smul_eq_mul,
    gaussianRieszCenteredBand_symmetric s η δ (gaussianRieszDensityMeasure ρ) x y]

lemma gaussianRieszMasterBand_canonical (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      ∫ y,gaussianRieszMasterBand s η δ c ρ (x,y) ∂gaussianRieszDensityMeasure ρ = 0 := by
  filter_upwards [gaussianRieszCenteredBand_canonical s η δ hs hη hηδ ha ρ M hM hρ] with x hx
  unfold gaussianRieszMasterBand
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [integral_const_mul,hx,mul_zero]

lemma norm_gaussianRieszMasterBand_le (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖gaussianRieszMasterBand s η δ c ρ p‖ ≤
      4*|c| * (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  unfold gaussianRieszMasterBand
  rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left
    (norm_gaussianRieszCenteredBand_le s η δ hs hη hηδ ha ρ M hM hρ p) (abs_nonneg c)
  simpa only [mul_assoc,mul_left_comm] using h

lemma essential_gaussianRieszMasterBand_le (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (eLpNormEssSup (gaussianRieszMasterBand s η δ c ρ)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))).toReal ≤
      4*|c| * (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hC : 0 ≤ 4*|c| * (gaussianRieszSourceCoefficient s/s*η^(-s)) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have h := eLpNormEssSup_le_of_ae_bound
    (μ := (gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))
    (Filter.Eventually.of_forall (norm_gaussianRieszMasterBand_le s η δ c hs hη hηδ ha ρ M hM hρ))
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

lemma gaussianRieszMasterBand_particle_cap (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s) (hc : 0 ≤ c)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    iidNegativeStatistic n (gaussianRieszMasterBand s η δ c ρ) ω ≤
      2*c*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  classical
  have hb : iidNegativeStatistic n
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ)) ω ≤
        2*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
    simpa only [iidNegativeStatistic,iidCoupledSum,DGRHS.Decoupling.offDiagonalSum,ite_not]
      using gaussianRieszCenteredBand_particle_cap s η δ hs hη hηδ ha ρ M hM hρ n hn ω
  unfold gaussianRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  nlinarith [mul_le_mul_of_nonneg_left hb hc]

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszMasterBand
#print axioms DGRHS.Gaussian.gaussianRieszMasterBand

#check DGRHS.Gaussian.measurable_gaussianRieszMasterBand
#print axioms DGRHS.Gaussian.measurable_gaussianRieszMasterBand

#check DGRHS.Gaussian.memLp_infty_gaussianRieszMasterBand
#print axioms DGRHS.Gaussian.memLp_infty_gaussianRieszMasterBand

#check DGRHS.Gaussian.gaussianRieszMasterBand_symmetric
#print axioms DGRHS.Gaussian.gaussianRieszMasterBand_symmetric

#check DGRHS.Gaussian.gaussianRieszMasterBand_canonical
#print axioms DGRHS.Gaussian.gaussianRieszMasterBand_canonical

#check DGRHS.Gaussian.norm_gaussianRieszMasterBand_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszMasterBand_le

#check DGRHS.Gaussian.essential_gaussianRieszMasterBand_le
#print axioms DGRHS.Gaussian.essential_gaussianRieszMasterBand_le

#check DGRHS.Gaussian.gaussianRieszMasterBand_particle_cap
#print axioms DGRHS.Gaussian.gaussianRieszMasterBand_particle_cap
