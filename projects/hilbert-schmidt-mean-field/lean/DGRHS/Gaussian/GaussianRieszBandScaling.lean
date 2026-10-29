import DGRHS.Gaussian.GaussianRieszBandPositiveCap
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual scalar scaling of the SAME band, and one fixed physical scale making
all three genuine master norms small. The scale is independent of eta/n/u. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussian_integralOperator_const_smul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X × X → ℝ)
    (hW : MemLp W 2 (μ.prod μ)) (c : ℝ) :
    DGRHS.Kernel.integralOperator (c • W) (hW.const_smul c) =
      c • DGRHS.Kernel.integralOperator W hW := by
  unfold DGRHS.Kernel.integralOperator
  rw [MemLp.toLp_const_smul, map_smul]

lemma gaussianRieszScaledCenteredBand_square_controls (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszBandPair s η δ)) (x,y)^2 ∂gaussianRieszDensityMeasure ρ) ≤
          16*c^2*gaussianRieszBandRowControl s δ M ι) ∧
    (∫ p, (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszBandPair s η δ)) p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
        16*c^2*gaussianRieszBandRowControl s δ M ι := by
  obtain ⟨hr,hj⟩ := gaussianRieszCenteredBand_square_controls s η δ hs hη hηδ ha ρ M hM hρ
  constructor
  · filter_upwards [hr] with x hx
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg c)]
  · simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg c)]

lemma norm_gaussianRieszScaledCenteredBand_operator_le (s η δ c : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator
      (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ))
      ((memLp_gaussianRieszCenteredBand s η δ hs hη hηδ ha ρ M hM hρ).const_smul c)‖ ≤
        4*|c| *Real.sqrt (gaussianRieszBandRowControl s δ M ι) := by
  rw [gaussian_integralOperator_const_smul, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left
    (norm_gaussianRieszCenteredBand_operator_le s η δ hs hη hηδ ha ρ M hM hρ) (abs_nonneg c)
  simpa only [mul_left_comm, mul_assoc] using h

lemma exists_gaussianRieszBand_small_scale (s c M ε : ℝ) (hM : 0 ≤ M)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      16*c^2*gaussianRieszBandRowControl s δ M ι < ε ∧
      4*|c| *Real.sqrt (gaussianRieszBandRowControl s δ M ι) < ε := by
  have hp : 0 < (Fintype.card ι : ℝ)-2*s := by linarith
  have ht : Tendsto (fun δ : ℝ => gaussianRieszBandRowControl s δ M ι)
      (𝓝[>] 0) (𝓝 0) := by
    unfold gaussianRieszBandRowControl
    have hr := (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝[>] 0)).mono_right nhdsWithin_le_nhds
    simpa only [mul_zero, id_eq] using (hr.rpow_const_nhds_zero hp).const_mul
      (M*(gaussianRieszSourceCoefficient s^2*Real.pi^((Fintype.card ι : ℝ)/2) /
        (((Fintype.card ι : ℝ)/2-s)^2)))
  have htr : Tendsto (fun δ => 16*c^2*gaussianRieszBandRowControl s δ M ι)
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero] using ht.const_mul (16*c^2)
  have hto : Tendsto (fun δ => 4*|c| *Real.sqrt (gaussianRieszBandRowControl s δ M ι))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp ht).const_mul (4*|c|)
  have he := (htr.eventually (gt_mem_nhds hε)).and (hto.eventually (gt_mem_nhds hε))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hd : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < 1 :=
    hpos.and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  obtain ⟨δ,hb,hpos,hlt⟩ := (he.and hd).exists
  exact ⟨δ,hpos,hlt,hb.1,hb.2⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussian_integralOperator_const_smul
#print axioms DGRHS.Gaussian.gaussian_integralOperator_const_smul

#check DGRHS.Gaussian.gaussianRieszScaledCenteredBand_square_controls
#print axioms DGRHS.Gaussian.gaussianRieszScaledCenteredBand_square_controls

#check DGRHS.Gaussian.norm_gaussianRieszScaledCenteredBand_operator_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszScaledCenteredBand_operator_le

#check DGRHS.Gaussian.exists_gaussianRieszBand_small_scale
#print axioms DGRHS.Gaussian.exists_gaussianRieszBand_small_scale
