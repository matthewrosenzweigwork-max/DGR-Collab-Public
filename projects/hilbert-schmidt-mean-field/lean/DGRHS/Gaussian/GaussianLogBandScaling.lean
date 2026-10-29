import DGRHS.Gaussian.GaussianLogBandCentered
import DGRHS.Gaussian.GaussianRieszBandScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual scalar scaling of the SAME band, and one fixed physical scale making
all three genuine master norms small. The scale is independent of eta/n/u. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianLogScaledCenteredBand_square_controls (η δ c : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianLogBandPair η δ)) (x,y)^2 ∂gaussianRieszDensityMeasure ρ) ≤
          16*c^2*gaussianLogBandRowControl δ M ι) ∧
    (∫ p, (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianLogBandPair η δ)) p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
        16*c^2*gaussianLogBandRowControl δ M ι := by
  obtain ⟨hr,hj⟩ := gaussianLogCenteredBand_square_controls η δ hη hηδ hd ρ M hM hρ
  constructor
  · filter_upwards [hr] with x hx
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg c)]
  · simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg c)]

lemma norm_gaussianLogScaledCenteredBand_operator_le (η δ c : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator
      (c • hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η δ))
      ((memLp_gaussianLogCenteredBand η δ hη hηδ hd ρ M hM hρ).const_smul c)‖ ≤
        4*|c| *Real.sqrt (gaussianLogBandRowControl δ M ι) := by
  rw [gaussian_integralOperator_const_smul, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left
    (norm_gaussianLogCenteredBand_operator_le η δ hη hηδ hd ρ M hM hρ) (abs_nonneg c)
  simpa only [mul_left_comm, mul_assoc] using h

lemma gaussianLogBandRowControl_factor (δ M : ℝ) (hδ : 0 < δ) :
    gaussianLogBandRowControl δ M ι =
      (M*Real.pi^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2)^2)*δ^(Fintype.card ι : ℝ) := by
  unfold gaussianLogBandRowControl
  rw [div_pow]
  have he : (δ^((Fintype.card ι : ℝ)/2))^2 = δ^(Fintype.card ι : ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [he]
  ring

lemma exists_gaussianLogBand_small_scale (c M ε : ℝ) (hM : 0 ≤ M)
    (hd : 0 < (Fintype.card ι : ℝ)) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      16*c^2*gaussianLogBandRowControl δ M ι < ε ∧
      4*|c| *Real.sqrt (gaussianLogBandRowControl δ M ι) < ε := by
  have ht : Tendsto (fun δ : ℝ => gaussianLogBandRowControl δ M ι)
      (𝓝[>] 0) (𝓝 0) := by
    have hr := (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝[>] 0)).mono_right nhdsWithin_le_nhds
    have hpow := (hr.rpow_const_nhds_zero hd).const_mul
      (M*Real.pi^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2)^2)
    apply (show Tendsto (fun δ : ℝ =>
      (M*Real.pi^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2)^2)*δ^(Fintype.card ι : ℝ))
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero,id_eq] using hpow).congr'
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] 0,0 < δ)] with δ hδ
    exact (gaussianLogBandRowControl_factor δ M hδ).symm
  have htr : Tendsto (fun δ => 16*c^2*gaussianLogBandRowControl δ M ι)
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero] using ht.const_mul (16*c^2)
  have hto : Tendsto (fun δ => 4*|c| *Real.sqrt (gaussianLogBandRowControl δ M ι))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp ht).const_mul (4*|c|)
  have he := (htr.eventually (gt_mem_nhds hε)).and (hto.eventually (gt_mem_nhds hε))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0,0 < δ := self_mem_nhdsWithin
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0,0 < δ ∧ δ < 1 :=
    hpos.and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  obtain ⟨δ,hb,hpos,hlt⟩ := (he.and hsmall).exists
  exact ⟨δ,hpos,hlt,hb.1,hb.2⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogScaledCenteredBand_square_controls
#print axioms DGRHS.Gaussian.gaussianLogScaledCenteredBand_square_controls
#check DGRHS.Gaussian.norm_gaussianLogScaledCenteredBand_operator_le
#print axioms DGRHS.Gaussian.norm_gaussianLogScaledCenteredBand_operator_le
#check DGRHS.Gaussian.gaussianLogBandRowControl_factor
#print axioms DGRHS.Gaussian.gaussianLogBandRowControl_factor
#check DGRHS.Gaussian.exists_gaussianLogBand_small_scale
#print axioms DGRHS.Gaussian.exists_gaussianLogBand_small_scale
