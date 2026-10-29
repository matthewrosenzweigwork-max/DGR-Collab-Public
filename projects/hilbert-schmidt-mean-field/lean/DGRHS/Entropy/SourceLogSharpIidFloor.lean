/- Genuine sharp iid logarithmic energy control. Finite infrared Gram
diagonal cancellation is used before the limit. This is an iid-a.e. bound,
not a promotion of product-a.e. positivity to arbitrary configurations. -/
import DGRHS.Gaussian.GaussianLogParticleSplit
import DGRHS.Gaussian.GaussianLogAdaptiveComparison
import DGRHS.CLT.SourceLogUniform
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

theorem logPhysicalMomentExponent_sharp_scale_ae (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ),
      logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) 1 N x ≤
        ((N : ℝ)+1)*gaussianLogShortConstant M ι*δ^(Fintype.card ι : ℝ) +
          (-Real.log δ+1/4)/2 := by
  let μ := gaussianRieszDensityMeasure ρ
  let T := fun j : ℕ => ((j+1 : ℕ) : ℝ)
  have hT : Tendsto T atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hT1 (j : ℕ) : 1 ≤ T j := by dsimp [T]; exact_mod_cast (Nat.le_add_left 1 j)
  have hz : hoeffdingCentered μ (gaussianLogBandPair δ δ) = 0 := by
    funext p
    simp [hoeffdingCentered, DGRHS.centeredKernel, DGRHS.potential,
      DGRHS.secondPotential, gaussianLogBandPair, gaussianLogBand]
  have hs (j : ℕ) : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      gaussianLogSourceApproxExponent μ 1 (T j) N x ≤
        ((N : ℝ)+1)*gaussianLogShortConstant M ι*δ^(Fintype.card ι : ℝ) +
          (-Real.log δ+1/4)/2 := by
    filter_upwards [ae_gaussianLogSourceApproxExponent_comparison δ δ (T j) 1
      hδ le_rfl hδ1 (hT1 j) (by norm_num) hd ρ M hM hρ N hN] with x hx
    rw [hz] at hx
    simp only [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum,
      Pi.zero_apply, ite_self, Finset.sum_const_zero, neg_zero, zero_div,
      mul_zero, one_mul, zero_add] at hx
    dsimp [gaussianLogShortConstant]
    nlinarith [hx]
  filter_upwards [ae_all_iff.mpr hs,
    ae_tendsto_gaussianLogSourceApproxExponent T hT hd ρ M hM hρ hpair 1 N] with x hx hlim
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun j => hx j))

theorem logPhysicalMomentExponent_sharp_logN_ae
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ),
      logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) 1 N x ≤
        2*gaussianLogShortConstant M ι+1/8+
          Real.log (N : ℝ)/(2*(Fintype.card ι : ℝ)) := by
  let d := (Fintype.card ι : ℝ)
  have hdne : d ≠ 0 := ne_of_gt hd
  let δ := Real.exp (-Real.log (N : ℝ)/d)
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hnp : 0 < (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  have hpower : δ^d = (N : ℝ)⁻¹ := by
    dsimp [δ]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have he : (-Real.log (N : ℝ)/d)*d = -Real.log (N : ℝ) := by field_simp [hdne]
    rw [he, Real.exp_neg, Real.exp_log hnp]
  have hδlog : Real.log δ = -Real.log (N : ℝ)/d := Real.log_exp _
  have hc := gaussianLogShortConstant_nonneg (ι := ι) M hM hd
  have hi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  filter_upwards [logPhysicalMomentExponent_sharp_scale_ae δ hδ hδ1 hd ρ M hM hρ hpair N hN] with x hx
  change logPhysicalMomentExponent _ 1 N x ≤ ((N : ℝ)+1)*gaussianLogShortConstant M ι*δ^d +
    (-Real.log δ+1/4)/2 at hx
  rw [hpower, hδlog] at hx
  have he : ((N : ℝ)+1)*gaussianLogShortConstant M ι*(N : ℝ)⁻¹ =
      gaussianLogShortConstant M ι+gaussianLogShortConstant M ι*(N : ℝ)⁻¹ := by
    field_simp
  rw [he] at hx
  have hterm := mul_le_mul_of_nonneg_left hi hc
  have hnorm : (-(-Real.log (N : ℝ)/d)+1/4)/2 =
      1/8+Real.log (N : ℝ)/(2*d) := by field_simp <;> ring
  rw [hnorm] at hx
  dsimp [d] at *
  nlinarith [hx]

end DGRHS.Entropy
#check @DGRHS.Entropy.logPhysicalMomentExponent_sharp_scale_ae
#check @DGRHS.Entropy.logPhysicalMomentExponent_sharp_logN_ae
#print axioms DGRHS.Entropy.logPhysicalMomentExponent_sharp_scale_ae
#print axioms DGRHS.Entropy.logPhysicalMomentExponent_sharp_logN_ae
