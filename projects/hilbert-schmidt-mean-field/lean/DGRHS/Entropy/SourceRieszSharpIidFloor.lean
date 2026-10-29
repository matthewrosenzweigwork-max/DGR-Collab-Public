/- Genuine iid singular Riesz floor, using actual finite-cutoff Gram
positivity and the proper near-kernel bound before the singular limit. -/
import DGRHS.Gaussian.GaussianRieszFullMoment
import DGRHS.Gaussian.GaussianRieszParticleComparison
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

theorem rieszNegativeStatistic_sharp_scale_ae (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s)) x ≤
      2*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
        (N : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*δ^((Fintype.card ι : ℝ)-s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let η := fun j : ℕ => δ*((((j+1 : ℕ) : ℝ))⁻¹)
  have hη (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hηδ (j : ℕ) : η j ≤ δ := by
    have hn : 1 ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
    exact mul_le_of_le_one_right hδ.le (inv_le_one_of_one_le₀ hn)
  have hcast : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hη0 : Tendsto η atTop (𝓝 0) := by
    simpa only [η, Pi.inv_apply, mul_zero] using hcast.inv_tendsto_atTop.const_mul δ
  have hz : hoeffdingCentered μ (gaussianRieszBandPair s δ δ) = 0 := by
    funext p
    simp [hoeffdingCentered, DGRHS.centeredKernel, DGRHS.potential,
      DGRHS.secondPotential, gaussianRieszBandPair, gaussianRieszEuclideanBand]
  have hb (j : ℕ) : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      iidNegativeStatistic N (hoeffdingCentered μ (gaussianRieszTruncatedPair s (η j))) x ≤
      2*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
        (N : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*δ^((Fintype.card ι : ℝ)-s))) := by
    filter_upwards [ae_gaussianRieszParticle_low_near_bound s (η j) δ δ 1 hs
      (hη j) (hηδ j) le_rfl (by norm_num) ha ρ M hM hρ N hN] with x hx
    rw [hz] at hx
    simpa only [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum,
      Pi.zero_apply, ite_self, Finset.sum_const_zero, neg_zero, zero_div,
      mul_zero, one_mul, mul_one, zero_add, μ] using hx
  filter_upwards [ae_all_iff.mpr hb,
    ae_tendsto_gaussianRieszParticleCutoff s 1 hs ha ρ M hM hρ η hη hη0 N] with x hx hlim
  simp only [one_mul] at hlim
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun j => hx j))

theorem rieszNegativeStatistic_sharp_Npower_ae (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s)) x ≤
      (2*gaussianRieszSourceCoefficient s/s+
        M*gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s))*(N : ℝ)^(s/(Fintype.card ι : ℝ)) := by
  let d := (Fintype.card ι : ℝ)
  have hd : 0 < d := by dsimp [d]; linarith
  have hdne : d ≠ 0 := ne_of_gt hd
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let δ := Real.exp (-Real.log (N : ℝ)/d)
  have hδ : 0 < δ := Real.exp_pos _
  have hlong : δ^(-s) = (N : ℝ)^(s/d) := by
    dsimp [δ]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hnp]
    congr 1
    ring
  have hshort : (N : ℝ)*δ^(d-s) = (N : ℝ)^(s/d) := by
    calc
      _ = Real.exp (Real.log (N : ℝ))*Real.exp ((-Real.log (N : ℝ)/d)*(d-s)) := by
        rw [Real.exp_log hnp]
        congr 1
        dsimp [δ]
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      _ = _ := by
        rw [←Real.exp_add, Real.rpow_def_of_pos hnp]
        congr 1
        field_simp [hdne] <;> ring
  filter_upwards [rieszNegativeStatistic_sharp_scale_ae s δ hs hδ ha ρ M hM hρ N hN] with x hx
  change _ ≤ 2*(gaussianRieszSourceCoefficient s/s*δ^(-s)) +
    (N : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^(d/2)/(d-s)*δ^(d-s))) at hx
  rw [hlong] at hx
  have he : (N : ℝ)*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^(d/2)/(d-s)*δ^(d-s))) =
      (M*gaussianRieszSourceCoefficient s*(2*Real.pi)^(d/2)/(d-s))*((N : ℝ)*δ^(d-s)) := by ring
  rw [he, hshort] at hx
  dsimp [d] at *
  simp only [div_eq_mul_inv] at hx ⊢
  nlinarith [hx]

end DGRHS.Entropy
#check @DGRHS.Entropy.rieszNegativeStatistic_sharp_scale_ae
#check @DGRHS.Entropy.rieszNegativeStatistic_sharp_Npower_ae
#print axioms DGRHS.Entropy.rieszNegativeStatistic_sharp_scale_ae
#print axioms DGRHS.Entropy.rieszNegativeStatistic_sharp_Npower_ae
