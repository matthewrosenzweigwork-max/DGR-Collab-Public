import DGRHS.Gaussian.GaussianLogScaleCancellation
import DGRHS.Gaussian.GaussianRieszParticleSplit
import DGRHS.Gaussian.PhysicalStatisticAlgebra
import DGRHS.Gaussian.GaussianLogInfraredExponent

/-! Actual proper physical scale decomposition and
finite-particle comparison, transferring pair equalities only at distinct labels. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLogCentered_constant (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (C : ℝ) :
    hoeffdingCentered μ (fun _ => C) = 0 := by
  funext p
  simp [hoeffdingCentered,DGRHS.centeredKernel,DGRHS.potential,DGRHS.secondPotential]

lemma ae_gaussianLogInfrared_centered_split (α δ T : ℝ)
    (hα : 0 < α) (hαδ : α ≤ δ) (hδT : δ ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInfraredPair T)
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair δ T)+
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair α δ))+
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair α) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := gaussianLogBandPair (ι := ι) δ T
  let V := gaussianLogBandPair (ι := ι) α δ
  let R := gaussianLogShortPair (ι := ι) α
  let C := fun _ : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => gaussianLogCounterterm T
  have hδ := lt_of_lt_of_le hα hαδ
  have hT := lt_of_lt_of_le hδ hδT
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hW : Integrable W (μ.prod μ) := integrable_gaussianLogBandPair δ T hδ hδT μ
  have hV : Integrable V (μ.prod μ) := integrable_gaussianLogBandPair α δ hα hαδ μ
  have hR : Integrable R (μ.prod μ) := (memLp_gaussianLogShortPair α hα hd ρ M hM hρ).integrable (by norm_num)
  have he : gaussianLogInfraredPair T =ᵐ[μ.prod μ] ((W+V)+R)-C := by
    filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    have hz := sub_ne_zero.mpr hp
    have h1 := gaussianLogAnchored_eq_short_counterterm T hT (p.1-p.2) hz
    have h2 := gaussianLogShortRange_split δ T hδ hδT (p.1-p.2) hz
    have h3 := gaussianLogShortRange_split α δ hα hαδ (p.1-p.2) hz
    change gaussianLogAnchored T ‖p.1-p.2‖ =
      (gaussianLogBand δ T (p.1-p.2)+gaussianLogBand α δ (p.1-p.2)+gaussianLogShortRange α (p.1-p.2))-
        gaussianLogCounterterm T
    rw [h1,h2,h3]
    ring
  have h1 := ae_hoeffdingCentered_congr μ _ _ he
  have h2 := ae_hoeffdingCentered_sub μ ((W+V)+R) C ((hW.add hV).add hR) (integrable_const _)
  have h3 := ae_hoeffdingCentered_add μ (W+V) R (hW.add hV) hR
  have h4 := ae_hoeffdingCentered_add μ W V hW hV
  have hC : hoeffdingCentered μ C = 0 := gaussianLogCentered_constant μ _
  filter_upwards [h1,h2,h3,h4] with p hp1 hp2 hp3 hp4
  rw [hp1,hp2]
  simp only [Pi.sub_apply,hC,Pi.zero_apply,sub_zero]
  rw [hp3]
  simp only [Pi.add_apply]
  rw [hp4]
  rfl

lemma ae_gaussianLogInfrared_particle_split (α δ T : ℝ)
    (hα : 0 < α) (hαδ : α ≤ δ) (hδT : δ ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInfraredPair T)) ω =
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair α δ)) ω +
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair α)) ω +
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair δ T)) ω := by
  have he := ae_physical_iidNegativeStatistic_congr (gaussianRieszDensityMeasure ρ) n _ _
    (ae_gaussianLogInfrared_centered_split α δ T hα hαδ hδT hd ρ M hM hρ)
  filter_upwards [he] with ω hω
  rw [hω,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_add]
  ring

lemma ae_gaussianLogShort_particle_cap (α : ℝ) (hα : 0 < α)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair α)) ω ≤
      (n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) := by
  apply ae_physical_iidNegativeStatistic_bound _ n hn _ _ (by positivity)
  exact Filter.Eventually.of_forall (gaussianLogCenteredShortPair_lower α hα hd ρ M hM hρ)

lemma ae_gaussianLogSourceApproxExponent_comparison (α δ T β : ℝ)
    (hα : 0 < α) (hαδ : α ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω ≤
      β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair α δ)) ω +
      β*(n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) +
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let C := β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4)
  have hδ := lt_of_lt_of_le hα hαδ
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  filter_upwards [ae_gaussianLogInfrared_particle_split α δ T hα hαδ (hδ1.trans hT) hd ρ M hM hρ n,
    ae_gaussianLogShort_particle_cap α hα hd ρ M hM hρ n hn] with ω hsplit hnear
  have hlow := gaussianLogCenteredBand_particle_diagonal_cap δ T hδ (hδ1.trans hT) μ n hn ω
  have hlow' := (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ))).mp hlow
  have hs : (∑ i : Fin n,
      (β*(∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2 -
      β/2*(∫ p,gaussianLogInfraredPair T p ∂μ.prod μ))) ≤ (n : ℝ)*C := by
    calc
      _ ≤ ∑ _ : Fin n,C := Finset.sum_le_sum (fun i hi =>
        gaussianLog_source_low_diagonal_bound δ T β hδ hδ1 hT hβ hd ρ M hM hρ (ω i))
      _ = _ := by simp
  have he : (∑ i : Fin n,
      (β*(∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2 -
      β/2*(∫ p,gaussianLogInfraredPair T p ∂μ.prod μ))) =
      β*(∑ i : Fin n,(∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ)) +
      β/2*(∑ i : Fin n,‖centeredGaussianLogBandFeature δ T hδ μ (ω i)‖^2) -
      (n : ℝ)*β/2*(∫ p,gaussianLogInfraredPair T p ∂μ.prod μ) := by
    simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp
    ring
  rw [he] at hs
  have hloβ := mul_le_mul_of_nonneg_left hlow' hβ
  have hneβ := mul_le_mul_of_nonneg_left hnear hβ
  have hneβn := mul_le_mul_of_nonneg_left hneβ hn'.le
  have hex : (n : ℝ)*gaussianLogSourceApproxExponent μ β T n ω =
      (n : ℝ)*β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogInfraredPair T)) ω +
      β*(∑ i : Fin n,(∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ)) -
      (n : ℝ)*β/2*(∫ p,gaussianLogInfraredPair T p ∂μ.prod μ) := by
    unfold gaussianLogSourceApproxExponent
    field_simp <;> ring
  change gaussianLogSourceApproxExponent μ β T n ω ≤ _
  change iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogInfraredPair T)) ω = _ at hsplit
  have hnle : 0 ≤ (n : ℝ) := hn'.le
  suffices hscaled : (n : ℝ)*gaussianLogSourceApproxExponent μ β T n ω ≤
      (n : ℝ)*(β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair α δ)) ω +
      β*(n : ℝ)*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*α^(Fintype.card ι : ℝ))) +
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4)) by
    exact (mul_le_mul_iff_right₀ hn').mp (by simpa only [mul_comm] using hscaled)
  rw [hex,hsplit]
  dsimp [C] at hs
  nlinarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogCentered_constant
#print axioms DGRHS.Gaussian.gaussianLogCentered_constant
#check DGRHS.Gaussian.ae_gaussianLogInfrared_centered_split
#print axioms DGRHS.Gaussian.ae_gaussianLogInfrared_centered_split
#check DGRHS.Gaussian.ae_gaussianLogInfrared_particle_split
#print axioms DGRHS.Gaussian.ae_gaussianLogInfrared_particle_split
#check DGRHS.Gaussian.ae_gaussianLogShort_particle_cap
#print axioms DGRHS.Gaussian.ae_gaussianLogShort_particle_cap
#check DGRHS.Gaussian.ae_gaussianLogSourceApproxExponent_comparison
#print axioms DGRHS.Gaussian.ae_gaussianLogSourceApproxExponent_comparison
