import DGRHS.Gaussian.GaussianLogCutoffMasterData
import DGRHS.Gaussian.GaussianLogSourceMoment

/-! Supporting development: actual source cutoff factory, uniform in both finite IR scale
and all physical UV cutoffs below a genuinely selected common scale. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma measurable_gaussianLogCutoffApproxExponent (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (β η T : ℝ) (hη : 0 < η) (n : ℕ) :
    Measurable (gaussianLogCutoffApproxExponent μ β η T n) := by
  classical
  have hm : StronglyMeasurable (gaussianLogBandPair (ι := ι) η T) :=
    (stronglyMeasurable_gaussianLogBand η T hη).comp_measurable (by fun_prop)
  have hs := measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _ hm).measurable
  have hp : StronglyMeasurable (fun x => ∫ y,gaussianLogBandPair η T (x,y) ∂μ) :=
    hm.integral_prod_right'
  have hsum : Measurable (fun ω : Fin n → EuclideanSpace ℝ ι =>
      ∑ i : Fin n,∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) := by
    apply Finset.measurable_sum
    intro i hi
    exact hp.measurable.comp (measurable_pi_apply i)
  unfold gaussianLogCutoffApproxExponent
  exact (((hs.const_mul β).add (hsum.const_mul (β/(n : ℝ)))).sub_const _).sub_const _

theorem gaussianLogCutoffSource_finiteIR_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∃ C : ℝ,∀ η : ℝ,0 < η → η ≤ δ →
      ∀ T : ℝ,1 ≤ T → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨δ,hδ,hδ1,hrow,hop⟩ := exists_gaussianLogMaster_scale (ι := ι) β M hM hd
  let A := 1+8*gaussianLogShortConstant M ι
  let u₀ := 1+4*gaussianLogSourceLowConstant δ β M ι
  have hc := gaussianLogShortConstant_nonneg (ι := ι) M hM hd
  have hA : 0 < A := by dsimp [A];positivity
  have hAC : 8*gaussianLogShortConstant M ι ≤ A := by dsimp [A];linarith
  have hclow : 0 ≤ gaussianLogSourceLowConstant δ β M ι := by
    have hlog := Real.log_nonpos hδ.le hδ1.le
    have hterm : 0 ≤ -Real.log δ+1/4 := by linarith
    unfold gaussianLogSourceLowConstant
    positivity
  have hu₀ : 1 ≤ u₀ := by dsimp [u₀];linarith
  have hlow : 4*gaussianLogSourceLowConstant δ β M ι ≤ u₀ := by dsimp [u₀];linarith
  let I := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ δ ∧ 1 ≤ p.2}
  let X := fun (θ : I) (n : ℕ) => gaussianLogCutoffApproxExponent μ β θ.val.1 θ.val.2 n
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) : AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianLogCutoffApproxExponent μ β θ.val.1 θ.val.2 θ.property.1 n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => gaussianLogCutoffSourceMasterData θ.val.1 δ θ.val.2 β A u₀
    θ.property.1 θ.property.2.1 hδ hδ1.le θ.property.2.2 hβ hd ρ M hM hρ n hn hA hAC hu₀ hlow hrow.le hop.le
  let K := (2+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ))^2
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤ 0+K*(n : ℝ)^(2/3 : ℝ) := by
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (gaussianLogCutoffAdaptive_actual_size_bound θ.val.1 δ A β (n : ℝ) u₀ θ.property.1 θ.property.2.1 hδ hδ1.le hA hβ hn' hu₀ hd μ).2
    simpa only [data,gaussianLogCutoffSourceMasterData,K,zero_add] using hz
  obtain ⟨C,hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2/3 : ℝ) (by norm_num) hsize
  exact ⟨δ,hδ,hδ1.le,C,fun η hη hηδ T hT n hn => hC ⟨(η,T),hη,hηδ,hT⟩ n hn⟩


end DGRHS.Gaussian

#check @DGRHS.Gaussian.measurable_gaussianLogCutoffApproxExponent
#print axioms DGRHS.Gaussian.measurable_gaussianLogCutoffApproxExponent
#check @DGRHS.Gaussian.gaussianLogCutoffSource_finiteIR_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogCutoffSource_finiteIR_uniform_exponential
