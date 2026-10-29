import DGRHS.Gaussian.GaussianLogMasterData
import DGRHS.Gaussian.GaussianRieszCutoffMoment
import DGRHS.Concentration.MasterLimit

/-! Uniform proper source moments are derived from the
actual physical adaptive data, then genuine singular convergence and Fatou. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma measurable_gaussianLogSourceApproxExponent (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (β T : ℝ) (n : ℕ) :
    Measurable (gaussianLogSourceApproxExponent μ β T n) := by
  classical
  have hm := stronglyMeasurable_gaussianLogInfraredPair (ι := ι) T
  have hs := measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _ hm).measurable
  have hp : StronglyMeasurable (fun x => ∫ y,gaussianLogInfraredPair T (x,y) ∂μ) :=
    hm.integral_prod_right'
  have hsum : Measurable (fun ω : Fin n → EuclideanSpace ℝ ι =>
      ∑ i : Fin n,∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ) := by
    apply Finset.measurable_sum
    intro i hi
    exact hp.measurable.comp (measurable_pi_apply i)
  unfold gaussianLogSourceApproxExponent
  exact ((hs.const_mul β).add (hsum.const_mul (β/(n : ℝ)))).sub_const _

theorem gaussianLogSource_finiteIR_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ C : ℝ,∀ T : ℝ,1 ≤ T → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω)
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
  let I := {T : ℝ // 1 ≤ T}
  let X := fun (θ : I) (n : ℕ) => gaussianLogSourceApproxExponent μ β θ.val n
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) : AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianLogSourceApproxExponent μ β θ.val n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => gaussianLogSourceMasterData δ θ.val β A u₀
    hδ hδ1.le θ.property hβ hd ρ M hM hρ n hn hA hAC hu₀ hlow hrow.le hop.le
  let K := (2+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ))^2
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤ 0+K*(n : ℝ)^(2/3 : ℝ) := by
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (gaussianLogAdaptive_actual_size_bound δ A β (n : ℝ) u₀ hδ hδ1.le hA hβ hn' hu₀ hd μ).2
    simpa only [data,gaussianLogSourceMasterData,K,zero_add] using hz
  obtain ⟨C,hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2/3 : ℝ) (by norm_num) hsize
  exact ⟨C,fun T hT n hn => hC ⟨T,hT⟩ n hn⟩

theorem logPhysicalSource_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ,∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨C,hC⟩ := gaussianLogSource_finiteIR_uniform_exponential β hβ hd ρ M hM hρ
  refine ⟨C,?_⟩
  intro n hn
  let T := fun j : ℕ => ((j+1 : ℕ) : ℝ)
  have hT : Tendsto T atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hT1 (j : ℕ) : 1 ≤ T j := by dsimp [T];exact_mod_cast (Nat.le_add_left 1 j)
  exact exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ))
    (fun j => gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β (T j) n)
    (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n)
    (fun j => (hC (T j) (hT1 j) n hn).1) C (fun j => (hC (T j) (hT1 j) n hn).2)
    (ae_tendsto_gaussianLogSourceApproxExponent T hT hd ρ M hM hρ hpair β n)

end DGRHS.Gaussian

#check DGRHS.Gaussian.measurable_gaussianLogSourceApproxExponent
#print axioms DGRHS.Gaussian.measurable_gaussianLogSourceApproxExponent
#check DGRHS.Gaussian.gaussianLogSource_finiteIR_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogSource_finiteIR_uniform_exponential
#check DGRHS.Gaussian.logPhysicalSource_uniform_exponential
#print axioms DGRHS.Gaussian.logPhysicalSource_uniform_exponential
