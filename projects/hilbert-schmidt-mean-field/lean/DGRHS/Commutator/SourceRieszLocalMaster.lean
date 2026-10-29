import DGRHS.Commutator.SourceRieszLocalParameters
import DGRHS.Gaussian.GaussianRieszCutoffMoment

/-! The actual local Riesz master family. All physical event, cap, row,
operator and size fields are constructed; no desired exponential estimate
or favorable cutoff data are hypotheses. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_sourceRieszLocalExponent (ρ : E→ℝ) (s M : ℝ) (n : ℕ)
    (γ σ : ℝ) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℕ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (sourceRieszLocalExponent ρ s M n γ σ K v N) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  have hT := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ (measurable_sourceRieszTransportKernel s n hv).stronglyMeasurable).measurable
  have hE := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_gaussianRieszPhysicalPair s)).measurable
  have hF : Measurable (sourceRieszLocalPhysicalPotential ρ s) :=
    (stronglyMeasurable_gaussianRieszPhysicalPair s).integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N→E=>∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i)) :=
    Finset.measurable_sum _ (fun i _=>hF.comp (measurable_pi_apply i))
  have hm : Measurable (fun ω : Fin N→E=>(3/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι-
      2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*iidNegativeStatistic N (hoeffdingCentered μ (sourceRieszTransportKernel n s v)) ω+
      (γ*iidNegativeStatistic N (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) ω+
        γ*((N:ℝ)⁻¹*∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i))-γ*sourceRieszLocalPhysicalEnergy ρ s)) := (measurable_const.sub (hT.const_mul (2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ))).add
    (((hE.const_mul γ).add ((hSum.const_mul (N:ℝ)⁻¹).const_mul γ)).sub measurable_const)
  convert hm using 1
  funext ω
  unfold sourceRieszLocalExponent DGRHS.CLT.sourceParticleExponent
  rw [←sourceRieszLocal_energy_normalization γ]

/-- Actual physical M1--M3 and finite size with the genuine local threshold. -/
def sourceRieszLocalMasterData (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0<γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (hγb : γ≤sourceRieszLocalBeta (ι:=ι) s M) :
    MasterCutoffData (gaussianRieszDensityMeasure ρ) N
      (sourceRieszLocalExponent ρ s M n γ σ K v N) 1 := by
  let μ := gaussianRieszDensityMeasure ρ
  let C := sourceRieszLocalAbsorptionConstant (ι:=ι) s M
  let η := sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N
  let q := fun u=>sourceRieszLocalCenteredCutoff μ s (η u) n γ σ K v
  have hC : 0<C := sourceRieszLocalAbsorptionConstant_pos s M hs (by linarith) hM
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN)
  have hη (u : ℝ) (hu : 1≤u) : 0<η u :=
    (gaussianRieszAdaptiveScale_pos_le 1 (4*C*γ) N u (Fintype.card ι) s (by norm_num) (by positivity) hn (by linarith)).1
  have hp := (sourceRieszLocalBeta_properties s M hs (by linarith) hM).2 γ hγ hγb
  have hγ1 := hp.1
  have hsmall := hp.2.1
  have hNorm := hp.2.2.1
  have hControl : 0≤sourceRieszFullSquareRowControl s M ι :=
    (integral_nonneg (fun y=>sq_nonneg (gaussianRieszPhysicalPair s ((0:E),y)))).trans
      (sourceRieszPhysicalPair_square_row s hs hd ρ M hM hρ (0:E)).2
  have hSquare := (sourceRieszLocal_small_square_bound s M γ hγ.le hγ1 hControl).trans hNorm
  refine { kernel := q
           cap := sourceRieszLocalAdaptiveCap (ι:=ι) s C γ N
           measurable := fun u hu=>(stronglyMeasurable_sourceRieszLocalCenteredCutoff μ s (η u) n γ σ hs (hη u hu) hv).measurable
           memLp := fun u hu=>memLp_sourceRieszLocalCenteredCutoff μ s (η u) n hs (hη u hu) γ σ hγ.le hσ hv ∞
           symmetric := fun u _=>sourceRieszLocalCenteredCutoff_symmetric μ s (η u) n γ σ K v
           canonical := fun u hu=>sourceRieszLocalCenteredCutoff_canonical μ s (η u) n hs (hη u hu) γ σ hγ.le hσ hv
           cap_pos := ?_
           compare := fun u hu=>ae_sourceRieszLocal_event_reduction s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hsmall u hu
           capped := ?_
           row := ?_
           joint := ?_
           operator := ?_
           size_finite := (sourceRieszLocalAdaptiveSize μ s C γ n hs hd hC hγ hγ1 σ hσ hv N hn).1 }
  · intro u hu
    have hc := gaussianRieszSourceCoefficient_pos s hs
    have he := hη u hu
    change 0<(N:ℝ)/2*(12*γ*(gaussianRieszSourceCoefficient s/s*(η u)^(-s)))
    positivity
  · intro u hu
    let B := 12*γ*(gaussianRieszSourceCoefficient s/s*(η u)^(-s))
    have hc := gaussianRieszSourceCoefficient_pos s hs
    have he := hη u hu
    have hB : 0≤B := by dsimp[B];positivity
    have hb := ae_physical_iidNegativeStatistic_bound μ N hN (q u) (B/2) (by positivity) (Filter.Eventually.of_forall (fun p=>by
      have hp := sourceRieszLocalCenteredCutoff_cap μ s (η u) n hs (hη u hu) γ σ hγ.le hσ hv p
      change |q u p|≤B at hp
      have hneg := (neg_le_abs (q u p)).trans hp
      convert hneg using 1 <;> ring))
    filter_upwards [hb] with ω hω
    calc
      _ ≤ (N:ℝ)*(B/2) := hω
      _ = _ := by unfold sourceRieszLocalAdaptiveCap;dsimp[B,η];ring
  · intro u hu
    filter_upwards [(sourceRieszLocalCenteredCutoff_square_controls s (η u) n hs (hη u hu) hd γ σ hγ.le hσ hv ρ M hM hρ).1] with x hx
    exact hx.trans hSquare
  · intro u hu
    exact (sourceRieszLocalCenteredCutoff_square_controls s (η u) n hs (hη u hu) hd γ σ hγ.le hσ hv ρ M hM hρ).2.trans hSquare
  · intro u hu
    have hb := norm_sourceRieszLocalCenteredCutoff_operator s (η u) n hs (hη u hu) hd γ σ hγ.le hσ hv ρ M hM hρ
    have hc := mul_le_mul_of_nonneg_left (sourceRieszLocalNormConstant_bounds (ι:=ι) s M).2.2 hγ.le
    have hh : 12*γ*Real.sqrt (sourceRieszFullSquareRowControl s M ι)≤1/glzUniversalTailConstant := by nlinarith [hc,hNorm]
    exact hb.trans hh

lemma sourceRieszLocalMasterData_growth (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0<γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (hγb : γ≤sourceRieszLocalBeta (ι:=ι) s M) :
    2*glzUniversalTailConstant^2*masterCutoffSize (gaussianRieszDensityMeasure ρ)
      (sourceRieszLocalMasterData s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hγb).kernel
      (sourceRieszLocalMasterData s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hγb).cap 1≤(N:ℝ) := by
  obtain ⟨hγ1,_,_,hg⟩ := (sourceRieszLocalBeta_properties s M hs (by linarith) hM).2 γ hγ hγb
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN)
  have hC := sourceRieszLocalAbsorptionConstant_pos s M hs (by linarith) hM
  have hb := (sourceRieszLocalAdaptiveSize (gaussianRieszDensityMeasure ρ) s (sourceRieszLocalAbsorptionConstant (ι:=ι) s M)
    γ n hs hd hC hγ hγ1 σ hσ hv N hn).2
  change masterCutoffSize _ _ _ 1≤sourceRieszLocalSizeConstant (ι:=ι) s M*γ*(N:ℝ) at hb
  change 2*glzUniversalTailConstant^2*masterCutoffSize (gaussianRieszDensityMeasure ρ)
    (fun u=>sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s
      (sourceRieszLocalAdaptiveScale (ι:=ι) s (sourceRieszLocalAbsorptionConstant (ι:=ι) s M) γ N u) n γ σ K v)
    (sourceRieszLocalAdaptiveCap (ι:=ι) s (sourceRieszLocalAbsorptionConstant (ι:=ι) s M) γ N) 1≤(N:ℝ)
  calc
    _ ≤ 2*glzUniversalTailConstant^2*(sourceRieszLocalSizeConstant (ι:=ι) s M*γ*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2*glzUniversalTailConstant^2*sourceRieszLocalSizeConstant (ι:=ι) s M*γ)*(N:ℝ) := by ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hg hn.le

/-- Uniform proper local exponential control, derived from the actual singular
Riesz kernel and transport contraction for every positive particle number. -/
theorem sourceRieszLocal_exponential_moment (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0<γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (hγb : γ≤sourceRieszLocalBeta (ι:=ι) s M) :
    Integrable (fun ω=>Real.exp (sourceRieszLocalExponent ρ s M n γ σ K v N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
    (∫ ω,Real.exp (sourceRieszLocalExponent ρ s M n γ σ K v N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Real.exp 1+glzUniversalTailConstant := by
  exact master_exponential_moment_large (gaussianRieszDensityMeasure ρ) N hN _
    (measurable_sourceRieszLocalExponent ρ s M n γ σ hv N).aemeasurable 1 le_rfl
    (sourceRieszLocalMasterData s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hγb)
    (sourceRieszLocalMasterData_growth s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hγb)

end DGRHS.Commutator

#check DGRHS.Commutator.measurable_sourceRieszLocalExponent
#print axioms DGRHS.Commutator.measurable_sourceRieszLocalExponent
#check DGRHS.Commutator.sourceRieszLocalMasterData
#print axioms DGRHS.Commutator.sourceRieszLocalMasterData
#check DGRHS.Commutator.sourceRieszLocalMasterData_growth
#print axioms DGRHS.Commutator.sourceRieszLocalMasterData_growth
#check DGRHS.Commutator.sourceRieszLocal_exponential_moment
#print axioms DGRHS.Commutator.sourceRieszLocal_exponential_moment
