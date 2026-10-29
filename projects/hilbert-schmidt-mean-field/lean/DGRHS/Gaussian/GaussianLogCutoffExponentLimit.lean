import DGRHS.Gaussian.GaussianLogCutoffAllScales
import DGRHS.Gaussian.GaussianLogCutoffIdentification
import DGRHS.Concentration.MasterLimit

/-! Supporting development. Actual SAME cutoff finite-particle exponent convergence
and proper Fatou passage, with common all-cutoff source moments as conclusions. -/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators Topology
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogCutoffSourceExponent (μ : Measure (EuclideanSpace ℝ ι))
    (β η : ℝ) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) : ℝ :=
  β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogTruncatedPair η)) ω +
    β/(n : ℝ)*(∑ i : Fin n,∫ y,gaussianLogTruncatedPair η (ω i,y) ∂μ) -
    β/2*(∫ p,gaussianLogTruncatedPair η p ∂μ.prod μ)

lemma ae_tendsto_gaussianLogCutoffApproxExponent (η : ℝ) (hη : 0 < η)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (hηT : ∀ j,η ≤ T j)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      Tendsto (fun j => gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η (T j) n ω)
        atTop (𝓝 (gaussianLogCutoffSourceExponent (gaussianRieszDensityMeasure ρ) β η n ω)) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  have ha := ae_tendsto_gaussianLogCenteredBand_to_cutoff η hη T hT hηT hd ρ M hM hρ hpair
  have hp : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),∀ i k : Fin n,i ≠ k →
      Tendsto (fun j => hoeffdingCentered μ (gaussianLogBandPair η (T j)) (ω i,ω k)) atTop
        (𝓝 (hoeffdingCentered μ (gaussianLogTruncatedPair η) (ω i,ω k))) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro k
    by_cases hik : i=k
    · exact Eventually.of_forall (fun _ h => False.elim (h hik))
    · filter_upwards [(measurePreserving_distinct_particle_pair n i k hik).quasiMeasurePreserving.ae ha] with ω hω
      exact fun _ => hω
  filter_upwards [hp] with ω hω
  have ht : Tendsto (fun j => iidCoupledSum n (hoeffdingCentered μ (gaussianLogBandPair η (T j))) ω) atTop
      (𝓝 (iidCoupledSum n (hoeffdingCentered μ (gaussianLogTruncatedPair η)) ω)) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    apply physical_tendsto_finset_sum
    intro i hi
    apply physical_tendsto_finset_sum
    intro k hk
    by_cases hik : i ≠ k
    · simp only [if_pos hik];exact hω i k hik
    · simp only [if_neg hik];exact tendsto_const_nhds
  have hneg := ((ht.neg).div_const (2*(n : ℝ))).const_mul β
  have hpot : Tendsto (fun j => ∑ i : Fin n,((∫ y,gaussianLogBandPair η (T j) (ω i,y) ∂μ)-gaussianLogCounterterm (T j)))
      atTop (𝓝 (∑ i : Fin n,∫ y,gaussianLogTruncatedPair η (ω i,y) ∂μ)) := by
    apply physical_tendsto_finset_sum
    intro i hi
    exact tendsto_gaussianLogCutoff_potential η hη T hT hηT hd ρ M hM hρ hpair (ω i)
  have hm := (tendsto_gaussianLogCutoff_pairMean η hη T hT hηT hd ρ M hM hρ hpair).const_mul (β/2)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have he (j : ℕ) : gaussianLogCutoffApproxExponent μ β η (T j) n ω =
      β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η (T j))) ω +
      β/(n : ℝ)*(∑ i : Fin n,((∫ y,gaussianLogBandPair η (T j) (ω i,y) ∂μ)-gaussianLogCounterterm (T j))) -
      β/2*((∫ p,gaussianLogBandPair η (T j) p ∂μ.prod μ)-gaussianLogCounterterm (T j)) := by
    simp_rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold gaussianLogCutoffApproxExponent
    field_simp [hn'] <;> ring
  change Tendsto (fun j => gaussianLogCutoffApproxExponent μ β η (T j) n ω) atTop
    (𝓝 (gaussianLogCutoffSourceExponent μ β η n ω))
  simp_rw [he]
  exact (hneg.add (hpot.const_mul (β/(n : ℝ)))).sub hm

theorem gaussianLogCutoffSource_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ,∀ η : ℝ,0 < η → η ≤ 1 → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (gaussianLogCutoffSourceExponent (gaussianRieszDensityMeasure ρ) β η n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (gaussianLogCutoffSourceExponent (gaussianRieszDensityMeasure ρ) β η n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨C,hC⟩ := gaussianLogCutoffSource_all_finiteIR_uniform_exponential β hβ hd ρ M hM hρ
  refine ⟨C,?_⟩
  intro η hη hη1 n hn
  let T : ℕ → ℝ := fun j => (j+1 : ℕ)
  have hT : Tendsto T atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hT1 (j : ℕ) : 1 ≤ T j := by dsimp only [T];exact_mod_cast (Nat.le_add_left 1 j)
  exact exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n => μ))
    (fun j => gaussianLogCutoffApproxExponent μ β η (T j) n) (gaussianLogCutoffSourceExponent μ β η n)
    (fun j => (hC η hη hη1 (T j) (hT1 j) n hn).1) C
    (fun j => (hC η hη hη1 (T j) (hT1 j) n hn).2)
    (ae_tendsto_gaussianLogCutoffApproxExponent η hη T hT (fun j => hη1.trans (hT1 j)) hd ρ M hM hρ hpair β n hn)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogCutoffSourceExponent
#print axioms DGRHS.Gaussian.gaussianLogCutoffSourceExponent
#check @DGRHS.Gaussian.ae_tendsto_gaussianLogCutoffApproxExponent
#print axioms DGRHS.Gaussian.ae_tendsto_gaussianLogCutoffApproxExponent
#check @DGRHS.Gaussian.gaussianLogCutoffSource_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogCutoffSource_uniform_exponential
