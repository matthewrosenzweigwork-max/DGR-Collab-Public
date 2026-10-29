import DGRHS.Commutator.SourceRieszLocalDecomposition
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! Source-normalized finite-particle algebra of the SAME local cutoff.
AE pair identities transfer only through distinct independent labels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration

lemma sourceRieszLocal_normalized_pair_linear {X : Type*} (N : ℕ) (U V : X×X→ℝ) (c d : ℝ) (ω : Fin N→X) :
    (1/(N:ℝ))*(∑ i : Fin N,∑ j : Fin N,if i=j then 0 else c*U (ω i,ω j)+d*V (ω i,ω j))=
      -2*c*iidNegativeStatistic N U ω-2*d*iidNegativeStatistic N V ω := by
  classical
  have hs : (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else c*U (ω i,ω j)+d*V (ω i,ω j))=
      c*iidCoupledSum N U ω+d*iidCoupledSum N V ω := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    simp only [ite_not]
    simp_rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i=j <;> simp [h]
  rw [hs]
  unfold iidNegativeStatistic
  ring

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszLocalShortAbsorption_statistic (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N) (ω : Fin N→E) :
    -2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*iidNegativeStatistic N
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v)) ω+
      γ*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s (2*η))) ω ≤
        (7/4:ℝ)*γ*(N:ℝ)*sourceRieszLocalShortPotential (ι:=ι) s η M := by
  have h := sourceRieszLocalShortAbsorption_sum s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ N hN ω
  have he := sourceRieszLocal_normalized_pair_linear N
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v))
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s (2*η)))
    (σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ) (-γ/2) ω
  change (1/(N:ℝ))*(∑ i : Fin N,∑ j : Fin N,if i=j then 0 else
    (σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ)*
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) (ω i,ω j)+
    (-γ/2)*hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s (2*η)) (ω i,ω j))=_ at he
  have he' : (1/(N:ℝ))*(∑ i : Fin N,∑ j : Fin N,if i=j then 0 else
    σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) (ω i,ω j)-
    γ/2*hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s (2*η)) (ω i,ω j))=
    -2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*iidNegativeStatistic N
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v)) ω+
      γ*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s (2*η))) ω := by
    convert he using 1 <;> simp only [sub_eq_add_neg,neg_div,neg_mul] <;> ring
  rw [←he']
  exact h

lemma ae_sourceRieszLocalCenteredCutoff_linear (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (γ σ : ℝ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    sourceRieszLocalCenteredCutoff μ s η n γ σ K v=ᵐ[μ.prod μ]
      (fun p=>-4*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
        hoeffdingCentered μ (sourceRieszLongTransportKernel n s η v) p+
        2*γ*hoeffdingCentered μ (gaussianRieszTruncatedPair s (2*η)) p) := by
  have hL := integrable_sourceRieszLocalLongKernel μ s η n hs hη hv
  have hG := (memLp_gaussianRieszTruncatedPair s (2*η) hs (by positivity) μ).integrable (by norm_num)
  have h := sourceRieszLocal_centered_add μ
    (fun p=>-4*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*sourceRieszLongTransportKernel n s η v p)
    (fun p=>2*γ*gaussianRieszTruncatedPair s (2*η) p) (hL.const_mul _) (hG.const_mul _)
  filter_upwards [h] with p hp
  change hoeffdingCentered μ (fun p=>-4*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
    sourceRieszLongTransportKernel n s η v p+2*γ*gaussianRieszTruncatedPair s (2*η) p) p=_ at hp ⊢
  rw [hp]
  simp only [Pi.add_apply,sourceRieszLocal_centered_const_mul]

lemma ae_sourceRieszLocalCutoff_statistic (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (γ σ : ℝ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N=>μ),
      (1/2:ℝ)*iidNegativeStatistic N (sourceRieszLocalCenteredCutoff μ s η n γ σ K v) ω=
        -2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
          iidNegativeStatistic N (hoeffdingCentered μ (sourceRieszLongTransportKernel n s η v)) ω+
          γ*iidNegativeStatistic N (hoeffdingCentered μ (gaussianRieszTruncatedPair s (2*η))) ω := by
  have h := ae_physical_iidNegativeStatistic_congr μ N _ _ (ae_sourceRieszLocalCenteredCutoff_linear μ s η n γ σ hs hη hv)
  filter_upwards [h] with ω hω
  rw [hω]
  change (1/2:ℝ)*iidNegativeStatistic N
    ((-4*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ) • hoeffdingCentered μ (sourceRieszLongTransportKernel n s η v)+
      (2*γ) • hoeffdingCentered μ (gaussianRieszTruncatedPair s (2*η))) ω=_
  rw [physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_const_smul,physical_iidNegativeStatistic_const_smul]
  ring

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocal_normalized_pair_linear
#print axioms DGRHS.Commutator.sourceRieszLocal_normalized_pair_linear

#check DGRHS.Commutator.sourceRieszLocalShortAbsorption_statistic
#print axioms DGRHS.Commutator.sourceRieszLocalShortAbsorption_statistic

#check DGRHS.Commutator.ae_sourceRieszLocalCenteredCutoff_linear
#print axioms DGRHS.Commutator.ae_sourceRieszLocalCenteredCutoff_linear

#check DGRHS.Commutator.ae_sourceRieszLocalCutoff_statistic
#print axioms DGRHS.Commutator.ae_sourceRieszLocalCutoff_statistic
