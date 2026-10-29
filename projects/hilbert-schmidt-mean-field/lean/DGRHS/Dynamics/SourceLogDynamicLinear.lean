/- Source dynamicEntropyTransfers(iii), actual bounded measurable tests.
The Gibbs Holder step uses the actual doubled-temperature partition bound;
Hoeffding controls the centered raw iid fluctuation. Common constants depend
on interval WIDTH and scalar controls, not the location of the test interval. -/
import DGRHS.Dynamics.BoundedRawProductLinearMGF
import DGRHS.Entropy.AbsoluteExponentialTransfer
import DGRHS.Entropy.GibbsHolderBootstrap
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_dynamic_linear_absolute_bound
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (J H L C₂ : ℝ) (hL : 0≤L) :
    ∃ D : ℝ,0≤D ∧ ∀ (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ),0≤M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
      -J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun x y=>logPhysicalPair (x,y)) →
      ∀ (N : ℕ),1≤N →
      (sourceLogSingularPartition (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) ρ N).toReal≤C₂ →
      ∀ (q : EuclideanSpace ℝ ι→ℝ),Measurable q → ∀ a b : ℝ,
      (∀ x,q x∈Set.Icc a b) → ‖b-a‖≤L →
      ∀ (ν : Measure (Fin N→EuclideanSpace ℝ ι)),∀ [IsProbabilityMeasure ν],
      klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ →
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤H →
      let μ := gaussianRieszDensityMeasure ρ
      let S := fun x : Fin N→EuclideanSpace ℝ ι=>(Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ)
      Integrable S ν ∧ (∫ x,|S x| ∂ν)≤D := by
  let C := Real.exp ((β:ℝ)*J)*Real.sqrt (Real.exp (L^2/2))*Real.sqrt C₂
  let D := max (H+Real.log (2*C)) 0
  refine ⟨D,le_max_right _ _,?_⟩
  intro ρ M hM hμ hρ hpair hI N hN hC₂ q hq a b hqbound hwidth ν hν hKL hH
  let μ := gaussianRieszDensityMeasure ρ
  let S := fun x : Fin N→EuclideanSpace ℝ ι=>(Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ)
  have hS : StronglyMeasurable S := by
    apply Measurable.stronglyMeasurable
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (hq.comp (measurable_pi_apply i)).sub_const _
  have hmom (σ : ℝ) (hσ : |σ|=1) :
      Integrable (fun x=>Real.exp (σ*S x)) (sourceLogSingularGibbs β ρ N) ∧
      (∫ x,Real.exp (σ*S x) ∂sourceLogSingularGibbs β ρ N)≤C := by
    obtain ⟨hi,hb⟩ := boundedRawProductLinearMGF (μ:=μ) q hq a b hqbound (2*σ) N
    have hcoef : ((((‖b-a‖₊/2)^2:ℝ≥0):ℝ))=(‖b-a‖/2)^2 := by simp
    have hsq : σ^2=1 := by nlinarith [sq_abs σ]
    have hw : ‖b-a‖^2≤L^2 := by nlinarith [sq_nonneg (L-‖b-a‖), norm_nonneg (b-a)]
    have hB : (∫ x,Real.exp ((2*σ)*S x) ∂Measure.pi (fun _ : Fin N=>μ))≤Real.exp (L^2/2) := by
      apply hb.trans
      apply Real.exp_le_exp.mpr
      rw [hcoef]
      nlinarith
    have hi' : Integrable (fun x=>Real.exp (-(0:ℝ)*(N:ℝ)*
        sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ (fun x y=>logPhysicalPair (x,y)))
          (DGRHS.interactionEnergy μ (fun x y=>logPhysicalPair (x,y))) N x+(2*σ)*S x))
        (Measure.pi (fun _ : Fin N=>μ)) := by simpa only [neg_zero,zero_mul,zero_add] using hi
    obtain ⟨hproper,hbound⟩ := sourceLog_gibbs_holder_bound β 0 β.coe_nonneg hd ρ M hM hρ hpair N hN
      S (2*σ) (Real.exp (L^2/2)) C₂ hi' (by simpa only [NNReal.coe_zero,neg_zero,zero_mul,zero_add] using hB)
      (by simpa only [NNReal.coe_zero,sub_zero] using hC₂)
    have hpref : Real.exp (-(β:ℝ)*DGRHS.interactionEnergy μ (fun x y=>logPhysicalPair (x,y)))≤Real.exp ((β:ℝ)*J) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hI β.coe_nonneg
      change (β:ℝ)*(-J)≤(β:ℝ)*DGRHS.interactionEnergy μ (fun x y=>logPhysicalPair (x,y)) at hh
      nlinarith
    refine ⟨by convert hproper using 1 <;> congr 1 <;> funext x <;> congr 1 <;> ring,?_⟩
    have he : (2*σ)/2=σ := by ring
    rw [he] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpref (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  letI := sourceLogSingularGibbs_probability β hd ρ M hM hρ hpair N
  have hp := hmom 1 (by norm_num)
  have hm := hmom (-1) (by norm_num)
  obtain ⟨hi,hb⟩ := entropy_absolute_expectation_scaled_of_two_exponential_bounds
    (sourceLogSingularGibbs β ρ N) ν S hS 1 (by norm_num)
    (by simpa only [one_mul] using hp.1) (by simpa only [neg_one_mul,one_mul] using hm.1) hKL C
    (by simpa only [one_mul] using hp.2) (by simpa only [neg_one_mul,one_mul] using hm.2)
  refine ⟨hi,?_⟩
  simp only [inv_one,one_mul] at hb
  exact (hb.trans (add_le_add hH le_rfl)).trans (le_max_left _ _)
end DGRHS.Dynamics
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_linear_absolute_bound
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_linear_absolute_bound
