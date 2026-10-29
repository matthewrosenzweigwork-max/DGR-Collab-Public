/- Actual empirical probability integrals and the source dynamic(iii) rate.
Both q integrals are proper; the constant is selected before N and the test. -/
import DGRHS.Dynamics.SourceLogDynamicLinear
import DGRHS.Commutator.SourceLogTransportEmpirical
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator

lemma bounded_test_empirical_fluctuation_identity
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (q : X→ℝ) (hq : Measurable q)
    (a b : ℝ) (hqbound : ∀ x,q x∈Set.Icc a b)
    (N : ℕ) (hN : 1≤N) (x : Fin N→X) :
    Integrable q μ ∧ Integrable q (transportEmpiricalLaw N x) ∧
    ((∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂μ)) =
      (Real.sqrt N)⁻¹*((Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ)) := by
  have hb : ∀ z,|q z|≤max |a| |b| := by
    intro z
    rw [abs_le]
    constructor
    · have := (hqbound z).1
      have := le_max_left |a| |b|
      have := neg_abs_le a
      linarith
    · exact ((hqbound z).2.trans (le_abs_self b)).trans (le_max_right _ _)
  have hiμ : Integrable q μ := (integrable_const (max |a| |b|)).mono' hq.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hb z)
  have hix : Integrable q (transportEmpiricalLaw N x) :=
    (integrable_const (max |a| |b|)).mono' hq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hb z)
  refine ⟨hiμ,hix,?_⟩
  rw [integral_transportEmpiricalLaw N x q hq (max |a| |b|) hb,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (N:ℝ)≠0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
  have hs : Real.sqrt (N:ℝ)≠0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN)
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg N)
  have hinv : (N:ℝ)⁻¹=(Real.sqrt N)⁻¹*(Real.sqrt N)⁻¹ := by
    calc (N:ℝ)⁻¹=((Real.sqrt N)^2)⁻¹ := congrArg Inv.inv hsquare.symm
      _ = (Real.sqrt N)⁻¹*(Real.sqrt N)⁻¹ := by rw [pow_two,mul_inv_rev]
  calc (N:ℝ)⁻¹*(∑ i : Fin N,q (x i))-(∫ y,q y ∂μ) =
      (N:ℝ)⁻¹*((∑ i : Fin N,q (x i))-(N:ℝ)*(∫ y,q y ∂μ)) := by
        field_simp
        <;> ring
    _ = (Real.sqrt N)⁻¹*((Real.sqrt N)⁻¹*((∑ i : Fin N,q (x i))-(N:ℝ)*(∫ y,q y ∂μ))) := by
      rw [hinv]
      ring

variable {ι : Type*} [Fintype ι]
theorem exists_sourceLog_dynamic_empirical_absolute_bound
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
      let E := fun x : Fin N→EuclideanSpace ℝ ι=>(∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂μ)
      Integrable q μ ∧ (∀ x,Integrable q (transportEmpiricalLaw N x)) ∧
      Integrable E ν ∧ (∫ x,|E x| ∂ν)≤D/Real.sqrt N := by
  obtain ⟨D,hD,hbound⟩ := exists_sourceLog_dynamic_linear_absolute_bound β hβ hd J H L C₂ hL
  refine ⟨D,hD,?_⟩
  intro ρ M hM hμ hρ hpair hI N hN hC₂ q hq a b hqbound hwidth ν hν hKL hH
  obtain ⟨hi,hb⟩ := hbound ρ M hM hρ hpair hI N hN hC₂ q hq a b hqbound hwidth ν hKL hH
  let μ := gaussianRieszDensityMeasure ρ
  let S := fun x : Fin N→EuclideanSpace ℝ ι=>(Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ)
  have hh := bounded_test_empirical_fluctuation_identity μ q hq a b hqbound N hN
  have he : (fun x : Fin N→EuclideanSpace ℝ ι=>(∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂μ)) =
      fun x=>(Real.sqrt N)⁻¹*S x := by funext x; exact (hh x).2.2
  refine ⟨(hh (fun _=>0)).1,fun x=>(hh x).2.1,?_,?_⟩
  · rw [he]
    exact hi.const_mul _
  · rw [he]
    simp_rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (N:ℝ)))]
    rw [integral_const_mul]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg (N:ℝ)))
end DGRHS.Dynamics
#check @DGRHS.Dynamics.bounded_test_empirical_fluctuation_identity
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_empirical_absolute_bound
#print axioms DGRHS.Dynamics.bounded_test_empirical_fluctuation_identity
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_empirical_absolute_bound
