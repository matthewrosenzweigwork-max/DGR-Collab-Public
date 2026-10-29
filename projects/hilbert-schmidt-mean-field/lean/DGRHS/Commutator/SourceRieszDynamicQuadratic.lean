import DGRHS.Commutator.SourceRieszLocalEmpirical

/-! Actual source dynamicQuadraticExpansion in the positive-Riesz branch.
Proper pair integrals follow from the physical bounded-density sections and
original 2s<d; an arbitrary favorable pair-integrability premise is not used.
Root LOG primitive is an adaptation reference only. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRiesz_dynamic_quadratic_expansion (s : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let μ := gaussianRieszDensityMeasure ρ
    let e := sourceRieszLocalEmpiricalLaw N x
    let h := sourceRieszTransportKernel 1 s v
    Integrable h (e.prod e) ∧ Integrable h (e.prod μ) ∧
    Integrable h (μ.prod e) ∧ Integrable h (μ.prod μ) ∧
    (∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ)=
      2*((∫ p,h p ∂e.prod μ)-(∫ p,h p ∂μ.prod μ))+
        sourceRieszLocalTransportEnergy ρ s 1 v N x := by
  let μ := gaussianRieszDensityMeasure ρ
  let e := sourceRieszLocalEmpiricalLaw N x
  let h := sourceRieszTransportKernel 1 s v
  obtain ⟨h1,h2,h3,h4,ha⟩ := sourceRieszLocalTransportEnergy_offCollision s 1 hs hd hv ρ M hM hρ N hN x
  refine ⟨h1,h2,h3,h4,?_⟩
  have he : (∫ p,h p ∂μ.prod e)=(∫ p,h p ∂e.prod μ) := by
    rw [←integral_prod_swap]
    congr 1
    funext p
    exact sourceRieszTransportKernel_symmetric s 1 v p
  simp_rw [sourceRieszLocalTransport_restrict_offCollision] at ha ⊢
  rw [ha,he]
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_dynamic_quadratic_expansion
#print axioms DGRHS.Commutator.sourceRiesz_dynamic_quadratic_expansion
