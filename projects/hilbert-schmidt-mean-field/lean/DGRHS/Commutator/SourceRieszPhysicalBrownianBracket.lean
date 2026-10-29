import DGRHS.Commutator.SourceRieszPhysicalBrownianCoefficients

/-! Literal energy of the constructed bounded predictable coefficient family.
The physical normalization and finite Euclidean coordinate sum yield the actual
empirical stopped-gradient square. No desired bracket identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι α : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszPredictableBounded_square_section_integrable
    (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) (ω : Ω) :
    Integrable (fun r=>(U r ω)^2) (sourceRieszBrownianTimeOn T) := by
  have hm : StronglyMeasurable (fun r=>U r ω) :=
    (hU.mono (sourceRiesz_predictable_le_product F)).comp_measurable
      (measurable_id.prodMk measurable_const)
  exact (MemLp.of_bound (p:=2) hm.aestronglyMeasurable K
    (ae_of_all _ (fun r=>hb r ω))).integrable_sq

lemma sourceRieszBrownianFamilyBracket_bounded_coefficients [Fintype α]
    (U : α→ℝ≥0→Ω→ℝ) (hU : ∀ b,IsStronglyPredictable F (U b))
    (K : ℝ) (hb : ∀ b r ω,‖U b r ω‖≤K) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianFamilyBracket P F T
      (fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hb b)) t ω=
      ∫ r in Ioc 0 t,∑ b,(U b r ω)^2 ∂sourceRieszBrownianTimeOn T := by
  let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hb b)
  filter_upwards [sourceRieszBrownianFamilyBracket_eq_energy P F T g,
    ae_all_iff.2 (fun b=>sourceRieszPredictableBoundedL2_energy P F T (U b) (hU b) K (hb b))]
      with ω hω he
  intro t
  calc
    sourceRieszBrownianFamilyBracket P F T g t ω =
        ∑ b,sourceRieszBrownianEnergy P F T (g b) t ω := hω t
    _ = ∑ b,∫ r in Ioc 0 t,(U b r ω)^2 ∂sourceRieszBrownianTimeOn T :=
      Finset.sum_congr rfl (fun b _=>he b t)
    _ = ∫ r in Ioc 0 t,∑ b,(U b r ω)^2 ∂sourceRieszBrownianTimeOn T :=
      (integral_finsetSum _ (fun b _=>(sourceRieszPredictableBounded_square_section_integrable
        F T (U b) (hU b) K (hb b) ω).integrableOn)).symm

variable [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_physical_coordinate_square (β : ℝ) (hβ : 0<β)
    (N : ℕ) (v : Fin N→E) :
    (∑ b : Fin N×ι,(Real.sqrt (2/β)/Real.sqrt N*(v b.1) b.2)^2)=
      (2/β)*(N:ℝ)⁻¹*(∑ i,‖v i‖^2) := by
  have hc : (Real.sqrt (2/β)/Real.sqrt N)^2=(2/β)*(N:ℝ)⁻¹ := by
    rw [div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (Nat.cast_nonneg N)]
    exact div_eq_mul_inv _ _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_pow,←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq]
  rw [hc]

lemma sourceRieszBrownianFamilyBracket_physical
    (β : ℝ) (hβ : 0<β) (N k : ℕ) (t : Fin k→ℝ≥0) (θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ) (X : ℝ≥0→Ω→Fin N→E)
    (U : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hU : ∀ b,IsStronglyPredictable F (U b))
    (K : ℝ) (hb : ∀ b r ω,‖U b r ω‖≤K)
    (he : ∀ᵐ ω ∂P,∀ r b,U b r ω=
      (Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) :
    ∀ᵐ ω ∂P,∀ s,sourceRieszBrownianFamilyBracket P F T
      (fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hb b)) s ω=
      (2/β)*(∫ r in Ioc 0 s,
        ∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) z‖^2
          ∂sourceRieszLocalEmpiricalLaw N (X r ω) ∂sourceRieszBrownianTimeOn T) := by
  filter_upwards [sourceRieszBrownianFamilyBracket_bounded_coefficients P F T U hU K hb,he]
    with ω hbr hω
  intro s
  rw [hbr s,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  simp_rw [hω r]
  rw [sourceRiesz_physical_coordinate_square β hβ N
    (fun i=>∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω i)),
    integral_sourceRieszLocalEmpiricalLaw]
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPredictableBounded_square_section_integrable
#print axioms DGRHS.Commutator.sourceRieszPredictableBounded_square_section_integrable
#check @DGRHS.Commutator.sourceRieszBrownianFamilyBracket_bounded_coefficients
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyBracket_bounded_coefficients
#check @DGRHS.Commutator.sourceRiesz_physical_coordinate_square
#print axioms DGRHS.Commutator.sourceRiesz_physical_coordinate_square
#check @DGRHS.Commutator.sourceRieszBrownianFamilyBracket_physical
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyBracket_physical
