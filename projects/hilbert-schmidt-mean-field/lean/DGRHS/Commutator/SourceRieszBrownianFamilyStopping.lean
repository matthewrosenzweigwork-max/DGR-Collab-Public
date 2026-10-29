import DGRHS.Commutator.SourceRieszPhysicalBrownianCoefficients
import DGRHS.Commutator.SourceRieszBrownianStoppedIdentification

/-! Exact deterministic stopping and finite-family identification for the
constructed integrals. Pointwise support of predictable versions is retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω α δ : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszPredictableBoundedL2_stopped_support
    (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) (a : ℝ≥0)
    (hz : ∀ r ω,a<r → U r ω=0) :
    ∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,a<p.1 →
      sourceRieszPredictableBoundedL2 P F T U hU K hb p=0 := by
  filter_upwards [(MemLp.of_bound (p:=2) hU.aestronglyMeasurable K
    (ae_of_all (sourceRieszBrownianPredictableMeasure P F T) (fun p=>hb p.1 p.2))).coeFn_toLp]
      with p hp
  intro ha
  exact hp.trans (hz p.1 p.2 ha)

theorem sourceRieszBrownianFamilyProcess_finite_stopped_sum
    [Fintype α] [Fintype δ]
    (B : α→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)
    (a : δ→ℝ≥0) (θ : δ→ℝ)
    (g : δ→α→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (hs : ∀ j b,∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,a j<p.1 → g j b p=0) :
    ∀ᵐ ω ∂P,∀ r,sourceRieszBrownianFamilyProcess P F B T (fun b=>∑ j,θ j • g j b) r ω=
      ∑ j,θ j*sourceRieszBrownianFamilyProcess P F B T (g j) (min r (a j)) ω := by
  filter_upwards [ae_all_iff.2 (fun b=>sourceRieszBrownianContinuousProcess_finite_stopped_sum
    P F T (B b) (hB.brownian b).toIsPreBrownianReal (hB.adapted b)
    (hB.increment_indep P F B b) (hB.brownian b).cont a θ (fun j=>g j b)
      (fun j=>hs j b))] with ω hω
  intro r
  dsimp only [sourceRieszBrownianFamilyProcess]
  simp_rw [hω _ r]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _=>(Finset.mul_sum _ _ _).symm)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPredictableBoundedL2_stopped_support
#print axioms DGRHS.Commutator.sourceRieszPredictableBoundedL2_stopped_support
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess_finite_stopped_sum
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess_finite_stopped_sum
