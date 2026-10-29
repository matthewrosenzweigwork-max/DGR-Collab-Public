import DGRHS.Commutator.SourceRieszPhysicalBrownianAssembly

/-! Predictable phase argument on the supplied filtration and the actual bounded
sine/cosine coefficient transforms. Every resulting finite Brownian integral
has mean zero. The initial statistic is measurable at time zero; independence
from the completed integral is never an assumption. No Ito formula is proved
by this unit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
variable (B : α→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B) (T : ℝ≥0)

include hB in
lemma sourceRieszBrownianFamilyProcess_mean_zero
    (g : α→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    Integrable (sourceRieszBrownianFamilyProcess P F B T g t) P ∧
      (∫ ω,sourceRieszBrownianFamilyProcess P F B T g t ω ∂P)=0 := by
  have hm := (sourceRieszBrownianFamilyProcess_martingale P F B hB T g).1
  refine ⟨hm.integrable t,?_⟩
  have he := hm.setIntegral_eq (show (0:ℝ≥0)≤t from bot_le) (s:=univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ,sourceRieszBrownianFamilyProcess_zero,integral_zero] using he.symm

include hB in
theorem exists_sourceRieszBrownianFamily_predictable_phase
    (g : α→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A) :
    ∃ R : ℝ≥0→Ω→ℝ,IsStronglyPredictable F R ∧
      (∀ ω,R 0 ω=A ω) ∧
      (∀ᵐ ω ∂P,∀ t,R t ω=A ω+sourceRieszBrownianFamilyProcess P F B T g t ω) ∧
      ∀ᵐ ω ∂P,Continuous (fun t=>R t ω) := by
  let Y := fun t ω=>A ω+sourceRieszBrownianFamilyProcess P F B T g t ω
  have hm := sourceRieszBrownianFamilyProcess_martingale P F B hB T g
  have hYa : StronglyAdapted F Y := fun t=>(hA.mono (F.mono bot_le)).add (hm.1.stronglyAdapted t)
  have hYc : ∀ᵐ ω ∂P,Continuous (fun t=>Y t ω) := by
    filter_upwards [hm.2.2] with ω hω
    exact continuous_const.add hω
  let R := sourceRieszPredictableVersion F Y hYa
  have he := sourceRieszPredictableVersion_ae_eq P F Y hYa hYc
  refine ⟨R,sourceRieszPredictableVersion_predictable F Y hYa,?_,he,?_⟩
  · intro ω
    change sourceRieszPredictableVersion F Y hYa 0 ω=A ω
    have h0 : (⊥:ℝ≥0)=0 := le_antisymm bot_le zero_le
    rw [←h0,sourceRieszPredictableVersion_bot,h0]
    simp only [Y,sourceRieszBrownianFamilyProcess_zero,add_zero]
  · filter_upwards [hYc,he] with ω hω heω
    exact hω.congr (fun t=>(heω t).symm)

lemma sourceRieszPredictable_sin_mul_bound
    (R U : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ t ω,‖U t ω‖≤K) :
    IsStronglyPredictable F (fun t ω=>Real.sin (R t ω)*U t ω) ∧
      ∀ t ω,‖Real.sin (R t ω)*U t ω‖≤K := by
  refine ⟨(Real.continuous_sin.comp_stronglyMeasurable hR).mul hU,?_⟩
  intro t ω
  rw [norm_mul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb t ω)

lemma sourceRieszPredictable_cos_mul_bound
    (R U : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ t ω,‖U t ω‖≤K) :
    IsStronglyPredictable F (fun t ω=>Real.cos (R t ω)*U t ω) ∧
      ∀ t ω,‖Real.cos (R t ω)*U t ω‖≤K := by
  refine ⟨(Real.continuous_cos.comp_stronglyMeasurable hR).mul hU,?_⟩
  intro t ω
  rw [norm_mul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb t ω)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess_mean_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess_mean_zero
#check @DGRHS.Commutator.exists_sourceRieszBrownianFamily_predictable_phase
#print axioms DGRHS.Commutator.exists_sourceRieszBrownianFamily_predictable_phase
#check @DGRHS.Commutator.sourceRieszPredictable_sin_mul_bound
#print axioms DGRHS.Commutator.sourceRieszPredictable_sin_mul_bound
#check @DGRHS.Commutator.sourceRieszPredictable_cos_mul_bound
#print axioms DGRHS.Commutator.sourceRieszPredictable_cos_mul_bound
