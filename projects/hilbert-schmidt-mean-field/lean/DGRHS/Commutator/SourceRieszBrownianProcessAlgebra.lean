import DGRHS.Commutator.SourceRieszBrownianContinuousMartingaleAE

/-! Simultaneous process identities for the unchanged measurable-limsup
representative. Fixed-time L2 linearity is upgraded on one common event by
countable dense times and continuous paths. Stopping here is at the deterministic
construction horizon T; no random stopping theorem is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_ae_continuous_indistinguishable (P : Measure Ω)
    (X Y : ℝ≥0→Ω→ℝ)
    (hX : ∀ᵐ ω ∂P,Continuous (fun t=>X t ω))
    (hY : ∀ᵐ ω ∂P,Continuous (fun t=>Y t ω))
    (he : ∀ t,X t=ᵐ[P] Y t) : ∀ᵐ ω ∂P,∀ t,X t ω=Y t ω := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  letI : Countable D := hDc.to_subtype
  have hd : DenseRange (fun t:D=>(t:ℝ≥0)) := by
    have hr : Set.range (fun t:D=>(t:ℝ≥0))=D := by ext t; simp
    rw [DenseRange,hr]
    exact hDd
  filter_upwards [hX,hY,ae_all_iff.2 (fun t:D=>he t)] with ω hx hy hω
  exact congrFun (DenseRange.equalizer hd hx hy (funext hω))

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

lemma sourceRieszBrownianProcessL2_add
    (g h : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind (g+h) t=
      sourceRieszBrownianProcessL2 P F T B hB hBa hind g t+
      sourceRieszBrownianProcessL2 P F T B hB hBa hind h t := by
  simp [sourceRieszBrownianProcessL2,map_add]

lemma sourceRieszBrownianProcessL2_smul
    (a : ℝ) (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind (a • g) t=
      a • sourceRieszBrownianProcessL2 P F T B hB hBa hind g t := by
  simp [sourceRieszBrownianProcessL2,map_smul]

lemma sourceRieszBrownianContinuousProcess_stopped_horizon
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) (ω : Ω) :
    sourceRieszBrownianContinuousProcess P F T B g t ω=
      sourceRieszBrownianContinuousProcess P F T B g (min t T) ω := by
  unfold sourceRieszBrownianContinuousProcess
  congr 1
  funext n
  exact congrFun (sourceRieszBrownianElementaryProcess_stopped F T B _ t) ω

variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))
include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_add
    (g h : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B (g+h) t ω=
      sourceRieszBrownianContinuousProcess P F T B g t ω+
      sourceRieszBrownianContinuousProcess P F T B h t ω := by
  apply sourceRiesz_ae_continuous_indistinguishable P
  · exact sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc _
  · filter_upwards [sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc g,
      sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc h] with ω hg hh
    exact hg.add hh
  · intro t
    have he := sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc (g+h) t
    rw [sourceRieszBrownianProcessL2_add P F T B hB hBa hind] at he
    filter_upwards [he,Lp.coeFn_add (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind h t),
      sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g t,
      sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc h t] with ω hh ha hg hk
    simpa only [Pi.add_apply,hg,hk] using hh.trans ha

include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_smul
    (a : ℝ) (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B (a • g) t ω=
      a*sourceRieszBrownianContinuousProcess P F T B g t ω := by
  apply sourceRiesz_ae_continuous_indistinguishable P
  · exact sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc _
  · filter_upwards [sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc g] with ω hg
    exact continuous_const.mul hg
  · intro t
    have he := sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc (a • g) t
    rw [sourceRieszBrownianProcessL2_smul P F T B hB hBa hind] at he
    filter_upwards [he,Lp.coeFn_smul a (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t),
      sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g t] with ω hh ha hg
    simpa only [Pi.smul_apply,smul_eq_mul,hg] using hh.trans ha

include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_zero_integrand :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B 0 t ω=0 := by
  have h := sourceRieszBrownianContinuousProcess_smul P F T B hB hBa hind hBc 0 0
  simpa only [zero_smul,zero_mul] using h

include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_finsetSum {ι : Type*} (S : Finset ι)
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B (∑ i∈S,g i) t ω=
      ∑ i∈S,sourceRieszBrownianContinuousProcess P F T B (g i) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using sourceRieszBrownianContinuousProcess_zero_integrand P F T B hB hBa hind hBc
  | insert i S hi ih =>
    filter_upwards [sourceRieszBrownianContinuousProcess_add P F T B hB hBa hind hBc (g i) (∑ j∈S,g j),ih]
      with ω ha hh
    intro t
    simpa only [Finset.sum_insert hi,hh t] using ha t

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_ae_continuous_indistinguishable
#print axioms DGRHS.Commutator.sourceRiesz_ae_continuous_indistinguishable
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_add
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_add
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_smul
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_smul
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_stopped_horizon
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_stopped_horizon
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_add
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_add
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_smul
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_smul
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_zero_integrand
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_zero_integrand
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_finsetSum
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_finsetSum
