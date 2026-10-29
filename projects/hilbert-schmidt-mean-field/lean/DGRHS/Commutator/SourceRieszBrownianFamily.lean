import DGRHS.Commutator.SourceRieszBrownianPredictableBracketAE
import DGRHS.Commutator.SourceRieszBrownianCrossMartingaleAE
import DGRHS.Commutator.SourceRieszBrownianProcessAlgebra

/-! Finite common-filtered Brownian drivers and their actual stochastic integral
sum. The primitive joint future process is independent of the supplied common
past. This is stronger data than separate coordinate Brownian laws alone and is
stated explicitly. The scalar and paired independence facts used by the proved
integral construction are consequences, not extra compensator assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω]

structure SourceRieszFilteredBrownianFamily (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ι→ℝ≥0→Ω→ℝ) : Prop where
  brownian : ∀ i,IsBrownianReal (B i) P
  adapted : ∀ i,StronglyAdapted F (B i)
  independent : iIndepFun (fun i ω=>fun r=>B i r ω) P
  jointFuture : ∀ s,Indep (MeasurableSpace.comap
    (fun ω=>fun (i:ι) (r:{t:ℝ≥0 // s≤t})=>B i r ω-B i s ω) inferInstance) (F s) P

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
variable (B : ι→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)

include hB in
lemma SourceRieszFilteredBrownianFamily.increment_indep (i : ι) (s t : ℝ≥0) (hst : s≤t) :
    Indep (MeasurableSpace.comap (fun ω=>B i t ω-B i s ω) (borel ℝ)) (F s) P := by
  apply indep_of_indep_of_le_left (hB.jointFuture s)
  have hh : Measurable[MeasurableSpace.comap
      (fun ω=>fun (j:ι) (r:{u:ℝ≥0 // s≤u})=>B j r ω-B j s ω) inferInstance]
      (fun ω=>fun (j:ι) (r:{u:ℝ≥0 // s≤u})=>B j r ω-B j s ω) :=
    Measurable.of_comap_le le_rfl
  exact ((measurable_pi_apply (⟨t,hst⟩:{u:ℝ≥0 // s≤u})).comp
    ((measurable_pi_apply i).comp hh)).comap_le

include hB in
lemma SourceRieszFilteredBrownianFamily.pair_increment_indep
    (i j : ι) (s t u : ℝ≥0) (hst : s≤t) (hsu : s≤u) :
    Indep (MeasurableSpace.comap (fun ω=>(B i t ω-B i s ω,B j u ω-B j s ω))
      inferInstance) (F s) P := by
  apply indep_of_indep_of_le_left (hB.jointFuture s)
  have hh : Measurable[MeasurableSpace.comap
      (fun ω=>fun (k:ι) (r:{v:ℝ≥0 // s≤v})=>B k r ω-B k s ω) inferInstance]
      (fun ω=>fun (k:ι) (r:{v:ℝ≥0 // s≤v})=>B k r ω-B k s ω) :=
    Measurable.of_comap_le le_rfl
  exact (((measurable_pi_apply (⟨t,hst⟩:{v:ℝ≥0 // s≤v})).comp
    ((measurable_pi_apply i).comp hh)).prodMk
    ((measurable_pi_apply (⟨u,hsu⟩:{v:ℝ≥0 // s≤v})).comp
      ((measurable_pi_apply j).comp hh))).comap_le

lemma sourceRiesz_martingale_finsetSum (S : Finset ι) (M : ι→ℝ≥0→Ω→ℝ)
    (hM : ∀ i∈S,Martingale (M i) F P) :
    Martingale (fun t ω=>∑ i∈S,M i t ω) F P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    convert martingale_zero ℝ F P using 1
    funext t ω
    simp only [Finset.sum_empty,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero]
  | insert i S hi ih =>
    have hh := (hM i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj=>hM j (Finset.mem_insert_of_mem hj)))
    convert hh using 1
    funext t ω
    simp only [Finset.sum_insert hi,Pi.add_apply]

lemma sourceRiesz_martingale_compensated_finsetSum (S : Finset ι)
    (M Q : ι→ℝ≥0→Ω→ℝ)
    (hc : ∀ i∈S,Martingale (fun t ω=>(M i t ω)^2-Q i t ω) F P)
    (hx : ∀ i∈S,∀ j∈S,i≠j → Martingale (fun t ω=>M i t ω*M j t ω) F P) :
    Martingale (fun t ω=>(∑ i∈S,M i t ω)^2-∑ i∈S,Q i t ω) F P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    convert martingale_zero ℝ F P using 1
    funext t ω
    simp only [Finset.sum_empty,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero]
  | insert i S hi ih =>
    have hrest := ih (fun j hj=>hc j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk=>hx j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    have hcross := sourceRiesz_martingale_finsetSum P F S (fun j t ω=>M i t ω*M j t ω)
      (fun j hj=>hx i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun hij=>hi (hij ▸ hj)))
    have hh := ((hc i (Finset.mem_insert_self _ _)).add hrest).add (hcross.smul 2)
    convert hh using 1
    funext t ω
    simp only [Finset.sum_insert hi,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [←Finset.mul_sum]
    ring

variable [Fintype ι] (T : ℝ≥0)

def sourceRieszBrownianFamilyProcess
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i,sourceRieszBrownianContinuousProcess P F T (B i) (g i) t ω

def sourceRieszBrownianFamilyBracket
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i,sourceRieszBrownianBracket P F T (g i) t ω

include hB in
theorem sourceRieszBrownianFamilyProcess_martingale
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (sourceRieszBrownianFamilyProcess P F B T g) F P ∧
      (∀ t,MemLp (sourceRieszBrownianFamilyProcess P F B T g t) 2 P) ∧
      ∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianFamilyProcess P F B T g t ω) := by
  have hm i := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T (B i)
    (hB.brownian i).toIsPreBrownianReal (hB.adapted i) (hB.increment_indep P F B i)
    (hB.brownian i).cont (g i)
  refine ⟨sourceRiesz_martingale_finsetSum P F Finset.univ _ (fun i _=>(hm i).1),
    fun t=>memLp_finsetSum _ (fun i _=>(hm i).2.1 t),?_⟩
  filter_upwards [ae_all_iff.2 (fun i=>(hm i).2.2)] with ω hω
  exact continuous_finsetSum _ (fun i _=>hω i)

lemma sourceRieszBrownianFamilyBracket_predictable
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    IsStronglyPredictable F (sourceRieszBrownianFamilyBracket P F T g) := by
  change StronglyMeasurable[F.predictable] (fun p:ℝ≥0×Ω=>∑ i,sourceRieszBrownianBracket P F T (g i) p.1 p.2)
  have hm := Finset.stronglyMeasurable_sum Finset.univ (fun i _=>sourceRieszBrownianBracket_predictable P F T (g i))
  convert hm using 1
  funext p
  simp only [Finset.sum_apply,Function.uncurry]

include hB in
theorem sourceRieszBrownianFamilyProcess_compensated_square
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (fun t ω=>(sourceRieszBrownianFamilyProcess P F B T g t ω)^2-
      sourceRieszBrownianFamilyBracket P F T g t ω) F P := by
  apply sourceRiesz_martingale_compensated_finsetSum P F Finset.univ
  · intro i _
    exact sourceRieszBrownianContinuousProcess_predictable_compensator_of_ae_continuous P F T (B i)
      (hB.brownian i).toIsPreBrownianReal (hB.adapted i) (hB.increment_indep P F B i)
      (hB.brownian i).cont (g i)
  · intro i _ j _ hij
    exact sourceRieszBrownianContinuousProcess_cross_martingale_of_ae_continuous P F T (B i) (B j)
      (hB.brownian i).toIsPreBrownianReal (hB.brownian j).toIsPreBrownianReal
      (hB.adapted i) (hB.adapted j) (hB.increment_indep P F B i) (hB.increment_indep P F B j)
      (hB.independent.indepFun hij) (hB.pair_increment_indep P F B i j)
      (hB.brownian i).cont (hB.brownian j).cont (g i) (g j)

lemma sourceRieszBrownianFamilyBracket_eq_energy
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianFamilyBracket P F T g t ω=
      ∑ i,sourceRieszBrownianEnergy P F T (g i) t ω := by
  filter_upwards [ae_all_iff.2 (fun i=>sourceRieszBrownianBracket_eq_energy P F T (g i))] with ω hω
  intro t
  exact Finset.sum_congr rfl (fun i _=>hω i t)

lemma sourceRieszBrownianFamilyProcess_zero
    (g : ι→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (ω : Ω) :
    sourceRieszBrownianFamilyProcess P F B T g 0 ω=0 := by
  simp [sourceRieszBrownianFamilyProcess,sourceRieszBrownianContinuousProcess_zero]

end DGRHS.Commutator
#check @DGRHS.Commutator.SourceRieszFilteredBrownianFamily
#print axioms DGRHS.Commutator.SourceRieszFilteredBrownianFamily
#check @DGRHS.Commutator.SourceRieszFilteredBrownianFamily.increment_indep
#print axioms DGRHS.Commutator.SourceRieszFilteredBrownianFamily.increment_indep
#check @DGRHS.Commutator.SourceRieszFilteredBrownianFamily.pair_increment_indep
#print axioms DGRHS.Commutator.SourceRieszFilteredBrownianFamily.pair_increment_indep
#check @DGRHS.Commutator.sourceRiesz_martingale_finsetSum
#print axioms DGRHS.Commutator.sourceRiesz_martingale_finsetSum
#check @DGRHS.Commutator.sourceRiesz_martingale_compensated_finsetSum
#print axioms DGRHS.Commutator.sourceRiesz_martingale_compensated_finsetSum
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess
#check @DGRHS.Commutator.sourceRieszBrownianFamilyBracket
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyBracket
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess_martingale
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess_martingale
#check @DGRHS.Commutator.sourceRieszBrownianFamilyBracket_predictable
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyBracket_predictable
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess_compensated_square
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess_compensated_square
#check @DGRHS.Commutator.sourceRieszBrownianFamilyBracket_eq_energy
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyBracket_eq_energy
#check @DGRHS.Commutator.sourceRieszBrownianFamilyProcess_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianFamilyProcess_zero
