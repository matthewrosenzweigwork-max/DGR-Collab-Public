/- Actual empirical second moment under the finite iid product law. Native
variance_sum_pi proves coordinate independence rather than assuming it. -/
import Mathlib.Probability.Moments.Variance
import DGRHS.Concentration.SourcePartitionRate
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def empiricalMean (F : Ω→ℝ) (N : ℕ) (x : Fin N→Ω) : ℝ :=
  (N:ℝ)⁻¹ * ∑ i : Fin N,F (x i)

lemma memLp_finite_sum {S : Type*} [MeasurableSpace S] {ν : Measure S}
    {ι : Type*} (s : Finset ι) (f : ι→S→ℝ) (hf : ∀ i∈s,MemLp (f i) 2 ν) :
    MemLp (fun x ↦ ∑ i∈s,f i x) 2 ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (memLp_zero : MemLp (fun _ : S ↦ (0:ℝ)) 2 ν)
  | @insert i s hi ih =>
    have ha := (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))
    convert ha using 1
    funext x
    simp only [Finset.sum_insert hi,Pi.add_apply]

lemma memLp_empiricalMean (F : Ω→ℝ) (hF : MemLp F 2 μ) (N : ℕ) :
    MemLp (empiricalMean F N) 2 (Measure.pi (fun _ : Fin N ↦ μ)) := by
  exact (memLp_finite_sum Finset.univ (fun (i : Fin N) (x : Fin N→Ω) ↦ F (x i))
    (fun i _ ↦ hF.comp_measurePreserving (measurePreserving_eval _ i))).const_mul _

lemma integral_empiricalMean (F : Ω→ℝ) (hF : MemLp F 2 μ)
    (N : ℕ) (hN : 1≤N) :
    (∫ x : Fin N→Ω,empiricalMean F N x ∂Measure.pi (fun _ : Fin N ↦ μ)) = ∫ x,F x ∂μ := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hi (i : Fin N) : (∫ x : Fin N→Ω,F (x i) ∂Measure.pi (fun _ : Fin N ↦ μ)) = ∫ x,F x ∂μ := by
    have hm := measurePreserving_eval (fun _ : Fin N ↦ μ) i
    have he := integral_map hm.aemeasurable (by rw [hm.map_eq]; exact hF.aestronglyMeasurable)
    rw [hm.map_eq] at he
    exact he.symm
  unfold empiricalMean
  rw [integral_const_mul,integral_finsetSum]
  · simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  · intro i _
    exact (hF.comp_measurePreserving (measurePreserving_eval _ i)).integrable (by norm_num)

lemma variance_empiricalMean (F : Ω→ℝ) (hF : MemLp F 2 μ) (N : ℕ) :
    variance (empiricalMean F N) (Measure.pi (fun _ : Fin N ↦ μ)) =
      (N:ℝ)⁻¹ * variance F μ := by
  unfold empiricalMean
  rw [variance_const_mul]
  have hv := variance_sum_pi (μ := fun _ : Fin N ↦ μ) (X := fun _ ↦ F) (fun _ ↦ hF)
  have he : (∑ i : Fin N,fun x : Fin N→Ω ↦ F (x i)) =
      (fun x : Fin N→Ω ↦ ∑ i : Fin N,F (x i)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hv
  have hv' : variance (fun x : Fin N→Ω ↦ ∑ i : Fin N,F (x i))
      (Measure.pi (fun _ : Fin N ↦ μ)) = (N:ℝ)*variance F μ := by
    simpa only [Finset.sum_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hv
  rw [hv']
  by_cases hn : (N:ℝ)=0
  · simp [hn]
  · field_simp

lemma empiricalMean_centered_second_moment (F : Ω→ℝ) (hF : MemLp F 2 μ)
    (N : ℕ) (hN : 1≤N) :
    (∫ x : Fin N→Ω,(empiricalMean F N x-(∫ y,F y ∂μ))^2
      ∂Measure.pi (fun _ : Fin N ↦ μ)) = (N:ℝ)⁻¹ * variance F μ := by
  rw [← integral_empiricalMean μ F hF N hN,
    ← variance_eq_integral (memLp_empiricalMean μ F hF N).aemeasurable]
  exact variance_empiricalMean μ F hF N

end DGRHS.Concentration
#print axioms DGRHS.Concentration.memLp_empiricalMean
#check @DGRHS.Concentration.memLp_empiricalMean
#print axioms DGRHS.Concentration.integral_empiricalMean
#check @DGRHS.Concentration.integral_empiricalMean
#print axioms DGRHS.Concentration.variance_empiricalMean
#check @DGRHS.Concentration.variance_empiricalMean
#print axioms DGRHS.Concentration.empiricalMean_centered_second_moment
#check @DGRHS.Concentration.empiricalMean_centered_second_moment
