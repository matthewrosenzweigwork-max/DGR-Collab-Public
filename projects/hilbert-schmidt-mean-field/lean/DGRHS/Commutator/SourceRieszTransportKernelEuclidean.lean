import DGRHS.Commutator.SourceRieszTransportKernelBound
import DGRHS.Commutator.SourceRieszTransportKernelMeasurable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Original all-fixed-n full Riesz transport prerequisite, 0<s<d,n>=1.
Source3284ff. Truncation derivative absorption remains a separate dependency;
this theorem makes no favorable profile or commutator moment assumption. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator

lemma sourceRieszTransportKernel_eq_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : ℝ) (n : ℕ) (v : E→E) {x y : E} (hxy : x≠y) :
    sourceRieszTransportKernel n s v (x,y)=
      iteratedFDeriv ℝ n (fun z : E=>‖z‖^(-s)/s) (x-y) (fun _=>v x-v y) := by
  classical
  simp only [sourceRieszTransportKernel,ite_eq_right hxy]
  rfl

lemma sourceRieszTransportKernel_eq_zero_of_lipschitz_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : ℝ) (n : ℕ) (hn : 0<n) {v : E→E} (hv : LipschitzWith 0 v) (p : E×E) :
    sourceRieszTransportKernel n s v p=0 := by
  obtain ⟨C,_,hC⟩ := exists_sourceRieszTransportKernel_bound (E:=E) s n
  have hb := hC hv p
  simp only [NNReal.coe_zero,zero_pow (Nat.ne_of_gt hn),mul_zero,zero_mul] at hb
  exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))

 theorem exists_sourceRieszTransportKernel_Euclidean {ι : Type*} [Fintype ι]
    (s : ℝ) (_hs : 0<s) (_hsd : s<(Fintype.card ι:ℝ)) (n : ℕ) (_hn : 1≤n) :
    ∃ C : ℝ,0<C ∧ ∀ {K : ℝ≥0} {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι},
      LipschitzWith K v →
      Measurable (sourceRieszTransportKernel n s v) ∧
      (∀ p,sourceRieszTransportKernel n s v p.swap=sourceRieszTransportKernel n s v p) ∧
      (∀ p,|sourceRieszTransportKernel n s v p|≤C*(K:ℝ)^n*‖p.1-p.2‖^(-s)) := by
  obtain ⟨C,hC,hB⟩ := exists_sourceRieszTransportKernel_bound (E:=EuclideanSpace ℝ ι) s n
  refine ⟨C+1,by linarith,?_⟩
  intro K v hv
  refine ⟨measurable_sourceRieszTransportKernel s n hv,sourceRieszTransportKernel_symmetric s n v,?_⟩
  intro p
  exact (hB hv p).trans (by gcongr;linarith)
end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransportKernel_eq_iteratedFDeriv
#print axioms DGRHS.Commutator.sourceRieszTransportKernel_eq_iteratedFDeriv
#check @DGRHS.Commutator.sourceRieszTransportKernel_eq_zero_of_lipschitz_zero
#print axioms DGRHS.Commutator.sourceRieszTransportKernel_eq_zero_of_lipschitz_zero
#check @DGRHS.Commutator.exists_sourceRieszTransportKernel_Euclidean
#print axioms DGRHS.Commutator.exists_sourceRieszTransportKernel_Euclidean
