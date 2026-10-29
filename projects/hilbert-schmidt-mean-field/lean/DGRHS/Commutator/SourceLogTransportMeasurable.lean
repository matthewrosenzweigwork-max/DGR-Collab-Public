import DGRHS.Commutator.SourceLogTransportBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

noncomputable section
open Set MeasureTheory
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Evenness of the physical potential gives symmetry of every contracted derivative. -/
theorem sourceLogPotential_iteratedFDeriv_neg (n : ℕ) (z w : E) :
    iteratedFDeriv ℝ n sourceLogPotential (-z) (fun _ => -w) =
      iteratedFDeriv ℝ n sourceLogPotential z (fun _ => w) := by
  let g : E ≃L[ℝ] E :=
    (LinearEquiv.smulOfNeZero ℝ E (-1) (by norm_num)).toContinuousLinearEquiv
  have hg : ∀ u, g u = -u := by intro u; change (-1 : ℝ) • u = -u; simp
  have he : sourceLogPotential ∘ g = sourceLogPotential (E := E) := by
    funext u
    simp [hg, sourceLogPotential]
  have hc : iteratedFDeriv ℝ n (sourceLogPotential ∘ g) z =
      (iteratedFDeriv ℝ n sourceLogPotential (g z)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right sourceLogPotential uniqueDiffOn_univ (mem_univ z) n
  rw [he] at hc
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ => F (fun _ => w)) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg] using hm.symm

theorem sourceLogTransportKernel_swap (n : ℕ) (v : E → E) (p : E × E) :
    sourceLogTransportKernel n v p.swap = sourceLogTransportKernel n v p := by
  classical
  by_cases hp : p.1 = p.2
  · simp [sourceLogTransportKernel, hp]
  · simp only [sourceLogTransportKernel, Prod.fst_swap, Prod.snd_swap,
      ite_eq_right hp, ite_eq_right (Ne.symm hp)]
    simpa only [neg_sub] using
      sourceLogPotential_iteratedFDeriv_neg n (p.1 - p.2) (v p.1 - v p.2)

section Measurable
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [FiniteDimensional ℝ E] in
/-- Actual derivative evaluation is continuous away from collision; the zero representative is measurable. -/
theorem measurable_sourceLogTransportKernel (n : ℕ) {v : E → E} {K : ℝ≥0}
    (hv : LipschitzWith K v) : Measurable (sourceLogTransportKernel n v) := by
  classical
  let s : Set (E × E) := {p | p.1 ≠ p.2}
  let f : E × E → ℝ := fun p =>
    iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2) (fun _ => v p.1 - v p.2)
  have hz : Continuous (fun p : E × E => p.1 - p.2) := continuous_fst.sub continuous_snd
  have hw : Continuous (fun p : E × E => (fun _ : Fin n => v p.1 - v p.2)) :=
    continuous_pi fun _ => (hv.continuous.comp continuous_fst).sub
      (hv.continuous.comp continuous_snd)
  have hEval : Continuous (fun q : (E [×n]→L[ℝ] ℝ) × (Fin n → E) => q.1 q.2) :=
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
  have hf : ContinuousOn f s := by
    intro p hp
    have hD : ContinuousAt (fun q : E × E =>
        iteratedFDeriv ℝ n sourceLogPotential (q.1 - q.2)) p :=
      ((contDiffAt_sourceLogPotential n (sub_ne_zero.mpr hp)).continuousAt_iteratedFDeriv
        le_rfl).comp (f := fun q : E × E => q.1 - q.2) hz.continuousAt
    have hpw : ContinuousAt (fun q : E × E =>
        (iteratedFDeriv ℝ n sourceLogPotential (q.1 - q.2),
          fun _ : Fin n => v q.1 - v q.2)) p := hD.prodMk hw.continuousAt
    exact (hEval.continuousAt.comp hpw).continuousWithinAt
  have hs : MeasurableSet s := (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  have hm := hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hs
  have he : s.piecewise f (fun _ => 0) = sourceLogTransportKernel n v := by
    funext p
    by_cases hp : p.1 = p.2 <;> simp [s, f, sourceLogTransportKernel, hp]
  rw [he] at hm
  exact hm
end Measurable

#print axioms sourceLogPotential_iteratedFDeriv_neg
#print axioms sourceLogTransportKernel_swap
#print axioms measurable_sourceLogTransportKernel
#check @measurable_sourceLogTransportKernel
end DGRHS.Commutator
