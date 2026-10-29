import DGRHS.Commutator.SourceRieszTransportKernel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Symmetry and proper measurable collision-zero totalization of the actual
higher Riesz transport contraction. Only global Lipschitz regularity of v is
used; no derivative of v or assumed measurability of the observable. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma sourceRieszPotential_iteratedFDeriv_neg (s : ℝ) (n : ℕ) (z : E) (w : Fin n→E) :
    iteratedFDeriv ℝ n (sourceRieszPotential s) (-z) (fun i=>-w i)=
      iteratedFDeriv ℝ n (sourceRieszPotential s) z w := by
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E (-1:ℝ) (by norm_num)).toContinuousLinearEquiv
  have hg : ∀ u,g u=-u := by intro u;change (-1:ℝ) • u=-u;simp
  have he : (sourceRieszPotential s ∘ g)=sourceRieszPotential (E:=E) s := by
    funext u
    simp [Function.comp_apply,hg,sourceRieszPotential]
  have hc : iteratedFDeriv ℝ n (sourceRieszPotential s ∘ g) z=
      (iteratedFDeriv ℝ n (sourceRieszPotential s) (g z)).compContinuousLinearMap
        (fun _=>g.toContinuousLinearMap) := by
    simpa only [preimage_univ,iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right (sourceRieszPotential s) uniqueDiffOn_univ (mem_univ z) n
  rw [he] at hc
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ=>F w) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,hg] using hm.symm

lemma sourceRieszTransportKernel_symmetric (s : ℝ) (n : ℕ) (v : E→E) (p : E×E) :
    sourceRieszTransportKernel n s v p.swap=sourceRieszTransportKernel n s v p := by
  classical
  by_cases hp : p.1=p.2
  · simp [sourceRieszTransportKernel,hp]
  have hp' : p.2≠p.1 := Ne.symm hp
  simp only [sourceRieszTransportKernel,Prod.fst_swap,Prod.snd_swap,ite_eq_right hp,ite_eq_right hp']
  simpa only [neg_sub] using sourceRieszPotential_iteratedFDeriv_neg s n (p.1-p.2) (fun _=>v p.1-v p.2)

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_sourceRieszTransportKernel (s : ℝ) (n : ℕ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    Measurable (sourceRieszTransportKernel n s v) := by
  classical
  let d : Set (E×E) := {p |p.1=p.2}
  let f : E×E→ℝ := fun p=>iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2) (fun _=>v p.1-v p.2)
  have hf : ContinuousOn f dᶜ := by
    intro p hp
    have hp' : p.1≠p.2 := hp
    have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp'
    have hd : ContinuousAt (fun q : E×E=>iteratedFDeriv ℝ n (sourceRieszPotential s) (q.1-q.2)) p :=
      ((contDiffAt_sourceRieszPotential s n hz).continuousAt_iteratedFDeriv le_rfl).comp (f := fun q : E×E=>q.1-q.2)
        (continuous_fst.sub continuous_snd).continuousAt
    have hw : ContinuousAt (fun q : E×E=>fun _ : Fin n=>v q.1-v q.2) p :=
      (continuous_pi (fun _=>(hv.continuous.comp continuous_fst).sub
        (hv.continuous.comp continuous_snd))).continuousAt
    have heval : Continuous (fun q : (E [×n]→L[ℝ] ℝ)×(Fin n→E)=>q.1 q.2) :=
      (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
    exact (heval.continuousAt.comp (hd.prodMk hw)).continuousWithinAt
  have h0 : ContinuousOn (fun _ : E×E=>(0:ℝ)) d := continuous_const.continuousOn
  have hd : MeasurableSet d := (isClosed_eq continuous_fst continuous_snd).measurableSet
  change Measurable (d.piecewise (fun _=>(0:ℝ)) f)
  exact h0.measurable_piecewise hf hd
end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_neg
#print axioms DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_neg
#check @DGRHS.Commutator.sourceRieszTransportKernel_symmetric
#print axioms DGRHS.Commutator.sourceRieszTransportKernel_symmetric
#check @DGRHS.Commutator.measurable_sourceRieszTransportKernel
#print axioms DGRHS.Commutator.measurable_sourceRieszTransportKernel
