import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual source full positive-Riesz kernel and exact higher derivative scaling.
Source3284ff, original SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
Native scaling route adapted from worker A's checked SourceLogTransportScaling,
SHA52e69af3934645bd17c1c30c6d2c81de5f5b8cdb48ab0ff7da4a7ee09458b6d1;
Riesz multiplicative homogeneity is proved here. No derivative bound premise. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceRieszPotential (s : ℝ) (z : E) : ℝ := ‖z‖^(-s)/s

def sourceRieszTransportKernel (n : ℕ) (s : ℝ) (v : E→E) (p : E×E) : ℝ := by
  classical
  exact if p.1=p.2 then 0 else
    iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2) (fun _=>v p.1-v p.2)

lemma contDiffAt_sourceRieszPotential (s : ℝ) (n : ℕ) {z : E} (hz : z≠0) :
    ContDiffAt ℝ n (sourceRieszPotential s) z :=
  ((contDiffAt_norm ℝ hz).rpow_const_of_ne (norm_ne_zero_iff.mpr hz)).div_const s

lemma contDiffOn_sourceRieszPotential (s : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (sourceRieszPotential (E:=E) s) ({0}ᶜ : Set E) := by
  intro z hz
  exact (contDiffAt_sourceRieszPotential s n (by simpa using hz)).contDiffWithinAt

lemma sourceRieszPotential_smul (s : ℝ) {r : ℝ} (hr : 0<r) (z : E) :
    sourceRieszPotential s (r • z)=r^(-s)*sourceRieszPotential s z := by
  simp only [sourceRieszPotential,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rw [Real.mul_rpow hr.le (norm_nonneg z)]
  ring

variable [FiniteDimensional ℝ E]

lemma sourceRieszPotential_iteratedFDeriv_smul (s : ℝ) (n : ℕ)
    {r : ℝ} (hr : 0<r) {z : E} (hz : z≠0) :
    r^n • iteratedFDeriv ℝ n (sourceRieszPotential s) (r • z)=
      r^(-s) • iteratedFDeriv ℝ n (sourceRieszPotential s) z := by
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toContinuousLinearEquiv
  have hg : ∀ u,g u=r • u := fun _=>rfl
  have hc : iteratedFDeriv ℝ n (sourceRieszPotential s ∘ g) z=
      (iteratedFDeriv ℝ n (sourceRieszPotential s) (g z)).compContinuousLinearMap
        (fun _=>g.toContinuousLinearMap) := by
    simpa only [preimage_univ,iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right (sourceRieszPotential s) uniqueDiffOn_univ (mem_univ z) n
  have he : (sourceRieszPotential s ∘ g)=r^(-s) • sourceRieszPotential (E:=E) s := by
    funext u
    exact sourceRieszPotential_smul s hr u
  rw [he,iteratedFDeriv_const_smul_apply (contDiffAt_sourceRieszPotential s n hz)] at hc
  ext m
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ=>F m) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,hg,
    ContinuousMultilinearMap.map_smul_univ] using hm.symm
end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPotential
#print axioms DGRHS.Commutator.sourceRieszPotential
#check @DGRHS.Commutator.sourceRieszTransportKernel
#print axioms DGRHS.Commutator.sourceRieszTransportKernel
#check @DGRHS.Commutator.contDiffAt_sourceRieszPotential
#print axioms DGRHS.Commutator.contDiffAt_sourceRieszPotential
#check @DGRHS.Commutator.contDiffOn_sourceRieszPotential
#print axioms DGRHS.Commutator.contDiffOn_sourceRieszPotential
#check @DGRHS.Commutator.sourceRieszPotential_smul
#print axioms DGRHS.Commutator.sourceRieszPotential_smul
#check @DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_smul
#print axioms DGRHS.Commutator.sourceRieszPotential_iteratedFDeriv_smul
