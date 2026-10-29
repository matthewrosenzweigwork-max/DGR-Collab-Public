/- Scalar measurability follows from native density and evaluation continuity.
No strong measurability of an arbitrary Hilbert feature map is a premise. -/
import DGRHS.Kernel.PositiveDefiniteKernelRKHS
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.Kernel

 theorem measurable_scalarRKHS_function {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H Ω ℝ]
    (hk : ∀ (x : Ω) (r : ℝ),Measurable (fun y=>(RKHS.kerFun H x r) y))
    (f : H) : Measurable (fun x=>f x) := by
  let S : Set H := {RKHS.kerFun H x r | (x : Ω) (r : ℝ)}
  have hs : ∀ g ∈ Submodule.span ℝ S,Measurable (fun x=>g x) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x,r,rfl⟩ := hg
      exact hk x r
    | zero => simpa only [RKHS.coe_zero,Pi.zero_apply] using (measurable_const : Measurable (fun _ : Ω=>(0:ℝ)))
    | add g h hg hh hgm hhm =>
      have he : (fun x=>(g+h) x)=(fun x=>g x)+(fun x=>h x) := by
        funext x
        simp only [RKHS.coe_add,Pi.add_apply]
      rw [he]
      exact hgm.add hhm
    | smul r g hg hgm =>
      simpa only [RKHS.coe_smul,Pi.smul_apply,smul_eq_mul] using hgm.const_mul r
  have hc : f ∈ closure (Submodule.span ℝ S : Set H) := by
    rw [←Submodule.topologicalClosure_coe]
    change f ∈ (Submodule.span ℝ {RKHS.kerFun H x r | (x : Ω) (r : ℝ)}).topologicalClosure
    rw [RKHS.kerFun_dense H]
    exact Submodule.mem_top
  obtain ⟨g,hg,hgf⟩ := mem_closure_iff_seq_limit.mp hc
  exact measurable_of_tendsto_metrizable (fun n=>hs (g n) (hg n))
    (tendsto_pi_nhds.2 (fun x=>((RKHS.continuous_eval x).tendsto f).comp hgf))
end DGRHS.Kernel
#check @DGRHS.Kernel.measurable_scalarRKHS_function
#print axioms DGRHS.Kernel.measurable_scalarRKHS_function
