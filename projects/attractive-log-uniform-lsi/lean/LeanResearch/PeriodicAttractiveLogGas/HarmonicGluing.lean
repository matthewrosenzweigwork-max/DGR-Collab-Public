import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic.Choose

/-! Gluing local smooth harmonic representatives on an open planar set.

Agreement on overlaps follows from continuity, local almost-everywhere equality,
and positivity of Euclidean volume on nonempty open sets. A countable subcover
then gives almost-everywhere equality on the entire set. Compatibility of the
local representatives and the global almost-everywhere conclusion are proved,
not supplied as hypotheses. No regularity outside the open set is asserted.
-/

noncomputable section

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology

namespace PeriodicAttractiveLogGas

/-- Continuous representatives of the same almost-everywhere function agree at
every point of an open overlap, for actual Euclidean Lebesgue measure. -/
theorem continuous_representatives_eqOn_open_inter
    {u f g : PlanarSpace → ℝ} {V W : Set PlanarSpace}
    (hV : IsOpen V) (hW : IsOpen W) (hf : Continuous f) (hg : Continuous g)
    (huf : u =ᵐ[volume.restrict V] f) (hug : u =ᵐ[volume.restrict W] g) :
    EqOn f g (V ∩ W) := by
  have huf' : u =ᵐ[volume.restrict (V ∩ W)] f :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left huf
  have hug' : u =ᵐ[volume.restrict (V ∩ W)] g :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hug
  exact Measure.eqOn_open_of_ae_eq (huf'.symm.trans hug') (hV.inter hW)
    hf.continuousOn hg.continuousOn

/-- Local globally smooth representatives, harmonic on their open neighborhoods,
glue to one smooth harmonic representative on the open set. A countable subcover
is used only to combine the local almost-everywhere identifications. -/
theorem exists_smooth_harmonic_representative_of_local
    {U : Set PlanarSpace} (hU : IsOpen U) {u : PlanarSpace → ℝ}
    (hloc : ∀ x ∈ U, ∃ V : Set PlanarSpace, ∃ v : PlanarSpace → ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContDiff ℝ ∞ v ∧
        HarmonicOnNhd v V ∧ u =ᵐ[volume.restrict V] v) :
    ∃ v : PlanarSpace → ℝ, ContDiffOn ℝ ∞ v U ∧ HarmonicOnNhd v U ∧
      u =ᵐ[volume.restrict U] v := by
  classical
  choose V v hVo hVmem hVU hvsmooth hvharm huae using
    (fun i : U ↦ hloc i i.2)
  have hcompat (i j : U) : EqOn (v i) (v j) (V i ∩ V j) :=
    continuous_representatives_eqOn_open_inter (hVo i) (hVo j)
      (hvsmooth i).continuous (hvsmooth j).continuous (huae i) (huae j)
  let g : PlanarSpace → ℝ := fun x ↦ if hx : x ∈ U then v ⟨x, hx⟩ x else 0
  have hglue (i : U) : EqOn g (v i) (V i) := by
    intro x hx
    have hxU : x ∈ U := hVU i hx
    dsimp only [g]
    rw [dite_eq_left hxU]
    exact hcompat ⟨x, hxU⟩ i ⟨hVmem ⟨x, hxU⟩, hx⟩
  have hlocalEq (i : U) {x : PlanarSpace} (hx : x ∈ V i) :
      g =ᶠ[𝓝 x] v i :=
    (hglue i).eventuallyEq_of_mem ((hVo i).mem_nhds hx)
  have hsmooth : ContDiffOn ℝ ∞ g U := by
    apply hU.contDiffOn_iff.mpr
    intro x hx
    exact (hvsmooth ⟨x, hx⟩).contDiffAt.congr_of_eventuallyEq
      (hlocalEq ⟨x, hx⟩ (hVmem ⟨x, hx⟩))
  have hharm : HarmonicOnNhd g U := by
    intro x hx
    exact (harmonicAt_congr_nhds (hlocalEq ⟨x, hx⟩ (hVmem ⟨x, hx⟩))).2
      (hvharm ⟨x, hx⟩ x (hVmem ⟨x, hx⟩))
  have hcover : U ⊆ ⋃ i : U, V i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hVmem ⟨x, hx⟩⟩
  obtain ⟨S, hScount, hScover⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo hcover
  have haeUnion : u =ᵐ[volume.restrict (⋃ i ∈ S, V i)] g := by
    apply (ae_eq_restrict_biUnion_iff V hScount u g).2
    intro i _
    exact (huae i).trans ((hglue i).aeEq_restrict (hVo i).measurableSet).symm
  exact ⟨g, hsmooth, hharm, ae_restrict_of_ae_restrict_of_subset hScover haeUnion⟩

end PeriodicAttractiveLogGas
