import DGPS.Examples.RoughBoundary.SemicontinuityAssembly

/-!
# T04: failure of both semicontinuities for both absolute nonlinear rates

For fixed `0 < α < 1` (resp. `1 ≤ p < 2`) the rough kernel class `K_α = K ∩ C^α` (resp.
`K_p = K ∩ W^{1,p}`) carries the `C^α` (resp. `W^{1,p}`) norm subspace topology, `V = 0`, and the
weak convolution drift is the canonical provider `RoughKernelClass.drift`. Neither the scalar
rate `r_*` nor the species rate `r_ms` is lower or upper semicontinuous there.

The content is the integrated SEM015 theorem `DGPS.RegularityBoundary.rates_neither_semicontinuous`;
this module only restates it with the frozen T04 signature (real parameters `α`, `p`).

Design: `HolderKernelClass α` is the existing `HolderKernel α.toNNReal`; `SobolevKernelClass p` is
the existing `SobolevKernel (ENNReal.ofReal p)`. Their topologies are the norm-embedding
subspace topologies of SEM001 (`holderTopology`, `sobolevTopology`); the Sobolev one is selected
by `dite` on `1 ≤ p`, so no `Fact` is needed in the frozen statement (the junk branch is `⊥`).
-/

open Filter Topology
open scoped ENNReal NNReal

namespace DGPS

/-- The kernel class `K_α = K ∩ C^α` (frozen name `HolderKernelClass`). -/
def HolderKernelClass (α : ℝ) : Type :=
  DGPS.Analysis.RateTopology.HolderKernel α.toNNReal

/-- The kernel class `K_p = K ∩ W^{1,p}` (frozen name `SobolevKernelClass`). -/
def SobolevKernelClass (p : ℝ) : Type :=
  DGPS.Analysis.RateTopology.SobolevKernel (ENNReal.ofReal p)

/-- The `C^α` norm subspace topology on `K_α`. -/
noncomputable instance instTopologicalSpaceHolderKernelClass_T04 (α : ℝ) :
    TopologicalSpace (HolderKernelClass α) :=
  DGPS.Analysis.RateTopology.holderTopology α.toNNReal

/-- The `W^{1,p}` norm subspace topology on `K_p` (for `1 ≤ p`; trivial junk topology otherwise). -/
noncomputable instance instTopologicalSpaceSobolevKernelClass_T04 (p : ℝ) :
    TopologicalSpace (SobolevKernelClass p) :=
  if h : 1 ≤ p then
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal h⟩
    DGPS.Analysis.RateTopology.sobolevTopology (ENNReal.ofReal p)
  else ⊥

/-- Kernel classes that sit inside the ambient rough kernel class `K`. -/
class RoughKernelSubclass (C : Type) where
  toRough : C → DGPS.Analysis.RateTopology.RoughKernelClass

noncomputable instance instRoughKernelSubclassHolder_T04 (α : ℝ) :
    RoughKernelSubclass (HolderKernelClass α) := ⟨fun W => W.1⟩

noncomputable instance instRoughKernelSubclassSobolev_T04 (p : ℝ) :
    RoughKernelSubclass (SobolevKernelClass p) := ⟨fun W => W.1⟩

/-- The interaction data (`V = 0`) of a Hölder-class kernel. -/
noncomputable def HolderKernelClass.toInteraction {α : ℝ} (W : HolderKernelClass α) :
    InteractionData 1 :=
  W.1.toInteraction

/-- The interaction data (`V = 0`) of a Sobolev-class kernel. -/
noncomputable def SobolevKernelClass.toInteraction {p : ℝ} (W : SobolevKernelClass p) :
    InteractionData 1 :=
  W.1.toInteraction

/-- The proven weak force provider, for every kernel of a kernel class. -/
noncomputable def kernelClassDrift {C : Type} [RoughKernelSubclass C] (W : C) :
    AbsoluteDrift (RoughKernelSubclass.toRough W).toInteraction :=
  (RoughKernelSubclass.toRough W).drift

end DGPS

namespace DGPS.RegularityBoundary

open DGPS.Analysis.RateTopology DGPS.Examples.RoughBoundary.Semicontinuity

/-- **T04 (Hölder).** For each `0 < α < 1`, neither `r_*` nor `r_ms` is lower or upper
semicontinuous on `K_α` with the `C^α` norm topology. -/
theorem rates_neither_semicontinuous_holder (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let K := DGPS.HolderKernelClass α
    let rStar : K → ℝ≥0∞ := fun W =>
      DGPS.scalarRate W.toInteraction (DGPS.kernelClassDrift W)
    let rMs : K → ℝ≥0∞ := fun W =>
      DGPS.speciesRate W.toInteraction (DGPS.kernelClassDrift W)
    ¬ LowerSemicontinuous rStar ∧ ¬ UpperSemicontinuous rStar ∧
    ¬ LowerSemicontinuous rMs ∧ ¬ UpperSemicontinuous rMs := by
  intro K rStar rMs
  obtain ⟨e0, L, hL, he0, -, -, hH, -⟩ := rates_neither_semicontinuous
  have h0 : 0 < ((α.toNNReal : ℝ≥0) : ℝ) := by rw [Real.coe_toNNReal _ hα0.le]; exact hα0
  have h1 : ((α.toNNReal : ℝ≥0) : ℝ) < 1 := by rw [Real.coe_toNNReal _ hα0.le]; exact hα1
  obtain ⟨-, ⟨l1, l2⟩, -, ⟨u1, u2⟩⟩ := hH α.toNNReal h0 h1
  exact ⟨l1, u1, l2, u2⟩

/-- **T04 (Sobolev).** For each `1 ≤ p < 2`, neither `r_*` nor `r_ms` is lower or upper
semicontinuous on `K_p` with the `W^{1,p}` norm topology. -/
theorem rates_neither_semicontinuous_sobolev (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    let K := DGPS.SobolevKernelClass p
    let rStar : K → ℝ≥0∞ := fun W =>
      DGPS.scalarRate W.toInteraction (DGPS.kernelClassDrift W)
    let rMs : K → ℝ≥0∞ := fun W =>
      DGPS.speciesRate W.toInteraction (DGPS.kernelClassDrift W)
    ¬ LowerSemicontinuous rStar ∧ ¬ UpperSemicontinuous rStar ∧
    ¬ LowerSemicontinuous rMs ∧ ¬ UpperSemicontinuous rMs := by
  intro K rStar rMs
  obtain ⟨e0, L, hL, he0, -, -, -, hS⟩ := rates_neither_semicontinuous
  obtain ⟨-, ⟨l1, l2⟩, -, ⟨u1, u2⟩⟩ := hS p hp1 hp2
  have hinst : (instTopologicalSpaceSobolevKernelClass_T04 p) =
      (haveI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp1⟩
       sobolevTopology (ENNReal.ofReal p)) := by
    unfold instTopologicalSpaceSobolevKernelClass_T04
    exact dite_eq_left_of_eq_true (eq_true hp1)
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp1⟩
  simp only [rStar, rMs, K]
  rw [hinst]
  exact ⟨l1, u1, l2, u2⟩

end DGPS.RegularityBoundary
