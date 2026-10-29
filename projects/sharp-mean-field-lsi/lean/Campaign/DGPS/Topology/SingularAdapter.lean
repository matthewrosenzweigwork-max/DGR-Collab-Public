import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Singular chain and homology adapter (TOP001)

Fixes the single coefficient object `F2 = ZMod 2` as a module over itself, in `ModuleCat.{0} F2`,
and instantiates Mathlib's categorical singular chain complex and singular homology functors
(`AlgebraicTopology.singularChainComplexFunctor`, `AlgebraicTopology.singularHomologyFunctor`)
on it, for spaces in `TopCat.{0}`. Local (relative) and global homology both use this adapter.

* `DGPS.Topology.singularChains`: `TopCat ⥤ ChainComplex (ModuleCat F2) ℕ`.
* `DGPS.Topology.singularHomology n`: `TopCat ⥤ ModuleCat F2`.
* `DGPS.Topology.singular_chain_and_homology_adapter`: the packet interface; chain and homology
  maps are functorial (identities, composition) and homology is degree-`n` homology of chains.
-/

open CategoryTheory

namespace DGPS.Topology

/-- The coefficient field `F2`. -/
abbrev F2 : Type := ZMod 2

/-- The module category of the adapter (universe 0). -/
abbrev F2Mod : Type 1 := ModuleCat.{0} F2

/-- The one-dimensional coefficient module `F2` over itself. -/
abbrev coeffModule : F2Mod := ModuleCat.of F2 F2

/-- Singular chain complex functor with `F2` coefficients. -/
noncomputable def singularChains : TopCat.{0} ⥤ ChainComplex F2Mod ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor.{0} F2Mod).obj coeffModule

/-- Degree-`n` singular homology functor with `F2` coefficients. -/
noncomputable def singularHomology (n : ℕ) : TopCat.{0} ⥤ F2Mod :=
  (AlgebraicTopology.singularHomologyFunctor.{0} F2Mod n).obj coeffModule

/-- Packet interface: chain and homology maps of continuous maps are functorial, and singular
homology is the degree-`n` homology of the singular chain complex. -/
theorem singular_chain_and_homology_adapter :
    (∀ X : TopCat.{0}, singularChains.map (𝟙 X) = 𝟙 (singularChains.obj X)) ∧
    (∀ {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
      singularChains.map (f ≫ g) = singularChains.map f ≫ singularChains.map g) ∧
    (∀ (n : ℕ) (X : TopCat.{0}), (singularHomology n).map (𝟙 X) = 𝟙 ((singularHomology n).obj X)) ∧
    (∀ (n : ℕ) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (singularHomology n).map (f ≫ g) = (singularHomology n).map f ≫ (singularHomology n).map g) ∧
    (∀ n : ℕ, singularHomology n =
      singularChains ⋙ HomologicalComplex.homologyFunctor F2Mod (ComplexShape.down ℕ) n) :=
  ⟨fun _ => singularChains.map_id _, fun f g => singularChains.map_comp f g,
    fun n _ => (singularHomology n).map_id _, fun n _ _ _ f g => (singularHomology n).map_comp f g,
    fun _ => rfl⟩

end DGPS.Topology
