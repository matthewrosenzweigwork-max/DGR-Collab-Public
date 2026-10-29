import DGPS.Topology.SingularAdapter
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractible spaces have no positive-degree homology (TOP014)

If `X` is a nonempty contractible space, then `H_n(X; F2) = 0` for every `n > 0`.  The proof
follows Mathlib's homotopy invariance: the identity of `X` is homotopic to a constant map, which
factors through a point, whose positive-degree homology vanishes.

* `DGPS.Topology.contractible_positive_degree_homology`: the packet interface; the degree-`n`
  singular homology object (with the `F2` adapter of TOP001) of a nonempty contractible space
  is a zero object for `n > 0`.
-/

open CategoryTheory

namespace DGPS.Topology

/-- Packet interface. For a nonempty contractible space `X` (in `TopCat.{0}`) and `n > 0`,
`H_n(X; F2)` is zero. Ordinary (not reduced) homology is used. -/
theorem contractible_positive_degree_homology (X : TopCat.{0}) [Nonempty X]
    [ContractibleSpace X] (n : ℕ) (hn : 0 < n) :
    Limits.IsZero ((singularHomology n).obj X) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic X
  let c : X ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let p : TopCat.of PUnit.{1} ⟶ X := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have hid : (singularHomology n).map (𝟙 X) = (singularHomology n).map (c ≫ p) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := 𝟙 X) (g := c ≫ p) H coeffModule n
  have hpt : Limits.IsZero ((singularHomology n).obj (TopCat.of PUnit.{1})) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      F2Mod n coeffModule (TopCat.of PUnit.{1}) (Nat.pos_iff_ne_zero.1 hn)
  rw [Limits.IsZero.iff_id_eq_zero, ← (singularHomology n).map_id, hid, (singularHomology n).map_comp]
  rw [hpt.eq_of_tgt ((singularHomology n).map c) 0, Limits.zero_comp]

end DGPS.Topology
