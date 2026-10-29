import DGPS.Topology.FundamentalClass
import DGPS.Topology.ContractibleHomology

/-!
# A closed positive dimensional manifold is not contractible (LIP037)

A nonempty compact connected boundaryless `n`-manifold, `n > 0`, has a nonzero class in
`H_n(M; F2)` (TOP013), whereas a contractible space has vanishing positive-degree homology
(TOP014).  Hence `M` is not contractible.
-/

namespace DGPS.Lipschitz

open DGPS.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

include I

/-- **Closed positive dimensional manifolds are not contractible.**  A nonempty compact connected
Hausdorff boundaryless topological `n`-manifold with `n > 0` is not contractible. -/
theorem closed_positive_dimensional_manifold_is_not_contractible
    [CompactSpace M] [ConnectedSpace M] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n) : ¬ ContractibleSpace M := by
  intro hc
  obtain ⟨c, hc0, -⟩ := nonzero_compact_fundamental_class I n hn hE (M := M)
  have hz := contractible_positive_degree_homology (TopCat.of M) n hn
  have := ModuleCat.subsingleton_of_isZero hz
  exact hc0 (Subsingleton.elim _ _)

end DGPS.Lipschitz
