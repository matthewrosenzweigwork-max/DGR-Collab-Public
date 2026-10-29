import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The finite-graph separation step of the manuscript collision-integral lemma.

Source: `lem:collision-integral`, "Separation into smaller groups", in the
immutable corrected manuscript, lines 202–203. The graph joins distinct
indices whose coordinate distance is strictly below the threshold. A simple
path has at most one fewer edge than the number of vertices. The component
of the anchored index therefore cannot contain a coordinate at the specified
positive radius. This establishes only geometric separation, not collision
integrability or the subsequent factorization and integration estimates.
-/

noncomputable section

open Set

namespace PeriodicAttractiveLogGas

section MetricSeparation

variable {ι E : Type*} [PseudoMetricSpace E]

/-- Distinct indices are adjacent precisely when their coordinate distance is
strictly smaller than the chosen threshold. Coincident coordinates are allowed. -/
def clusterThresholdGraph (w : ι → E) (τ : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ dist (w i) (w j) < τ
  symm := ⟨fun i j h ↦ ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The triangle inequality along every actual walk. -/
theorem clusterThresholdGraph_walk_dist_le (w : ι → E) (τ : ℝ)
    {i j : ι} (p : (clusterThresholdGraph w τ).Walk i j) :
    dist (w i) (w j) ≤ (p.length : ℝ) * τ := by
  induction p with
  | nil => simp
  | @cons i l j h p ih =>
    calc
      dist (w i) (w j) ≤ dist (w i) (w l) + dist (w l) (w j) := dist_triangle _ _ _
      _ ≤ τ + (p.length : ℝ) * τ := add_le_add h.2.le ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℝ) * τ := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- A walk with distinct endpoints has at least one edge, so its distance
bound is strict when each edge has distance strictly below the threshold. -/
theorem clusterThresholdGraph_walk_dist_lt (w : ι → E) (τ : ℝ)
    {i j : ι} (hne : i ≠ j) (p : (clusterThresholdGraph w τ).Walk i j) :
    dist (w i) (w j) < (p.length : ℝ) * τ := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons i l j h p =>
    calc
      dist (w i) (w j) ≤ dist (w i) (w l) + dist (w l) (w j) := dist_triangle _ _ _
      _ < τ + (p.length : ℝ) * τ :=
        add_lt_add_of_lt_of_le h.2 (clusterThresholdGraph_walk_dist_le w τ p)
      _ = ((SimpleGraph.Walk.cons h p).length : ℝ) * τ := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Every vertex in the anchored component is strictly inside radius `R`.
The only path estimate used is the actual finite simple-path cardinal bound. -/
theorem clusterThresholdGraph_reachable_dist_lt [Fintype ι]
    (w : ι → E) (hcard : 2 ≤ Fintype.card ι) {R : ℝ} (hR : 0 < R)
    {i j : ι}
    (hreach : (clusterThresholdGraph w (R / ((Fintype.card ι - 1 : ℕ) : ℝ))).Reachable i j) :
    dist (w i) (w j) < R := by
  classical
  have hn : 0 < Fintype.card ι - 1 := by omega
  have hnR : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hτ : 0 ≤ R / ((Fintype.card ι - 1 : ℕ) : ℝ) := (div_pos hR hnR).le
  by_cases hij : i = j
  · simpa only [hij, dist_self] using hR
  · apply hreach.elim_path
    intro p
    have hlen : p.val.length ≤ Fintype.card ι - 1 := by
      have h := p.property.length_lt
      omega
    have hlenR : (p.val.length : ℝ) ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) := by
      exact_mod_cast hlen
    calc
      dist (w i) (w j) < (p.val.length : ℝ) *
          (R / ((Fintype.card ι - 1 : ℕ) : ℝ)) :=
        clusterThresholdGraph_walk_dist_lt w _ hij p.val
      _ ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) *
          (R / ((Fintype.card ι - 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hlenR hτ
      _ = R := by field_simp [ne_of_gt hnR]

/-- A coordinate at distance at least `R` forces a nontrivial partition, whose
cross distances are all at least `R / (number of vertices - 1)`. -/
theorem exists_separated_cluster [Fintype ι]
    (w : ι → E) (a : ι) (hcard : 2 ≤ Fintype.card ι)
    {R : ℝ} (hR : 0 < R) (hfar : ∃ b : ι, R ≤ dist (w a) (w b)) :
    ∃ S : Set ι, a ∈ S ∧ S.Nonempty ∧ S ⊂ Set.univ ∧ Sᶜ.Nonempty ∧
      ∀ i ∈ S, ∀ j ∈ Sᶜ,
        R / ((Fintype.card ι - 1 : ℕ) : ℝ) ≤ dist (w i) (w j) := by
  classical
  let G := clusterThresholdGraph w (R / ((Fintype.card ι - 1 : ℕ) : ℝ))
  let S : Set ι := (G.connectedComponentMk a).supp
  have ha : a ∈ S := rfl
  obtain ⟨b, hb⟩ := hfar
  have hbnot : b ∉ S := by
    intro hbS
    change G.connectedComponentMk b = G.connectedComponentMk a at hbS
    have hreach : G.Reachable a b := SimpleGraph.ConnectedComponent.exact hbS.symm
    exact (not_lt_of_ge hb) (clusterThresholdGraph_reachable_dist_lt w hcard hR hreach)
  have hcomp : Sᶜ.Nonempty := ⟨b, hbnot⟩
  refine ⟨S, ha, ⟨a, ha⟩, hcomp.ssubset_univ, hcomp, ?_⟩
  intro i hi j hj
  by_contra hdist
  have hlt : dist (w i) (w j) < R / ((Fintype.card ι - 1 : ℕ) : ℝ) :=
    lt_of_not_ge hdist
  have hij : i ≠ j := by
    intro heq
    exact hj (heq ▸ hi)
  have hadj : G.Adj i j := ⟨hij, hlt⟩
  exact hj (((G.connectedComponentMk a).mem_supp_congr_adj hadj).mp hi)

end MetricSeparation

/-- The manuscript's exact unit-shell threshold `1 / (2 * (k - 1))`, with
index zero anchored at the Euclidean origin. The closed far-distance assumption
also covers the manuscript's strict unit-shell condition. -/
theorem exists_unitShell_separated_cluster {k : ℕ} (hk : 2 ≤ k)
    (w : Fin k → PlanarSpace) (hw0 : w ⟨0, by omega⟩ = 0)
    (hfar : ∃ j : Fin k, (1 / 2 : ℝ) ≤ ‖w j‖) :
    ∃ S : Set (Fin k), (⟨0, by omega⟩ : Fin k) ∈ S ∧ S.Nonempty ∧
      S ⊂ Set.univ ∧ Sᶜ.Nonempty ∧
      ∀ i ∈ S, ∀ j ∈ Sᶜ, (1 : ℝ) / (2 * ((k : ℝ) - 1)) ≤ dist (w i) (w j) := by
  let a : Fin k := ⟨0, by omega⟩
  have hfar' : ∃ j : Fin k, (1 / 2 : ℝ) ≤ dist (w a) (w j) := by
    obtain ⟨j, hj⟩ := hfar
    refine ⟨j, ?_⟩
    have ha : w a = 0 := hw0
    simpa only [ha, dist_zero_left] using hj
  have hcard : 2 ≤ Fintype.card (Fin k) := by simpa only [Fintype.card_fin] using hk
  obtain ⟨S, ha, hne, hproper, hcomp, hsep⟩ :=
    exists_separated_cluster w a hcard (by norm_num : (0 : ℝ) < 1 / 2) hfar'
  refine ⟨S, ha, hne, hproper, hcomp, ?_⟩
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  simpa only [Fintype.card_fin, hcast, div_div] using hsep

end PeriodicAttractiveLogGas
