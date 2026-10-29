import DGPS.Topology.LocalHomology
import Mathlib.Algebra.Field.ZMod

open CategoryTheory CategoryTheory.Limits DGPS.Topology.LocalHomology

namespace DGPS.Topology

/-- The canonical mod two local class at `x`: the nonzero element of `H_n(X, X ∖ {x}; F2)` when
one exists (it is unique when the group is one-dimensional), and `0` otherwise. -/
noncomputable def canonicalLocalClass (n : ℕ) (X : TopCat.{0}) (x : X) :
    (relativeHomology n).obj (TopPair.ofSet X {x}ᶜ) := by
  classical
  exact if h : ∃ c : (relativeHomology n).obj (TopPair.ofSet X {x}ᶜ), c ≠ 0 then h.choose else 0

private theorem top007_unique_nonzero_aux {V : Type} [AddCommGroup V] [Module F2 V]
    (h : Module.rank F2 V = 1) : ∃ c : V, c ≠ 0 ∧ ∀ d : V, d ≠ 0 → d = c := by
  have : Module.Free F2 V := Module.Free.of_divisionRing F2 V
  obtain ⟨v, hv0, hv⟩ := rank_eq_one_iff.1 h
  refine ⟨v, hv0, fun d hd => ?_⟩
  obtain ⟨a, rfl⟩ := hv d
  have ha : a ≠ 0 := fun h0 => hd (by rw [h0, zero_smul])
  have : a = 1 := by
    have key : ∀ b : F2, b ≠ 0 → b = 1 := by decide
    exact key a ha
  rw [this, one_smul]

private theorem top007_unique_nonzero {V : F2Mod} (h : Module.rank F2 V = 1) :
    ∃ c : V, c ≠ 0 ∧ ∀ d : V, d ≠ 0 → d = c :=
  top007_unique_nonzero_aux h

private theorem top007_canonical_spec {n : ℕ} {X : TopCat.{0}} {x : X}
    (h : Module.rank F2 ((relativeHomology n).obj (TopPair.ofSet X {x}ᶜ)) = 1) :
    canonicalLocalClass n X x ≠ 0 ∧ ∀ d, d ≠ 0 → d = canonicalLocalClass n X x := by
  classical
  obtain ⟨c, hc, hu⟩ := top007_unique_nonzero h
  have hex : ∃ c : (relativeHomology n).obj (TopPair.ofSet X {x}ᶜ), c ≠ 0 := ⟨c, hc⟩
  have e : canonicalLocalClass n X x = hex.choose := by
    unfold canonicalLocalClass; rw [dite_eq_left_of_eq_true (eq_true hex)]
  have h1 : canonicalLocalClass n X x ≠ 0 := by rw [e]; exact hex.choose_spec
  exact ⟨h1, fun d hd => (hu d hd).trans (hu _ h1).symm⟩

/-- **Canonical mod two local section.**  On an `n`-manifold without boundary (`n > 0`), each
local group `H_n(M, M ∖ {x}; F2)` has a unique nonzero element `canonicalLocalClass n M x`, and
every transition isomorphism induced by an open embedding of an `n`-manifold `Y` into `M`
carries the canonical class at `y` to the canonical class at `e y`.  No orientability is
assumed. -/
theorem canonical_mod_two_local_section {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n) :
    (∀ x : M, canonicalLocalClass n (TopCat.of M) x ≠ 0 ∧
      ∀ d : (relativeHomology n).obj (TopPair.ofSet (TopCat.of M) {x}ᶜ), d ≠ 0 →
        d = canonicalLocalClass n (TopCat.of M) x) ∧
    ∀ (Y : Type) [TopologicalSpace Y] [ChartedSpace H Y] (e : TopCat.of Y ⟶ TopCat.of M)
      (he : Topology.IsOpenEmbedding e.hom) (y : Y),
      ((relativeHomology n).map (pointPairMap e he.injective y)).hom
          (canonicalLocalClass n (TopCat.of Y) y) = canonicalLocalClass n (TopCat.of M) (e y) := by
  refine ⟨fun x => top007_canonical_spec (local_homology_in_a_chart I n hn hE x).1, ?_⟩
  intro Y _ _ e he y
  have hY := top007_canonical_spec (local_homology_in_a_chart I n hn hE y).1
  have hM := top007_canonical_spec (local_homology_in_a_chart I n hn hE (e y)).1
  have : T1Space M := I.t1Space M
  have hiso := isIso_pointPairMap (X := TopCat.of M) e he y n
  have hinj : Function.Injective ((relativeHomology n).map (pointPairMap e he.injective y)).hom :=
    (ConcreteCategory.injective_of_mono_of_preservesPullback _)
  refine hM.2 _ fun h0 => hY.1 (hinj ?_)
  simpa using h0

end DGPS.Topology
