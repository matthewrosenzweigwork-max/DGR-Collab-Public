import SharpSymmetricLSI.Infra.Topology.NotContractible
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Section 4.2 (lane s42; R15): invariance of dimension, and contractible compact manifolds

Manuscript, end of Section 4.2: "The dimension of the charts is locally constant, by invariance
of dimension, and hence has a common value `n` on `𝒮`. [...] If `n > 0`, its top homology [...]
contradicting contractibility. A connected zero-dimensional manifold is a point."

* `chart_dim_eq`: two charts at a point, onto open subsets of `ℝᵃ` and `ℝᵇ`, have `a = b`
  (local homology `H_{a}(M, M ∖ x; 𝔽₂)` is nonzero via the first chart and zero via the second
  if `a ≠ b`, `a, b ≥ 1`; a `0`-dimensional chart makes `{x}` open, which is impossible in `ℝᵇ`,
  `b ≥ 1`).
* `subsingleton_of_contractible_charts`: a compact Hausdorff contractible space, each point of
  which has a chart onto an open subset of some `ℝⁿ` (`n` depending on the point), is a point.
-/

universe u

open CategoryTheory Set Topology Module

namespace SharpLSI.Topology

/-- Nonzero local classes at corresponding points of a homeomorphism of open sets. -/
theorem exists_ne_zero_iff_of_homeomorph {X Y : TopCat.{u}} {U : Set X} {V : Set Y}
    (h : U ≃ₜ V) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hX1 : ∀ x : X, IsClosed ({x} : Set X)) (hY1 : ∀ y : Y, IsClosed ({y} : Set Y))
    {x : X} (hx : x ∈ U) :
    (∃ α : locH n ({x} : Set X), α ≠ 0) ↔
      ∃ β : locH n ({(h ⟨x, hx⟩ : Y)} : Set Y), β ≠ 0 := by
  have hpt : ∀ u : U, (u : X) ∈ ({x} : Set X) ↔ (h u : Y) ∈ ({(h ⟨x, hx⟩ : Y)} : Set Y) := by
    intro u
    simp only [mem_singleton_iff]
    constructor
    · rintro rfl; rfl
    · intro hu
      exact congrArg Subtype.val (h.injective (Subtype.ext hu))
  have hxU : ({x} : Set X) ⊆ U := singleton_subset_iff.2 hx
  have hyV : ({(h ⟨x, hx⟩ : Y)} : Set Y) ⊆ V := singleton_subset_iff.2 (h ⟨x, hx⟩).2
  have hE1 := bijective_excMap n hU (hX1 x) hxU
  have hH := bijective_homeoPairMap h n hpt
  have hE2 := bijective_excMap n hV (hY1 _) hyV
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨α', rfl⟩ := hE1.2 α
    refine ⟨excMap n V _ (TopPair.singularHomologyMap (homeoPairMap h hpt) R2 n α'),
      fun h0 => hα ?_⟩
    have h1 : TopPair.singularHomologyMap (homeoPairMap h hpt) R2 n α' = 0 :=
      hE2.1 (h0.trans (map_zero _).symm)
    have h2 : α' = 0 := hH.1 (h1.trans (map_zero _).symm)
    rw [h2, map_zero]
  · rintro ⟨β, hβ⟩
    obtain ⟨β', rfl⟩ := hE2.2 β
    obtain ⟨α', rfl⟩ := hH.2 β'
    refine ⟨excMap n U _ α', fun h0 => hβ ?_⟩
    have h2 : α' = 0 := hE1.1 (h0.trans (map_zero _).symm)
    rw [h2, map_zero, map_zero]

end SharpLSI.Topology

namespace SharpLSI

open SharpLSI.Topology

section dim

variable {M : Type} [TopologicalSpace M]

theorem euclidean_zero_eq (v w : EuclideanSpace ℝ (Fin 0)) : v = w := by
  ext i; exact i.elim0

/-- A `0`-dimensional chart at `x` makes `{x}` open. -/
theorem isOpen_singleton_of_chart_zero {x : M} {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    {V : Set (EuclideanSpace ℝ (Fin 0))} (h : U ≃ₜ V) : IsOpen ({x} : Set M) := by
  have hsV : Subsingleton V := ⟨fun v w => Subtype.ext (euclidean_zero_eq _ _)⟩
  have hsU : Subsingleton U := h.toEquiv.subsingleton
  have e : U = {x} := by
    ext y
    constructor
    · intro hy
      exact congrArg Subtype.val (hsU.elim ⟨y, hy⟩ ⟨x, hx⟩)
    · rintro rfl; exact hx
  rw [← e]; exact hU

/-- In a chart of positive dimension, `{x}` is not open. -/
theorem not_isOpen_singleton_of_chart {b : ℕ} (hb : 1 ≤ b) {x : M} {U : Set M} (hx : x ∈ U)
    {V : Set (EuclideanSpace ℝ (Fin b))} (hV : IsOpen V) (h : U ≃ₜ V)
    (hxo : IsOpen ({x} : Set M)) : False := by
  have e : (Subtype.val : U → M) ⁻¹' {x} = {⟨x, hx⟩} := by
    ext y; simp [Subtype.ext_iff]
  have h1 : IsOpen ({⟨x, hx⟩} : Set U) := by
    rw [← e]; exact hxo.preimage continuous_subtype_val
  have h2 : IsOpen (h '' {⟨x, hx⟩}) := h.isOpenMap _ h1
  have h3 := hV.isOpenMap_subtype_val _ h2
  rw [Set.image_singleton, Set.image_singleton] at h3
  haveI : Nontrivial (EuclideanSpace ℝ (Fin b)) := by
    refine ⟨⟨0, EuclideanSpace.single (⟨0, hb⟩ : Fin b) 1, fun h0 => ?_⟩⟩
    have := congrArg (fun v : EuclideanSpace ℝ (Fin b) => v (⟨0, hb⟩ : Fin b)) h0
    simp at this
  exact not_isOpen_singleton _ h3

/-- **Invariance of dimension** for charts at a point. -/
theorem chart_dim_eq [T1Space M] {x : M} {a b : ℕ}
    {U₁ : Set M} (hU₁ : IsOpen U₁) (hx₁ : x ∈ U₁) {V₁ : Set (EuclideanSpace ℝ (Fin a))}
    (hV₁ : IsOpen V₁) (h₁ : U₁ ≃ₜ V₁)
    {U₂ : Set M} (hU₂ : IsOpen U₂) (hx₂ : x ∈ U₂) {V₂ : Set (EuclideanSpace ℝ (Fin b))}
    (hV₂ : IsOpen V₂) (h₂ : U₂ ≃ₜ V₂) : a = b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact hb.symm
    · exact (not_isOpen_singleton_of_chart hb hx₂ hV₂ h₂
        (isOpen_singleton_of_chart_zero hU₁ hx₁ h₁)).elim
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    exact (not_isOpen_singleton_of_chart ha hx₁ hV₁ h₁
      (isOpen_singleton_of_chart_zero hU₂ hx₂ h₂)).elim
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  by_contra hab
  have hab' : a' ≠ b' := fun h => hab (by rw [h])
  -- charts into `Eu`
  let g₁ : U₁ ≃ₜ (toEu.{0} (a' + 1) '' V₁) := h₁.trans ((toEu.{0} (a' + 1)).image V₁)
  let g₂ : U₂ ≃ₜ (toEu.{0} (b' + 1) '' V₂) := h₂.trans ((toEu.{0} (b' + 1)).image V₂)
  have hW₁ : IsOpen (toEu.{0} (a' + 1) '' V₁) := (toEu (a' + 1)).isOpenMap _ hV₁
  have hW₂ : IsOpen (toEu.{0} (b' + 1) '' V₂) := (toEu (b' + 1)).isOpenMap _ hV₂
  have hfin₁ : finrank ℝ (Eu.{0} (a' + 1)) = a' + 1 := finrank_Eu _
  have hfin₂ : finrank ℝ (Eu.{0} (b' + 1)) = b' + 1 := finrank_Eu _
  have hM1 : ∀ y : TopCat.of M, IsClosed ({y} : Set (TopCat.of M)) := fun _ => isClosed_singleton
  obtain ⟨β, hβ⟩ := exists_locH_point_ne_zero hfin₁ (g₁ ⟨x, hx₁⟩ : Eu.{0} (a' + 1))
  have hα := (exists_ne_zero_iff_of_homeomorph (X := TopCat.of M)
    (Y := TopCat.of (Eu.{0} (a' + 1))) g₁ hU₁ hW₁ (a' + 1) hM1
    (fun _ => isClosed_singleton) hx₁).2 ⟨β, hβ⟩
  obtain ⟨γ, hγ⟩ := (exists_ne_zero_iff_of_homeomorph (X := TopCat.of M)
    (Y := TopCat.of (Eu.{0} (b' + 1))) g₂ hU₂ hW₂ (a' + 1) hM1
    (fun _ => isClosed_singleton) hx₂).1 hα
  have hZ := isZero_locH_point hfin₂ (g₂ ⟨x, hx₂⟩ : Eu.{0} (b' + 1)) hab'
  haveI := ModuleCat.subsingleton_of_isZero hZ
  exact hγ (Subsingleton.elim _ _)

/-- **A compact Hausdorff contractible space locally homeomorphic to Euclidean spaces (of
possibly varying dimension) is a point.** -/
theorem subsingleton_of_contractible_charts [T2Space M] [CompactSpace M] [ContractibleSpace M]
    (hM : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ n : ℕ,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ Nonempty (U ≃ₜ V)) :
    Subsingleton M := by
  rcases isEmpty_or_nonempty M with hM0 | hne
  · exact ⟨fun a => (IsEmpty.false a).elim⟩
  obtain ⟨x₀⟩ := hne
  choose U hU hxU n V hV hh using hM
  have hloc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨U x, hU x, hxU x, fun y hy => ?_⟩
    exact (chart_dim_eq (hU x) hy (hV x) (hh x).some (hU y) (hxU y) (hV y) (hh y).some).symm
  have hconst : ∀ y, n y = n x₀ := fun y => hloc.apply_eq_of_preconnectedSpace y x₀
  have key : ∀ y k, n y = k → ∃ V' : Set (EuclideanSpace ℝ (Fin k)), IsOpen V' ∧
      Nonempty (U y ≃ₜ V') := by
    rintro y k rfl; exact ⟨V y, hV y, hh y⟩
  rcases Nat.eq_zero_or_pos (n x₀) with h0 | hpos
  · -- zero-dimensional: every point is open
    have hopen : ∀ y : M, IsOpen ({y} : Set M) := fun y => by
      obtain ⟨V', -, ⟨g⟩⟩ := key y 0 ((hconst y).trans h0)
      exact isOpen_singleton_of_chart_zero (hU y) (hxU y) g
    refine ⟨fun a b => ?_⟩
    have hc : IsClopen ({a} : Set M) := ⟨isClosed_singleton, hopen a⟩
    rcases isClopen_iff.mp hc with he | he
    · have ha : a ∈ (∅ : Set M) := he ▸ mem_singleton a
      simp at ha
    · have hb : b ∈ ({a} : Set M) := he ▸ mem_univ b
      exact (mem_singleton_iff.mp hb).symm
  · exact (not_contractible_of_locallyEuclidean hpos (fun y => by
      obtain ⟨V', hV', hg⟩ := key y (n x₀) (hconst y)
      exact ⟨U y, hU y, hxU y, V', hV', hg⟩) ‹_›).elim

end dim

end SharpLSI
