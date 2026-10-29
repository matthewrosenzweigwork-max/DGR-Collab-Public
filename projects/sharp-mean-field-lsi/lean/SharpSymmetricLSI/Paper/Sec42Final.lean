import SharpSymmetricLSI.Paper.Sec42Flow2
import SharpSymmetricLSI.Paper.Sec42Dim
import SharpSymmetricLSI.Paper.Sec42Spectral2
import SharpSymmetricLSI.Statements.R14_Local_Structure

/-!
# Section 4.2 (lane s42; R15): `𝒮` is a point, `ker(I+T) = 0`, (4.13)

Manuscript, end of Section 4.2: `𝒮` is compact (closed in `𝒫(𝕋^d)`, by lower semicontinuity of
`F`), locally homeomorphic to open subsets of Euclidean spaces (R14), and contractible
(Paper/Sec42Flow2), hence a point (Paper/Sec42Dim). The chart at `μ` then has dimension
`n = dim ker(I+T) = 0`, and (4.13) follows (Paper/Sec42Spectral2).
-/

open MeasureTheory Filter Topology Set

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem isClosed_minSet (hyp : Hyp V W KV KW) :
    IsClosed {ν : ProbabilityMeasure (Torus d) | IsMinimizer V W ν} := by
  have hlsc := lowerSemicontinuous_freeEnergy hyp (V := V) (W := W)
  have e : {ν : ProbabilityMeasure (Torus d) | IsMinimizer V W ν} =
      (fun ν : ProbabilityMeasure (Torus d) => freeEnergy V W ν) ⁻¹' Iic (Fstar V W) := by
    ext ν
    simp only [mem_setOf_eq, mem_preimage, mem_Iic, IsMinimizer]
    constructor
    · intro h; exact h.le
    · intro h
      exact le_antisymm h (iInf_le (fun ρ' : ProbabilityMeasure (Torus d) => freeEnergy V W ρ') ν)
  rw [e]
  exact hlsc.isClosed_preimage _

theorem compactSpace_minSet (hyp : Hyp V W KV KW) : CompactSpace (MinSet V W) :=
  isCompact_iff_compactSpace.mp (isClosed_minSet hyp).isCompact

/-- R14's chart, as a chart of the subspace `𝒮`. -/
theorem minSet_chart (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) (ν : MinSet V W)
    {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis W (ν.1 : Measure (Torus d)) φ) :
    ∃ U : Set (MinSet V W), IsOpen U ∧ ν ∈ U ∧
      ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ Nonempty (U ≃ₜ O) := by
  obtain ⟨U, hUo, hνU, O, hO, ⟨e⟩⟩ := minSet_topological_chart hd hyp hr ν.2 hφ
  refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hνU, O, hO, ⟨?_⟩⟩
  refine Homeomorph.trans ?_ e
  exact
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- An open subset of `ℝⁿ`, `n ≥ 1`, with at most one point is empty. -/
theorem eq_empty_of_subsingleton_open {n : ℕ} (hn : 1 ≤ n) {O : Set (EuclideanSpace ℝ (Fin n))}
    (hO : IsOpen O) (hs : O.Subsingleton) : O = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
  have e : O = {x} := hs.eq_singleton_of_mem hx
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1, fun h0 => ?_⟩⟩
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v (⟨0, hn⟩ : Fin n)) h0
    simp at this
  rw [e] at hO
  exact not_isOpen_singleton _ hO

/-- **R15 `minSet_singleton`.** -/
theorem minSet_singleton_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ContractibleSpace {ν : ProbabilityMeasure (Torus d) // IsMinimizer V W ν} ∧
    (∀ ν, IsMinimizer V W ν → ν = μ) ∧
    (∀ h, InKerIT W μ h → h =ᵐ[(μ : Measure (Torus d))] 0) ∧
    ∃ σ : ℝ, 0 < σ ∧ ∀ h, MemL20 μ h →
      σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h := by
  have hC : ContractibleSpace (MinSet V W) := contractible_minSet hd hyp hr μ hμ
  haveI := compactSpace_minSet hyp
  -- `𝒮` is a point
  have hsub : Subsingleton (MinSet V W) := by
    refine subsingleton_of_contractible_charts fun ν => ?_
    obtain ⟨-, -, -, -, n, φ, hφ⟩ := minSet_local_structure hd hyp ν.2
    obtain ⟨U, hU, hνU, O, hO, he⟩ := minSet_chart hd hyp hr ν hφ
    exact ⟨U, hU, hνU, n, O, hO, he⟩
  have huniq : ∀ ν, IsMinimizer V W ν → ν = μ := fun ν hν =>
    congrArg Subtype.val (hsub.elim ⟨ν, hν⟩ ⟨μ, hμ⟩)
  -- `ker(I+T) = 0`
  obtain ⟨-, -, -, -, n, φ, hφ⟩ := minSet_local_structure hd hyp hμ
  have hn : n = 0 := by
    by_contra hn0
    obtain ⟨U, -, hμU, O, hO, ⟨e⟩⟩ := minSet_chart hd hyp hr ⟨μ, hμ⟩ hφ
    have hOs : O.Subsingleton := fun a ha b hb => by
      have h1 : e.symm ⟨a, ha⟩ = e.symm ⟨b, hb⟩ := Subtype.ext (hsub.elim _ _)
      exact congrArg Subtype.val (e.symm.injective h1)
    have hOe := eq_empty_of_subsingleton_open (Nat.one_le_iff_ne_zero.mpr hn0) hO hOs
    exact (Set.nonempty_of_mem (e ⟨⟨μ, hμ⟩, hμU⟩).2).ne_empty hOe
  subst hn
  have hker : ∀ h, InKerIT W μ h → h =ᵐ[(μ : Measure (Torus d))] 0 := fun h hh => by
    obtain ⟨a, ha⟩ := hφ.2.2 h hh
    filter_upwards [ha] with x hx
    rw [hx]; simp
  refine ⟨hC, huniq, hker, ?_⟩
  exact secondVar_coercive_of_ker hyp hμ fun h hh => hker h hh

end SharpLSI
