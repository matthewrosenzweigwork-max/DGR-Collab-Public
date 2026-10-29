import DGPS.Frontier.EX012.T05
import DGPS.Frontier.EX012.T06

/-!
# EX012.07: Analytic implicit function

Task id: EX012.07 (node EX012, one-site complementary range equation).
Title: Analytic implicit function.

Provides:
* `DGPS.Frontier.EX012.ex012_07_analytic_implicit_function`: the main statement. For
  `α` with `[HolderExponent α]`, `W = PH.orthSub α 2`, `Y = PH.orthSub α 0` and
  `F = rangeMap_EX01229 α : (ℝ × ℝ × ℝ) × W → Y` (the polynomial map of EX012.05), there are an
  open set `U ⊆ ℝ³` and an open set `V ⊆ W`, both containing `0`, and a total map
  `w : ℝ³ → W` such that `w` is analytic at every point of `U` (`AnalyticOnNhd ℝ w U`),
  `w` maps `U` into `V` (`Set.MapsTo w U V`), `w 0 = 0`, and for all `p ∈ U` and `z ∈ V`,
  `F (p, z) = 0 ↔ z = w p`.

Helpers (all suffixed `_EX01207`):
* `completeSpace_orthSub_EX01207`: the closed subspace `PH.orthSub α k` of the Banach space
  `PH α k` is complete.
* `analyticImplicit_general_EX01207`: the implicit-function statement for an arbitrary map
  `f : E₁ × E₂ → F` between real Banach spaces which is `C^ω` at `0`, vanishes at `0`, and has
  invertible partial derivative `fderiv ℝ f 0 ∘L inr` in the unknown variable. It converts the
  two eventual conclusions of `ContDiffAt.implicitFunction` (solution and uniqueness) and the
  local power series of the implicit function into a single pair of open neighborhoods.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis is
  added beyond the specification, and no part of the statement is weakened.
* `F` is the literal map `rangeMap_EX01229 α` of EX012.05 (and EX012.29), with the domain
  `(ℝ × ℝ × ℝ) × PH.orthSub α 2`, the parameter `p = (a, b, τ)` being the first factor.
  "`ℝ³`" is read as `ℝ × ℝ × ℝ`, and `0 ∈ ℝ³` as `(0, 0, 0)`.
* "Open neighborhoods `U ⊂ ℝ³` and `V ⊂ W` of zero" is read as `IsOpen U ∧ (0 : ℝ × ℝ × ℝ) ∈ U`
  and `IsOpen V ∧ (0 : W) ∈ V`, with `V` open for the norm topology of the subspace `W`.
* "A total map `w : ℝ³ → W`, analytic at every point of `U`" is read as an existentially
  quantified function `w : ℝ × ℝ × ℝ → W` (defined on all of `ℝ³`) with `AnalyticOnNhd ℝ w U`,
  that is, `AnalyticAt ℝ w p` for every `p ∈ U`. Analyticity is real analyticity in the sense of
  Mathlib (a convergent power series expansion at each point).
* "`w(U) ⊂ V`" is read as `Set.MapsTo w U V`; "`w(0) = 0`" as `w 0 = 0`.
* The equivalence `F (p, z) = 0 ↔ z = w p` holds for every `p ∈ U` and every `z ∈ V`, as in the
  specification (uniqueness of the zero of `F (p, ·)` inside `V`, and existence of the zero
  `w p ∈ V`).
* Proof route as in the specification: completeness of `W` and `Y` comes from the closedness of
  `PH.orthSub α k` in the complete space `PH α k` (FOU017), which is the content of
  `completeSpace_orthSub_EX01207`; `F` is real analytic with `F 0 = 0` and has derivative `L`
  in the unknown variable at `0` (EX012.05); the partial derivative is the continuous linear
  equivalence `ellEquiv` (FOU018, as identified in EX012.06), hence invertible; Mathlib's
  `ContDiffAt.implicitFunction` is applied with the index `ω`. The eventual solution/uniqueness
  statement in a neighborhood of `(0, 0)` is shrunk to a product `U₁ ×ˢ V₁`; the parameter factor
  is then shrunk further, through continuity of the implicit function at `0`, so that its values
  lie in `interior V₁`, and through the eventual analyticity of the implicit function near `0`
  (from its local power series at `0`), so that it is analytic on a whole open set.
* The identification of the derivative with `ellEquiv` is taken from EX012.05, part (iii). EX012.06
  (the explicit inverse of `ellEquiv` on second harmonics) is imported as a prerequisite of the
  task graph; the proof here needs only that the derivative is a continuous linear equivalence, so
  no other content of EX012.06 is used.
* The implicit function `w` is Mathlib's `ContDiffAt.implicitFunction`, but the statement is
  existential: no uniqueness of `w` outside `U` is claimed (the specification states none), and
  the theorem does not assert any quantitative bound on `U` or `V`.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic
open scoped Topology ContDiff

namespace DGPS.Frontier.EX012

section Helpers

/-- The closed subspace `PH.orthSub α k` of the Banach space `PH α k` is complete. -/
theorem completeSpace_orthSub_EX01207 (α : ℝ) [HolderExponent α] (k : ℕ) :
    CompleteSpace (PH.orthSub α k) :=
  (PH.isClosed_orthSub (α := α) k).completeSpace_coe

/-- Analytic implicit function theorem in the neighborhood form of EX012.07, for a map
`f : E₁ × E₂ → F` of real Banach spaces which is `C^ω` at `0`, vanishes at `0`, and has
invertible partial derivative in the unknown variable at `0`. -/
theorem analyticImplicit_general_EX01207 {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E₁ × E₂ → F} (hf : ContDiffAt ℝ ω f 0) (h0 : f 0 = 0)
    (hinv : (fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible) :
    ∃ (U : Set E₁) (V : Set E₂) (w : E₁ → E₂), IsOpen U ∧ IsOpen V ∧ (0 : E₁) ∈ U ∧
      (0 : E₂) ∈ V ∧ AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
      ∀ p ∈ U, ∀ z ∈ V, f (p, z) = 0 ↔ z = w p := by
  have pn : ((ω : ℕ∞ω)) ≠ 0 := by simp
  have hψ0 : hf.implicitFunction pn hinv 0 = 0 := hf.implicitFunction_apply_self pn hinv
  have hev := hf.eventually_apply_eq_iff_implicitFunction pn hinv
  have hcd := hf.contDiffAt_implicitFunction pn hinv
  set ψ := hf.implicitFunction pn hinv
  have hev' : {v : E₁ × E₂ | f v = f 0 ↔ ψ v.1 = v.2} ∈ 𝓝 ((0 : E₁), (0 : E₂)) := hev
  obtain ⟨U₁, hU₁, V₁, hV₁, hsub⟩ := mem_nhds_prod_iff.1 hev'
  have hVint : interior V₁ ∈ 𝓝 (0 : E₂) := by
    rw [interior_mem_nhds]
    exact hV₁
  have hcont : ContinuousAt ψ (0 : E₁) := hcd.continuousAt
  have hpre : ψ ⁻¹' interior V₁ ∈ 𝓝 (0 : E₁) :=
    hcont.preimage_mem_nhds (by rw [hψ0]; exact hVint)
  have han : ∀ᶠ p in 𝓝 (0 : E₁), AnalyticAt ℝ ψ p := hcd.analyticAt.eventually_analyticAt
  have hT : {p : E₁ | p ∈ U₁ ∧ ψ p ∈ interior V₁ ∧ AnalyticAt ℝ ψ p} ∈ 𝓝 (0 : E₁) :=
    Filter.inter_mem hU₁ (Filter.inter_mem hpre han)
  refine ⟨interior {p : E₁ | p ∈ U₁ ∧ ψ p ∈ interior V₁ ∧ AnalyticAt ℝ ψ p}, interior V₁, ψ,
    isOpen_interior, isOpen_interior, mem_interior_iff_mem_nhds.2 hT,
    mem_interior_iff_mem_nhds.2 hV₁, fun p hp => (interior_subset hp).2.2,
    fun p hp => (interior_subset hp).2.1, hψ0, ?_⟩
  intro p hp z hz
  have h : f (p, z) = f 0 ↔ ψ p = z :=
    hsub (Set.mk_mem_prod (interior_subset hp).1 (interior_subset hz))
  rw [h0] at h
  rw [h]
  exact eq_comm

end Helpers

section Main

variable (α : ℝ) [HolderExponent α]

/-- **EX012.07.**  There are open neighborhoods `U ⊆ ℝ³` and `V ⊆ W = PH.orthSub α 2` of zero and a
total map `w : ℝ³ → W`, analytic at every point of `U`, with `w(U) ⊆ V` and `w 0 = 0`, such that
for all `p ∈ U` and `z ∈ V`, `F (p, z) = 0 ↔ z = w p`, where `F = rangeMap_EX01229 α`. -/
theorem ex012_07_analytic_implicit_function :
    ∃ (U : Set (ℝ × ℝ × ℝ)) (V : Set (PH.orthSub α 2)) (w : ℝ × ℝ × ℝ → PH.orthSub α 2),
      IsOpen U ∧ IsOpen V ∧ (0 : ℝ × ℝ × ℝ) ∈ U ∧ (0 : PH.orthSub α 2) ∈ V ∧
      AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
      ∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p := by
  obtain ⟨hAn, h0, hpart, -, -⟩ := ex012_05_polynomial_map_derivative α
  have : CompleteSpace (PH.orthSub α 2) := completeSpace_orthSub_EX01207 α 2
  have : CompleteSpace (PH.orthSub α 0) := completeSpace_orthSub_EX01207 α 0
  refine analyticImplicit_general_EX01207 (f := rangeMap_EX01229 α)
    (hAn 0 (Set.mem_univ _)).contDiffAt h0 ?_
  rw [hpart]
  exact ContinuousLinearMap.isInvertible_equiv

end Main

end DGPS.Frontier.EX012
