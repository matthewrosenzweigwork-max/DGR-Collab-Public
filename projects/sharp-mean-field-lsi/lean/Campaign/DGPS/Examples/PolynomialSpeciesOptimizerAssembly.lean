import DGPS.Examples.PolynomialSpeciesFactorImplicitBranches
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! Candidate-only compactness and uniqueness assembly.
No compiler claim; origin exclusion and original-domain representation remain
separate obligations. This file does not assert the frozen T11 theorem. -/
noncomputable section
open Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029
namespace DGPS.Examples.PolynomialSpecies

/-- Uniform capture from a compact parameter bound and a sequential limit
classification. The latter is an explicit dependency, not an optimizer premise
silently added to the final theorem. -/
theorem compact_uniform_capture_of_limit
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V)
    (P : ℝ → X → Prop)
    (hlimit : ∀ (h : ℕ → ℝ) (x : ℕ → X) (x₀ : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, x n ∈ K) → (∀ n, P (h n) (x n)) →
      Tendsto x atTop (𝓝 x₀) → x₀ ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ x ∈ K, P h x → x ∈ V := by
  by_contra hno
  push_neg at hno
  have hchoose : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
      ∃ x ∈ K, P h x ∧ x ∉ V := by
    intro n
    exact hno (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hh hs x hx hP hnV using hchoose
  have hh0 : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hh n).le) (fun n => (hs n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨x₀, _hx₀, φ, hφ, hconv⟩ := hK.tendsto_subseq hx
  have hmem := hlimit (h ∘ φ) (x ∘ φ) x₀
    (fun n => hh (φ n)) (hh0.comp hφ.tendsto_atTop)
    (fun n => hx (φ n)) (fun n => hP (φ n)) hconv
  have hev := hconv.eventually (hV.mem_nhds hmem)
  obtain ⟨n, hn⟩ := hev.exists
  exact hnV (φ n) hn

section ActualGraph
variable {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)

include hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst

/-- Two actual critical sequences at the SAME parameter and approaching the
SAME coefficient minimum must eventually coincide. Arbitrary tilt accumulation
is allowed; no assertion that the physical scaled tilt tends to zero is used. -/
theorem polynomial_actual_factor_same_limit_unique
    (p : ℕ → PolynomialFactorParameters)
    (z w : ℕ → PolynomialFactorUnknowns) (σ₀ : ℝ) (j : Fin 2)
    (hp : Tendsto p atTop (𝓝 (0, σ₀)))
    (hz : Tendsto z atTop (𝓝 (polynomialQuarticCriticalBase j)))
    (hw : Tendsto w atTop (𝓝 (polynomialQuarticCriticalBase j)))
    (hcz : ∀ᶠ n in atTop, polynomialFactorCriticalSystem ψ (p n, z n) = 0)
    (hcw : ∀ᶠ n in atTop, polynomialFactorCriticalSystem ψ (p n, w n) = 0) :
    ∀ᶠ n in atTop, z n = w n := by
  obtain ⟨β, _hβ0, _hβC, _hβzero, huniq⟩ :=
    polynomial_actual_factor_implicit_branch_at_tilt
      hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst σ₀ j
  have hez := (hp.prodMk_nhds hz).eventually huniq
  have hew := (hp.prodMk_nhds hw).eventually huniq
  filter_upwards [hez, hew, hcz, hcw] with n hnz hnw hzn hwn
  exact ((hnz.mp hzn).symm).trans (hnw.mp hwn)

/-- A uniform pairwise-uniqueness neighborhood over any compact set of scaled
tilts. This does NOT claim that the local roots are optimizers. -/
theorem polynomial_actual_factor_uniform_local_unique
    (K : Set ℝ) (hK : IsCompact K) (j : Fin 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h σ : ℝ) (z w : PolynomialFactorUnknowns),
      |h| < δ → σ ∈ K →
      dist z (polynomialQuarticCriticalBase j) < δ →
      dist w (polynomialQuarticCriticalBase j) < δ →
      polynomialFactorCriticalSystem ψ ((h, σ), z) = 0 →
      polynomialFactorCriticalSystem ψ ((h, σ), w) = 0 → z = w := by
  by_contra hno
  push_neg at hno
  have hex : ∀ n : ℕ, ∃ (h σ : ℝ) (z w : PolynomialFactorUnknowns),
      |h| < 1 / ((n : ℝ) + 1) ∧ σ ∈ K ∧
      dist z (polynomialQuarticCriticalBase j) < 1 / ((n : ℝ) + 1) ∧
      dist w (polynomialQuarticCriticalBase j) < 1 / ((n : ℝ) + 1) ∧
      polynomialFactorCriticalSystem ψ ((h, σ), z) = 0 ∧
      polynomialFactorCriticalSystem ψ ((h, σ), w) = 0 ∧ z ≠ w := by
    intro n
    exact hno (1 / ((n : ℝ) + 1)) (by positivity)
  choose h σ z w hh hσ hz hw hcz hcw hne using hex
  have hh0 : Tendsto h atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by simpa only [dist_zero_right, Real.norm_eq_abs] using (hh n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hz0 : Tendsto z atTop (𝓝 (polynomialQuarticCriticalBase j)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hz n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw0 : Tendsto w atTop (𝓝 (polynomialQuarticCriticalBase j)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hw n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨σ₀, _hσ₀, φ, hφ, hσconv⟩ := hK.tendsto_subseq hσ
  have hp : Tendsto (fun n => (h (φ n), σ (φ n))) atTop (𝓝 (0, σ₀)) :=
    (hh0.comp hφ.tendsto_atTop).prodMk_nhds hσconv
  have he := polynomial_actual_factor_same_limit_unique
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
    (fun n => (h (φ n), σ (φ n))) (z ∘ φ) (w ∘ φ) σ₀ j hp
    (hz0.comp hφ.tendsto_atTop) (hw0.comp hφ.tendsto_atTop)
    (Filter.Eventually.of_forall fun n => hcz (φ n))
    (Filter.Eventually.of_forall fun n => hcw (φ n))
  obtain ⟨n, hn⟩ := he.exists
  exact hne (φ n) hn
end ActualGraph

/-- Pure quotient-law assembly: attainment, an involution producing the
opposite class, and uniqueness WITHIN each sign class imply exactly two laws.
These hypotheses must be discharged for actual optimizers before use in T11. -/
theorem exactly_two_laws_of_sign_classes
    {D L : Type*} (P : D → Prop) (law : D → L) (R : D → D)
    (side : D → Bool)
    (hex : ∃ d, P d)
    (hR : ∀ d, P d → P (R d))
    (hflip : ∀ d, P d → side (R d) = !side d)
    (hsame : ∀ d e, P d → P e → side d = side e → law d = law e)
    (hsep : ∀ d e, P d → P e → law d = law e → side d = side e) :
    ∃ d e, P d ∧ P e ∧ law d ≠ law e ∧ e = R d ∧
      ∀ f, P f → law f = law d ∨ law f = law e := by
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, R d, hd, hR d hd, ?_, rfl, ?_⟩
  · intro heq
    have hs := hsep d (R d) hd (hR d hd) heq
    rw [hflip d hd] at hs
    cases side d <;> simp_all
  · intro f hf
    by_cases hs : side f = side d
    · exact Or.inl (hsame f d hf hd hs)
    · apply Or.inr
      apply hsame f (R d) hf (hR d hd)
      rw [hflip d hd]
      cases hfd : side f <;> cases hdd : side d <;> simp_all
end DGPS.Examples.PolynomialSpecies
