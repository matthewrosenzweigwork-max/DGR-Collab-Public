import DGPS.Frontier.LIP032.T22
import DGPS.Lipschitz.MeanFieldLocalFlow

/-!
# LIP032.23: Canonical L2 class and representative transport

Task id and title: LIP032.23, "Canonical L2 class and representative transport" (node LIP032,
contractibility of the minimizer set; pure density task, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.l2Class_LIP03223` : the `L^2(m; ℝ)` class `[f]` of a real function `f`
  (`MemLp.toLp f` when `f ∈ L²(m)`, and `0` otherwise).
* `DGPS.Frontier.LIP032.l2Class_coe_ae_LIP03223` : if `f ∈ L²(m)` then the coercion of `[f]`
  agrees with `f` a.e.
* `DGPS.Frontier.LIP032.l2Class_eq_of_ae_eq_LIP03223` : a.e.-equal functions have equal classes.
* `DGPS.Frontier.LIP032.memLp_two_of_continuous_LIP03223` : a continuous function on the torus is
  in `L²(m)`.
* `DGPS.Frontier.LIP032.lip032_23_canonical_l2_class_representative_transport` : for the
  interpolation density `f_{ν,s}`, the class `[f_{ν,s}]` has a coercion equal a.e. to `f_{ν,s}`,
  which is a.e. nonnegative, has integral one and is a.e. bounded by `C = e^{2(M_V+M_W)}`;
  moreover a.e.-equal continuous input densities have equal classes.

## R5 notes
* Hypotheses of the main statement are exactly those of LIP032.22: `A : InteractionData d`; reals
  `M_V`, `M_W` with `|A.V| ≤ M_V`, `|A.W| ≤ M_W` (no nonnegativity assumed, none needed); free-energy
  minimizers `μ`, `ν` (memberships in `S`, unused in the proof, binders `_hμ`, `_hν`); `s ∈ [0,1]`.
  No hypothesis was added.
* The mathematical class `L²(m; ℝ)` is `Lp ℝ 2 (haar d)`, which is also the campaign alias `L2s d`
  (`DGPS.Lipschitz.L2s`, an `abbrev`); the identification with the alias that Task 29 must record is
  therefore definitional here, and the class is typed as `L2s d`.
* Design choice: `l2Class_LIP03223 f` is total in `f` (it uses `dite` on `MemLp f 2 (haar d)`), so
  that the statement does not need a membership proof as an argument. For `f` in `L²` it is the
  `MemLp.toLp` class; the junk value `0` is never used by the statements below.
* The specification's "a.e.-equal continuous input densities yield equal classes" is stated in the
  main theorem as: for every continuous `g` with `g =ᵐ f_{ν,s}`, `[g] = [f_{ν,s}]`. The helper
  `l2Class_eq_of_ae_eq_LIP03223` proves the more general fact for arbitrary a.e.-equal functions
  (no continuity needed).
* "Representative is a.e. nonnegative / integral one / `|[f]| ≤ C` a.e." are stated for the coercion
  `⇑[f]` of the class, transported along the a.e. equality `⇑[f] =ᵐ f` (so the integral is that of
  the chosen representative, equal to the integral of `f`, which is one by LIP032.22). Also
  `f_{ν,s} ∈ L²(m)` is stated as a conjunct. `C` is written inline as `Real.exp (2 * (M_V + M_W))`.
* The specification's `∫ |f|² ≤ C² m(X)` is not stated separately; membership in `L²` is obtained
  from continuity on the compact torus (`MemLp` from `memLp_top`, finite measure), which is the same
  fact LIB07 supplies.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The `L²(m; ℝ)` class of a real function `f` on the torus (`0` if `f ∉ L²(m)`). -/
noncomputable def l2Class_LIP03223 (f : Torus d → ℝ) : DGPS.Lipschitz.L2s d := by
  classical
  exact if h : MemLp f 2 (haar d) then h.toLp f else 0

/-- A continuous function on the torus lies in `L²(m)`. -/
theorem memLp_two_of_continuous_LIP03223 {f : Torus d → ℝ} (hf : Continuous f) :
    MemLp f 2 (haar d) :=
  (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f) (p := 2) (μ := haar d))

/-- For `f ∈ L²(m)`, the coercion of the class `[f]` agrees with `f` a.e. -/
theorem l2Class_coe_ae_LIP03223 {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    (⇑(l2Class_LIP03223 f) : Torus d → ℝ) =ᵐ[haar d] f := by
  have : l2Class_LIP03223 f = hf.toLp f := by simp [l2Class_LIP03223, hf]
  rw [this]
  exact MemLp.coeFn_toLp hf

/-- A.e.-equal functions have equal classes. -/
theorem l2Class_eq_of_ae_eq_LIP03223 {f g : Torus d → ℝ} (h : f =ᵐ[haar d] g) :
    l2Class_LIP03223 f = l2Class_LIP03223 g := by
  by_cases hf : MemLp f 2 (haar d)
  · have hg : MemLp g 2 (haar d) := hf.ae_eq h
    have e1 : l2Class_LIP03223 f = hf.toLp f := by simp [l2Class_LIP03223, hf]
    have e2 : l2Class_LIP03223 g = hg.toLp g := by simp [l2Class_LIP03223, hg]
    rw [e1, e2]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp g 2 (haar d) := fun hg => hf (hg.ae_eq h.symm)
    simp [l2Class_LIP03223, hf, hg]

/-- **LIP032.23.** The interpolation density `f_{ν,s}` defines an `L²(m)` class `[f_{ν,s}]` whose
coercion agrees with `f_{ν,s}` a.e.; the representative is a.e. nonnegative, has integral one and
is a.e. bounded by `C = e^{2(M_V+M_W)}`; a.e.-equal continuous inputs yield equal classes. -/
theorem lip032_23_canonical_l2_class_representative_transport
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    MemLp (interpolDensity_LIP03222 A μ ν s) 2 (haar d) ∧
    (⇑(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Torus d → ℝ)
      =ᵐ[haar d] interpolDensity_LIP03222 A μ ν s ∧
    (0 ≤ᵐ[haar d] (⇑(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Torus d → ℝ)) ∧
    ∫ x, (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x ∂haar d = 1 ∧
    (∀ᵐ x ∂haar d, |(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x| ≤
      Real.exp (2 * (M_V + M_W))) ∧
    (∀ g : Torus d → ℝ, Continuous g → g =ᵐ[haar d] interpolDensity_LIP03222 A μ ν s →
      l2Class_LIP03223 g = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) := by
  obtain ⟨hcont, hint, hbnd, -⟩ :=
    lip032_22_interpolation_bounded_density A M_V M_W hV hW μ _hμ ν _hν s hs0 hs1
  have hmem : MemLp (interpolDensity_LIP03222 A μ ν s) 2 (haar d) :=
    memLp_two_of_continuous_LIP03223 hcont
  have hae := l2Class_coe_ae_LIP03223 hmem
  have h0 : ∀ x, 0 ≤ interpolDensity_LIP03222 A μ ν s x := fun x =>
    (Real.exp_pos _).le.trans (hbnd x).1
  refine ⟨hmem, hae, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    rw [hx]
    exact h0 x
  · rw [integral_congr_ae hae]
    exact hint
  · filter_upwards [hae] with x hx
    rw [hx, abs_of_nonneg (h0 x)]
    exact (hbnd x).2
  · intro g _ hg
    exact l2Class_eq_of_ae_eq_LIP03223 hg

end DGPS.Frontier.LIP032
