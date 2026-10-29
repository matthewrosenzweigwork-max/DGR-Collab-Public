import DGPS.Frontier.LIP032.T18
import DGPS.Frontier.LIP032.T22

/-!
# LIP032.26: Finite entropy of bounded positive densities

Task id and title: LIP032.26, "Finite entropy of bounded positive densities" (node LIP032,
contractibility of the minimizer set; leaf formalization, pure density task, no positive-rate
hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_26_finite_entropy_bounded_positive_densities` : for a continuous
  real density `f` on `𝕋^d` with `∫ f dm = 1` and `c ≤ f ≤ C` for some `0 < c`, the relative
  entropy `H(μ_f | m)` equals `ENNReal.ofReal (∫ f log f dm)`, is finite, and satisfies
  `0 ≤ ∫ f log f dm ≤ log C`.
* `DGPS.Frontier.LIP032.lip032_26_finite_entropy_bounded_positive_densities_interpolation` : the
  finiteness and the two real bounds for the interpolation density `f_{ν,s} = (1-s) p_ν + s q` of
  LIP032.22 (with `s = 1` giving `q`), with `c = exp(-2(M_V+M_W))` and `C = exp(2(M_V+M_W))`.

## R5 notes
* The relative entropy is the campaign's DEF005 `DGPS.relativeEntropy (μ_f) (haar d)` valued in
  `ℝ≥0∞`. Its finiteness and its value are stated together: the identity is written as
  `relativeEntropy … = ENNReal.ofReal (∫ f log f dm)`, and the separate `≠ ⊤` conjunct records the
  finiteness claim explicitly. The real integral is nonnegative, so this is the real identity
  `H(μ_f | m) = ∫ f log f dm` after `toReal`.
* The hypotheses are exactly the specification's: `f` continuous (this gives measurability and
  boundedness on the compact torus, so they are not separate hypotheses), `∫ f dm = 1` (mass one),
  and `c ≤ f x ≤ C` for all `x` with `0 < c`. The lower bound `0 < c` is the specification's
  `0 < c`; nonnegativity of `f` is derived from it, not assumed separately. No upper-bound hypothesis
  `C ≥ c` is listed: it follows from `c ≤ f x ≤ C` at any point.
* The mass-one hypothesis is used in the identity to kill the `(∫ f) log (∫ f)` term of
  `DGPS.homogeneousEntropy_eq_formula` and in the upper bound `∫ f log C = log C`.
* The specification's proof writes the entropy integrand as `z log z - z + 1`. The campaign's
  DEF005 unfolds to the same integrand (`DGPS.entropy_mass_one`); the formula with `∫ f log f` is
  obtained from `DGPS.homogeneousEntropy_eq_formula` (`∫ f log f - a log a` with `a = 1`). The
  `∫ f log f ≥ 0` clause uses `DGPS.self_mul_log_sub_add_one_nonneg`, i.e. the specification's
  "integrate `z log z - z + 1 ≥ 0`" route, not the LIB08 entropy-nonnegativity route.
* Integrability of `f` and of `f log f` is obtained from continuity on the compact torus through
  `integrable_continuous_LIP03218` (LIP032.18); `f log f` is continuous because `f ≠ 0`.
* The interpolation corollary is a specialization of the main statement via LIP032.22
  (`lip032_22_interpolation_bounded_density`). Its minimizer memberships `μ, ν ∈ S` are kept as
  binders named `_hμ`, `_hν` only to match LIP032.22 and are not used in the proof (the bounds hold
  for every probability measure). Its conclusion omits the equality with `ENNReal.ofReal` and
  states the finiteness and the two real bounds; the upper bound is written `2 * (M_V + M_W)`, which
  is `log (exp (2 * (M_V + M_W)))` by `Real.log_exp`.
* The specification's nonnegativity of `M_V, M_W` is not needed and is not assumed.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.26.** Finite entropy of bounded positive densities: for a continuous mass-one density
`f` with `c ≤ f ≤ C` and `0 < c`, `H(μ_f | m) = ∫ f log f dm`, which is finite and lies in
`[0, log C]`. -/
theorem lip032_26_finite_entropy_bounded_positive_densities {f : Torus d → ℝ}
    (hf : Continuous f) (h1 : ∫ x, f x ∂haar d = 1) {c C : ℝ} (hc : 0 < c)
    (hb : ∀ x, c ≤ f x ∧ f x ≤ C) :
    DGPS.relativeEntropy (densityMeasure_LIP03218 f) (haar d)
        = ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂haar d) ∧
      DGPS.relativeEntropy (densityMeasure_LIP03218 f) (haar d) ≠ ⊤ ∧
      0 ≤ ∫ x, f x * Real.log (f x) ∂haar d ∧
      ∫ x, f x * Real.log (f x) ∂haar d ≤ Real.log C := by
  have hpos : ∀ x, 0 < f x := fun x => hc.trans_le (hb x).1
  have hnn : ∀ x, 0 ≤ f x := fun x => (hpos x).le
  have hne : ∀ x, f x ≠ 0 := fun x => (hpos x).ne'
  have hcont : Continuous fun x => f x * Real.log (f x) := hf.mul (hf.log hne)
  have hint : Integrable f (haar d) := integrable_continuous_LIP03218 hf
  have hlog : Integrable (fun x => f x * Real.log (f x)) (haar d) :=
    integrable_continuous_LIP03218 hcont
  have hnn' : 0 ≤ᵐ[haar d] f := Filter.Eventually.of_forall fun x => hnn x
  have hmeas : AEMeasurable f (haar d) := hf.measurable.aemeasurable
  have hH : DGPS.relativeEntropy (densityMeasure_LIP03218 f) (haar d)
      = ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂haar d) := by
    rw [densityMeasure_LIP03218, DGPS.relativeEntropy_withDensity hnn' hmeas,
      DGPS.homogeneousEntropy_eq_formula hnn' hint hlog, h1, Real.log_one, mul_zero, sub_zero]
  have hsplit : ∫ x, (f x * Real.log (f x) - f x + 1) ∂haar d
      = ∫ x, f x * Real.log (f x) ∂haar d := by
    have hA : Integrable (fun x => f x * Real.log (f x) - f x) (haar d) := hlog.sub hint
    rw [integral_add hA (integrable_const 1), integral_sub hlog hint, h1, integral_const]
    simp
  have hlow : 0 ≤ ∫ x, f x * Real.log (f x) ∂haar d := by
    rw [← hsplit]
    exact integral_nonneg fun x => DGPS.self_mul_log_sub_add_one_nonneg (hnn x)
  have hup : ∫ x, f x * Real.log (f x) ∂haar d ≤ Real.log C := by
    have hle : ∀ x, f x * Real.log (f x) ≤ f x * Real.log C := fun x =>
      mul_le_mul_of_nonneg_left (Real.log_le_log (hpos x) (hb x).2) (hnn x)
    calc ∫ x, f x * Real.log (f x) ∂haar d ≤ ∫ x, f x * Real.log C ∂haar d :=
          integral_mono hlog (hint.mul_const _) hle
      _ = Real.log C := by rw [integral_mul_const, h1, one_mul]
  refine ⟨hH, ?_, hlow, hup⟩
  rw [hH]
  exact ENNReal.ofReal_ne_top

/-- **LIP032.26, interpolation case.** For the interpolation density `f_{ν,s} = (1-s) p_ν + s q`
of LIP032.22 (with `s ∈ [0,1]`, and `s = 1` giving `q`), the relative entropy is finite and
`0 ≤ ∫ f log f dm ≤ 2 (M_V + M_W)`. -/
theorem lip032_26_finite_entropy_bounded_positive_densities_interpolation
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    DGPS.relativeEntropy (densityMeasure_LIP03218 (interpolDensity_LIP03222 A μ ν s)) (haar d)
        ≠ ⊤ ∧
      0 ≤ ∫ x, interpolDensity_LIP03222 A μ ν s x *
        Real.log (interpolDensity_LIP03222 A μ ν s x) ∂haar d ∧
      ∫ x, interpolDensity_LIP03222 A μ ν s x *
        Real.log (interpolDensity_LIP03222 A μ ν s x) ∂haar d ≤ 2 * (M_V + M_W) := by
  obtain ⟨hcont, hint, hbnd, -⟩ :=
    lip032_22_interpolation_bounded_density A M_V M_W hV hW μ _hμ ν _hν s hs0 hs1
  have hc : 0 < Real.exp (-(2 * (M_V + M_W))) := Real.exp_pos _
  have hC : Real.log (Real.exp (2 * (M_V + M_W))) = 2 * (M_V + M_W) := Real.log_exp _
  obtain ⟨-, hne, hlow, hup⟩ :=
    lip032_26_finite_entropy_bounded_positive_densities hcont hint hc hbnd
  exact ⟨hne, hlow, hup.trans_eq hC⟩

end DGPS.Frontier.LIP032
