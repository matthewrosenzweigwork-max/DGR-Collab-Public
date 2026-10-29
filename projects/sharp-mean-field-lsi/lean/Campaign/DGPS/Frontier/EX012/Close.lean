import DGPS.Frontier.EX012.T02
import DGPS.Frontier.EX012.T04
import DGPS.Frontier.EX012.T11
import DGPS.Frontier.EX012.T12

/-!
# EX012.CLOSE: One-site complementary range equation

Task id: EX012.CLOSE (node EX012, closing unit).
Title: Closing unit: declare and prove `DGPS.Examples.one_site_complementary_range_equation`.

On mean-zero periodic `C^{2,α}` logarithms the ground Euler equation is
`R(v, τ) = D² v + v + (1/2)[(D v)² - Haar((D v)²)] + (τ/4) cos(2θ) = 0`, `τ = h²`. Writing
`v = a c₁ + b s₁ + w` with `w` orthogonal to the constants and first harmonics, the `Q` equation
(`rangeMap`) has exactly one small analytic solution `w(a, b, τ)`; its leading terms are
`((τ - a² + b²)/12) c₂ - (ab/6) s₂`, with weighted remainder of order at least three under the
weights `(1, 1, 2)`.

## Provides

* `DGPS.Examples.one_site_complementary_range_equation`: for `[HolderExponent α]` there are open
  neighborhoods `U` of `0` in `ℝ³` and `V` of `0` in `W = PH.orthSub α 2`, and a map
  `w : ℝ³ → W`, analytic on `U`, with `w 0 = 0`, `w U ⊆ V` and
  `rangeMap α (p, z) = 0 ↔ z = w p` for `p ∈ U`, `z ∈ V` (one small analytic solution), such that
  (a) `Q_k` is a bounded linear map for `k = 0, 2`; (b) there are constants `K₂, K₃` with
  `‖w p‖ ≤ K₂ r(p)²` and `‖w(a,b,τ) - w₂(a,b,τ)‖ ≤ K₃ r(a,b,τ)³` on `U`, where
  `r = |a| + |b| + √|τ|` and `w₂(a,b,τ) = ((τ - a² + b²)/12) c₂ - (ab/6) s₂`;
  (c) there are radii `ε, δ > 0` such that every mean-zero `v ∈ PH α 2` with `‖v‖ < ε`, every
  `τ` with `|τ| < δ` and `R(v, τ) = 0` has `(a v, b v, τ) ∈ U`,
  `v = a v • c₁ + b v • s₁ + w (a v, b v, τ)`, and the pair `(a v, b v)` is the only pair with
  such a representation; (d) there is `h1 > 0` such that for every `0 < h < h1` and every ground
  minimizer `ρ` of EX011 the positive smooth representative `r` has `u = √r` satisfying the
  constrained Euler equation, and its centered logarithm `v` is a mean-zero element of `PH α 2`
  with `‖v‖ < ε`, `|h²| < δ`, `R(v, h²) = 0` and the representation of (c) at `τ = h²`.

## R5 notes

* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. The
  specification gives only an informal statement; the Lean form above is the conjunction of the
  conclusions of EX012.02, EX012.04, EX012.11 and EX012.12 made to refer to one and the same
  neighborhood package `(U, V, w)`. No hypothesis is added.
* The statement is existential in `(U, V, w)`, as is EX012.07: "the small analytic solution" is
  read as the function `w` defined by the characterization on `U × V`, which fixes `w` on `U`
  (local uniqueness). The package is that of EX012.11 (hence of EX012.10); EX012.12's part (i)
  is applied to it through `ex012_12_small_full_solutions_range`, which holds for any package
  with this characterization, and part (ii) is re-derived for it with the EX012.12 helpers.
* "Weighted remainder of order at least three under weights `(1, 1, 2)`" is read, as in
  EX012.11, as the single inequality `‖w - w₂‖ ≤ K₃ (|a| + |b| + √|τ|)³` over the whole
  neighborhood `U`, for both signs of `τ`. The companion quadratic bound is also recorded. The
  constants `K₂ = 2 C₂` and `K₃ = 4 b₂ M₁ C₂ + 4 b₂ C₂²` are existential, independent of
  `(a, b, τ)`.
* The norm in the remainder bound is the `PH α 2` norm of the difference of `w (a, b, τ)`
  (coerced to `PH α 2`) and `w₂`, as in EX012.11.
* `R(v, τ)` is `residual α v τ ∈ PH α 0` (EX012.30), and `R(v, τ) = 0` is equality in `PH α 0`;
  mean zero is `PH.integral 2 v = 0`. "Sufficiently small `v` and `τ`" is `‖v‖ < ε`,
  `|τ| < δ`, with `ε, δ` produced after `(U, V, w)`. The coefficients `a`, `b` are
  `coefA v`, `coefB v` of EX012.35.
* Uniqueness of the representation is stated for all real pairs `(a', b')`, as in EX012.12.
* Part (d): "minimizing logarithm" is the logarithm of the smooth representative of an EX011
  ground minimizer, with the quantifier shape `h1` first, then `h` and `ρ`, as in EX012.12.
  The constrained Euler equation (EX012.02) is stated for `u = √r` with
  `λ = E_h(u²) = groundE h u`, pointwise on `ℝ`; the minimality of `ρ` over `AbsoluteDensity 1`
  is converted to minimality among admissible smooth densities by EX012.36 (the helper
  `ground_min_EX01212` of EX012.12).
* Part (a) restates the boundedness of the complement projection `Q_k` (EX012.04 (iii)) with
  its explicit bound, for `k = 0, 2` only, the regularities of that statement.
* The dependence on the definition gates EX012.36 and EX012.37 is inherited from the cited
  results, which are proved in the campaign form of these gates; nothing is assumed here.
-/

open MeasureTheory
open scoped ContDiff
open DGPS.Circle.VonMisesSmallField
open DGPS.Analysis.PeriodicHolder
open DGPS.Frontier.EX012

namespace DGPS.Examples

/-- **EX012.CLOSE.** One-site complementary range equation: on one neighborhood package
`(U, V, w)` the range equation has the unique small analytic solution `w(a, b, τ)` with leading
terms `((τ - a² + b²)/12) c₂ - (ab/6) s₂` and weighted remainder of order three; every small
full solution, including the EX011 minimizing logarithms at `τ = h²`, has the representation
`v = a c₁ + b s₁ + w(a, b, τ)` with uniquely determined `(a, b)`. -/
theorem one_site_complementary_range_equation (α : ℝ) [HolderExponent α] :
    ∃ (U : Set (ℝ × ℝ × ℝ)) (V : Set (PH.orthSub α 2)) (w : ℝ × ℝ × ℝ → PH.orthSub α 2),
      IsOpen U ∧ IsOpen V ∧ (0 : ℝ × ℝ × ℝ) ∈ U ∧ (0 : PH.orthSub α 2) ∈ V ∧
      AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
      (∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p) ∧
      (∀ k : ℕ, (k = 0 ∨ k = 2) →
        ∃ Q : PH α k →L[ℝ] PH.orthSub α k, Q = proj_EX01226 α k ∧
          ‖Q‖ ≤ 1 + ‖(PH.modeCLM k 0 : PH α k →L[ℝ] PH α k)‖ + ‖(PH.modeCLM k 1 : PH α k →L[ℝ] PH α k)‖) ∧
      (∃ K₂ K₃ : ℝ,
        (∀ p ∈ U, ‖w p‖ ≤ K₂ * (|p.1| + |p.2.1| + Real.sqrt |p.2.2|) ^ 2) ∧
        (∀ a b τ : ℝ, (a, b, τ) ∈ U →
          ‖(w (a, b, τ) : PH α 2) - (((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
              ((a * b) / 6) • sinMode_EX01228 α 2 2)‖ ≤
            K₃ * (|a| + |b| + Real.sqrt |τ|) ^ 3)) ∧
      ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
        (∀ v : PH α 2, ‖v‖ < ε → PH.integral 2 v = 0 → ∀ τ : ℝ, |τ| < δ →
          residual_EX01230 α v τ = 0 →
          (coefA_EX01235 v, coefB_EX01235 v, τ) ∈ U ∧
          v = coefA_EX01235 v • cosMode_EX01228 α 2 1 + coefB_EX01235 v • sinMode_EX01228 α 2 1 +
            ((w (coefA_EX01235 v, coefB_EX01235 v, τ) : PH.orthSub α 2) : PH α 2) ∧
          ∀ a b : ℝ, v = a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1 +
            ((w (a, b, τ) : PH.orthSub α 2) : PH α 2) →
            a = coefA_EX01235 v ∧ b = coefB_EX01235 v) ∧
        ∃ h1 : ℝ, 0 < h1 ∧
          ∀ h : ℝ, 0 < h → h < h1 → ∀ ρ : AbsoluteDensity 1,
            (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
            ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
              (∃ u : ℝ → ℝ, (∀ t, u t = Real.sqrt (r (torusLift fun _ => t))) ∧
                ∀ x : ℝ, -4 * angD_EX01217 (angD_EX01217 u) x +
                  h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x - 4 * u x * Real.log (u x) =
                    groundE_EX01236 h u * u x) ∧
              ∃ v : PH α 2,
                v.val = (fun s => Real.log (r (torusLift fun _ => s)) -
                  ∫ y, Real.log (r y) ∂haar 1) ∧
                ‖v‖ < ε ∧ PH.integral 2 v = 0 ∧ |h ^ 2| < δ ∧
                residual_EX01230 α v (h ^ 2) = 0 ∧
                (coefA_EX01235 v, coefB_EX01235 v, h ^ 2) ∈ U ∧
                v = coefA_EX01235 v • cosMode_EX01228 α 2 1 +
                  coefB_EX01235 v • sinMode_EX01228 α 2 1 +
                  ((w (coefA_EX01235 v, coefB_EX01235 v, h ^ 2) : PH.orthSub α 2) : PH α 2) ∧
                ∀ a b : ℝ, v = a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1 +
                  ((w (a, b, h ^ 2) : PH.orthSub α 2) : PH α 2) →
                  a = coefA_EX01235 v ∧ b = coefB_EX01235 v := by
  obtain ⟨b₂, M₁, C₂, -, -, -, -, -, -, U, V, w, hUo, hVo, hU0, hV0, hAn, hmaps, hw0, hchar,
    -, -, hquad, hrem⟩ := ex012_11_weighted_remainder α
  have hQ : ∀ k : ℕ, (k = 0 ∨ k = 2) →
      ∃ Q : PH α k →L[ℝ] PH.orthSub α k, Q = proj_EX01226 α k ∧
        ‖Q‖ ≤ 1 + ‖(PH.modeCLM k 0 : PH α k →L[ℝ] PH α k)‖ + ‖(PH.modeCLM k 1 : PH α k →L[ℝ] PH α k)‖ := fun k hk => by
    obtain ⟨P₀, P₁, h0, h1, -, Q, hQ, hQn⟩ :=
      (ex012_04_bounded_derivative_fourier_projections (α := α)).2.2.1 k hk
    exact ⟨Q, hQ, by rw [← h0, ← h1]; exact hQn⟩
  obtain ⟨ε, δ, hε, hδ, hA⟩ := ex012_12_small_full_solutions_range hUo hVo hU0 hV0 hchar
  refine ⟨U, V, w, hUo, hVo, hU0, hV0, hAn, hmaps, hw0, hchar, hQ,
    ⟨2 * C₂, 4 * b₂ * M₁ * C₂ + 4 * b₂ * C₂ ^ 2, hquad, hrem⟩, ε, δ, hε, hδ, hA, ?_⟩
  obtain ⟨h1, hh1, hT01⟩ := ex012_01_positive_smooth_normalized_logarithm α (ε / 2) (by positivity)
  refine ⟨min h1 (Real.sqrt δ), lt_min hh1 (Real.sqrt_pos.2 hδ), fun h hh hlt ρ hmin => ?_⟩
  have hlt1 : h < h1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt2 : h < Real.sqrt δ := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨r, hr, hsm, hρ, -, u, hu, hsmu, hper, hposu, hsq, -, v, hv, -, hmeanI, hnorm⟩ :=
    hT01 h hh hlt1 ρ hmin
  have hadm : IsAdmSmooth_EX01236 u := ⟨hsmu, hper, hposu, hsq⟩
  have hmin' := ground_min_EX01212 h ρ r hr hsm hρ hmin hu hadm
  obtain ⟨-, -, -, hR⟩ := ex012_03_remove_euler_constant_forward h hadm hmin'
  have hvc : v.val = centeredLog2_EX01221 u := centeredLog_eq_EX01212 hr hsm hu hv
  have hres : residual_EX01230 α v (h ^ 2) = 0 := by
    refine residual_zero_EX01212 v (h ^ 2) ?_ ?_
    · rw [hvc]; exact centeredLog2_contDiff_EX01203 hadm
    · rw [hvc]; exact hR
  have hint : PH.integral 2 v = 0 := by
    rw [PH.integral_apply]; exact hmeanI
  have hτ : |h ^ 2| < δ := by
    rw [abs_of_nonneg (sq_nonneg h)]
    exact (Real.lt_sqrt hh.le).1 hlt2
  have hvε : ‖v‖ < ε := lt_of_le_of_lt hnorm (by linarith)
  exact ⟨r, hr, hsm, hρ, ⟨u, hu, ex012_02_constrained_euler_equation h hadm hmin'⟩, v, hv, hvε,
    hint, hτ, hres, hA v hvε hint (h ^ 2) hτ hres⟩

end DGPS.Examples
