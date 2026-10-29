import DGPS.Frontier.EX012.T01
import DGPS.Frontier.EX012.T03
import DGPS.Frontier.EX012.T07
import DGPS.Frontier.EX012.T30
import DGPS.Frontier.EX012.T35

/-!
# EX012.12: All small full solutions

Task id: EX012.12 (node EX012, one-site complementary range equation, assembly).
Title: All small full solutions.

Every sufficiently small mean-zero `v ∈ PH α 2` with `R(v, τ) = 0` and sufficiently small `τ` is
`v = a c₁ + b s₁ + w(a, b, τ)` with `a = 2 ∫ v c₁`, `b = 2 ∫ v s₁` and `w` the analytic small
solution of EX012.07; the pair `(a, b)` is the only one that gives such a representation. Every
sufficiently small minimizing logarithm of EX011 (EX012.01) satisfies `R(v, h²) = 0` (EX012.03)
and therefore has this representation.

## Provides

* `DGPS.Frontier.EX012.ex012_12_small_full_solutions (α : ℝ) [HolderExponent α]`: the main
  statement. There are the data `U, V, w` of EX012.07 (open neighborhoods of `0` in `ℝ³` and in
  `W = PH.orthSub α 2`, a map `w : ℝ³ → W` analytic on `U`, `w 0 = 0`, `w U ⊆ V`, and
  `F (p, z) = 0 ↔ z = w p` for `p ∈ U`, `z ∈ V`) and radii `ε, δ > 0` such that
  (i) every mean-zero `v ∈ PH α 2` with `‖v‖ < ε`, every `τ` with `|τ| < δ` and
  `R(v, τ) = 0` satisfies `(a v, b v, τ) ∈ U`, `v = a v • c₁ + b v • s₁ + w (a v, b v, τ)`, and
  `(a, b)` is the only pair with `v = a • c₁ + b • s₁ + w (a, b, τ)`; (ii) there is `h1 > 0`
  such that for every `0 < h < h1` and every ground minimizer `ρ` of EX011 the positive smooth
  representative `r` has the centered logarithm `v ∈ PH α 2` with `‖v‖ < ε`, mean zero,
  `R(v, h²) = 0`, and the representation of (i) at `τ = h²`.
* `DGPS.Frontier.EX012.ex012_12_small_full_solutions_range`: part (i) alone, for any open
  neighborhoods `U, V` of zero and any `w` with the characterization `F (p, z) = 0 ↔ z = w p`
  on `U × V`; the radii `ε, δ` are produced from `U, V`.
* `DGPS.Frontier.EX012.ex012_12_small_full_solutions_coefficients`: for `z ∈ W`, the first
  cosine and sine coefficients of `a • c₁ + b • s₁ + z` are `a` and `b`.
* Helpers (suffix `_EX01212`): `fullRep_EX01212` (the representation property of part (i)),
  `angD_angD_EX01212` (`D² f = ((2π)²)⁻¹ f''` for smooth `f`), `residual_zero_EX01212`
  (`eulerR_EX01222 τ v.val = 0` pointwise implies `residual_EX01230 α v τ = 0`),
  `centeredLog_eq_EX01212` (the centered logarithm of EX012.01 is `centeredLog2_EX01221 u`),
  `ground_min_EX01212` (an EX011 ground minimizer minimizes `groundE_EX01236` over admissible
  densities).

## R5 notes

* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. The
  statement adds no hypothesis beyond the specification's: mean zero, smallness of `v` and `τ`,
  and `R(v, τ) = 0`.
* "Sufficiently small `v` and `τ`" is read as `‖v‖ < ε` (the `PH α 2` norm) and `|τ| < δ` for
  radii `ε, δ > 0` which are produced together with `U, V, w`; the quantifier order is
  `∃ U V w ε δ, ∀ v τ`. The data `U, V, w` are the existential output of EX012.07, whose statement
  is existential, so `w` is determined only on `U` (by the characterization). "The small analytic
  solution `w(a, b, τ)`" is read as this `w`. The statement does not mention `a`, `b` as given
  numbers: they are the coefficients `coefA_EX01235 v`, `coefB_EX01235 v` of EX012.35.
* `R(v, τ)` is `residual_EX01230 α v τ ∈ PH α 0` (EX012.30), and `R(v, τ) = 0` is equality in
  `PH α 0`. The range equation `F = 0` is the projected equation `Q₀ R = 0`
  (`rangeMap_EX01229`); the two omitted first-harmonic components of the full stationary equation
  are neither used nor claimed, as the specification requires. Only `R = 0` is assumed, and `Q₀`
  is applied to it.
* Mean zero is `PH.integral 2 v = 0`, the interval integral `∫₀¹ v.val`. Reconstruction
  `v = a c₁ + b s₁ + Q₂ v` uses it (EX012.35 (ii)).
* Uniqueness of the representation is stated for every pair `(a', b')` of reals, without asking
  `(a', b', τ) ∈ U`; it needs only that `w (a', b', τ)` lies in `W`, so it is stronger than a
  uniqueness among points of `U`. It is read as uniqueness of `(a, b)` (the value
  `w (a, b, τ)` is then determined).
* Part (ii): "minimizing logarithm from EX011" is the logarithm `v` of the strictly positive smooth
  representative `r` of a minimizer `ρ` of `ex010_ground h` over `AbsoluteDensity 1`, as in EX012.01
  (same quantifier shape: `h1` first, then `h` and `ρ`). "Sufficiently small" is the smallness
  given by EX012.01 with the tolerance `ε / 2`, and `h1` is also cut by `√δ` so that `|h²| < δ`.
  The conclusion gives `v` with the formula of EX012.01 (`v.val s = log r(s) - ∫ log r`).
  `R(v, h²) = 0` is proved from EX012.03 (forward), applied to `u = √r`; the minimality
  over `AbsoluteDensity 1` is turned into minimality of `groundE_EX01236` over admissible
  densities by EX012.36 (`ground_smoothDensity_EX01236` and the transport lemma), which is
  the form of hypothesis EX012.03 uses.
* The relation `v.val = centeredLog2_EX01221 u` (EX012.01's `v` versus EX012.03's `v`) is proved,
  using `∫ log r ∂haar 1 = ∫₀¹ log r` (`integral_haar_one`) and `2 log √r = log r`.
* EX012.03's residual `eulerR_EX01222 (h²) v.val` is converted to the `PH α 0` residual of
  EX012.30 pointwise (`D (D v) = ((2π)²)⁻¹ v''`, `cos (2π·2·x) = cos (2π·(2:ℕ)·x)`).
-/

open MeasureTheory
open scoped ContDiff Topology
open DGPS.Circle.VonMisesSmallField
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Helpers

variable {α : ℝ} [HolderExponent α]

/-- The property of part (i): `(a v, b v, τ) ∈ U`, `v = a c₁ + b s₁ + w (a v, b v, τ)`, and
`(a v, b v)` is the only pair of real numbers with this property. -/
def fullRep_EX01212 (α : ℝ) [HolderExponent α] (U : Set (ℝ × ℝ × ℝ))
    (w : ℝ × ℝ × ℝ → PH.orthSub α 2) (v : PH α 2) (τ : ℝ) : Prop :=
  (coefA_EX01235 v, coefB_EX01235 v, τ) ∈ U ∧
    v = coefA_EX01235 v • cosMode_EX01228 α 2 1 + coefB_EX01235 v • sinMode_EX01228 α 2 1 +
      ((w (coefA_EX01235 v, coefB_EX01235 v, τ) : PH.orthSub α 2) : PH α 2) ∧
    ∀ a b : ℝ, v = a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1 +
      ((w (a, b, τ) : PH.orthSub α 2) : PH α 2) → a = coefA_EX01235 v ∧ b = coefB_EX01235 v

/-- The first cosine and sine coefficients of `a c₁ + b s₁ + z`, `z ∈ W`, are `a` and `b`. -/
theorem ex012_12_small_full_solutions_coefficients (a b : ℝ) (z : PH.orthSub α 2) :
    coefA_EX01235 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1 + (z : PH α 2)) = a ∧
      coefB_EX01235 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1 + (z : PH α 2)) = b := by
  obtain ⟨c1, c2, c3⟩ := coeffs_cosMode_EX01226 (α := α) 2
  obtain ⟨s1, s2, s3⟩ := coeffs_sinMode_EX01226 (α := α) 2
  have hz := z.2
  refine ⟨?_, ?_⟩
  · unfold coefA_EX01235
    rw [modeWeight_one_EX01235, map_add, map_add, map_smul, map_smul, c2, s2, hz.2.1]
    simp
    ring
  · unfold coefB_EX01235
    rw [modeWeight_one_EX01235, map_add, map_add, map_smul, map_smul, c3, s3, hz.2.2]
    simp
    ring

theorem fullRep_of_eq_EX01212 {U : Set (ℝ × ℝ × ℝ)} {w : ℝ × ℝ × ℝ → PH.orthSub α 2}
    {v : PH α 2} {τ : ℝ} (hU : (coefA_EX01235 v, coefB_EX01235 v, τ) ∈ U)
    (hv : v = coefA_EX01235 v • cosMode_EX01228 α 2 1 + coefB_EX01235 v • sinMode_EX01228 α 2 1 +
      ((w (coefA_EX01235 v, coefB_EX01235 v, τ) : PH.orthSub α 2) : PH α 2)) :
    fullRep_EX01212 α U w v τ := by
  refine ⟨hU, hv, fun a b h => ?_⟩
  have := ex012_12_small_full_solutions_coefficients a b (w (a, b, τ))
  rw [← h] at this
  exact ⟨this.1.symm, this.2.symm⟩

/-- Part (i), for any neighborhoods `U, V` and any `w` characterizing the zeros of the range map. -/
theorem ex012_12_small_full_solutions_range {U : Set (ℝ × ℝ × ℝ)} {V : Set (PH.orthSub α 2)}
    {w : ℝ × ℝ × ℝ → PH.orthSub α 2} (hUo : IsOpen U) (hVo : IsOpen V)
    (hU0 : (0 : ℝ × ℝ × ℝ) ∈ U) (hV0 : (0 : PH.orthSub α 2) ∈ V)
    (hchar : ∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ v : PH α 2, ‖v‖ < ε → PH.integral 2 v = 0 → ∀ τ : ℝ, |τ| < δ →
        residual_EX01230 α v τ = 0 → fullRep_EX01212 α U w v τ := by
  let Φ : PH α 2 × ℝ → (ℝ × ℝ × ℝ) × PH.orthSub α 2 := fun y =>
    (((extract_EX01235 (α := α) y.1).1, (extract_EX01235 (α := α) y.1).2.1, y.2),
      (extract_EX01235 (α := α) y.1).2.2)
  have hΦc : Continuous Φ := by
    have hE : Continuous fun y : PH α 2 × ℝ => extract_EX01235 (α := α) y.1 :=
      extract_EX01235.continuous.comp continuous_fst
    exact ((hE.fst.prodMk (hE.snd.fst.prodMk continuous_snd)).prodMk hE.snd.snd)
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ]
  have hopen : IsOpen (Φ ⁻¹' (U ×ˢ V)) := (hUo.prod hVo).preimage hΦc
  have hmem : (0 : PH α 2 × ℝ) ∈ Φ ⁻¹' (U ×ˢ V) := by
    show Φ 0 ∈ U ×ˢ V
    rw [hΦ0]
    exact ⟨hU0, hV0⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 hmem
  refine ⟨ρ, ρ, hρ, hρ, fun v hv hmean τ hτ hR => ?_⟩
  have hy : ((v, τ) : PH α 2 × ℝ) ∈ Metric.ball 0 ρ := by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨hv, by rwa [Real.norm_eq_abs]⟩
  obtain ⟨hU, hV⟩ := hball hy
  have hU' : (coefA_EX01235 v, coefB_EX01235 v, τ) ∈ U := hU
  have hV' : proj_EX01226 α 2 v ∈ V := hV
  have hrec := (ex012_35_bounded_coefficient_extraction_reconstruction (α := α)).2 v hmean
  have hsum : harmInj_EX01228 α 2 (coefA_EX01235 v, coefB_EX01235 v) +
      ((proj_EX01226 α 2 v : PH.orthSub α 2) : PH α 2) = v := by
    rw [harmInj_apply_EX01228]
    exact hrec.symm
  have hF : rangeMap_EX01229 α ((coefA_EX01235 v, coefB_EX01235 v, τ), proj_EX01226 α 2 v) = 0 := by
    rw [ex012_30_equality_projected_residual, hsum, hR, map_zero]
  have hz := (hchar _ hU' _ hV').1 hF
  refine fullRep_of_eq_EX01212 hU' ?_
  rw [← hz]
  exact hrec

theorem angD_angD_EX01212 {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    angD_EX01217 (angD_EX01217 f) x = ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f) x := by
  have hd : Differentiable ℝ (deriv f) :=
    ((contDiff_infty_iff_deriv.mp hf).2).differentiable (by simp)
  have h2 : deriv (angD_EX01217 f) x = (2 * Real.pi)⁻¹ * deriv (deriv f) x :=
    ((hd x).hasDerivAt.const_smul (2 * Real.pi)⁻¹).deriv
  rw [angD_EX01217_apply, h2]
  rw [sq, mul_inv]
  ring

/-- `eulerR_EX01222 τ v.val = 0` pointwise gives `R(v, τ) = 0` in `PH α 0`, for smooth `v`. -/
theorem residual_zero_EX01212 (v : PH α 2) (τ : ℝ) (hv : ContDiff ℝ ∞ v.val)
    (hR : ∀ x, eulerR_EX01222 τ v.val x = 0) : residual_EX01230 α v τ = 0 := by
  refine PH.ext (funext fun x => ?_)
  rw [ex012_30_equality_projected_residual_residual_val]
  have h := hR x
  unfold eulerR_EX01222 at h
  rw [angD_angD_EX01212 hv] at h
  have e1 : ∀ y, (angDeriv_EX01224 v).val y = angD_EX01217 v.val y := fun y => rfl
  simp only [e1]
  have e2 : (2 * Real.pi * ((2 : ℕ) : ℝ) * x) = 2 * Real.pi * 2 * x := by push_cast; ring
  rw [e2]
  simpa using h

end Helpers

section Minimizers

variable {α : ℝ} [HolderExponent α]

/-- An EX011 ground minimizer with smooth positive representative `r` and `u = √r` minimizes
`groundE_EX01236 h` among admissible densities. -/
theorem ground_min_EX01212 (h : ℝ) (ρ : AbsoluteDensity 1) (r : Torus 1 → ℝ)
    (hr : ∀ x, 0 < r x) (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r)
    (hmin : ∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ')
    {u : ℝ → ℝ} (hu : ∀ t, u t = Real.sqrt (r (torusLift fun _ => t)))
    (hadm : IsAdmSmooth_EX01236 u) :
    ∀ w : ℝ → ℝ, IsAdmSmooth_EX01236 w → groundE_EX01236 h u ≤ groundE_EX01236 h w := by
  obtain ⟨u', hadm', hu'sq, -, -, -, hgr⟩ :=
    gate_ex012_36_ground_functional_admissible_density_definition_gate_transport h ρ r hr hsm hρ
  have huu : u' = u := by
    funext t
    have h1 : u t ^ 2 = r (torusLift fun _ => t) := by
      rw [hu t]; exact Real.sq_sqrt (hr _).le
    exact (sq_eq_sq₀ (hadm'.pos t).le (hadm.pos t).le).1 ((hu'sq t).trans h1.symm)
  subst huu
  intro w hw
  have := hmin (smoothDensity_EX01236 w hw)
  rwa [hgr, ground_smoothDensity_EX01236 h hw] at this

/-- The centered logarithm of EX012.01 is `centeredLog2_EX01221 u` for `u = √r`. -/
theorem centeredLog_eq_EX01212 {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x) (hsm : IsSmoothPeriodic r)
    {u : ℝ → ℝ} (hu : ∀ t, u t = Real.sqrt (r (torusLift fun _ => t)))
    {v : ℝ → ℝ}
    (hv : v = fun s => Real.log (r (torusLift fun _ => s)) - ∫ y, Real.log (r y) ∂haar 1) :
    v = centeredLog2_EX01221 u := by
  have hlog : ∀ t, 2 * Real.log (u t) = Real.log (r (torusLift fun _ => t)) := fun t => by
    rw [hu t, Real.log_sqrt (hr _).le]; ring
  have hℓ : ∫ y, Real.log (r y) ∂haar 1 = ∫ t in (0 : ℝ)..1, 2 * Real.log (u t) := by
    rw [DGPS.integral_haar_one (fun y => Real.log (r y))
      (hsm.continuous_torus.log fun x => (hr x).ne')]
    exact intervalIntegral.integral_congr fun t _ => (hlog t).symm
  funext s
  rw [hv]
  unfold centeredLog2_EX01221
  simp only
  rw [hℓ, hlog s]

end Minimizers

section Main

variable (α : ℝ) [HolderExponent α]

/-- **EX012.12.**  All small full solutions of the range equation are given by the analytic
solution `w(a, b, τ)` of EX012.07, with uniquely determined first-harmonic coefficients; this
applies to every sufficiently small minimizing logarithm of EX011. -/
theorem ex012_12_small_full_solutions :
    ∃ (U : Set (ℝ × ℝ × ℝ)) (V : Set (PH.orthSub α 2)) (w : ℝ × ℝ × ℝ → PH.orthSub α 2),
      IsOpen U ∧ IsOpen V ∧ (0 : ℝ × ℝ × ℝ) ∈ U ∧ (0 : PH.orthSub α 2) ∈ V ∧
      AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
      (∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p) ∧
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
  obtain ⟨U, V, w, hUo, hVo, hU0, hV0, hAn, hmaps, hw0, hchar⟩ :=
    ex012_07_analytic_implicit_function α
  obtain ⟨ε, δ, hε, hδ, hA⟩ := ex012_12_small_full_solutions_range hUo hVo hU0 hV0 hchar
  refine ⟨U, V, w, hUo, hVo, hU0, hV0, hAn, hmaps, hw0, hchar, ε, δ, hε, hδ, hA, ?_⟩
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
  exact ⟨r, hr, hsm, hρ, v, hv, hvε, hint, hτ, hres, hA v hvε hint (h ^ 2) hτ hres⟩

end Main

end DGPS.Frontier.EX012
