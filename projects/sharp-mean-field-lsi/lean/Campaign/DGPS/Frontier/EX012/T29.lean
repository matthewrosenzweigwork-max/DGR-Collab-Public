import DGPS.Frontier.EX012.T24
import DGPS.Frontier.EX012.T25
import DGPS.Frontier.EX012.T26
import DGPS.Frontier.EX012.T27
import DGPS.Frontier.EX012.T28

/-!
# EX012.29: Polynomial regularity and partial derivative

Task id: EX012.29 (node EX012, one-site complementary range equation).
Title: Polynomial regularity and partial derivative.

Provides:
* `DGPS.Frontier.EX012.ex012_29_polynomial_regularity_partial_derivative`: the main statement.
  For `rangeMap_EX01229 α : (ℝ × ℝ × ℝ) × W → Y` (with `W = PH.orthSub α 2`,
  `Y = PH.orthSub α 0`), the displayed map
  `F(p, w) = L w + Q [ (1/2) (D f_p + D w)^2 + (τ/4) c₂ ]`, `p = (a, b, τ)`,
  `f_p = a c₁ + b s₁`, it is asserted that (i) `F` is real analytic at every point of its
  domain, (ii) `F (0, 0) = 0`, (iii) the derivative in the unknown variable at `(0, 0)` is `L`,
  in the form `fderiv ℝ F (0, 0) ∘L inr = L`, which is the continuous-linear-map type expected
  by `ContDiffAt.implicitFunction`, and also `fderiv ℝ (w ↦ F (0, w)) 0 = L`.
* `DGPS.Frontier.EX012.ex012_29_polynomial_regularity_partial_derivative_contDiff`: `F` is
  `C^ω`, `ContDiff ℝ ω F`, hence `ContDiffAt ℝ ω F (0, 0)`.
* `DGPS.Frontier.EX012.ex012_29_polynomial_regularity_partial_derivative_partial`: the
  identity `fderiv ℝ F (0, 0) ∘L inr = L` alone.
* `DGPS.Frontier.EX012.ex012_29_polynomial_regularity_partial_derivative_invertible`: the
  partial derivative `fderiv ℝ F (0, 0) ∘L inr` satisfies `ContinuousLinearMap.IsInvertible`,
  the hypothesis of the implicit function theorem.
* `DGPS.Frontier.EX012.ex012_29_polynomial_regularity_partial_derivative_decomp`: the
  decomposition `F x = linPart x + quadPart x` into a continuous linear part and a quadratic
  part.
* Helpers (all suffixed `_EX01229`): `rangeMap_EX01229` (the map `F`), `abMap_EX01229` (the
  coordinates `(a, b)`), `fieldMap_EX01229` (the continuous linear map `(p, w) ↦ D f_p + D w`),
  `quadForm_EX01229` (the bilinear form `(z, z') ↦ (1/2) Q (z z')`), `quadPart_EX01229` (the
  quadratic part), `linPart_EX01229` (the continuous linear part `(p, w) ↦ L w + (τ/4) Q c₂`),
  `fieldMap_apply_EX01229`, `quadForm_apply_EX01229`, `linPart_apply_EX01229`,
  `rangeMap_eq_aux_EX01229`, `rangeMap_eq_EX01229` (the decomposition),
  `quadPart_analyticAt_EX01229`, `rangeMap_analyticOnNhd_EX01229`, `rangeMap_zero_EX01229`,
  `quadPart_hasFDerivAt_zero_EX01229` (the quadratic part has zero derivative at the origin),
  `rangeMap_hasFDerivAt_zero_EX01229`, `linPart_inr_EX01229`.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No further
  hypothesis is added.
* The displayed `F` is the one of EX012.05: `F(p, w) = L w + Q[(1/2)(D f_p + D w)^2 + (τ/4) c₂]`
  with `p = (a, b, τ)`. Here `L` is `ComplementaryElliptic.ellEquiv`, the equivalence supplied by
  FOU018 (`complementary_circle_elliptic_inverse`), `W = PH.orthSub α 2`, `Y = PH.orthSub α 0`,
  `D = angDeriv_EX01224` (EX012.24), the square is the diagonal of the bounded multiplication
  `ex012_27_bounded_multiplication` (EX012.27), `Q = proj_EX01226 α 0` (EX012.26),
  `c₂ = cosMode_EX01228 α 0 2` and `f_p = harmInj_EX01228 α 2 (a, b)` (EX012.28), with `w`
  included into `PH α 2` through the subtype coercion before `D` is applied.
* "The ordinary Banach product `ℝ³ × W`" is read as `(ℝ × ℝ × ℝ) × PH.orthSub α 2` with the
  product norm, so that the unknown variable is the second factor of a two-factor product as
  `ContDiffAt.implicitFunction` requires; `ℝ³` is `ℝ × ℝ × ℝ` with `p = (a, (b, τ))`.
* "Analytic" is read as `AnalyticOnNhd ℝ F Set.univ` (analytic at every point), together with
  the `ContDiff ℝ ω F` form (the pinned `ContDiff/Defs.lean` identifies the index `ω` with
  analyticity), obtained from the analytic statement by `AnalyticOnNhd.contDiff`.
* Analyticity is proved by the route of the specification: `F` is a continuous linear map plus
  the diagonal of a continuous bilinear map composed with a continuous linear map, using
  `ContinuousLinearMap.analyticAt`, `ContinuousLinearMap.analyticAt_bilinear`, `AnalyticAt.prod`,
  `AnalyticAt.comp_of_eq` and `AnalyticAt.add`. The derivative of the quadratic part at the
  origin vanishes by `ContinuousLinearMap.hasFDerivAt_of_bilinear`, because the field map
  vanishes at the origin.
* "`D_wF(0,0) = L`" is stated in the exact form
  `fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ _ _ = L`, with `L` the underlying continuous linear map of `ellEquiv`; the partial derivative of
  the section `w ↦ F ((0,0,0), w)` is also given and equals `L`.
* The map `F` is defined literally as displayed (the projection applied to the sum), and its
  split into a linear part and a quadratic part is a proved lemma, not a definition.
* Nothing is proved here about the identification `F(p, w) = Q R(f_p + w, τ)`; that is EX012.30.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic
open scoped ContDiff

namespace DGPS.Frontier.EX012

section Construction

variable (α : ℝ) [HolderExponent α]

/-- The coordinates `(a, b)` of the parameter `p = (a, b, τ)` as a continuous linear map on the
product `(ℝ × ℝ × ℝ) × W`. -/
noncomputable def abMap_EX01229 : (ℝ × ℝ × ℝ) × PH.orthSub α 2 →L[ℝ] ℝ × ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2))))

/-- The continuous linear map `(p, w) ↦ D f_p + D w` into `PH α 0`, `p = (a, b, τ)`. -/
noncomputable def fieldMap_EX01229 :
    (ℝ × ℝ × ℝ) × PH.orthSub α 2 →L[ℝ] PH α 0 :=
  (angDeriv_EX01224 (α := α)).comp ((harmInj_EX01228 α 2).comp (abMap_EX01229 α)) +
    (angDeriv_EX01224 (α := α)).comp
      ((PH.orthSub α 2).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)))

/-- The displayed map `F(p, w) = L w + Q [ (1/2) (D f_p + D w)^2 + (τ/4) c₂ ]`. -/
noncomputable def rangeMap_EX01229 :
    (ℝ × ℝ × ℝ) × PH.orthSub α 2 → PH.orthSub α 0 := fun x =>
  ellEquiv x.2 +
    proj_EX01226 α 0
      ((1 / 2 : ℝ) •
          ex012_27_bounded_multiplication α
            (angDeriv_EX01224 (harmInj_EX01228 α 2 (x.1.1, x.1.2.1)) +
              angDeriv_EX01224 (x.2 : PH α 2))
            (angDeriv_EX01224 (harmInj_EX01228 α 2 (x.1.1, x.1.2.1)) +
              angDeriv_EX01224 (x.2 : PH α 2)) +
        (x.1.2.2 / 4) • cosMode_EX01228 α 0 2)

theorem fieldMap_apply_EX01229 (x : (ℝ × ℝ × ℝ) × PH.orthSub α 2) :
    fieldMap_EX01229 α x =
      angDeriv_EX01224 (harmInj_EX01228 α 2 (x.1.1, x.1.2.1)) +
        angDeriv_EX01224 (x.2 : PH α 2) := rfl

/-- The continuous bilinear form `(z, z') ↦ (1/2) Q (z z')` into `Y`. -/
noncomputable def quadForm_EX01229 : PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH.orthSub α 0 :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.compL ℝ (PH α 0) (PH α 0) (PH.orthSub α 0)
      (proj_EX01226 α 0)).comp (ex012_27_bounded_multiplication α)

theorem quadForm_apply_EX01229 (z z' : PH α 0) :
    quadForm_EX01229 α z z' =
      (1 / 2 : ℝ) • proj_EX01226 α 0 (ex012_27_bounded_multiplication α z z') := rfl

/-- The quadratic part `x ↦ (1/2) Q ((D f_p + D w)^2)`. -/
noncomputable def quadPart_EX01229 :
    (ℝ × ℝ × ℝ) × PH.orthSub α 2 → PH.orthSub α 0 := fun x =>
  quadForm_EX01229 α (fieldMap_EX01229 α x) (fieldMap_EX01229 α x)

/-- The continuous linear part `(p, w) ↦ L w + (τ/4) Q c₂`. -/
noncomputable def linPart_EX01229 :
    (ℝ × ℝ × ℝ) × PH.orthSub α 2 →L[ℝ] PH.orthSub α 0 :=
  ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)) +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)))).smulRight
      ((1 / 4 : ℝ) • (proj_EX01226 α 0 (cosMode_EX01228 α 0 2)))

theorem linPart_apply_EX01229 (x : (ℝ × ℝ × ℝ) × PH.orthSub α 2) :
    linPart_EX01229 α x =
      ellEquiv x.2 + (x.1.2.2 / 4) • proj_EX01226 α 0 (cosMode_EX01228 α 0 2) := by
  simp only [linPart_EX01229, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe, smul_smul]
  congr 2
  ring

theorem rangeMap_eq_aux_EX01229 (z : PH α 0) (w : PH.orthSub α 2) (t : ℝ) :
    ellEquiv w +
        proj_EX01226 α 0 ((1 / 2 : ℝ) • ex012_27_bounded_multiplication α z z +
          t • cosMode_EX01228 α 0 2) =
      (ellEquiv w + t • proj_EX01226 α 0 (cosMode_EX01228 α 0 2)) + quadForm_EX01229 α z z := by
  rw [quadForm_apply_EX01229]
  simp only [map_add, map_smul]
  abel

/-- The displayed map is the sum of its linear and quadratic parts. -/
theorem rangeMap_eq_EX01229 (x : (ℝ × ℝ × ℝ) × PH.orthSub α 2) :
    rangeMap_EX01229 α x = linPart_EX01229 α x + quadPart_EX01229 α x := by
  rw [linPart_apply_EX01229]
  exact rangeMap_eq_aux_EX01229 α (fieldMap_EX01229 α x) x.2 (x.1.2.2 / 4)

end Construction

section Regularity

variable (α : ℝ) [HolderExponent α]

theorem quadPart_analyticAt_EX01229 (x : (ℝ × ℝ × ℝ) × PH.orthSub α 2) :
    AnalyticAt ℝ (quadPart_EX01229 α) x := by
  have hg : AnalyticAt ℝ (fun u : PH α 0 × PH α 0 => quadForm_EX01229 α u.1 u.2)
      (fieldMap_EX01229 α x, fieldMap_EX01229 α x) :=
    ContinuousLinearMap.analyticAt_bilinear (quadForm_EX01229 α) _
  have hf : AnalyticAt ℝ (fun y : (ℝ × ℝ × ℝ) × PH.orthSub α 2 =>
      (fieldMap_EX01229 α y, fieldMap_EX01229 α y)) x :=
    AnalyticAt.prod ((fieldMap_EX01229 α).analyticAt x) ((fieldMap_EX01229 α).analyticAt x)
  have h := hg.comp_of_eq hf rfl
  have e : quadPart_EX01229 α = (fun u : PH α 0 × PH α 0 => quadForm_EX01229 α u.1 u.2) ∘
      (fun y : (ℝ × ℝ × ℝ) × PH.orthSub α 2 => (fieldMap_EX01229 α y, fieldMap_EX01229 α y)) := by
    funext y
    rfl
  rw [e]
  exact h

theorem rangeMap_analyticOnNhd_EX01229 :
    AnalyticOnNhd ℝ (rangeMap_EX01229 α) Set.univ := by
  have hF : rangeMap_EX01229 α = fun x => linPart_EX01229 α x + quadPart_EX01229 α x :=
    funext (rangeMap_eq_EX01229 α)
  rw [hF]
  exact fun x _ => ((linPart_EX01229 α).analyticAt x).add (quadPart_analyticAt_EX01229 α x)

theorem rangeMap_zero_EX01229 : rangeMap_EX01229 α 0 = 0 := by
  rw [rangeMap_eq_EX01229]
  simp [quadPart_EX01229]

theorem quadPart_hasFDerivAt_zero_EX01229 :
    HasFDerivAt (quadPart_EX01229 α) (0 : (ℝ × ℝ × ℝ) × PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) 0 := by
  have h := (quadForm_EX01229 α).hasFDerivAt_of_bilinear (fieldMap_EX01229 α).hasFDerivAt
    (fieldMap_EX01229 α).hasFDerivAt (x := 0)
  have h0 : ((quadForm_EX01229 α).precompR ((ℝ × ℝ × ℝ) × PH.orthSub α 2)
      (fieldMap_EX01229 α 0) (fieldMap_EX01229 α) +
      (quadForm_EX01229 α).precompL ((ℝ × ℝ × ℝ) × PH.orthSub α 2) (fieldMap_EX01229 α)
        (fieldMap_EX01229 α 0)) = 0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [h0] at h
  exact h

theorem rangeMap_hasFDerivAt_zero_EX01229 :
    HasFDerivAt (rangeMap_EX01229 α) (linPart_EX01229 α) 0 := by
  have hF : rangeMap_EX01229 α = fun x => linPart_EX01229 α x + quadPart_EX01229 α x :=
    funext (rangeMap_eq_EX01229 α)
  rw [hF]
  have h := (linPart_EX01229 α).hasFDerivAt.add (quadPart_hasFDerivAt_zero_EX01229 α)
  rwa [add_zero] at h

theorem linPart_inr_EX01229 :
    (linPart_EX01229 α).comp
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)) =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) := by
  ext w
  simp [linPart_apply_EX01229]

end Regularity

section Main

variable (α : ℝ) [HolderExponent α]

/-- `F` is `C^ω`, in particular `C^ω` at the origin. -/
theorem ex012_29_polynomial_regularity_partial_derivative_contDiff :
    ContDiff ℝ ω (rangeMap_EX01229 α) :=
  (rangeMap_analyticOnNhd_EX01229 α).contDiff

/-- The partial derivative in the unknown variable at the origin, in the form expected by
`ContDiffAt.implicitFunction`. -/
theorem ex012_29_polynomial_regularity_partial_derivative_partial :
    fderiv ℝ (rangeMap_EX01229 α) 0 ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2) =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) := by
  rw [(rangeMap_hasFDerivAt_zero_EX01229 α).fderiv]
  exact linPart_inr_EX01229 α

/-- The partial derivative in the unknown variable at the origin is invertible. -/
theorem ex012_29_polynomial_regularity_partial_derivative_invertible :
    (fderiv ℝ (rangeMap_EX01229 α) 0 ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)).IsInvertible := by
  rw [ex012_29_polynomial_regularity_partial_derivative_partial]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The decomposition of `F` into its continuous linear part and its quadratic part. -/
theorem ex012_29_polynomial_regularity_partial_derivative_decomp
    (x : (ℝ × ℝ × ℝ) × PH.orthSub α 2) :
    rangeMap_EX01229 α x = linPart_EX01229 α x + quadPart_EX01229 α x :=
  rangeMap_eq_EX01229 α x

/-- **EX012.29.**  The map `F(p, w) = L w + Q [ (1/2) (D f_p + D w)^2 + (τ/4) c₂ ]` from
`ℝ³ × W` to `Y` is real analytic, `F (0, 0) = 0`, and its derivative in `w` at `(0, 0)` is
`L`. -/
theorem ex012_29_polynomial_regularity_partial_derivative :
    AnalyticOnNhd ℝ (rangeMap_EX01229 α) Set.univ ∧
    rangeMap_EX01229 α 0 = 0 ∧
    fderiv ℝ (rangeMap_EX01229 α) 0 ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2) =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) ∧
    fderiv ℝ (fun w : PH.orthSub α 2 => rangeMap_EX01229 α (((0 : ℝ), (0 : ℝ), (0 : ℝ)), w)) 0 =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) := by
  refine ⟨rangeMap_analyticOnNhd_EX01229 α, rangeMap_zero_EX01229 α,
    ex012_29_polynomial_regularity_partial_derivative_partial α, ?_⟩
  have hg : HasFDerivAt (rangeMap_EX01229 α) (linPart_EX01229 α)
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2) 0) := by
    rw [map_zero]
    exact rangeMap_hasFDerivAt_zero_EX01229 α
  have h := HasFDerivAt.comp (x := (0 : PH.orthSub α 2)) hg
    (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2)).hasFDerivAt
  have h2 : (fun w : PH.orthSub α 2 => rangeMap_EX01229 α (((0 : ℝ), (0 : ℝ), (0 : ℝ)), w)) =
      rangeMap_EX01229 α ∘ ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2) := rfl
  rw [h2, h.fderiv]
  exact linPart_inr_EX01229 α

end Main

end DGPS.Frontier.EX012
