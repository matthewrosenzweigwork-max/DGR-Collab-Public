import DGPS.Frontier.STR029.T12
import DGPS.Frontier.STR029.T16

/-!
# STR029.56: Exact quadratic amplitude factor

Task id: STR029.56 (node STR029, frontier unit).
Title: Exact quadratic amplitude factor.

Statement: with `x = (a, b)`, `θ = (h, γ)` and `F(x, θ) = J(h, γ, a cos t + b sin t + ψ(a, b, h, γ))`,
where `ψ` is the graph of STR029.16, one has `F(0, θ) = 0`, `D_x F(0, θ) = 0` and
`F(x, θ) = ∫_0^1 (1 - t) D_x² F(t x, θ)[x, x] dt`.

## Provides

* `DGPS.Frontier.STR029.str029_56_exact_quadratic_amplitude_factor`: the three statements in one
  conjunction, for every pair `(U, ψ)` with the properties of the graph of STR029.16 that are used
  and for every `x, θ` such that the segment `{(t x, θ) : t ∈ [0, 1]}` lies in `U`.
* `DGPS.Frontier.STR029.str029_56_exact_quadratic_amplitude_factor_zero`: `F(0, θ) = 0`, for
  `(0, 0, h, γ) ∈ U`.
* `DGPS.Frontier.STR029.str029_56_exact_quadratic_amplitude_factor_fderiv_zero`: `D_x F(0, θ) = 0`,
  for `(0, 0, h, γ) ∈ U`.
* `DGPS.Frontier.STR029.str029_56_exact_quadratic_amplitude_factor_graph`: the same conclusion for
  the graph `(U, ψ)` of STR029.16 itself, as an existence statement that repeats the properties of
  `(U, V, ψ)` identifying it with that graph.
* `DGPS.Frontier.STR029.Fred_STR02956`: the reduced functional `F(x, θ)`.
* `DGPS.Frontier.STR029.JC2_STR02956`: the chart functional `J(h, γ, ·)` as a function on the
  Banach space `C^{2,1/2}`, written with the smooth operations of STR029.54 and STR029.55.
* `DGPS.Frontier.STR029.JC2_smooth_STR02956`: `JC2_STR02956 h γ` is `C^∞`.

The proof does not use a Gâteaux to Fréchet upgrade. The functional `J` is a composition of the
bounded linear maps, the product and the smooth density of STR029.54 and STR029.55, hence `C^∞`
on `C^{2,1/2}`. The derivative at zero is computed from the directional derivative of STR029.50,
whose gradient vanishes at zero amplitude (STR029.12 and STR029.50). The identity is the integral
Taylor formula for `t ↦ F(t x, θ)` with vanishing value and slope at `t = 0`.

## R5 notes

* Statement issue (domain). STR029.16 gives `ψ` as a total map `ℝ⁴ → E` that is `C^∞` only on the
  open neighbourhood `U` of zero, and gives `ψ (0, 0, h, γ) = 0` only when `(0, 0, h, γ) ∈ U`.
  Therefore `F(0, θ) = 0` for every `θ` and the Taylor identity for every `x` cannot be proved
  from the Lean interface of STR029.16. The single added hypothesis is
  `hseg : ∀ t ∈ [0, 1], (t a, t b, h, γ) ∈ U`, i.e. the segment `[0, x] × {θ}` lies in the domain
  `U`. It is used for `t = 0` (the slice `(0, 0, h, γ) ∈ U`) and for the smoothness of
  `t ↦ F(t x, θ)` on `[0, 1]`. No other hypothesis is added. For the first two conclusions alone
  only `(0, 0, h, γ) ∈ U` is needed, see the `_zero` and `_fderiv_zero` lemmas.
* The properties of `ψ` used are exactly those exported by STR029.16: `U` is open, `ψ` is `C^∞` on
  `U` (`ContDiffOn ℝ ∞ ψ U`), and `ψ (0, 0, h, γ) = 0` when `(0, 0, h, γ) ∈ U`. The theorem is
  stated for every such pair `(U, ψ)`, which contains the pair given by STR029.16. The `_graph`
  corollary instantiates it with that pair.
* `F(x, θ)` is `Fred_STR02956 ψ x θ = J(h, γ, a cos t + b sin t + w)` with `w = ψ (a, b, h, γ)` and
  `J = Jchart_STR02950`, the variational chart functional of STR029.50. The chart function is
  `uT_STR02901 a b w`, as in STR029.15. `(a, b)` and `(h, γ)` are pairs of reals.
* `D_x F(0, θ)` is `fderiv ℝ (fun y => F y θ) 0`, a continuous linear form on `ℝ × ℝ`, and
  `D_x² F(t x, θ)[x, x]` is `fderiv ℝ (fderiv ℝ (fun y => F y θ)) (t • x) x x`. The integral is the
  interval integral over `[0, 1]`. On the segment `F(·, θ)` is `C^2`, so this second derivative is
  symmetric and continuous and the integrand is continuous in `t`.
* Regularity of `J`: `J` is proved `C^∞` as a map on the concrete Banach space `C^{2,1/2}` of
  STR029.69 (`JC2_smooth_STR02956`, with `JC2_eq_STR02956` identifying it with `Jchart_STR02950`),
  so that the chain rule applies to `x ↦ J(h, γ, a cos + b sin + ψ(a, b, h, γ))` on `U`.
* The common optimizer-chart predicate, the weighted carriers and the AbsoluteDensity domain are
  not used. `J` and the gradient are the variational chart quantities of STR029.49 to STR029.55.
  The Euler range map is not used: `ψ` is the graph of the variational range map (`Rpar_STR02916`,
  built from `Rvar_STR02915` of STR029.15) given by STR029.16, and `ψ` enters only through its
  regularity and its value on the slice. No angular-to-physical rate normalisation is applied.
* The vanishing at zero amplitude is checked directly: `J(h, γ, 0) = 0`, and the gradient
  `gradG_STR02950 h γ 0` vanishes pointwise, so by STR029.50 the directional derivatives of `J`
  at zero are zero.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Integral Taylor formula in one variable -/

/-- Integral form of the second-order Taylor remainder on `[0, 1]` with weight `(1 - t)`:
if `g' = g1` and `g1' = g2` on `[0, 1]` with `g2` continuous, then
`∫_0^1 (1 - t) g2 t dt = g 1 - g 0 - g1 0`. -/
theorem taylor_integral_one_STR02956 (g g1 g2 : ℝ → ℝ)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g1 (g2 t) t)
    (hg2 : ContinuousOn g2 (Set.Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, (1 - t) * g2 t = g 1 - g 0 - g1 0 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => (1 - s) * g1 s + g s) ((1 - x) * g2 x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := (hasDerivAt_id' x).const_sub 1
    have h3 := (h1.mul (hg1 x hx)).add (hg x hx)
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * g2 t) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ContinuousOn.mul (continuousOn_const.sub continuousOn_id) hg2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  show (1 - 1) * g1 1 + g 1 - ((1 - 0) * g1 0 + g 0) = g 1 - g 0 - g1 0
  ring

/-! ### The chart functional on `C^{2,1/2}` and its zero amplitude behaviour -/

/-- The chart functional `J(h, γ, u)` on `C^{2,1/2}`, written with the bounded linear maps and the
smooth density of STR029.54 and STR029.55:
`I - 2 (1 + γ) (E - log Z + log Z_h)` with `I = ∫ u'^2 ρ` and `E = ∫ u ρ`. -/
noncomputable def JC2_STR02956 (h γ : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  meanCLM_STR02954 (e1_STR02955 u * e1_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) -
    2 * (1 + γ) *
      (meanCLM_STR02954 (e0_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) -
        Real.log (Z_STR02954 (h, e0_STR02955 u)) +
        Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))))

/-- `JC2_STR02956 h γ` is `C^∞` on the Banach space `C^{2,1/2}`. -/
theorem JC2_smooth_STR02956 (h γ : ℝ) : ContDiff ℝ ∞ (JC2_STR02956 h γ) := by
  have h0 : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => e0_STR02955 u) := e0_STR02955.contDiff
  have h1 : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => e1_STR02955 u) := e1_STR02955.contDiff
  have hρ : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => rho_STR02954 (h, e0_STR02955 u)) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk h0)
  have hZ : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (h, e0_STR02955 u))) :=
    logZ_smooth_STR02954.comp (contDiff_const.prodMk h0)
  have hI : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e1_STR02955 u * e1_STR02955 u * rho_STR02954 (h, e0_STR02955 u))) :=
    meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hρ)
  have hE : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e0_STR02955 u * rho_STR02954 (h, e0_STR02955 u))) :=
    meanCLM_STR02954.contDiff.comp (h0.mul hρ)
  unfold JC2_STR02956
  exact hI.sub (contDiff_const.mul ((hE.sub hZ).add contDiff_const))

/-- `JC2_STR02956` is the chart functional `Jchart_STR02950` of the underlying function. -/
theorem JC2_eq_STR02956 (h γ : ℝ) (u : PeriodicC2_STR02969) :
    JC2_STR02956 h γ u = Jchart_STR02950 h γ u.val := by
  have hI : meanCLM_STR02954 (e1_STR02955 u * e1_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) =
      meanT_STR02901 (fun r => deriv u.val r ^ 2 * rhoT_STR02901 h u.val r) := by
    rw [meanCLM_apply_STR02954]
    congr 1
    funext r
    rw [val_mul_STR02954, val_mul_STR02954, Pi.mul_apply, Pi.mul_apply, rho_val_STR02954]
    simp only [e1_val_STR02955, e0_val_STR02955]
    ring
  have hE : meanCLM_STR02954 (e0_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) =
      meanT_STR02901 (fun r => u.val r * rhoT_STR02901 h u.val r) := by
    rw [meanCLM_apply_STR02954]
    congr 1
    funext r
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
    simp only [e0_val_STR02955]
  have hZ : Z_STR02954 (h, e0_STR02955 u) =
      meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u.val s)) :=
    Z_eq_meanT_STR02954 (h, e0_STR02955 u)
  unfold JC2_STR02956 Jchart_STR02950 fisherChart_STR02949 entropyChart_STR02949
  rw [hI, hE, hZ]

/-- The chart functional vanishes at the zero amplitude: `J(h, γ, 0) = 0`. -/
theorem Jchart_zero_STR02956 (h γ : ℝ) : Jchart_STR02950 h γ (fun _ => 0) = 0 := by
  simp [Jchart_STR02950, fisherChart_STR02949, entropyChart_STR02949, meanT_STR02901]

/-- The gradient `G` of STR029.50 vanishes at the zero amplitude, pointwise in `t`. -/
theorem gradG_zero_STR02956 (h γ t : ℝ) : gradG_STR02950 h γ (fun _ => 0) t = 0 := by
  simp [gradG_STR02950, meanT_STR02901]

theorem JC2_zero_STR02956 (h γ : ℝ) : JC2_STR02956 h γ 0 = 0 := by
  rw [JC2_eq_STR02956]
  exact Jchart_zero_STR02956 h γ

/-- The Fréchet derivative of `J(h, γ, ·)` at zero amplitude vanishes. -/
theorem fderiv_JC2_zero_STR02956 (h γ : ℝ) : fderiv ℝ (JC2_STR02956 h γ) 0 = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hd : DifferentiableAt ℝ (JC2_STR02956 h γ) 0 :=
    ((JC2_smooth_STR02956 h γ).differentiable (by simp)) 0
  have hline : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 : HasDerivAt (fun s : ℝ => JC2_STR02956 h γ (s • v))
      (fderiv ℝ (JC2_STR02956 h γ) 0 v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := str029_50_integrate_variation_compute_mean_variation h γ
    (PeriodicC2_STR02969.isC2 (0 : PeriodicC2_STR02969)) (PeriodicC2_STR02969.isC2 v)
  have hfun : (fun s : ℝ => JC2_STR02956 h γ (s • v)) = fun s : ℝ =>
      Jchart_STR02950 h γ (fun t => (0 : PeriodicC2_STR02969).val t + s * v.val t) := by
    funext s
    rw [JC2_eq_STR02956]
    congr 1
    funext t
    have h0 : (0 : PeriodicC2_STR02969).val t = 0 := rfl
    rw [h0, PeriodicC2_STR02969.val_smul]
    simp
  have hG : meanT_STR02901 (fun t => gradG_STR02950 h γ (0 : PeriodicC2_STR02969).val t * v.val t)
      = 0 := by
    have : gradG_STR02950 h γ (0 : PeriodicC2_STR02969).val = fun _ => 0 := by
      funext t
      exact gradG_zero_STR02956 h γ t
    rw [this]
    simp [meanT_STR02901]
  rw [hfun] at h1
  rw [h1.unique h2, hG]
  rfl

/-! ### The reduced functional `F(x, θ)` -/

/-- The affine embedding `y ↦ (y.1, y.2, θ.1, θ.2)` of the amplitudes `y = (a, b)` into the
parameter space `(a, b, h, γ)` of STR029.16, for fixed `θ = (h, γ)`. -/
def iota_STR02956 (θ y : ℝ × ℝ) : Par_STR02916 := (y.1, y.2, θ.1, θ.2)

theorem iota_contDiff_STR02956 (θ : ℝ × ℝ) : ContDiff ℝ ∞ (iota_STR02956 θ) := by
  unfold iota_STR02956
  exact contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))

/-- The reduced functional `F(x, θ) = J(h, γ, a cos t + b sin t + ψ(a, b, h, γ))` with `x = (a, b)`
and `θ = (h, γ)`, where `J = Jchart_STR02950` and the chart function is `uT_STR02901 a b w`. -/
noncomputable def Fred_STR02956 (ψ : Par_STR02916 → E_STR02969) (x θ : ℝ × ℝ) : ℝ :=
  Jchart_STR02950 θ.1 θ.2
    (uT_STR02901 x.1 x.2 ((ψ (x.1, x.2, θ.1, θ.2) : E_STR02969) : PeriodicC2_STR02969).val)

/-- The chart point `a cos + b sin + ψ(a, b, h, γ)` of `C^{2,1/2}`, as a function of `y = (a, b)`. -/
noncomputable def Lamp_STR02956 (ψ : Par_STR02916 → E_STR02969) (θ y : ℝ × ℝ) :
    PeriodicC2_STR02969 :=
  y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915 +
    ((ψ (iota_STR02956 θ y) : E_STR02969) : PeriodicC2_STR02969)

theorem Fred_eq_STR02956 (ψ : Par_STR02916 → E_STR02969) (y θ : ℝ × ℝ) :
    Fred_STR02956 ψ y θ = JC2_STR02956 θ.1 θ.2 (Lamp_STR02956 ψ θ y) := by
  rw [JC2_eq_STR02956]
  unfold Fred_STR02956 Lamp_STR02956 iota_STR02956
  rw [paramMap_val_STR02915]

theorem Fred_fun_eq_STR02956 (ψ : Par_STR02916 → E_STR02969) (θ : ℝ × ℝ) :
    (fun y => Fred_STR02956 ψ y θ) = JC2_STR02956 θ.1 θ.2 ∘ Lamp_STR02956 ψ θ := by
  funext y
  exact Fred_eq_STR02956 ψ y θ

theorem Lamp_contDiffOn_STR02956 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hψ : ContDiffOn ℝ ∞ ψ U) (θ : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (Lamp_STR02956 ψ θ) (iota_STR02956 θ ⁻¹' U) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y => ψ (iota_STR02956 θ y)) (iota_STR02956 θ ⁻¹' U) :=
    hψ.comp (iota_contDiff_STR02956 θ).contDiffOn (fun y hy => hy)
  have hE : ContDiffOn ℝ ∞
      (fun y : ℝ × ℝ => ((ψ (iota_STR02956 θ y) : E_STR02969) : PeriodicC2_STR02969))
      (iota_STR02956 θ ⁻¹' U) :=
    E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ
  have hlin : ContDiff ℝ ∞ (fun y : ℝ × ℝ => y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  exact hlin.contDiffOn.add hE

/-- `F(·, θ)` is `C^∞` on the open set of amplitudes whose slice lies in the domain `U` of `ψ`. -/
theorem Fred_contDiffOn_STR02956 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hψ : ContDiffOn ℝ ∞ ψ U) (θ : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun y => Fred_STR02956 ψ y θ) (iota_STR02956 θ ⁻¹' U) := by
  rw [Fred_fun_eq_STR02956]
  exact (JC2_smooth_STR02956 θ.1 θ.2).comp_contDiffOn (Lamp_contDiffOn_STR02956 hψ θ)

theorem isOpen_iota_preimage_STR02956 {U : Set Par_STR02916} (hU : IsOpen U) (θ : ℝ × ℝ) :
    IsOpen (iota_STR02956 θ ⁻¹' U) :=
  hU.preimage (iota_contDiff_STR02956 θ).continuous

theorem mem_iota_preimage_STR02956 {U : Set Par_STR02916} (θ y : ℝ × ℝ) :
    y ∈ iota_STR02956 θ ⁻¹' U ↔ ((y.1, y.2, θ.1, θ.2) : Par_STR02916) ∈ U :=
  Iff.rfl

theorem Lamp_zero_STR02956 (ψ : Par_STR02916 → E_STR02969) (θ : ℝ × ℝ)
    (h0 : ψ (0, 0, θ.1, θ.2) = 0) : Lamp_STR02956 ψ θ 0 = 0 := by
  unfold Lamp_STR02956 iota_STR02956
  simp [h0]

theorem Fred_zero_STR02956 (ψ : Par_STR02916 → E_STR02969) (θ : ℝ × ℝ)
    (h0 : ψ (0, 0, θ.1, θ.2) = 0) : Fred_STR02956 ψ 0 θ = 0 := by
  rw [Fred_eq_STR02956, Lamp_zero_STR02956 ψ θ h0]
  exact JC2_zero_STR02956 θ.1 θ.2

theorem fderiv_Fred_zero_STR02956 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (θ : ℝ × ℝ)
    (h0U : ((0, 0, θ.1, θ.2) : Par_STR02916) ∈ U) (h0 : ψ (0, 0, θ.1, θ.2) = 0) :
    fderiv ℝ (fun y => Fred_STR02956 ψ y θ) 0 = 0 := by
  have hW := isOpen_iota_preimage_STR02956 hU θ
  have h0W : (0 : ℝ × ℝ) ∈ iota_STR02956 θ ⁻¹' U := by
    rw [mem_iota_preimage_STR02956]
    simpa using h0U
  have hLd : DifferentiableAt ℝ (Lamp_STR02956 ψ θ) 0 :=
    ((Lamp_contDiffOn_STR02956 hψ θ).contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hJd : DifferentiableAt ℝ (JC2_STR02956 θ.1 θ.2) (Lamp_STR02956 ψ θ 0) :=
    ((JC2_smooth_STR02956 θ.1 θ.2).differentiable (by simp)) _
  rw [Fred_fun_eq_STR02956, fderiv_comp 0 hJd hLd, Lamp_zero_STR02956 ψ θ h0,
    fderiv_JC2_zero_STR02956]
  exact ContinuousLinearMap.zero_comp _

/-! ### The integral Taylor formula along a segment -/

/-- Integral Taylor formula for a function `F` of two variables along the segment `[0, x]`, when
`F` is `C^∞` on an open set containing the segment and `F 0 = 0`, `D F 0 = 0`. -/
theorem taylor_quad_STR02956 (F : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ)) (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) (x : ℝ × ℝ) (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ W)
    (h0 : F 0 = 0) (hd0 : fderiv ℝ F 0 = 0) :
    F x = ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  have hD2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ F)) W := hDF.fderiv_of_isOpen hW (by simp)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => F (s • x)) (fderiv ℝ F (t • x) x) t := by
    intro t ht
    have hFd : DifferentiableAt ℝ F (t • x) :=
      (hF.contDiffAt (hW.mem_nhds (hmem t ht))).differentiableAt (by simp)
    exact hFd.hasFDerivAt.comp_hasDerivAt t (hline t)
  have hg1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => fderiv ℝ F (s • x) x) (fderiv ℝ (fderiv ℝ F) (t • x) x x) t := by
    intro t ht
    have hd : DifferentiableAt ℝ (fderiv ℝ F) (t • x) :=
      (hDF.contDiffAt (hW.mem_nhds (hmem t ht))).differentiableAt (by simp)
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ F (s • x)) (fderiv ℝ (fderiv ℝ F) (t • x) x) t :=
      hd.hasFDerivAt.comp_hasDerivAt t (hline t)
    simpa using h1.clm_apply (hasDerivAt_const t x)
  have hg2 : ContinuousOn (fun s : ℝ => fderiv ℝ (fderiv ℝ F) (s • x) x x) (Set.Icc 0 1) := by
    have hcomp : ContinuousOn (fun s : ℝ => fderiv ℝ (fderiv ℝ F) (s • x)) (Set.Icc 0 1) :=
      hD2.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmem
    exact (hcomp.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hT := taylor_integral_one_STR02956 (fun s : ℝ => F (s • x))
    (fun s : ℝ => fderiv ℝ F (s • x) x) (fun s : ℝ => fderiv ℝ (fderiv ℝ F) (s • x) x x)
    hg hg1 hg2
  simp only [one_smul, zero_smul, h0, hd0, zero_apply] at hT
  rw [hT]
  ring

/-! ### The main theorem -/

/-- The value `F(0, θ)` vanishes whenever the slice point `(0, 0, h, γ)` lies in the domain `U`
of `ψ`. -/
theorem str029_56_exact_quadratic_amplitude_factor_zero
    (U : Set Par_STR02916) (ψ : Par_STR02916 → E_STR02969)
    (hψ0 : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    (θ : ℝ × ℝ) (h0U : ((0, 0, θ.1, θ.2) : Par_STR02916) ∈ U) :
    Fred_STR02956 ψ 0 θ = 0 :=
  Fred_zero_STR02956 ψ θ (hψ0 θ.1 θ.2 h0U)

/-- The derivative `D_x F(0, θ)` vanishes whenever the slice point `(0, 0, h, γ)` lies in the open
domain `U` of `ψ`. -/
theorem str029_56_exact_quadratic_amplitude_factor_fderiv_zero
    (U : Set Par_STR02916) (ψ : Par_STR02916 → E_STR02969) (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψ0 : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    (θ : ℝ × ℝ) (h0U : ((0, 0, θ.1, θ.2) : Par_STR02916) ∈ U) :
    fderiv ℝ (fun y => Fred_STR02956 ψ y θ) 0 = 0 :=
  fderiv_Fred_zero_STR02956 hU hψ θ h0U (hψ0 θ.1 θ.2 h0U)

/-- STR029.56: exact quadratic amplitude factor. For `x = (a, b)` and `θ = (h, γ)` with the segment
`{(t a, t b, h, γ) : t ∈ [0, 1]}` in the open domain `U` of the graph `ψ`: `F(0, θ) = 0`,
`D_x F(0, θ) = 0` and `F(x, θ) = ∫_0^1 (1 - t) D_x² F(t x, θ)[x, x] dt`. -/
theorem str029_56_exact_quadratic_amplitude_factor
    (U : Set Par_STR02916) (ψ : Par_STR02916 → E_STR02969) (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψ0 : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    (x θ : ℝ × ℝ)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t * x.1, t * x.2, θ.1, θ.2) : Par_STR02916) ∈ U) :
    Fred_STR02956 ψ 0 θ = 0 ∧ fderiv ℝ (fun y => Fred_STR02956 ψ y θ) 0 = 0 ∧
      Fred_STR02956 ψ x θ = ∫ t in (0 : ℝ)..1,
        (1 - t) * fderiv ℝ (fderiv ℝ (fun y => Fred_STR02956 ψ y θ)) (t • x) x x := by
  have h0U : ((0, 0, θ.1, θ.2) : Par_STR02916) ∈ U := by
    simpa using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hz := str029_56_exact_quadratic_amplitude_factor_zero U ψ hψ0 θ h0U
  have hd := str029_56_exact_quadratic_amplitude_factor_fderiv_zero U ψ hU hψ hψ0 θ h0U
  refine ⟨hz, hd, ?_⟩
  refine taylor_quad_STR02956 (fun y => Fred_STR02956 ψ y θ) (iota_STR02956 θ ⁻¹' U)
    (isOpen_iota_preimage_STR02956 hU θ) (Fred_contDiffOn_STR02956 hψ θ) x ?_ hz hd
  intro t ht
  rw [mem_iota_preimage_STR02956]
  simpa using hseg t ht

/-- The conclusion of `str029_56_exact_quadratic_amplitude_factor` for the graph `(U, ψ)` of
STR029.16 itself. -/
theorem str029_56_exact_quadratic_amplitude_factor_graph :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      (∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0) ∧
      ∀ x θ : ℝ × ℝ,
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ((t * x.1, t * x.2, θ.1, θ.2) : Par_STR02916) ∈ U) →
        Fred_STR02956 ψ 0 θ = 0 ∧ fderiv ℝ (fun y => Fred_STR02956 ψ y θ) 0 = 0 ∧
          Fred_STR02956 ψ x θ = ∫ t in (0 : ℝ)..1,
            (1 - t) * fderiv ℝ (fderiv ℝ (fun y => Fred_STR02956 ψ y θ)) (t • x) x x := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hUV, hiff, hslice, -⟩ :=
    str029_16_unique_smooth_range_graph
  exact ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hUV, hiff, hslice, fun x θ hseg =>
    str029_56_exact_quadratic_amplitude_factor U ψ hU hψ hslice x θ hseg⟩

end DGPS.Frontier.STR029
