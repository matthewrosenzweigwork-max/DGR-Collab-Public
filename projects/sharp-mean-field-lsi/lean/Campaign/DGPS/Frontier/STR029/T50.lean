import DGPS.Frontier.STR029.T49

/-!
# STR029.50: Integrate the variation and compute its mean

Task id: STR029.50 (node STR029, frontier unit, leaf formalization).
Title: Integrate the variation and compute its mean.

For a real parameter `h`, a real parameter `γ` (with `r = 1 + γ`) and `2π`-periodic functions
`u, v` of class `C^{2,1/2}`, let `ρ = ρ(h,u)`, `I = ∫ u'^2 ρ`, `E_ρ = ∫ u ρ`, where `∫` is the
normalised Haar mean, and let `J(h,γ,u) = I_h(ρ(h,u)) - 2 (1 + γ) H_h(ρ(h,u))`.  The expression
`G = ρ [-2 u'' + 6 h sin 3t u' - u'^2 - 2 r u - I + 2 r E_ρ]` of STR029.12 represents the
variation of `J`, `D_u J [v] = ∫ G v`, and has Haar mean zero, `∫ G = 0`.

## Provides

* `DGPS.Frontier.STR029.str029_50_integrate_variation_compute_mean`: one conjunction.
  (1) `s ↦ J(h,γ,u + s v)` has derivative `∫ G v` at `s = 0`.  (2) `∫ G = 0`.
* `DGPS.Frontier.STR029.str029_50_integrate_variation_compute_mean_variation`: part (1).
* `DGPS.Frontier.STR029.str029_50_integrate_variation_compute_mean_mean_zero`: part (2).
* `DGPS.Frontier.STR029.str029_50_integrate_variation_compute_mean_deriv`: the `deriv` form of
  part (1): `deriv (s ↦ J(h,γ,u + s v)) 0 = ∫ G v`.
* `DGPS.Frontier.STR029.Jchart_STR02950`: the functional `J(h,γ,u)` in the logarithmic chart.
* `DGPS.Frontier.STR029.gradG_STR02950`: the expression `G` as a function of `t`.

Auxiliary declarations carry the suffix `_STR02950`.  They give the linearity of the Haar mean
on continuous functions (`meanT_comb2_STR02950`, `meanT_comb4_STR02950`), the mean of the density
(`meanT_rho_STR02950`), the pointwise derivative of the density (`hasDerivAt_rho_STR02950`),
the vanishing of the mean of a derivative of a periodic function (`mean_ibp_STR02950`), and the
integration by parts identity that turns the first variation of STR029.49 into `∫ G v`
(`mean_variation_STR02950`).

## R5 notes

* The operator `D_u` is read as the directional (Gâteaux) derivative at `u` in the direction `v`,
  formalised as `HasDerivAt (fun s => J h γ (fun t => u t + s * v t)) (∫ G v) 0`, exactly as in
  STR029.49.  A Fréchet derivative on a bundled `C^{2,α}` space is not claimed, because the
  campaign library has no such bundled carrier at this commit.
* The carrier is the concrete predicate `IsC2Alpha_STR02901 (1 / 2)` on plain functions, with
  `α = 1/2` fixed in the node preamble.  The specification lists a Haar-mean-zero `u` and a
  mean-zero `v`; these two hypotheses are not needed, since `ρ(h,u)` is normalised for every
  `u`, `H` and `I` are defined for every `C^{2,α}` function, and the integration by parts uses
  only periodicity.  The statement is therefore proved for arbitrary `C^{2,α}` functions `u, v`
  and all real `h, γ`, which contains the mean-zero case.
* `r = 1 + γ` is written literally as `1 + γ`.  `J` is `fisherChart_STR02949 - 2 (1 + γ)
  entropyChart_STR02949`, the chart formulas of STR029.49 (`H = ∫ u ρ - log Z + log Z_h`,
  `I = ∫ u'^2 ρ`).  No identification with `ordinaryEntropy`, `ordinaryFisher` or
  `AbsoluteDensity`, and no angular-to-physical rate normalisation, is made here; the node
  preamble assigns that identification to STR029.01.
* `∫ f` is `meanT_STR02901 f`, `ρ` is `rhoT_STR02901 h u`, `u'` and `u''` are `deriv u` and
  `deriv (deriv u)`, `I = meanT (u'^2 ρ)` and `E_ρ = meanT (u ρ)` appear inside `G` as the
  closed terms of STR029.49.
* The proof follows the specification.  The density satisfies `ρ' = ρ (-3 h sin 3t + u')`, so
  the product `u' v ρ` has the derivative `u'' v ρ + u' v' ρ + u' v ρ'`, whose mean over one
  period vanishes by periodicity.  Subtracting `2 r DH[v]` from `DI[v]` of STR029.49 and using
  this identity gives `∫ G v`.  For the mean, the same identity with `v = 1` shows that `∫ G`
  equals `(I - I ∫ ρ) - 2 r (E_ρ - E_ρ ∫ ρ)`, which vanishes because `∫ ρ = 1`.
-/

namespace DGPS.Frontier.STR029

/-- The functional `J(h,γ,u) = I_h(ρ(h,u)) - 2 (1 + γ) H_h(ρ(h,u))` in the logarithmic chart. -/
noncomputable def Jchart_STR02950 (h γ : ℝ) (u : ℝ → ℝ) : ℝ :=
  fisherChart_STR02949 h u - 2 * (1 + γ) * entropyChart_STR02949 h u

/-- The expression `G = ρ [-2 u'' + 6 h sin 3t u' - u'^2 - 2 r u - I + 2 r E_ρ]` with `r = 1 + γ`,
`I = ∫ u'^2 ρ` and `E_ρ = ∫ u ρ`. -/
noncomputable def gradG_STR02950 (h γ : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  rhoT_STR02901 h u t *
    (-2 * deriv (deriv u) t + 6 * h * Real.sin (3 * t) * deriv u t - deriv u t ^ 2 -
      2 * (1 + γ) * u t -
      meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r) +
      2 * (1 + γ) * meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r))

/-- Linearity of the Haar mean on two continuous functions. -/
theorem meanT_comb2_STR02950 {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (a b : ℝ) :
    meanT_STR02901 (fun t => a * A t + b * B t) =
      a * meanT_STR02901 A + b * meanT_STR02901 B := by
  have e : (fun t => a * A t + b * B t) = a • A + b • B := by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have c1 : Continuous (a • A) := hA.const_smul a
  have c2 : Continuous (b • B) := hB.const_smul b
  rw [e, meanT_add_STR02953 c1 c2, meanT_smul_STR02953, meanT_smul_STR02953]

/-- Linearity of the Haar mean on four continuous functions. -/
theorem meanT_comb4_STR02950 {A B C D : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) (a b c d : ℝ) :
    meanT_STR02901 (fun t => a * A t + b * B t + c * C t + d * D t) =
      a * meanT_STR02901 A + b * meanT_STR02901 B + c * meanT_STR02901 C +
        d * meanT_STR02901 D := by
  have e : (fun t => a * A t + b * B t + c * C t + d * D t) =
      (fun t => (a * A t + b * B t) + c * C t) + d • D := by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have c1 : Continuous (fun t => (a * A t + b * B t) + c * C t) := by fun_prop
  have c2 : Continuous (d • D) := hD.const_smul d
  have e1 : (fun t => (a * A t + b * B t) + c * C t) =
      (fun t => 1 * (a * A t + b * B t) + c * C t) := by
    funext t
    ring
  have c3 : Continuous (fun t => a * A t + b * B t) := by fun_prop
  rw [e, meanT_add_STR02953 c1 c2, meanT_smul_STR02953, e1,
    meanT_comb2_STR02950 c3 hC 1 c, meanT_comb2_STR02950 hA hB a b]
  ring

/-- The density `ρ(h,u)` is continuous. -/
theorem continuous_rho_STR02950 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (rhoT_STR02901 h u) := by
  unfold rhoT_STR02901
  fun_prop

/-- The density `ρ(h,u)` has Haar mean one. -/
theorem meanT_rho_STR02950 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    meanT_STR02901 (rhoT_STR02901 h u) = 1 := by
  have hZ : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) :=
    meanT_pos_STR02901 (by fun_prop) (fun s => Real.exp_pos _)
  have e : rhoT_STR02901 h u =
      (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)))⁻¹ •
        (fun s => Real.exp (h * Real.cos (3 * s) + u s)) := by
    funext t
    simp only [rhoT_STR02901, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  rw [e, meanT_smul_STR02953, inv_mul_cancel₀ hZ.ne']

/-- The density `ρ(h,u)` is `2π`-periodic when `u` is. -/
theorem periodic_rho_STR02950 (h : ℝ) {u : ℝ → ℝ} (hu : Function.Periodic u (2 * Real.pi)) :
    Function.Periodic (rhoT_STR02901 h u) (2 * Real.pi) := by
  intro t
  have hc : Real.cos (3 * (t + 2 * Real.pi)) = Real.cos (3 * t) := by
    have := Real.cos_add_nat_mul_two_pi (3 * t) 3
    rw [show 3 * (t + 2 * Real.pi) = 3 * t + ((3 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact this
  simp only [rhoT_STR02901, hc, hu t]

/-- Pointwise derivative of the density: `ρ' = ρ (-3 h sin 3t + u')`. -/
theorem hasDerivAt_rho_STR02950 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (t : ℝ) :
    HasDerivAt (rhoT_STR02901 h u)
      (rhoT_STR02901 h u t * (-(3 * h * Real.sin (3 * t)) + deriv u t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.cos (3 * s)) (-Real.sin (3 * t) * 3) t := by
    simpa using ((hasDerivAt_id' t).const_mul (3 : ℝ)).cos
  have h2 := ((h1.const_mul h).add (hu.2.1 t).hasDerivAt).exp
  have h3 := h2.div_const (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)))
  refine h3.congr_deriv ?_
  simp only [rhoT_STR02901, Pi.add_apply]
  ring

/-- The mean over one period of the derivative of `u' v ρ` vanishes, by periodicity. -/
theorem mean_ibp_STR02950 (h : ℝ) {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hvp : Function.Periodic v (2 * Real.pi)) (hvd : Differentiable ℝ v)
    (hvc : Continuous (deriv v)) :
    meanT_STR02901 (fun t => deriv (deriv u) t * v t * rhoT_STR02901 h u t +
      deriv u t * deriv v t * rhoT_STR02901 h u t +
      deriv u t * v t * (rhoT_STR02901 h u t * (-(3 * h * Real.sin (3 * t)) + deriv u t))) =
        0 := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hu1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hu2 : Continuous (deriv (deriv u)) := hu.2.2.2.1
  have hv0 : Continuous v := hvd.continuous
  have hR : Continuous (rhoT_STR02901 h u) := continuous_rho_STR02950 h hu0
  have hder : ∀ x, HasDerivAt (fun t => deriv u t * v t * rhoT_STR02901 h u t)
      (deriv (deriv u) x * v x * rhoT_STR02901 h u x +
        deriv u x * deriv v x * rhoT_STR02901 h u x +
        deriv u x * v x * (rhoT_STR02901 h u x * (-(3 * h * Real.sin (3 * x)) + deriv u x))) x := by
    intro x
    have d1 : HasDerivAt (deriv u) (deriv (deriv u) x) x := (hu.2.2.1 x).hasDerivAt
    have d2 : HasDerivAt v (deriv v x) x := (hvd x).hasDerivAt
    have d3 := hasDerivAt_rho_STR02950 h hu x
    refine ((d1.mul d2).mul d3).congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hcont : Continuous (fun t => deriv (deriv u) t * v t * rhoT_STR02901 h u t +
      deriv u t * deriv v t * rhoT_STR02901 h u t +
      deriv u t * v t * (rhoT_STR02901 h u t * (-(3 * h * Real.sin (3 * t)) + deriv u t))) := by
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * Real.pi)
    (fun x _ => hder x) (hcont.intervalIntegrable _ _)
  have hp1 : deriv u (2 * Real.pi) = deriv u 0 := by
    simpa using (periodic_deriv_STR02901 hu.1) 0
  have hp2 : v (2 * Real.pi) = v 0 := by simpa using hvp 0
  have hp3 : rhoT_STR02901 h u (2 * Real.pi) = rhoT_STR02901 h u 0 := by
    simpa using periodic_rho_STR02950 h hu.1 0
  unfold meanT_STR02901
  rw [hint]
  simp only [hp1, hp2, hp3, sub_self, mul_zero]

/-- Integration by parts: the mean of `G v` equals `2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v -
2 r ∫ ρ (u - E_ρ) v`, the variation of `J` given by STR029.49. -/
theorem mean_variation_STR02950 (h γ : ℝ) {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hvp : Function.Periodic v (2 * Real.pi)) (hvd : Differentiable ℝ v)
    (hvc : Continuous (deriv v)) :
    meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t) =
      2 * meanT_STR02901 (fun t => deriv u t * deriv v t * rhoT_STR02901 h u t) +
        meanT_STR02901 (fun t => rhoT_STR02901 h u t *
          (deriv u t ^ 2 - meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)) *
            v t) -
        2 * (1 + γ) * meanT_STR02901 (fun t => rhoT_STR02901 h u t *
          (u t - meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)) * v t) := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hu1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hu2 : Continuous (deriv (deriv u)) := hu.2.2.2.1
  have hv0 : Continuous v := hvd.continuous
  have hR : Continuous (rhoT_STR02901 h u) := continuous_rho_STR02950 h hu0
  have hibp := mean_ibp_STR02950 h hu hvp hvd hvc
  set I := meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r) with hI
  set E := meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r) with hE
  have e : (fun t => gradG_STR02950 h γ u t * v t) =
      fun t => 2 * (deriv u t * deriv v t * rhoT_STR02901 h u t) +
        1 * (rhoT_STR02901 h u t * (deriv u t ^ 2 - I) * v t) +
        (-(2 * (1 + γ))) * (rhoT_STR02901 h u t * (u t - E) * v t) +
        (-2) * (deriv (deriv u) t * v t * rhoT_STR02901 h u t +
          deriv u t * deriv v t * rhoT_STR02901 h u t +
          deriv u t * v t * (rhoT_STR02901 h u t * (-(3 * h * Real.sin (3 * t)) +
            deriv u t))) := by
    funext t
    simp only [gradG_STR02950, ← hI, ← hE]
    ring
  rw [e, meanT_comb4_STR02950 (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop), hibp]
  ring

/-- Part (1): the expression `G` represents the variation of `J`,
`D_u J [v] = ∫ G v`, as a directional derivative at `s = 0`. -/
theorem str029_50_integrate_variation_compute_mean_variation (h γ : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    HasDerivAt (fun s : ℝ => Jchart_STR02950 h γ (fun t => u t + s * v t))
      (meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t)) 0 := by
  obtain ⟨hE, hF⟩ := str029_49_first_variations_entropy_fisher_information h hu hv
  have key := hF.sub (hE.const_mul (2 * (1 + γ)))
  refine key.congr_deriv ?_
  rw [mean_variation_STR02950 h γ hu hv.1 hv.2.1 hv.2.2.1.continuous]

/-- Part (2): `G` has Haar mean zero. -/
theorem str029_50_integrate_variation_compute_mean_mean_zero (h γ : ℝ) {u : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    meanT_STR02901 (gradG_STR02950 h γ u) = 0 := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hu1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hR : Continuous (rhoT_STR02901 h u) := continuous_rho_STR02950 h hu0
  have h1 := mean_variation_STR02950 h γ (v := fun _ => (1 : ℝ)) hu (fun _ => rfl)
    (differentiable_const 1) (by rw [deriv_const']; exact continuous_const)
  have hρ := meanT_rho_STR02950 h hu0
  set I := meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r) with hI
  set E := meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r) with hE
  have e0 : (fun t => gradG_STR02950 h γ u t * (fun _ : ℝ => (1 : ℝ)) t) =
      gradG_STR02950 h γ u := by
    funext t
    simp only [mul_one]
  have eI : (fun t => rhoT_STR02901 h u t * (deriv u t ^ 2 - I) * (fun _ : ℝ => (1 : ℝ)) t) =
      fun t => 1 * (deriv u t ^ 2 * rhoT_STR02901 h u t) + (-I) * rhoT_STR02901 h u t := by
    funext t
    ring
  have eE : (fun t => rhoT_STR02901 h u t * (u t - E) * (fun _ : ℝ => (1 : ℝ)) t) =
      fun t => 1 * (u t * rhoT_STR02901 h u t) + (-E) * rhoT_STR02901 h u t := by
    funext t
    ring
  have e1 : (fun t => deriv u t * deriv (fun _ : ℝ => (1 : ℝ)) t * rhoT_STR02901 h u t) =
      fun _ => (0 : ℝ) := by
    funext t
    simp
  rw [e0, eI, eE, e1, meanT_comb2_STR02950 (by fun_prop) hR,
    meanT_comb2_STR02950 (by fun_prop) hR, hρ] at h1
  have hz : meanT_STR02901 (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [meanT_STR02901]
  rw [hz, ← hI, ← hE] at h1
  linarith

/-- Integrate the variation and compute its mean.  For `C^{2,1/2}` functions `u, v`, the
expression `G` of STR029.12 represents the variation of `J(h,γ,·)` at `u` in the direction `v`,
`D_u J [v] = ∫ G v`, and `∫ G = 0`. -/
theorem str029_50_integrate_variation_compute_mean (h γ : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    HasDerivAt (fun s : ℝ => Jchart_STR02950 h γ (fun t => u t + s * v t))
        (meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t)) 0 ∧
      meanT_STR02901 (gradG_STR02950 h γ u) = 0 :=
  ⟨str029_50_integrate_variation_compute_mean_variation h γ hu hv,
    str029_50_integrate_variation_compute_mean_mean_zero h γ hu⟩

/-- The `deriv` form of part (1): `deriv (s ↦ J(h,γ,u + s v)) 0 = ∫ G v`. -/
theorem str029_50_integrate_variation_compute_mean_deriv (h γ : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    deriv (fun s : ℝ => Jchart_STR02950 h γ (fun t => u t + s * v t)) 0 =
      meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t) :=
  (str029_50_integrate_variation_compute_mean_variation h γ hu hv).deriv

end DGPS.Frontier.STR029
