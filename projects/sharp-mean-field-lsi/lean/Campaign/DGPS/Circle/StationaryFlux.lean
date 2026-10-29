import DGPS.Circle.AngularNormalization
/-!
# Periodic stationary flux vanishes (EX005)

On the angular circle `AngCircle = AddCircle (2π)` with normalized Haar measure `angHaar`, let `U`
be a smooth periodic potential. Any probability measure `ν` solving
`∂θ(∂θ ν + U' ν) = 0` in the sense of distributions (tested against smooth periodic `ψ`:
`∫ (ψ'' - U' ψ') dν = 0`) is the smooth strictly positive Gibbs density
`exp (-U) / ∫ exp (-U)` with respect to `angHaar`. No `H¹` regularity of `ν` is assumed.

Proof: a smooth mean-zero periodic function is a derivative of a smooth periodic function
(`exists_antideriv`), so the flux `j` is a constant (`flux_identity`); testing `e^U` forces `j = 0`;
then `e^U ν` has zero derivative, hence is a Haar multiple (`measure_eq_smul_haar`, using that
smooth functions determine finite measures, `measure_ext_of_smooth`).
-/
open MeasureTheory Real
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Circle.StationaryFlux

/-- Real-line lift of a function on the angular circle. -/
noncomputable def lift (ψ : AngCircle → ℝ) : ℝ → ℝ := fun s => ψ (s : AngCircle)

theorem lift_periodic (ψ : AngCircle → ℝ) : Function.Periodic (lift ψ) (2 * π) := fun s => by
  simp [lift]

theorem exists_coe (θ : AngCircle) : ∃ s : ℝ, (s : AngCircle) = θ :=
  QuotientAddGroup.mk_surjective θ

theorem coe_angSec (θ : AngCircle) : ((angSec θ : ℝ) : AngCircle) = θ := by
  unfold angSec; exact AddCircle.coe_equivIoc

theorem periodic_deriv {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π)) :
    Function.Periodic (deriv f) (2 * π) := fun x => by
  have h : (fun y => f (y + 2 * π)) = f := funext hf
  have := deriv_comp_add_const (f := f) (a := 2 * π) (x := x)
  rw [h] at this
  exact this.symm

theorem angDeriv_coe (ψ : AngCircle → ℝ) (s : ℝ) :
    angDeriv ψ (s : AngCircle) = deriv (lift ψ) s := by
  unfold angDeriv
  have h : (((angSec (s : AngCircle) : ℝ) - s : ℝ) : AngCircle) = 0 := by
    rw [AddCircle.coe_sub, coe_angSec, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have : angSec (s : AngCircle) = s + n * (2 * π) := by
    rw [zsmul_eq_mul] at hn; linarith
  show deriv (lift ψ) _ = _
  rw [this]
  exact (periodic_deriv (lift_periodic ψ)).int_mul n s



theorem isSmooth_iff (ψ : AngCircle → ℝ) : IsSmoothAngular ψ ↔ ContDiff ℝ ∞ (lift ψ) := Iff.rfl

theorem continuous_of_smooth {ψ : AngCircle → ℝ} (h : IsSmoothAngular ψ) : Continuous ψ := by
  have hq : Topology.IsQuotientMap ((↑) : ℝ → AngCircle) := QuotientAddGroup.isQuotientMap_mk _
  exact hq.continuous_iff.2 h.continuous

theorem lift_angDeriv (ψ : AngCircle → ℝ) :
    lift (angDeriv ψ) = deriv (lift ψ) := funext fun s => angDeriv_coe ψ s

theorem smooth_angDeriv {ψ : AngCircle → ℝ} (h : IsSmoothAngular ψ) :
    IsSmoothAngular (angDeriv ψ) := by
  rw [isSmooth_iff, lift_angDeriv]
  exact (contDiff_infty_iff_deriv.1 h).2

theorem hasDerivAt_lift {ψ : AngCircle → ℝ} (h : IsSmoothAngular ψ) (s : ℝ) :
    HasDerivAt (lift ψ) (angDeriv ψ (s : AngCircle)) s := by
  rw [angDeriv_coe]
  exact ((contDiff_infty_iff_deriv.1 h).1 s).hasDerivAt

theorem angDeriv_eq_of_hasDerivAt {ψ g : AngCircle → ℝ}
    (h : ∀ s : ℝ, HasDerivAt (lift ψ) (g (s : AngCircle)) s) : angDeriv ψ = g := by
  funext θ
  obtain ⟨s, rfl⟩ := exists_coe θ
  rw [angDeriv_coe, (h s).deriv]

theorem smooth_mul {f g : AngCircle → ℝ} (hf : IsSmoothAngular f) (hg : IsSmoothAngular g) :
    IsSmoothAngular (fun θ => f θ * g θ) := hf.mul hg

theorem angDeriv_mul {f g : AngCircle → ℝ} (hf : IsSmoothAngular f) (hg : IsSmoothAngular g) :
    angDeriv (fun θ => f θ * g θ) = fun θ => angDeriv f θ * g θ + f θ * angDeriv g θ := by
  refine angDeriv_eq_of_hasDerivAt fun s => ?_
  exact (hasDerivAt_lift hf s).mul (hasDerivAt_lift hg s)

theorem smooth_exp {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    IsSmoothAngular (fun θ => Real.exp (f θ)) := Real.contDiff_exp.comp hf

theorem angDeriv_exp {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    angDeriv (fun θ => Real.exp (f θ)) = fun θ => Real.exp (f θ) * angDeriv f θ := by
  refine angDeriv_eq_of_hasDerivAt fun s => ?_
  exact (hasDerivAt_lift hf s).exp

theorem smooth_const (c : ℝ) : IsSmoothAngular (fun _ : AngCircle => c) := contDiff_const

theorem angDeriv_const (c : ℝ) : angDeriv (fun _ : AngCircle => c) = fun _ => 0 := by
  refine angDeriv_eq_of_hasDerivAt fun s => ?_
  exact hasDerivAt_const s c

theorem smooth_sub {f g : AngCircle → ℝ} (hf : IsSmoothAngular f) (hg : IsSmoothAngular g) :
    IsSmoothAngular (fun θ => f θ - g θ) := hf.sub hg

theorem smooth_neg {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    IsSmoothAngular (fun θ => - f θ) := hf.neg


theorem integrable_of_smooth {μ : Measure AngCircle} [IsFiniteMeasure μ] {f : AngCircle → ℝ}
    (hf : IsSmoothAngular f) : Integrable f μ :=
  (continuous_of_smooth hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integral_lift_period (φ : AngCircle → ℝ) :
    ∫ x in (0 : ℝ)..2 * π, lift φ x = 2 * π * ∫ θ, φ θ ∂angHaar := by
  have h := AddCircle.intervalIntegral_preimage (2 * π) 0 φ
  rw [zero_add] at h
  have h2 : ∫ b : AngCircle, φ b = 2 * π * ∫ θ, φ θ ∂angHaar := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
      ENNReal.toReal_ofReal Real.two_pi_pos.le]
    rfl
  exact h.trans h2

theorem exists_antideriv {φ : AngCircle → ℝ} (hφ : IsSmoothAngular φ)
    (h0 : ∫ θ, φ θ ∂angHaar = 0) : ∃ ψ, IsSmoothAngular ψ ∧ angDeriv ψ = φ := by
  have hc : Continuous (lift φ) := hφ.continuous
  set G : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..s, lift φ x with hG
  have hper : Function.Periodic G (2 * π) := by
    intro s
    have h1 : G (s + 2 * π) = G s + ∫ x in s..s + 2 * π, lift φ x :=
      (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)).symm
    have h2 : ∫ x in s..s + 2 * π, lift φ x = ∫ x in (0 : ℝ)..0 + 2 * π, lift φ x :=
      (lift_periodic φ).intervalIntegral_add_eq s 0
    rw [h1, h2, zero_add, integral_lift_period, h0]
    simp
  have hD : ∀ s, HasDerivAt G (lift φ s) s := fun s => (hc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hl : lift (hper.lift) = G := funext fun s => hper.lift_coe s
  refine ⟨hper.lift, ?_, ?_⟩
  · rw [isSmooth_iff, hl]
    refine contDiff_infty_iff_deriv.2 ⟨fun s => (hD s).differentiableAt, ?_⟩
    have : deriv G = lift φ := funext fun s => (hD s).deriv
    rw [this]; exact hφ
  · refine angDeriv_eq_of_hasDerivAt fun s => ?_
    rw [hl]; exact hD s

open Complex in
theorem smooth_dense (f : AngCircle → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : AngCircle → ℝ, IsSmoothAngular h ∧ ∀ θ, |f θ - h θ| < ε := by
  let F : C(AngCircle, ℂ) := ⟨fun θ => (f θ : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hmem : F ∈ closure (Submodule.span ℂ (Set.range (fourier (T := 2 * π))) : Set C(AngCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]; trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  have hsm : ∀ g ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * π))),
      ContDiff ℝ ∞ (fun s : ℝ => g (s : AngCircle)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      simp only [fourier_coe_apply]
      have hco : ContDiff ℝ ∞ (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
      exact Complex.contDiff_exp.comp ((contDiff_const.mul hco).div_const _)
    | zero => exact contDiff_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  refine ⟨fun θ => (g θ).re, ?_, fun θ => ?_⟩
  · exact Complex.reCLM.contDiff.comp (hsm g hg)
  · have h1 : dist (F θ) (g θ) ≤ dist F g := ContinuousMap.dist_apply_le_dist θ
    have h2 : f θ - (g θ).re = (F θ - g θ).re := by simp [F]
    rw [h2]
    exact lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans (by rw [← dist_eq_norm]; exact h1)) hdist


theorem measure_ext_of_smooth {μ₁ μ₂ : Measure AngCircle} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂]
    (h : ∀ f, IsSmoothAngular f → ∫ θ, f θ ∂μ₁ = ∫ θ, f θ ∂μ₂) : μ₁ = μ₂ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have approx : ∀ (μ : Measure AngCircle) [IsFiniteMeasure μ] (g : AngCircle → ℝ)
      (hg : IsSmoothAngular g) (ε : ℝ), (∀ θ, |f θ - g θ| < ε) →
      |∫ θ, f θ ∂μ - ∫ θ, g θ ∂μ| ≤ ε * μ.real Set.univ := by
    intro μ _ g hg ε hε
    rw [← integral_sub (f.integrable μ) (integrable_of_smooth hg)]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun θ => f θ - g θ) (C := ε)
      (Filter.Eventually.of_forall fun θ => (hε θ).le)
    simpa using this
  set C := μ₁.real Set.univ + μ₂.real Set.univ with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ ε > 0, |∫ θ, f θ ∂μ₁ - ∫ θ, f θ ∂μ₂| ≤ ε * C := by
    intro ε hε
    obtain ⟨g, hg, hlt⟩ := smooth_dense f f.continuous hε
    have h1 := approx μ₁ g hg ε hlt
    have h2 := approx μ₂ g hg ε hlt
    rw [h g hg] at h1
    have : ∫ θ, f θ ∂μ₁ - ∫ θ, f θ ∂μ₂ =
        (∫ θ, f θ ∂μ₁ - ∫ θ, g θ ∂μ₂) - (∫ θ, f θ ∂μ₂ - ∫ θ, g θ ∂μ₂) := by ring
    rw [this, hC, mul_add]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  by_contra hne
  have hpos : 0 < |∫ θ, f θ ∂μ₁ - ∫ θ, f θ ∂μ₂| := abs_pos.2 (sub_ne_zero.2 hne)
  have := key (|∫ θ, f θ ∂μ₁ - ∫ θ, f θ ∂μ₂| / (C + 1)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

theorem measure_eq_smul_haar (μ : Measure AngCircle) [IsFiniteMeasure μ]
    (h : ∀ ψ, IsSmoothAngular ψ → ∫ θ, angDeriv ψ θ ∂μ = 0) :
    μ = ENNReal.ofReal (μ.real Set.univ) • angHaar := by
  have : IsFiniteMeasure (ENNReal.ofReal (μ.real Set.univ) • angHaar) :=
    ⟨by simp [Measure.smul_apply]⟩
  apply measure_ext_of_smooth
  intro φ hφ
  set m := ∫ θ, φ θ ∂angHaar with hm
  have hφm : IsSmoothAngular (fun θ => φ θ - m) := smooth_sub hφ (smooth_const m)
  have h0 : ∫ θ, (φ θ - m) ∂angHaar = 0 := by
    rw [integral_sub (integrable_of_smooth hφ) (integrable_const _)]; simp [hm]
  obtain ⟨ψ, hψ, hψd⟩ := exists_antideriv hφm h0
  have := h ψ hψ
  rw [hψd, integral_sub (integrable_of_smooth hφ) (integrable_const _)] at this
  rw [integral_smul_measure, ENNReal.toReal_ofReal measureReal_nonneg]
  simp only [integral_const, smul_eq_mul] at this ⊢
  nlinarith


/-- Claim 1 of the integrating-factor argument: the flux functional on `e^U g`. -/
theorem flux_identity {U : AngCircle → ℝ} (hU : IsSmoothAngular U) (ν : Measure AngCircle)
    [IsFiniteMeasure ν]
    (hν : ∀ ψ, IsSmoothAngular ψ →
      ∫ θ, (angDeriv (angDeriv ψ) θ - angDeriv U θ * angDeriv ψ θ) ∂ν = 0)
    {g : AngCircle → ℝ} (hg : IsSmoothAngular g) :
    ∫ θ, Real.exp (U θ) * angDeriv g θ ∂ν =
      (∫ θ, Real.exp (U θ) * g θ ∂angHaar) * (- ∫ θ, angDeriv U θ ∂ν) := by
  have hU' := smooth_angDeriv hU
  have hφ : IsSmoothAngular (fun θ => Real.exp (U θ) * g θ) := smooth_mul (smooth_exp hU) hg
  set m := ∫ θ, Real.exp (U θ) * g θ ∂angHaar with hm
  have hφm : IsSmoothAngular (fun θ => Real.exp (U θ) * g θ - m) := smooth_sub hφ (smooth_const m)
  have h0 : ∫ θ, (Real.exp (U θ) * g θ - m) ∂angHaar = 0 := by
    rw [integral_sub (integrable_of_smooth hφ) (integrable_const _)]; simp [hm]
  obtain ⟨ψ, hψ, hψd⟩ := exists_antideriv hφm h0
  have h1 := hν ψ hψ
  have hd : angDeriv (fun θ => Real.exp (U θ) * g θ - m) = fun θ =>
      Real.exp (U θ) * angDeriv U θ * g θ + Real.exp (U θ) * angDeriv g θ := by
    refine angDeriv_eq_of_hasDerivAt fun s => ?_
    have := (hasDerivAt_lift hφ s).sub_const m
    rw [angDeriv_mul (smooth_exp hU) hg, angDeriv_exp hU] at this
    exact this
  have hdd : angDeriv (angDeriv ψ) = fun θ =>
      Real.exp (U θ) * angDeriv U θ * g θ + Real.exp (U θ) * angDeriv g θ := by
    rw [hψd, hd]
  have hpt : ∀ θ, angDeriv (angDeriv ψ) θ - angDeriv U θ * angDeriv ψ θ =
      Real.exp (U θ) * angDeriv g θ + m * angDeriv U θ := by
    intro θ
    rw [hdd, hψd]
    ring
  simp_rw [hpt] at h1
  have hi1 : Integrable (fun θ => Real.exp (U θ) * angDeriv g θ) ν :=
    integrable_of_smooth (smooth_mul (smooth_exp hU) (smooth_angDeriv hg))
  have hi2 : Integrable (fun θ => m * angDeriv U θ) ν := (integrable_of_smooth hU').const_mul m
  rw [integral_add hi1 hi2, integral_const_mul] at h1
  linarith


theorem stationary_eq_gibbs {U : AngCircle → ℝ} (hU : IsSmoothAngular U) (ν : Measure AngCircle)
    [IsProbabilityMeasure ν]
    (hν : ∀ ψ, IsSmoothAngular ψ →
      ∫ θ, (angDeriv (angDeriv ψ) θ - angDeriv U θ * angDeriv ψ θ) ∂ν = 0) :
    ν = angHaar.withDensity
      (fun θ => ENNReal.ofReal (Real.exp (-U θ) / ∫ x, Real.exp (-U x) ∂angHaar)) := by
  have hexpU := smooth_exp hU
  have hexpN := smooth_exp (smooth_neg hU)
  have hm : 0 < ∫ θ, Real.exp (U θ) ∂angHaar := integral_exp_pos (integrable_of_smooth hexpU)
  have hZ : 0 < ∫ θ, Real.exp (-U θ) ∂angHaar := integral_exp_pos (integrable_of_smooth hexpN)
  have h1 := flux_identity hU ν hν (smooth_const 1)
  rw [angDeriv_const] at h1
  simp only [mul_zero, integral_zero, mul_one] at h1
  have hc0 : (- ∫ θ, angDeriv U θ ∂ν) = 0 := by
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd h hm.ne'
    · exact h
  have hflux : ∀ g, IsSmoothAngular g → ∫ θ, Real.exp (U θ) * angDeriv g θ ∂ν = 0 := by
    intro g hg
    rw [flux_identity hU ν hν hg, hc0, mul_zero]
  have hmeasU : Measurable fun θ => Real.exp (U θ) :=
    (continuous_of_smooth hexpU).measurable
  have hmeasN : Measurable fun θ => Real.exp (-U θ) :=
    (continuous_of_smooth hexpN).measurable
  have hmU : Measurable fun θ => ENNReal.ofReal (Real.exp (U θ)) :=
    ENNReal.measurable_ofReal.comp hmeasU
  have hmN : Measurable fun θ => ENNReal.ofReal (Real.exp (-U θ)) :=
    ENNReal.measurable_ofReal.comp hmeasN
  set μ : Measure AngCircle := ν.withDensity (fun θ => ENNReal.ofReal (Real.exp (U θ))) with hμdef
  have hμfin : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity_ofReal (integrable_of_smooth hexpU).2
  have hμ : ∀ ψ, IsSmoothAngular ψ → ∫ θ, angDeriv ψ θ ∂μ = 0 := by
    intro ψ hψ
    rw [hμdef, integral_withDensity_eq_integral_toReal_smul₀
      hmU.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    exact hflux ψ hψ
  have hμeq := measure_eq_smul_haar μ hμ
  set k := μ.real Set.univ with hk
  have hk0 : 0 ≤ k := measureReal_nonneg
  have hνμ : ν = μ.withDensity (fun θ => ENNReal.ofReal (Real.exp (-U θ))) := by
    rw [hμdef, ← withDensity_mul _ hmU hmN]
    have : ((fun θ => ENNReal.ofReal (Real.exp (U θ))) * fun θ => ENNReal.ofReal (Real.exp (-U θ)))
        = 1 := by
      funext θ
      simp only [Pi.mul_apply, Pi.one_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    rw [this, withDensity_one]
  have hνk : ν = angHaar.withDensity (fun θ => ENNReal.ofReal (k * Real.exp (-U θ))) := by
    have e : (fun θ => ENNReal.ofReal (k * Real.exp (-U θ))) =
        ENNReal.ofReal k • (fun θ => ENNReal.ofReal (Real.exp (-U θ))) := by
      funext θ
      simp [ENNReal.ofReal_mul hk0]
    rw [e, withDensity_smul _ hmN, ← withDensity_smul_measure,
      ← hμeq]
    exact hνμ
  have hnorm : k * ∫ θ, Real.exp (-U θ) ∂angHaar = 1 := by
    have h2 : ν Set.univ = 1 := measure_univ
    rw [hνk, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ((integrable_of_smooth hexpN).const_mul k)
        (Filter.Eventually.of_forall fun θ => by positivity),
      integral_const_mul] at h2
    exact (ENNReal.ofReal_eq_one.1 h2)
  have hk' : k = (∫ θ, Real.exp (-U θ) ∂angHaar)⁻¹ := by
    field_simp; linarith
  rw [hνk]
  congr 1
  funext θ
  rw [hk', div_eq_inv_mul]

end DGPS.Circle.StationaryFlux

open MeasureTheory
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples

/-- EX005: for a smooth periodic potential `U` on the angular circle, every probability measure
`ν` with `∂θ(∂θ ν + U' ν) = 0` distributionally (`∫ (ψ'' - U' ψ') dν = 0` for all smooth periodic
`ψ`) is the smooth strictly positive normalized Gibbs density `exp (-U) / ∫ exp (-U)` with respect
to normalized Haar measure `angHaar`. No `H¹` density is presupposed. -/
theorem periodic_stationary_flux_vanishes (U : AngCircle → ℝ) (hU : IsSmoothAngular U)
    (ν : ProbabilityMeasure AngCircle)
    (hν : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
      ∫ θ, (angDeriv (angDeriv ψ) θ - angDeriv U θ * angDeriv ψ θ) ∂(ν : Measure AngCircle) = 0) :
    ∃ ρ : AngCircle → ℝ, IsSmoothAngular ρ ∧ (∀ θ, 0 < ρ θ) ∧
      (∀ θ, ρ θ = Real.exp (-U θ) / ∫ x, Real.exp (-U x) ∂angHaar) ∧
      (ν : Measure AngCircle) = angHaar.withDensity (fun θ => ENNReal.ofReal (ρ θ)) := by
  have hZ : 0 < ∫ θ, Real.exp (-U θ) ∂angHaar :=
    integral_exp_pos (DGPS.Circle.StationaryFlux.integrable_of_smooth
      (DGPS.Circle.StationaryFlux.smooth_exp (DGPS.Circle.StationaryFlux.smooth_neg hU)))
  refine ⟨fun θ => Real.exp (-U θ) / ∫ x, Real.exp (-U x) ∂angHaar, ?_, fun θ => ?_,
    fun _ => rfl, ?_⟩
  · exact (DGPS.Circle.StationaryFlux.smooth_exp
      (DGPS.Circle.StationaryFlux.smooth_neg hU)).div_const _
  · exact div_pos (Real.exp_pos _) hZ
  · exact DGPS.Circle.StationaryFlux.stationary_eq_gibbs hU (ν : Measure AngCircle) hν

end DGPS.Examples
