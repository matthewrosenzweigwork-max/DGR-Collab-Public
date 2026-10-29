import DGPS.Circle.QuantitativeLSI
import DGPS.Foundations.RelativeEntropy
import DGPS.Model.FreeEnergy
import DGPS.Equilibrium.GaussianRate
/-!
# Angular to physical normalization (EX001)

The angular circle `AddCircle (2π)` with normalized Haar measure `dθ/(2π)` is identified with the
unit-period torus `Torus 1` by `θ = 2π x` (`angEquiv`). The map is measure preserving, transports
smooth tests and weak derivatives (the physical gradient is `2π` times the angular derivative),
and gives the main theorem `DGPS.Examples.angular_to_physical_normalization`: entropy, feature
means and free-energy gaps are invariant; Dirichlet forms, Fisher information and Poincaré rates
are multiplied by `a₀ = 4π²`; the absolute square-root `H¹` domains correspond bijectively.
-/

open MeasureTheory Real
open scoped ContDiff ENNReal

namespace DGPS.Circle.AngularNormalization

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- angular circle -/
abbrev AngCircle := AddCircle (2 * π)

noncomputable abbrev angHaar : Measure AngCircle := AddCircle.haarAddCircle

noncomputable def angRescale : UnitAddCircle ≃+ AngCircle :=
  AddCircle.equivAddCircle 1 (2 * π) one_ne_zero Real.two_pi_pos.ne'

theorem angRescale_mk (t : ℝ) : angRescale (t : UnitAddCircle) = ((2 * π * t : ℝ) : AngCircle) := by
  simp [angRescale, mul_comm]

noncomputable def angHomeo : UnitAddCircle ≃ₜ AngCircle :=
  AddCircle.homeomorphAddCircle 1 (2 * π) one_ne_zero Real.two_pi_pos.ne'

theorem angHomeo_apply (t : UnitAddCircle) : angHomeo t = angRescale t := rfl

noncomputable def angEquiv : Torus 1 ≃ᵐ AngCircle :=
  (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).trans angHomeo.toMeasurableEquiv

theorem angEquiv_apply (x : Torus 1) : angEquiv x = angRescale (x 0) := rfl

theorem measurePreserving_angEquiv : MeasurePreserving angEquiv (haar 1) angHaar := by
  have h1 : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle) (haar 1)
      (volume : Measure UnitAddCircle) := measurePreserving_funUnique volume (Fin 1)
  have h2 : MeasurePreserving (angHomeo.toMeasurableEquiv) volume angHaar := by
    refine ⟨angHomeo.toMeasurableEquiv.measurable, ?_⟩
    have : (Measure.map angHomeo.toMeasurableEquiv (volume : Measure UnitAddCircle)).IsAddHaarMeasure :=
      angRescale.isAddHaarMeasure_map _ angHomeo.continuous angHomeo.symm.continuous
    have : IsProbabilityMeasure (Measure.map angHomeo.toMeasurableEquiv (volume : Measure UnitAddCircle)) :=
      inferInstance
    exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  exact h2.comp h1


/-! ### Angular smooth tests and weak derivatives -/

/-- Representative in `(0, 2π]`. -/
noncomputable def angSec (θ : AngCircle) : ℝ := (AddCircle.equivIoc (2 * π) 0 θ : ℝ)

def IsSmoothAngular (ψ : AngCircle → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun s : ℝ => ψ (s : AngCircle))

noncomputable def angDeriv (ψ : AngCircle → ℝ) (θ : AngCircle) : ℝ :=
  deriv (fun s : ℝ => ψ (s : AngCircle)) (angSec θ)

theorem comp_angEquiv_liftT (ψ : AngCircle → ℝ) (y : Fin 1 → ℝ) :
    (ψ ∘ angEquiv) (torusLift y) = ψ ((2 * π * y 0 : ℝ) : AngCircle) := by
  simp only [Function.comp, angEquiv_apply]
  exact congrArg ψ (angRescale_mk _)

theorem isSmoothPeriodic_comp_iff (ψ : AngCircle → ℝ) :
    IsSmoothPeriodic (ψ ∘ angEquiv) ↔ IsSmoothAngular ψ := by
  unfold IsSmoothPeriodic IsSmoothAngular
  have h1 : ((ψ ∘ angEquiv) ∘ torusLift : (Fin 1 → ℝ) → ℝ)
      = (fun s : ℝ => ψ (s : AngCircle)) ∘ (fun y : Fin 1 → ℝ => 2 * π * y 0) := by
    funext y; exact comp_angEquiv_liftT ψ y
  have h2 : (fun s : ℝ => ψ (s : AngCircle))
      = ((ψ ∘ angEquiv) ∘ torusLift : (Fin 1 → ℝ) → ℝ) ∘ (fun s : ℝ => fun _ : Fin 1 => s / (2 * π)) := by
    funext s
    rw [Function.comp_apply, h1]
    simp only [Function.comp_apply]
    congr 2
    field_simp
  constructor
  · intro h
    rw [h2]
    exact h.comp (by fun_prop)
  · intro h
    rw [h1]
    exact h.comp (by fun_prop)


theorem secT_zero_mem (x : Torus 1) : SharpLSI.secT x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
  ((AddCircle.measurableEquivIoc 1 0) (x 0)).2

theorem angSec_angEquiv (x : Torus 1) : angSec (angEquiv x) = 2 * π * SharpLSI.secT x 0 := by
  have hx : x 0 = ((SharpLSI.secT x 0 : ℝ) : UnitAddCircle) := by
    have := congrFun (SharpLSI.liftT_secT x) 0
    exact this.symm
  have hm := secT_zero_mem x
  rw [angSec, angEquiv_apply, hx, angRescale_mk]
  have : (2 * π * SharpLSI.secT x 0) ∈ Set.Ioc (0 : ℝ) (0 + 2 * π) := by
    constructor
    · have : 0 < SharpLSI.secT x 0 := hm.1
      positivity
    · have : SharpLSI.secT x 0 ≤ 1 := by simpa using hm.2
      nlinarith [Real.pi_pos]
  exact AddCircle.equivIoc_coe_of_mem (p := 2 * π) (a := 0) this

theorem coordPartial_comp_angEquiv {ψ : AngCircle → ℝ} (hψ : IsSmoothAngular ψ) (x : Torus 1) :
    coordPartial 0 (ψ ∘ angEquiv) x = 2 * π * angDeriv ψ (angEquiv x) := by
  have h1 : ((ψ ∘ angEquiv) ∘ torusLift : (Fin 1 → ℝ) → ℝ)
      = (fun s : ℝ => ψ (s : AngCircle)) ∘ (fun y : Fin 1 → ℝ => 2 * π * y 0) := by
    funext y; exact comp_angEquiv_liftT ψ y
  unfold coordPartial angDeriv
  rw [h1, angSec_angEquiv]
  have hd : DifferentiableAt ℝ (fun s : ℝ => ψ (s : AngCircle)) (2 * π * SharpLSI.secT x 0) :=
    (hψ.differentiable (by simp)).differentiableAt
  have hL : HasFDerivAt (fun y : Fin 1 → ℝ => 2 * π * y 0)
      ((2 * π) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ))
      (SharpLSI.secT x) := by
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
      (x := SharpLSI.secT x)).const_mul (2 * π)
    simpa using this
  have := (hd.hasDerivAt.comp_hasFDerivAt (SharpLSI.secT x) hL).fderiv
  rw [this]
  simp
  ring


/-- Weak angular derivative `g = u'` of `u` on the angular circle (normalized angular Haar). -/
structure IsAngularWeakDeriv (u g : AngCircle → ℝ) : Prop where
  memLp : MemLp u 2 angHaar
  memLp_deriv : MemLp g 2 angHaar
  ibp : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
    ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar

def AngularH1 (u : AngCircle → ℝ) : Prop := ∃ g, IsAngularWeakDeriv u g

/-- The physical gradient `2π (u')∘θ` as a tangent field on the unit circle. -/
noncomputable def physGrad (g : AngCircle → ℝ) : Torus 1 → Tangent 1 :=
  fun x => (2 * π * g (angEquiv x)) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

theorem physGrad_apply (g : AngCircle → ℝ) (x : Torus 1) (j : Fin 1) :
    physGrad g x j = 2 * π * g (angEquiv x) := by
  have : j = 0 := Subsingleton.elim _ _
  subst this
  simp [physGrad]

theorem memLp_comp_angEquiv_iff {E : Type*} [NormedAddCommGroup E] {p : ENNReal}
    (f : AngCircle → E) : MemLp (f ∘ angEquiv) p (haar 1) ↔ MemLp f p angHaar := by
  rw [← MeasurableEquiv.memLp_map_measure_iff angEquiv, measurePreserving_angEquiv.map_eq]

theorem integral_comp_angEquiv (f : AngCircle → ℝ) :
    ∫ x, f (angEquiv x) ∂haar 1 = ∫ θ, f θ ∂angHaar :=
  measurePreserving_angEquiv.integral_comp' f

theorem integral_u_coordPartial (u : AngCircle → ℝ) {ψ : AngCircle → ℝ} (hψ : IsSmoothAngular ψ) :
    ∫ x, (u ∘ angEquiv) x * coordPartial 0 (ψ ∘ angEquiv) x ∂haar 1
      = 2 * π * ∫ θ, u θ * angDeriv ψ θ ∂angHaar := by
  have : ∀ x, (u ∘ angEquiv) x * coordPartial 0 (ψ ∘ angEquiv) x
      = 2 * π * (fun θ => u θ * angDeriv ψ θ) (angEquiv x) := fun x => by
    rw [coordPartial_comp_angEquiv hψ]; simp only [Function.comp_apply]; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_angEquiv (fun θ => u θ * angDeriv ψ θ)]

theorem integral_physGrad_mul (g : AngCircle → ℝ) (ψ : AngCircle → ℝ) :
    ∫ x, physGrad g x 0 * (ψ ∘ angEquiv) x ∂haar 1 = 2 * π * ∫ θ, g θ * ψ θ ∂angHaar := by
  have : ∀ x, physGrad g x 0 * (ψ ∘ angEquiv) x
      = 2 * π * (fun θ => g θ * ψ θ) (angEquiv x) := fun x => by
    rw [physGrad_apply]; simp only [Function.comp_apply]; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_angEquiv (fun θ => g θ * ψ θ)]

theorem isWeakGradient_comp_iff (u g : AngCircle → ℝ) :
    IsAngularWeakDeriv u g ↔ IsWeakGradient (u ∘ angEquiv) (physGrad g) := by
  have hg : MemLp (physGrad g) 2 (haar 1) ↔ MemLp g 2 angHaar := by
    rw [← memLp_comp_angEquiv_iff]
    constructor
    · intro h
      have := memLp_coord h 0
      have h2 : (fun x => physGrad g x 0) = fun x => 2 * π * (g ∘ angEquiv) x := by
        funext x; exact physGrad_apply g x 0
      rw [h2] at this
      have h3 := this.const_mul (2 * π)⁻¹
      refine h3.ae_eq (Filter.Eventually.of_forall fun x => ?_)
      simp only
      field_simp
    · intro h
      have h4 : MemLp (fun x => 2 * π * (g ∘ angEquiv) x) 2 (haar 1) :=
        h.const_mul (2 * π)
      exact ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
          ℝ →L[ℝ] Tangent 1).comp_memLp' h4
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  constructor
  · intro h
    refine ⟨(memLp_comp_angEquiv_iff u).2 h.memLp, hg.2 h.memLp_deriv, ?_⟩
    intro φ hφ j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    set ψ : AngCircle → ℝ := φ ∘ angEquiv.symm with hψdef
    have hφψ : φ = ψ ∘ angEquiv := by
      funext x; simp [hψdef]
    have hψ : IsSmoothAngular ψ := by
      rw [← isSmoothPeriodic_comp_iff, ← hφψ]; exact hφ
    rw [hφψ, integral_u_coordPartial u hψ, integral_physGrad_mul, h.ibp ψ hψ]
    ring
  · intro h
    refine ⟨(memLp_comp_angEquiv_iff u).1 h.memLp, hg.1 h.memLp_grad, ?_⟩
    intro ψ hψ
    have hφ : IsSmoothPeriodic (ψ ∘ angEquiv) := (isSmoothPeriodic_comp_iff ψ).2 hψ
    have := h.ibp (ψ ∘ angEquiv) hφ 0
    rw [integral_u_coordPartial u hψ, integral_physGrad_mul] at this
    have h2 : 2 * π * (∫ θ, u θ * angDeriv ψ θ ∂angHaar + ∫ θ, g θ * ψ θ ∂angHaar) = 0 := by
      linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hpi
    · linarith

/-- `a₀ = 4π²`, the square of the angular frequency. -/
noncomputable def a0 : ℝ := 4 * π ^ 2

theorem a0_pos : 0 < a0 := by unfold a0; positivity

/-- Angular Dirichlet form `∫ |u'|² dθ/(2π)` of an angular derivative field, in `ℝ≥0∞`. -/
noncomputable def angDirichlet (g : AngCircle → ℝ) : ℝ≥0∞ := ∫⁻ θ, ‖g θ‖ₑ ^ 2 ∂angHaar

theorem enorm_physGrad_sq (g : AngCircle → ℝ) (x : Torus 1) :
    ‖physGrad g x‖ₑ ^ 2 = ENNReal.ofReal a0 * ‖g (angEquiv x)‖ₑ ^ 2 := by
  have he : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : Tangent 1)‖ₑ = 1 := by
    rw [← ofReal_norm]; simp
  have h2 : ‖(2 * π : ℝ)‖ₑ = ENNReal.ofReal (2 * π) := by
    rw [← ofReal_norm, Real.norm_of_nonneg Real.two_pi_pos.le]
  have h : ‖physGrad g x‖ₑ = ENNReal.ofReal (2 * π) * ‖g (angEquiv x)‖ₑ := by
    unfold physGrad
    rw [enorm_smul, he, mul_one, enorm_mul, h2]
  rw [h, mul_pow, a0, ← ENNReal.ofReal_pow Real.two_pi_pos.le]
  congr 2
  ring

theorem lintegral_comp_angEquiv (f : AngCircle → ℝ≥0∞) :
    ∫⁻ x, f (angEquiv x) ∂haar 1 = ∫⁻ θ, f θ ∂angHaar :=
  measurePreserving_angEquiv.lintegral_comp_emb angEquiv.measurableEmbedding f

theorem ae_comp_angEquiv_iff {p : AngCircle → Prop} :
    (∀ᵐ x ∂haar 1, p (angEquiv x)) ↔ ∀ᵐ θ ∂angHaar, p θ := by
  constructor
  · intro h
    have h2 := (measurePreserving_angEquiv.symm angEquiv).quasiMeasurePreserving.ae h
    filter_upwards [h2] with θ hθ
    simpa using hθ
  · intro h
    exact measurePreserving_angEquiv.quasiMeasurePreserving.ae h

/-! ### Scaling of Dirichlet forms and Fisher information -/

theorem lintegral_enorm_sq_of_weakGradient {u g : AngCircle → ℝ} (h : IsAngularWeakDeriv u g)
    {G : Torus 1 → Tangent 1} (hG : IsWeakGradient (u ∘ angEquiv) G) :
    ∫⁻ x, ‖G x‖ₑ ^ 2 ∂haar 1 = ENNReal.ofReal a0 * angDirichlet g := by
  have hae := ((isWeakGradient_comp_iff u g).1 h).ae_eq hG
  calc ∫⁻ x, ‖G x‖ₑ ^ 2 ∂haar 1 = ∫⁻ x, ‖physGrad g x‖ₑ ^ 2 ∂haar 1 :=
        lintegral_congr_ae (hae.mono fun x hx => by simp only [hx])
    _ = ∫⁻ x, ENNReal.ofReal a0 * ‖g (angEquiv x)‖ₑ ^ 2 ∂haar 1 := by
        simp_rw [enorm_physGrad_sq]
    _ = ENNReal.ofReal a0 * ∫⁻ x, ‖g (angEquiv x)‖ₑ ^ 2 ∂haar 1 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal a0 * angDirichlet g := by
        rw [lintegral_comp_angEquiv (fun θ => ‖g θ‖ₑ ^ 2)]
        rfl

theorem norm_physGrad_sq (g : AngCircle → ℝ) (x : Torus 1) :
    ‖physGrad g x‖ ^ 2 = a0 * g (angEquiv x) ^ 2 := by
  have he : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : Tangent 1)‖ = 1 := by simp
  have h : ‖physGrad g x‖ = 2 * π * |g (angEquiv x)| := by
    unfold physGrad
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos]
  rw [h, mul_pow, sq_abs, a0]
  ring

theorem integral_norm_sq_of_weakGradient {u g : AngCircle → ℝ} (h : IsAngularWeakDeriv u g)
    {G : Torus 1 → Tangent 1} (hG : IsWeakGradient (u ∘ angEquiv) G) :
    ∫ x, ‖G x‖ ^ 2 ∂haar 1 = a0 * ∫ θ, g θ ^ 2 ∂angHaar := by
  have hae := ((isWeakGradient_comp_iff u g).1 h).ae_eq hG
  calc ∫ x, ‖G x‖ ^ 2 ∂haar 1 = ∫ x, ‖physGrad g x‖ ^ 2 ∂haar 1 :=
        integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    _ = ∫ x, a0 * (fun θ => g θ ^ 2) (angEquiv x) ∂haar 1 := by
        simp_rw [norm_physGrad_sq]
    _ = a0 * ∫ θ, g θ ^ 2 ∂angHaar := by
        rw [integral_const_mul, integral_comp_angEquiv (fun θ => g θ ^ 2)]

/-! ### The absolute square-root domains -/

theorem physGrad_surj {G : Torus 1 → Tangent 1} :
    physGrad (fun θ => G (angEquiv.symm θ) 0 / (2 * π)) = G := by
  funext x
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  unfold physGrad
  have : (2 * π * (G (angEquiv.symm (angEquiv x)) 0 / (2 * π))) = G x 0 := by
    rw [MeasurableEquiv.symm_apply_apply]; field_simp
  rw [this]
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp

theorem angularH1_comp_iff (u : AngCircle → ℝ) : AngularH1 u ↔ MemH1 (u ∘ angEquiv) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨physGrad g, (isWeakGradient_comp_iff u g).1 hg⟩
  · rintro ⟨G, hG⟩
    refine ⟨fun θ => G (angEquiv.symm θ) 0 / (2 * π), ?_⟩
    rw [isWeakGradient_comp_iff, physGrad_surj]
    exact hG

theorem bijOn_h1 :
    Set.BijOn (fun u : AngCircle → ℝ => u ∘ angEquiv) {u | AngularH1 u} (H1Haar 1) := by
  refine ⟨fun u hu => (angularH1_comp_iff u).1 hu, ?_, ?_⟩
  · intro u _ v _ h
    funext θ
    have := congrFun h (angEquiv.symm θ)
    simpa using this
  · intro v hv
    refine ⟨v ∘ angEquiv.symm, ?_, ?_⟩
    · show AngularH1 _
      rw [angularH1_comp_iff]
      have : (v ∘ angEquiv.symm) ∘ angEquiv = v := by funext x; simp
      rw [this]; exact hv
    · funext x; simp

/-- Angular absolute-admissible square roots: `u ∈ H¹`, `u ≥ 0` a.e., `∫ u² dθ/(2π) = 1`. -/
def AngularAbsoluteAdmissible (u : AngCircle → ℝ) : Prop :=
  AngularH1 u ∧ 0 ≤ᵐ[angHaar] u ∧ ∫ θ, u θ ^ 2 ∂angHaar = 1

theorem angularAbsoluteAdmissible_comp_iff (u : AngCircle → ℝ) :
    AngularAbsoluteAdmissible u ↔
      (u ∘ angEquiv) ∈ H1Haar 1 ∧ 0 ≤ᵐ[haar 1] (u ∘ angEquiv) ∧
        ∫ x, (u ∘ angEquiv) x ^ 2 ∂haar 1 = 1 := by
  unfold AngularAbsoluteAdmissible
  have h2 : ∫ x, (u ∘ angEquiv) x ^ 2 ∂haar 1 = ∫ θ, u θ ^ 2 ∂angHaar :=
    integral_comp_angEquiv (fun θ => u θ ^ 2)
  rw [angularH1_comp_iff, mem_H1Haar, h2]
  have : (0 ≤ᵐ[haar 1] (u ∘ angEquiv)) ↔ (0 ≤ᵐ[angHaar] u) :=
    ae_comp_angEquiv_iff (p := fun θ => (0 : ℝ) ≤ u θ)
  rw [this]

/-- The density of the absolute-admissible class attached to an angular admissible `u`. -/
noncomputable def toAbsoluteDensity (u : AngCircle → ℝ) (h : AngularAbsoluteAdmissible u) :
    AbsoluteDensity 1 :=
  have h' := (angularAbsoluteAdmissible_comp_iff u).1 h
  ⟨u ∘ angEquiv, h'.1, h'.2.1, h'.2.2⟩

theorem toAbsoluteDensity_sqrt (u : AngCircle → ℝ) (h : AngularAbsoluteAdmissible u) :
    (toAbsoluteDensity u h).sqrt = u ∘ angEquiv := rfl

theorem exists_angular_of_absoluteDensity (ρ : AbsoluteDensity 1) :
    ∃ u, ∃ h : AngularAbsoluteAdmissible u, (toAbsoluteDensity u h).sqrt = ρ.sqrt := by
  refine ⟨ρ.sqrt ∘ angEquiv.symm, ?_, ?_⟩
  · rw [angularAbsoluteAdmissible_comp_iff]
    have : (ρ.sqrt ∘ angEquiv.symm) ∘ angEquiv = ρ.sqrt := by funext x; simp
    rw [this]
    exact ⟨ρ.sqrt_mem, ρ.sqrt_nonneg, ρ.mass_one⟩
  · funext x; simp [toAbsoluteDensity]

theorem bijOn_absolute :
    Set.BijOn (fun u : AngCircle → ℝ => u ∘ angEquiv) {u | AngularAbsoluteAdmissible u}
      {v | v ∈ H1Haar 1 ∧ 0 ≤ᵐ[haar 1] v ∧ ∫ x, v x ^ 2 ∂haar 1 = 1} := by
  refine ⟨fun u hu => (angularAbsoluteAdmissible_comp_iff u).1 hu, ?_, ?_⟩
  · intro u _ v _ h
    funext θ
    have := congrFun h (angEquiv.symm θ)
    simpa using this
  · intro v hv
    refine ⟨v ∘ angEquiv.symm, ?_, ?_⟩
    · show AngularAbsoluteAdmissible _
      rw [angularAbsoluteAdmissible_comp_iff]
      have : (v ∘ angEquiv.symm) ∘ angEquiv = v := by funext x; simp
      rw [this]; exact hv
    · funext x; simp

/-! ### Fisher information and entropy of an absolute density -/

theorem circleFisherInformation_eq {ρ : AbsoluteDensity 1} {u g : AngCircle → ℝ}
    (hu : ρ.sqrt = u ∘ angEquiv) (hg : IsAngularWeakDeriv u g) :
    DGPS.Analysis.circleFisherInformation ρ = a0 * (4 * ∫ θ, g θ ^ 2 ∂angHaar) := by
  have hw : IsWeakGradient (u ∘ angEquiv) (weakGradient ρ.sqrt ρ.sqrt_mem) := by
    have key : ∀ w : Torus 1 → ℝ, w = u ∘ angEquiv →
        IsWeakGradient w (weakGradient ρ.sqrt ρ.sqrt_mem) →
        IsWeakGradient (u ∘ angEquiv) (weakGradient ρ.sqrt ρ.sqrt_mem) := by
      rintro w rfl h; exact h
    exact key _ hu (isWeakGradient_weakGradient ρ.sqrt_mem)
  unfold DGPS.Analysis.circleFisherInformation
  rw [integral_norm_sq_of_weakGradient hg hw]
  ring

theorem homogeneousEntropy_comp_angEquiv (v : AngCircle → ℝ) :
    homogeneousEntropy (haar 1) (v ∘ angEquiv) = homogeneousEntropy angHaar v := by
  have h1 : ∫ x, (v ∘ angEquiv) x ∂haar 1 = ∫ θ, v θ ∂angHaar := integral_comp_angEquiv v
  unfold homogeneousEntropy
  rw [h1]
  split_ifs
  · rfl
  · exact lintegral_comp_angEquiv
      (fun θ => ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂angHaar) (v θ)))

theorem circleEntropy_eq {ρ : AbsoluteDensity 1} {u : AngCircle → ℝ} (hu : ρ.sqrt = u ∘ angEquiv) :
    DGPS.Analysis.circleEntropy ρ = (homogeneousEntropy angHaar (fun θ => u θ ^ 2)).toReal := by
  unfold DGPS.Analysis.circleEntropy
  rw [← homogeneousEntropy_comp_angEquiv]
  have : ρ.density = (fun θ => u θ ^ 2) ∘ angEquiv := by
    funext x; simp [AbsoluteDensity.density, hu]
  rw [this]

/-! ### Feature means and relative entropy of measures -/

theorem integral_map_angEquiv (ν : Measure (Torus 1)) (f : AngCircle → ℝ) :
    ∫ θ, f θ ∂ν.map angEquiv = ∫ x, f (angEquiv x) ∂ν :=
  integral_map_equiv angEquiv f

theorem map_ac_iff (ν : Measure (Torus 1)) : ν.map angEquiv ≪ angHaar ↔ ν ≪ haar 1 := by
  constructor
  · intro h s hs
    have h1 : angHaar (angEquiv.symm ⁻¹' s) = 0 := by
      rw [← measurePreserving_angEquiv.measure_preimage_equiv (angEquiv.symm ⁻¹' s)]
      simpa [Set.preimage_preimage] using hs
    have h2 := h h1
    simpa [MeasurableEquiv.map_apply, Set.preimage_preimage] using h2
  · intro h
    have := angEquiv.measurableEmbedding.absolutelyContinuous_map h
    rwa [measurePreserving_angEquiv.map_eq] at this

theorem relativeEntropy_map_angEquiv (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    relativeEntropy (ν.map angEquiv) angHaar = relativeEntropy ν (haar 1) := by
  by_cases h : ν ≪ haar 1
  · rw [relativeEntropy_of_absolutelyContinuous h,
      relativeEntropy_of_absolutelyContinuous ((map_ac_iff ν).2 h),
      ← homogeneousEntropy_comp_angEquiv]
    refine homogeneousEntropy_congr_ae ?_
    have := angEquiv.measurableEmbedding.rnDeriv_map ν (haar 1)
    rw [measurePreserving_angEquiv.map_eq] at this
    filter_upwards [this] with x hx
    simp only [Function.comp_apply, hx]
  · rw [relativeEntropy_of_not_absolutelyContinuous h,
      relativeEntropy_of_not_absolutelyContinuous (fun h' => h ((map_ac_iff ν).1 h'))]

/-! ### Free energy on the angular circle -/

/-- The free energy `H(ν | dθ/2π) + ∫ V dν + (1/2) ∬ W dν²` on the angular circle with
potentials `V`, `W` given in the angular variable. -/
noncomputable def angFreeEnergy (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ)
    (ν : Measure AngCircle) : EReal :=
  ((relativeEntropy ν angHaar : ℝ≥0∞) : EReal) + ((∫ θ, V θ ∂ν : ℝ) : EReal) +
    (((1 / 2 : ℝ) * ∫ p, W p.1 p.2 ∂(ν.prod ν) : ℝ) : EReal)

/-- The infimum of the angular free energy over all Borel probabilities. -/
noncomputable def angFreeEnergyMinimum (V : AngCircle → ℝ) (W : AngCircle → AngCircle → ℝ) :
    EReal :=
  ⨅ ν : ProbabilityMeasure AngCircle, angFreeEnergy V W (ν : Measure AngCircle)

/-- Angular potential attached to interaction data under `θ = 2π x`. -/
noncomputable def angV (A : InteractionData 1) : AngCircle → ℝ := fun θ => A.V (angEquiv.symm θ)

/-- Angular interaction attached to interaction data under `θ = 2π x`. -/
noncomputable def angW (A : InteractionData 1) : AngCircle → AngCircle → ℝ :=
  fun a b => A.W (angEquiv.symm a) (angEquiv.symm b)

theorem angFreeEnergy_map (A : InteractionData 1) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] :
    angFreeEnergy (angV A) (angW A) (ν.map angEquiv) =
      ((relativeEntropy ν (haar 1) : ℝ≥0∞) : EReal) + ((potentialEnergy A ν : ℝ) : EReal) +
        (((1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal) := by
  have hV : ∫ θ, angV A θ ∂ν.map angEquiv = potentialEnergy A ν := by
    rw [integral_map_angEquiv]; simp [angV, potentialEnergy]
  have hW : ∫ p, angW A p.1 p.2 ∂((ν.map angEquiv).prod (ν.map angEquiv))
      = interactionEnergy A ν := by
    rw [Measure.map_prod_map ν ν angEquiv.measurable angEquiv.measurable]
    rw [interactionEnergy]
    have hm : (Measure.map (Prod.map angEquiv angEquiv) (ν.prod ν)) =
        Measure.map (MeasurableEquiv.prodCongr angEquiv angEquiv) (ν.prod ν) := rfl
    rw [hm, integral_map_equiv]
    simp [angW, MeasurableEquiv.prodCongr]
  unfold angFreeEnergy
  rw [relativeEntropy_map_angEquiv, hV, hW]

theorem freeEnergy_eq_angFreeEnergy (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy A ν = angFreeEnergy (angV A) (angW A) ((ν : Measure (Torus 1)).map angEquiv) :=
  (angFreeEnergy_map A ν).symm

theorem freeEnergyMinimum_eq_angFreeEnergyMinimum (A : InteractionData 1) :
    freeEnergyMinimum A = angFreeEnergyMinimum (angV A) (angW A) := by
  apply le_antisymm
  · refine le_iInf fun ν' => ?_
    let ν : ProbabilityMeasure (Torus 1) :=
      ⟨(ν' : Measure AngCircle).map angEquiv.symm,
        inferInstance⟩
    have h : (ν : Measure (Torus 1)).map angEquiv = ν' := by
      show ((ν' : Measure AngCircle).map angEquiv.symm).map angEquiv = ν'
      rw [Measure.map_map angEquiv.measurable angEquiv.symm.measurable]
      simp
    calc freeEnergyMinimum A ≤ freeEnergy A ν := iInf_le _ ν
      _ = angFreeEnergy (angV A) (angW A) ((ν : Measure (Torus 1)).map angEquiv) :=
          freeEnergy_eq_angFreeEnergy A ν
      _ = angFreeEnergy (angV A) (angW A) (ν' : Measure AngCircle) := by rw [h]
  · refine le_iInf fun ν => ?_
    let ν' : ProbabilityMeasure AngCircle :=
      ⟨(ν : Measure (Torus 1)).map angEquiv,
        inferInstance⟩
    calc angFreeEnergyMinimum (angV A) (angW A)
        ≤ angFreeEnergy (angV A) (angW A) (ν' : Measure AngCircle) := iInf_le _ ν'
      _ = freeEnergy A ν := (freeEnergy_eq_angFreeEnergy A ν).symm

/-- The free-energy gap `F(ν) - F_*` is the same in the angular and physical variables. -/
theorem freeEnergyGap_eq (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy A ν - freeEnergyMinimum A =
      angFreeEnergy (angV A) (angW A) ((ν : Measure (Torus 1)).map angEquiv) -
        angFreeEnergyMinimum (angV A) (angW A) := by
  rw [freeEnergy_eq_angFreeEnergy, freeEnergyMinimum_eq_angFreeEnergyMinimum]

/-! ### Poincaré rates -/

theorem memLp_physGrad_iff (μ : Measure (Torus 1)) (g : AngCircle → ℝ) :
    MemLp (physGrad g) 2 μ ↔ MemLp (g ∘ angEquiv) 2 μ := by
  have e : (fun x => physGrad g x 0) = fun x => 2 * π * (g ∘ angEquiv) x := by
    funext x; exact physGrad_apply g x 0
  constructor
  · intro h
    have h1 : MemLp (fun x => physGrad g x 0) 2 μ :=
      (EuclideanSpace.proj (0 : Fin 1) : Tangent 1 →L[ℝ] ℝ).comp_memLp' h
    rw [e] at h1
    refine (h1.const_mul (2 * π)⁻¹).ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only
    field_simp
  · intro h
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : ℝ →L[ℝ] Tangent 1).comp_memLp'
        (h.const_mul (2 * π))

theorem integrable_physGrad_iff (μ : Measure (Torus 1)) (g : AngCircle → ℝ) :
    Integrable (physGrad g) μ ↔ Integrable (g ∘ angEquiv) μ := by
  have e : (fun x => physGrad g x 0) = fun x => 2 * π * (g ∘ angEquiv) x := by
    funext x; exact physGrad_apply g x 0
  constructor
  · intro h
    have h1 : Integrable (fun x => physGrad g x 0) μ :=
      (EuclideanSpace.proj (0 : Fin 1) : Tangent 1 →L[ℝ] ℝ).integrable_comp h
    rw [e] at h1
    refine (h1.const_mul (2 * π)⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    field_simp
  · intro h
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : ℝ →L[ℝ] Tangent 1).integrable_comp
        (h.const_mul (2 * π))

theorem ibp_comp_iff (u g : AngCircle → ℝ) :
    (∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
      ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar) ↔
    (∀ φ : Torus 1 → ℝ, IsSmoothPeriodic φ → ∀ j : Fin 1,
      ∫ x, (u ∘ angEquiv) x * coordPartial j φ x ∂haar 1 = -∫ x, physGrad g x j * φ x ∂haar 1) := by
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  constructor
  · intro h φ hφ j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    set ψ : AngCircle → ℝ := φ ∘ angEquiv.symm with hψdef
    have hφψ : φ = ψ ∘ angEquiv := by
      funext x; simp [hψdef]
    have hψ : IsSmoothAngular ψ := by
      rw [← isSmoothPeriodic_comp_iff, ← hφψ]; exact hφ
    rw [hφψ, integral_u_coordPartial u hψ, integral_physGrad_mul, h ψ hψ]
    ring
  · intro h ψ hψ
    have hφ : IsSmoothPeriodic (ψ ∘ angEquiv) := (isSmoothPeriodic_comp_iff ψ).2 hψ
    have := h (ψ ∘ angEquiv) hφ 0
    rw [integral_u_coordPartial u hψ, integral_physGrad_mul] at this
    have h2 : 2 * π * (∫ θ, u θ * angDeriv ψ θ ∂angHaar + ∫ θ, g θ * ψ θ ∂angHaar) = 0 := by
      linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hpi
    · linarith

/-- Weighted weak derivative on the angular circle for a probability `ν`: the analogue of
`IsMeasureWeakGradient` with the angular Haar pairing. -/
structure IsAngMeasureWeakDeriv (ν : ProbabilityMeasure AngCircle) (u g : AngCircle → ℝ) : Prop where
  memLp : MemLp u 2 (ν : Measure AngCircle)
  memLp_deriv : MemLp g 2 (ν : Measure AngCircle)
  integrable : Integrable u angHaar
  integrable_deriv : Integrable g angHaar
  ibp : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
    ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar

/-- Test functions of the angular weighted form domain. -/
structure AngWeakH1Test (ν : ProbabilityMeasure AngCircle) where
  fn : AngCircle → ℝ
  grad : AngCircle → ℝ
  isWeak : IsAngMeasureWeakDeriv ν fn grad

/-- Angular variance `∫ (u - ν(u))² dν`. -/
noncomputable def angVariance (ν : ProbabilityMeasure AngCircle) (u : AngCircle → ℝ) : ℝ :=
  ∫ θ, (u θ - ∫ φ, u φ ∂(ν : Measure AngCircle)) ^ 2 ∂(ν : Measure AngCircle)

/-- Angular Dirichlet energy `∫ |u'|² dν`. -/
noncomputable def angDirichletEnergy (ν : ProbabilityMeasure AngCircle) (f : AngWeakH1Test ν) :
    ℝ≥0∞ :=
  ∫⁻ θ, ‖f.grad θ‖ₑ ^ 2 ∂(ν : Measure AngCircle)

/-- Angular Poincaré rate `inf_{Var_ν(f) > 0} ∫ |f'|² dν / Var_ν(f)`. -/
noncomputable def angPoincareRate (ν : ProbabilityMeasure AngCircle) : ℝ≥0∞ :=
  ⨅ f : {f : AngWeakH1Test ν // 0 < angVariance ν f.fn},
    angDirichletEnergy ν f.1 / ENNReal.ofReal (angVariance ν f.1.fn)

/-- Pushforward of a probability on the unit torus to the angular circle. -/
noncomputable def angMap (μ : ProbabilityMeasure (Torus 1)) : ProbabilityMeasure AngCircle :=
  ⟨(μ : Measure (Torus 1)).map angEquiv, inferInstance⟩

theorem angMap_coe (μ : ProbabilityMeasure (Torus 1)) :
    (angMap μ : Measure AngCircle) = (μ : Measure (Torus 1)).map angEquiv := rfl

theorem isAngMeasureWeakDeriv_iff (μ : ProbabilityMeasure (Torus 1)) (u g : AngCircle → ℝ) :
    IsAngMeasureWeakDeriv (angMap μ) u g ↔ IsMeasureWeakGradient μ (u ∘ angEquiv) (physGrad g) := by
  have hmap : ∀ {E : Type} [NormedAddCommGroup E] (f : AngCircle → E),
      MemLp f 2 (angMap μ : Measure AngCircle) ↔ MemLp (f ∘ angEquiv) 2 (μ : Measure (Torus 1)) :=
    fun f => MeasurableEquiv.memLp_map_measure_iff angEquiv
  have hint : ∀ f : AngCircle → ℝ, Integrable f angHaar ↔ Integrable (f ∘ angEquiv) (haar 1) := by
    intro f
    rw [← integrable_map_equiv angEquiv f, measurePreserving_angEquiv.map_eq]
  constructor
  · intro h
    exact ⟨(hmap u).1 h.memLp, (memLp_physGrad_iff _ g).2 ((hmap g).1 h.memLp_deriv),
      (hint u).1 h.integrable, (integrable_physGrad_iff _ g).2 ((hint g).1 h.integrable_deriv),
      (ibp_comp_iff u g).1 h.ibp⟩
  · intro h
    exact ⟨(hmap u).2 h.memLp, (hmap g).2 ((memLp_physGrad_iff _ g).1 h.memLp_grad),
      (hint u).2 h.integrable, (hint g).2 ((integrable_physGrad_iff _ g).1 h.integrable_grad),
      (ibp_comp_iff u g).2 h.ibp⟩

theorem lintegral_physGrad (μ : Measure (Torus 1)) (g : AngCircle → ℝ) :
    ∫⁻ x, ‖physGrad g x‖ₑ ^ 2 ∂μ
      = ENNReal.ofReal a0 * ∫⁻ θ, ‖g θ‖ₑ ^ 2 ∂μ.map angEquiv := by
  simp_rw [enorm_physGrad_sq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_map_equiv (fun θ => ‖g θ‖ₑ ^ 2) angEquiv]

theorem angVariance_angMap (μ : ProbabilityMeasure (Torus 1)) (v : AngCircle → ℝ) :
    angVariance (angMap μ) v = weightedVariance μ (v ∘ angEquiv) := by
  unfold angVariance weightedVariance
  rw [angMap_coe, integral_map_equiv]
  rw [integral_map_equiv]
  rfl

theorem poincareRate_eq (μ : ProbabilityMeasure (Torus 1)) :
    poincareRate μ = ENNReal.ofReal a0 * angPoincareRate (angMap μ) := by
  have ha0 : ENNReal.ofReal a0 ≠ 0 := (ENNReal.ofReal_pos.2 a0_pos).ne'
  apply le_antisymm
  · rw [angPoincareRate, ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
    refine le_iInf fun ⟨h, hv⟩ => ?_
    let f : WeakH1Test μ := ⟨h.fn ∘ angEquiv, physGrad h.grad,
      (isAngMeasureWeakDeriv_iff μ _ _).1 h.isWeak⟩
    have hv' : 0 < weightedVariance μ f.fn := by
      rw [← angVariance_angMap]; exact hv
    calc poincareRate μ ≤ poincareQuotient μ f := poincareRate_le_quotient μ f hv'
      _ = ENNReal.ofReal a0 *
          (angDirichletEnergy (angMap μ) h / ENNReal.ofReal (angVariance (angMap μ) h.fn)) := by
        unfold poincareQuotient dirichletEnergy angDirichletEnergy
        rw [angVariance_angMap, lintegral_physGrad, mul_div_assoc]
        rfl
  · rw [le_poincareRate_iff]
    intro f hf
    have hw : IsAngMeasureWeakDeriv (angMap μ) (f.fn ∘ angEquiv.symm)
        (fun θ => f.grad (angEquiv.symm θ) 0 / (2 * π)) := by
      rw [isAngMeasureWeakDeriv_iff, physGrad_surj]
      have e : (f.fn ∘ angEquiv.symm) ∘ angEquiv = f.fn := by funext x; simp
      rw [e]; exact f.isWeak
    let h : AngWeakH1Test (angMap μ) := ⟨_, _, hw⟩
    have hv : 0 < angVariance (angMap μ) h.fn := by
      rw [angVariance_angMap]
      have e : h.fn ∘ angEquiv = f.fn := by funext x; simp [h]
      rw [e]; exact hf
    have hle : angPoincareRate (angMap μ) ≤
        angDirichletEnergy (angMap μ) h / ENNReal.ofReal (angVariance (angMap μ) h.fn) :=
      iInf_le (fun g : {f : AngWeakH1Test (angMap μ) // 0 < angVariance (angMap μ) f.fn} =>
        angDirichletEnergy (angMap μ) g.1 / ENNReal.ofReal (angVariance (angMap μ) g.1.fn))
        ⟨h, hv⟩
    have e1 : h.fn ∘ angEquiv = f.fn := by funext x; simp [h]
    have e2 : physGrad h.grad = f.grad := physGrad_surj
    calc ENNReal.ofReal a0 * angPoincareRate (angMap μ)
        ≤ ENNReal.ofReal a0 *
          (angDirichletEnergy (angMap μ) h / ENNReal.ofReal (angVariance (angMap μ) h.fn)) :=
          by gcongr
      _ = poincareQuotient μ f := by
        unfold poincareQuotient dirichletEnergy angDirichletEnergy
        rw [angVariance_angMap, e1, ← e2, lintegral_physGrad, mul_div_assoc]
        rfl

end DGPS.Circle.AngularNormalization

namespace DGPS.Examples

open MeasureTheory
open scoped ENNReal
open DGPS.Circle.AngularNormalization

/-- EX001: under `θ = 2π x` (`angEquiv`), normalized angular Haar measure is the pushforward of the
unit-period Haar measure; entropies, feature means and free-energy gaps are invariant; Dirichlet
forms, Fisher information and Poincaré rates are multiplied by `a₀ = 4π²`; and the absolute
square-root `H¹` domains correspond bijectively. -/
theorem angular_to_physical_normalization :
    a0 = 4 * Real.pi ^ 2 ∧
    MeasurePreserving angEquiv (haar 1) angHaar ∧
    (∀ v : AngCircle → ℝ,
      homogeneousEntropy (haar 1) (v ∘ angEquiv) = homogeneousEntropy angHaar v) ∧
    (∀ (ν : Measure (Torus 1)) [IsProbabilityMeasure ν],
      relativeEntropy (ν.map angEquiv) angHaar = relativeEntropy ν (haar 1)) ∧
    (∀ (ν : Measure (Torus 1)) (f : AngCircle → ℝ),
      ∫ θ, f θ ∂ν.map angEquiv = ∫ x, f (angEquiv x) ∂ν) ∧
    (∀ (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)),
      freeEnergy A ν = angFreeEnergy (angV A) (angW A) ((ν : Measure (Torus 1)).map angEquiv)) ∧
    (∀ A : InteractionData 1,
      freeEnergyMinimum A = angFreeEnergyMinimum (angV A) (angW A)) ∧
    (∀ (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)),
      freeEnergy A ν - freeEnergyMinimum A =
        angFreeEnergy (angV A) (angW A) ((ν : Measure (Torus 1)).map angEquiv) -
          angFreeEnergyMinimum (angV A) (angW A)) ∧
    (∀ (u g : AngCircle → ℝ), IsAngularWeakDeriv u g → ∀ G : Torus 1 → Tangent 1,
      IsWeakGradient (u ∘ angEquiv) G →
        ∫⁻ x, ‖G x‖ₑ ^ 2 ∂haar 1 = ENNReal.ofReal a0 * angDirichlet g) ∧
    (∀ (ρ : AbsoluteDensity 1) (u g : AngCircle → ℝ), ρ.sqrt = u ∘ angEquiv →
      IsAngularWeakDeriv u g →
        DGPS.Analysis.circleFisherInformation ρ = a0 * (4 * ∫ θ, g θ ^ 2 ∂angHaar)) ∧
    (∀ μ : ProbabilityMeasure (Torus 1),
      poincareRate μ = ENNReal.ofReal a0 * angPoincareRate (angMap μ)) ∧
    Set.BijOn (fun u : AngCircle → ℝ => u ∘ angEquiv) {u | AngularH1 u} (H1Haar 1) ∧
    Set.BijOn (fun u : AngCircle → ℝ => u ∘ angEquiv) {u | AngularAbsoluteAdmissible u}
      {v | v ∈ H1Haar 1 ∧ 0 ≤ᵐ[haar 1] v ∧ ∫ x, v x ^ 2 ∂haar 1 = 1} :=
  ⟨rfl, measurePreserving_angEquiv, homogeneousEntropy_comp_angEquiv,
    fun ν _ => relativeEntropy_map_angEquiv ν, integral_map_angEquiv,
    freeEnergy_eq_angFreeEnergy, freeEnergyMinimum_eq_angFreeEnergyMinimum, freeEnergyGap_eq,
    fun _ _ hg _ hG => lintegral_enorm_sq_of_weakGradient hg hG,
    fun _ _ _ hu hg => circleFisherInformation_eq hu hg,
    poincareRate_eq, bijOn_h1, bijOn_absolute⟩

end DGPS.Examples
