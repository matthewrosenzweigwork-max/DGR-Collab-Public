import DGPS.Particle.Gibbs
import DGPS.Foundations.WeakSobolev

/-!
# Fixed-`N` weighted Sobolev equivalence (DEF017)

INTERFACES/common_lemmas.md DEF017. For every fixed `N`, `0 < c ≤ dP_N/dm^N ≤ C < ∞`
(`particle_weight_bounds`); hence `H¹(P_N) = H¹(m^N)` as sets with the same distributional weak
gradient and equivalent norms (`particleSobolev_equiv`, `particleEnergy_equiv`). No `N`-uniform
equivalence is asserted.

Also proved here (deferred by DEF016): a.e. uniqueness of the particle weak gradient
(`IsParticleHaarWeakGradient.ae_eq`, `IsParticleWeakGradient.ae_eq`), by a Fourier argument on
`(𝕋^d)^N ≃ 𝕋^{dN}`: the curried-coordinates map `particleUncurry` is measure preserving onto the
product Haar measure on `UnitAddTorus (Fin N × Fin d)`, where Mathlib's Fourier basis applies.
Consequently `particleEnergy` does not depend on the chosen gradient
(`particleEnergy_eq_of_isParticleWeakGradient`).
-/

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace DGPS

/-- Generic Fourier uniqueness on a finite-index torus. -/
theorem ae_eq_zero_of_mFourier_orthogonal {ι : Type*} [Fintype ι]
    {h : UnitAddTorus ι → ℝ}
    (hh : MemLp h 2 (Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (H : ∀ n : ι → ℤ,
      ∫ x, h x * (UnitAddTorus.mFourier n x).re
        ∂(Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)) = 0 ∧
      ∫ x, h x * (UnitAddTorus.mFourier n x).im
        ∂(Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)) = 0) :
    h =ᵐ[Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)] 0 := by
  set ν : Measure (UnitAddTorus ι) :=
    Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle) with hνdef
  have hint : Integrable h ν := hh.integrable one_le_two
  have hcoef : ∀ n : ι → ℤ,
      UnitAddTorus.mFourierCoeff (d := ι) (fun x => (h x : ℂ)) n = 0 := by
    intro n
    set e := UnitAddTorus.mFourier (-n)
    have hI : Integrable (fun t => e t • (h t : ℂ)) ν := by
      simp only [smul_eq_mul]
      refine hint.ofReal.bdd_mul (c := 1) e.continuous.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      calc ‖e t‖ ≤ ‖e‖ := e.norm_coe_le_norm t
        _ = 1 := UnitAddTorus.mFourier_norm
    have hre : ∫ t, h t * (e t).re ∂ν = 0 := (H (-n)).1
    have him : ∫ t, h t * (e t).im ∂ν = 0 := (H (-n)).2
    have h1 := Complex.reCLM.integral_comp_comm hI
    have h2 := Complex.imCLM.integral_comp_comm hI
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h1 h2
    have hdef : UnitAddTorus.mFourierCoeff (d := ι) (fun x => (h x : ℂ)) n
        = ∫ x, e x * (h x : ℂ) ∂ν := by
      simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
      rfl
    rw [hdef]
    apply Complex.ext
    · rw [← h1, Complex.zero_re]
      simpa [mul_comm] using hre
    · rw [← h2, Complex.zero_im]
      simpa [mul_comm] using him
  have hc : MemLp (fun x => (h x : ℂ)) 2 ν := hh.ofReal
  have hf0 : hc.toLp _ = 0 := by
    rw [← LinearIsometryEquiv.map_eq_zero_iff UnitAddTorus.mFourierBasis.repr]
    ext n
    rw [UnitAddTorus.mFourierBasis_repr]
    calc UnitAddTorus.mFourierCoeff (d := ι) (hc.toLp _) n
        = UnitAddTorus.mFourierCoeff (d := ι) (fun x => (h x : ℂ)) n := by
          unfold UnitAddTorus.mFourierCoeff
          refine integral_congr_ae ?_
          filter_upwards [hc.coeFn_toLp] with x hx
          rw [hx]
      _ = 0 := hcoef n
      _ = _ := by simp
  have h2 : (fun x => (h x : ℂ)) =ᵐ[ν] 0 :=
    hc.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hf0)
  filter_upwards [h2] with x hx
  simpa using hx

/-- Curried-coordinates map. -/
def particleUncurry (d : ℕ) (N : ℕ+) : ParticleSpace d N ≃ᵐ (Fin N × Fin d → UnitAddCircle) :=
  (MeasurableEquiv.curry (Fin N) (Fin d) UnitAddCircle).symm

theorem particleUncurry_apply {d : ℕ} {N : ℕ+} (x : ParticleSpace d N) (p : Fin N × Fin d) :
    particleUncurry d N x p = x p.1 p.2 := rfl

theorem measurePreserving_particleUncurry (d : ℕ) (N : ℕ+) :
    MeasurePreserving (particleUncurry d N) (particleHaar d N)
      (Measure.pi fun _ : Fin N × Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  refine ⟨(particleUncurry d N).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (particleUncurry d N).measurable (MeasurableSet.univ_pi hs)]
  have : particleUncurry d N ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext x
    simp [Set.mem_pi, particleUncurry_apply, Prod.forall]
  rw [this, particleHaar, Measure.pi_pi]
  simp_rw [haar_eq_pi_haarAddCircle, Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : Fin N × Fin d => AddCircle.haarAddCircle (s p))).symm


/-! ### Test functions on the particle torus -/

theorem contDiff_mFourier_particleLift {d : ℕ} {N : ℕ+} (n : Fin N × Fin d → ℤ) :
    ContDiff ℝ ∞ (fun y : Fin N → Fin d → ℝ =>
      UnitAddTorus.mFourier n (particleUncurry d N (particleLift y))) := by
  have h : ∀ y : Fin N → Fin d → ℝ,
      UnitAddTorus.mFourier n (particleUncurry d N (particleLift y))
        = ∏ p : Fin N × Fin d, Complex.exp (2 * Real.pi * Complex.I * (n p) * (y p.1 p.2) / (1 : ℝ)) := by
    intro y
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, particleUncurry_apply, particleLift,
      torusLift, SharpLSI.liftT]
    exact Finset.prod_congr rfl fun p _ => fourier_coe_apply
  simp_rw [h]
  refine contDiff_prod fun p _ => Complex.contDiff_exp.comp ?_
  have : ContDiff ℝ ∞ (fun y : Fin N → Fin d → ℝ => ((y p.1 p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ p.2).comp (contDiff_apply ℝ _ p.1))
  exact (contDiff_const.mul this).div_const _

theorem isSmoothPeriodicParticle_re_mFourier {d : ℕ} {N : ℕ+} (n : Fin N × Fin d → ℤ) :
    IsSmoothPeriodicParticle (fun x : ParticleSpace d N =>
      (UnitAddTorus.mFourier n (particleUncurry d N x)).re) :=
  Complex.reCLM.contDiff.comp (contDiff_mFourier_particleLift n)

theorem isSmoothPeriodicParticle_im_mFourier {d : ℕ} {N : ℕ+} (n : Fin N × Fin d → ℤ) :
    IsSmoothPeriodicParticle (fun x : ParticleSpace d N =>
      (UnitAddTorus.mFourier n (particleUncurry d N x)).im) :=
  Complex.imCLM.contDiff.comp (contDiff_mFourier_particleLift n)

/-- A real `L²(m^N)` function orthogonal to every smooth periodic test vanishes a.e. -/
theorem ae_eq_zero_of_forall_integral_mul_eq_zero_particle {d : ℕ} {N : ℕ+}
    {h : ParticleSpace d N → ℝ} (hh : MemLp h 2 (particleHaar d N))
    (H : ∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ →
      ∫ x, h x * φ x ∂particleHaar d N = 0) :
    h =ᵐ[particleHaar d N] 0 := by
  have he := measurePreserving_particleUncurry d N
  set ν' : Measure (Fin N × Fin d → UnitAddCircle) :=
    Measure.pi fun _ : Fin N × Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)
  set h' : (Fin N × Fin d → UnitAddCircle) → ℝ := h ∘ (particleUncurry d N).symm with hh'_def
  have hh' : MemLp h' 2 ν' := hh.comp_measurePreserving he.symm
  have key : ∀ ψ : (Fin N × Fin d → UnitAddCircle) → ℝ,
      ∫ x, h' x * ψ x ∂ν' = ∫ x, h x * ψ (particleUncurry d N x) ∂particleHaar d N := by
    intro ψ
    rw [← he.integral_comp' (fun y => h' y * ψ y)]
    simp [h', MeasurableEquiv.symm_apply_apply]
  have H' : ∀ n : Fin N × Fin d → ℤ,
      ∫ x, h' x * (UnitAddTorus.mFourier n x).re ∂ν' = 0 ∧
      ∫ x, h' x * (UnitAddTorus.mFourier n x).im ∂ν' = 0 := fun n =>
    ⟨by rw [key (fun x => (UnitAddTorus.mFourier n x).re)]
        exact H _ (isSmoothPeriodicParticle_re_mFourier n),
     by rw [key (fun x => (UnitAddTorus.mFourier n x).im)]
        exact H _ (isSmoothPeriodicParticle_im_mFourier n)⟩
  have hz := ae_eq_zero_of_mFourier_orthogonal hh' H'
  have := he.quasiMeasurePreserving.ae_eq_comp hz
  filter_upwards [this] with x hx
  simpa [h', MeasurableEquiv.symm_apply_apply] using hx


/-! ### Bounded tests and integrability -/

theorem memLp_top_comp_particleSecT {d : ℕ} {N : ℕ+} {G : (Fin N → Fin d → ℝ) → ℝ}
    (hG : Continuous G) :
    MemLp (fun x : ParticleSpace d N => G (fun i => SharpLSI.secT (x i))) ∞ (particleHaar d N) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin N => Icc (0 : Fin d → ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hm : Measurable fun x : ParticleSpace d N => fun i => SharpLSI.secT (x i) :=
    Measurable.of_eval fun i => SharpLSI.measurable_secT.comp (measurable_pi_apply i)
  exact memLp_top_of_bound (hG.measurable.comp hm).aestronglyMeasurable C
    (Eventually.of_forall fun x => hC _ (Set.mem_univ_pi.2 fun i => secT_mem_Icc (x i)))

theorem IsSmoothPeriodicParticle.memLp_top {d : ℕ} {N : ℕ+} {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) : MemLp φ ∞ (particleHaar d N) := by
  have h := memLp_top_comp_particleSecT (d := d) (N := N) hφ.continuous
  have e : ∀ x : ParticleSpace d N, particleLift (fun i => SharpLSI.secT (x i)) = x := fun x => by
    funext i; simp [particleLift, torusLift, SharpLSI.liftT_secT]
  simpa [Function.comp_def, e] using h

theorem IsSmoothPeriodicParticle.memLp_top_particlePartial {d : ℕ} {N : ℕ+}
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) :
    MemLp (particlePartial i j φ) ∞ (particleHaar d N) :=
  memLp_top_comp_particleSecT ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem memLp_particleCoord {d : ℕ} {N : ℕ+} {μ : Measure (ParticleSpace d N)}
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : MemLp g 2 μ) (i : Fin N) (j : Fin d) :
    MemLp (fun x => g x i j) 2 μ :=
  (((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin N → Tangent d) →L[ℝ] Tangent d)).comp_memLp' hg)

theorem integrable_mul_of_memLp_two_particle {d : ℕ} {N : ℕ+} {u φ : ParticleSpace d N → ℝ}
    (hu : MemLp u 2 (particleHaar d N)) (hφ : MemLp φ ∞ (particleHaar d N)) :
    Integrable (fun x => u x * φ x) (particleHaar d N) :=
  (hu.integrable one_le_two).mul_of_top_left hφ

/-! ### The Haar-side weak Sobolev space `H¹(m^N)` -/

/-- `g = (∇₁f, …, ∇_N f)` is the weak gradient of `f` in the unweighted space `H¹(m^N)` on
`(𝕋^d)^N`: `f, g ∈ L²(m^N)` and `∫ f ∂_{ij}φ dm^N = -∫ gᵢⱼ φ dm^N` for smooth periodic `φ`. -/
structure IsParticleHaarWeakGradient {d : ℕ} (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) : Prop where
  memLp : MemLp f 2 (particleHaar d N)
  memLp_grad : MemLp g 2 (particleHaar d N)
  ibp : ∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ → ∀ (i : Fin N) (j : Fin d),
    ∫ x, f x * particlePartial i j φ x ∂particleHaar d N =
      -∫ x, g x i j * φ x ∂particleHaar d N

/-- `f ∈ H¹(m^N)`. -/
def MemParticleHaarH1 {d : ℕ} (N : ℕ+) (f : ParticleSpace d N → ℝ) : Prop :=
  ∃ g, IsParticleHaarWeakGradient N f g

/-- Weak gradients for the Gibbs weight are weak gradients for `m^N` and conversely (the
distributional identity is against `m^N` in both cases, and `L²(P_N) = L²(m^N)`). -/
theorem isParticleWeakGradient_iff {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) :
    IsParticleWeakGradient A N f g ↔ IsParticleHaarWeakGradient N f g :=
  ⟨fun h => ⟨(DGPS.Particle.memLp_particleLaw_iff A N).1 h.memLp,
      (DGPS.Particle.memLp_particleLaw_iff A N).1 h.memLp_grad, h.ibp⟩,
   fun h => ⟨(DGPS.Particle.memLp_particleLaw_iff A N).2 h.memLp,
      (DGPS.Particle.memLp_particleLaw_iff A N).2 h.memLp_grad, h.ibp⟩⟩

theorem memParticleH1_iff {d : ℕ} (A : InteractionData d) (N : ℕ+) (f : ParticleSpace d N → ℝ) :
    MemParticleH1 A N f ↔ MemParticleHaarH1 N f :=
  exists_congr fun g => isParticleWeakGradient_iff A N f g

/-! ### A.e. uniqueness of the particle weak gradient -/

/-- Uniqueness of the weak gradient on `(𝕋^d)^N` (Fourier argument on `𝕋^{dN}`). -/
theorem IsParticleHaarWeakGradient.ae_eq {d : ℕ} {N : ℕ+} {f : ParticleSpace d N → ℝ}
    {g g' : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleHaarWeakGradient N f g) (hg' : IsParticleHaarWeakGradient N f g') :
    g =ᵐ[particleHaar d N] g' := by
  have hj : ∀ (i : Fin N) (j : Fin d), (fun x => g x i j - g' x i j) =ᵐ[particleHaar d N] 0 := by
    intro i j
    refine ae_eq_zero_of_forall_integral_mul_eq_zero_particle
      ((memLp_particleCoord hg.memLp_grad i j).sub (memLp_particleCoord hg'.memLp_grad i j))
      fun φ hφ => ?_
    have e1 := hg.ibp φ hφ i j
    have e2 := hg'.ibp φ hφ i j
    simp_rw [sub_mul]
    rw [integral_sub (integrable_mul_of_memLp_two_particle (memLp_particleCoord hg.memLp_grad i j)
      hφ.memLp_top) (integrable_mul_of_memLp_two_particle
      (memLp_particleCoord hg'.memLp_grad i j) hφ.memLp_top)]
    linarith
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hj i)] with x hx
  funext i
  ext j
  simpa [sub_eq_zero] using hx i j

/-- Uniqueness of the weak gradient for the Gibbs weight, a.e. for `P_N` (equivalently `m^N`). -/
theorem IsParticleWeakGradient.ae_eq {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleSpace d N → ℝ} {g g' : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleWeakGradient A N f g) (hg' : IsParticleWeakGradient A N f g') :
    g =ᵐ[particleLaw A N] g' :=
  (DGPS.Particle.particleLaw_absolutelyContinuous A N).ae_le
    (((isParticleWeakGradient_iff A N f g).1 hg).ae_eq ((isParticleWeakGradient_iff A N f g').1 hg'))

theorem IsParticleWeakGradient.ae_eq_haar {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f : ParticleSpace d N → ℝ} {g g' : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleWeakGradient A N f g) (hg' : IsParticleWeakGradient A N f g') :
    g =ᵐ[particleHaar d N] g' :=
  ((isParticleWeakGradient_iff A N f g).1 hg).ae_eq ((isParticleWeakGradient_iff A N f g').1 hg')

/-- The chosen weak gradient of `f ∈ H¹(P_N)` agrees a.e. with every weak gradient. -/
theorem particleWeakGradient_ae_eq {d : ℕ} {A : InteractionData d} {N : ℕ+} (f : ParticleH1 A N)
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : IsParticleWeakGradient A N f.1 g) :
    particleWeakGradient f =ᵐ[particleLaw A N] g :=
  (isParticleWeakGradient_particleWeakGradient f).ae_eq hg

/-- The Gibbs energy is independent of the choice of weak gradient. -/
theorem particleEnergy_eq_of_isParticleWeakGradient {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) {g : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleWeakGradient A N f.1 g) :
    particleEnergy A N f = ∫ x, particleTangentNormSq (g x) ∂particleLaw A N := by
  unfold particleEnergy
  refine integral_congr_ae ?_
  filter_upwards [particleWeakGradient_ae_eq f hg] with x hx
  rw [hx]

/-! ### DEF017: weight bounds and the Sobolev equivalence -/

/-- DEF017 (weights): for every fixed `N`, `0 < c ≤ dP_N/dm^N ≤ C < ∞`; stated both for the
explicit density and for the Radon–Nikodym derivative. -/
theorem particle_weight_bounds {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ x, c ≤ particleDensity A N x ∧ particleDensity A N x ≤ C) ∧
      (∀ᵐ x ∂particleHaar d N,
        ENNReal.ofReal c ≤ (particleLaw A N).rnDeriv (particleHaar d N) x ∧
        (particleLaw A N).rnDeriv (particleHaar d N) x ≤ ENNReal.ofReal C) := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  refine ⟨c, C, hc, hcC, hb, ?_⟩
  have := Measure.rnDeriv_withDensity (particleHaar d N)
    (DGPS.Particle.particleDensity_measurable A N).ennreal_ofReal
  filter_upwards [this] with x hx
  rw [particleLaw, hx]
  exact ⟨ENNReal.ofReal_le_ofReal (hb x).1, ENNReal.ofReal_le_ofReal (hb x).2⟩

/-- The squared `H¹(μ)` norm `‖f‖₂² + ‖g‖₂²` of a function and its gradient. -/
noncomputable def particleH1NormSq {d : ℕ} {N : ℕ+} (μ : Measure (ParticleSpace d N))
    (f : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d) : ℝ :=
  ∫ x, f x ^ 2 ∂μ + ∫ x, particleTangentNormSq (g x) ∂μ

/-- The unweighted Dirichlet energy `∫ ∑ᵢ |∇ᵢ f|² dm^N` of a test in `H¹(P_N)` (the same space as
`H¹(m^N)`), computed with the chosen weak gradient. -/
noncomputable def particleHaarEnergy {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) : ℝ :=
  ∫ x, particleTangentNormSq (particleWeakGradient f x) ∂particleHaar d N

theorem integral_particleLaw_mono {d : ℕ} (A : InteractionData d) (N : ℕ+)
    {F : ParticleSpace d N → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hF : Integrable F (particleHaar d N))
    {c C : ℝ} (hb : ∀ x, c ≤ particleDensity A N x ∧ particleDensity A N x ≤ C) (hc : 0 ≤ c) :
    c * ∫ x, F x ∂particleHaar d N ≤ ∫ x, F x ∂particleLaw A N ∧
      ∫ x, F x ∂particleLaw A N ≤ C * ∫ x, F x ∂particleHaar d N := by
  have hC : 0 ≤ C := hc.trans ((hb (fun _ => 0 : ParticleSpace d N) |>.1).trans (hb _).2)
  have hint : Integrable (fun x => particleDensity A N x * F x) (particleHaar d N) := by
    refine Integrable.mono' (hF.const_mul C)
      ((DGPS.Particle.particleDensity_measurable A N).aestronglyMeasurable.mul hF.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (DGPS.Particle.particleDensity_pos A N x).le (hF0 x))]
    exact mul_le_mul_of_nonneg_right (hb x).2 (hF0 x)
  rw [DGPS.Particle.integral_particleLaw]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hF.const_mul c) hint fun x =>
      mul_le_mul_of_nonneg_right (hb x).1 (hF0 x)
  · rw [← integral_const_mul]
    exact integral_mono hint (hF.const_mul C) fun x =>
      mul_le_mul_of_nonneg_right (hb x).2 (hF0 x)

theorem integrable_sq_of_memLp {d : ℕ} {N : ℕ+} {μ : Measure (ParticleSpace d N)}
    {f : ParticleSpace d N → ℝ} (hf : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ :=
  hf.integrable_sq

theorem integrable_particleTangentNormSq {d : ℕ} {N : ℕ+} {μ : Measure (ParticleSpace d N)}
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : MemLp g 2 μ) :
    Integrable (fun x => particleTangentNormSq (g x)) μ := by
  unfold particleTangentNormSq
  refine integrable_finsetSum _ fun i _ => ?_
  have h : MemLp (fun x => g x i) 2 μ :=
    ((ContinuousLinearMap.proj i : (Fin N → Tangent d) →L[ℝ] Tangent d)).comp_memLp' hg
  exact h.norm.integrable_sq

/-- DEF017 (Sobolev equivalence). For every fixed `N`, with `c ≤ dP_N/dm^N ≤ C`:
`H¹(P_N) = H¹(m^N)` as sets, with the same distributional weak gradient (a.e. unique), and the
squared norms are equivalent with constants `c, C`. No `N`-uniformity is asserted. -/
theorem particleSobolev_equiv {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ f : ParticleSpace d N → ℝ, MemParticleH1 A N f ↔ MemParticleHaarH1 N f) ∧
      (∀ f g, IsParticleWeakGradient A N f g ↔ IsParticleHaarWeakGradient N f g) ∧
      (∀ f g, IsParticleHaarWeakGradient N f g →
        c * particleH1NormSq (particleHaar d N) f g ≤ particleH1NormSq (particleLaw A N) f g ∧
        particleH1NormSq (particleLaw A N) f g ≤ C * particleH1NormSq (particleHaar d N) f g) ∧
      (∀ f g g', IsParticleWeakGradient A N f g → IsParticleWeakGradient A N f g' →
        g =ᵐ[particleLaw A N] g' ∧ g =ᵐ[particleHaar d N] g') := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  refine ⟨c, C, hc, hcC, memParticleH1_iff A N, isParticleWeakGradient_iff A N, ?_,
    fun f g g' hg hg' => ⟨hg.ae_eq hg', hg.ae_eq_haar hg'⟩⟩
  intro f g hg
  obtain ⟨h1, h2⟩ := integral_particleLaw_mono A N (fun x => sq_nonneg (f x))
    (integrable_sq_of_memLp hg.memLp) hb hc.le
  obtain ⟨k1, k2⟩ := integral_particleLaw_mono A N
    (fun x => Finset.sum_nonneg fun i _ => sq_nonneg ‖g x i‖)
    (integrable_particleTangentNormSq hg.memLp_grad) hb hc.le
  unfold particleH1NormSq particleTangentNormSq
  constructor <;> linarith

/-- Energy equivalence on `H¹(P_N) = H¹(m^N)`. -/
theorem particleEnergy_equiv {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ f : ParticleH1 A N,
      c * particleHaarEnergy f ≤ particleEnergy A N f ∧
      particleEnergy A N f ≤ C * particleHaarEnergy f := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  refine ⟨c, C, hc, hcC, fun f => ?_⟩
  have hg := (isParticleWeakGradient_iff A N _ _).1 (isParticleWeakGradient_particleWeakGradient f)
  exact integral_particleLaw_mono A N
    (fun x => Finset.sum_nonneg fun i _ => sq_nonneg ‖particleWeakGradient f x i‖)
    (integrable_particleTangentNormSq hg.memLp_grad) hb hc.le

end DGPS
