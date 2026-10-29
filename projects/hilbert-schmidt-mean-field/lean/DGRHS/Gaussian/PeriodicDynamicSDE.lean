import DGRHS.Gaussian.PeriodicDynamicTerminal
import DGRHS.Gaussian.PeriodicDynamicCF
import DGRHS.Commutator.SourceRieszSourceMartingaleAssembly
import DGRHS.Commutator.SourceRieszFiniteHorizonSDE

/-!
Packet P11c, unit 4 (part 3): the torus particle system, its Itô admissibility, and the finite-family
martingale inputs, in the lifted formulation.

**Representation of the torus particle system.** The particle system on `𝕋^d` is written through its
continuous lift to `ℝ^d` (the standard coordinate form of a diffusion on the torus: the driving Brownian
motions live on `ℝ^d` and the interaction force is lattice periodic).  A configuration
`x : Fin N → ℝ^d` represents the torus configuration `π x = (periodicLift (x i))_i`; all torus
statistics (empirical measures, tests, Gibbs laws) are evaluated on `π x`.  The SDE is
`dx_i = -(1/N) Σ_{j≠i} F(π x_i - π x_j) dt + √(2/β) dB_i` with `F` the torus force (the gradient of the
smooth periodic kernel, `0` at collisions), exactly (2.31) of the source with the periodic kernel.

With this representation the Euclidean Brownian/predictable/martingale stack (which is statement-wise
independent of the kernel and of the density) is reused unchanged through the lifted tests
`periodicLiftFn (f a r)` (`periodicStoppedGrad_lift`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace BigOperators Interval Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The torus configuration represented by a lifted configuration. -/
def periodicProj (N : ℕ) (x : Fin N → E) : Fin N → PeriodicTorus ι := fun i => periodicLift (x i)

lemma continuous_periodicLift : Continuous (periodicLift : E → PeriodicTorus ι) := by
  unfold periodicLift
  exact continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (EuclideanSpace.proj i).continuous

lemma measurable_periodicLift : Measurable (periodicLift : E → PeriodicTorus ι) :=
  continuous_periodicLift.measurable

lemma measurable_periodicProj (N : ℕ) : Measurable (periodicProj (ι := ι) N) :=
  measurable_pi_iff.mpr fun i => measurable_periodicLift.comp (measurable_pi_apply i)

/-- The totalized particle drift `-(1/N) Σ_{j≠i} F(π x_i - π x_j)`. -/
def periodicParticleDrift (F : PeriodicTorus ι → E) (N : ℕ) (x : Fin N → E) (i : Fin N) : E :=
  -((N : ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i, F (periodicLift (x i) - periodicLift (x j))

/-- The Brownian vector of the `i`th particle. -/
abbrev periodicBrownianVector (N : ℕ) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) (i : Fin N) (r : ℝ≥0) (ω : Ω) : E :=
  sourceRieszParticleBrownianVector N B i r ω

/-- The additive-noise weak SDE (TeX 714-720, Remark 2.1) for `N` particles on the torus in lifted coordinates,
on the whole time axis: `X_i(r) = X_i(0) + ∫_0^r -(1/N) Σ_{j≠i} F(πX_i - πX_j) du + √(2/β)(B_i(r) - B_i(0))`
with `π` the lift to the torus and the totalized force `F(0) = 0`. -/
structure PeriodicAdditiveWeakSDE (F : PeriodicTorus ι → E) (P : Measure Ω) (Fil : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (β : ℝ) (N : ℕ) (X : ℝ → Ω → Fin N → E) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P Fil B
  jointly_measurable : Measurable (Function.uncurry X)
  adapted : ∀ i, StronglyAdapted Fil (fun r ω => X (r : ℝ) ω i)
  continuous_on_horizon : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ≥0 => X (r : ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P, ∀ i,
    IntegrableOn (fun r : ℝ => periodicParticleDrift F N (X r ω) i) (Ioc 0 (T : ℝ))
  equation : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ T → ∀ i,
    X (r : ℝ) ω i = X 0 ω i + (∫ u in Ioc 0 (r : ℝ), periodicParticleDrift F N (X u ω) i) +
      Real.sqrt (2 / β) • (periodicBrownianVector N B i r ω - periodicBrownianVector N B i 0 ω)

/-- The finite-horizon form of `PeriodicAdditiveWeakSDE`: the particle system (TeX 714-720, Remark 2.1) on `[0,T]`
in lifted coordinates, with `X` measurable and adapted on the horizon, continuous paths and an integrable drift;
this is the system of Theorem 2.13 (i). -/
structure PeriodicFiniteHorizonWeakSDE (F : PeriodicTorus ι → E) (P : Measure Ω)
    (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (N : ℕ) (X : ℝ → Ω → Fin N → E)
    (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P Fil B
  measurable_on_horizon : Measurable (fun p : Icc (0 : ℝ) (T : ℝ) × Ω => X p.1 p.2)
  adapted_on_horizon : ∀ i, ∀ r : ℝ≥0, r ≤ T → StronglyMeasurable[Fil r] (fun ω => X (r : ℝ) ω i)
  continuous_on_horizon : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ≥0 => X (r : ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P, ∀ i,
    IntegrableOn (fun r : ℝ => periodicParticleDrift F N (X r ω) i) (Ioc 0 (T : ℝ))
  equation : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ T → ∀ i,
    X (r : ℝ) ω i = X 0 ω i + (∫ u in Ioc 0 (r : ℝ), periodicParticleDrift F N (X u ω) i) +
      Real.sqrt (2 / β) • (periodicBrownianVector N B i r ω - periodicBrownianVector N B i 0 ω)

lemma PeriodicFiniteHorizonWeakSDE.extended (F : PeriodicTorus ι → E) (P : Measure Ω)
    (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (N : ℕ) (X : ℝ → Ω → Fin N → E)
    (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) (h : PeriodicFiniteHorizonWeakSDE F P Fil T β N X B) :
    PeriodicAdditiveWeakSDE F P Fil T β N (sourceRieszParticleRealHorizonExtension T N X) B := by
  let Xe := sourceRieszParticleRealHorizonExtension T N X
  have he (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : Xe r = X r :=
    sourceRieszParticleRealHorizonExtension_eq T N X r hr
  refine ⟨h.brownian, sourceRieszParticleRealHorizonExtension_measurable T N X h.measurable_on_horizon,
    sourceRieszParticleRealHorizonExtension_adapted Fil T N X h.adapted_on_horizon, ?_, ?_, ?_⟩
  · intro i
    exact (sourceRieszParticleRealHorizonExtension_continuous P T N X h.continuous_on_horizon i).mono
      (fun ω hω => hω.continuousOn)
  · filter_upwards [h.drift_integrable] with ω hω
    intro i
    apply (hω i).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change periodicParticleDrift F N (X r ω) i = periodicParticleDrift F N (Xe r ω) i
    rw [he r ⟨hr.1.le, hr.2⟩]
  · filter_upwards [h.equation] with ω hω
    intro r hr i
    have hi : (∫ u in Ioc 0 (r : ℝ), periodicParticleDrift F N (Xe u ω) i) =
        ∫ u in Ioc 0 (r : ℝ), periodicParticleDrift F N (X u ω) i := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change periodicParticleDrift F N (Xe u ω) i = periodicParticleDrift F N (X u ω) i
      rw [he u ⟨hu.1.le, hu.2.trans hr⟩]
    change Xe r ω i = Xe 0 ω i + (∫ u in Ioc 0 (r : ℝ), periodicParticleDrift F N (Xe u ω) i) + _
    rw [he r ⟨r.coe_nonneg, hr⟩, he 0 ⟨le_rfl, T.coe_nonneg⟩, hi]
    exact hω r hr i

/-- Literal initial data: the projected initial configuration has the Gibbs law, independent of the
drivers. -/
structure PeriodicInitialGibbsBrownianData (P : Measure Ω) (Q : Measure (Fin N → PeriodicTorus ι))
    (X₀ : Ω → Fin N → E) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) : Prop where
  initial_gibbs : P.map (fun ω => periodicProj N (X₀ ω)) = Q
  initial_independent_drivers : IndepFun X₀ (fun ω => fun b r => B b r ω) P

lemma periodicStoppedGrad_lift (t : ℝ) (f : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) (z : E) :
    periodicStoppedGrad t f r (periodicLift z) =
      sourceRieszStoppedGradient t (fun r => periodicLiftFn (f r)) r z := by
  unfold periodicStoppedGrad sourceRieszStoppedGradient
  split_ifs
  · exact periodicGrad_lift (f r) z
  · rfl

lemma integral_empirical_periodicProj (N : ℕ) (x : Fin N → E) (q : PeriodicTorus ι → ℝ) :
    (∫ z, q z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N x)) =
      ∫ z, periodicLiftFn q z ∂sourceRieszLocalEmpiricalLaw N x := by
  rw [integral_sourceRieszLocalEmpiricalLaw, integral_sourceRieszLocalEmpiricalLaw]
  rfl

lemma periodic_stopped_square_proj (N k : ℕ) (t : Fin k → ℝ≥0) (θ : Fin k → ℝ)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (X : ℝ → Ω → Fin N → E) (r : ℝ) (ω : Ω) :
    sourceRieszEmpiricalStoppedSquare N k t θ (fun a r => periodicLiftFn (f a r)) X r ω =
      ∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) r z‖ ^ 2
        ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X r ω)) := by
  unfold sourceRieszEmpiricalStoppedSquare
  rw [integral_sourceRieszLocalEmpiricalLaw, integral_sourceRieszLocalEmpiricalLaw]
  simp only [periodicProj, periodicStoppedGrad_lift]

lemma periodic_initial_statistic_F0 (Fil : Filtration ℝ≥0 mΩ) (N k : ℕ) (μ₀ : Measure (PeriodicTorus ι))
    (f : Fin k → PeriodicTorus ι → ℝ) (hf : ∀ a, Measurable (f a)) (θ : Fin k → ℝ)
    (X : ℝ≥0 → Ω → Fin N → E) (hXa : ∀ i, StronglyAdapted Fil (fun r ω => X r ω i)) :
    StronglyMeasurable[Fil 0] (fun ω => ∑ a, θ a *
      (Real.sqrt N * dynEmpiricalDifference μ₀ (f a) N (periodicProj N (X 0 ω)))) := by
  have hX0 : Measurable[Fil 0] (X 0) := by
    letI : MeasurableSpace Ω := Fil 0
    apply Measurable.of_eval
    intro i
    exact (hXa i 0).measurable
  have hm : Measurable[Fil 0] (fun ω => ∑ a, θ a *
      (Real.sqrt N * dynEmpiricalDifference μ₀ (f a) N (periodicProj N (X 0 ω)))) := by
    letI : MeasurableSpace Ω := Fil 0
    exact Finset.measurable_sum _ (fun a _ =>
      (((measurable_dynEmpiricalDifference_all μ₀ (f a) (hf a) N).comp
        ((measurable_periodicProj N).comp hX0)).const_mul _).const_mul _)
  exact hm.stronglyMeasurable

/-- The time-dependent empirical Itô formula with the actual fixed individual Brownian integral,
normalized as the raw martingale of TeX 3870. -/
def PeriodicPrimitiveEmpiricalIto (F : PeriodicTorus ι → E) (β : ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (N k : ℕ) (t : Fin k → ℝ≥0)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (X : ℝ → Ω → Fin N → E) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ)
    (g : Fin k → (Fin N × ι) → Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P Fil T)) : Prop :=
  ∀ a, ∀ r : ℝ≥0, r ≤ t a → ∀ᵐ ω ∂P,
    (∫ z, f a r z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X r ω))) -
      (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X 0 ω))) =
      (∫ u in Ioc 0 (r : ℝ), periodicEmpiricalTestDrift F β (f a) N u (periodicProj N (X u ω))) +
        sourceRieszBrownianFamilyProcess P Fil B T (g a) r ω / Real.sqrt N

/-- Source-authorized primitive Itô admissibility (source 865(i), 1046, 3870-3881) restricted to the
actual physical coefficient families; no expected phase or terminal duality is an input. -/
structure PeriodicItoAdmissibility (F : PeriodicTorus ι → E) (P : Measure Ω) [IsProbabilityMeasure P]
    (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (N k : ℕ) (t : Fin k → ℝ≥0)
    (μ₀ : Measure (PeriodicTorus ι)) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (X : ℝ → Ω → Fin N → E) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) : Prop where
  empirical : ∀ (V : Fin k → (Fin N × ι) → ℝ≥0 → Ω → ℝ)
      (hV : ∀ a b, IsStronglyPredictable Fil (V a b))
      (hVb : ∀ a b r ω, ‖V a b r ω‖ ≤ |Real.sqrt (2 / β) / Real.sqrt N| * (G : ℝ)),
      (∀ᵐ ω ∂P, ∀ a b r, V a b r ω = (Real.sqrt (2 / β) / Real.sqrt N) *
        (periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2) →
      PeriodicPrimitiveEmpiricalIto F β P Fil T N k t f X B
        (fun a b => sourceRieszPredictableBoundedL2 P Fil T (V a b) (hV a b)
          (|Real.sqrt (2 / β) / Real.sqrt N| * (G : ℝ)) (hVb a b))
  trigonometric : ∀ (θ : Fin k → ℝ) (U : (Fin N × ι) → ℝ≥0 → Ω → ℝ)
      (hU : ∀ b, IsStronglyPredictable Fil (U b))
      (hUb : ∀ b r ω, ‖U b r ω‖ ≤ |Real.sqrt (2 / β) / Real.sqrt N| * ((G : ℝ) * (∑ a, |θ a|))),
      (∀ᵐ ω ∂P, ∀ r b, U b r ω = (Real.sqrt (2 / β) / Real.sqrt N) *
        ((∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2)) →
      SourceRieszPrimitiveActualTrigIto P Fil T N B U hU
        (|Real.sqrt (2 / β) / Real.sqrt N| * ((G : ℝ) * (∑ a, |θ a|))) hUb
        (fun ω => ∑ a, θ a * (Real.sqrt N *
          dynEmpiricalDifference μ₀ (f a 0) N (periodicProj N (X 0 ω))))

lemma PeriodicPrimitiveEmpiricalIto.horizon_extension (F : PeriodicTorus ι → E) (β : ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (N k : ℕ) (t : Fin k → ℝ≥0)
    (ht : ∀ a, t a ≤ T) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (X : ℝ → Ω → Fin N → E)
    (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ)
    (g : Fin k → (Fin N × ι) → Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P Fil T))
    (h : PeriodicPrimitiveEmpiricalIto F β P Fil T N k t f X B g) :
    PeriodicPrimitiveEmpiricalIto F β P Fil T N k t f (sourceRieszParticleRealHorizonExtension T N X) B g := by
  intro a r hr
  have he (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
      sourceRieszParticleRealHorizonExtension T N X u = X u :=
    sourceRieszParticleRealHorizonExtension_eq T N X u hu
  have hi (ω : Ω) : (∫ u in Ioc 0 (r : ℝ), periodicEmpiricalTestDrift F β (f a) N u
      (periodicProj N (sourceRieszParticleRealHorizonExtension T N X u ω))) =
      ∫ u in Ioc 0 (r : ℝ), periodicEmpiricalTestDrift F β (f a) N u (periodicProj N (X u ω)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change periodicEmpiricalTestDrift F β (f a) N u
      (periodicProj N (sourceRieszParticleRealHorizonExtension T N X u ω)) = _
    rw [he u ⟨hu.1.le, hu.2.trans (hr.trans (ht a))⟩]
  simpa only [he r ⟨r.coe_nonneg, hr.trans (ht a)⟩, he 0 ⟨le_rfl, T.coe_nonneg⟩, hi] using h a r hr

lemma PeriodicItoAdmissibility.horizon_extension (F : PeriodicTorus ι → E) (P : Measure Ω)
    [IsProbabilityMeasure P] (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (N k : ℕ)
    (t : Fin k → ℝ≥0) (ht : ∀ a, t a ≤ T) (μ₀ : Measure (PeriodicTorus ι))
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0) (X : ℝ → Ω → Fin N → E)
    (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ) (h : PeriodicItoAdmissibility F P Fil T β N k t μ₀ f G X B) :
    PeriodicItoAdmissibility F P Fil T β N k t μ₀ f G (sourceRieszParticleRealHorizonExtension T N X) B := by
  have hext (a : Fin k) (r : ℝ) (ω : Ω) (i : Fin N) :
      periodicStoppedGrad (t a : ℝ) (f a) r (periodicLift (sourceRieszParticleRealHorizonExtension T N X r ω i)) =
        periodicStoppedGrad (t a : ℝ) (f a) r (periodicLift (X r ω i)) := by
    by_cases hr : r ∈ Icc 0 (t a : ℝ)
    · rw [sourceRieszParticleRealHorizonExtension_eq T N X r ⟨hr.1, hr.2.trans (ht a)⟩]
    · simp only [periodicStoppedGrad, ite_eq_right hr]
  constructor
  · intro V hV hVb he
    have he' : ∀ᵐ ω ∂P, ∀ a b r, V a b r ω = (Real.sqrt (2 / β) / Real.sqrt N) *
        (periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2 := by
      simpa only [hext] using he
    exact PeriodicPrimitiveEmpiricalIto.horizon_extension F β P Fil T N k t ht f X B _
      (h.empirical V hV hVb he')
  · intro θ U hU hUb he
    have he' : ∀ᵐ ω ∂P, ∀ r b, U b r ω = (Real.sqrt (2 / β) / Real.sqrt N) *
        ((∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2) := by
      simpa only [hext] using he
    simpa only [sourceRieszParticleRealHorizonExtension_eq T N X 0 ⟨le_rfl, T.coe_nonneg⟩]
      using h.trigonometric θ U hU hUb he'

lemma periodic_primitive_empirical_Ito_normalized (F : PeriodicTorus ι → E) (β : ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (N k : ℕ) (hN : 0 < N)
    (t : Fin k → ℝ≥0) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (X : ℝ → Ω → Fin N → E)
    (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ)
    (g : Fin k → (Fin N × ι) → Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P Fil T))
    (hIto : PeriodicPrimitiveEmpiricalIto F β P Fil T N k t f X B g)
    (m : Fin k → ℝ → Ω → ℝ)
    (hme : ∀ᵐ ω ∂P, ∀ (a : Fin k) (r : ℝ≥0), Real.sqrt N * m a r ω =
      sourceRieszBrownianFamilyProcess P Fil B T (g a) r ω) :
    ∀ a, ∀ r : ℝ≥0, r ≤ t a → ∀ᵐ ω ∂P,
      (∫ z, f a r z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X r ω))) -
        (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X 0 ω))) =
        (∫ u in Ioc 0 (r : ℝ), periodicEmpiricalTestDrift F β (f a) N u (periodicProj N (X u ω))) +
          m a r ω := by
  intro a r hr
  have hn : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  filter_upwards [hIto a r hr, hme] with ω hIω hmω
  have hraw : sourceRieszBrownianFamilyProcess P Fil B T (g a) r ω / Real.sqrt N = m a r ω := by
    rw [← hmω a r]
    field_simp [hn]
  simpa only [hraw] using hIω

lemma gradient_periodicLiftFn_eq (f : PeriodicTorus ι → ℝ) (z : E) :
    gradient (periodicLiftFn f) z = periodicGrad f (periodicLift z) :=
  (periodicGrad_lift f z).symm

/-- Finite-family stochastic adapter (torus form of `exists_sourceRiesz_source_fixed_martingale_inputs`):
the fixed raw martingales, the empirical terminal identity and the expected-phase identity. -/
theorem exists_periodic_fixed_martingale_inputs (F : PeriodicTorus ι → E) (P : Measure Ω)
    [IsProbabilityMeasure P] (Fil : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hβ : 0 < β) (N k : ℕ)
    (hN : 0 < N) (t : Fin k → ℝ≥0) (ht : ∀ a, t a ≤ T) (μ₀ : Measure (PeriodicTorus ι))
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (hf0 : ∀ a, Measurable (f a 0))
    (hgrad : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a : ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ))
    (X : ℝ → Ω → Fin N → E) (B : (Fin N × ι) → ℝ≥0 → Ω → ℝ)
    (hSDE : PeriodicAdditiveWeakSDE F P Fil T β N X B)
    (hIto : PeriodicItoAdmissibility F P Fil T β N k t μ₀ f G X B) :
    ∃ m : Fin k → ℝ → Ω → ℝ,
      (∀ a, Measurable (Function.uncurry (m a))) ∧
      (∀ a ω, m a 0 ω = 0) ∧
      (∀ a, ∀ᵐ ω ∂P, Continuous (fun r : ℝ => m a r ω)) ∧
      (∀ a, Martingale (fun r : ℝ≥0 => m a (r : ℝ)) Fil P) ∧
      (∀ a (r : ℝ≥0), MemLp (m a (r : ℝ)) 2 P) ∧
      (∀ a, ∀ᵐ ω ∂P,
        (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X (t a) ω))) -
          (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X 0 ω))) =
          (∫ r in Ioc 0 (t a : ℝ), periodicEmpiricalTestDrift F β (f a) N r (periodicProj N (X r ω))) +
            m a (t a) ω) ∧
      ∀ θ : Fin k → ℝ,
        let A := fun ω => ∑ a, θ a * (Real.sqrt N *
          dynEmpiricalDifference μ₀ (f a 0) N (periodicProj N (X 0 ω)))
        let W := fun r ω => ∑ a, θ a * (Real.sqrt N * m a (min r (t a : ℝ)) ω)
        let H := fun r ω => ∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) r z‖ ^ 2
          ∂sourceRieszLocalEmpiricalLaw N (periodicProj N (X r ω))
        let χ := fun r : ℝ => ∫ ω, sourceRieszFinitePhase (A ω + W r ω) ∂P
        ∀ r ∈ Icc 0 (T : ℝ), χ r = χ 0 - (1 / β : ℝ) •
          (∫ u in 0..r, ∫ ω, sourceRieszFinitePhase (A ω + W u ω) * (H u ω : ℂ) ∂P) := by
  classical
  let ft : Fin k → ℝ → E → ℝ := fun a r => periodicLiftFn (f a r)
  have hbt : ∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖gradient (ft a r) z‖ ≤ (G : ℝ) := by
    intro a r hr z
    simpa only [ft, gradient_periodicLiftFn_eq] using hb a r hr (periodicLift z)
  have hEmp := hIto.empirical
  have hTrig := hIto.trigonometric
  let c := Real.sqrt (2 / β) / Real.sqrt N
  let Xe := sourceRieszParticleHorizonExtension T N X
  have hXea := sourceRieszParticleHorizonExtension_adapted Fil T N X hSDE.adapted
  have hXec := sourceRieszParticleHorizonExtension_continuous P T N X hSDE.continuous_on_horizon
  have hext (a : Fin k) (r : ℝ≥0) (ω : Ω) (i : Fin N) :
      periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (Xe r ω i)) =
        periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω i)) := by
    rw [periodicStoppedGrad_lift, periodicStoppedGrad_lift]
    exact sourceRieszParticleHorizonExtension_stopped_gradient T (t a) (ht a) N X (ft a) r ω i
  obtain ⟨V, hV, hVb, hVz, hVe, hVm⟩ := exists_sourceRiesz_physical_fixed_martingales
    P Fil T N k hN t c ft hgrad G hbt Xe hXea hXec B hSDE.brownian
  have hVe' : ∀ᵐ ω ∂P, ∀ a b r, V a b r ω = c *
      (periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2 := by
    filter_upwards [hVe] with ω hω
    intro a b r
    rw [hω a b r, ← hext a r ω b.1, periodicStoppedGrad_lift]
  let gV := fun a b => sourceRieszPredictableBoundedL2 P Fil T (V a b) (hV a b) (|c| * (G : ℝ)) (hVb a b)
  obtain ⟨m, hmm, hm0, hmc, hMart, hLp, hme, hId⟩ := hVm
  refine ⟨m, hmm, hm0, hmc, hMart, hLp, ?_, ?_⟩
  · intro a
    exact periodic_primitive_empirical_Ito_normalized F β P Fil T N k hN t f X B gV
      (hEmp V hV hVb hVe') m hme a (t a) le_rfl
  · intro θ A W H χ
    obtain ⟨U, hU, hUb, hUe⟩ := exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
      P Fil N k t θ c ft hgrad G hbt Xe hXea hXec
    have hUe' : ∀ᵐ ω ∂P, ∀ r b, U b r ω = c *
        ((∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2) := by
      filter_upwards [hUe] with ω hω
      intro r b
      have h1 := hω r b
      have h2 : ∀ a, sourceRieszStoppedGradient (t a : ℝ) (ft a) (r : ℝ) (Xe r ω b.1) =
          periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1)) := fun a => by
        rw [← hext a r ω b.1, periodicStoppedGrad_lift]
      simpa only [h2] using h1
    let Kθ := |c| * ((G : ℝ) * (∑ a, |θ a|))
    let g := fun b => sourceRieszPredictableBoundedL2 P Fil T (U b) (hU b) Kθ (hUb b)
    have he (b : Fin N × ι) : ∀ᵐ ω ∂P, ∀ r, U b r ω = ∑ a, θ a * V a b r ω := by
      filter_upwards [hUe', hVe'] with ω hu hv
      intro r
      have hh := map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (β := fun _ : ι => ℝ) b.2)
        (fun a => θ a • periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) Finset.univ
      have heval : (∑ a, θ a • periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2 =
          ∑ a, θ a * (periodicStoppedGrad (t a : ℝ) (f a) (r : ℝ) (periodicLift (X r ω b.1))) b.2 := by
        simpa only [PiLp.projₗ_apply, PiLp.smul_apply, smul_eq_mul] using hh
      rw [hu r b, heval, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [hv a b r]; ring)
    have hg : g = (fun b => ∑ a, θ a • gV a b) := by
      funext b
      exact sourceRieszPredictableBoundedL2_linear_combination P Fil T (U b) (hU b) Kθ (hUb b)
        (fun a => V a b) (fun a => hV a b) (|c| * (G : ℝ)) (fun a => hVb a b) θ (he b)
    have hW : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, sourceRieszBrownianFamilyProcess P Fil B T g r ω = W r ω := by
      rw [hg]
      exact hId θ
    have hW0 : ∀ ω, W 0 ω = 0 := by
      intro ω
      change (∑ a, θ a * (Real.sqrt N * m a (min 0 (t a : ℝ)) ω)) = 0
      apply Finset.sum_eq_zero
      intro a _
      simp only [min_eq_left (t a).coe_nonneg, hm0, mul_zero]
    have hA : StronglyMeasurable[Fil 0] A :=
      periodic_initial_statistic_F0 Fil N k μ₀ (fun a => f a 0) hf0 θ (fun r ω => X (r : ℝ) ω) hSDE.adapted
    have hphase := sourceRiesz_primitive_actual_Ito_expected_stopped_phase P Fil T β hβ N k hN t θ ft
      hgrad G hbt X hSDE.jointly_measurable B hSDE.brownian U hU Kθ hUb
      (by
        filter_upwards [hUe'] with ω hω
        intro r b
        rw [hω r b]
        simp only [periodicStoppedGrad_lift, ft]
        rfl)
      A hA (hTrig θ U hU hUb hUe') W hW0 hW
    intro r hr
    have hHeq : sourceRieszEmpiricalStoppedSquare N k t θ ft X = H := by
      funext u ω
      exact periodic_stopped_square_proj N k t θ f X u ω
    have := hphase r hr
    rw [hHeq] at this
    exact this

end DGRHS.Periodic
