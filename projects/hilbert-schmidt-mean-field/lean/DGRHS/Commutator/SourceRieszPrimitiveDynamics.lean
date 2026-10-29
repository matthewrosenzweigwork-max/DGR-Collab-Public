import DGRHS.Commutator.SourceRieszPhysicalBrownianPhaseHorizon
import DGRHS.Commutator.SourceRieszAdjointPhysicalDrift
import DGRHS.Commutator.SourceRieszFiniteTerminal
import DGRHS.CLT.SourceRieszSingularGibbs

/-! Literal source SDE/initial data and source-authorized primitive Itô
admissibility (source714--721,865(i),1046,3870--3881). The admissibility
predicates contain the actual fixed Brownian integrals and actual coefficient
energy. The physical energy normalization and expected phase are conclusions.
The finite-horizon extension uses the same supplied filtration. No existence,
uniqueness, general Itô theorem, terminal duality, or original CLT is claimed.
The collision-zero force still requires its collision-occupation adapter. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval
namespace DGRHS.Commutator
open DGRHS.CLT
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszParticleSDEDrift (s : ℝ) (N : ℕ) (x : Fin N→E) (i : Fin N) : E :=
  -((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,sourceRieszForce s (x i-x j)

def sourceRieszParticleBrownianVector (N : ℕ)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (i : Fin N) (r : ℝ≥0) (ω : Ω) : E :=
  WithLp.toLp 2 (fun j => B (i,j) r ω)

structure SourceRieszAdditiveWeakSDE
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P F B
  jointly_measurable : Measurable (Function.uncurry X)
  adapted : ∀ i,StronglyAdapted F (fun r ω => X (r:ℝ) ω i)
  continuous_on_horizon : ∀ i,∀ᵐ ω ∂P,
    ContinuousOn (fun r : ℝ≥0 => X (r:ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P,∀ i,
    IntegrableOn (fun r : ℝ => sourceRieszParticleSDEDrift s N (X r ω) i) (Ioc 0 (T:ℝ))
  equation : ∀ᵐ ω ∂P,∀ r : ℝ≥0,r≤T → ∀ i,
    X (r:ℝ) ω i = X 0 ω i +
      (∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift s N (X u ω) i) +
      Real.sqrt (2/β) • (sourceRieszParticleBrownianVector N B i r ω-
        sourceRieszParticleBrownianVector N B i 0 ω)

/-- Literal source initial data, with possible correlations between particles.
This is an assumption from source865(i), not an independence statement about
initial observables and completed adapted stochastic integrals. -/
structure SourceRieszInitialGibbsBrownianData
    (P : Measure Ω) (s β : ℝ) (ρ : E→ℝ) (N : ℕ)
    (X₀ : Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  initial_gibbs : P.map X₀ = sourceRieszSingularGibbs s β ρ N
  initial_independent_drivers : IndepFun X₀ (fun ω => fun b r => B b r ω) P


/-- Constant continuation after the original finite horizon, on the same
filtration. It does not change a stopped test before its terminal time. -/
def sourceRieszParticleHorizonExtension (T : ℝ≥0) (N : ℕ)
    (X : ℝ→Ω→Fin N→E) (r : ℝ≥0) (ω : Ω) : Fin N→E := X (min r T:ℝ≥0) ω

lemma sourceRieszParticleHorizonExtension_adapted
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (hX : ∀ i,StronglyAdapted F (fun r ω=>X (r:ℝ) ω i)) :
    ∀ i,StronglyAdapted F (fun r ω=>sourceRieszParticleHorizonExtension T N X r ω i) := by
  intro i r
  exact (hX i (min r T)).mono (F.mono (min_le_left _ _))

lemma sourceRieszParticleHorizonExtension_continuous
    (P : Measure Ω) (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (hX : ∀ i,∀ᵐ ω ∂P,ContinuousOn (fun r:ℝ≥0=>X (r:ℝ) ω i) (Icc 0 T)) :
    ∀ i,∀ᵐ ω ∂P,Continuous (fun r=>sourceRieszParticleHorizonExtension T N X r ω i) := by
  intro i
  filter_upwards [hX i] with ω hω
  exact hω.comp_continuous (continuous_id.min continuous_const)
    (fun r=>⟨zero_le,min_le_right _ _⟩)

lemma sourceRieszParticleHorizonExtension_stopped_gradient
    (T a : ℝ≥0) (ha : a≤T) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (f : ℝ→E→ℝ) (r : ℝ≥0) (ω : Ω) (i : Fin N) :
    sourceRieszStoppedGradient (a:ℝ) f (r:ℝ) (sourceRieszParticleHorizonExtension T N X r ω i)=
      sourceRieszStoppedGradient (a:ℝ) f (r:ℝ) (X r ω i) := by
  by_cases hr : r≤a
  · simp only [sourceRieszParticleHorizonExtension,min_eq_left (hr.trans ha)]
  · have hr' : ¬(r:ℝ)∈Icc 0 (a:ℝ) := fun hh=>hr hh.2
    simp only [sourceRieszStoppedGradient,if_neg hr']

/-- The time-dependent empirical Itô formula uses the actual fixed individual
Brownian integral, normalized exactly as the raw martingale in source3870. -/
def SourceRieszPrimitiveEmpiricalIto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) : Prop :=
  ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
    (∫ z,f a r z ∂sourceRieszLocalEmpiricalLaw N (X r ω))-
      (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
      (∫ u in Ioc 0 (r:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N u (X u ω))+
        sourceRieszBrownianFamilyProcess P F B T (g a) r ω/Real.sqrt N

/-- Only the actual finite-driver integral and its actual bounded sin/cos
transforms appear. For original use, U is the identified physical coefficient
family and A is the initial Gibbs statistic. This is a source-admissibility
predicate, not a newly proved general stochastic chain rule. -/
def SourceRieszPrimitiveActualTrigIto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (N : ℕ) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (U : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hU : ∀ b,IsStronglyPredictable F (U b))
    (K : ℝ) (hUb : ∀ b r ω,‖U b r ω‖≤K) (A : Ω→ℝ) : Prop :=
  let g := fun b => sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
  let M := sourceRieszBrownianFamilyProcess P F B T g
  ∀ (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R),
    (∀ ω,R 0 ω=A ω) → (∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) →
    let gs := fun b => sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)
    let gc := fun b => sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)
    ∀ r : ℝ≥0,r≤T →
      (∀ᵐ ω ∂P,Real.cos (A ω+M r ω)=Real.cos (A ω)-
        sourceRieszBrownianFamilyProcess P F B T gs r ω-
        (1/2:ℝ)*(∫ u in Ioc 0 (r:ℝ),Real.cos (R (Real.toNNReal u) ω)*
          ∑ b,(U b (Real.toNNReal u) ω)^2)) ∧
      (∀ᵐ ω ∂P,Real.sin (A ω+M r ω)=Real.sin (A ω)+
        sourceRieszBrownianFamilyProcess P F B T gc r ω-
        (1/2:ℝ)*(∫ u in Ioc 0 (r:ℝ),Real.sin (R (Real.toNNReal u) ω)*
          ∑ b,(U b (Real.toNNReal u) ω)^2))

lemma sourceRiesz_actual_coefficient_energy_physical
    (P : Measure Ω) (β : ℝ) (hβ : 0<β) (N k : ℕ)
    (t : Fin k→ℝ≥0) (θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (he : ∀ᵐ ω ∂P,∀ r b,U b r ω=
      (Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) :
    ∀ᵐ ω ∂P,∀ r : ℝ≥0,(∑ b,(U b r ω)^2)=
      (2/β)*sourceRieszEmpiricalStoppedSquare N k t θ f X r ω := by
  filter_upwards [he] with ω hω
  intro r
  simp_rw [hω r]
  rw [sourceRiesz_physical_coordinate_square β hβ N
    (fun i => ∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω i))]
  unfold sourceRieszEmpiricalStoppedSquare
  rw [integral_sourceRieszLocalEmpiricalLaw]
  ring

lemma sourceRiesz_actual_energy_time_integral_physical
    (P : Measure Ω) (β : ℝ) (hβ : 0<β) (N k : ℕ)
    (t : Fin k→ℝ≥0) (θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (he : ∀ᵐ ω ∂P,∀ r b,U b r ω=
      (Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) :
    ∀ᵐ ω ∂P,∀ (a : ℝ→ℝ) (r : ℝ≥0),
      (1/2:ℝ)*(∫ u in Ioc 0 (r:ℝ),a u*(∑ b,(U b (Real.toNNReal u) ω)^2))=
        (1/β)*(∫ u in Ioc 0 (r:ℝ),a u*sourceRieszEmpiricalStoppedSquare N k t θ f X u ω) := by
  filter_upwards [sourceRiesz_actual_coefficient_energy_physical P β hβ N k t θ f X U he]
    with ω hω
  intro a r
  have hi : (∫ u in Ioc 0 (r:ℝ),a u*(∑ b,(U b (Real.toNNReal u) ω)^2))=
      ∫ u in Ioc 0 (r:ℝ),(2/β)*(a u*sourceRieszEmpiricalStoppedSquare N k t θ f X u ω) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hh := hω (Real.toNNReal u)
    rw [Real.coe_toNNReal _ hu.1.le] at hh
    change a u*(∑ b,(U b (Real.toNNReal u) ω)^2)=
      (2/β)*(a u*sourceRieszEmpiricalStoppedSquare N k t θ f X u ω)
    rw [hh]
    ring
  rw [hi,integral_const_mul]
  ring

lemma sourceRiesz_primitive_empirical_Ito_normalized_version
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (hN : 0<N) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (hIto : SourceRieszPrimitiveEmpiricalIto P F T s β N k t f X B g)
    (m : Fin k→ℝ→Ω→ℝ)
    (hme : ∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),Real.sqrt N*m a r ω=
      sourceRieszBrownianFamilyProcess P F B T (g a) r ω) :
    ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
      (∫ z,f a r z ∂sourceRieszLocalEmpiricalLaw N (X r ω))-
        (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
        (∫ u in Ioc 0 (r:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N u (X u ω))+m a r ω := by
  intro a r hr
  have hn : Real.sqrt (N:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  filter_upwards [hIto a r hr,hme] with ω hIω hmω
  have hraw : sourceRieszBrownianFamilyProcess P F B T (g a) r ω/Real.sqrt N=m a r ω := by
    rw [← hmω a r]
    field_simp [hn]
  simpa only [hraw] using hIω


/-- The source primitive formulas for the actual coefficient energy imply the
physical expected identity for any identified real-time version, including the
fixed stopped sum constructed before all weights. -/
theorem sourceRiesz_primitive_actual_Ito_expected_stopped_phase
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (hβ : 0<β) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X))
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)
    (U : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hU : ∀ b,IsStronglyPredictable F (U b))
    (K : ℝ) (hUb : ∀ b r ω,‖U b r ω‖≤K)
    (he : ∀ᵐ ω ∂P,∀ r b,U b r ω=
      (Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2))
    (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A)
    (hIto : SourceRieszPrimitiveActualTrigIto P F T N B U hU K hUb A)
    (W : ℝ→Ω→ℝ) (hW0 : ∀ ω,W 0 ω=0)
    (hW : ∀ᵐ ω ∂P,∀ r:ℝ≥0,
      sourceRieszBrownianFamilyProcess P F B T
        (fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)) r ω=W r ω) :
    let H := sourceRieszEmpiricalStoppedSquare N k t θ f X
    let χ := fun r:ℝ=>∫ ω,sourceRieszFinitePhase (A ω+W r ω) ∂P
    ∀ r∈Icc 0 (T:ℝ),χ r=χ 0-(1/β:ℝ) •
      (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A ω+W u ω)*(H u ω:ℂ) ∂P) := by
  intro H χ r hr
  let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
  let M := sourceRieszBrownianFamilyProcess P F B T g
  change ∀ᵐ ω ∂P,∀ r:ℝ≥0,M r ω=W r ω at hW
  obtain ⟨R,hR,hR0,hRe,hRc⟩ :=
    exists_sourceRieszBrownianFamily_predictable_phase P F B hB T g A hA
  let q := Real.toNNReal r
  have hqr : (q:ℝ)=r := Real.coe_toNNReal _ hr.1
  have hqT : q≤T := by
    change (q:ℝ)≤(T:ℝ)
    rw [hqr]
    exact hr.2
  obtain ⟨hc,hs⟩ := hIto R hR hR0 hRe q hqT
  have henergy := sourceRiesz_actual_energy_time_integral_physical P β hβ N k t θ f X U he
  have hc' : ∀ᵐ ω ∂P,Real.cos (A ω+M q ω)=Real.cos (A ω)-
      sourceRieszBrownianFamilyProcess P F B T
        (fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)) q ω-
      (1/β)*(∫ u in Ioc 0 (q:ℝ),Real.cos (R (Real.toNNReal u) ω)*H u ω) := by
    filter_upwards [hc,henergy] with ω hcω hEω
    exact hcω.trans (congrArg (fun z:ℝ=>Real.cos (A ω)-
      sourceRieszBrownianFamilyProcess P F B T
        (fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)) q ω-z)
      (hEω (fun u=>Real.cos (R (Real.toNNReal u) ω)) q))
  have hs' : ∀ᵐ ω ∂P,Real.sin (A ω+M q ω)=Real.sin (A ω)+
      sourceRieszBrownianFamilyProcess P F B T
        (fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)) q ω-
      (1/β)*(∫ u in Ioc 0 (q:ℝ),Real.sin (R (Real.toNNReal u) ω)*H u ω) := by
    filter_upwards [hs,henergy] with ω hsω hEω
    exact hsω.trans (congrArg (fun z:ℝ=>Real.sin (A ω)+
      sourceRieszBrownianFamilyProcess P F B T
        (fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)) q ω-z)
      (hEω (fun u=>Real.sin (R (Real.toNNReal u) ω)) q))
  have hi := sourceRiesz_physical_brownian_expected_phase P F T β hβ N k hN t θ f
    hgrad G hb X hXm B hB U hU K hUb A hA R hR q hqT hRe hc' hs'
  have hχ : (∫ ω,sourceRieszFinitePhase (A ω+M q ω) ∂P)=χ r := by
    apply integral_congr_ae
    filter_upwards [hW] with ω hω
    rw [hω q,hqr]
  have hχ0 : (∫ ω,sourceRieszFinitePhase (A ω) ∂P)=χ 0 := by
    simp only [χ,hW0,add_zero]
  have hInt : (∫ u in Ioc 0 (q:ℝ),∫ ω,
      sourceRieszFinitePhase (A ω+M (Real.toNNReal u) ω)*(H u ω:ℂ) ∂P)=
      ∫ u in Ioc 0 r,∫ ω,sourceRieszFinitePhase (A ω+W u ω)*(H u ω:ℂ) ∂P := by
    rw [hqr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    apply integral_congr_ae
    filter_upwards [hW] with ω hω
    rw [hω (Real.toNNReal u),Real.coe_toNNReal _ hu.1.le]
  rw [hχ,hχ0,hInt] at hi
  simpa only [intervalIntegral.integral_of_le hr.1] using hi

lemma sourceRiesz_physical_initial_statistic_F0
    (F : Filtration ℝ≥0 mΩ) (N k : ℕ) (ρ : E→ℝ)
    (f : Fin k→E→ℝ) (hf : ∀ a,Measurable (f a)) (θ : Fin k→ℝ)
    (X : ℝ≥0→Ω→Fin N→E)
    (hXa : ∀ i,StronglyAdapted F (fun r ω=>X r ω i)) :
    StronglyMeasurable[F 0] (fun ω=>∑ a,θ a*
      (Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ (f a) N (X 0 ω))) := by
  have hX0 : Measurable[F 0] (X 0) := by
    letI : MeasurableSpace Ω := F 0
    apply Measurable.of_eval
    intro i
    exact (hXa i 0).measurable
  have hm : Measurable[F 0] (fun ω=>∑ a,θ a*
      (Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ (f a) N (X 0 ω))) := by
    exact Finset.measurable_sum _ (fun a _=>
      ((measurable_sourceRiesz_empirical_fluctuation ρ (f a) (hf a) N).comp hX0).const_mul _)
  exact hm.stronglyMeasurable

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRieszParticleSDEDrift
#print axioms DGRHS.Commutator.sourceRieszParticleSDEDrift
#check @DGRHS.Commutator.sourceRieszParticleBrownianVector
#print axioms DGRHS.Commutator.sourceRieszParticleBrownianVector
#check @DGRHS.Commutator.SourceRieszAdditiveWeakSDE
#print axioms DGRHS.Commutator.SourceRieszAdditiveWeakSDE
#check @DGRHS.Commutator.SourceRieszInitialGibbsBrownianData
#print axioms DGRHS.Commutator.SourceRieszInitialGibbsBrownianData
#check @DGRHS.Commutator.sourceRieszParticleHorizonExtension
#print axioms DGRHS.Commutator.sourceRieszParticleHorizonExtension
#check @DGRHS.Commutator.sourceRieszParticleHorizonExtension_adapted
#print axioms DGRHS.Commutator.sourceRieszParticleHorizonExtension_adapted
#check @DGRHS.Commutator.sourceRieszParticleHorizonExtension_continuous
#print axioms DGRHS.Commutator.sourceRieszParticleHorizonExtension_continuous
#check @DGRHS.Commutator.sourceRieszParticleHorizonExtension_stopped_gradient
#print axioms DGRHS.Commutator.sourceRieszParticleHorizonExtension_stopped_gradient
#check @DGRHS.Commutator.SourceRieszPrimitiveEmpiricalIto
#print axioms DGRHS.Commutator.SourceRieszPrimitiveEmpiricalIto
#check @DGRHS.Commutator.SourceRieszPrimitiveActualTrigIto
#print axioms DGRHS.Commutator.SourceRieszPrimitiveActualTrigIto
#check @DGRHS.Commutator.sourceRiesz_actual_coefficient_energy_physical
#print axioms DGRHS.Commutator.sourceRiesz_actual_coefficient_energy_physical
#check @DGRHS.Commutator.sourceRiesz_actual_energy_time_integral_physical
#print axioms DGRHS.Commutator.sourceRiesz_actual_energy_time_integral_physical
#check @DGRHS.Commutator.sourceRiesz_primitive_empirical_Ito_normalized_version
#print axioms DGRHS.Commutator.sourceRiesz_primitive_empirical_Ito_normalized_version
#check @DGRHS.Commutator.sourceRiesz_primitive_actual_Ito_expected_stopped_phase
#print axioms DGRHS.Commutator.sourceRiesz_primitive_actual_Ito_expected_stopped_phase
#check @DGRHS.Commutator.sourceRiesz_physical_initial_statistic_F0
#print axioms DGRHS.Commutator.sourceRiesz_physical_initial_statistic_F0
