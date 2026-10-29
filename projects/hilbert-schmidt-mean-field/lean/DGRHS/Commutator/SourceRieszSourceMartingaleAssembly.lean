import DGRHS.Commutator.SourceRieszPrimitiveDynamics
import DGRHS.Commutator.SourceRieszFiniteHorizonSDE
import DGRHS.Commutator.SourceRieszPhysicalFixedMartingales
import DGRHS.Commutator.SourceRieszPredictableLinearIdentification

/-! UNCOMPILED successor. The source's primitive samplewise Itô admissibility
is stated only for predictable versions of the actual physical coefficients.
Fixed individual raw martingales are chosen before all weight vectors. The
expected phase and empirical terminal identities are conclusions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Primitive source865(i) admissibility, restricted to the actual physical
coefficient families. It contains no expected-phase or terminal-duality input. -/
structure SourceRieszPhysicalItoAdmissibility
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  empirical : ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceRieszPrimitiveEmpiricalIto P F T s β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))
  trigonometric : ∀ (θ : Fin k→ℝ) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hU : ∀ b,IsStronglyPredictable F (U b))
      (hUb : ∀ b r ω,‖U b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))),
      (∀ᵐ ω ∂P,∀ r b,U b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) →
      SourceRieszPrimitiveActualTrigIto P F T N B U hU
        (|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))) hUb
        (fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω)))

lemma SourceRieszPhysicalItoAdmissibility.horizon_extension
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszPhysicalItoAdmissibility P F T s β N k t ρ₀ f G X B) :
    SourceRieszPhysicalItoAdmissibility P F T s β N k t ρ₀ f G
      (sourceRieszParticleRealHorizonExtension T N X) B := by
  have hext (a:Fin k) (r:ℝ) (ω:Ω) (i:Fin N) :
      sourceRieszStoppedGradient (t a:ℝ) (f a) r
        (sourceRieszParticleRealHorizonExtension T N X r ω i)=
        sourceRieszStoppedGradient (t a:ℝ) (f a) r (X r ω i) :=
    sourceRieszParticleRealHorizonExtension_stopped_gradient T (t a) (ht a) N X (f a) r ω i
  constructor
  · intro V hV hVb he
    have he' : ∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 := by
      simpa only [hext] using he
    exact SourceRieszPrimitiveEmpiricalIto.horizon_extension P F T s β N k t ht f X B _
      (h.empirical V hV hVb he')
  · intro θ U hU hUb he
    have he' : ∀ᵐ ω ∂P,∀ r b,U b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) := by
      simpa only [hext] using he
    simpa only [sourceRieszParticleRealHorizonExtension_eq T N X 0 ⟨le_rfl,T.coe_nonneg⟩]
      using h.trigonometric θ U hU hUb he'

/-- Exact finite-family stochastic adapter to the original dynamic consumer.
The SDE and source-admissibility assumptions refer to one actual configuration
process and one common filtered Brownian family. -/
theorem exists_sourceRiesz_source_fixed_martingale_inputs
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hβ : 0<β) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (hf0 : ∀ a,Measurable (f a 0))
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (hSDE : SourceRieszAdditiveWeakSDE P F T s β N X B)
    (hIto : SourceRieszPhysicalItoAdmissibility P F T s β N k t ρ₀ f G X B) :
    ∃ m : Fin k→ℝ→Ω→ℝ,
      (∀ a,Measurable (Function.uncurry (m a))) ∧
      (∀ a ω,m a 0 ω=0) ∧
      (∀ a,∀ᵐ ω ∂P,Continuous (fun r:ℝ=>m a r ω)) ∧
      (∀ a,Martingale (fun r:ℝ≥0=>m a (r:ℝ)) F P) ∧
      (∀ a (r:ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
      (∀ a,∀ᵐ ω ∂P,
        (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
          (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
          (∫ r in Ioc 0 (t a:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N r (X r ω))+m a (t a) ω) ∧
      ∀ θ : Fin k→ℝ,
        let A := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω))
        let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a:ℝ)) ω)
        let H := sourceRieszEmpiricalStoppedSquare N k t θ f X
        let χ := fun r:ℝ=>∫ ω,sourceRieszFinitePhase (A ω+W r ω) ∂P
        ∀ r∈Icc 0 (T:ℝ),χ r=χ 0-(1/β:ℝ) •
          (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A ω+W u ω)*(H u ω:ℂ) ∂P) := by
  classical
  have hEmp := hIto.empirical
  have hTrig := hIto.trigonometric
  let c := Real.sqrt (2/β)/Real.sqrt N
  let Xe := sourceRieszParticleHorizonExtension T N X
  have hXea := sourceRieszParticleHorizonExtension_adapted F T N X hSDE.adapted
  have hXec := sourceRieszParticleHorizonExtension_continuous P T N X hSDE.continuous_on_horizon
  have hext (a:Fin k) (r:ℝ≥0) (ω:Ω) (i:Fin N) :
      sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (Xe r ω i)=
        sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω i) :=
    sourceRieszParticleHorizonExtension_stopped_gradient T (t a) (ht a) N X (f a) r ω i
  obtain ⟨V,hV,hVb,hVz,hVe,hVm⟩ := exists_sourceRiesz_physical_fixed_martingales
    P F T N k hN t c f hgrad G hb Xe hXea hXec B hSDE.brownian
  have hVe' : ∀ᵐ ω ∂P,∀ a b r,V a b r ω=
      c*(sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 := by
    filter_upwards [hVe] with ω hω
    intro a b r
    rw [hω a b r,hext]
  let gV := fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b) (|c| * (G:ℝ)) (hVb a b)
  obtain ⟨m,hmm,hm0,hmc,hMart,hLp,hme,hId⟩ := hVm
  refine ⟨m,hmm,hm0,hmc,hMart,hLp,?_,?_⟩
  · intro a
    exact sourceRiesz_primitive_empirical_Ito_normalized_version P F T s β N k hN t f X B
      gV (hEmp V hV hVb hVe') m hme a (t a) le_rfl
  · intro θ A W H χ
    obtain ⟨U,hU,hUb,hUe⟩ := exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
      P F N k t θ c f hgrad G hb Xe hXea hXec
    have hUe' : ∀ᵐ ω ∂P,∀ r b,U b r ω=
        c*((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) := by
      filter_upwards [hUe] with ω hω
      intro r b
      simpa only [hext] using hω r b
    let Kθ := |c| *((G:ℝ)*(∑ a,|θ a|))
    let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) Kθ (hUb b)
    have he (b:Fin N×ι) : ∀ᵐ ω ∂P,∀ r,U b r ω=∑ a,θ a*V a b r ω := by
      filter_upwards [hUe',hVe'] with ω hu hv
      intro r
      have hh := map_sum (PiLp.projₗ (𝕜:=ℝ) 2 (β:=fun _:ι=>ℝ) b.2)
        (fun a=>θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) Finset.univ
      have heval : (∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2=
          ∑ a,θ a*(sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 := by
        simpa only [PiLp.projₗ_apply,PiLp.smul_apply,smul_eq_mul] using hh
      rw [hu r b,heval,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _=>by rw [hv a b r];ring)
    have hg : g=(fun b=>∑ a,θ a • gV a b) := by
      funext b
      exact sourceRieszPredictableBoundedL2_linear_combination P F T (U b) (hU b) Kθ (hUb b)
        (fun a=>V a b) (fun a=>hV a b) (|c| * (G:ℝ)) (fun a=>hVb a b) θ (he b)
    have hW : ∀ᵐ ω ∂P,∀ r:ℝ≥0,sourceRieszBrownianFamilyProcess P F B T g r ω=W r ω := by
      rw [hg]
      exact hId θ
    have hW0 : ∀ ω,W 0 ω=0 := by
      intro ω
      change (∑ a,θ a*(Real.sqrt N*m a (min 0 (t a:ℝ)) ω))=0
      apply Finset.sum_eq_zero
      intro a _
      simp only [min_eq_left (t a).coe_nonneg,hm0,mul_zero]
    have hA : StronglyMeasurable[F 0] A :=
      sourceRiesz_physical_initial_statistic_F0 F N k ρ₀ (fun a=>f a 0) hf0 θ
        (fun r ω=>X (r:ℝ) ω) hSDE.adapted
    exact sourceRiesz_primitive_actual_Ito_expected_stopped_phase P F T β hβ N k hN t θ f
      hgrad G hb X hSDE.jointly_measurable B hSDE.brownian U hU Kθ hUb hUe' A hA
      (hTrig θ U hU hUb hUe') W hW0 hW

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.exists_sourceRiesz_source_fixed_martingale_inputs
#print axioms DGRHS.Commutator.exists_sourceRiesz_source_fixed_martingale_inputs

#check @DGRHS.Commutator.SourceRieszPhysicalItoAdmissibility
#print axioms DGRHS.Commutator.SourceRieszPhysicalItoAdmissibility
#check @DGRHS.Commutator.SourceRieszPhysicalItoAdmissibility.horizon_extension
#print axioms DGRHS.Commutator.SourceRieszPhysicalItoAdmissibility.horizon_extension
