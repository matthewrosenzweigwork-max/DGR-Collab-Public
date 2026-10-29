import DGRHS.Commutator.SourceLogPrimitiveForceBridge
import DGRHS.Commutator.SourceRieszSourceMartingaleAssembly

/-! Actual logarithmic primitive Itô admissibility and fixed martingales.
Only the force/empirical-drift bridge at zero is used. The initial statistic
and empirical drift are literal logarithmic objects. Brownian coefficients,
energy and sin/cos formulas are interaction-independent. Fixed martingales
are selected before every weight vector; expected phase is a conclusion.
This new body awaits actual restricted diagnostics and independent review. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceLogPhysicalItoAdmissibility
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  empirical : ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceLogPrimitiveEmpiricalIto P F T β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))
  trigonometric : ∀ (θ : Fin k→ℝ) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hU : ∀ b,IsStronglyPredictable F (U b))
      (hUb : ∀ b r ω,‖U b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))),
      (∀ᵐ ω ∂P,∀ r b,U b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) →
      SourceRieszPrimitiveActualTrigIto P F T N B U hU
        (|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))) hUb
        (fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω)))

lemma SourceLogPhysicalItoAdmissibility.to_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B) :
    SourceRieszPhysicalItoAdmissibility P F T 0 β N k t ρ₀ f G X B := by
  constructor
  · intro V hV hVb he
    exact (sourceLogPrimitiveEmpiricalIto_iff_zero P F T β N k t f X B _).mp
      (h.empirical V hV hVb he)
  · intro θ U hU hUb he
    simpa only [sourceRieszDynamicEmpiricalDifference_eq_log] using h.trigonometric θ U hU hUb he

lemma SourceLogPhysicalItoAdmissibility.of_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszPhysicalItoAdmissibility P F T 0 β N k t ρ₀ f G X B) :
    SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B := by
  constructor
  · intro V hV hVb he
    exact (sourceLogPrimitiveEmpiricalIto_iff_zero P F T β N k t f X B _).mpr
      (h.empirical V hV hVb he)
  · intro θ U hU hUb he
    simpa only [sourceRieszDynamicEmpiricalDifference_eq_log] using h.trigonometric θ U hU hUb he

lemma SourceLogPhysicalItoAdmissibility.horizon_extension
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B) :
    SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G
      (sourceRieszParticleRealHorizonExtension T N X) B := by
  exact SourceLogPhysicalItoAdmissibility.of_zero P F T β N k t ρ₀ f G _ B
    (SourceRieszPhysicalItoAdmissibility.horizon_extension P F T 0 β N k t ht ρ₀ f G X B
      (h.to_zero P F T β N k t ρ₀ f G X B))

theorem exists_sourceLog_source_fixed_martingale_inputs
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (hβ : 0<β) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (hf0 : ∀ a,Measurable (f a 0))
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (hSDE : SourceRieszAdditiveWeakSDE P F T 0 β N X B)
    (hIto : SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B) :
    ∃ m : Fin k→ℝ→Ω→ℝ,
      (∀ a,Measurable (Function.uncurry (m a))) ∧
      (∀ a ω,m a 0 ω=0) ∧
      (∀ a,∀ᵐ ω ∂P,Continuous (fun r:ℝ=>m a r ω)) ∧
      (∀ a,Martingale (fun r:ℝ≥0=>m a (r:ℝ)) F P) ∧
      (∀ a (r:ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
      (∀ a,∀ᵐ ω ∂P,
        (∫ z,f a (t a) z ∂transportEmpiricalLaw N (X (t a) ω))-
          (∫ z,f a 0 z ∂transportEmpiricalLaw N (X 0 ω))=
          (∫ r in Ioc 0 (t a:ℝ),DGRHS.Dynamics.sourceLogEmpiricalTestDrift β (f a) N r (X r ω))+m a (t a) ω) ∧
      ∀ θ : Fin k→ℝ,
        let A := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω))
        let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a:ℝ)) ω)
        let H := sourceRieszEmpiricalStoppedSquare N k t θ f X
        let χ := fun r:ℝ=>∫ ω,sourceRieszFinitePhase (A ω+W r ω) ∂P
        ∀ r∈Icc 0 (T:ℝ),χ r=χ 0-(1/β:ℝ) •
          (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A ω+W u ω)*(H u ω:ℂ) ∂P) := by
  obtain ⟨m,hmm,hm0,hmc,hMart,hLp,hEmp,hPhase⟩ :=
    exists_sourceRiesz_source_fixed_martingale_inputs P F T 0 β hβ N k hN t ht ρ₀ f hf0 hgrad G hb X B
      hSDE (hIto.to_zero P F T β N k t ρ₀ f G X B)
  refine ⟨m,hmm,hm0,hmc,hMart,hLp,?_,?_⟩
  · simpa only [sourceRieszLocalEmpiricalLaw_eq_transport,sourceRieszEmpiricalTestDrift_zero_eq_log] using hEmp
  · simpa only [sourceRieszDynamicEmpiricalDifference_eq_log] using hPhase

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogPhysicalItoAdmissibility
#print axioms DGRHS.Commutator.SourceLogPhysicalItoAdmissibility
#check @DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.to_zero
#print axioms DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.to_zero
#check @DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.of_zero
#print axioms DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.of_zero
#check @DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.horizon_extension
#print axioms DGRHS.Commutator.SourceLogPhysicalItoAdmissibility.horizon_extension
#check @DGRHS.Commutator.exists_sourceLog_source_fixed_martingale_inputs
#print axioms DGRHS.Commutator.exists_sourceLog_source_fixed_martingale_inputs
