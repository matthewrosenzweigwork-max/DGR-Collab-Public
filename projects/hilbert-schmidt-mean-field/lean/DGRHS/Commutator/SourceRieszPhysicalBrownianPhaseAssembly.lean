import DGRHS.Commutator.SourceRieszPhysicalBrownianPhase

/-! Physical finite-family phase bridge for the actual common filtered Brownian
family and literal empirical gradient square. Coefficients, the bracket and
zero expectations of the transformed stochastic integrals are derived. Only
the two primitive samplewise Ito identities are conditional admissibility;
the expected phase identity is the conclusion, never an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_physical_brownian_phase
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (hβ : 0<β) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i,StronglyAdapted F (fun r:ℝ≥0=>fun ω=>X r ω i))
    (hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun r:ℝ≥0=>X r ω i))
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)
    (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A) :
    let c := Real.sqrt (2/β)/Real.sqrt N
    let K := |c| * ((G:ℝ)*(∑ a,|θ a|))
    let H := fun r ω=>∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) r z‖^2
      ∂sourceRieszLocalEmpiricalLaw N (X r ω)
    ∃ U : (Fin N×ι)→ℝ≥0→Ω→ℝ,
    ∃ hU : ∀ b,IsStronglyPredictable F (U b),
    ∃ hUb : ∀ b r ω,‖U b r ω‖≤K,
      let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
      let M := sourceRieszBrownianFamilyProcess P F B T g
      let Q := sourceRieszBrownianFamilyBracket P F T g
      ∃ R : ℝ≥0→Ω→ℝ,∃ hR : IsStronglyPredictable F R,
        let gs := fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)
        let gc := fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)
        let Ns := sourceRieszBrownianFamilyProcess P F B T gs
        let Nc := sourceRieszBrownianFamilyProcess P F B T gc
        (∀ᵐ ω ∂P,∀ r b,U b r ω=
          c*((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) ∧
        (∀ ω,R 0 ω=A ω) ∧
        (∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) ∧
        (∀ᵐ ω ∂P,Continuous (fun r=>R r ω)) ∧
        Martingale M F P ∧ Martingale (fun r ω=>(M r ω)^2-Q r ω) F P ∧
        (∀ᵐ ω ∂P,∀ s,Q s ω=(2/β)*(∫ r in Ioc 0 (min (s:ℝ) (T:ℝ)),H r ω)) ∧
        ∀ s:ℝ≥0,s≤T →
        (∀ᵐ ω ∂P,Real.cos (A ω+M s ω)=Real.cos (A ω)-Ns s ω-
          (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.cos (R (Real.toNNReal r) ω)*H r ω)) →
        (∀ᵐ ω ∂P,Real.sin (A ω+M s ω)=Real.sin (A ω)+Nc s ω-
          (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.sin (R (Real.toNNReal r) ω)*H r ω)) →
        (∫ ω,sourceRieszFinitePhase (A ω+M s ω) ∂P)=
          (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-(1/β:ℝ) •
            (∫ r in Ioc 0 (s:ℝ),∫ ω,
              sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P) := by
  dsimp only
  obtain ⟨U,hU,hUb,hcoef,hM,hML,hMc,hzero,hQ,hcomp,hbr⟩ :=
    exists_sourceRiesz_physical_brownian_integral_and_bracket P F T β hβ N k hN t ht θ
      f hgrad G hb X hXa hXc B hB
  let K := |Real.sqrt (2/β)/Real.sqrt N| * ((G:ℝ)*(∑ a,|θ a|))
  let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
  let M := sourceRieszBrownianFamilyProcess P F B T g
  obtain ⟨R,hR,hR0,hphase,hRc⟩ :=
    exists_sourceRieszBrownianFamily_predictable_phase P F B hB T g A hA
  refine ⟨U,hU,hUb,R,hR,hcoef,hR0,hphase,hRc,hM,hcomp,hbr,?_⟩
  intro s hs hcos hsin
  exact sourceRiesz_physical_brownian_expected_phase P F T β hβ N k hN t θ f hgrad G hb
    X hXm B hB U hU K hUb A hA R hR s hs hphase hcos hsin

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_physical_brownian_phase
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_brownian_phase
