import DGRHS.Commutator.SourceRieszBrownianRealPhase

/-! Export to the original jointly measurable real-time expected-Ito interface.
Every stochastic term in the hypotheses is the actual constructed sine/cosine
Brownian integral; the literal expected phase equation is proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRiesz_physical_brownian_expected_phase_horizon
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
    (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A)
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R) (hR0 : ∀ ω,R 0 ω=A ω) :
    let H := sourceRieszEmpiricalStoppedSquare N k t θ f X
    let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
    let M := sourceRieszBrownianFamilyProcess P F B T g
    let gs := fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)
    let gc := fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)
    let Ns := sourceRieszBrownianFamilyProcess P F B T gs
    let Nc := sourceRieszBrownianFamilyProcess P F B T gc
    (∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) →
    (∀ s:ℝ≥0,s≤T → ∀ᵐ ω ∂P,Real.cos (A ω+M s ω)=Real.cos (A ω)-Ns s ω-
      (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.cos (R (Real.toNNReal r) ω)*H r ω)) →
    (∀ s:ℝ≥0,s≤T → ∀ᵐ ω ∂P,Real.sin (A ω+M s ω)=Real.sin (A ω)+Nc s ω-
      (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.sin (R (Real.toNNReal r) ω)*H r ω)) →
    let M₀ := sourceRieszBrownianRealPhaseProcess A R
    let χ := fun r:ℝ=>∫ ω,sourceRieszFinitePhase (A ω+M₀ r ω) ∂P
    Measurable (Function.uncurry M₀) ∧
      ∀ r∈Icc 0 (T:ℝ),χ r=χ 0-(1/β:ℝ) •
        (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A ω+M₀ u ω)*(H u ω:ℂ) ∂P) := by
  intro H g M gs gc Ns Nc hphase hcos hsin M₀ χ
  refine ⟨measurable_sourceRieszBrownianRealPhaseProcess F A hA R hR,?_⟩
  intro r hr
  let s := Real.toNNReal r
  have hsr : (s:ℝ)=r := Real.coe_toNNReal _ hr.1
  have hs : s≤T := by
    change (s:ℝ)≤(T:ℝ)
    rw [hsr]
    exact hr.2
  have hi := sourceRiesz_physical_brownian_expected_phase P F T β hβ N k hN t θ f
    hgrad G hb X hXm B hB U hU K hUb A hA R hR s hs hphase (hcos s hs) (hsin s hs)
  have he := sourceRieszBrownianRealPhaseProcess_expected_export P A R M hR0 hphase H (1/β) s hi
  simpa only [hsr,intervalIntegral.integral_of_le hr.1] using he

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_physical_brownian_expected_phase_horizon
#print axioms DGRHS.Commutator.sourceRiesz_physical_brownian_expected_phase_horizon
