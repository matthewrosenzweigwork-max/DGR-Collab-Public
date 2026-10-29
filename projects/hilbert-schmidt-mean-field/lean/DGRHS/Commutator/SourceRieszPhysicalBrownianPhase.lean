import DGRHS.Commutator.SourceRieszPhysicalPhaseInputs

/-! Physical finite-family phase bridge for the actual common filtered Brownian
family and literal empirical gradient square. The preceding physical assembly
constructs the coefficients and bracket; this consumer derives proper zero
expectations of the transformed stochastic integrals. Only
the two primitive samplewise Ito identities are conditional admissibility;
the expected phase identity is the conclusion, never an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszEmpiricalStoppedSquare (N k : ℕ) (t : Fin k→ℝ≥0) (θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E) (r : ℝ) (ω : Ω) : ℝ :=
  ∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) r z‖^2
    ∂sourceRieszLocalEmpiricalLaw N (X r ω)

lemma sourceRieszEmpiricalStoppedSquare_data
    (N k : ℕ) (hN : 0<N) (t : Fin k→ℝ≥0) (θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (sourceRieszEmpiricalStoppedSquare N k t θ f X)) ∧
      ∀ r ω,‖sourceRieszEmpiricalStoppedSquare N k t θ f X r ω‖≤((G:ℝ)*(∑ a,|θ a|))^2 := by
  exact sourceRiesz_empirical_stopped_square_measurable_bound (Ω:=Ω) (ι:=ι)
    N k hN (fun a=>(t a:ℝ)) θ f hgrad G hb X hXm

theorem sourceRiesz_physical_brownian_expected_phase
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
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R) (s : ℝ≥0) (hs : s≤T) :
    let H := sourceRieszEmpiricalStoppedSquare N k t θ f X
    let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
    let M := sourceRieszBrownianFamilyProcess P F B T g
    let gs := fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hUb b)
    let gc := fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hUb b)
    let Ns := sourceRieszBrownianFamilyProcess P F B T gs
    let Nc := sourceRieszBrownianFamilyProcess P F B T gc
    (∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) →
    (∀ᵐ ω ∂P,Real.cos (A ω+M s ω)=Real.cos (A ω)-Ns s ω-
      (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.cos (R (Real.toNNReal r) ω)*H r ω)) →
    (∀ᵐ ω ∂P,Real.sin (A ω+M s ω)=Real.sin (A ω)+Nc s ω-
      (1/β)*(∫ r in Ioc 0 (s:ℝ),Real.sin (R (Real.toNNReal r) ω)*H r ω)) →
    (∫ ω,sourceRieszFinitePhase (A ω+M s ω) ∂P)=
      (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-(1/β:ℝ) •
        (∫ r in Ioc 0 (s:ℝ),∫ ω,
          sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P) := by
  intro H g M gs gc Ns Nc hphase hcos hsin
  have hHdata : Measurable (Function.uncurry H) ∧
      ∀ r ω,‖H r ω‖≤((G:ℝ)*(∑ a,|θ a|))^2 :=
    sourceRieszEmpiricalStoppedSquare_data N k hN t θ f hgrad G hb X hXm
  obtain ⟨hHm,hHb⟩ := hHdata
  have hmap : Measurable (fun p:ℝ≥0×Ω=>((p.1:ℝ),p.2)) :=
    (NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd
  have hHm' := hHm.comp hmap
  dsimp only [Function.comp_def,Function.uncurry] at hHm'
  have hn (r:ℝ≥0) : Real.toNNReal (r:ℝ)=r := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ r.coe_nonneg
  have hcint (ω:Ω) :
      (∫ r in Ioc 0 s,Real.cos (R r ω)*H r ω ∂sourceRieszBrownianTimeOn T)=
        ∫ r in Ioc 0 (s:ℝ),Real.cos (R (Real.toNNReal r) ω)*H r ω := by
    simpa only [hn,min_eq_left (show (s:ℝ)≤(T:ℝ) from hs)] using
      sourceRieszBrownianTimeOn_setIntegral_real T s
        (fun r=>Real.cos (R (Real.toNNReal r) ω)*H r ω)
  have hsint (ω:Ω) :
      (∫ r in Ioc 0 s,Real.sin (R r ω)*H r ω ∂sourceRieszBrownianTimeOn T)=
        ∫ r in Ioc 0 (s:ℝ),Real.sin (R (Real.toNNReal r) ω)*H r ω := by
    simpa only [hn,min_eq_left (show (s:ℝ)≤(T:ℝ) from hs)] using
      sourceRieszBrownianTimeOn_setIntegral_real T s
        (fun r=>Real.sin (R (Real.toNNReal r) ω)*H r ω)
  have he := sourceRieszBrownian_samplewise_trig_expected_phase P F T B hB U hU K hUb
    A hA R hR (fun r:ℝ≥0=>H r) hHm' (((G:ℝ)*(∑ a,|θ a|))^2)
    (fun r ω=>hHb r ω) (1/β) s hphase
    (by simpa only [hcint] using hcos) (by simpa only [hsint] using hsin)
  have htime :
      (∫ r in Ioc 0 s,∫ ω,sourceRieszFinitePhase (A ω+M r ω)*(H r ω:ℂ) ∂P
        ∂sourceRieszBrownianTimeOn T)=
      ∫ r in Ioc 0 (s:ℝ),∫ ω,sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P := by
    simpa only [hn,min_eq_left (show (s:ℝ)≤(T:ℝ) from hs)] using
      sourceRieszBrownianTimeOn_setIntegral_complex T s
        (fun r=>∫ ω,sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P)
  exact he.trans (congrArg (fun z:ℂ=>(∫ ω,sourceRieszFinitePhase (A ω) ∂P)-(1/β:ℝ) • z) htime)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_physical_brownian_expected_phase
#print axioms DGRHS.Commutator.sourceRiesz_physical_brownian_expected_phase

#check @DGRHS.Commutator.sourceRieszEmpiricalStoppedSquare
#print axioms DGRHS.Commutator.sourceRieszEmpiricalStoppedSquare

#check @DGRHS.Commutator.sourceRieszEmpiricalStoppedSquare_data
#print axioms DGRHS.Commutator.sourceRieszEmpiricalStoppedSquare_data
