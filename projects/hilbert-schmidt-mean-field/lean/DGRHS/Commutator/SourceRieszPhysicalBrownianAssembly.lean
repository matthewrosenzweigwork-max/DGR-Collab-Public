import DGRHS.Commutator.SourceRieszPhysicalBrownianBracket

/-! Exact transport from the constructed nonnegative-time Lebesgue integral to
the real-time integral in the DGR source, and assembly for actual independently
driven particle gradients. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator

lemma sourceRieszBrownianTimeOn_integral_real (T : ℝ≥0) (h : ℝ→ℝ) :
    (∫ r,h (r:ℝ) ∂sourceRieszBrownianTimeOn T)=∫ r in Ioc 0 (T:ℝ),h r := by
  rw [sourceRieszBrownianTimeOn,←integral_indicator measurableSet_Ioc]
  have he : (Ioc 0 T).indicator (fun r:ℝ≥0=>h (r:ℝ))=
      (fun r:ℝ≥0=>(Ioc 0 (T:ℝ)).indicator h (r:ℝ)) := by
    funext r
    have hpos : (0:ℝ≥0)<r ↔ (0:ℝ)<(r:ℝ) := Iff.rfl
    simp only [Set.indicator_apply,mem_Ioc,hpos,NNReal.coe_le_coe]
  rw [he]
  change (∫ r : {x:ℝ // 0≤x},(Ioc 0 (T:ℝ)).indicator h r
    ∂Measure.comap Subtype.val volume)=_
  calc
    _ = ∫ r in Ici (0:ℝ),(Ioc 0 (T:ℝ)).indicator h r :=
      integral_subtype_comap (μ:=(volume:Measure ℝ)) (s:=Ici (0:ℝ)) measurableSet_Ici _
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr (show Ioc 0 (T:ℝ)⊆Ici 0 from fun r hr=>hr.1.le)]

lemma sourceRieszBrownianTimeOn_setIntegral_real (T s : ℝ≥0) (h : ℝ→ℝ) :
    (∫ r in Ioc 0 s,h (r:ℝ) ∂sourceRieszBrownianTimeOn T)=
      ∫ r in Ioc 0 (min (s:ℝ) (T:ℝ)),h r := by
  rw [sourceRieszBrownianTimeOn,Measure.restrict_restrict measurableSet_Ioc,Ioc_inter_Ioc,max_self]
  exact sourceRieszBrownianTimeOn_integral_real (min s T) h

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_physical_brownian_integral_and_bracket
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (hβ : 0<β) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (hXa : ∀ i,StronglyAdapted F (fun r:ℝ≥0=>fun ω=>X r ω i))
    (hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun r:ℝ≥0=>X r ω i))
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B) :
    let c := Real.sqrt (2/β)/Real.sqrt N
    let K := |c| * ((G:ℝ)*(∑ a,|θ a|))
    ∃ U : (Fin N×ι)→ℝ≥0→Ω→ℝ,
    ∃ hU : ∀ b,IsStronglyPredictable F (U b),
    ∃ hUb : ∀ b r ω,‖U b r ω‖≤K,
      let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
      let M := sourceRieszBrownianFamilyProcess P F B T g
      let Q := sourceRieszBrownianFamilyBracket P F T g
      (∀ᵐ ω ∂P,∀ r b,U b r ω=
        c*((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) ∧
      Martingale M F P ∧ (∀ s,MemLp (M s) 2 P) ∧
      (∀ᵐ ω ∂P,Continuous (fun s=>M s ω)) ∧
      (∀ ω,M 0 ω=0) ∧ IsStronglyPredictable F Q ∧
      Martingale (fun s ω=>(M s ω)^2-Q s ω) F P ∧
      ∀ᵐ ω ∂P,∀ s,Q s ω=(2/β)*(∫ r in Ioc 0 (min (s:ℝ) (T:ℝ)),
        ∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) r z‖^2
          ∂sourceRieszLocalEmpiricalLaw N (X r ω)) := by
  dsimp only
  obtain ⟨U,hU,hUb,he⟩ := exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
    P F N k t θ (Real.sqrt (2/β)/Real.sqrt N) f hgrad G hb
      (fun r:ℝ≥0=>X r) hXa hXc
  refine ⟨U,hU,hUb,he,?_⟩
  let K := |Real.sqrt (2/β)/Real.sqrt N| * ((G:ℝ)*(∑ a,|θ a|))
  let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hUb b)
  have hm := sourceRieszBrownianFamilyProcess_martingale P F B hB T g
  refine ⟨hm.1,hm.2.1,hm.2.2,sourceRieszBrownianFamilyProcess_zero P F B T g,
    sourceRieszBrownianFamilyBracket_predictable P F T g,
    sourceRieszBrownianFamilyProcess_compensated_square P F B hB T g,?_⟩
  filter_upwards [sourceRieszBrownianFamilyBracket_physical P F T β hβ N k t θ f
    (fun r:ℝ≥0=>X r) U hU K hUb he] with ω hω
  intro s
  rw [hω s]
  congr 1
  exact sourceRieszBrownianTimeOn_setIntegral_real T s (fun r=>
    ∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) r z‖^2
      ∂sourceRieszLocalEmpiricalLaw N (X r ω))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianTimeOn_integral_real
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn_integral_real
#check @DGRHS.Commutator.sourceRieszBrownianTimeOn_setIntegral_real
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn_setIntegral_real
#check @DGRHS.Commutator.exists_sourceRiesz_physical_brownian_integral_and_bracket
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_brownian_integral_and_bracket
