import DGRHS.Commutator.SourceRieszBrownianTrigExpectation

/-! Measurability and uniform properness of the literal empirical stopped
physical gradient square, and exact complex time-integral conversion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_empirical_stopped_square_measurable_bound
    (N k : ℕ) (hN : 0<N) (t θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ)
    (hf : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (hX : Measurable (Function.uncurry X)) :
    let H := fun r ω=>∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      ∂sourceRieszLocalEmpiricalLaw N (X r ω)
    Measurable (Function.uncurry H) ∧
      ∀ r ω,‖H r ω‖≤((G:ℝ)*(∑ a,|θ a|))^2 := by
  dsimp only
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  let C := ((G:ℝ)*(∑ a,|θ a|))^2
  have hSm : Measurable (fun p:ℝ×E=>S p.1 p.2) :=
    measurable_sourceRieszStopped_square k t θ f hf
  refine ⟨?_,?_⟩
  · have he : (fun p:ℝ×Ω=>∫ z,S p.1 z ∂sourceRieszLocalEmpiricalLaw N (X p.1 p.2))=
        (fun p:ℝ×Ω=>(N:ℝ)⁻¹*∑ i:Fin N,S p.1 (X p.1 p.2 i)) :=
      funext fun p=>integral_sourceRieszLocalEmpiricalLaw N (X p.1 p.2) _
    change Measurable (fun p:ℝ×Ω=>∫ z,S p.1 z ∂sourceRieszLocalEmpiricalLaw N (X p.1 p.2))
    rw [he]
    exact (Finset.measurable_sum _ fun i _=>hSm.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX))).const_mul _
  · intro r ω
    letI := sourceRieszLocalEmpiricalLaw_probability N hN (X r ω)
    have hh : ∀ᵐ z ∂sourceRieszLocalEmpiricalLaw N (X r ω),‖S r z‖≤C :=
      ae_of_all _ (fun z=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact sourceRieszStopped_square_bound k t θ f G hb r z)
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=sourceRieszLocalEmpiricalLaw N (X r ω)) hh

lemma sourceRieszBrownianTimeOn_integral_complex (T : ℝ≥0) (h : ℝ→ℂ) :
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

lemma sourceRieszBrownianTimeOn_setIntegral_complex (T s : ℝ≥0) (h : ℝ→ℂ) :
    (∫ r in Ioc 0 s,h (r:ℝ) ∂sourceRieszBrownianTimeOn T)=
      ∫ r in Ioc 0 (min (s:ℝ) (T:ℝ)),h r := by
  rw [sourceRieszBrownianTimeOn,Measure.restrict_restrict measurableSet_Ioc,Ioc_inter_Ioc,max_self]
  exact sourceRieszBrownianTimeOn_integral_complex (min s T) h

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_empirical_stopped_square_measurable_bound
#print axioms DGRHS.Commutator.sourceRiesz_empirical_stopped_square_measurable_bound
#check @DGRHS.Commutator.sourceRieszBrownianTimeOn_integral_complex
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn_integral_complex
#check @DGRHS.Commutator.sourceRieszBrownianTimeOn_setIntegral_complex
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn_setIntegral_complex
