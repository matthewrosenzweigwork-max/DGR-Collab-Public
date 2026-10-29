import DGRHS.Commutator.SourceRieszFiniteCovariance

/-! Proper finite-horizon stopped-gradient square covariance. Native measurable
piecewise fields and indicator set integrals identify the actual square with
weighted cross integrals. No stochastic bracket realization is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_sourceRieszStoppedGradient (t : ℝ) (f : ℝ→E→ℝ)
    (hf : ContinuousOn (fun p : ℝ×E=>gradient (f p.1) p.2) (Icc 0 t ×ˢ univ)) :
    Measurable (fun p : ℝ×E=>sourceRieszStoppedGradient t f p.1 p.2) := by
  have hz : ContinuousOn (fun _ : ℝ×E=>(0:E)) (Icc 0 t ×ˢ univ)ᶜ := continuousOn_const
  have hh := hf.measurable_piecewise hz (measurableSet_Icc.prod MeasurableSet.univ)
  have heq : (Icc 0 t ×ˢ (univ : Set E)).piecewise
      (fun p=>gradient (f p.1) p.2) (fun _=>(0:E))=
      (fun p : ℝ×E=>sourceRieszStoppedGradient t f p.1 p.2) := by
    funext p
    by_cases h : p.1∈Icc 0 t <;> simp [Set.piecewise,sourceRieszStoppedGradient,h]
  rw [heq] at hh
  exact hh

lemma norm_sourceRieszStoppedGradient_le (t : ℝ) (f : ℝ→E→ℝ) (G : ℝ≥0)
    (hb : ∀ r∈Icc 0 t,∀ z,‖gradient (f r) z‖≤(G:ℝ)) (r : ℝ) (z : E) :
    ‖sourceRieszStoppedGradient t f r z‖≤(G:ℝ) := by
  by_cases hr : r∈Icc 0 t
  · simpa [sourceRieszStoppedGradient,hr] using hb r hr z
  · simp [sourceRieszStoppedGradient,hr]

lemma sourceRieszStoppedGradient_inner_eq_cut (ta tb : ℝ) (f g : ℝ→E→ℝ)
    (r : ℝ) (z : E) :
    ⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫=
      sourceRieszCrossGradientCut (min ta tb) f g (r,z) := by
  have hh : (r,z)∈Icc 0 (min ta tb) ×ˢ (univ : Set E) ↔
      r∈Icc 0 ta ∧ r∈Icc 0 tb := by
    simp only [mem_prod,mem_univ,and_true,mem_Icc,le_min_iff]
    tauto
  by_cases ha : r∈Icc 0 ta <;> by_cases hb : r∈Icc 0 tb <;>
    simp only [sourceRieszStoppedGradient,sourceRieszCrossGradientCut,Set.piecewise,
      hh,ha,hb,ite_true,ite_false,inner_zero_right,inner_zero_left,true_and,false_and]

/-- Every section is proper; the empirical law is the actual finite atomic law. -/
lemma sourceRiesz_bounded_difference_time {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (Q : ℝ×E→ℝ) (hQ : Measurable Q) (C : ℝ) (_hC : 0≤C)
    (hb : ∀ r∈Icc 0 T,∀ z,|Q (r,z)|≤C)
    (N : ℕ) (hN : 0<N) (X : ℝ→Ω→Fin N→E) (hX : Measurable (Function.uncurry X))
    (ω : Ω) :
    Integrable (fun r=>sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>Q (r,z)) N (X r ω)) (volume.restrict (Ioc 0 T)) := by
  have hm := measurable_sourceRieszEmpiricalDifference_time ρ hρ Q hQ N
    (Function.uncurry X) hX
  apply (integrable_const (2*C)).mono'
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
  letI := hp r hr'
  letI := sourceRieszLocalEmpiricalLaw_probability N hN (X r ω)
  have hb' : ∀ z,‖Q (r,z)‖≤C := fun z=>by simpa only [Real.norm_eq_abs] using hb r hr' z
  have he : |∫ z,Q (r,z) ∂sourceRieszLocalEmpiricalLaw N (X r ω)|≤C := by
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=sourceRieszLocalEmpiricalLaw N (X r ω)) (Filter.Eventually.of_forall hb')
  have hd : |∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)|≤C := by
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=gaussianRieszDensityMeasure (ρ r)) (Filter.Eventually.of_forall hb')
  change |(∫ z,Q (r,z) ∂sourceRieszLocalEmpiricalLaw N (X r ω))-
    (∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r))|≤2*C
  exact (abs_sub _ _).trans (by linarith)

/-- Terminal-time support gives the exact smaller-horizon cross integral. -/
lemma sourceRieszStopped_pair_time_integral {Ω : Type*}
    (T ta tb : ℝ) (hta : ta≤T) (_htb : tb≤T) (β : ℝ) (ρ : ℝ→E→ℝ)
    (f g : ℝ→E→ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E) (ω : Ω) :
    (2/β)*(∫ r,sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫)
      N (X r ω) ∂volume.restrict (Ioc 0 T))=
      sourceRieszCrossCovarianceError β ρ ta tb f g N X ω := by
  let U := min ta tb
  let A := fun r=>sourceRieszDynamicEmpiricalDifference (ρ r)
    (fun z=>⟪gradient (f r) z,gradient (g r) z⟫) N (X r ω)
  have heq : (fun r=>sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫)
      N (X r ω))=ᵐ[volume.restrict (Ioc 0 T)] (Ioc 0 U).indicator A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hu : r≤U
    · have ha : r∈Icc 0 ta := ⟨hr.1.le,hu.trans (min_le_left _ _)⟩
      have hb : r∈Icc 0 tb := ⟨hr.1.le,hu.trans (min_le_right _ _)⟩
      simp [sourceRieszStoppedGradient,ha,hb,Set.indicator,A,hr.1,hu,mem_Ioc]
    · have hcut : ∀ z,⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫=0 := by
        intro z
        rw [sourceRieszStoppedGradient_inner_eq_cut]
        simp [sourceRieszCrossGradientCut,Set.piecewise,U,mem_Icc,hu]
      simp only [hcut,sourceRieszDynamicEmpiricalDifference,integral_zero,sub_self]
      simp [Set.indicator,mem_Ioc,hu]
  have hsub : Ioc 0 U⊆Ioc 0 T := fun r hr=>⟨hr.1,hr.2.trans ((min_le_left _ _).trans hta)⟩
  rw [integral_congr_ae heq,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr hsub]
  rfl

/-- Spatial properness justifies the square's actual empirical/background expansion. -/
lemma sourceRieszStopped_square_difference (k : ℕ) (t θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ) (r : ℝ) (μ : Measure E) (N : ℕ) (x : Fin N→E)
    (hi : ∀ a b,Integrable
      (fun z=>⟪sourceRieszStoppedGradient (t a) (f a) r z,
        sourceRieszStoppedGradient (t b) (f b) r z⟫) μ) :
    ((∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      ∂sourceRieszLocalEmpiricalLaw N x)-
      (∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2 ∂μ))=
      ∑ a,∑ b,(θ a*θ b)*
        ((∫ z,⟪sourceRieszStoppedGradient (t a) (f a) r z,
          sourceRieszStoppedGradient (t b) (f b) r z⟫ ∂sourceRieszLocalEmpiricalLaw N x)-
        (∫ z,⟪sourceRieszStoppedGradient (t a) (f a) r z,
          sourceRieszStoppedGradient (t b) (f b) r z⟫ ∂μ)) := by
  simp_rw [sourceRieszStoppedGradientNormSq]
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>
    (integrable_sourceRieszLocalEmpiricalLaw N x _).const_mul _),
    integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>(hi a b).const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _=>(integrable_sourceRieszLocalEmpiricalLaw N x _).const_mul _),
    integral_finsetSum _ (fun b _=>(hi _ b).const_mul _),integral_const_mul,
    ←Finset.sum_sub_distrib,←mul_sub]

/-- Actual stopped-square time integral, with every sample section proper. -/
theorem sourceRieszStopped_square_time_identity {Ω : Type*} [MeasurableSpace Ω]
    (T β : ℝ) (k : ℕ) (t θ : Fin k→ℝ) (ht : ∀ a,t a≤T)
    (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (N : ℕ) (hN : 0<N) (X : ℝ→Ω→Fin N→E) (hX : Measurable (Function.uncurry X))
    (ω : Ω) :
    let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
    Integrable (fun r=>sourceRieszDynamicEmpiricalDifference (ρ r) (S r) N (X r ω))
      (volume.restrict (Ioc 0 T)) ∧
    (2/β)*(∫ r,sourceRieszDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)
      ∂volume.restrict (Ioc 0 T))=
      ∑ a,∑ b,(θ a*θ b)*sourceRieszCrossCovarianceError β ρ (t a) (t b) (f a) (f b) N X ω := by
  let Q := fun a b (p : ℝ×E)=>⟪sourceRieszStoppedGradient (t a) (f a) p.1 p.2,
    sourceRieszStoppedGradient (t b) (f b) p.1 p.2⟫
  have hQm (a b : Fin k) : Measurable (Q a b) :=
    (measurable_sourceRieszStoppedGradient (t a) (f a) (hf a)).inner
      (measurable_sourceRieszStoppedGradient (t b) (f b) (hf b))
  have hQb (a b : Fin k) (r : ℝ) (z : E) : |Q a b (r,z)|≤(G:ℝ)^2 := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [pow_two] using mul_le_mul
      (norm_sourceRieszStoppedGradient_le (t a) (f a) G (hb a) r z)
      (norm_sourceRieszStoppedGradient_le (t b) (f b) G (hb b) r z)
      (norm_nonneg _) G.coe_nonneg
  let P := fun a b r=>sourceRieszDynamicEmpiricalDifference (ρ r) (fun z=>Q a b (r,z)) N (X r ω)
  have hiP (a b : Fin k) : Integrable (P a b) (volume.restrict (Ioc 0 T)) :=
    sourceRiesz_bounded_difference_time T ρ hρ hp (Q a b) (hQm a b) ((G:ℝ)^2)
      (sq_nonneg _) (fun r _ z=>hQb a b r z) N hN X hX ω
  have hiQ (r : ℝ) (hr : r∈Icc 0 T) (a b : Fin k) :
      Integrable (fun z=>Q a b (r,z)) (gaussianRieszDensityMeasure (ρ r)) := by
    letI := hp r hr
    apply (integrable_const ((G:ℝ)^2)).mono'
      ((hQm a b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hQb a b r z
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  have heq : (fun r=>sourceRieszDynamicEmpiricalDifference (ρ r) (S r) N (X r ω))
      =ᵐ[volume.restrict (Ioc 0 T)] (fun r=>∑ a,∑ b,(θ a*θ b)*P a b r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact sourceRieszStopped_square_difference k t θ f r (gaussianRieszDensityMeasure (ρ r))
      N (X r ω) (hiQ r ⟨hr.1.le,hr.2⟩)
  have hisum : Integrable (fun r=>∑ a,∑ b,(θ a*θ b)*P a b r) (volume.restrict (Ioc 0 T)) :=
    integrable_finsetSum _ fun a _=>integrable_finsetSum _ fun b _=>(hiP a b).const_mul _
  refine ⟨hisum.congr heq.symm,?_⟩
  rw [integral_congr_ae heq,integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>(hiP a b).const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _=>(hiP _ b).const_mul _),integral_const_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  have hpair := sourceRieszStopped_pair_time_integral T (t a) (t b) (ht a) (ht b) β ρ (f a) (f b) N X ω
  change (2/β)*((θ a*θ b)*(∫ r,P a b r ∂volume.restrict (Ioc 0 T)))=_
  rw [show (2/β)*((θ a*θ b)*(∫ r,P a b r ∂volume.restrict (Ioc 0 T)))=
    (θ a*θ b)*((2/β)*(∫ r,P a b r ∂volume.restrict (Ioc 0 T))) by ring,hpair]


/-- Original physical data derive the actual stopped-square error rate. -/
theorem exists_sourceRiesz_stopped_square_covariance_replacement
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (Gmax : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N → ∀ (Ω : Type u),∀ [MeasurableSpace Ω],
      ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (f : Fin k→ℝ→E→ℝ),
      (∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r)) →
      (∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (A B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤A r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ r∈Icc 0 T,sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (A r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      let J := fun r ω=>sourceRieszDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)
      (∀ ω,Integrable (fun r=>J r ω) (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun ω=>(2/β)*(∫ r in Ioc 0 T,J r ω)) ν ∧
      (∫ ω,|(2/β)*(∫ r in Ioc 0 T,J r ω)| ∂ν)≤
        T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_finite_family_covariance_replacement
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  obtain ⟨_,hi,hb⟩ := hfactory T hT k t θ ht N hN Ω ν ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  have hsq (ω : Ω) := sourceRieszStopped_square_time_identity T β k t θ
    (fun a=>(ht a).2) ρ hρm hprob f Gmax hf hfB N (by omega) X hXm ω
  have heq : (fun ω=>(2/β)*(∫ r in Ioc 0 T,sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2) N (X r ω)))=
      (fun ω=>∑ a,∑ b,(θ a*θ b)*sourceRieszCrossCovarianceError β ρ (t a) (t b) (f a) (f b) N X ω) :=
    funext fun ω=>(hsq ω).2
  refine ⟨fun ω=>(hsq ω).1,?_,?_⟩
  · rw [heq];exact hi
  · calc
      _ = ∫ ω,|∑ a,∑ b,(θ a*θ b)*sourceRieszCrossCovarianceError β ρ (t a) (t b) (f a) (f b) N X ω| ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω=>congrArg abs (hsq ω).2)
      _ ≤ _ := hb

end DGRHS.Commutator
#check @DGRHS.Commutator.measurable_sourceRieszStoppedGradient
#print axioms DGRHS.Commutator.measurable_sourceRieszStoppedGradient
#check @DGRHS.Commutator.norm_sourceRieszStoppedGradient_le
#print axioms DGRHS.Commutator.norm_sourceRieszStoppedGradient_le
#check @DGRHS.Commutator.sourceRieszStoppedGradient_inner_eq_cut
#print axioms DGRHS.Commutator.sourceRieszStoppedGradient_inner_eq_cut
#check @DGRHS.Commutator.sourceRiesz_bounded_difference_time
#print axioms DGRHS.Commutator.sourceRiesz_bounded_difference_time
#check @DGRHS.Commutator.sourceRieszStopped_pair_time_integral
#print axioms DGRHS.Commutator.sourceRieszStopped_pair_time_integral
#check @DGRHS.Commutator.sourceRieszStopped_square_difference
#print axioms DGRHS.Commutator.sourceRieszStopped_square_difference

#check @DGRHS.Commutator.sourceRieszStopped_square_time_identity
#print axioms DGRHS.Commutator.sourceRieszStopped_square_time_identity

#check @DGRHS.Commutator.exists_sourceRiesz_stopped_square_covariance_replacement
#print axioms DGRHS.Commutator.exists_sourceRiesz_stopped_square_covariance_replacement
