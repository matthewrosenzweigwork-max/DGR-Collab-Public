import DGRHS.Commutator.SourceRieszStoppedProductCovariance

/-! Actual bounded nonnegative covariance expressions for finite characteristic
function comparison. These are empirical/background time integrals, with no
predictable-bracket realization or stochastic admissibility premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszStopped_square_bound (k : ℕ) (t θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (r : ℝ) (z : E) :
    ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2≤
      ((G:ℝ)*(∑ a,|θ a|))^2 := by
  have hnorm : ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖≤
      (G:ℝ)*(∑ a,|θ a|) := by
    calc
      _ ≤ ∑ a,‖θ a • sourceRieszStoppedGradient (t a) (f a) r z‖ := norm_sum_le _ _
      _ ≤ ∑ a,|θ a| *(G:ℝ) := by
        apply Finset.sum_le_sum;intro a _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_sourceRieszStoppedGradient_le (t a) (f a) G (hb a) r z) (abs_nonneg _)
      _ = _ := by rw [←Finset.sum_mul,mul_comm]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

lemma measurable_sourceRieszStopped_square (k : ℕ) (t θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) :
    Measurable (fun p : ℝ×E=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) p.1 p.2‖^2) := by
  have heq : (fun p : ℝ×E=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) p.1 p.2‖^2)=
      (fun p=>∑ a,∑ b,(θ a*θ b)*⟪sourceRieszStoppedGradient (t a) (f a) p.1 p.2,
        sourceRieszStoppedGradient (t b) (f b) p.1 p.2⟫) :=
    funext fun p=>sourceRieszStoppedGradientNormSq k t θ f p.1 p.2
  rw [heq]
  exact Finset.measurable_sum _ fun a _=>Finset.measurable_sum _ fun b _=>
    ((measurable_sourceRieszStoppedGradient (t a) (f a) (hf a)).inner
      (measurable_sourceRieszStoppedGradient (t b) (f b) (hf b))).const_mul _

/-- Proper positive bounded means on the physical horizon, not outside it. -/
theorem sourceRiesz_nonnegative_bounded_covariance_components
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T β : ℝ) (hT : 0≤T) (hβ : 0<β)
    (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (Q : ℝ×E→ℝ) (hQ : Measurable Q) (C : ℝ)
    (hb : ∀ r∈Icc 0 T,∀ z,Q (r,z)∈Icc 0 C)
    (N : ℕ) (hN : 0<N) (X : ℝ→Ω→Fin N→E) (hX : Measurable (Function.uncurry X)) :
    let η := volume.restrict (Ioc 0 T)
    let H := fun r ω=>∫ z,Q (r,z) ∂sourceRieszLocalEmpiricalLaw N (X r ω)
    let m := fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)
    let V := fun ω=>(2/β)*∫ r,H r ω ∂η
    let b := (2/β)*∫ r,m r ∂η
    Integrable m η ∧ Integrable (Function.uncurry H) (η.prod ν) ∧
    (∀ ω,Integrable (fun r=>H r ω) η) ∧ Integrable V ν ∧
    b∈Icc 0 ((2/β)*T*C) ∧ (∀ ω,V ω∈Icc 0 ((2/β)*T*C)) ∧
    (∀ ω,V ω-b=(2/β)*∫ r,sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>Q (r,z)) N (X r ω) ∂η) := by
  let η := volume.restrict (Ioc 0 T)
  let H := fun r ω=>∫ z,Q (r,z) ∂sourceRieszLocalEmpiricalLaw N (X r ω)
  let m := fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)
  have hC : 0≤C := (hb 0 ⟨le_rfl,hT⟩ 0).1.trans (hb 0 ⟨le_rfl,hT⟩ 0).2
  have hHb (r : ℝ) (hr : r∈Icc 0 T) (ω : Ω) : H r ω∈Icc 0 C := by
    letI := sourceRieszLocalEmpiricalLaw_probability N hN (X r ω)
    refine ⟨integral_nonneg fun z=>(hb r hr z).1,?_⟩
    apply (le_abs_self _).trans
    have hh : ∀ᵐ z ∂sourceRieszLocalEmpiricalLaw N (X r ω),‖Q (r,z)‖≤C :=
      Filter.Eventually.of_forall fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (hb r hr z).1];exact (hb r hr z).2
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const hh
  have hmb (r : ℝ) (hr : r∈Icc 0 T) : m r∈Icc 0 C := by
    letI := hp r hr
    refine ⟨integral_nonneg fun z=>(hb r hr z).1,?_⟩
    apply (le_abs_self _).trans
    have hh : ∀ᵐ z ∂gaussianRieszDensityMeasure (ρ r),‖Q (r,z)‖≤C :=
      Filter.Eventually.of_forall fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (hb r hr z).1];exact (hb r hr z).2
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const hh
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρ r
  have hmm : Measurable m := by
    simpa only [hκ] using (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  have hHm : Measurable (Function.uncurry H) := by
    have heq : Function.uncurry H=(fun p : ℝ×Ω=>(N:ℝ)⁻¹*∑ i : Fin N,Q (p.1,X p.1 p.2 i)) :=
      funext fun p=>integral_sourceRieszLocalEmpiricalLaw N (X p.1 p.2) _
    rw [heq]
    exact (Finset.measurable_sum _ fun i _=>hQ.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX))).const_mul _
  have hm : Integrable m η := by
    apply (integrable_const C).mono' hmm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (hmb r ⟨hr.1.le,hr.2⟩).1]
    exact (hmb r ⟨hr.1.le,hr.2⟩).2
  have htime : ∀ᵐ p : ℝ×Ω ∂η.prod ν,p.1∈Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall fun _=>hr
  have hiH : Integrable (Function.uncurry H) (η.prod ν) := by
    apply (integrable_const C).mono' hHm.aestronglyMeasurable
    filter_upwards [htime] with p hp
    change |H p.1 p.2|≤C
    rw [abs_of_nonneg (hHb p.1 ⟨hp.1.le,hp.2⟩ p.2).1]
    exact (hHb p.1 ⟨hp.1.le,hp.2⟩ p.2).2
  have his (ω : Ω) : Integrable (fun r=>H r ω) η := by
    apply (integrable_const C).mono' (hHm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change |H r ω|≤C
    rw [abs_of_nonneg (hHb r ⟨hr.1.le,hr.2⟩ ω).1]
    exact (hHb r ⟨hr.1.le,hr.2⟩ ω).2
  have hbint : ∀ (F : ℝ→ℝ),Integrable F η → (∀ r∈Icc 0 T,F r∈Icc 0 C) →
      (2/β)*(∫ r,F r ∂η)∈Icc 0 ((2/β)*T*C) := by
    intro F hi hF
    have hlo : 0≤∫ r,F r ∂η := integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr;exact (hF r ⟨hr.1.le,hr.2⟩).1)
    have hup : (∫ r,F r ∂η)≤T*C := by
      calc
        _ ≤ ∫ _ : ℝ,C ∂η := integral_mono_ae hi (integrable_const _) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr;exact (hF r ⟨hr.1.le,hr.2⟩).2)
        _ = _ := by rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,
          Real.volume_real_Ioc_of_le hT,sub_zero]
    refine ⟨mul_nonneg (by positivity) hlo,?_⟩
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hup (by positivity : 0≤(2:ℝ)/β))
  refine ⟨hm,hiH,his,hiH.integral_prod_right.const_mul _,hbint m hm hmb,
    fun ω=>hbint _ (his ω) (fun r hr=>hHb r hr ω),?_⟩
  intro ω
  change (2/β)*(∫ r,H r ω ∂η)-(2/β)*(∫ r,m r ∂η)=
    (2/β)*(∫ r,H r ω-m r ∂η)
  rw [integral_sub (his ω) hm]
  ring

/-- Native stopped gradients derive all actual covariance caps and properness. -/
theorem sourceRieszStopped_covariance_components
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T β : ℝ) (hT : 0≤T) (hβ : 0<β)
    (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (k : ℕ) (t θ : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hg : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (N : ℕ) (hN : 0<N) (X : ℝ→Ω→Fin N→E) (hX : Measurable (Function.uncurry X)) :
    let Q := fun p : ℝ×E=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) p.1 p.2‖^2
    let C := ((G:ℝ)*(∑ a,|θ a|))^2
    let η := volume.restrict (Ioc 0 T)
    let H := fun r ω=>∫ z,Q (r,z) ∂sourceRieszLocalEmpiricalLaw N (X r ω)
    let m := fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)
    let V := fun ω=>(2/β)*∫ r,H r ω ∂η
    let b := (2/β)*∫ r,m r ∂η
    Integrable m η ∧ Integrable (Function.uncurry H) (η.prod ν) ∧
    (∀ ω,Integrable (fun r=>H r ω) η) ∧ Integrable V ν ∧
    b∈Icc 0 ((2/β)*T*C) ∧ (∀ ω,V ω∈Icc 0 ((2/β)*T*C)) ∧
    (∀ ω,V ω-b=(2/β)*∫ r,sourceRieszDynamicEmpiricalDifference (ρ r)
      (fun z=>Q (r,z)) N (X r ω) ∂η) := by
  exact sourceRiesz_nonnegative_bounded_covariance_components ν T β hT hβ ρ hρ hp
    _ (measurable_sourceRieszStopped_square k t θ f hf) _
    (fun r _ z=>⟨sq_nonneg _,sourceRieszStopped_square_bound k t θ f G hg r z⟩) N hN X hX

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszStopped_square_bound
#print axioms DGRHS.Commutator.sourceRieszStopped_square_bound
#check @DGRHS.Commutator.measurable_sourceRieszStopped_square
#print axioms DGRHS.Commutator.measurable_sourceRieszStopped_square
#check @DGRHS.Commutator.sourceRiesz_nonnegative_bounded_covariance_components
#print axioms DGRHS.Commutator.sourceRiesz_nonnegative_bounded_covariance_components

#check @DGRHS.Commutator.sourceRieszStopped_covariance_components
#print axioms DGRHS.Commutator.sourceRieszStopped_covariance_components
