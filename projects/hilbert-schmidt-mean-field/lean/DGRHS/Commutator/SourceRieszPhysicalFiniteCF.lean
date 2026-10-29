import DGRHS.Commutator.SourceRieszFiniteItoVolterra

/- Original DGR dynamic finite-family source3971--3997 physical instantiation.
Bounded stopped-gradient squares, actual moving density and empirical process,
original extended physical Gr/literal initial Gibbs derive the covariance rate.
Only the literal finite source Ito formula is conditional admissibility; no
terminal duality, favorable bracket convergence or desired CF factorization is
assumed. Original generic time-Ito-admissibility review is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_physical_finite_Ito_comparison
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
      let H := fun r ω=>∫ z,S r z ∂sourceRieszLocalEmpiricalLaw N (X r ω)
      let m := fun r=>∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r)
      ∀ (A₀ : Ω→ℝ),Measurable A₀ → ∀ (M₀ : ℝ→Ω→ℝ),
      Measurable (Function.uncurry M₀) →
      let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+M₀ r ω)
      let chi := fun r=>∫ ω,Φ r ω ∂ν
      (∀ r∈Icc 0 T,chi r=chi 0-(1/β:ℝ) •
        (∫ u in 0..r,∫ ω,Φ u ω*(H u ω:ℂ) ∂ν)) →
      ‖chi T-chi 0*(Real.exp (-(1/β)*(∫ r in 0..T,m r)):ℂ)‖≤
        Real.exp ((((Gmax:ℝ)*(∑ a : Fin k,|θ a|))^2/β)*T)*
          (T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_stopped_square_product_replacement
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  dsimp only
  intro A₀ hA₀ M₀ hM₀ hIto
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  let H := fun r ω=>∫ z,S r z ∂sourceRieszLocalEmpiricalLaw N (X r ω)
  let m := fun r=>∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r)
  let C := ((Gmax:ℝ)*(∑ a : Fin k,|θ a|))^2
  have hC : 0≤C := sq_nonneg _
  have hSm : Measurable (fun p : ℝ×E=>S p.1 p.2) :=
    measurable_sourceRieszStopped_square k t θ f hf
  have hSb (r : ℝ) (z : E) : S r z∈Icc 0 C :=
    ⟨sq_nonneg _,sourceRieszStopped_square_bound k t θ f Gmax hfB r z⟩
  have hHm : Measurable (Function.uncurry H) := by
    have heq : Function.uncurry H=(fun p : ℝ×Ω=>(N:ℝ)⁻¹*∑ i : Fin N,S p.1 (X p.1 p.2 i)) :=
      funext fun p=>integral_sourceRieszLocalEmpiricalLaw N (X p.1 p.2) _
    rw [heq]
    exact (Finset.measurable_sum _ fun i _=>hSm.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hXm))).const_mul _
  have hHb (r : ℝ) (hr : r∈Icc 0 T) (ω : Ω) : |H r ω|≤C := by
    letI := sourceRieszLocalEmpiricalLaw_probability N (by omega : 0<N) (X r ω)
    have hh : ∀ᵐ z ∂sourceRieszLocalEmpiricalLaw N (X r ω),‖S r z‖≤C :=
      Filter.Eventually.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (hSb r z).1]
        exact (hSb r z).2
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=sourceRieszLocalEmpiricalLaw N (X r ω)) hh
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρm r
  have hmm : Measurable m := by
    simpa only [hκ] using (hSm.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  have hmb (r : ℝ) (hr : r∈Icc 0 T) : 0≤m r ∧ m r≤C := by
    letI := hprob r hr
    refine ⟨integral_nonneg fun z=>(hSb r z).1,?_⟩
    apply (le_abs_self _).trans
    have hh : ∀ᵐ z ∂gaussianRieszDensityMeasure (ρ r),‖S r z‖≤C :=
      Filter.Eventually.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (hSb r z).1]
        exact (hSb r z).2
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=gaussianRieszDensityMeasure (ρ r)) hh
  have hh := sourceRiesz_finite_Ito_volterra ν T β C hT hβ hC
    A₀ hA₀ M₀ H hM₀ hHm hHb m hmm hmb hIto
  obtain ⟨_,_,_,_,hb⟩ := hfactory T hT k t θ ht N hN Ω ν ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hb

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_physical_finite_Ito_comparison
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_finite_Ito_comparison
