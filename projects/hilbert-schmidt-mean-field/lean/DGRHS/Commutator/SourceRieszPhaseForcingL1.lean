import DGRHS.Commutator.SourceRieszFinitePhase

/- DGR source3959/3971--3986: actual proper L1-in-time phase forcing.
This strengthens norm-after-time-integration to integrated forcing norm,
using the SAME constructed physical rescaled covariance J. No Ito identity
or desired bracket/CF conclusion is a premise or conclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRiesz_phase_forcing_L1 {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (η : Measure ℝ) [SFinite η]
    (A : Ω→ℝ) (hA : Measurable A) (M J : ℝ→Ω→ℝ)
    (hM : Measurable (Function.uncurry M)) (hJ : Measurable (Function.uncurry J))
    (hiJ : Integrable (Function.uncurry J) (η.prod ν)) :
    let F := fun r ω=>sourceRieszFinitePhase (A ω+M r ω)*(J r ω:ℂ)
    Integrable (Function.uncurry F) (η.prod ν) ∧
    Integrable (fun r=>(1/2:ℝ) • (∫ ω,F r ω ∂ν)) η ∧
    (∫ r,‖(1/2:ℝ) • (∫ ω,F r ω ∂ν)‖ ∂η)≤
      (1/2)*(∫ r,∫ ω,|J r ω| ∂ν ∂η) := by
  let F := fun r ω=>sourceRieszFinitePhase (A ω+M r ω)*(J r ω:ℂ)
  obtain ⟨hiF,hiG,_⟩ := sourceRiesz_phase_product_correction ν η A hA M J hM hJ hiJ
  refine ⟨hiF,hiG.smul (1/2:ℝ),?_⟩
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
  apply integral_mono hiG.norm hiJ.abs.integral_prod_left
  intro r
  change ‖∫ ω,F r ω ∂ν‖≤∫ ω,|J r ω| ∂ν
  have heq (ω : Ω) : ‖F r ω‖=|J r ω| := by
    simp only [F,norm_mul,norm_sourceRieszFinitePhase,one_mul,Complex.norm_real,Real.norm_eq_abs]
  simpa only [heq] using norm_integral_le_integral_norm (fun ω=>F r ω)

theorem exists_sourceRiesz_finite_phase_forcing_L1
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
      let J := fun r ω=>(2/β)*sourceRieszDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)
      ∀ (A₀ : Ω→ℝ),Measurable A₀ → ∀ (M₀ : ℝ→Ω→ℝ),
      Measurable (Function.uncurry M₀) →
      let F := fun r ω=>sourceRieszFinitePhase (A₀ ω+M₀ r ω)*(J r ω:ℂ)
      Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      Integrable (fun r=>(1/2:ℝ) • (∫ ω,F r ω ∂ν)) (volume.restrict (Ioc 0 T)) ∧
      (∫ r in Ioc 0 T,‖(1/2:ℝ) • (∫ ω,F r ω ∂ν)‖)≤
        T*D*(∑ a : Fin k,|θ a|)^2/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_stopped_square_product_replacement
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  dsimp only
  intro A₀ hA₀ M₀ hM₀
  obtain ⟨hJm,_,hiJ,_,hb⟩ := hfactory T hT k t θ ht N hN Ω ν ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  obtain ⟨hiF,hiG,hbound⟩ := sourceRiesz_phase_forcing_L1 ν
    (volume.restrict (Ioc 0 T)) A₀ hA₀ M₀ _ hM₀ hJm hiJ
  refine ⟨hiF,hiG,hbound.trans ?_⟩
  calc
    (1/2)*(∫ r in Ioc 0 T,∫ ω,|_| ∂ν)≤(1/2)*(T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_phase_forcing_L1
#print axioms DGRHS.Commutator.sourceRiesz_phase_forcing_L1
#check @DGRHS.Commutator.exists_sourceRiesz_finite_phase_forcing_L1
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_phase_forcing_L1
