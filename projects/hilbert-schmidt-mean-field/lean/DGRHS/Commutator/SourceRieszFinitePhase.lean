import DGRHS.Commutator.SourceRieszStoppedSquareBounds
import Mathlib.Analysis.Complex.Trigonometric

/-! Finite unit-phase covariance correction, derived from actual physical
product-L1 error. No finite Ito identity, terminal duality or CF limit is a
hypothesis or conclusion. The stochastic source-admissibility gate is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszFinitePhase (x : ℝ) : ℂ := Complex.exp (Complex.I*(x:ℂ))

lemma norm_sourceRieszFinitePhase (x : ℝ) : ‖sourceRieszFinitePhase x‖=1 :=
  Complex.norm_exp_I_mul_ofReal x

lemma measurable_sourceRieszFinitePhase : Measurable sourceRieszFinitePhase :=
  Complex.continuous_exp.measurable.comp (measurable_const.mul Complex.continuous_ofReal.measurable)

/-- Properness and unit phase bound before taking the finite time correction. -/
theorem sourceRiesz_phase_product_correction {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (η : Measure ℝ) [SFinite η]
    (A : Ω→ℝ) (hA : Measurable A) (M J : ℝ→Ω→ℝ)
    (hM : Measurable (Function.uncurry M)) (hJ : Measurable (Function.uncurry J))
    (hiJ : Integrable (Function.uncurry J) (η.prod ν)) :
    let F := fun r ω=>sourceRieszFinitePhase (A ω+M r ω)*(J r ω:ℂ)
    Integrable (Function.uncurry F) (η.prod ν) ∧
    Integrable (fun r=>∫ ω,F r ω ∂ν) η ∧
    ‖(1/2:ℝ) • (∫ r,∫ ω,F r ω ∂ν ∂η)‖≤
      (1/2)*(∫ r,∫ ω,|J r ω| ∂ν ∂η) := by
  let F := fun r ω=>sourceRieszFinitePhase (A ω+M r ω)*(J r ω:ℂ)
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_sourceRieszFinitePhase.comp ((hA.comp measurable_snd).add hM)).mul
      (Complex.continuous_ofReal.measurable.comp hJ)
  have hnorm (r : ℝ) (ω : Ω) : ‖F r ω‖=|J r ω| := by
    simp only [F,norm_mul,norm_sourceRieszFinitePhase,one_mul,Complex.norm_real,Real.norm_eq_abs]
  have hiF : Integrable (Function.uncurry F) (η.prod ν) := by
    apply hiJ.abs.mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p=>by
      change ‖F p.1 p.2‖≤|J p.1 p.2|
      rw [hnorm]
  refine ⟨hiF,hiF.integral_prod_left,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
  calc
    ‖∫ r,∫ ω,F r ω ∂ν ∂η‖≤∫ r,‖∫ ω,F r ω ∂ν‖ ∂η := norm_integral_le_integral_norm _
    _ ≤ ∫ r,∫ ω,|J r ω| ∂ν ∂η := by
      apply integral_mono hiF.integral_prod_left.norm hiJ.abs.integral_prod_left
      intro r
      change ‖∫ ω,F r ω ∂ν‖≤∫ ω,|J r ω| ∂ν
      simpa only [hnorm] using (norm_integral_le_integral_norm (fun ω=>F r ω))


/-- Genuine physical correction rate for the original finite Ito comparison. -/
theorem exists_sourceRiesz_finite_phase_covariance_correction
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
      Integrable (fun r=>∫ ω,F r ω ∂ν) (volume.restrict (Ioc 0 T)) ∧
      ‖(1/2:ℝ) • (∫ r in Ioc 0 T,∫ ω,F r ω ∂ν)‖≤
        T*D*(∑ a : Fin k,|θ a|)^2/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_stopped_square_product_replacement
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  dsimp only
  intro A₀ hA₀ M₀ hM₀
  obtain ⟨hJm,_,hiJ,_,hb⟩ := hfactory T hT k t θ ht N hN Ω ν ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  obtain ⟨hiF,hiI,hbound⟩ := sourceRiesz_phase_product_correction ν
    (volume.restrict (Ioc 0 T)) A₀ hA₀ M₀ _ hM₀ hJm hiJ
  refine ⟨hiF,hiI,hbound.trans ?_⟩
  calc
    (1/2)*(∫ r in Ioc 0 T,∫ ω,|_| ∂ν)≤(1/2)*(T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszFinitePhase
#print axioms DGRHS.Commutator.sourceRieszFinitePhase
#check @DGRHS.Commutator.norm_sourceRieszFinitePhase
#print axioms DGRHS.Commutator.norm_sourceRieszFinitePhase
#check @DGRHS.Commutator.measurable_sourceRieszFinitePhase
#print axioms DGRHS.Commutator.measurable_sourceRieszFinitePhase
#check @DGRHS.Commutator.sourceRiesz_phase_product_correction
#print axioms DGRHS.Commutator.sourceRiesz_phase_product_correction
#check @DGRHS.Commutator.exists_sourceRiesz_finite_phase_covariance_correction
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_phase_covariance_correction
