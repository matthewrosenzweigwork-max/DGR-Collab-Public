import DGRHS.Commutator.SourceRieszCovarianceReplacement

/-! Actual finite-family covariance expressions from original physical data.
Deterministic terminal cutoffs and signed cross weights are explicit. No
stochastic bracket or Ito admissibility is asserted by this module. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszStoppedGradient (t : ℝ) (f : ℝ→E→ℝ) (r : ℝ) (z : E) : E :=
  if r∈Icc 0 t then gradient (f r) z else 0

theorem sourceRieszStoppedGradientNormSq (k : ℕ) (t θ : Fin k→ℝ)
    (f : Fin k→ℝ→E→ℝ) (r : ℝ) (z : E) :
    ‖∑ a : Fin k,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2=
      ∑ a : Fin k,∑ b : Fin k,(θ a*θ b)*
        ⟪sourceRieszStoppedGradient (t a) (f a) r z,
          sourceRieszStoppedGradient (t b) (f b) r z⟫ := by
  rw [←real_inner_self_eq_norm_sq,sum_inner]
  simp_rw [inner_sum,real_inner_smul_left,real_inner_smul_right,mul_assoc]

def sourceRieszCrossCovarianceError (β : ℝ) (ρ : ℝ→E→ℝ)
    (ta tb : ℝ) (f g : ℝ→E→ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E) (ω : Ω) : ℝ :=
  (2/β)*∫ r,sourceRieszDynamicEmpiricalDifference (ρ r)
    (fun z=>⟪gradient (f r) z,gradient (g r) z⟫) N (X r ω)
      ∂volume.restrict (Ioc 0 (min ta tb))

/-- Proper finite-sum L1 estimate, instantiated below by actual physical rates. -/
theorem sourceRiesz_weighted_finite_L1 {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (θ : Fin k→ℝ) (C : Fin k→Fin k→Ω→ℝ) (B : ℝ)
    (hi : ∀ a b,Integrable (C a b) ν)
    (hb : ∀ a b,(∫ ω,|C a b ω| ∂ν)≤B) :
    Integrable (fun ω=>∑ a : Fin k,∑ b : Fin k,(θ a*θ b)*C a b ω) ν ∧
      (∫ ω,|∑ a : Fin k,∑ b : Fin k,(θ a*θ b)*C a b ω| ∂ν)≤
        B*(∑ a : Fin k,|θ a|)^2 := by
  let F := fun a b ω=>(θ a*θ b)*C a b ω
  have hiF (a b : Fin k) : Integrable (F a b) ν := (hi a b).const_mul _
  have hiS : Integrable (fun ω=>∑ a : Fin k,∑ b : Fin k,F a b ω) ν :=
    integrable_finsetSum _ fun a _=>integrable_finsetSum _ fun b _=>hiF a b
  have hiA : Integrable (fun ω=>∑ a : Fin k,∑ b : Fin k,|F a b ω|) ν :=
    integrable_finsetSum _ fun a _=>integrable_finsetSum _ fun b _=>(hiF a b).abs
  refine ⟨hiS,?_⟩
  calc
    (∫ ω,|∑ a : Fin k,∑ b : Fin k,F a b ω| ∂ν)
      ≤ ∫ ω,∑ a : Fin k,∑ b : Fin k,|F a b ω| ∂ν := by
        apply integral_mono hiS.abs hiA
        intro ω
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _=>Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ a : Fin k,∑ b : Fin k,(∫ ω,|F a b ω| ∂ν) := by
      rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>(hiF a b).abs)]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum _ (fun b _=>(hiF a b).abs)
    _ ≤ ∑ a : Fin k,∑ b : Fin k,|θ a*θ b| *B := by
      apply Finset.sum_le_sum;intro a _
      apply Finset.sum_le_sum;intro b _
      simp_rw [F,abs_mul,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb a b) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = B*(∑ a : Fin k,|θ a|)^2 := by
      simp_rw [abs_mul]
      rw [pow_two]
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      ring

/-- Common constant before horizon, finite family, weights and all physical inputs. -/
theorem exists_sourceRiesz_finite_family_covariance_replacement
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
      let C := fun a b=>sourceRieszCrossCovarianceError β ρ (t a) (t b) (f a) (f b) N X
      (∀ a b,Integrable (C a b) ν) ∧
      Integrable (fun ω=>∑ a : Fin k,∑ b : Fin k,(θ a*θ b)*C a b ω) ν ∧
      (∫ ω,|∑ a : Fin k,∑ b : Fin k,(θ a*θ b)*C a b ω| ∂ν)≤
        T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_cross_gradient_covariance_replacement
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hfreg hf hfB X hXm A B hA hB hE
  let C := fun a b=>sourceRieszCrossCovarianceError β ρ (t a) (t b) (f a) (f b) N X
  have hpair (a b : Fin k) : Integrable (C a b) ν ∧
      (∫ ω,|C a b ω| ∂ν)≤T*D/Real.sqrt N := by
    obtain ⟨_,_,_,_,_,hi,hb⟩ := hfactory T hT (t a) (t b) (ht a) (ht b) N hN
      Ω ν ρ hρm hprob hρ (f a) (f b) (hfreg a) (hfreg b) (hf a) (hf b)
      (hfB a) (hfB b) X hXm A B hA hB hE
    refine ⟨hi,hb.trans ?_⟩
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((min_le_left (t a) (t b)).trans (ht a).2) hD)
      (Real.sqrt_nonneg _)
  obtain ⟨hi,hb⟩ := sourceRiesz_weighted_finite_L1 ν k θ C (T*D/Real.sqrt N)
    (fun a b=>(hpair a b).1) (fun a b=>(hpair a b).2)
  refine ⟨fun a b=>(hpair a b).1,hi,hb.trans_eq ?_⟩
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszStoppedGradient
#print axioms DGRHS.Commutator.sourceRieszStoppedGradient
#check @DGRHS.Commutator.sourceRieszStoppedGradientNormSq
#print axioms DGRHS.Commutator.sourceRieszStoppedGradientNormSq
#check @DGRHS.Commutator.sourceRieszCrossCovarianceError
#print axioms DGRHS.Commutator.sourceRieszCrossCovarianceError
#check @DGRHS.Commutator.sourceRiesz_weighted_finite_L1
#print axioms DGRHS.Commutator.sourceRiesz_weighted_finite_L1
#check @DGRHS.Commutator.exists_sourceRiesz_finite_family_covariance_replacement
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_family_covariance_replacement
