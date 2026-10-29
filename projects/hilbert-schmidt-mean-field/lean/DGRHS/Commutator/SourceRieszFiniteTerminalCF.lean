import DGRHS.Commutator.SourceRieszFiniteTerminal
import DGRHS.Commutator.SourceRieszPhysicalFiniteCF

/-! Source3933--4015 finite-N terminal characteristic comparison. The same
weighted stopped raw noise process appears in primitive particle Ito and in
the primitive finite phase Ito formula. Its zero initial value identifies
chi(0) with the actual initial fluctuation. No independence between the
initial fluctuation and terminal noise, factorization or CF limit is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal RealInnerProductSpace BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_finite_terminal_CF_comparison
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K Gmax : ℝ≥0) :
    ∃ Dc Dl : ℝ,0≤Dc ∧ 0≤Dl ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (f : Fin k→ℝ→E→ℝ),(∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ)) →
      (∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
      ∀ (L : ℝ),(∀ a,∀ r∈Icc 0 (t a),∀ z,|f a r z|≤L) →
      (∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),∀ z,
        deriv (fun u=>f a u z) r+β⁻¹*laplacian (f a r) z=
          ∫ y,⟪sourceRieszForce s (z-y),gradient (f a r) z-gradient (f a r) y⟫
            ∂gaussianRieszDensityMeasure (ρ r)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ r∈Icc 0 T,sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : Fin k→ℝ→Ω→ℝ),(∀ a,Measurable (Function.uncurry (m a))) →
      (∀ a,∀ ω,m a 0 ω=0) →
      (∀ a,∀ᵐ ω ∂ν,(∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
        (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 (t a),sourceRieszEmpiricalTestDrift s β (f a) N r (X r ω))+m a (t a) ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceRieszMeanTestDrift s β (ρ r) (f a) r) →
      let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
      let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
      let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a)) ω)
      let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+W r ω)
      let chi := fun r=>∫ ω,Φ r ω ∂ν
      (∀ r∈Icc 0 T,chi r=chi 0-(1/β:ℝ) •
        (∫ u in 0..r,∫ ω,Φ u ω*((∫ z,S u z ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ):ℂ) ∂ν)) →
      ‖(∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω) ∂ν)*
          (Real.exp (-(1/β)*(∫ r in 0..T,∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r))):ℂ)‖≤
        T*Dc*(∑ a,|θ a|)/(2*Real.sqrt N)+
          Real.exp ((((Gmax:ℝ)*(∑ a,|θ a|))^2/β)*T)*
            (T*Dl*(∑ a,|θ a|)^2/Real.sqrt N) := by
  obtain ⟨Dc,hDc,hterminal⟩ := exists_sourceRiesz_finite_terminal_representation
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K
  obtain ⟨Dl,hDl,hcf⟩ := exists_sourceRiesz_physical_finite_Ito_comparison
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax Gmax
  refine ⟨Dc,Dl,hDc,hDl,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hf hK hgrad hfB L hL hback
    X hXm G B hG hB hE m hmm hm0 hIto hweak
  dsimp only
  intro hphase
  let R := fun ω=>∑ a,θ a*(-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
    sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f a r)) N (X r ω))))
  let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
  let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
  let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a)) ω)
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  obtain ⟨hA₀,hZ,hRm,hRi,hRb,hrep⟩ := hterminal T hT k t θ ht N hN Ω ν
    ρ hρm hprob hρ f hf hK hgrad L hL hback X hXm G B hG hB hE
    (fun a=>m a (t a)) hIto hweak
  have hWm : Measurable (Function.uncurry W) := by
    apply Finset.measurable_sum
    intro a _
    exact (((hmm a).comp ((measurable_fst.min measurable_const).prodMk measurable_snd)).const_mul _).const_mul _
  have hWT (ω : Ω) : W T ω=∑ a,θ a*(Real.sqrt N*m a (t a) ω) := by
    dsimp only [W]
    apply Finset.sum_congr rfl
    intro a _
    rw [min_eq_right (ht a).2]
  have hW0 (ω : Ω) : W 0 ω=0 := by
    dsimp only [W]
    have hh (a : Fin k) : min 0 (t a)=0 := min_eq_left (ht a).1
    simp only [hh,hm0,mul_zero,Finset.sum_const_zero]
  have hcomp := hcf T hT k t θ ht N hN Ω ν ρ hρm hprob hρ f hf hgrad hfB
    X hXm G B hG hB hE A₀ hA₀ W hWm hphase
  simp only [hW0,add_zero] at hcomp
  have hY : Measurable (fun ω=>A₀ ω+W T ω) :=
    hA₀.add (hWm.comp (measurable_const.prodMk measurable_id))
  obtain ⟨_,_,hpert⟩ := sourceRiesz_terminal_phase_expectation ν (fun ω=>A₀ ω+W T ω) R hY hRm hRi
  have he : (∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)=
      ∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω+R ω) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hrep] with ω hω
    exact congrArg sourceRieszFinitePhase (hω.trans (by rw [hWT]))
  calc
    _ ≤ ‖(∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω) ∂ν)‖+
      ‖(∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω) ∂ν)*
          (Real.exp (-(1/β)*(∫ r in 0..T,∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r))):ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (by rw [he];exact hpert.trans hRb) hcomp

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_finite_terminal_CF_comparison
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_terminal_CF_comparison
