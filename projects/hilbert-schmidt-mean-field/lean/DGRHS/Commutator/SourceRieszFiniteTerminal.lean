import DGRHS.Commutator.SourceRieszAdjointTimeIdentity
import DGRHS.Commutator.SourceRieszTerminalPhase

/-! Source3933--3946: actual finite-family adjoint terminal algebra and
proper signed remainder. One common constant is chosen before all horizons,
tests, particle counts and processes. The terminal representation is derived
from the primitive particle and mean-field formulas, never supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal RealInnerProductSpace BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_sourceRiesz_empirical_fluctuation (ρ q : E→ℝ)
    (hq : Measurable q) (N : ℕ) :
    Measurable (fun x : Fin N→E=>Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ q N x) := by
  unfold sourceRieszDynamicEmpiricalDifference
  simp_rw [integral_sourceRieszLocalEmpiricalLaw]
  exact (((Finset.measurable_sum _ fun i _=>hq.comp (measurable_pi_apply i)).const_mul _).sub
    measurable_const).const_mul _

lemma sourceRiesz_finite_remainder_L1 {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (θ : Fin k→ℝ) (R : Fin k→Ω→ℝ) (B : ℝ)
    (hi : ∀ a,Integrable (R a) ν) (hb : ∀ a,(∫ ω,|R a ω| ∂ν)≤B) :
    Integrable (fun ω=>∑ a,θ a*R a ω) ν ∧
      (∫ ω,|∑ a,θ a*R a ω| ∂ν)≤B*(∑ a,|θ a|) := by
  have hiF (a : Fin k) : Integrable (fun ω=>θ a*R a ω) ν := (hi a).const_mul _
  have hiS := integrable_finsetSum Finset.univ (fun a _=>hiF a)
  have hiA := integrable_finsetSum Finset.univ (fun a _=>(hiF a).abs)
  refine ⟨hiS,?_⟩
  calc
    _ ≤ ∫ ω,∑ a,|θ a*R a ω| ∂ν :=
      integral_mono hiS.abs hiA (fun ω=>Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ a,∫ ω,|θ a*R a ω| ∂ν := integral_finsetSum _ (fun a _=>(hiF a).abs)
    _ ≤ ∑ a,|θ a| * B := by
      apply Finset.sum_le_sum
      intro a _
      simp_rw [abs_mul,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb a) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;ring

theorem exists_sourceRiesz_finite_terminal_representation
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (f : Fin k→ℝ→E→ℝ),(∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ)) →
      (∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) →
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
      ∀ (m : Fin k→Ω→ℝ),
      (∀ a,∀ᵐ ω ∂ν,(∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
        (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 (t a),sourceRieszEmpiricalTestDrift s β (f a) N r (X r ω))+m a ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceRieszMeanTestDrift s β (ρ r) (f a) r) →
      let R := fun ω=>∑ a,θ a*(-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
        sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f a r)) N (X r ω))))
      let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
      let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
      Measurable A₀ ∧ Measurable Z ∧ Measurable R ∧ Integrable R ν ∧
      (∫ ω,|R ω| ∂ν)≤T*D*(∑ a,|θ a|)/(2*Real.sqrt N) ∧
      Z=ᵐ[ν](fun ω=>A₀ ω+(∑ a,θ a*(Real.sqrt N*m a ω))+R ω) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_physical_adjoint_time_identity
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ f hf hK hgrad L hL hback
    X hXm G B hG hB hE m hIto hweak
  let R := fun a ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
    sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f a r)) N (X r ω)))
  have hsub (a : Fin k) {r : ℝ} (hr : r∈Icc 0 (t a)) : r∈Icc 0 T := ⟨hr.1,hr.2.trans (ht a).2⟩
  have hsingle (a : Fin k) := hfactory (t a) (ht a).1 N hN Ω ν ρ hρm
    (fun r hr=>hprob r (hsub a hr)) (fun r hr=>hρ r (hsub a hr))
    (f a) (hf a) (hK a) (hgrad a) L (hL a) (hback a) X hXm
    G B (fun r hr=>hG r (hsub a hr)) (fun r hr=>hB r (hsub a hr))
    (fun r hr=>hE r (hsub a hr)) (m a) (hIto a) (hweak a)
  have hRi (a : Fin k) : Integrable (R a) ν := (hsingle a).2.2.2.2.1
  have hRb (a : Fin k) : (∫ ω,|R a ω| ∂ν)≤T*D/(2*Real.sqrt N) :=
    (hsingle a).2.2.2.2.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ht a).2 hD) (by positivity))
  obtain ⟨hi,hb⟩ := sourceRiesz_finite_remainder_L1 ν k θ R (T*D/(2*Real.sqrt N)) hRi hRb
  have hXm' (r : ℝ) : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
  refine ⟨?_,?_,?_,hi,by convert hb using 1 <;> ring,?_⟩
  · exact Finset.measurable_sum _ fun a _=>
      ((measurable_sourceRiesz_empirical_fluctuation (ρ 0) (f a 0)
        (hf a 0 ⟨le_rfl,(ht a).1⟩).continuous.measurable N).comp (hXm' 0)).const_mul _
  · exact Finset.measurable_sum _ fun a _=>
      ((measurable_sourceRiesz_empirical_fluctuation (ρ (t a)) (f a (t a))
        (hf a (t a) ⟨(ht a).1,le_rfl⟩).continuous.measurable N).comp (hXm' (t a))).const_mul _
  · exact Finset.measurable_sum _ fun a _=>((hsingle a).2.2.2.1).const_mul _
  · filter_upwards [ae_all_iff.mpr (fun a=>(hsingle a).2.2.1)] with ω hω
    calc
      _ = ∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω)+
          Real.sqrt N*m a ω+R a ω) := Finset.sum_congr rfl fun a _=>congrArg (fun z=>θ a*z) (hω a).2.2
      _ = _ := by simp_rw [mul_add,Finset.sum_add_distrib];rfl

end DGRHS.Commutator
#check @DGRHS.Commutator.measurable_sourceRiesz_empirical_fluctuation
#print axioms DGRHS.Commutator.measurable_sourceRiesz_empirical_fluctuation
#check @DGRHS.Commutator.sourceRiesz_finite_remainder_L1
#print axioms DGRHS.Commutator.sourceRiesz_finite_remainder_L1
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_finite_terminal_representation
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_terminal_representation
