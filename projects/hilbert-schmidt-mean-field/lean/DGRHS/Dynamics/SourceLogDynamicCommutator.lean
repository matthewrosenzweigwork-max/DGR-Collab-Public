/- Source dynamicEntropyTransfers(ii), physical logarithmic branch.
A common coefficient is chosen before all densities, velocities, N and laws.
Actual family Gibbs moments plus finite bounded Gibbs entropy control the
expectation of ABSOLUTE commutator at the original1/N scale. -/
import DGRHS.Entropy.AbsoluteExponentialTransfer
import DGRHS.Commutator.SourceLogFamilyGibbsMoments
import DGRHS.Commutator.SourceLogTransportAllLaws
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_dynamic_commutator_absolute_bound
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (hK : 0<(K:ℝ)) (M : ℝ) (hM : 0≤M) (J H : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ (v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι), LipschitzWith K v →
      ∀ (ρ : EuclideanSpace ℝ ι→ℝ),∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
      -J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun x y=>logPhysicalPair (x,y)) →
      ∀ (N : ℕ),1≤N → ∀ (ν : Measure (Fin N→EuclideanSpace ℝ ι)),∀ [IsProbabilityMeasure ν],
      klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ →
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤H →
      Integrable (sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel 1 v) N) ν ∧
        (∫ x,|sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel 1 v) N x| ∂ν)≤D/(N:ℝ) := by
  obtain ⟨Csr,hC,hfactory⟩ := exists_log_transport_family_gibbs_moments (ι:=ι) 1 (by omega)
  obtain ⟨βloc,hloc,hβfactory⟩ := hfactory K hK M hM hd
  obtain ⟨Cub,Cpf,hCub,hCpf,hε,hCem,hforcing,hmom⟩ := hβfactory β hβ J
  let ε := sourceLogTransportEpsilon (β:ℝ) βloc Csr ((K:ℝ)^1)
  let Cem := sourceLogTransportCem (β:ℝ) βloc (-J) DGRHS.Concentration.glzUniversalTailConstant Cub
  let D := max (ε⁻¹*(H+Real.log (2*Cem))) 0
  refine ⟨D,le_max_right _ _,?_⟩
  intro v hv ρ hμ hρ hpair hI N hN ν hν hKL hH
  let Q := sourceLogSingularGibbs β ρ N
  letI := sourceLogSingularGibbs_probability β hd ρ M hM hρ hpair N
  let a := sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel 1 v) N
  obtain ⟨ha,A,hA,hproper⟩ := sourceLogTransport_all_law_proper 1 (by omega) hv (gaussianRieszDensityMeasure ρ) N (by omega)
  have hp := (hmom v hv ρ hρ hpair hI).2 1 (by norm_num) N hN
  have hm := (hmom v hv ρ hρ hpair hI).2 (-1) (by norm_num) N hN
  have hp' : Integrable (fun x=>Real.exp (ε*((N:ℝ)*a x))) Q := by simpa only [one_mul] using hp.1
  have hm' : Integrable (fun x=>Real.exp (-(ε*((N:ℝ)*a x)))) Q := by simpa only [neg_one_mul,neg_mul,one_mul] using hm.1
  have hbP : (∫ x,Real.exp (ε*((N:ℝ)*a x)) ∂Q)≤Cem := by simpa only [one_mul] using hp.2
  have hbM : (∫ x,Real.exp (-(ε*((N:ℝ)*a x))) ∂Q)≤Cem := by simpa only [neg_one_mul,neg_mul,one_mul] using hm.2
  obtain ⟨hi,hb⟩ := entropy_absolute_expectation_scaled_of_two_exponential_bounds Q ν
    (fun x=>(N:ℝ)*a x) ha ε hε hp' hm' hKL Cem hbP hbM
  have hn : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hai : Integrable a ν := by
    have h := hi.const_mul (N:ℝ)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using h
  have he : (fun x=>|(N:ℝ)*a x|)=(fun x=>(N:ℝ)*|a x|) := by
    funext x
    rw [abs_mul,abs_of_pos hn]
  rw [he,integral_const_mul] at hb
  have hc := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hε.le)
  have hfinal : (N:ℝ)*(∫ x,|a x| ∂ν)≤D :=
    (hb.trans (by linarith)).trans (le_max_left _ _)
  exact ⟨hai,(le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hfinal)⟩
end DGRHS.Dynamics
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_commutator_absolute_bound
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_commutator_absolute_bound
