/- Appendix common scalar controls give genuinely constant, hence measurable
and proper, time coefficients. This is an explicitly bounded-family special
case of the original conditional dynamical theorem, not a silent replacement
of its general time-dependent hypotheses. -/
import DGRHS.Dynamics.SourceLogPhysicalTime
import DGRHS.Commutator.SourceLogFamilyEntropicCommutator
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_uniform_physical_diffusive_bound
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) (M : ℝ) (hM : 0 ≤ M) (J : ℝ) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
        (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
        (f : ℝ → Measure (Fin N → EuclideanSpace ℝ ι)) (E : ℝ → ℝ),
      (∀ t, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) →
      (∀ t, IsProbabilityMeasure (f t)) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        sourceLogTimeAdmissible (ρ t) (v t) K M ∧
        -J ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ t))
          (fun x y => logPhysicalPair (x,y))) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        sourceLogCollisionFreeEnergy β (ρ t) M N (f t)=(E t : EReal)) →
      AbsolutelyContinuousOnInterval E 0 T →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T → deriv E t ≤
        |∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
          (sourceLogTransportKernel 1 (v t)) N x ∂f t|/N) →
      E T ≤ sourceA (fun _ => a) T*E 0+sourceB (fun _ => a) (fun _ => b) T/N := by
  obtain ⟨Csr,hC,hfactory⟩ := exists_log_transport_family_entropic_commutator (ι := ι) 1 (by omega)
  obtain ⟨βloc,hloc,hβfactory⟩ := hfactory K hK M hM hd
  obtain ⟨Cub,Cpf,hCub,hCpf,hε,hCem,hforcing,hfamily⟩ := hβfactory β hβ J
  let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^1)
  let Cem := sourceLogTransportCem (β : ℝ) βloc (-J)
    DGRHS.Concentration.glzUniversalTailConstant Cub
  let a := (β : ℝ)/ε
  let b := ε⁻¹*(Real.log Cpf+Real.log Cem)
  refine ⟨a,b,div_pos hβ hε,mul_nonneg (inv_pos.mpr hε).le hforcing,?_⟩
  intro N hN T hT ρ v f E hμ hf hphys hrepr hE hdiss
  apply source_diffusive_gronwall (by omega : 0 < N) hT hE
    intervalIntegrable_const intervalIntegrable_const hdiss
  filter_upwards [hphys,hrepr] with t hpt hrt ht
  obtain ⟨⟨hv,_,_,hρ,hpair⟩,hI⟩ := hpt ht
  letI := hμ t
  letI := hf t
  have hbound := (hfamily (v t) hv (ρ t) hρ hpair hI N hN (f t)).2
  rw [hrt ht,←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff] at hbound
  exact hbound

lemma sourceA_constant (a T : ℝ) : sourceA (fun _ => a) T=Real.exp (T*a) := by
  simp [sourceA,intervalIntegral.integral_const,smul_eq_mul]
end DGRHS.Dynamics
#check @DGRHS.Dynamics.exists_sourceLog_uniform_physical_diffusive_bound
#check @DGRHS.Dynamics.sourceA_constant
#print axioms DGRHS.Dynamics.exists_sourceLog_uniform_physical_diffusive_bound
#print axioms DGRHS.Dynamics.sourceA_constant
