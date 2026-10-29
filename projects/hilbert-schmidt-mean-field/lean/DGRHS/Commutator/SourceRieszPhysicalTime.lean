import DGRHS.Commutator.SourceRieszCommonFiniteEnergy
import DGRHS.Dynamics.SourceDiffusiveLocal

/-! Actual physical n=1 Riesz diffusive endpoint. The finite real curve equals
the genuine extended physical objective pointwise at every claimed time.
Reference probability/envelope assumptions include endpoints; velocity is only
needed AE in the interior. General time coefficients require measurable/proper
factors explicitly. No PDE solution or dissipation identity is asserted here. -/
noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "H" => EuclideanSpace ℝ ι

/-- Physical dissipation plus the actual first commutator gives the original
local-in-lifespan Gronwall bound, under honest time-factor qualifications. -/
theorem sourceRiesz_physical_diffusive (s β : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hβ : 0<β)
    (M : ℝ→ℝ) (hM : ∀ t,0≤M t) (K : ℝ→ℝ≥0) :
    ∃ a b : ℝ→ℝ,(∀ t,0<a t ∧ 0≤b t) ∧
      ∀ (ρ : ℝ→H→ℝ) (v : ℝ→H→H),
      (∀ t,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) →
      ∀ (N : ℕ),1≤N → ∀ (f : ℝ→Measure (Fin N→H)),
      (∀ t,IsProbabilityMeasure (f t)) → ∀ (e : ℝ→ℝ) (Tstar : ℝ≥0∞),
      (∀ t,0≤t → ENNReal.ofReal t<Tstar → ∀ᵐ x ∂volume,ρ t x≤M t) →
      (∀ᵐ t ∂volume,0<t → ENNReal.ofReal t<Tstar → LipschitzWith (K t) (v t)) →
      (∀ t,0≤t → ENNReal.ofReal t<Tstar →
        sourceRieszTransportExtendedFreeEnergy (ρ t) s (M t) β N (f t)=(e t:EReal)) →
      (∀ T,0≤T → ENNReal.ofReal T<Tstar → AbsolutelyContinuousOnInterval e 0 T) →
      AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
      (∀ T,0≤T → ENNReal.ofReal T<Tstar → extendedSourceA a T≠∞) →
      (∀ T,0≤T → ENNReal.ofReal T<Tstar → extendedSourceB a b T≠∞) →
      (∀ᵐ t ∂volume,0<t → ENNReal.ofReal t<Tstar → deriv e t≤
        |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy (ρ t) s 1 (v t) N ω ∂f t|/N) →
      ∀ T,0≤T → ENNReal.ofReal T<Tstar →
      sourceRieszTransportExtendedFreeEnergy (ρ T) s (M T) β N (f T)≤
        (sourceA a T:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s (M 0) β N (f 0)+
        (sourceB a b T/N:ℝ) := by
  choose Cpf Cem hCpf hCem hFamily using
    (fun t : ℝ=>sourceRieszCommon_finiteObjective_transport (ι:=ι) s (M t) 1 le_rfl hs hd (hM t) β hβ)
  let ε := fun t=>sourceRieszPositiveTransportParameter (ι:=ι) s (M t) 1 (K t) β
  let a := fun t=>β/ε t
  let b := fun t=>(ε t)⁻¹*(Real.log (Cpf t)+Real.log (Cem t))
  have hε : ∀ t,0<ε t := fun t=>sourceRieszPositiveTransportParameter_pos s (M t) 1 (K t) β hs hd (hM t) hβ
  have hab : ∀ t,0<a t ∧ 0≤b t := by
    intro t
    exact ⟨div_pos hβ (hε t),mul_nonneg (inv_nonneg.mpr (hε t).le)
      (add_nonneg (Real.log_nonneg (hCpf t)) (Real.log_nonneg (hCem t)))⟩
  refine ⟨a,b,hab,?_⟩
  intro ρ v hμ N hN f hf e Tstar hρ hv hrepr he hma hmb hA hB hdiss T hT hTstar
  let J := fun t=>∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy (ρ t) s 1 (v t) N ω ∂f t
  have hbound : ∀ᵐ t ∂volume,0<t → ENNReal.ofReal t<Tstar → |J t|≤a t*N*e t+b t := by
    filter_upwards [hv] with t hvt ht htstar
    let _ := hμ t
    let _ := hf t
    have h := ((hFamily t (K t) (v t) (hvt ht htstar)).2
      (ρ t) (hμ t) (hρ t ht.le htstar) N hN (f t) (e t) (hrepr t ht.le htstar)).2.2
    exact h
  have hg := source_diffusive_gronwall_local (by omega : 0<N) he hma hmb
    (Eventually.of_forall fun t=>(hab t).1.le) (Eventually.of_forall fun t=>(hab t).2)
    hA hB hdiss hbound T hT hTstar
  have hzero : ENNReal.ofReal 0<Tstar := by
    simpa using (lt_of_le_of_lt (show (0:ℝ≥0∞)≤ENNReal.ofReal T from bot_le) hTstar)
  rw [hrepr T hT hTstar,hrepr 0 le_rfl hzero,←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
  exact hg

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_physical_diffusive
#print axioms DGRHS.Commutator.sourceRiesz_physical_diffusive
