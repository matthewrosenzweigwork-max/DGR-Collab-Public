/- Physical logarithmic time coefficients, constructed from the genuine
all-law commutator theorem before N or the evolving competitor is chosen.
Coefficient measurability is an explicit integration-domain condition: mere
pointwise choice does not prove it. Real energy representatives preserve
finiteness before the EReal-to-real bridge. -/
import DGRHS.Commutator.SourceLogEntropicCommutator
import DGRHS.Dynamics.SourceDiffusiveLocal
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

/-- Exactly the physical data required by the checked logarithmic n=1 estimate.
A positive Lipschitz upper bound also covers constant velocities. -/
def sourceLogTimeAdmissible (ρ : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (K : ℝ≥0) (M : ℝ) : Prop :=
  LipschitzWith K v ∧ 0 < (K : ℝ) ∧ 0 ≤ M ∧
  (∀ᵐ x ∂volume, ρ x ≤ M) ∧
  Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
    (gaussianRieszDensityMeasure ρ))

/-- The conclusion contains actual all-law properness and bounds, not an
assumed concentration, moment, entropic or time-endpoint field. -/
theorem exists_sourceLog_time_coefficients (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (K : ℝ → ℝ≥0) (M : ℝ → ℝ)
    (hμ : ∀ t, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) :
    ∃ a b : ℝ → ℝ, (∀ t, 0 ≤ a t ∧ 0 ≤ b t) ∧
      ∀ t, sourceLogTimeAdmissible (ρ t) (v t) (K t) (M t) →
      ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → EuclideanSpace ℝ ι),
      ∀ [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
        (sourceLogTransportKernel 1 (v t)) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
        (sourceLogTransportKernel 1 (v t)) N x ∂ν| : ℝ) : EReal) ≤
        (a t*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β (ρ t) (M t) N ν+(b t : ℝ) := by
  classical
  obtain ⟨Csr,hC,hfactory⟩ := exists_sourceLog_entropic_commutator (ι := ι) 1 (by omega)
  have hp (t : ℝ) : ∃ a b : ℝ, (0 ≤ a ∧ 0 ≤ b) ∧
      (sourceLogTimeAdmissible (ρ t) (v t) (K t) (M t) →
      ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → EuclideanSpace ℝ ι),
      ∀ [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
        (sourceLogTransportKernel 1 (v t)) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
        (sourceLogTransportKernel 1 (v t)) N x ∂ν| : ℝ) : EReal) ≤
        (a*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β (ρ t) (M t) N ν+(b : ℝ)) := by
    by_cases ht : sourceLogTimeAdmissible (ρ t) (v t) (K t) (M t)
    · obtain ⟨hv,hK,hM,hρ,hpair⟩ := ht
      letI := hμ t
      obtain ⟨βloc,hloc,hβfactory⟩ := hfactory hv hK hd (ρ t) (M t) hM hρ hpair
      obtain ⟨Cub,Cpf,hCub,hCpf,hremaining,hε,hCem,hcap,hforcing,hmom,hbound⟩ := hβfactory β hβ
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K t : ℝ)^1)
      let Cem := sourceLogTransportCem (β : ℝ) βloc
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ t)) (fun x y => logPhysicalPair (x,y)))
        DGRHS.Concentration.glzUniversalTailConstant Cub
      refine ⟨(β : ℝ)/ε, ε⁻¹*(Real.log Cpf+Real.log Cem),
        ⟨(div_pos hβ hε).le,mul_nonneg (inv_pos.mpr hε).le hforcing⟩,?_⟩
      intro _ N hN ν hν
      exact hbound N hN ν
    · exact ⟨0,0,⟨le_rfl,le_rfl⟩,fun h => (ht h).elim⟩
  choose a b hab using hp
  exact ⟨a,b,fun t => (hab t).1,fun t => (hab t).2⟩

/-- Actual conditional source diffusive estimate, with constructed physical
coefficients. All laws are chosen after those coefficients. The energy is
an actual finite real representative, never a totalized infinite toReal. -/
theorem exists_sourceLog_physical_diffusive_bound (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (K : ℝ → ℝ≥0) (M : ℝ → ℝ)
    (hμ : ∀ t, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) :
    ∃ a b : ℝ → ℝ, (∀ t, 0 ≤ a t ∧ 0 ≤ b t) ∧
      ∀ (N : ℕ), 1 ≤ N →
      ∀ (f : ℝ → Measure (Fin N → EuclideanSpace ℝ ι)),
      (∀ t, IsProbabilityMeasure (f t)) → ∀ (E : ℝ → ℝ) (Tstar : ℝ≥0∞),
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        sourceLogTimeAdmissible (ρ t) (v t) (K t) (M t)) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        sourceLogCollisionFreeEnergy β (ρ t) (M t) N (f t)=(E t : EReal)) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval E 0 T) →
      AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        deriv E t ≤ |∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
          (sourceLogTransportKernel 1 (v t)) N x ∂f t|/N) →
      ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
        E T ≤ sourceA a T*E 0+sourceB a b T/N := by
  obtain ⟨a,b,hab,hcoeff⟩ := exists_sourceLog_time_coefficients β hβ hd ρ v K M hμ
  refine ⟨a,b,hab,?_⟩
  intro N hN f hf E Tstar hphys hrepr hE hma hmb hA hB hdiss
  let J := fun t => ∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
    (sourceLogTransportKernel 1 (v t)) N x ∂f t
  apply source_diffusive_gronwall_local (by omega : 0 < N) hE hma hmb
    (Eventually.of_forall fun t => (hab t).1) (Eventually.of_forall fun t => (hab t).2) hA hB hdiss
  filter_upwards [hphys,hrepr] with t hpt hrt ht htstar
  letI := hf t
  have hbound := (hcoeff t (hpt ht htstar) N hN (f t)).2
  rw [hrt ht htstar,←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff] at hbound
  exact hbound
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLogTimeAdmissible
#check @DGRHS.Dynamics.exists_sourceLog_time_coefficients
#check @DGRHS.Dynamics.exists_sourceLog_physical_diffusive_bound
#print axioms DGRHS.Dynamics.sourceLogTimeAdmissible
#print axioms DGRHS.Dynamics.exists_sourceLog_time_coefficients
#print axioms DGRHS.Dynamics.exists_sourceLog_physical_diffusive_bound
