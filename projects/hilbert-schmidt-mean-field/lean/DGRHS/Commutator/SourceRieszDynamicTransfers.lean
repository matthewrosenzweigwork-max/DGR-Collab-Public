import DGRHS.Commutator.SourceRieszDynamicEntropy
import DGRHS.Commutator.SourceRieszDynamicCommutator
import DGRHS.Commutator.SourceRieszDynamicOscillation

/-! Original positive-Riesz lem:dynamicEntropyTransfers(i)-(iii). Actual physical
free-energy Gronwall, literal initial Gibbs and common density envelope yield
finite entropy and proper source domain, then absolute commutator/empirical
errors. All three constants are chosen before N, both densities, law, velocity,
test, interval location and Gronwall coefficients. No desired KL/error premise. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszDynamic_entropy_transfers (s β M Bmax L : ℝ)
    (hs : 0<s) (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ))
    (hM : 0≤M) (hBmax : 0≤Bmax) (hL : 0≤L) (K : ℝ≥0) :
    ∃ H Dc Dl : ℝ,0≤H ∧ 0≤Dc ∧ 0≤Dl ∧ ∀ N : ℕ,1≤N → ∀ (ρ₀ ρ : E→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
        [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ₀ x≤M) → (∀ᵐ x ∂volume,ρ x≤M) →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],∀ A B : ℝ,0≤A → B≤Bmax →
      sourceRieszTransportExtendedFreeEnergy ρ s M β N ν≤
        (A:EReal)*sourceRieszTransportExtendedFreeEnergy ρ₀ s M β N (sourceRieszSingularGibbs s β ρ₀ N)+
          (B/(N:ℝ):ℝ) →
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ ∧
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H ∧
      ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) ∧
      Integrable (sourceRieszTransportBackgroundEnergy ρ s N) ν ∧
      Integrable (llr ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ν ∧
      sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=(sourceRieszTransportProperFreeEnergy ρ s β N ν:ℝ) ∧
      (∀ (v : E→E),LipschitzWith K v →
        Integrable (sourceRieszLocalTransportEnergy ρ s 1 v N) ν ∧
        (∫ ω,|sourceRieszLocalTransportEnergy ρ s 1 v N ω| ∂ν)≤Dc/(N:ℝ)) ∧
      ∀ (q : E→ℝ),Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
        sSup (Set.range q)-sInf (Set.range q)≤L →
        Integrable q (gaussianRieszDensityMeasure ρ) ∧
        (∀ ω,Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
        Integrable (sourceRieszDynamicRawFluctuation ρ q N) ν ∧
        Integrable (sourceRieszDynamicEmpiricalDifference ρ q N) ν ∧
        (∫ ω,|sourceRieszDynamicEmpiricalDifference ρ q N ω| ∂ν)≤Dl/Real.sqrt N := by
  obtain ⟨H,hH,hentropy⟩ := sourceRieszDynamic_common_entropy (ι:=ι) s β M Bmax hs hβ hd hM hBmax
  obtain ⟨Dc,hDc,hcomm⟩ := sourceRieszDynamic_common_commutator (ι:=ι) s β M H hs hβ hd hM K
  obtain ⟨Dl,hDl,hlinear⟩ := sourceRieszDynamic_common_oscillation (ι:=ι) s β M H L hs hβ hd hM hL
  refine ⟨H,Dc,Dl,hH,hDc,hDl,?_⟩
  intro N hN ρ₀ ρ hμ₀ hμ hρ₀ hρ ν hν A B hA hB hE
  obtain ⟨hKL,hHb⟩ := hentropy N hN ρ₀ ρ hρ₀ hρ ν A B hA hB hE
  have hv0 : LipschitzWith 0 (fun _ : E=>(0:E)) := by intro x y;simp
  obtain ⟨_,_,_,_,_,hproper⟩ := sourceRieszTransport_finiteKL_entropic s M 1 (by omega) hs hd hM β hβ hv0 ρ hρ
  obtain ⟨hac,hbg,hllr,_,_⟩ := hproper N hN ν hKL
  have heq := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM β hβ ρ hρ N hN ν hac hbg hllr
  refine ⟨hKL,hHb,hac,hbg,hllr,heq,?_,?_⟩
  · intro v hv
    exact hcomm v hv ρ hρ N hN ν hKL hHb
  · intro q hq hlo hup hosc
    exact hlinear ρ hρ N hN q hq hlo hup hosc ν hKL hHb

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamic_entropy_transfers
#print axioms DGRHS.Commutator.sourceRieszDynamic_entropy_transfers
