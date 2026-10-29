import DGRHS.Commutator.SourceLogInitialCharacteristic
import DGRHS.Kernel.MeanZeroResolventUnique

/-! Logarithmic adaptation of proof-b SourceRieszInitialCovariance.
The actual initial covariance is a proper Gaussian second moment.
The static witness and the dynamic CF cannot choose different inverses of
the SAME original mean-zero operator: native two-sided inverse uniqueness
identifies them before any dynamic positive-semidefiniteness argument. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Kernel DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceLog_initial_covariance_witness
    (k : ℕ) (β : ℝ≥0) (hd : 0<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ z ∂volume,ρ z≤M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∀ (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 (v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan v)=v) →
      ∀ φ : Fin k→Lp ℝ 2 μ,
      ∃ (P : Measure (ℕ→ℝ)) (Z : (ℕ→ℝ)→Fin k→ℝ) (hP : IsProbabilityMeasure P),
        HasGaussianLaw Z P ∧ (∀ a,MemLp (fun ω=>Z ω a) 2 P) ∧
        (∀ a,(∫ ω,Z ω a ∂P)=0) ∧
        (∀ a b,Integrable (fun ω=>Z ω a*Z ω b) P ∧
          (∫ ω,Z ω a*Z ω b ∂P)=⟪sourceCenteredL2 (φ a),R0 (sourceCenteredL2 (φ b))⟫) := by
  dsimp only
  intro hSym hCan R0 hR0 φ
  obtain ⟨hSym1,hCan1,R1,hR1,hR2,hstat⟩ := exists_sourceLogSingularStatic
    k β hd ρ M hM hρ hpair
  have he : R1=R0 := meanZeroResolvent_unique _ _ hSym hCan β R1 R0 hR1 hR0
  obtain ⟨P,Z,hP,hPN,hweak,hZ,hMean,hCov,hCF,hMGF⟩ := hstat φ
  refine ⟨P,Z,hP,hZ,fun a=>?_,hMean,?_⟩
  · exact (hZ.map_fun (ContinuousLinearMap.proj a)).memLp_two
  · simpa only [he] using hCov

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_initial_covariance_witness
#print axioms DGRHS.Commutator.exists_sourceLog_initial_covariance_witness
