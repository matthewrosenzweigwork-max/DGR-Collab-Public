/- The original covariance comparison (remark:staticCLTInterpretation), with
actual physical log/Riesz operators and their constructed SAME mean-zero inverses. -/
import DGRHS.Kernel.PositiveResolventBounds
import DGRHS.CLT.SourceRieszLiteralStatic
import DGRHS.CLT.SourceLogLiteralStatic
noncomputable section
open MeasureTheory
open scoped InnerProductSpace NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian DGRHS.Kernel
variable {ι : Type*} [Fintype ι]

theorem exists_sourceRieszCovarianceBounds (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ)=0)
      (R : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R v+β • integralOperatorOnMeanZero h hh hSym hCan (R v)=v) ∧
      (∀ v, R (v+β • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ φ : Lp ℝ 2 μ,
        ‖sourceCenteredL2 φ‖^2/(1+β*‖integralOperatorOnMeanZero h hh hSym hCan‖) ≤
          inner ℝ (sourceCenteredL2 φ) (R (sourceCenteredL2 φ)) ∧
        inner ℝ (sourceCenteredL2 φ) (R (sourceCenteredL2 φ)) ≤ ‖sourceCenteredL2 φ‖^2 := by
  dsimp only
  obtain ⟨hSym,hCan,R,hR1,hR2,_⟩ := exists_sourceRieszSingularStatic 0 s β hs hβ ha ρ M hM hρ
  obtain ⟨_,_,hpos⟩ := sourceRieszKernel_properties s hs ha ρ M hM hρ
  exact ⟨hSym,hCan,R,hR1,hR2,fun φ => meanZero_kernel_resolvent_quadratic_bounds _ _
    hSym hCan hpos β hβ R hR1 (sourceCenteredL2 φ)⟩

theorem exists_sourceLogCovarianceBounds (β : ℝ≥0)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ)=0)
      (R : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R v+(β : ℝ) • integralOperatorOnMeanZero h hh hSym hCan (R v)=v) ∧
      (∀ v, R (v+(β : ℝ) • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ φ : Lp ℝ 2 μ,
        ‖sourceCenteredL2 φ‖^2/(1+(β : ℝ)*‖integralOperatorOnMeanZero h hh hSym hCan‖) ≤
          inner ℝ (sourceCenteredL2 φ) (R (sourceCenteredL2 φ)) ∧
        inner ℝ (sourceCenteredL2 φ) (R (sourceCenteredL2 φ)) ≤ ‖sourceCenteredL2 φ‖^2 := by
  dsimp only
  obtain ⟨hSym,hCan,R,hR1,hR2,_⟩ := exists_sourceLogSingularStatic 0 β hd ρ M hM hρ hpair
  obtain ⟨_,_,hpos⟩ := sourceLogKernel_properties hd ρ M hM hρ hpair
  exact ⟨hSym,hCan,R,hR1,hR2,fun φ => meanZero_kernel_resolvent_quadratic_bounds _ _
    hSym hCan hpos (β : ℝ) β.coe_nonneg R hR1 (sourceCenteredL2 φ)⟩

end DGRHS.CLT
#check @DGRHS.CLT.exists_sourceRieszCovarianceBounds
#check @DGRHS.CLT.exists_sourceLogCovarianceBounds
#print axioms DGRHS.CLT.exists_sourceRieszCovarianceBounds
#print axioms DGRHS.CLT.exists_sourceLogCovarianceBounds
